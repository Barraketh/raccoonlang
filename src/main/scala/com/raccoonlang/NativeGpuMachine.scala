package com.raccoonlang

import scala.collection.mutable

import NativeGpuAst._
import NativeGpuBackend._
import NativeGpuDevice._

/**
 * One-invocation interpreter for the decoded checked Cuda AST. The scheduler and request boundaries mirror the source
 * WarpMachine; the device owns only private primitive backing arrays.
 */
private[raccoonlang] object NativeGpuMachine {
  private val WarpCount = 8
  private val LaneCount = 32
  private val FullMask = (BigInt(1) << LaneCount) - 1
  private val NormalizeBudget = 96
  private val U32Limit = BigInt(1) << 32
  private val U64Limit = BigInt(1) << 64

  private final case class Position(block: Block, pc: Int)
  private sealed trait Frame
  private final case class BranchNo(no: Block, rest: Position, parentMask: BigInt, noMask: BigInt) extends Frame
  private final case class BranchJoin(rest: Position, parentMask: BigInt) extends Frame
  private final case class Scoped(rest: Position, parentMask: BigInt) extends Frame
  private final case class Loop(
      id: BigInt,
      stop: Vector[BigInt],
      step: Vector[BigInt],
      body: Block,
      rest: Position,
      parentMask: BigInt,
      iterationMask: BigInt
  ) extends Frame

  private sealed trait Status
  private case object Runnable extends Status
  private case object Blocked extends Status
  private final case class BlockedGate(id: BigInt) extends Status
  private final case class BlockedMbar(address: BigInt, parity: BigInt) extends Status
  private final case class BlockedBulk(kind: BulkWaitKind, pending: BigInt) extends Status
  private final case class BlockedTmem(kind: TmemWaitKind) extends Status
  private case object Finished extends Status

  private final case class Register(values: Vector[BigInt], initializedMask: BigInt)
  private final class Warp(val id: Int, initial: Block) {
    var position: Position = Position(initial, 0)
    var frames: List[Frame] = Nil
    val registers: mutable.Map[BigInt, Register] = mutable.HashMap.empty
    var deferredLoads: Vector[RegisterWrite] = Vector.empty
    var activeMask: BigInt = FullMask
    var status: Status = Runnable
  }

  private final case class Barrier(
      address: BigInt,
      expectedArrivals: BigInt,
      arrivals: BigInt,
      expectedBytes: BigInt,
      issuedBytes: BigInt,
      completedBytes: BigInt,
      phase: BigInt,
      initialized: Boolean,
      completedPhases: BigInt
  )
  private final case class Gate(
      id: BigInt,
      expectedThreads: BigInt,
      arrivedThreads: BigInt,
      remainingThreads: BigInt,
      released: Boolean
  )
  private sealed trait Event {
    def warp: Int
    def committed: Boolean
  }
  private final case class DataEvent(
      warp: Int,
      request: Request,
      barrier: Option[BigInt],
      barrierPhase: BigInt,
      committed: Boolean
  ) extends Event
  private final case class CommitEvent(warp: Int, address: BigInt, phase: BigInt) extends Event {
    override val committed: Boolean = true
  }

  private sealed trait EvalValue
  private final case class Lanes(values: Vector[BigInt]) extends EvalValue
  private final case class SharedPointer(tpe: DType, byteBase: BigInt) extends EvalValue
  private final case class ParameterAddress(name: String) extends EvalValue
  private final case class Bad(message: String) extends EvalValue

  private sealed trait Attempt
  private case object Progress extends Attempt
  private case object Waiting extends Attempt
  private final case class Failed(failure: Failure) extends Attempt

  private final class Run(plan: Plan, inputs: Inputs, fuel: BigInt) {
    private val device = new NativeGpuDevice(plan, inputs)
    private val warps = Array.tabulate(WarpCount)(id => new Warp(id, plan.kernel.body))
    private val barriers = mutable.LinkedHashMap.empty[BigInt, Barrier]
    private val gates = mutable.LinkedHashMap.empty[BigInt, Gate]
    private val events = mutable.ArrayBuffer.empty[Event]
    private var cursor = 0
    private var warpSteps = BigInt(0)
    private var asyncCompletions = BigInt(0)
    private var tmaBytes = BigInt(0)
    private var scalarMuls = BigInt(0)
    private var scalarAdds = BigInt(0)
    private var mmaInstructions = BigInt(0)
    private var tmemLoads = BigInt(0)
    private var tmaStores = BigInt(0)

    def execute(): Result = {
      if (fuel < 0) return result(Some(InvalidState("fuel must be a nonnegative Nat")))
      device.initializationFailure match {
        case Some(message) => return result(Some(InvalidState(message)))
        case None          => ()
      }
      var remaining = fuel
      while (true) {
        wakeAll()
        val finished = warps.forall(_.status == Finished)
        if (finished && events.isEmpty) return finalResult()
        if (remaining == 0) return result(Some(FuelExhausted))
        remaining -= 1

        findRunnable(cursor) match {
          case Some(index) =>
            cursor = (index + 1) % WarpCount
            stepWarp(index) match {
              case Progress        => ()
              case Waiting         => ()
              case Failed(problem) => return result(Some(problem))
            }
          case None if events.nonEmpty =>
            retireHead() match {
              case Progress        => ()
              case Waiting         => return result(Some(Deadlocked))
              case Failed(problem) => return result(Some(problem))
            }
          case None => return result(Some(Deadlocked))
        }
      }
      result(Some(Deadlocked))
    }

    private def finalResult(): Result = {
      if (warps.exists(_.deferredLoads.nonEmpty) || !device.isTmemQuiescent || barriers.values.exists(_.initialized))
        result(Some(NotQuiescent))
      else if (!device.outputIsComplete) result(Some(IncompleteOutput))
      else result(None, device.outputSnapshot)
    }

    private def result(failure: Option[Failure], output: Vector[Int] = Vector.empty): Result =
      Result(
        if (failure.isEmpty) output else Vector.empty,
        Stats(warpSteps, asyncCompletions, tmaBytes, scalarMuls, scalarAdds, mmaInstructions, tmemLoads, tmaStores),
        failure
      )

    private def findRunnable(from: Int): Option[Int] = {
      var offset = 0
      while (offset < WarpCount) {
        val index = (from + offset) % WarpCount
        if (warps(index).status == Runnable) return Some(index)
        offset += 1
      }
      None
    }

    private def wakeAll(): Unit = {
      var index = 0
      while (index < WarpCount) {
        wakeOne(index)
        index += 1
      }
    }

    private def wakeOne(index: Int): Unit = {
      val warp = warps(index)
      warp.status match {
        case BlockedGate(gateId) =>
          gates.get(gateId).filter(_.released).foreach { gate =>
            val participants = maskCount(warp.activeMask)
            val left = (gate.remainingThreads - participants).max(BigInt(0))
            if (left == 0) gates.update(gateId, Gate(gate.id, gate.expectedThreads, 0, 0, released = false))
            else gates.update(gateId, gate.copy(remainingThreads = left))
            warp.status = Runnable
            warpSteps += 1
          }
        case BlockedMbar(address, parity) if findBarrier(address).exists(barrierWaitReady(_, parity)) =>
          warp.status = Runnable
        case BlockedBulk(_, pending) if storeEventsForWarp(warp.id) <= pending => warp.status = Runnable
        case BlockedTmem(TmemWaitKind.Load) if pendingTmemLoads(warp.id) == 0  => warp.status = Runnable
        case _                                                                 => ()
      }
    }

    private def stepWarp(index: Int): Attempt = {
      val warp = warps(index)
      normalize(warp)
      warp.status match {
        case Finished => Progress
        case Runnable =>
          warp.position.block.statements.lift(warp.position.pc) match {
            case None            => Progress
            case Some(statement) => stepStatement(warp, statement, Position(warp.position.block, warp.position.pc + 1))
          }
        case _ => Waiting
      }
    }

    private def normalize(warp: Warp): Unit = {
      var fuelLeft = NormalizeBudget
      var done = false
      while (fuelLeft > 0 && !done) {
        fuelLeft -= 1
        if (warp.activeMask == 0 && warp.position.pc < warp.position.block.statements.length) {
          warp.position = Position(Block(Vector.empty), 0)
        } else if (warp.position.pc < warp.position.block.statements.length) {
          warp.status = Runnable
          done = true
        } else {
          warp.frames match {
            case Nil =>
              warp.position = Position(Block(Vector.empty), 0)
              warp.status = Finished
              done = true
            case frame :: rest =>
              warp.frames = rest
              frame match {
                case BranchNo(no, after, parent, noMask) =>
                  if (maskCount(noMask) == 0) {
                    warp.position = after
                    warp.activeMask = parent
                  } else {
                    warp.frames = BranchJoin(after, parent) :: warp.frames
                    warp.position = Position(no, 0)
                    warp.activeMask = noMask
                    warp.status = Runnable
                    done = true
                  }
                case BranchJoin(after, parent) =>
                  warp.position = after
                  warp.activeMask = parent
                case Scoped(after, parent) =>
                  warp.position = after
                  warp.activeMask = parent
                case loop: Loop =>
                  warp.registers.get(loop.id) match {
                    case None =>
                      warp.position = Position(Block(Vector.empty), 0)
                      warp.status = Blocked
                      done = true
                    case Some(register) =>
                      val nextValues = addLoopValues(register.values, loop.step, loop.iterationMask)
                      writeMasked(warp.registers, loop.id, nextValues, loop.iterationMask)
                      val nextMask = loopMask(nextValues, loop.stop, loop.parentMask)
                      if (nextMask == 0) {
                        warp.position = loop.rest
                        warp.activeMask = loop.parentMask
                      } else {
                        warp.frames = loop.copy(iterationMask = nextMask) :: warp.frames
                        warp.position = Position(loop.body, 0)
                        warp.activeMask = nextMask
                        warp.status = Runnable
                        done = true
                      }
                  }
              }
          }
        }
      }
    }

    private def stepStatement(warp: Warp, statement: Stmt, rest: Position): Attempt = statement match {
      case Stmt.Decl(_, id, init, _) =>
        eval(warp, init, warp.activeMask) match {
          case Lanes(values) if values.length == LaneCount =>
            warp.registers.update(id, Register(values, warp.activeMask))
            retire(warp, rest)
          case Lanes(_)     => failInvalid("initializer is not a 32-lane vector")
          case Bad(message) => failInvalid(message)
          case _            => failInvalid("register initializer is not a numeric lane vector")
        }
      case Stmt.DeclOut(_, id) =>
        warp.registers.update(id, Register(Vector.fill(LaneCount)(BigInt(0)), 0))
        retire(warp, rest)
      case Stmt.Assign(id, value) =>
        eval(warp, value, warp.activeMask) match {
          case Lanes(values) =>
            if (!warp.registers.contains(id)) failInvalid("assignment writes an undeclared register")
            else {
              writeMasked(warp.registers, id, values, warp.activeMask)
              retire(warp, rest)
            }
          case Bad(message) => failInvalid(message)
          case _            => failInvalid("assignment value is not a numeric lane vector")
        }
      case Stmt.Store(_, _, _) => Failed(Unsupported("generic global store statement"))
      case Stmt.Shared(_, _, _) =>
        Failed(Unsupported("static shared declaration outside the dynamic-shared Tiny subset"))
      case Stmt.ForLoop(id, start, stop, body)         => stepLoop(warp, id, start, stop, Expr.Lit(1), body, rest)
      case Stmt.ForStride(id, start, stop, step, body) => stepLoop(warp, id, start, stop, step, body, rest)
      case Stmt.IfElse(condition, yes, no)             => stepIfElse(warp, condition, yes, no, rest)
      case Stmt.Scoped(body) =>
        warp.frames = Scoped(rest, warp.activeMask) :: warp.frames
        warp.position = Position(body, 0)
        warpSteps += 1
        Progress
      case Stmt.Sync => gateArrive(warp, BigInt(1000000), BigInt(256), rest)
      case Stmt.SyncWarp =>
        if (warp.activeMask != FullMask) failInvalid("__syncwarp requires its default full-warp member mask")
        else gateArrive(warp, BigInt(2000000 + warp.id), BigInt(32), rest)
      case Stmt.Instruction(instruction) => stepInstruction(warp, instruction, rest)
      case Stmt.Error(message)           => Failed(Unsupported(s"Cuda.Stmt.error: $message"))
    }

    private def stepIfElse(warp: Warp, condition: Expr, yes: Block, no: Block, rest: Position): Attempt =
      eval(warp, condition, warp.activeMask) match {
        case Lanes(values) if values.length == LaneCount =>
          val (yesMask, noMask) = splitMask(values, warp.activeMask)
          warpSteps += 1
          if (maskCount(yesMask) == 0) {
            warp.frames = BranchJoin(rest, warp.activeMask) :: warp.frames
            warp.position = Position(no, 0)
            warp.activeMask = noMask
          } else {
            warp.frames = BranchNo(no, rest, warp.activeMask, noMask) :: warp.frames
            warp.position = Position(yes, 0)
            warp.activeMask = yesMask
          }
          Progress
        case Lanes(_)     => failInvalid("if condition is not a 32-lane vector")
        case Bad(message) => failInvalid(message)
        case _            => failInvalid("if condition is not a numeric lane vector")
      }

    private def stepLoop(
        warp: Warp,
        id: BigInt,
        start: Expr,
        stop: Expr,
        step: Expr,
        body: Block,
        rest: Position
    ): Attempt = {
      val initial = eval(warp, start, warp.activeMask)
      val bounds = eval(warp, stop, warp.activeMask)
      val increments = eval(warp, step, warp.activeMask)
      (initial, bounds, increments) match {
        case (Lanes(values), Lanes(stops), Lanes(amounts))
            if values.length == LaneCount && stops.length == LaneCount && amounts.length == LaneCount =>
          warp.registers.update(id, Register(values, warp.activeMask))
          val iterations = loopMask(values, stops, warp.activeMask)
          if (iterations == 0) retire(warp, rest)
          else {
            warpSteps += 1
            warp.frames = Loop(id, stops, amounts, body, rest, warp.activeMask, iterations) :: warp.frames
            warp.position = Position(body, 0)
            warp.activeMask = iterations
            Progress
          }
        case (Bad(message), _, _)           => failInvalid(message)
        case (_, Bad(message), _)           => failInvalid(message)
        case (_, _, Bad(message))           => failInvalid(message)
        case (Lanes(_), Lanes(_), Lanes(_)) => failInvalid("loop operand is not a 32-lane vector")
        case _                              => failInvalid("loop start is not a numeric lane vector")
      }
    }

    private def stepInstruction(warp: Warp, instruction: Instr, rest: Position): Attempt = instruction match {
      case Instr.BarSync(idExpr, threadsExpr) =>
        val id = evalUniform(warp, idExpr)
        val threads = evalUniform(warp, threadsExpr)
        (id, threads) match {
          case (Some(value), Some(count)) => gateArrive(warp, value, count, rest)
          case (None, _)                  => failInvalid("bar.sync id is not uniform")
          case (_, None)                  => failInvalid("bar.sync participant count is not uniform")
        }
      case Instr.MbarInit(barExpr, countExpr) =>
        val address = evalAddress(warp, barExpr)
        val count = evalUniform(warp, countExpr)
        (address, count) match {
          case (Some(bar), Some(expected)) => stepMbarInit(warp, bar, expected, rest)
          case (None, _)                   => failInvalid("mbarrier.init address is not shared memory")
          case (_, None)                   => failInvalid("mbarrier.init arrival count is not uniform")
        }
      case Instr.MbarInval(barExpr) =>
        evalAddress(warp, barExpr).fold[Attempt](failInvalid("mbarrier.inval address is not shared memory"))(
          stepMbarInval(warp, _, rest)
        )
      case Instr.MbarArrive(window, barExpr, arrival) =>
        if (window == Window.Cluster) Failed(Unsupported("cluster-scope mbarrier arrival"))
        else
          evalAddress(warp, barExpr) match {
            case None => failInvalid("mbarrier.arrive address is not shared memory")
            case Some(address) =>
              arrival match {
                case Arrival.One => stepMbarArrive(warp, address, 1, 0, rest)
                case Arrival.Count(value) =>
                  evalUniform(warp, value) match {
                    case Some(count) => stepMbarArrive(warp, address, count, 0, rest)
                    case None        => failInvalid("mbarrier arrival count is not uniform")
                  }
                case Arrival.ExpectTx(value) =>
                  evalUniform(warp, value) match {
                    case Some(bytes) => stepMbarArrive(warp, address, 1, bytes, rest)
                    case None        => failInvalid("mbarrier expected byte count is not uniform")
                  }
              }
          }
      case Instr.MbarWait(scope, barExpr, parityExpr) =>
        if (scope == BarrierScope.Cluster) Failed(Unsupported("cluster-scope mbarrier wait"))
        else {
          val address = evalAddress(warp, barExpr)
          val parity = evalUniform(warp, parityExpr)
          (address, parity) match {
            case (None, _)                => failInvalid("mbarrier.wait address is not shared memory")
            case (_, None)                => failInvalid("mbarrier.wait parity is not uniform")
            case (Some(bar), Some(value)) => stepMbarWait(warp, bar, value, rest)
          }
        }
      case Instr.FenceMbarInit | Instr.FenceProxyAsync | Instr.TcFence(_) => retire(warp, rest)
      case Instr.ClusterArrive               => Failed(Unsupported("cluster barrier arrive"))
      case Instr.ClusterWait                 => Failed(Unsupported("cluster barrier wait"))
      case load: Instr.TmaLoad               => stepTmaLoad(warp, load, rest)
      case Instr.TmaStore(map, x, y, source) => stepTmaStore(warp, map, x, y, source, rest)
      case Instr.BulkCommit =>
        if (!oneLaneActive(warp)) failInvalid("cp.async.bulk.commit_group requires exactly one active lane")
        else {
          var index = 0
          while (index < events.length) {
            events(index) match {
              case event: DataEvent if event.warp == warp.id && isStore(event.request) =>
                events(index) = event.copy(committed = true)
              case _ => ()
            }
            index += 1
          }
          retire(warp, rest)
        }
      case Instr.BulkWait(kind, pending) =>
        if (!oneLaneActive(warp)) failInvalid("cp.async.bulk.wait_group requires exactly one active lane")
        else if (storeEventsForWarp(warp.id) <= pending) retire(warp, rest)
        else { warp.status = BlockedBulk(kind, pending); Waiting }
      case Instr.TmemAlloc(group, slotExpr, colsExpr) => stepTmemAlloc(warp, group, slotExpr, colsExpr, rest)
      case Instr.TmemRelinquish(group) =>
        device
          .relinquish(group, warp.activeMask)
          .fold(retire(warp, rest))(message =>
            if (group == Group.Two) Failed(Unsupported(message)) else failInvalid(message)
          )
      case Instr.TmemDealloc(group, addressExpr, colsExpr) => stepTmemDealloc(warp, group, addressExpr, colsExpr, rest)
      case Instr.Mma(group, accumulator, a, b, descriptor, accumulate) =>
        if (!oneLaneActive(warp)) failInvalid("tcgen05.mma issue requires exactly one active lane")
        else stepMma(warp, group, accumulator, a, b, descriptor, accumulate, rest)
      case Instr.TcCommit(group, barExpr, multicast) => stepTcCommit(warp, group, barExpr, multicast, rest)
      case Instr.TmemLoad(shape, destinations, addressExpr) =>
        stepTmemLoad(warp, shape, destinations, addressExpr, rest)
      case Instr.TmemStore(_, _, _, _) => Failed(Unsupported("tcgen05.st is outside the TinyGEMM interpreter subset"))
      case Instr.TmemWait(TmemWaitKind.Store) => Failed(Unsupported("tcgen05.wait::st without supported tmemStore"))
      case Instr.TmemWait(TmemWaitKind.Load) =>
        if (warp.activeMask != FullMask)
          failInvalid("tcgen05.wait::ld requires all 32 lanes of the issuing warp to participate")
        else if (pendingTmemLoads(warp.id) != 0) { warp.status = BlockedTmem(TmemWaitKind.Load); Waiting }
        else {
          warp.deferredLoads.foreach(write => writeMasked(warp.registers, write.id, write.lanes, FullMask))
          warp.deferredLoads = Vector.empty
          retire(warp, rest)
        }
      case Instr.Elect(flag) =>
        if (warp.activeMask != FullMask) failInvalid("elect.sync requires its fixed full-warp member mask")
        else {
          val values = Array.fill(LaneCount)(BigInt(0))
          var found = false
          var lane = 0
          while (lane < LaneCount) {
            if (laneActive(warp.activeMask, lane) && !found) { values(lane) = 1; found = true }
            lane += 1
          }
          if (!found) failInvalid("elect.sync has no active lane")
          else {
            writeMasked(warp.registers, flag, values.toVector, warp.activeMask)
            retire(warp, rest)
          }
        }
      case Instr.Shfl(destination, value, lane)  => stepShfl(warp, destination, value, lane, rest)
      case Instr.VoteAny(destination, predicate) => stepVoteAny(warp, destination, predicate, rest)
      case Instr.SetMaxNReg(_, _)   => Failed(Unsupported("setmaxnreg register-pool behavior is not modeled"))
      case Instr.MovF32(_, _)       => Failed(Unsupported("floating-point mov in exact-ring TinyGEMM"))
      case Instr.Ex2(_, _)          => Failed(Unsupported("floating-point ex2 in exact-ring TinyGEMM"))
      case Instr.Lg2(_, _)          => Failed(Unsupported("floating-point lg2 in exact-ring TinyGEMM"))
      case Instr.Ex2Emulated(_, _)  => Failed(Unsupported("floating-point ex2 emulation in exact-ring TinyGEMM"))
      case Instr.Rcp(_, _, _)       => Failed(Unsupported("floating-point reciprocal in exact-ring TinyGEMM"))
      case Instr.CvtBf16x2(_, _, _) => Failed(Unsupported("bf16 conversion in exact-ring TinyGEMM"))
      case Instr.LdRelaxed(scope, destination, addressExpr) => stepLdShared(warp, scope, destination, addressExpr, rest)
      case Instr.CasRelaxed(_, _, _, _, _)                  => Failed(Unsupported("atomic compare-and-swap"))
      case Instr.MovSpecial(_, _)                           => Failed(Unsupported("cluster special register"))
      case Instr.Mapa(_, _, _)                              => Failed(Unsupported("cluster shared-memory mapa"))
      case Instr.StShared(address, values)                  => stepStShared(warp, address, values, rest)
    }

    private def stepTmaLoad(warp: Warp, instruction: Instr.TmaLoad, rest: Position): Attempt = {
      import instruction._
      if (group == Group.Two) return Failed(Unsupported("two-CTA TMA load"))
      if (!oneLaneActive(warp)) return failInvalid("TMA load issue requires exactly one active lane")
      val resolved = evalMap(warp, map)
      val destination = evalAddress(warp, dst)
      val xValue = evalUniform(warp, x)
      val yValue = evalUniform(warp, y)
      val barrierAddress = evalAddress(warp, bar)
      if (resolved.isEmpty) return failInvalid("TMA load map operand is not a validated launcher map")
      if (destination.isEmpty) return failInvalid("TMA load destination is not a uniform shared address")
      if (xValue.isEmpty) return failInvalid("TMA load x coordinate is not uniform")
      if (yValue.isEmpty) return failInvalid("TMA load y coordinate is not uniform")
      if (barrierAddress.isEmpty) return failInvalid("TMA load completion operand is not a shared address")
      val address = barrierAddress.get
      val barrier = findBarrier(address)
      if (barrier.isEmpty) return failInvalid("TMA load targets an uninitialized completion barrier")
      val phase = barrier.get.phase
      scheduleBarrierBytes(barrier.get, phase, BigInt(16384)) match {
        case None => failInvalid("TMA load exceeds the current expect_tx byte budget")
        case Some(updated) =>
          barriers.update(address, updated)
          events += DataEvent(
            warp.id,
            Request.TmaLoad(resolved.get, destination.get, xValue.get, yValue.get),
            Some(address),
            phase,
            committed = true
          )
          retire(warp, rest)
      }
    }

    private def stepTmaStore(
        warp: Warp,
        mapExpr: Expr,
        xExpr: Expr,
        yExpr: Expr,
        sourceExpr: Expr,
        rest: Position
    ): Attempt = {
      if (!oneLaneActive(warp)) return failInvalid("TMA store issue requires exactly one active lane")
      val map = evalMap(warp, mapExpr)
      val x = evalUniform(warp, xExpr)
      val y = evalUniform(warp, yExpr)
      val source = evalAddress(warp, sourceExpr)
      if (map.isEmpty) return failInvalid("TMA store map operand is not a validated launcher map")
      if (x.isEmpty) return failInvalid("TMA store x coordinate is not uniform")
      if (y.isEmpty) return failInvalid("TMA store y coordinate is not uniform")
      if (source.isEmpty) return failInvalid("TMA store source is not a uniform shared address")
      events += DataEvent(warp.id, Request.TmaStore(map.get, x.get, y.get, source.get), None, 0, committed = false)
      retire(warp, rest)
    }

    private def stepMma(
        warp: Warp,
        group: Group,
        accumulatorExpr: Expr,
        a: MmaA,
        b: SmemDesc,
        descriptor: InstrDesc,
        accumulateExpr: Expr,
        rest: Position
    ): Attempt = {
      val accumulator = evalUniform(warp, accumulatorExpr)
      val sourceA = evalMmaA(warp, a)
      val sourceB = evalOperand(warp, b)
      val accumulate = evalUniform(warp, accumulateExpr)
      if (group == Group.Two) return Failed(Unsupported("two-CTA tcgen05.mma"))
      if (accumulator.isEmpty) return failInvalid("tcgen05.mma accumulator address is not uniform")
      if (sourceA.isEmpty) return failInvalid("tcgen05.mma A operand is unsupported or nonuniform")
      if (sourceB.isEmpty) return failInvalid("tcgen05.mma B descriptor is unsupported or nonuniform")
      if (accumulate.isEmpty) return failInvalid("tcgen05.mma accumulate predicate is not uniform")
      events += DataEvent(
        warp.id,
        Request.Mma(MmaDesc(group, accumulator.get, sourceA.get, sourceB.get, descriptor, accumulate.get)),
        None,
        0,
        committed = true
      )
      retire(warp, rest)
    }

    private def stepTmemLoad(
        warp: Warp,
        shape: TmemShape,
        destinations: Vector[BigInt],
        addressExpr: Expr,
        rest: Position
    ): Attempt = {
      if (warp.activeMask != FullMask)
        return failInvalid("tcgen05.ld requires all 32 lanes of the issuing warp to participate")
      val address = evalUniform(warp, addressExpr)
      if (address.isEmpty) return failInvalid("tcgen05.ld tensor-memory base is not uniform across the warp")
      events += DataEvent(
        warp.id,
        Request.TmemLoad(shape, destinations, address.get, BigInt(warp.id % 4), warp.activeMask),
        None,
        0,
        committed = true
      )
      retire(warp, rest)
    }

    private def stepTmemAlloc(warp: Warp, group: Group, slotExpr: Expr, colsExpr: Expr, rest: Position): Attempt = {
      if (warp.activeMask != FullMask)
        return failInvalid("tcgen05.alloc requires all 32 lanes of the issuing warp to participate")
      if (group == Group.Two) return Failed(Unsupported("two-CTA tensor-memory allocation"))
      val slot = evalAddress(warp, slotExpr)
      val cols = evalUniform(warp, colsExpr)
      if (slot.isEmpty) return failInvalid("tensor-memory allocation slot is not a shared address")
      if (cols.isEmpty) return failInvalid("tensor-memory allocation column count is not uniform")
      device.allocate(group, slot.get, cols.get, warp.activeMask) match {
        case Some(message) => Failed(DeviceFault(message))
        case None          => retire(warp, rest)
      }
    }

    private def stepTmemDealloc(
        warp: Warp,
        group: Group,
        addressExpr: Expr,
        colsExpr: Expr,
        rest: Position
    ): Attempt = {
      if (warp.activeMask != FullMask)
        return failInvalid("tcgen05.dealloc requires all 32 lanes of the issuing warp to participate")
      if (group == Group.Two) return Failed(Unsupported("two-CTA tensor-memory deallocation"))
      val address = evalUniform(warp, addressExpr)
      val cols = evalUniform(warp, colsExpr)
      if (address.isEmpty) return failInvalid("tensor-memory deallocation address is not uniform")
      if (cols.isEmpty) return failInvalid("tensor-memory deallocation column count is not uniform")
      device.deallocate(group, address.get, cols.get, warp.activeMask) match {
        case Some(_) => Failed(DeviceFault("tensor-memory deallocation does not match the live allocation"))
        case None    => retire(warp, rest)
      }
    }

    private def stepTcCommit(
        warp: Warp,
        group: Group,
        barExpr: Expr,
        multicast: Option[BigInt],
        rest: Position
    ): Attempt = {
      if (!oneLaneActive(warp)) return failInvalid("tcgen05.commit issue requires exactly one active lane")
      if (group == Group.Two) return Failed(Unsupported("two-CTA tcgen05.commit"))
      if (multicast.nonEmpty) return Failed(Unsupported("multicast tcgen05.commit"))
      evalAddress(warp, barExpr) match {
        case None => failInvalid("tcgen05.commit barrier is not shared memory")
        case Some(address) =>
          findBarrier(address) match {
            case None => failInvalid("tcgen05.commit targets an uninitialized mbarrier")
            case Some(barrier) =>
              events += CommitEvent(warp.id, address, barrier.phase)
              retire(warp, rest)
          }
      }
    }

    private def stepLdShared(
        warp: Warp,
        scope: Scope,
        destination: BigInt,
        addressExpr: Expr,
        rest: Position
    ): Attempt = scope match {
      case Scope.Cluster => Failed(Unsupported("cluster-scope generic load"))
      case Scope.Gpu     => Failed(Unsupported("GPU-scope generic load"))
      case Scope.Cta =>
        evalAddress(warp, addressExpr) match {
          case None => failInvalid("generic load address is not a uniform shared pointer")
          case Some(address) =>
            device.readShared(address, DType.U32) match {
              case None => Failed(DeviceFault("generic shared load is out of bounds or misaligned"))
              case Some(value) =>
                writeMasked(warp.registers, destination, uniform(value), warp.activeMask)
                retire(warp, rest)
            }
        }
    }

    private def stepStShared(warp: Warp, addressExpr: Expr, expressions: Vector[Expr], rest: Position): Attempt =
      eval(warp, addressExpr, warp.activeMask) match {
        case Bad(message) => failInvalid(message)
        case Lanes(addressValues) if addressValues.length == LaneCount && expressions.nonEmpty =>
          val initialJournalCapacity = math
            .min(
              expressions.length.toLong * maskCount(warp.activeMask).toLong,
              256L
            )
            .toInt
          val transaction = device.beginSharedTransaction(initialJournalCapacity)
          val valueIterator = expressions.iterator
          var word = 0
          while (valueIterator.hasNext) {
            eval(warp, valueIterator.next(), warp.activeMask) match {
              case Lanes(values) =>
                val shifted = addressValues.map(_ + word * 4)
                if (!device.writeSharedLanes(shifted, values, warp.activeMask, DType.F32, transaction)) {
                  device.rollbackSharedTransaction(transaction)
                  return Failed(DeviceFault("st.shared vector access is outside dynamic shared memory"))
                }
              case Bad(_) =>
                device.rollbackSharedTransaction(transaction)
                return Failed(DeviceFault("st.shared vector access is outside dynamic shared memory"))
              case _ =>
                device.rollbackSharedTransaction(transaction)
                return Failed(DeviceFault("st.shared vector access is outside dynamic shared memory"))
            }
            word += 1
          }
          device.commitSharedTransaction(transaction)
          retire(warp, rest)
        case Lanes(_) => failInvalid("st.shared requires a 32-lane address vector and at least one value")
        case _        => failInvalid("st.shared address is not a lane vector")
      }

    private def stepShfl(
        warp: Warp,
        destination: BigInt,
        sourceExpr: Expr,
        sourceLane: BigInt,
        rest: Position
    ): Attempt = {
      if (warp.activeMask != FullMask) return failInvalid("shfl.sync.idx requires its fixed full-warp member mask")
      if (sourceLane < 0 || sourceLane >= LaneCount) return failInvalid("shfl.sync.idx source lane is out of range")
      if (!laneActive(warp.activeMask, sourceLane.toInt))
        return failInvalid("shfl.sync.idx source lane is not participating")
      eval(warp, sourceExpr, warp.activeMask) match {
        case Bad(message) => failInvalid(message)
        case Lanes(values) if values.length == LaneCount =>
          writeMasked(warp.registers, destination, uniform(values(sourceLane.toInt)), warp.activeMask)
          retire(warp, rest)
        case _ => failInvalid("shfl.sync.idx source is not a lane vector")
      }
    }

    private def stepVoteAny(warp: Warp, destination: BigInt, predicate: Expr, rest: Position): Attempt = {
      if (warp.activeMask != FullMask) return failInvalid("vote.sync.any requires its fixed full-warp member mask")
      eval(warp, predicate, warp.activeMask) match {
        case Bad(message) => failInvalid(message)
        case Lanes(values) if values.length == LaneCount =>
          val result =
            if (values.indices.exists(index => laneActive(warp.activeMask, index) && values(index) != 0)) BigInt(1)
            else BigInt(0)
          writeMasked(warp.registers, destination, uniform(result), warp.activeMask)
          retire(warp, rest)
        case _ => failInvalid("vote.sync.any predicate is not a lane vector")
      }
    }

    private def stepMbarInit(warp: Warp, address: BigInt, expected: BigInt, rest: Position): Attempt = {
      if (!oneLaneActive(warp) || expected <= 0 || !device.sharedRange(address, 8, 8))
        return failInvalid(
          "mbarrier.init requires one active lane, a positive participant count, and a valid shared byte address"
        )
      findBarrier(address) match {
        case Some(barrier) if barrier.initialized => failInvalid("mbarrier.init reinitialized a live barrier")
        case _ =>
          barriers.update(address, Barrier(address, expected, 0, 0, 0, 0, 0, initialized = true, completedPhases = 0))
          retire(warp, rest)
      }
    }

    private def stepMbarInval(warp: Warp, address: BigInt, rest: Position): Attempt = {
      if (!oneLaneActive(warp)) return failInvalid("mbarrier.inval requires exactly one active lane")
      findBarrier(address) match {
        case None => failInvalid("mbarrier.inval used an unknown shared byte address")
        case Some(barrier) if !barrierQuiescent(barrier) || events.exists(eventUsesBarrier(_, address)) =>
          failInvalid("mbarrier.inval while the barrier phase or async events are live")
        case Some(barrier) =>
          barriers.update(
            address,
            barrier.copy(arrivals = 0, expectedBytes = 0, issuedBytes = 0, completedBytes = 0, initialized = false)
          )
          retire(warp, rest)
      }
    }

    private def stepMbarArrive(
        warp: Warp,
        address: BigInt,
        arrivals: BigInt,
        bytes: BigInt,
        rest: Position
    ): Attempt = {
      if (!oneLaneActive(warp)) return failInvalid("mbarrier.arrive requires exactly one active lane")
      findBarrier(address) match {
        case None => failInvalid("mbarrier.arrive used an unknown shared byte address")
        case Some(barrier) =>
          afterArrival(barrier, arrivals, bytes) match {
            case None          => failInvalid("mbarrier arrival count exceeds its initialized phase")
            case Some(changed) => barriers.update(address, changed); retire(warp, rest)
          }
      }
    }

    private def stepMbarWait(warp: Warp, address: BigInt, parity: BigInt, rest: Position): Attempt = {
      if (parity > 1) return failInvalid("mbarrier wait parity is not a one-bit value")
      findBarrier(address) match {
        case None => failInvalid("mbarrier.wait used an unknown shared byte address")
        case Some(barrier) if barrierWaitReady(barrier, parity) => retire(warp, rest)
        case Some(_)                                            => warp.status = BlockedMbar(address, parity); Waiting
      }
    }

    private def gateArrive(warp: Warp, gateId: BigInt, expected: BigInt, rest: Position): Attempt = {
      val participants = maskCount(warp.activeMask)
      if (expected <= 0 || expected > 256 || participants <= 0)
        return failInvalid("synchronization has an invalid participant count or empty active mask")
      val updated = gates.get(gateId) match {
        case None =>
          addGateArrival(Gate(gateId, expected, 0, 0, released = false), participants)
            .getOrElse(return failInvalid("synchronization arrival exceeds expected participants"))
        case Some(old) if old.expectedThreads != expected =>
          return failInvalid("synchronization id reused with a different participant count")
        case Some(old) =>
          addGateArrival(old, participants)
            .getOrElse(
              return failInvalid("synchronization arrival exceeds expected participants or overlaps a live epoch")
            )
      }
      gates.update(gateId, updated)
      warp.position = rest
      warp.status = BlockedGate(gateId)
      Progress
    }

    private def addGateArrival(gate: Gate, threads: BigInt): Option[Gate] = {
      if (gate.released || gate.arrivedThreads + threads > gate.expectedThreads) None
      else {
        val now = gate.arrivedThreads + threads
        if (now == gate.expectedThreads) Some(gate.copy(arrivedThreads = now, remainingThreads = now, released = true))
        else Some(gate.copy(arrivedThreads = now, remainingThreads = 0, released = false))
      }
    }

    private def stepMmaRequest(request: Request): Either[String, Completion] = request match {
      case Request.TmaLoad(map, destination, x, y) => device.load(map, destination, x, y)
      case Request.TmaStore(map, x, y, source)     => device.store(map, x, y, source)
      case Request.Mma(desc)                       => device.mma(desc)
      case Request.TmemLoad(shape, destinations, base, warpGroup, mask) =>
        device.tmemLoad(shape, destinations, base, warpGroup, mask)
    }

    private def retireHead(): Attempt = {
      if (events.isEmpty) return Waiting
      val event = events.remove(0)
      if (!event.committed) return Failed(Deadlocked)
      event match {
        case data: DataEvent =>
          stepMmaRequest(data.request) match {
            case Left(message) => Failed(DeviceFault(message))
            case Right(completion) =>
              if (data.request.isInstanceOf[Request.TmemLoad])
                // Match WarpMachine.appendRegisterWrites: prepend the newly completed batch, then publish head-to-tail.
                warps(data.warp).deferredLoads = completion.registerWrites ++ warps(data.warp).deferredLoads
              else
                completion.registerWrites.foreach(write =>
                  writeMasked(warps(data.warp).registers, write.id, write.lanes, maskFor(data.request))
                )
              if (!completeBarrierBytes(data.barrier, data.barrierPhase, completion.transferBytes))
                return failInvalid("data event completed more bytes than its live mbarrier expected")
              asyncCompletions += 1
              tmaBytes += completion.transferBytes
              scalarMuls += completion.scalarMuls
              scalarAdds += completion.scalarAdds
              data.request match {
                case _: Request.Mma      => mmaInstructions += 1
                case _: Request.TmemLoad => tmemLoads += 1
                case _: Request.TmaStore => tmaStores += 1
                case _: Request.TmaLoad  => ()
              }
              Progress
          }
        case commit: CommitEvent => retireCommit(commit)
      }
    }

    private def retireCommit(event: CommitEvent): Attempt = findBarrier(event.address) match {
      case None => failInvalid("tcgen05.commit arrived at an uninitialized mbarrier")
      case Some(barrier) if barrier.phase != event.phase =>
        failInvalid("tcgen05.commit completed against a different barrier phase")
      case Some(barrier) =>
        afterArrival(barrier, 1, 0) match {
          case None          => failInvalid("tcgen05.commit exceeded the mbarrier arrival count")
          case Some(updated) => barriers.update(event.address, updated); asyncCompletions += 1; Progress
        }
    }

    private def maskFor(request: Request): BigInt = request match {
      case Request.TmemLoad(_, _, _, _, mask) => mask
      case _                                  => FullMask
    }

    private def completeBarrierBytes(address: Option[BigInt], phase: BigInt, bytes: BigInt): Boolean = address match {
      case None => true
      case Some(got) =>
        findBarrier(got) match {
          case None                                    => false
          case Some(barrier) if barrier.phase != phase => false
          case Some(barrier) =>
            afterBytes(barrier, bytes) match {
              case None          => false
              case Some(updated) => barriers.update(got, updated); true
            }
        }
    }

    private def afterArrival(barrier: Barrier, arrivals: BigInt, txBytes: BigInt): Option[Barrier] = {
      if (!barrier.initialized || barrier.arrivals + arrivals > barrier.expectedArrivals) None
      else {
        val nextArrivals = barrier.arrivals + arrivals
        val nextExpectedBytes = barrier.expectedBytes + txBytes
        if (barrier.expectedArrivals <= nextArrivals && nextExpectedBytes <= barrier.completedBytes)
          Some(
            barrier.copy(
              arrivals = 0,
              expectedBytes = 0,
              issuedBytes = 0,
              completedBytes = 0,
              phase = (barrier.phase + 1) % 2,
              completedPhases = barrier.completedPhases + 1
            )
          )
        else Some(barrier.copy(arrivals = nextArrivals, expectedBytes = nextExpectedBytes))
      }
    }

    private def afterBytes(barrier: Barrier, bytes: BigInt): Option[Barrier] = {
      val nextDone = barrier.completedBytes + bytes
      if (!barrier.initialized || nextDone > barrier.issuedBytes || nextDone > barrier.expectedBytes) None
      else if (barrier.expectedArrivals <= barrier.arrivals && barrier.expectedBytes <= nextDone)
        Some(
          barrier.copy(
            arrivals = 0,
            expectedBytes = 0,
            issuedBytes = 0,
            completedBytes = 0,
            phase = (barrier.phase + 1) % 2,
            completedPhases = barrier.completedPhases + 1
          )
        )
      else Some(barrier.copy(completedBytes = nextDone))
    }

    private def scheduleBarrierBytes(barrier: Barrier, phase: BigInt, bytes: BigInt): Option[Barrier] =
      if (!barrier.initialized || phase != barrier.phase || barrier.issuedBytes + bytes > barrier.expectedBytes) None
      else Some(barrier.copy(issuedBytes = barrier.issuedBytes + bytes))

    private def barrierQuiescent(barrier: Barrier): Boolean =
      barrier.initialized && barrier.arrivals == 0 && barrier.expectedBytes == 0 && barrier.issuedBytes == 0 && barrier.completedBytes == 0

    private def barrierWaitReady(barrier: Barrier, parity: BigInt): Boolean =
      barrier.initialized && barrier.completedPhases > 0 && barrier.phase != parity

    private def findBarrier(address: BigInt): Option[Barrier] = barriers.get(address)

    private def eventUsesBarrier(event: Event, address: BigInt): Boolean = event match {
      case DataEvent(_, _, Some(bar), _, _) => bar == address
      case CommitEvent(_, bar, _)           => bar == address
      case _                                => false
    }

    private def storeEventsForWarp(warp: Int): BigInt =
      BigInt(events.count {
        case DataEvent(owner, request, _, _, _) => owner == warp && isStore(request)
        case _                                  => false
      })

    private def pendingTmemLoads(warp: Int): BigInt =
      BigInt(events.count {
        case DataEvent(owner, _: Request.TmemLoad, _, _, _) => owner == warp
        case _                                              => false
      })

    private def isStore(request: Request): Boolean = request.isInstanceOf[Request.TmaStore]

    private def oneLaneActive(warp: Warp): Boolean = maskCount(warp.activeMask) == 1

    private def retire(warp: Warp, rest: Position): Attempt = {
      warp.position = rest
      warp.status = Runnable
      warpSteps += 1
      Progress
    }

    private def failInvalid(message: String): Attempt = Failed(InvalidState(message))

    private def evalUniform(warp: Warp, expression: Expr): Option[BigInt] =
      eval(warp, expression, warp.activeMask) match {
        case Lanes(values) => uniformValue(values, warp.activeMask)
        case _             => None
      }

    private def evalAddress(warp: Warp, expression: Expr): Option[BigInt] =
      eval(warp, expression, warp.activeMask) match {
        case Lanes(values)          => uniformValue(values, warp.activeMask)
        case SharedPointer(_, base) => Some(base)
        case _                      => None
      }

    private def evalMap(warp: Warp, expression: Expr): Option[ResolvedMap] =
      eval(warp, expression, warp.activeMask) match {
        case ParameterAddress(name) => device.resolveMap(name)
        case _                      => None
      }

    private def evalOperand(warp: Warp, desc: SmemDesc): Option[OperandDesc] =
      evalAddress(warp, desc.base).map(base => OperandDesc(base, desc.lbo, desc.step))

    private def evalMmaA(warp: Warp, a: MmaA): Option[MmaSource] = a match {
      case MmaA.Smem(desc)    => evalOperand(warp, desc).map(MmaSource.Shared)
      case MmaA.Tmem(address) => evalUniform(warp, address).map(MmaSource.Tmem)
    }

    private def eval(warp: Warp, expression: Expr, activeMask: BigInt): EvalValue = {
      if (activeMask == 0) return Lanes(Vector.fill(LaneCount)(BigInt(0)))
      expression match {
        case Expr.Var(id) =>
          warp.registers.get(id) match {
            case None                                                  => Bad("read of an undeclared warp register")
            case Some(register) if register.values.length != LaneCount => Bad("warp register is not a 32-lane vector")
            case Some(register) if !maskCovers(register.initializedMask, activeMask) =>
              Bad("warp register read includes an uninitialized active lane")
            case Some(register) => Lanes(register.values)
          }
        case Expr.Lit(value)   => Lanes(uniform(value))
        case Expr.Lit64(value) => Lanes(uniform(value))
        case Expr.Zero(_)      => Lanes(uniform(0))
        case Expr.Param(name) =>
          dimension(name).fold[EvalValue](Bad("unsupported scalar parameter"))(value => Lanes(uniform(value)))
        case Expr.Special(builtin) => Lanes(specialValues(builtin, warp.id))
        case Expr.Bin(BinOp.Land, left, right) =>
          eval(warp, left, activeMask) match {
            case Bad(message) => Bad(message)
            case Lanes(leftValues) =>
              val (rightMask, _) = splitMask(leftValues, activeMask)
              eval(warp, right, rightMask) match {
                case Bad(message)       => Bad(message)
                case Lanes(rightValues) => vectorBinary(BinOp.Land, leftValues, rightValues, activeMask)
                case _                  => Bad("logical expression operand is not a lane vector")
              }
            case _ => Bad("binary expression operand is not a lane vector")
          }
        case Expr.Bin(op, left, right) =>
          eval(warp, left, activeMask) match {
            case Bad(message) => Bad(message)
            case Lanes(leftValues) =>
              eval(warp, right, activeMask) match {
                case Bad(message)       => Bad(message)
                case Lanes(rightValues) => vectorBinary(op, leftValues, rightValues, activeMask)
                case _                  => Bad("binary expression operand is not a lane vector")
              }
            case _ => Bad("binary expression operand is not a lane vector")
          }
        case Expr.Max(left, right) =>
          (eval(warp, left, activeMask), eval(warp, right, activeMask)) match {
            case (Lanes(a), Lanes(b)) if a.length == b.length =>
              Lanes(
                a.indices
                  .map(index => if (laneActive(activeMask, index)) a(index).max(b(index)) else BigInt(0))
                  .toVector
              )
            case (Bad(message), _) => Bad(message)
            case (_, Bad(message)) => Bad(message)
            case _                 => Bad("max expression has mismatched lane widths")
          }
        case Expr.Fma(_, _, _) => Bad("floating-point FMA is outside the exact-ring expression subset")
        case Expr.Select(condition, yes, no) =>
          eval(warp, condition, activeMask) match {
            case Bad(message) => Bad(message)
            case Lanes(conditions) =>
              val (yesMask, noMask) = splitMask(conditions, activeMask)
              mergeSelected(eval(warp, yes, yesMask), eval(warp, no, noMask), yesMask, noMask)
            case _ => Bad("select condition is not a lane vector")
          }
        case Expr.Index(base, index) =>
          eval(warp, base, activeMask) match {
            case Bad(message) => Bad(message)
            case SharedPointer(tpe, byteBase) =>
              sharedWidth(tpe) match {
                case None => Bad("shared pointer dtype is outside the supported load subset")
                case Some(width) =>
                  eval(warp, index, activeMask) match {
                    case Lanes(indices) if indices.length == LaneCount =>
                      val addresses = indices.map(value => byteBase + value * width)
                      device.readSharedLanes(addresses, activeMask, tpe) match {
                        case Some(values) => Lanes(values)
                        case None         => Bad("shared-memory index is out of bounds or misaligned")
                      }
                    case Bad(message) => Bad(message)
                    case _            => Bad("shared pointer index is not a 32-lane vector")
                  }
              }
            case ParameterAddress(_) => Bad("indexing parameter addresses is unsupported in TinyGEMM")
            case Lanes(_)            => Bad("index base is a value vector, not a typed pointer")
          }
        case Expr.Cast(tpe, value) =>
          eval(warp, value, activeMask) match {
            case Bad(message)  => Bad(message)
            case Lanes(values) => castValues(tpe, values, activeMask)
            case _             => Bad("cast operand is not a lane vector")
          }
        case Expr.SharedAddr(offset)     => Lanes(uniform(offset))
        case Expr.SharedPtr(tpe, offset) => SharedPointer(tpe, offset)
        case Expr.ParamAddr(name)        => ParameterAddress(name)
      }
    }

    private def mergeSelected(yes: EvalValue, no: EvalValue, yesMask: BigInt, noMask: BigInt): EvalValue = {
      if (maskCount(yesMask) == 0) no
      else if (maskCount(noMask) == 0) yes
      else
        (yes, no) match {
          case (Lanes(a), Lanes(b)) if a.length == b.length =>
            Lanes(a.indices.map(index => if (laneActive(yesMask, index)) a(index) else b(index)).toVector)
          case (ParameterAddress(a), ParameterAddress(b)) if a == b => ParameterAddress(a)
          case (SharedPointer(tpeA, baseA), SharedPointer(tpeB, baseB)) if tpeA == tpeB && baseA == baseB =>
            SharedPointer(tpeA, baseA)
          case (Bad(message), _)                          => Bad(message)
          case (_, Bad(message))                          => Bad(message)
          case (_: Lanes, _: Lanes)                       => Bad("select expressions have mismatched lane widths")
          case (_: ParameterAddress, _: ParameterAddress) => Bad("lane-varying parameter addresses are unsupported")
          case (_: SharedPointer, _: SharedPointer)       => Bad("lane-varying shared pointers are unsupported")
          case _                                          => Bad("select expressions have incompatible value kinds")
        }
    }

    private def vectorBinary(op: BinOp, left: Vector[BigInt], right: Vector[BigInt], mask: BigInt): EvalValue = {
      if (left.length != right.length) return Bad("binary expression has mismatched lane widths")
      val output = Vector.tabulate(left.length) { lane =>
        if (!laneActive(mask, lane)) BigInt(0)
        else
          binary(op, left(lane), right(lane)) match {
            case Some(value) => value
            case None        => return Bad("integer division by zero in a warp expression")
          }
      }
      Lanes(output)
    }

    private def binary(op: BinOp, left: BigInt, right: BigInt): Option[BigInt] = op match {
      case BinOp.Add  => Some(left + right)
      case BinOp.Sub  => Some((left - right).max(BigInt(0)))
      case BinOp.Mul  => Some(left * right)
      case BinOp.Div  => if (right == 0) None else Some(left / right)
      case BinOp.Rem  => if (right == 0) None else Some(left % right)
      case BinOp.Lt   => Some(if (left < right) 1 else 0)
      case BinOp.Eq   => Some(if (left == right) 1 else 0)
      case BinOp.Land => Some(if (left != 0 && right != 0) 1 else 0)
      case BinOp.Shl  => Some(if (right >= 64) BigInt(0) else left << right.toInt)
      case BinOp.Shr  => Some(if (right >= 64) BigInt(0) else left >> right.toInt)
      case BinOp.Bor  => Some((left | right) & (U64Limit - 1))
      case BinOp.Band => Some((left & right) & (U64Limit - 1))
      case BinOp.Bxor => Some((left ^ right) & (U64Limit - 1))
    }

    private def castValues(tpe: DType, values: Vector[BigInt], mask: BigInt): EvalValue = {
      val limit = tpe match {
        case DType.U32  => Some(U32Limit)
        case DType.U64  => Some(U64Limit)
        case DType.Bool => None
        case _          => return Bad("floating-point casts are outside the exact-ring expression subset")
      }
      Lanes(values.indices.map { lane =>
        if (!laneActive(mask, lane)) BigInt(0)
        else if (tpe == DType.Bool) if (values(lane) == 0) BigInt(0) else BigInt(1)
        else values(lane) % limit.get
      }.toVector)
    }

    private def dimension(name: String): Option[BigInt] = name match {
      case "M" => Some(plan.metadata.m)
      case "N" => Some(plan.metadata.n)
      case "K" => Some(plan.metadata.k)
      case _   => None
    }

    private def specialValues(builtin: Builtin, warpId: Int): Vector[BigInt] = builtin match {
      case Builtin.ThreadX                 => Vector.tabulate(LaneCount)(lane => BigInt(warpId * LaneCount + lane))
      case Builtin.BlockX | Builtin.BlockY => uniform(0)
      case Builtin.GridX                   => uniform(1)
      case Builtin.Warp                    => uniform(warpId)
      case Builtin.Lane                    => Vector.tabulate(LaneCount)(BigInt(_))
    }

    private def sharedWidth(tpe: DType): Option[BigInt] = tpe match {
      case DType.U32 | DType.F32 => Some(BigInt(4))
      case DType.BF16            => Some(BigInt(2))
      case _                     => None
    }

    private def splitMask(values: Vector[BigInt], mask: BigInt): (BigInt, BigInt) = {
      var yes = BigInt(0)
      var no = BigInt(0)
      var lane = 0
      while (lane < values.length && lane < LaneCount) {
        if (laneActive(mask, lane)) {
          if (values(lane) == 0) no |= BigInt(1) << lane else yes |= BigInt(1) << lane
        }
        lane += 1
      }
      (yes, no)
    }

    private def uniformValue(values: Vector[BigInt], mask: BigInt): Option[BigInt] = {
      var found: Option[BigInt] = None
      var lane = 0
      while (lane < values.length && lane < LaneCount) {
        if (laneActive(mask, lane)) found match {
          case None                                       => found = Some(values(lane))
          case Some(previous) if previous != values(lane) => return None
          case _                                          => ()
        }
        lane += 1
      }
      found
    }

    private def loopMask(values: Vector[BigInt], stops: Vector[BigInt], parent: BigInt): BigInt = {
      var result = BigInt(0)
      var lane = 0
      while (lane < LaneCount) {
        if (laneActive(parent, lane) && values(lane) < stops(lane)) result |= BigInt(1) << lane
        lane += 1
      }
      result
    }

    private def addLoopValues(values: Vector[BigInt], steps: Vector[BigInt], mask: BigInt): Vector[BigInt] =
      values.indices.map(index => if (laneActive(mask, index)) values(index) + steps(index) else values(index)).toVector

    private def writeMasked(
        registers: mutable.Map[BigInt, Register],
        id: BigInt,
        values: Vector[BigInt],
        mask: BigInt
    ): Unit = {
      val padded = if (values.length == LaneCount) values else Vector.fill(LaneCount)(BigInt(0))
      registers.get(id) match {
        case None => registers.update(id, Register(padded, mask))
        case Some(old) =>
          val merged =
            Vector.tabulate(LaneCount)(lane => if (laneActive(mask, lane)) padded(lane) else old.values(lane))
          registers.update(id, Register(merged, maskUnion(old.initializedMask, mask)))
      }
    }

    private def maskUnion(left: BigInt, right: BigInt): BigInt = (left | right) & FullMask
    private def maskCovers(available: BigInt, required: BigInt): Boolean =
      (available & FullMask) == available && (required & FullMask) == required && (required & ~available) == 0
    private def maskCount(mask: BigInt): Int = (mask & FullMask).bitCount
    private def laneActive(mask: BigInt, lane: Int): Boolean = ((mask >> lane) & 1) != 0
    private def uniform(value: BigInt): Vector[BigInt] = Vector.fill(LaneCount)(value)

  }

  def run(plan: Plan, inputs: Inputs, fuel: BigInt): Result = new Run(plan, inputs, fuel).execute()
}
