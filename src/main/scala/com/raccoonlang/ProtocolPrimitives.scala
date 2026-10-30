package com.raccoonlang

import com.raccoonlang.Value._

/**
 * The reductions of the resource-protocol primitives (docs/kernel.md, "Resource protocols"), which `Builtins` publishes
 * as the natives `Protocol.new`, `Protocol.step` and `Protocol.observe`:
 *
 *   - R1: `new(P, init, supply#(n))` is `Fresh.mk(supply#(n + 1), i, canon(i, init))`, where `i` is
 *     `inst#(P, init, n)`;
 *   - R2: `step(P, init, s, A, B, h, toks)` is `canon(s, B)`;
 *   - R3: `observe(P, init, s, C, toks)` is `Observed.mk(toks, valid#(P, init, C))`;
 *
 * where `canon(s, [])` is `Toks.nil` and `canon(s, a :: C)` is `Toks.cons(a, tok#(P, init, s, a), C, canon(s, C))`. R1
 * fires on a canonical supply and a known initial list, and R2 on a known output list; a known list is `nil` or a chain
 * of conses ending in `nil`, whatever its elements. Otherwise the application is stuck, blocked on the supply's and the
 * list's reduction blockers, and `Interpreter.resolveInEqStore` re-runs it once one is solved, as it does
 * `List.append`. R3 always fires. R2 and R3 ignore their input packet's contents: tokens carry no data.
 *
 * The ghosts `supply#`, `inst#`, `tok#` and `valid#` are built only here. The root supply exists only once
 * `Interpreter.run` applies an entry, after checking it, and only R1 makes another supply, so checking never allocates:
 * during checking every supply is a variable or stuck, and R1 never fires. R2 and R3 do fire during checking. A type or
 * proof may contain a primitive application, since a read extent may compute with live linear values (S1), and then
 * converts by these reductions. That is sound because a read consumes nothing and its value is a type or a proof, which
 * no linear binder receives, and because each call in it takes linear inputs from disjoint regions of locals that were
 * live together (`Ledger.call`). So an `observe` in a type or proof reads a packet the program could observe at that
 * point, and the `valid#` it returns holds: `observe(join(t, t))` is refused.
 */
private[raccoonlang] object ProtocolPrimitives {
  private val SupplyName = "supply#"

  // A ghost's own type is `KernelObject`: no term applies a ghost, and each application carries its precise type.
  private def ghost(name: String): VConst = VConst(name, Ghost, KernelObject)
  private val SupplyGhost = ghost(SupplyName)
  private val InstGhost = ghost("inst#")
  private val TokGhost = ghost("tok#")
  private val ValidGhost = ghost("valid#")

  private def supply(n: Value): Value = VApp(SupplyGhost, Vector(n), Kernel.supplyType)

  /** The root supply, `supply#(0)`, which `Interpreter.run` gives an entry. */
  lazy val rootSupply: Value = supply(Kernel.zeroValue)

  /**
   * The number `n` of `sup` when it is a canonical supply `supply#(n)`, or else the reduction blockers of the stuck
   * supply. Every supply ghost is canonical: R1 and the root build them.
   */
  private def supplyNumber(sup: Value): Either[DepSet, Value] =
    sup match {
      case VApp(VConst(SupplyName, Ghost, _), Vector(n), _, _) => Right(n)
      case stuck                                               => Left(ReductionBlockers.of(stuck))
    }

  /** A known list: each cons cell as its element and the cell itself, in order, then the `nil` that ends it. */
  private final case class KnownList(cells: Vector[(Value, Value)], nil: Value)

  /** The spine of `list` when it is known, or else the reduction blockers of the stuck value that ends it. */
  private def knownList(list: Value): Either[DepSet, KnownList] = {
    val cells = Vector.newBuilder[(Value, Value)]
    var rest = list
    while (!Kernel.isListNil(rest))
      rest match {
        // A `List` value with two stored fields is a cons.
        case cell @ ConstructorValue(_, Vector(head, tail)) =>
          cells += (head -> cell)
          rest = tail
        case stuck => return Left(ReductionBlockers.of(stuck))
      }
    Right(KnownList(cells.result(), rest))
  }

  private def toksType(proto: Value, init: Value, s: Value, atoms: Value): Value =
    Interpreter.evalApply(Kernel.toksFamily, Vector(proto, init, s, atoms))

  /** `canon(s, list)`: a fresh token of `s` for each atom, built from the back, each cons typed by its own cell. */
  private def canon(proto: Value, init: Value, s: Value, list: KnownList): Value = {
    var packet = ConstructorValue(Kernel.toksNil, Vector.empty, toksType(proto, init, s, list.nil))
    var tail = list.nil
    list.cells.reverseIterator.foreach { case (a, cell) =>
      val tokType = Interpreter.evalApply(Kernel.tokFamily, Vector(proto, init, s, a))
      val token = VApp(TokGhost, Vector(proto, init, s, a), tokType)
      packet = ConstructorValue(Kernel.toksCons, Vector(a, token, tail, packet), toksType(proto, init, s, cell))
      tail = cell
    }
    packet
  }

  /** R1, for `new(P, init, sup)`. */
  def allocate(self: VLam, args: Vector[Value]): Value = {
    val (proto, init, sup) = (args(0), args(1), args(2))
    val freshType = Interpreter.evalApply(Kernel.freshFamily, Vector(proto, init))
    (supplyNumber(sup), knownList(init)) match {
      case (Right(n), Right(list)) =>
        val instType = Interpreter.evalApply(Kernel.instFamily, Vector(proto, init))
        val identity = VApp(InstGhost, Vector(proto, init, n), instType)
        val packet = canon(proto, init, identity, list)
        ConstructorValue(Kernel.freshMk, Vector(supply(NatNormalForm.successor(n)), identity, packet), freshType)
      case (number, list) =>
        val blockers = number.left.getOrElse(DepSet.empty) ++ list.left.getOrElse(DepSet.empty)
        VBlockedApp(self, args, freshType, blockers)
    }
  }

  /** R2, for `step(P, init, s, A, B, h, toks)`. */
  def step(self: VLam, args: Vector[Value]): Value = {
    val (proto, init, s, output) = (args(0), args(1), args(2), args(4))
    knownList(output) match {
      case Right(list)    => canon(proto, init, s, list)
      case Left(blockers) => VBlockedApp(self, args, toksType(proto, init, s, output), blockers)
    }
  }

  /** R3, for `observe(P, init, s, C, toks)`. */
  def observe(args: Vector[Value]): Value = {
    val (proto, init, s, atoms, toks) = (args(0), args(1), args(2), args(3), args(4))
    val validType = Interpreter.evalApply(Kernel.validFamily, Vector(proto, init, atoms))
    val valid = VApp(ValidGhost, Vector(proto, init, atoms), validType)
    val observedType = Interpreter.evalApply(Kernel.observedFamily, Vector(proto, init, s, atoms))
    ConstructorValue(Kernel.observedMk, Vector(toks, valid), observedType)
  }
}
