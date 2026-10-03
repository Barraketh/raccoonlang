package com.raccoonlang

import com.raccoonlang.CoreAst.{Term => CTerm}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/** The Core evaluator. Plans hold syntax and addresses, never live values or environments. */
private[raccoonlang] object PreparedEval {
  private sealed trait Node {
    def scope: Scope
  }
  private final case class Ref(local: CoreAst.LocalRef, slot: Int, scope: Scope) extends Node
  private final case class Global(name: String, scope: Scope) extends Node
  private final case class NatLiteral(value: BigInt, scope: Scope) extends Node
  private final case class StringLiteral(scalars: Vector[Int], scope: Scope) extends Node
  private final case class Application(
      fn: Node,
      args: Vector[Node],
      fnSlot: Int,
      argStart: Int,
      tail: Boolean,
      scope: Scope
  ) extends Node
  private final case class Binding(
      value: Node,
      pattern: CoreAst.LetPattern,
      slots: Vector[Int],
      next: Node,
      scope: Scope
  ) extends Node
  private final case class Matching(
      term: CTerm.Match,
      scrut: Node,
      cases: Map[String, Branch],
      scope: Scope
  ) extends Node
  private final case class Branch(source: CoreAst.Case, body: Node, slots: Vector[Int])
  private final case class PiValue(term: CTerm.Pi, scope: Scope) extends Node
  private final case class LambdaValue(term: CTerm.Lam, scope: Scope) extends Node
  private final case class Scoped(term: CTerm.Scope, body: Node, slot: Int, scope: Scope) extends Node
  private final case class Proposition(scopeTerm: Node, scope: Scope) extends Node
  private final case class SortValue(
      level: Node,
      kind: Node,
      lifetime: Node,
      levelSlot: Int,
      kindSlot: Int,
      scope: Scope
  ) extends Node
  private final case class FormValue(form: CoreAst.Form, args: Vector[Node], start: Int, scope: Scope) extends Node
  private final case class UnresolvedSelect(field: String, scope: Scope) extends Node

  /** Chronological local order is kept separately from the address map for exact Env/ValueId materialization. */
  private final case class Scope(
      refs: Vector[CoreAst.LocalRef],
      slots: Vector[Int],
      addresses: Map[CoreAst.LocalRef, Int]
  ) {
    lazy val layout: RuntimeSlotLayout = RuntimeSlotLayout(refs)
    def bind(refsToBind: Vector[CoreAst.LocalRef], allocate: () => Int): (Scope, Vector[Int]) = {
      val assigned = refsToBind.map(_ => allocate())
      (
        Scope(refs ++ refsToBind, slots ++ assigned, addresses ++ refsToBind.zip(assigned)),
        assigned
      )
    }
  }

  private final case class Plan(root: Node, slots: Int, boundRefs: Vector[CoreAst.LocalRef], duplicateBindings: Boolean)
  private val emptyPlan = Plan(null, 0, Vector.empty, duplicateBindings = false)

  private final class Compiler {
    private var size = 0
    private var highWater = 0
    private var allBindings = Set.empty[CoreAst.LocalRef]
    private var duplicateBindings = false
    private def allocate(): Int = {
      val result = size
      size += 1
      highWater = math.max(highWater, size)
      result
    }
    def compile(
        term: CTerm,
        binders: Vector[CoreAst.LocalRef] = Vector.empty,
        peers: Vector[CoreAst.LocalRef] = Vector.empty
    ): Plan = {
      val initial = Scope(Vector.empty, Vector.empty, Map.empty)
      def bind(scope: Scope, refs: Vector[CoreAst.LocalRef]): Scope = {
        noteBindings(refs, scope)
        scope.bind(refs, () => allocate())._1
      }
      val withBinders = bind(initial, binders)
      val withPeers = bind(withBinders, peers)
      val root = node(term, withPeers, tail = true)
      Plan(root, highWater, allBindings.toVector, duplicateBindings)
    }

    private def noteBindings(refs: Vector[CoreAst.LocalRef], scope: Scope): Unit = {
      if (refs.distinct.length != refs.length || refs.exists(scope.addresses.contains)) duplicateBindings = true
      allBindings ++= refs
    }

    private def node(term: CTerm, scope: Scope, tail: Boolean): Node = {
      // Parent-owned operand blocks sit below entrySize. Rewind only this subtree's region; lexical binders
      // remain pinned while their body is compiled, and highWater preserves the plan's maximum address.
      val entrySize = size
      try
        term match {
          case CTerm.LocalRef(ref, _)   => Ref(ref, scope.addresses.getOrElse(ref, -1), scope)
          case CTerm.GlobalRef(name, _) => Global(name, scope)
          case CTerm.NatLit(value, _)   => NatLiteral(value, scope)
          case CTerm.StrLit(scalars, _) => StringLiteral(scalars, scope)
          case CTerm.App(fn, args, _, _) =>
            val fnSlot = allocate()
            val argStart = size
            args.foreach(_ => allocate())
            Application(
              node(fn, scope, tail = false),
              args.map(node(_, scope, tail = false)),
              fnSlot,
              argStart,
              tail,
              scope
            )
          case body: CTerm.Body =>
            def chain(index: Int, active: Scope): Node =
              if (index == body.lets.length) node(body.res, active, tail)
              else {
                val let = body.lets(index)
                val refs = let.pattern match {
                  case CoreAst.LetPattern.Local(ref)     => Vector(ref)
                  case fields: CoreAst.LetPattern.Fields => fields.vars.map(_.ref)
                }
                noteBindings(refs, active)
                val (nextScope, slots) = active.bind(refs, () => allocate())
                Binding(node(let.value, active, tail = false), let.pattern, slots, chain(index + 1, nextScope), active)
              }
            chain(0, scope)
          case m: CTerm.Match =>
            // Scrutinee temporaries die before the selected case starts; cases are mutually exclusive.
            // Environments that escape evaluation copy their values into immutable snapshots.
            val regionStart = size
            val branches = m.cases
              .map { branch =>
                size = regionStart
                val refs = branch.argRefs ++ m.equation.map(_.ref).toVector
                noteBindings(refs, scope)
                val (branchScope, slots) = scope.bind(refs, () => allocate())
                val body = node(branch.body, branchScope, tail)
                branch.ctorName -> Branch(branch, body, slots)
              }
              .reverse
              .toMap
            size = regionStart
            val scrut = node(m.scrut, scope, tail = false)
            Matching(m, scrut, branches, scope)
          case pi: CTerm.Pi   => PiValue(pi, scope)
          case lam: CTerm.Lam => LambdaValue(lam, scope)
          case s: CTerm.Scope =>
            noteBindings(Vector(s.ref), scope)
            val (inner, slots) = scope.bind(Vector(s.ref), () => allocate())
            Scoped(s, node(s.body, inner, tail), slots.head, scope)
          case CTerm.Prop(lifetime, _) => Proposition(node(lifetime, scope, tail = false), scope)
          case CTerm.Sort(level, kind, lifetime, _) =>
            val levelSlot = allocate()
            val kindSlot = allocate()
            SortValue(
              node(level, scope, tail = false),
              node(kind, scope, tail = false),
              node(lifetime, scope, tail = false),
              levelSlot,
              kindSlot,
              scope
            )
          case CTerm.FormOp(form, args, _) =>
            val start = size
            args.foreach(_ => allocate())
            FormValue(form, args.map(node(_, scope, tail = false)), start, scope)
          case CTerm.Select(_, field, _) => UnresolvedSelect(field, scope)
        }
      finally size = entrySize
    }
  }

  /** Compatibility handle; ordinary and prepared entry points use the same machine. */
  final class Prepared private[PreparedEval] (val function: VLam) {
    def run(args: Vector[Value]): Value = evalApply(function, args)
  }

  private final class Runtime {
    // Reentrant helper/native calls get isolated banks; only the usual shallow nesting is retained.
    private val retainedSessions = 8
    private val terms = new java.util.IdentityHashMap[CTerm, Plan]()
    private val functions = new java.util.IdentityHashMap[CTerm.Lam, Plan]()
    private val sessions = scala.collection.mutable.ArrayBuffer.empty[EvalSession]
    private var active = 0

    def plan(term: CTerm): Plan = {
      val cached = terms.get(term)
      if (cached ne null) cached
      else {
        // This cache is thread-local, bounded, and stores syntax/layout only. In particular it does
        // not hold a checking context, a closure, or a reusable slot array.
        if (terms.size() >= 4096) terms.clear()
        val built = new Compiler().compile(term)
        terms.put(term, built)
        built
      }
    }

    def functionPlan(term: CTerm.Lam): Plan = {
      val cached = functions.get(term)
      if (cached ne null) cached
      else {
        if (functions.size() >= 4096) functions.clear()
        val built = new Compiler().compile(term.body, term.ty.binders.map(_.localRef), term.recursivePeers.map(_._1))
        functions.put(term, built)
        built
      }
    }

    def withSession[A](f: EvalSession => A): A = {
      if (active == sessions.length && active < retainedSessions) sessions += new EvalSession(this)
      val session = if (active < retainedSessions) sessions(active) else new EvalSession(this)
      active += 1
      try f(session)
      finally active -= 1
    }
  }

  private val runtime = new ThreadLocal[Runtime] {
    override def initialValue(): Runtime = new Runtime
  }

  private def nullaryConstructor(value: Value): Value =
    value match {
      case head: ConstructorHead if head.totalArity == 0 => Packed.construct(head, Vector.empty, head.tpe)
      case other                                         => other
    }

  // Root references have no active lexical slots. Use the same read rule as the machine's boxed
  // reference handler without allocating a plan, frame, and nested session for each checker lookup.
  def evalTerm(term: CTerm, env: Env): Value =
    term match {
      case CTerm.LocalRef(ref, _)   => nullaryConstructor(env(ref))
      case CTerm.GlobalRef(name, _) => nullaryConstructor(env(name))
      case CTerm.FormOp(form, args, _) if args.isEmpty =>
        Interpreter.evalFormOp(form, Vector.empty)
      case CTerm.Prop(CTerm.FormOp(form, args, _), _) if args.isEmpty =>
        Sorts.prop(Interpreter.getLifetime(Interpreter.evalFormOp(form, Vector.empty)))
      case CTerm.Sort(
            CTerm.FormOp(levelForm, levelArgs, _),
            CTerm.FormOp(kindForm, kindArgs, _),
            CTerm.FormOp(lifetimeForm, lifetimeArgs, _),
            _
          ) if levelArgs.isEmpty && kindArgs.isEmpty && lifetimeArgs.isEmpty =>
        val level = Interpreter.getLevel(Interpreter.evalFormOp(levelForm, Vector.empty))
        val kind = Interpreter.getKind(Interpreter.evalFormOp(kindForm, Vector.empty))
        val lifetime = Interpreter.getLifetime(Interpreter.evalFormOp(lifetimeForm, Vector.empty))
        Sorts.sort(level, kind, lifetime)
      case _ => runtime.get().withSession(_.runTerm(term, env))
    }
  def evalApply(fn: Value, args: Vector[Value]): Value = runtime.get().withSession(_.runApply(fn, args, null))
  def evalValidatedStringAppend(layout: SourceStringLayout, chars: VPacked): Value =
    runtime.get().withSession(_.runApply(layout.stringMk, Vector(chars), layout))

  def prepare(function: Value): Option[Prepared] =
    function match {
      case lam: VLam if eligible(lam) =>
        Some(new Prepared(lam))
      case _ => None
    }

  private def eligible(lam: VLam): Boolean =
    lam.body match {
      case LamBody.Core(term, _) =>
        val actual = lam.tpe.binders
        val syntax = term.ty.binders
        if (
          lam.tpe.isPropValued || actual.isEmpty || !term.ty.knownPropValued.contains(false) ||
          actual.length != syntax.length
        ) false
        else {
          var i = 0
          while (i < actual.length && actual(i).localRef == syntax(i).localRef) i += 1
          i == actual.length
        }
      case _ => false
    }

  private final class Frame {
    var base: Int = 0
    var env: Env = Env.empty
    var plan: Plan = null
    var boxed: Boolean = false
  }

  /** Reuses its banks across calls. Slots are never published; escaping values receive an immutable Env snapshot. */
  private[raccoonlang] final class EvalSession(runtime: Runtime) {
    // A null natTypes entry reads values directly. Non-null entries carry a nonnegative Nat payload and
    // its exact validated type; a null bigs entry selects the Long payload, otherwise the BigInt payload.
    // values may cache one immutable VPacked for repeated generic reads. Native calls bridge a boxed Value or small Nat;
    // BigInt literals and slots stay in the loop's local result fields.
    // Validate at literal/native introduction, then transfer payloads unchanged; generic and escape paths box once.
    private var values = new Array[Value](256)
    private var longs = new Array[Long](256)
    private var bigs = new Array[BigInt](256)
    private var natTypes = new Array[Value](256)
    private var frames = Array.fill(32)(new Frame)
    private var frameDepth = 0
    // An activation's exact immutable closure determines slot eligibility. Keep this only for
    // the current evaluation; neither values nor environments enter the syntax-plan cache.
    private val fastClosures = new java.util.IdentityHashMap[VLam, Plan]()
    private var tailArguments = new Array[Value](8)
    private var tailLongs = new Array[Long](8)
    private var tailBigs = new Array[BigInt](8)
    private var tailNatTypes = new Array[Value](8)

    // Kind and metadata are parallel arrays so the interpreter allocates no continuation objects per step.
    private var kinds = new Array[Int](256)
    private var nodes = new Array[Node](256)
    private var indices = new Array[Int](256)
    private var savedEnvs = new Array[Env](256)
    private var depth = 0
    private var appliedNode: Node = null
    private var resultValue: Value = null
    private var resultLong: Long = 0L
    private var resultNatType: Value = null

    private val AppFunction = 1
    private val AppArgument = 2
    private val LetValue = 3
    private val MatchScrutinee = 4
    private val Return = 5
    private val PropLifetime = 6
    private val SortLevel = 7
    private val SortKind = 8
    private val SortLifetime = 9
    private val FormArgument = 10
    private val RestoreEnv = 11

    private def ensureSlots(required: Int): Unit =
      if (required > values.length) {
        val capacity = math.max(required, values.length * 2)
        values = java.util.Arrays.copyOf(values, capacity)
        longs = java.util.Arrays.copyOf(longs, capacity)
        bigs = java.util.Arrays.copyOf(bigs, capacity)
        natTypes = java.util.Arrays.copyOf(natTypes, capacity)
      }

    private def push(kind: Int, node: Node, index: Int = 0): Unit = {
      if (depth == kinds.length) {
        val capacity = kinds.length * 2
        kinds = java.util.Arrays.copyOf(kinds, capacity)
        nodes = java.util.Arrays.copyOf(nodes, capacity)
        indices = java.util.Arrays.copyOf(indices, capacity)
        savedEnvs = java.util.Arrays.copyOf(savedEnvs, capacity)
      }
      kinds(depth) = kind
      nodes(depth) = node
      indices(depth) = index
      depth += 1
    }

    private def readValue(slot: Int): Value =
      if (natTypes(slot) eq null) values(slot)
      else if (values(slot) ne null) values(slot)
      else {
        val ty = natTypes(slot)
        val value = VPacked.nat(if (bigs(slot) eq null) BigInt(longs(slot)) else bigs(slot), ty)
        values(slot) = value
        value
      }

    private def writeValue(slot: Int, value: Value): Unit = {
      if (natTypes(slot) ne null) {
        bigs(slot) = null
        natTypes(slot) = null
      }
      values(slot) = value
    }

    private def writeNat(slot: Int, value: BigInt, ty: Value, cached: Value): Unit = {
      // `ty` comes from a validated Nat capability and `value` from a checked VPacked Nat.
      if (value.signum < 0) wtf("Tagged Nat must be nonnegative")
      val small = value.isValidLong
      longs(slot) = if (small) value.longValue else 0L
      bigs(slot) = if (small) null else value
      natTypes(slot) = ty
      values(slot) = cached
    }

    private def clearResult(): Unit = {
      resultNatType = null
      resultValue = null
    }

    private def setValueResult(value: Value): Unit = {
      resultNatType = null
      resultValue = value
    }

    private def setLongResult(value: Long, ty: Value): Unit = {
      if (value < 0) wtf("Tagged Nat result must be nonnegative")
      resultLong = value
      resultNatType = ty
      resultValue = null
    }

    private def writeResult(slot: Int, value: Value, ty: Value, small: Long, big: BigInt): Unit = {
      if (ty eq null) writeValue(slot, value)
      else {
        values(slot) = value
        longs(slot) = small
        bigs(slot) = big
        natTypes(slot) = ty
      }
    }

    private def copySlot(source: Int, target: Int): Unit = {
      if (natTypes(source) eq null) writeValue(target, values(source))
      else {
        values(target) = values(source)
        longs(target) = longs(source)
        bigs(target) = bigs(source)
        natTypes(target) = natTypes(source)
      }
    }

    /** A negative sentinel means the slot needs the ordinary boxed native path. */
    private def natLongOrMiss(slot: Int, ty: Value): Long =
      if (natTypes(slot) ne null) {
        if ((natTypes(slot).asInstanceOf[AnyRef] eq ty.asInstanceOf[AnyRef]) && (bigs(slot) eq null)) longs(slot)
        else -1L
      } else {
        values(slot) match {
          case packed: VPacked
              if (packed.codec eq NatCodec) &&
                (packed.tpe.asInstanceOf[AnyRef] eq ty.asInstanceOf[AnyRef]) =>
            val n = PackedPayload.natValue(packed.payload)
            if (n.isValidLong) {
              writeNat(slot, n, ty, packed)
              n.longValue
            } else -1L
          case _ => -1L
        }
      }

    private def tryScalarApplication(lam: VLam, app: Application, caller: Frame): Boolean = {
      if (app.args.length != 2) return false
      val capability = Packed.scalarNatCapability(lam, caller.env) match {
        case Some(value) => value
        case None        => return false
      }
      val ty = capability.natTpe
      val left = natLongOrMiss(caller.base + app.argStart, ty)
      val right = natLongOrMiss(caller.base + app.argStart + 1, ty)
      if (left < 0 || right < 0) return false
      val result = capability.kind match {
        case Packed.ScalarNatKind.Add =>
          if (left > Long.MaxValue - right) return false
          left + right
        case Packed.ScalarNatKind.Sub => if (left < right) 0L else left - right
        case Packed.ScalarNatKind.Mul =>
          if (right != 0 && left > Long.MaxValue / right) return false
          left * right
        case Packed.ScalarNatKind.Div => if (right == 0) 0L else left / right
        case Packed.ScalarNatKind.Mod => if (right == 0) left else left % right
        case Packed.ScalarNatKind.Beq =>
          setValueResult(if (left == right) capability.yes else capability.no)
          return true
        case Packed.ScalarNatKind.Ble =>
          setValueResult(if (left <= right) capability.yes else capability.no)
          return true
        case Packed.ScalarNatKind.Blt =>
          setValueResult(if (left < right) capability.yes else capability.no)
          return true
      }
      setLongResult(result, ty)
      true
    }

    private def bind(slot: Int, value: Value): Unit = {
      val canonical = Value.canonicalizeProof(value)
      Env.assertCanonicalProof(canonical)
      writeValue(slot, canonical)
    }

    private def bindLetLocal(slot: Int, value: Value): Unit = {
      Env.assertCanonicalProof(value)
      writeValue(slot, value)
    }

    private def clear(frame: Frame): Unit = {
      val until = frame.base + frame.plan.slots
      java.util.Arrays.fill(values.asInstanceOf[Array[AnyRef]], frame.base, until, null)
      java.util.Arrays.fill(bigs.asInstanceOf[Array[AnyRef]], frame.base, until, null)
      java.util.Arrays.fill(natTypes.asInstanceOf[Array[AnyRef]], frame.base, until, null)
      frame.env = Env.empty
      frame.plan = null
      frame.boxed = false
    }

    private def materialize(scope: Scope, frame: Frame): Env = {
      if (frame.boxed || scope.refs.isEmpty) frame.env
      else {
        val bound = Vector.tabulate(scope.slots.length)(i => readValue(frame.base + scope.slots(i)))
        frame.env.bindRuntimeLocals(scope.layout, bound)
      }
    }

    private def peerValues(lam: VLam, core: LamBody.Core): Vector[Value] =
      core.term.recursivePeers.map { case (_, name) =>
        if (core.term.recursivePeers.length == 1 && core.term.name.contains(name)) lam
        else
          core.env.globals
            .get(name)
            .map(_.value(core.env))
            .getOrElse(wtf(s"Checked recursive peer $name is absent from its group"))
      }

    private def overlaps(env: Env, refs: Vector[CoreAst.LocalRef]): Boolean = {
      var i = 0
      while (i < refs.length) {
        if (env.containsLocal(refs(i))) return true
        i += 1
      }
      false
    }

    private def fastCore(core: LamBody.Core, plan: Plan): Boolean =
      !plan.duplicateBindings && !overlaps(core.env, plan.boundRefs)

    private def fastPlan(lam: VLam, core: LamBody.Core): Plan = {
      val cached = fastClosures.get(lam)
      if (cached ne null) {
        if (cached eq emptyPlan) null else cached
      } else {
        val plan = if (eligible(lam)) runtime.functionPlan(core.term) else null
        val fast = (plan ne null) && fastCore(core, plan)
        if (fastClosures.size() >= 1024) fastClosures.clear()
        fastClosures.put(lam, if (fast) plan else emptyPlan)
        if (fast) plan else null
      }
    }

    private def activate(plan: Plan, env: Env, boxed: Boolean, tail: Boolean): Frame = {
      if (tail) {
        while (depth > 0 && kinds(depth - 1) == RestoreEnv) {
          depth -= 1
          savedEnvs(depth) = null
        }
        clear(frames(frameDepth))
      } else {
        push(Return, null)
        frameDepth += 1
        if (frameDepth == frames.length) frames = java.util.Arrays.copyOf(frames, frames.length * 2)
        if (frames(frameDepth) eq null) frames(frameDepth) = new Frame
      }
      val frame = frames(frameDepth)
      frame.base = if (frameDepth == 0) 0 else frames(frameDepth - 1).base + frames(frameDepth - 1).plan.slots
      frame.env = env
      frame.plan = plan
      frame.boxed = boxed
      ensureSlots(frame.base + plan.slots)
      frame
    }

    private def enter(lam: VLam, args: Vector[Value], tail: Boolean): Node = {
      val core = lam.body.asInstanceOf[LamBody.Core]
      val fast = fastPlan(lam, core)
      val plan = if (fast ne null) fast else runtime.functionPlan(core.term)
      if (args.length != lam.tpe.binders.length)
        fail(ArityMismatch(lam.tpe.binders.length, args.length, ArityMismatch.Arguments))
      if (fast ne null) {
        val frame = activate(plan, core.env, boxed = false, tail)
        var i = 0
        while (i < args.length) { bind(frame.base + i, args(i)); i += 1 }
        val peers = peerValues(lam, core)
        while (i < args.length + peers.length) {
          bind(frame.base + i, peers(i - args.length)); i += 1
        }
      } else {
        val bound = BinderOps.instantiateFullRuntime(lam.tpe.binders, lam.tpe.runtimeSlotLayout, core.env, args)
        val peers = peerValues(lam, core)
        val env = if (peers.isEmpty) bound else bound.bindRuntimeLocals(core.term.recursivePeerSlotLayout, peers)
        activate(plan, env, boxed = true, tail)
      }
      plan.root
    }

    def runTerm(term: CTerm, env: Env): Value = {
      val plan = runtime.plan(term)
      val boxed = plan.duplicateBindings || overlaps(env, plan.boundRefs)
      ensureSlots(plan.slots)
      val frame = frames(0)
      frame.base = 0
      frame.env = env
      frame.plan = plan
      frame.boxed = boxed
      runLoop(plan.root)
    }

    def runApply(fn: Value, args: Vector[Value], delayedStringAppend: SourceStringLayout): Value = {
      val frame = frames(0)
      frame.base = 0
      frame.env = Env.empty
      frame.plan = emptyPlan
      frame.boxed = false
      frameDepth = 0
      depth = 0
      try {
        applyFunction(fn, args, tail = true, delayedStringAppend)
        if (appliedNode eq null) resultValue else runLoop(appliedNode)
      } finally {
        if (frame.plan ne null) clear(frame)
        appliedNode = null
        clearResult()
        fastClosures.clear()
      }
    }

    private def runLoop(root: Node): Value = {
      frameDepth = 0
      depth = 0
      try {
        var pc: Node = root
        var result: Value = null
        var localNatType: Value = null
        var localLong = 0L
        var localBig: BigInt = null
        while (true) {
          var current = frames(frameDepth)
          pc match {
            case Ref(ref, slot, _) =>
              if (current.boxed || slot < 0) {
                result = nullaryConstructor(current.env(ref))
                localNatType = null
                localBig = null
              } else {
                val address = current.base + slot
                localNatType = natTypes(address)
                if (localNatType eq null) {
                  result = nullaryConstructor(Value.forced(readValue(address)))
                  localBig = null
                } else {
                  result = values(address)
                  localLong = longs(address)
                  localBig = bigs(address)
                }
              }
            case Global(name, _) =>
              result = nullaryConstructor(current.env(name))
              localNatType = null
              localBig = null
            case NatLiteral(value, _) =>
              localNatType = current.env.nativeLiterals.natLayout
                .getOrElse(fail(NatLiteralUnavailable("no validated Nat layout")))
                .natTpe
              if (value.signum < 0) {
                // Raw Core can reach this without the literal checker. Preserve VPacked's validation.
                result = VPacked.nat(value, localNatType)
              }
              if (value.isValidLong) {
                localLong = value.longValue
                localBig = null
              } else localBig = value
              result = null
            case StringLiteral(scalars, _) =>
              result = Packed.evalStrLit(scalars, current.env)
              localNatType = null
              localBig = null
            case a: Application =>
              push(AppFunction, a)
              pc = a.fn
              result = null
              localNatType = null
              localBig = null
            case b: Binding =>
              if (current.boxed) {
                push(RestoreEnv, null)
                savedEnvs(depth - 1) = current.env
              }
              push(LetValue, b)
              pc = b.value
              result = null
              localNatType = null
              localBig = null
            case m: Matching =>
              m.term.wildcard match {
                case Some(w) => wtf(s"An unexpanded wildcard case at ${w.span} reached evaluation")
                case None    =>
              }
              if (current.boxed) {
                push(RestoreEnv, null)
                savedEnvs(depth - 1) = current.env
              }
              push(MatchScrutinee, m)
              pc = m.scrut
              result = null
              localNatType = null
              localBig = null
            case PiValue(term, scope) =>
              result = Interpreter.evalPi(term, materialize(scope, current))
              localNatType = null
              localBig = null
            case LambdaValue(term, scope) =>
              val env = materialize(scope, current)
              result = Interpreter.evalLam(term, Interpreter.evalPi(term.ty, env), env)
              localNatType = null
              localBig = null
            case Scoped(term, body, slot, _) =>
              if (current.boxed) {
                push(RestoreEnv, null)
                savedEnvs(depth - 1) = current.env
                current.env = current.env.putLocal(term.ref, Atoms.of(term))
              } else bind(current.base + slot, Atoms.of(term))
              pc = body
              result = null
              localNatType = null
              localBig = null
            case p: Proposition =>
              push(PropLifetime, p)
              pc = p.scopeTerm
              result = null
              localNatType = null
              localBig = null
            case s: SortValue =>
              push(SortLevel, s)
              pc = s.level
              result = null
              localNatType = null
              localBig = null
            case f: FormValue =>
              if (f.args.isEmpty) {
                result = Interpreter.evalFormOp(f.form, Vector.empty)
                localNatType = null
                localBig = null
              } else {
                push(FormArgument, f)
                pc = f.args.head
                result = null
                localNatType = null
                localBig = null
              }
            case UnresolvedSelect(field, _) =>
              wtf(s"Unresolved field selection .$field reached evaluation")
          }
          if ((result ne null) || (localNatType ne null)) {
            var continue = true
            while (continue) {
              if (depth == 0) {
                if ((localNatType ne null) && (result eq null))
                  result = VPacked.nat(if (localBig eq null) BigInt(localLong) else localBig, localNatType)
                return result
              }
              depth -= 1
              val kind = kinds(depth)
              val node = nodes(depth)
              val index = indices(depth)
              nodes(depth) = null
              kind match {
                case AppFunction =>
                  val app = node.asInstanceOf[Application]
                  writeResult(current.base + app.fnSlot, result, localNatType, localLong, localBig)
                  if (app.args.isEmpty) {
                    if ((localNatType ne null) && (result eq null))
                      result = VPacked.nat(if (localBig eq null) BigInt(localLong) else localBig, localNatType)
                    applyApplication(result, app, current)
                    pc = appliedNode
                    result = resultValue
                    localNatType = resultNatType
                    localLong = resultLong
                    localBig = null
                    continue = appliedNode eq null
                  } else {
                    push(AppArgument, app, 0)
                    pc = app.args.head
                    continue = false
                  }
                case AppArgument =>
                  val app = node.asInstanceOf[Application]
                  writeResult(current.base + app.argStart + index, result, localNatType, localLong, localBig)
                  if (index + 1 < app.args.length) {
                    push(AppArgument, app, index + 1)
                    pc = app.args(index + 1)
                    continue = false
                  } else {
                    val fn = readValue(current.base + app.fnSlot)
                    applyApplication(fn, app, current)
                    pc = appliedNode
                    result = resultValue
                    localNatType = resultNatType
                    localLong = resultLong
                    localBig = null
                    continue = appliedNode eq null
                  }
                case LetValue =>
                  val binding = node.asInstanceOf[Binding]
                  if (current.boxed) {
                    if ((localNatType ne null) && (result eq null))
                      result = VPacked.nat(if (localBig eq null) BigInt(localLong) else localBig, localNatType)
                    current.env = Interpreter.bindRuntimeLet(binding.pattern, result, current.env)
                    pc = binding.next
                    continue = false
                  } else {
                    binding.pattern match {
                      case CoreAst.LetPattern.Local(_) =>
                        if (localNatType eq null) bindLetLocal(current.base + binding.slots.head, result)
                        else writeResult(current.base + binding.slots.head, result, localNatType, localLong, localBig)
                      case f: CoreAst.LetPattern.Fields =>
                        if ((localNatType ne null) && (result eq null))
                          result = VPacked.nat(if (localBig eq null) BigInt(localLong) else localBig, localNatType)
                        val fields = StructEta.destructuredFields(result) match {
                          case Some(found) => found
                          case None        => wtf(s"A checked destructuring's value $result has no fields")
                        }
                        if (fields.length != f.vars.length)
                          wtf(
                            s"A checked destructuring binds ${f.vars.length} fields of $result, which has ${fields.length}"
                          )
                        var j = 0
                        while (j < fields.length) {
                          bind(current.base + binding.slots(j), fields(j))
                          j += 1
                        }
                    }
                    pc = binding.next
                    continue = false
                  }
                case MatchScrutinee =>
                  val matching = node.asInstanceOf[Matching]
                  if ((localNatType ne null) && (result eq null))
                    result = VPacked.nat(if (localBig eq null) BigInt(localLong) else localBig, localNatType)
                  val scrut = result
                  var selectedName: String = null
                  var selectedFields: Vector[Value] = null
                  scrut match {
                    case ConstructorForm.Stored(name, fields) =>
                      selectedName = name
                      selectedFields = fields
                    case _: VProof =>
                    case other =>
                      StructEta.fields(other) match {
                        case Some(fields) =>
                          selectedName = matching.term.cases match {
                            case Vector(single) => single.ctorName
                            case _ => wtf(s"Eta-eligible struct match has ${matching.term.cases.length} cases")
                          }
                          selectedFields = fields
                        case None =>
                      }
                  }
                  if (selectedName ne null) {
                    val branch = matching.cases.getOrElse(selectedName, null)
                    if (branch eq null) wtf(s"Checked match has no branch for constructor $selectedName")
                    val expected = branch.slots.length - matching.term.equation.size
                    if (selectedFields.length != expected)
                      wtf(
                        s"Checked branch for ${branch.source.ctorName} binds $expected fields, got ${selectedFields.length}"
                      )
                    if (current.boxed) {
                      current.env =
                        Interpreter.branchEnv(matching.term, branch.source, scrut, selectedFields, current.env)
                    } else {
                      var j = 0
                      while (j < selectedFields.length) {
                        bind(current.base + branch.slots(j), selectedFields(j))
                        j += 1
                      }
                      if (matching.term.equation.nonEmpty)
                        bind(
                          current.base + branch.slots(j),
                          Interpreter.matchEquationEvidence(selectedName, scrut, selectedFields, current.env)
                        )
                    }
                    pc = branch.body
                    continue = false
                  } else {
                    val env = materialize(matching.scope, current)
                    result = scrut match {
                      case proof: VProof => Interpreter.evalProofMatch(matching.term, proof, env)
                      case other =>
                        val blockedOn = Blocker.unapply(other).getOrElse(DepSet.empty)
                        Value.canonicalizeProof(
                          Interpreter.stuckMatchThunk(
                            matching.term,
                            env,
                            Interpreter.evalTerm(matching.term.motive, env),
                            blockedOn
                          )
                        )
                    }
                    localNatType = null
                    localBig = null
                  }
                case Return =>
                  clear(frames(frameDepth))
                  frameDepth -= 1
                  current = frames(frameDepth)
                case RestoreEnv =>
                  current.env = savedEnvs(depth)
                  savedEnvs(depth) = null
                case PropLifetime =>
                  if ((localNatType ne null) && (result eq null))
                    result = VPacked.nat(if (localBig eq null) BigInt(localLong) else localBig, localNatType)
                  result = Sorts.prop(Interpreter.getLifetime(result))
                  localNatType = null
                  localBig = null
                case SortLevel =>
                  val sort = node.asInstanceOf[SortValue]
                  if ((localNatType ne null) && (result eq null))
                    result = VPacked.nat(if (localBig eq null) BigInt(localLong) else localBig, localNatType)
                  Interpreter.getLevel(result)
                  writeValue(current.base + sort.levelSlot, result)
                  push(SortKind, sort)
                  pc = sort.kind
                  continue = false
                case SortKind =>
                  val sort = node.asInstanceOf[SortValue]
                  if ((localNatType ne null) && (result eq null))
                    result = VPacked.nat(if (localBig eq null) BigInt(localLong) else localBig, localNatType)
                  Interpreter.getKind(result)
                  writeValue(current.base + sort.kindSlot, result)
                  push(SortLifetime, sort)
                  pc = sort.lifetime
                  continue = false
                case SortLifetime =>
                  val sort = node.asInstanceOf[SortValue]
                  if ((localNatType ne null) && (result eq null))
                    result = VPacked.nat(if (localBig eq null) BigInt(localLong) else localBig, localNatType)
                  result = Sorts.sort(
                    Interpreter.getLevel(readValue(current.base + sort.levelSlot)),
                    Interpreter.getKind(readValue(current.base + sort.kindSlot)),
                    Interpreter.getLifetime(result)
                  )
                  localNatType = null
                  localBig = null
                case FormArgument =>
                  val form = node.asInstanceOf[FormValue]
                  if ((localNatType ne null) && (result eq null))
                    result = VPacked.nat(if (localBig eq null) BigInt(localLong) else localBig, localNatType)
                  writeValue(current.base + form.start + index, result)
                  if (index + 1 < form.args.length) {
                    push(FormArgument, form, index + 1)
                    pc = form.args(index + 1)
                    continue = false
                  } else {
                    val args = Vector.newBuilder[Value]
                    var i = 0
                    while (i < form.args.length) {
                      args += readValue(current.base + form.start + i)
                      i += 1
                    }
                    result = Interpreter.evalFormOp(form.form, args.result())
                    localNatType = null
                    localBig = null
                  }
                case other => wtf(s"Unknown prepared continuation kind $other")
              }
            }
          }
        }
        wtf("Prepared evaluator loop exited")
      } finally {
        var i = frameDepth
        while (i >= 0) {
          if (frames(i).plan ne null) clear(frames(i))
          i -= 1
        }
        java.util.Arrays.fill(nodes.asInstanceOf[Array[AnyRef]], 0, depth, null)
        java.util.Arrays.fill(savedEnvs.asInstanceOf[Array[AnyRef]], 0, depth, null)
        java.util.Arrays.fill(tailArguments.asInstanceOf[Array[AnyRef]], null)
        java.util.Arrays.fill(tailBigs.asInstanceOf[Array[AnyRef]], null)
        java.util.Arrays.fill(tailNatTypes.asInstanceOf[Array[AnyRef]], null)
        depth = 0
        appliedNode = null
        clearResult()
        fastClosures.clear()
      }
    }

    private def applyFunction(
        fn: Value,
        args: Vector[Value],
        tail: Boolean,
        delayedStringAppend: SourceStringLayout = null
    ): Unit = {
      fn.tpe match {
        case pi: VPi =>
          if (args.length != pi.binders.length)
            fail(ArityMismatch(pi.binders.length, args.length, ArityMismatch.Arguments))
          fn match {
            case lam: VLam =>
              lam.body match {
                case _: LamBody.Core =>
                  appliedNode = enter(lam, args, tail)
                  clearResult()
                case LamBody.Native(run, nativeEnv, _, _) =>
                  appliedNode = null
                  setValueResult(run(args, nativeEnv))
                case LamBody.ProofEta =>
                  val env = BinderOps.instantiateFullRuntime(pi.binders, pi.runtimeSlotLayout, pi.env, args)
                  appliedNode = null
                  setValueResult(Value.canonicalizeProof(VProof(pi.codomain(env))))
              }
            case head: ConstructorHead =>
              lazy val env = BinderOps.instantiateFullRuntime(pi.binders, pi.runtimeSlotLayout, pi.env, args)
              val resultTy = pi.constructorResultType(args, env)
              val storedArgs = Value.constructorStoredArgs(head, args)
              appliedNode = null
              if (delayedStringAppend eq null) setValueResult(Packed.construct(head, storedArgs, resultTy))
              else {
                if (!(head eq delayedStringAppend.stringMk))
                  wtf("A delayed String.append key capability reached a different constructor")
                setValueResult(VApp.deferredStringAppendResult(delayedStringAppend, storedArgs, resultTy))
              }
            case head @ (_: VConst | _: VApp | _: NeutralThunk | _: Var) =>
              val env = BinderOps.instantiateFullRuntime(pi.binders, pi.runtimeSlotLayout, pi.env, args)
              val blockedOn = Blocker.unapply(head).getOrElse(DepSet.empty)
              appliedNode = null
              setValueResult(Value.canonicalizeProof(VApp(head, args, pi.codomain(env), blockedOn)))
            case _ => fail(CannotApplyNonFunction(fn))
          }
        case _ => fail(CannotApplyNonFunction(fn.tpe))
      }
    }

    private def applyApplication(fn: Value, app: Application, caller: Frame): Unit = {
      val corePlan = fn match {
        case lam: VLam if lam.tpe.numExplicit == lam.tpe.binders.length =>
          lam.body match {
            case core: LamBody.Core =>
              if (app.args.length != lam.tpe.binders.length)
                fail(ArityMismatch(lam.tpe.binders.length, app.args.length, ArityMismatch.Arguments))
              fastPlan(lam, core)
            case _ => null
          }
        case _ => null
      }
      if (corePlan ne null) {
        appliedNode = enterFromSlots(fn.asInstanceOf[VLam], app, caller, corePlan)
        clearResult()
      } else
        fn match {
          case lam: VLam if tryScalarApplication(lam, app, caller) =>
            appliedNode = null
          case other =>
            val args = Vector.tabulate(app.args.length)(i => readValue(caller.base + app.argStart + i))
            applyFunction(other, Interpreter.residualArguments(other, args), app.tail)
        }
    }

    /** All-explicit Core calls copy arguments straight from the caller's slots, without a binding Vector. */
    private def enterFromSlots(lam: VLam, app: Application, caller: Frame, plan: Plan): Node = {
      val core = lam.body.asInstanceOf[LamBody.Core]
      val count = app.args.length
      if (app.tail) {
        while (depth > 0 && kinds(depth - 1) == RestoreEnv) {
          depth -= 1
          savedEnvs(depth) = null
        }
        if (count > tailArguments.length) {
          val capacity = math.max(count, tailArguments.length * 2)
          tailArguments = new Array[Value](capacity)
          tailLongs = new Array[Long](capacity)
          tailBigs = new Array[BigInt](capacity)
          tailNatTypes = new Array[Value](capacity)
        }
        var i = 0
        while (i < count) {
          val source = caller.base + app.argStart + i
          tailArguments(i) = values(source)
          val ty = natTypes(source)
          tailNatTypes(i) = ty
          if (ty ne null) {
            tailLongs(i) = longs(source)
            tailBigs(i) = bigs(source)
          }
          i += 1
        }
        clear(caller)
      } else {
        push(Return, null)
        frameDepth += 1
        if (frameDepth == frames.length) frames = java.util.Arrays.copyOf(frames, frames.length * 2)
        if (frames(frameDepth) eq null) frames(frameDepth) = new Frame
      }
      val frame = frames(frameDepth)
      frame.base = if (frameDepth == 0) 0 else frames(frameDepth - 1).base + frames(frameDepth - 1).plan.slots
      frame.env = core.env
      frame.plan = plan
      frame.boxed = false
      ensureSlots(frame.base + plan.slots)
      var i = 0
      while (i < count) {
        val target = frame.base + i
        if (app.tail) {
          if (tailNatTypes(i) eq null) bind(target, tailArguments(i))
          else {
            values(target) = tailArguments(i)
            longs(target) = tailLongs(i)
            bigs(target) = tailBigs(i)
            natTypes(target) = tailNatTypes(i)
          }
          tailArguments(i) = null
          tailBigs(i) = null
          tailNatTypes(i) = null
        } else if (natTypes(caller.base + app.argStart + i) eq null)
          bind(target, readValue(caller.base + app.argStart + i))
        else copySlot(caller.base + app.argStart + i, target)
        i += 1
      }
      while (i < count + core.term.recursivePeers.length) {
        val (_, name) = core.term.recursivePeers(i - count)
        val peer =
          if (core.term.recursivePeers.length == 1 && core.term.name.contains(name)) lam
          else
            core.env.globals
              .get(name)
              .map(_.value(core.env))
              .getOrElse(wtf(s"Checked recursive peer $name is absent from its group"))
        bind(frame.base + i, peer)
        i += 1
      }
      plan.root
    }

  }
}
