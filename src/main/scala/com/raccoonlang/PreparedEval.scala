package com.raccoonlang

import com.raccoonlang.CoreAst.{Term => CTerm}
import com.raccoonlang.Value._

/** An opt-in execution tier for a checked Core closure. Its plan holds syntax and addresses, never live values. */
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
  private final case class Branch(body: Node, slots: Vector[Int])
  private final case class Generic(term: CTerm, scope: Scope) extends Node

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

  private final case class FunctionPlan(term: CTerm.Lam, root: Node, slots: Int)

  private final class Compiler(term: CTerm.Lam) {
    private var size = 0
    private def allocate(): Int = {
      val result = size
      size += 1
      result
    }
    def compile(): FunctionPlan = {
      val binders = term.ty.binders.map(_.localRef)
      val peers = term.recursivePeers.map(_._1)
      val initial = Scope(Vector.empty, Vector.empty, Map.empty)
      val (withBinders, _) = initial.bind(binders, () => allocate())
      val (withPeers, _) = withBinders.bind(peers, () => allocate())
      FunctionPlan(term, node(term.body, withPeers, tail = true), size)
    }

    private def node(term: CTerm, scope: Scope, tail: Boolean): Node =
      term match {
        case CTerm.LocalRef(ref, _)   => Ref(ref, scope.addresses.getOrElse(ref, -1), scope)
        case CTerm.GlobalRef(name, _) => Global(name, scope)
        case CTerm.NatLit(value, _)   => NatLiteral(value, scope)
        case CTerm.StrLit(scalars, _) => StringLiteral(scalars, scope)
        case CTerm.App(fn, args, evidence, _) if evidence.isEmpty =>
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
              val (nextScope, slots) = active.bind(refs, () => allocate())
              Binding(node(let.value, active, tail = false), let.pattern, slots, chain(index + 1, nextScope), active)
            }
          chain(0, scope)
        case m: CTerm.Match if m.wildcard.isEmpty && m.equation.isEmpty =>
          val branches = m.cases.map { branch =>
            val (branchScope, slots) = scope.bind(branch.argRefs, () => allocate())
            branch.ctorName -> Branch(node(branch.body, branchScope, tail), slots)
          }.toMap
          Matching(m, node(m.scrut, scope, tail = false), branches, scope)
        case other => Generic(other, scope)
      }
  }

  /** Explicit preparation is limited to a checked, data-valued Core lambda. */
  final class Prepared private[PreparedEval] (val function: VLam) {
    private val plans = new java.util.IdentityHashMap[CTerm.Lam, FunctionPlan]()
    private val session = new EvalSession(this)
    private var busy = false

    private[PreparedEval] def plan(term: CTerm.Lam): FunctionPlan = {
      val cached = plans.get(term)
      if (cached ne null) cached
      else {
        val built = new Compiler(term).compile()
        plans.put(term, built)
        built
      }
    }

    def run(args: Vector[Value]): Value = synchronized {
      if (busy) new EvalSession(this).run(function, args)
      else {
        busy = true
        try session.run(function, args)
        finally busy = false
      }
    }
  }

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
    var plan: FunctionPlan = null
    var lam: VLam = null
  }

  /** Reuses its banks across calls. Slots are never published; escaping values receive an immutable Env snapshot. */
  private[raccoonlang] final class EvalSession(prepared: Prepared) {
    private var values = new Array[Value](256)
    private var frames = Array.fill(32)(new Frame)
    private var frameDepth = 0
    private var tailArguments = new Array[Value](8)

    // Kind and metadata are parallel arrays so the interpreter allocates no continuation objects per step.
    private var kinds = new Array[Int](256)
    private var nodes = new Array[Node](256)
    private var indices = new Array[Int](256)
    private var depth = 0
    private var appliedNode: Node = null
    private var appliedValue: Value = null

    private val AppFunction = 1
    private val AppArgument = 2
    private val LetValue = 3
    private val MatchScrutinee = 4
    private val Return = 5

    private def ensureSlots(required: Int): Unit =
      if (required > values.length) {
        val capacity = math.max(required, values.length * 2)
        values = java.util.Arrays.copyOf(values, capacity)
      }

    private def push(kind: Int, node: Node, index: Int = 0): Unit = {
      if (depth == kinds.length) {
        val capacity = kinds.length * 2
        kinds = java.util.Arrays.copyOf(kinds, capacity)
        nodes = java.util.Arrays.copyOf(nodes, capacity)
        indices = java.util.Arrays.copyOf(indices, capacity)
      }
      kinds(depth) = kind
      nodes(depth) = node
      indices(depth) = index
      depth += 1
    }

    private def readValue(slot: Int): Value = values(slot)

    private def writeValue(slot: Int, value: Value): Unit = values(slot) = value

    private def bind(slot: Int, value: Value): Unit = {
      val canonical = Value.canonicalizeProof(value)
      Env.assertCanonicalProof(canonical)
      writeValue(slot, canonical)
    }

    private def clear(frame: Frame): Unit = {
      val until = frame.base + frame.plan.slots
      java.util.Arrays.fill(values.asInstanceOf[Array[AnyRef]], frame.base, until, null)
      frame.env = Env.empty
      frame.plan = null
      frame.lam = null
    }

    private def materialize(scope: Scope, frame: Frame): Env = {
      if (scope.refs.isEmpty) frame.env
      else {
        val bound = Vector.tabulate(scope.slots.length)(i => readValue(frame.base + scope.slots(i)))
        frame.env.bindRuntimeLocals(scope.layout, bound)
      }
    }

    private def enter(lam: VLam, args: Vector[Value], tail: Boolean): Node = {
      val core = lam.body.asInstanceOf[LamBody.Core]
      val plan = prepared.plan(core.term)
      if (args.length != lam.tpe.binders.length)
        fail(ArityMismatch(lam.tpe.binders.length, args.length, ArityMismatch.Arguments))
      if (tail) clear(frames(frameDepth))
      else {
        push(Return, null)
        frameDepth += 1
        if (frameDepth == frames.length) frames = java.util.Arrays.copyOf(frames, frames.length * 2)
        if (frames(frameDepth) eq null) frames(frameDepth) = new Frame
      }
      val frame = frames(frameDepth)
      frame.base = if (frameDepth == 0) 0 else frames(frameDepth - 1).base + frames(frameDepth - 1).plan.slots
      frame.env = core.env
      frame.plan = plan
      frame.lam = lam
      ensureSlots(frame.base + plan.slots)
      var i = 0
      while (i < args.length) {
        bind(frame.base + i, args(i))
        i += 1
      }
      while (i < args.length + core.term.recursivePeers.length) {
        val (_, name) = core.term.recursivePeers(i - args.length)
        val peer =
          if (core.term.recursivePeers.length == 1 && core.term.name.contains(name)) lam
          else
            core.env.globals.get(name).map(_.value(core.env)).getOrElse(wtf(s"Checked recursive peer $name is absent"))
        bind(frame.base + i, peer)
        i += 1
      }
      plan.root
    }

    def run(lam: VLam, args: Vector[Value]): Value = {
      frameDepth = 0
      depth = 0
      val core = lam.body.asInstanceOf[LamBody.Core]
      val plan = prepared.plan(core.term)
      val frame = frames(0)
      frame.base = 0
      frame.env = core.env
      frame.plan = plan
      frame.lam = lam
      ensureSlots(plan.slots)
      try {
        var i = 0
        if (args.length != lam.tpe.binders.length)
          fail(ArityMismatch(lam.tpe.binders.length, args.length, ArityMismatch.Arguments))
        while (i < args.length) {
          bind(i, args(i))
          i += 1
        }
        while (i < args.length + core.term.recursivePeers.length) {
          val (_, name) = core.term.recursivePeers(i - args.length)
          val peer =
            if (core.term.recursivePeers.length == 1 && core.term.name.contains(name)) lam
            else
              core.env.globals
                .get(name)
                .map(_.value(core.env))
                .getOrElse(wtf(s"Checked recursive peer $name is absent"))
          bind(i, peer)
          i += 1
        }
        var pc: Node = plan.root
        var result: Value = null
        while (true) {
          var current = frames(frameDepth)
          pc match {
            case Ref(ref, slot, _) =>
              result = nullaryConstructor(
                if (slot < 0) current.env(ref) else Value.forced(readValue(current.base + slot))
              )
            case Global(name, _)           => result = nullaryConstructor(current.env(name))
            case NatLiteral(value, _)      => result = Packed.evalNatLit(value, current.env)
            case StringLiteral(scalars, _) => result = Packed.evalStrLit(scalars, current.env)
            case a: Application =>
              push(AppFunction, a)
              pc = a.fn
              result = null
            case b: Binding =>
              push(LetValue, b)
              pc = b.value
              result = null
            case m: Matching =>
              push(MatchScrutinee, m)
              pc = m.scrut
              result = null
            case Generic(term, scope) => result = Interpreter.evalTerm(term, materialize(scope, current))
          }
          if (result ne null) {
            var continue = true
            while (continue) {
              if (depth == 0) return result
              depth -= 1
              val kind = kinds(depth)
              val node = nodes(depth)
              val index = indices(depth)
              nodes(depth) = null
              kind match {
                case AppFunction =>
                  val app = node.asInstanceOf[Application]
                  writeValue(current.base + app.fnSlot, result)
                  if (app.args.isEmpty) {
                    applyApplication(result, app, current)
                    pc = appliedNode
                    result = appliedValue
                    continue = appliedNode eq null
                  } else {
                    push(AppArgument, app, 0)
                    pc = app.args.head
                    continue = false
                  }
                case AppArgument =>
                  val app = node.asInstanceOf[Application]
                  writeValue(current.base + app.argStart + index, result)
                  if (index + 1 < app.args.length) {
                    push(AppArgument, app, index + 1)
                    pc = app.args(index + 1)
                    continue = false
                  } else {
                    val fn = readValue(current.base + app.fnSlot)
                    applyApplication(fn, app, current)
                    pc = appliedNode
                    result = appliedValue
                    continue = appliedNode eq null
                  }
                case LetValue =>
                  val binding = node.asInstanceOf[Binding]
                  binding.pattern match {
                    case CoreAst.LetPattern.Local(_) => bind(current.base + binding.slots.head, result)
                    case f: CoreAst.LetPattern.Fields =>
                      val fields = StructEta
                        .destructuredFields(result)
                        .getOrElse(wtf(s"A checked destructuring's value $result has no fields"))
                      if (fields.length != f.vars.length)
                        wtf(s"A checked destructuring binds ${f.vars.length} fields of $result, got ${fields.length}")
                      var j = 0
                      while (j < fields.length) {
                        bind(current.base + binding.slots(j), fields(j))
                        j += 1
                      }
                  }
                  pc = binding.next
                  continue = false
                case MatchScrutinee =>
                  val matching = node.asInstanceOf[Matching]
                  val scrut = result
                  var selectedName: String = null
                  var selectedFields: Vector[Value] = null
                  scrut match {
                    case ConstructorForm.Stored(name, fields) =>
                      selectedName = name
                      selectedFields = fields
                    case _: VProof =>
                    case other =>
                      StructEta.fields(other).foreach { fields =>
                        selectedName = matching.term.cases match {
                          case Vector(single) => single.ctorName
                          case _ => wtf(s"Eta-eligible struct match has ${matching.term.cases.length} cases")
                        }
                        selectedFields = fields
                      }
                  }
                  if (selectedName ne null) {
                    val branch =
                      matching.cases.getOrElse(selectedName, wtf(s"Checked match has no branch for $selectedName"))
                    if (selectedFields.length != branch.slots.length)
                      wtf(
                        s"Checked branch $selectedName binds ${branch.slots.length} fields, got ${selectedFields.length}"
                      )
                    var j = 0
                    while (j < selectedFields.length) {
                      bind(current.base + branch.slots(j), selectedFields(j))
                      j += 1
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
                  }
                case Return =>
                  clear(frames(frameDepth))
                  frameDepth -= 1
                  current = frames(frameDepth)
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
        java.util.Arrays.fill(tailArguments.asInstanceOf[Array[AnyRef]], null)
        depth = 0
        appliedNode = null
        appliedValue = null
      }
    }

    private def applyFunction(fn: Value, args: Vector[Value], tail: Boolean): Unit =
      fn match {
        case lam: VLam if eligible(lam) =>
          appliedNode = enter(lam, args, tail)
          appliedValue = null
        case other =>
          appliedNode = null
          appliedValue = Interpreter.evalApply(other, args)
      }

    private def applyApplication(fn: Value, app: Application, caller: Frame): Unit =
      fn match {
        case lam: VLam if eligible(lam) && lam.tpe.numExplicit == lam.tpe.binders.length =>
          appliedNode = enterFromSlots(lam, app, caller)
          appliedValue = null
        case other =>
          val args = Vector.tabulate(app.args.length)(i => readValue(caller.base + app.argStart + i))
          applyFunction(other, Interpreter.residualArguments(other, args), app.tail)
      }

    /** All-explicit Core calls copy arguments straight from the caller's slots, without a binding Vector. */
    private def enterFromSlots(lam: VLam, app: Application, caller: Frame): Node = {
      val core = lam.body.asInstanceOf[LamBody.Core]
      val plan = prepared.plan(core.term)
      val count = app.args.length
      if (count != lam.tpe.binders.length)
        fail(ArityMismatch(lam.tpe.binders.length, count, ArityMismatch.Arguments))
      if (app.tail) {
        if (count > tailArguments.length) tailArguments = new Array[Value](math.max(count, tailArguments.length * 2))
        var i = 0
        while (i < count) {
          tailArguments(i) = readValue(caller.base + app.argStart + i)
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
      frame.lam = lam
      ensureSlots(frame.base + plan.slots)
      var i = 0
      while (i < count) {
        bind(frame.base + i, if (app.tail) tailArguments(i) else readValue(caller.base + app.argStart + i))
        if (app.tail) tailArguments(i) = null
        i += 1
      }
      while (i < count + core.term.recursivePeers.length) {
        val (_, name) = core.term.recursivePeers(i - count)
        val peer =
          if (core.term.recursivePeers.length == 1 && core.term.name.contains(name)) lam
          else
            core.env.globals.get(name).map(_.value(core.env)).getOrElse(wtf(s"Checked recursive peer $name is absent"))
        bind(frame.base + i, peer)
        i += 1
      }
      plan.root
    }

    private def nullaryConstructor(value: Value): Value =
      value match {
        case head: ConstructorHead if head.totalArity == 0 => Packed.construct(head, Vector.empty, head.tpe)
        case other                                         => other
      }
  }
}
