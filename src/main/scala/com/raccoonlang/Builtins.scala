package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.packed.Words
import com.raccoonlang.telescope.BinderOps

private object Builtins {
  private sealed trait Entry {
    def instantiate(name: String, tpe: Value, span: Span): Value
  }

  /**
   * A universe former, `Sort` or `Lin` of a level, or `Univ` of a kind and a level: its declared codomain is replaced
   * by the universe's own type.
   */
  private final case class UniverseEntry(arity: Int, universe: Vector[Value] => Universe) extends Entry {
    override def instantiate(name: String, tpe: Value, span: Span): Value =
      tpe match {
        case pi: VPi if pi.binders.length == arity =>
          val refs = pi.binders.map(_.localRef)
          val preciseType =
            pi.copy(
              codomain = env => universe(refs.map(env(_))).tpe,
              id = ValueId.Const(name)
            )
          VLam(
            preciseType,
            ValueId.Const(name),
            LamBody.Native((args, _) => universe(args), Env.empty, isRawRecursive = false)
          )
        case pi: VPi => throw ArityMismatch(arity, pi.binders.length, Some(span))
        case other   => throw CannotApplyNonFunction(other, Some(span))
      }
  }

  /**
   * An opaque type former, such as `Protocol.Tok`: a symbol of its declared type, as an axiom publishes, whose
   * applications `Interpreter.evalApply` leaves as symbol applications. These never reduce, convert only by congruence
   * (`ValueEquivalence.defEq`), and give unification neither injectivity nor apartness (`rigidForm` is `None` for
   * them). The symbol has no inductive metadata and no constructors, so `match` on its values is `NonInductiveMatch`
   * and no constructor of it can be named. Its declared type is kernel source, which no prelude or program can
   * redeclare.
   */
  private case object Opaque extends Entry {
    override def instantiate(name: String, tpe: Value, span: Span): Value = VConst(name, Symbol, tpe)
  }

  private final case class Native(
      run: (VLam, VPi, Vector[Value]) => Value,
      isStable: Boolean = true
  ) extends Entry {
    override def instantiate(name: String, tpe: Value, span: Span): Value =
      tpe match {
        case pi: VPi =>
          lazy val self: VLam =
            VLam(
              pi,
              ValueId.Const(name),
              LamBody.Native((args, _) => run(self, pi, args), Env.empty, isRawRecursive = false)
            )
          self
        case other => throw CannotApplyNonFunction(other, Some(span))
      }
  }

  /**
   * A native whose application is a value of its own: the native applied to the arguments, at the declared codomain
   * instantiated at them. It never reduces, converts by congruence, and quotes as a call of the native by name.
   * `Nat.expand_eq(n)` is one, a proof of `Eq(Nat, n, Nat.expand(n))`, which holds because `Nat.expand` preserves its
   * argument (`NatNormalForm.expansion`); as a proof it converts with every proof of its proposition.
   */
  private def ownApplication(self: VLam, pi: VPi, args: Vector[Value]): Value =
    VApp(self, args, pi.codomain(BinderOps.instantiateFull(pi.binders, pi.env, args)))

  /**
   * No two `Native` entries are extensionally equal functions, so conversion may treat distinct native lambdas as
   * unequal without opening them (see ValueEquivalence).
   */
  private val entries: Map[String, Entry] =
    Map(
      "Sort" -> UniverseEntry(1, args => VSort(Interpreter.getLevel(args(0)))),
      "Lin" -> UniverseEntry(1, args => VLin(Interpreter.getLevel(args(0)))),
      "Univ" -> UniverseEntry(2, args => VUniv(Interpreter.getKind(args(0)), Interpreter.getLevel(args(1)))),
      "Kind.join" -> Native { (_, _, args) =>
        Kind.join(Interpreter.getKind(args(0)), Interpreter.getKind(args(1)))
      },
      "Level.succ" -> Native { (_, _, args) =>
        Level.succ(Interpreter.getLevel(args.head))
      },
      "Level.max" -> Native { (_, _, args) =>
        Level.max(args.map(arg => Interpreter.getLevel(arg)))
      },
      "Nat.add" -> Native((_, _, args) => NatNormalForm.add(args(0), args(1))),
      "Nat.mul" -> Native((_, _, args) => NatNormalForm.mul(args(0), args(1))),
      "Nat.pow" -> Native((_, _, args) => NatNormalForm.pow(args(0), args(1))),
      "Nat.sub" -> Native((_, _, args) => NatNormalForm.sub(args(0), args(1))),
      "Nat.pred" -> Native((_, _, args) => NatNormalForm.pred(args(0))),
      "Nat.isZero" -> Native((_, _, args) => NatNormalForm.isZero(args(0))),
      "Nat.beq" -> Native((_, _, args) => NatNormalForm.beq(args(0), args(1))),
      "Nat.ble" -> Native((_, _, args) => NatNormalForm.ble(args(0), args(1))),
      "Nat.div" -> Native((_, _, args) => NatNormalForm.div(args(0), args(1))),
      "Nat.mod" -> Native((_, _, args) => NatNormalForm.mod(args(0), args(1))),
      "Nat.expand" -> Native((_, _, args) => NatNormalForm.expand(args(0))),
      // Declared by the prelude, whose `Eq` its type names.
      "Nat.expand_eq" -> Native(ownApplication),
      "List.append" -> Native((_, _, args) => Words.append(args(0), args(1))),
      "List.length" -> Native((_, _, args) => Words.length(args(0))),
      "Protocol.Supply" -> Opaque,
      "Protocol.Inst" -> Opaque,
      "Protocol.Tok" -> Opaque,
      // R1–R3 (`ProtocolPrimitives`); a stuck `new` or `step` keeps the native itself as its head.
      "Protocol.new" -> Native((self, _, args) => ProtocolPrimitives.allocate(self, args)),
      "Protocol.step" -> Native((self, _, args) => ProtocolPrimitives.step(self, args)),
      "Protocol.observe" -> Native((_, _, args) => ProtocolPrimitives.observe(args))
    )

  def instantiate(name: String, tpe: Value, span: Span): Value =
    entries.get(name) match {
      case Some(entry) => entry.instantiate(name, tpe, span)
      case None        => throw WTF(s"Unknown builtin $name", Some(span))
    }
}
