package com.raccoonlang

import com.raccoonlang.Value._

private object Builtins {
  private sealed trait Entry {
    def instantiate(name: String, tpe: Value, span: Span): Value
  }

  private case object SortEntry extends Entry {
    override def instantiate(name: String, tpe: Value, span: Span): Value =
      tpe match {
        case pi: VPi if pi.binders.length == 1 =>
          val lRef = pi.binders.head.localRef
          val preciseType =
            pi.copy(
              codomain = env => VSort(Level.succ(Interpreter.getLevel(env(lRef)))),
              id = ValueId.Const(name)
            )
          VLam(
            preciseType,
            ValueId.Const(name),
            LamBody.Native((args, _) => VSort(Interpreter.getLevel(args.head)), Env.empty, isRawRecursive = false)
          )
        case pi: VPi => throw ArityMismatch(1, pi.binders.length, Some(span))
        case other   => throw CannotApplyNonFunction(other, Some(span))
      }
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
   * No two entries are extensionally equal functions, so conversion may treat distinct native lambdas as unequal
   * without opening them (see ValueEquivalence).
   */
  private val entries: Map[String, Entry] =
    Map(
      "Sort" -> SortEntry,
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
      "Nat.ble" -> Native((_, _, args) => NatNormalForm.ble(args(0), args(1)))
    )

  def instantiate(name: String, tpe: Value, span: Span): Value =
    entries.get(name) match {
      case Some(entry) => entry.instantiate(name, tpe, span)
      case None        => throw WTF(s"Unknown builtin $name", Some(span))
    }
}
