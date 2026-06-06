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
            isStable = true,
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
              isStable,
              LamBody.Native((args, _) => run(self, pi, args), Env.empty, isRawRecursive = false)
            )
          self
        case other => throw CannotApplyNonFunction(other, Some(span))
      }
  }

  private final case class Constructor(erasedFamilyArgIndexes: Vector[Int]) extends Entry {
    override def instantiate(name: String, tpe: Value, span: Span): Value =
      tpe match {
        case pi: VPi =>
          if (erasedFamilyArgIndexes.length > pi.binders.length)
            throw ArityMismatch(erasedFamilyArgIndexes.length, pi.binders.length, Some(span))
          ConstructorHead(name, erasedFamilyArgIndexes, pi.binders.length, pi)
        case other => throw CannotApplyNonFunction(other, Some(span))
      }
  }

  private val LiftName = "Quot.lift"
  private val IndName = "Quot.ind"
  private val MkName = "Quot.mk"

  private val entries: Map[String, Entry] =
    Map(
      "Sort" -> SortEntry,
      "add_normalizer" -> Native((_, _, args) => Normalizers.add_normalizer(args.head.tpe +: args)),
      "Level.succ" -> Native { (_, _, args) =>
        Level.succ(Interpreter.getLevel(args.head))
      },
      "Level.max" -> Native { (_, _, args) =>
        Level.max(args.map(arg => Interpreter.getLevel(arg)))
      },
      MkName -> Constructor(Vector(0, 1)),
      LiftName -> Native(runLift),
      IndName -> Native(runInd)
    )

  def instantiate(name: String, tpe: Value, span: Span): Value =
    entries.get(name) match {
      case Some(entry) => entry.instantiate(name, tpe, span)
      case None        => throw WTF(s"Unknown builtin $name", Some(span))
    }

  private def runLift(self: VLam, selfType: VPi, args: Vector[Value]): Value = {
    val q = args(0)
    val resultTy = args(1)
    val f = args(2)

    q match {
      case QuotientMk(rep)    => Interpreter.evalApply(f, Vector(rep))
      case Blocker(blockerId) => VBlockedApp(self, args, resultTy, blockerId)
      case _                  => VApp(VConst(LiftName, Symbol, selfType), args, resultTy)
    }
  }

  private def runInd(self: VLam, selfType: VPi, args: Vector[Value]): Value = {
    val q = args(0)
    val motive = args(1)
    val mkCase = args(2)
    lazy val resultTy = Interpreter.evalApply(motive, Vector(q))

    q match {
      case QuotientMk(rep)    => Interpreter.evalApply(mkCase, Vector(rep))
      case Blocker(blockerId) => VBlockedApp(self, args, resultTy, blockerId)
      case _                  => VApp(VConst(IndName, Symbol, selfType), args, resultTy)
    }
  }

  private object QuotientMk {
    def unapply(value: Value): Option[Value] =
      value match {
        case ctor @ VCtor(head, _, _) if head.name == MkName && ctor.fields.length == 1 => Some(ctor.fields.head)
        case _                                                                          => None
      }
  }
}
