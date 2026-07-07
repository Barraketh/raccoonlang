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
            LamBody.Native(
              (args, _) => VSort(Interpreter.getLevel(args.head)),
              Env.empty[Value],
              isRawRecursive = false
            )
          )
        case pi: VPi => throw ArityMismatch(1, pi.binders.length, Some(span))
        case other   => throw CannotApplyNonFunction(other, Some(span))
      }
  }

  private final case class Native(
      run: (VLam, VPi, Vector[Value]) => Value
  ) extends Entry {
    override def instantiate(name: String, tpe: Value, span: Span): Value =
      tpe match {
        case pi: VPi =>
          lazy val self: VLam =
            VLam(
              pi,
              ValueId.Const(name),
              LamBody.Native((args, _) => run(self, pi, args), Env.empty[Value], isRawRecursive = false)
            )
          self
        case other => throw CannotApplyNonFunction(other, Some(span))
      }
  }

  private final case class Constructor(numErasedFamilyArgs: Int) extends Entry {
    override def instantiate(name: String, tpe: Value, span: Span): Value =
      tpe match {
        case pi: VPi =>
          if (numErasedFamilyArgs > pi.binders.length)
            throw ArityMismatch(numErasedFamilyArgs, pi.binders.length, Some(span))
          ConstructorHead(name, numErasedFamilyArgs, pi.binders.length, pi)
        case other => throw CannotApplyNonFunction(other, Some(span))
      }
  }

  private val LiftName = "Quot.lift"
  private val IndName = "Quot.ind"
  private val MkName = "Quot.mk"

  private val entries: Map[String, Entry] =
    Map(
      "Sort" -> SortEntry,
      "Level.succ" -> Native { (_, _, args) =>
        Level.succ(Interpreter.getLevel(args.head))
      },
      "Level.max" -> Native { (_, _, args) =>
        Level.max(args.map(arg => Interpreter.getLevel(arg)))
      },
      MkName -> Constructor(3),
      LiftName -> Native(runLift),
      IndName -> Native(runInd)
    )

  def instantiate(name: String, tpe: Value, span: Span): Value =
    entries.get(name) match {
      case Some(entry) => entry.instantiate(name, tpe, span)
      case None        => throw WTF(s"Unknown builtin $name", Some(span))
    }

  private def runLift(self: VLam, selfType: VPi, args: Vector[Value]): Value = {
    val q = args(4)
    val resultTy = args(5)
    val f = args(6)

    q match {
      case QuotientMk(rep)    => Interpreter.evalApply(f, Vector(rep))
      case Blocker(blockerId) => VBlockedApp(self, args, resultTy, blockerId)
      case _                  => VApp(VConst(LiftName, Symbol, selfType), args, resultTy)
    }
  }

  private def runInd(self: VLam, selfType: VPi, args: Vector[Value]): Value = {
    val q = args(3)
    val motive = args(4)
    val mkCase = args(5)
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
        case VCtor(head, storedArgs, _) if head.name == MkName =>
          Value.constructorPatternArgs(head, storedArgs) match {
            case Vector(rep) => Some(rep)
            case _           => None
          }
        case _ => None
      }
  }
}
