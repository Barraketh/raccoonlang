package com.raccoonlang

import com.raccoonlang.Value._

private object Builtins {
  private sealed trait Entry {
    def instantiate(name: String, tpe: Value): Value
  }

  private case object SortEntry extends Entry {
    override def instantiate(name: String, tpe: Value): Value =
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
              Env.empty,
              isRawRecursive = false
            )
          )
        case pi: VPi => fail(ArityMismatch(1, pi.binders.length))
        case other   => fail(CannotApplyNonFunction(other))
      }
  }

  private final case class Native(
      run: (VLam, VPi, Vector[Value]) => Value
  ) extends Entry {
    override def instantiate(name: String, tpe: Value): Value =
      tpe match {
        case pi: VPi =>
          lazy val self: VLam =
            VLam(
              pi,
              ValueId.Const(name),
              LamBody.Native((args, _) => run(self, pi, args), Env.empty, isRawRecursive = false)
            )
          self
        case other => fail(CannotApplyNonFunction(other))
      }
  }

  private final case class Constructor(numErasedFamilyArgs: Int) extends Entry {
    override def instantiate(name: String, tpe: Value): Value =
      tpe match {
        case pi: VPi =>
          if (numErasedFamilyArgs > pi.binders.length)
            fail(ArityMismatch(numErasedFamilyArgs, pi.binders.length))
          // Quot.sound identifies distinct Quot.mk applications, so unification must not assume
          // injectivity or disjointness for builtin constructors.
          ConstructorHead(name, numErasedFamilyArgs, pi.binders.length, pi, noConfusion = false)
        case other => fail(CannotApplyNonFunction(other))
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
      "Level.imax" -> Native { (_, _, args) =>
        Level.imax(Interpreter.getLevel(args(0)), Interpreter.getLevel(args(1)))
      },
      MkName -> Constructor(3),
      LiftName -> Native(runLift),
      IndName -> Native(runInd)
    )

  def instantiate(name: String, tpe: Value): Value =
    entries.get(name) match {
      case Some(entry) => entry.instantiate(name, tpe)
      case None        => wtf(s"Unknown builtin $name")
    }

  private def runLift(self: VLam, selfType: VPi, args: Vector[Value]): Value = {
    // Prelude declaration order: {u} {v} {A} {r} q B f sound.
    val (q, resultTy, f) = (args(4), args(5), args(6))

    q match {
      case QuotientMk(rep) => Interpreter.evalApply(f, Vector(rep))
      case Blocker(blockedOn) =>
        Value.canonicalizeProof(VBlockedApp(self, args, resultTy, blockedOn))
      case _ =>
        Value.canonicalizeProof(VApp(VConst(LiftName, Symbol, selfType), args, resultTy))
    }
  }

  private def runInd(self: VLam, selfType: VPi, args: Vector[Value]): Value = {
    // Prelude declaration order: {u} {A} {r} q motive mk.
    val (q, motive, mkCase) = (args(3), args(4), args(5))
    lazy val resultTy = Interpreter.evalApply(motive, Vector(q))

    q match {
      case QuotientMk(rep) => Interpreter.evalApply(mkCase, Vector(rep))
      case Blocker(blockedOn) =>
        Value.canonicalizeProof(VBlockedApp(self, args, resultTy, blockedOn))
      case _ =>
        Value.canonicalizeProof(VApp(VConst(IndName, Symbol, selfType), args, resultTy))
    }
  }

  private object QuotientMk {
    def unapply(value: Value): Option[Value] =
      value match {
        case VCtor(head, storedArgs, _) if head.name == MkName =>
          storedArgs match {
            case Vector(rep) => Some(rep)
            case _           => None
          }
        case _ => None
      }
  }
}
