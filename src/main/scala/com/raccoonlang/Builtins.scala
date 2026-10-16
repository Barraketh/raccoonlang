package com.raccoonlang

import com.raccoonlang.Value._

private object Builtins {
  private sealed trait Entry {
    def instantiate(name: String, tpe: Value): Value
  }

  /** A native function; `bind` locates its arguments in its declared type once, and returns what runs a call. */
  private final case class Native(
      bind: VPi => (VLam, Vector[Value]) => Value
  ) extends Entry {
    override def instantiate(name: String, tpe: Value): Value =
      tpe match {
        case pi: VPi =>
          val run = bind(pi)
          lazy val self: VLam =
            VLam(
              pi,
              ValueId.Const(name),
              LamBody.Native((args, _) => run(self, args), Env.empty, isRawRecursive = false)
            )
          self
        case other => fail(CannotApplyNonFunction(other))
      }
  }

  /** A constructor that stores its binders from `firstField` on; the binders before it are its family's arguments. */
  private final case class Constructor(firstField: String) extends Entry {
    override def instantiate(name: String, tpe: Value): Value =
      tpe match {
        case pi: VPi =>
          // Quot.sound identifies distinct Quot.mk applications, so unification must not assume
          // injectivity or disjointness for builtin constructors.
          ConstructorHead(name, binderIndex(pi, firstField), pi.binders.length, pi, noConfusion = false)
        case other => fail(CannotApplyNonFunction(other))
      }
  }

  private val LiftName = "Quot.lift"
  private val IndName = "Quot.ind"
  private val MkName = "Quot.mk"

  private val entries: Map[String, Entry] =
    Map(
      MkName -> Constructor("a"),
      LiftName -> Native(runLift),
      IndName -> Native(runInd)
    )

  def instantiate(name: String, tpe: Value): Value =
    entries.get(name) match {
      case Some(entry) => entry.instantiate(name, tpe)
      case None        => wtf(s"Unknown builtin $name")
    }

  /** Locate a primitive quotient argument in its declared telescope. */
  private def binderIndex(pi: VPi, name: String): Int =
    pi.binders.indexWhere(_.name == name) match {
      case -1  => wtf(s"Builtin type $pi has no binder $name")
      case idx => idx
    }

  private def runLift(selfType: VPi): (VLam, Vector[Value]) => Value = {
    val (qAt, resultTyAt, fAt) = (binderIndex(selfType, "q"), binderIndex(selfType, "B"), binderIndex(selfType, "f"))
    (self, args) =>
      args(qAt) match {
        case QuotientMk(rep) => Interpreter.evalApply(args(fAt), Vector(rep))
        case Blocker(blockedOn) =>
          Value.canonicalizeProof(VBlockedApp(self, args, args(resultTyAt), blockedOn))
        case _ =>
          Value.canonicalizeProof(VApp(VConst(LiftName, Symbol, selfType), args, args(resultTyAt)))
      }
  }

  private def runInd(selfType: VPi): (VLam, Vector[Value]) => Value = {
    val (qAt, motiveAt, mkAt) =
      (binderIndex(selfType, "q"), binderIndex(selfType, "motive"), binderIndex(selfType, "mk"))
    (self, args) => {
      lazy val resultTy = Interpreter.evalApply(args(motiveAt), Vector(args(qAt)))
      args(qAt) match {
        case QuotientMk(rep) => Interpreter.evalApply(args(mkAt), Vector(rep))
        case Blocker(blockedOn) =>
          Value.canonicalizeProof(VBlockedApp(self, args, resultTy, blockedOn))
        case _ =>
          Value.canonicalizeProof(VApp(VConst(IndName, Symbol, selfType), args, resultTy))
      }
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
