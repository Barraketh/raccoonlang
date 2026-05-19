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
              codomain = (env, eqStore) => VSort(Level.succ(Interpreter.getLevel(env(lRef))(eqStore))),
              id = ValueId.Const(name)
            )
          VLam(
            preciseType,
            ValueId.Const(name),
            isStable = true,
            LamBody.Native((args, eqStore) => VSort(Interpreter.getLevel(args.head)(eqStore)))
          )
        case pi: VPi => throw ArityMismatch(1, pi.binders.length, Some(span))
        case other   => throw CannotApplyNonFunction(other, Some(span))
      }
  }

  private final case class Native(
      run: (VLam, VPi, Vector[Value], EqStore) => Value,
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
              LamBody.Native((args, eqStore) => run(self, pi, args, eqStore))
            )
          self
        case other => throw CannotApplyNonFunction(other, Some(span))
      }
  }

  private final case class Constructor(numErased: Int, isStruct: Boolean = false) extends Entry {
    override def instantiate(name: String, tpe: Value, span: Span): Value =
      tpe match {
        case pi: VPi if numErased <= pi.binders.length =>
          ConstructorHead(name, numErased, pi.binders.length, pi, isStruct)
        case pi: VPi =>
          throw ArityMismatch(numErased, pi.binders.length, Some(span))
        case other => throw CannotApplyNonFunction(other, Some(span))
      }
  }

  private val LiftName = "Quot.lift"
  private val IndName = "Quot.ind"
  private val MkName = "Quot.mk"

  private val entries: Map[String, Entry] =
    Map(
      "Sort" -> SortEntry,
      "add_normalizer" -> Native((_, _, args, _) => Normalizers.add_normalizer(args.head.tpe +: args)),
      "Level.succ" -> Native { (_, _, args, eqStore) =>
        Level.succ(Interpreter.getLevel(args.head)(eqStore))
      },
      "Level.max" -> Native { (_, _, args, eqStore) =>
        Level.max(args.map(arg => Interpreter.getLevel(arg)(eqStore)))
      },
      MkName -> Constructor(numErased = 2),
      LiftName -> Native(runLift),
      IndName -> Native(runInd)
    )

  def instantiate(name: String, tpe: Value, span: Span): Value =
    entries.get(name) match {
      case Some(entry) => entry.instantiate(name, tpe, span)
      case None        => throw WTF(s"Unknown builtin $name", Some(span))
    }

  private def runLift(self: VLam, selfType: VPi, args: Vector[Value], store: EqStore): Value = {
    implicit val eqStore: EqStore = store
    val q = args(0)
    val resultTy = args(1)
    val f = args(2)

    q.caseOf {
      case QuotientMk(rep) => Interpreter.evalApply(f, Vector(rep))
      case b: Blocker      => VBlockedApp(self, args, resultTy, b.blockerId)
      case _               => VApp(VConst(LiftName, Symbol, selfType), args, resultTy)
    }
  }

  private def runInd(self: VLam, selfType: VPi, args: Vector[Value], store: EqStore): Value = {
    implicit val eqStore: EqStore = store
    val q = args(0)
    val motive = args(1)
    val mkCase = args(2)
    lazy val resultTy = Interpreter.evalApply(motive, Vector(q))

    q.caseOf {
      case QuotientMk(rep) => Interpreter.evalApply(mkCase, Vector(rep))
      case b: Blocker      => VBlockedApp(self, args, resultTy, b.blockerId)
      case _               => VApp(VConst(IndName, Symbol, selfType), args, resultTy)
    }
  }

  private object QuotientMk {
    def unapply(value: Value)(implicit eqStore: EqStore): Option[Value] =
      value.caseOf {
        case ctor @ VCtor(head, _, _) if head.name == MkName && ctor.fields.length == 1 => Some(ctor.fields.head)
        case _                                                                          => None
      }
  }
}
