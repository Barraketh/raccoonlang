package com.raccoonlang

import com.raccoonlang.Value._

private object Quotients {
  private val QuotName = "Quot"
  private val MkName = "Quot.mk"
  private val LiftCoreName = "Quot.liftCore"
  private val IndCoreName = "Quot.indCore"

  def install(env: TypecheckEnv): TypecheckEnv = {
    val quotPi = evalHeader("(A: Sort($u))(r: A -> A -> Prop): Sort(u)", env)
    val quotConst = VConst(QuotName, Symbol, quotPi)
    val quot =
      VLam(
        quotPi,
        ValueId.Const(QuotName),
        isStable = true,
        LamBody.Native((args, eqStore) => VApp(quotConst, args, TypeChecker.getUniverse(args(0))(eqStore)))
      )

    val envWithQuot = env.putGlobal(QuotName, quot)
    val mkPi = evalHeader("(A: Sort($u))(r: A -> A -> Prop)(a: A): Quot(A, r)", envWithQuot)
    val mk = ConstructorHead(MkName, numErased = 2, totalArity = 3, tpe = mkPi, isStruct = false)
    val envWithMk = envWithQuot.putGlobal(MkName, mk)

    val liftCorePi =
      evalHeader("(A: Sort($u))(r: A -> A -> Prop)(B: Sort($v))(f: A -> B)(q: Quot(A, r)): B", envWithMk)
    lazy val liftCore: VLam =
      VLam(
        liftCorePi,
        ValueId.Const(LiftCoreName),
        isStable = true,
        LamBody.Native((args, eqStore) => runLiftCore(liftCore, liftCorePi, args)(eqStore))
      )
    val envWithLift = envWithMk.putGlobal(LiftCoreName, liftCore)

    val indCorePi = evalHeader(
      "(A: Sort($u))(r: A -> A -> Prop)(motive: (q: Quot(A, r)) -> Prop)" +
        "(mk: (a: A) -> motive(Quot.mk(A, r, a)))(q: Quot(A, r)): motive(q)",
      envWithLift
    )
    lazy val indCore: VLam =
      VLam(
        indCorePi,
        ValueId.Const(IndCoreName),
        isStable = true,
        LamBody.Native((args, eqStore) => runIndCore(indCore, indCorePi, args)(eqStore))
      )

    envWithLift.putGlobal(IndCoreName, indCore)
  }

  private def runLiftCore(self: VLam, selfType: VPi, args: Vector[Value])(implicit eqStore: EqStore): Value = {
    val resultTy = args(2)
    val f = args(3)
    val q = args(4)

    q.caseOf {
      case QuotientMk(rep) => Interpreter.evalApply(f, Vector(rep))
      case b: Blocker     => VBlockedApp(self, args, resultTy, b.blockerId)
      case _              => VApp(VConst(LiftCoreName, Symbol, selfType), args, resultTy)
    }
  }

  private def runIndCore(self: VLam, selfType: VPi, args: Vector[Value])(implicit eqStore: EqStore): Value = {
    val motive = args(2)
    val mkCase = args(3)
    val q = args(4)
    lazy val resultTy = Interpreter.evalApply(motive, Vector(q))

    q.caseOf {
      case QuotientMk(rep) => Interpreter.evalApply(mkCase, Vector(rep))
      case b: Blocker     => VBlockedApp(self, args, resultTy, b.blockerId)
      case _              => VApp(VConst(IndCoreName, Symbol, selfType), args, resultTy)
    }
  }

  private object QuotientMk {
    def unapply(value: Value)(implicit eqStore: EqStore): Option[Value] =
      value.caseOf {
        case VCtor(head, Vector(rep), _) if head.name == MkName => Some(rep)
        case _                                                  => None
      }
  }

  private def evalHeader(header: String, env: TypecheckEnv): VPi = {
    implicit val eqStore: EqStore = EqStore.empty
    implicit val normalizers: NormalizerMap = NormalizerMap.empty

    TypeChecker.evalTypeTerm(parseHeader(header), env) match {
      case pi: VPi => pi
      case other   => throw CannotApplyNonFunction(other)
    }
  }

  private def parseHeader(s: String): CoreAst.TypeTerm = {
    LanguageParser.parseFuncHeader(s) match {
      case Success(header, _, _) => Elaborator.getType(header)
      case err: Failure          => throw new RuntimeException(err.message)
    }
  }
}
