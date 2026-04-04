package com.raccoonlang

import com.raccoonlang.CoreAst.Term.{Capture, PatternApp}
import com.raccoonlang.CoreAst.{TypePattern, TypeTerm}
import com.raccoonlang.Interpreter._
import com.raccoonlang.Util.NEL
import com.raccoonlang.Value._

import scala.collection.immutable.BitSet

object TypePatternOps {
  private def requirePi(fn: Value)(implicit eqStore: EqStore): VPi =
    resolveInEqStore(fn.tpe) match {
      case pi: VPi => pi
      case other   => throw CannotApplyNonFunction(other)
    }

  // =========================
  // Semantic head views
  // =========================

  private sealed trait SemanticHead
  private case class ValueHead(v: Value) extends SemanticHead
  private case object SortHead extends SemanticHead

  private def fnHeadView(fn: Value)(implicit eqStore: EqStore): SemanticHead =
    resolveInEqStore(fn) match {
      case VLam(_, LamId.Const("Sort"), _, _) => SortHead
      case VConst("Sort", _, _)               => SortHead
      case other                              => ValueHead(other)
    }

  private def actualHeadView(v: Value)(implicit eqStore: EqStore): Option[(SemanticHead, Vector[Value])] =
    resolveInEqStore(v) match {
      case VSort(level)       => Some((SortHead, Vector(level)))
      case av: AppliedValue   => Some((ValueHead(av.head), av.args.toVector))
      case v: VCtor           => Some(ValueHead(v.head), v.fields)
      case h: VConst          => Some((ValueHead(h), Vector.empty))
      case h: ConstructorHead => Some((ValueHead(h), Vector.empty))
      case _                  => None
    }

  private def decomposeForPatternHeadDef(fn: Value, actual: Value)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Vector[Value] = {
    val fnHead = fnHeadView(fn)
    actualHeadView(actual) match {
      case Some((SortHead, args)) if fnHead == SortHead =>
        args

      case Some((ValueHead(actualHead), args)) =>
        fnHead match {
          case ValueHead(expectedHead) if TypeChecker.defEq(actualHead, expectedHead) =>
            args
          case _ =>
            throw PatternHeadMismatch(fn, actual)
        }

      case _ =>
        throw PatternHeadMismatch(fn, actual)
    }
  }

  private def decomposeForBinding(actual: Value, expectedArity: Int)(implicit eqStore: EqStore): Vector[Value] =
    actualHeadView(actual) match {
      case Some((_, args)) if args.length == expectedArity => args
      case Some((_, args)) =>
        throw WTF(s"Pattern bind arity mismatch: expected $expectedArity args, got ${args.length} in $actual")
      case None => throw WTF(s"Failed to deconstruct $actual")
    }

  // =========================
  // User-visible opening
  // =========================
  //
  // These functions open the pattern the user actually wrote in a binder like:
  //   (v : Vec $A $n)
  // Captures here are exported into userEnv.

  private def freshOpenInternal(
      env: Env,
      p: TypePattern,
      expectedTy: Option[Value]
  )(implicit eqStore: EqStore): (Env, Value, BitSet) = p match {
    case Capture(name, _) =>
      val exp = expectedTy.getOrElse(throw PatternCaptureNeedsExpectedType(name))
      val fresh = FreshVar.freshVar(name, exp)
      (env.putLocal(name, fresh), fresh, BitSet.apply(fresh.id))

    case t: TypeTerm =>
      val v = evalTypeTerm(t, env)
      (env, v, BitSet.empty)

    case PatternApp(fn, args, _) =>
      val fnV = evalTypeTerm(fn, env)
      val pi = requirePi(fnV)

      if (pi.binders.length != args.length)
        throw PatternArityMismatch(fnV, pi.binders.length, args.length)

      val newVars = collection.mutable.BitSet()
      val (nextUserEnv, _, argVals) =
        pi.binders.toList.zip(args.toList).foldLeft((env, pi.env.newScope, Vector.empty[Value])) {
          case ((curUserEnv, curFamilyEnv, curArgs), (binder, argPat)) =>
            val (familyAfterBinderTy, binderTyV, newVarIds1) = freshOpenInternal(curFamilyEnv, binder.ty, None)
            val (userAfterArg, argV, newVarIds2) = freshOpenInternal(curUserEnv, argPat, Some(binderTyV))

            newVars |= newVarIds1
            newVars |= newVarIds2

            (
              userAfterArg,
              familyAfterBinderTy.putLocal(binder.name, argV),
              curArgs :+ argV
            )
        }

      val res = evalApply(fnV, NEL.mk(argVals))
      (nextUserEnv, res, newVars.toImmutable)
  }

  private def bindInternal(
      env: Env,
      pat: TypePattern,
      value: Value
  )(implicit eqStore: EqStore): Env = pat match {
    case Capture(name, _) => env.putLocal(name, value)

    case _: TypeTerm => env

    case PatternApp(_, patArgs, _) =>
      val args = decomposeForBinding(value, patArgs.length)
      patArgs.toVector.zip(args).foldLeft(env) { case (curEnv, (nextPat, arg)) =>
        bindInternal(curEnv, nextPat, arg)
      }
  }

  private def matchOpenInternal(
      userEnv: Env,
      p: TypePattern,
      actual: Value
  )(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Env = {
    val actual0 = resolveInEqStore(actual)

    p match {
      case Capture(name, _) => userEnv.putLocal(name, actual0)

      case t: TypeTerm =>
        val v = evalTypeTerm(t, userEnv)
        TypeChecker.checkFits(actual0, v)
        userEnv

      case PatternApp(fn, args, _) =>
        val fnV = evalTypeTerm(fn, userEnv)
        val pi = requirePi(fnV)

        if (pi.binders.length != args.length)
          throw PatternArityMismatch(fnV, pi.binders.length, args.length)

        val actualArgs = decomposeForPatternHeadDef(fnV, actual0)
        if (actualArgs.length != args.length)
          throw PatternArityMismatch(fnV, args.length, actualArgs.length)

        val (nextUserEnv, _) =
          pi.binders.toList.zip(args.toList).zip(actualArgs).foldLeft((userEnv, pi.env.newScope)) {
            case ((curUserEnv, curPiEnv), ((binder, argPat), actualArg)) =>
              val nextPiEnv = bindInternal(curPiEnv, binder.ty, actualArg.tpe).putLocal(binder.name, actualArg)
              val nextUserEnv = matchOpenInternal(curUserEnv, argPat, actualArg)
              (nextUserEnv, nextPiEnv)
          }
        nextUserEnv
    }
  }

  // =========================
  // Public API
  // =========================

  // Used by FreshVar.assignFreshVars and typecheckPi
  def freshOpen(env: Env, p: TypePattern, meta: EqStore): (Env, Value, BitSet) = {
    implicit val eqStore: EqStore = meta
    freshOpenInternal(env, p, None)
  }

  // Used by Interpreter.getEnvWithArgs
  def bindValue(env: Env, p: TypePattern, actualTy: Value, meta: EqStore): Env = {
    implicit val eqStore: EqStore = meta
    bindInternal(env, p, actualTy)
  }

  // Used by TypeChecker.typecheckApply
  def matchValue(env: Env, p: TypePattern, actualTy: Value, meta: EqStore)(implicit
      normalizers: NormalizerMap
  ): Env = {
    implicit val eqStore: EqStore = meta
    matchOpenInternal(env, p, actualTy)
  }

}
