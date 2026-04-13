package com.raccoonlang

import com.raccoonlang.BinderOps.Freshened
import com.raccoonlang.CoreAst.Term.{Capture, PatternApp}
import com.raccoonlang.CoreAst.{TypePattern, TypeTerm}
import com.raccoonlang.Interpreter._
import com.raccoonlang.Util.NEL
import com.raccoonlang.Value._

import scala.collection.immutable.BitSet

object TypePatternOps {
  private type Captures = Vector[(String, Var)]

  final case class FreshOpened(
      env: Env,
      value: Value,
      captures: Captures,
      newVars: BitSet
  )

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
      case VLam(_, ValueId.Const("Sort"), _, _) => SortHead
      // Defensive: older environments could install Sort as a const; keep support
      case VConst("Sort", _, _) => SortHead
      case other                => ValueHead(other)
    }

  private def actualHeadView(v: Value)(implicit eqStore: EqStore): Option[(SemanticHead, Vector[Value])] =
    resolveInEqStore(v) match {
      case VSort(level)       => Some((SortHead, Vector(level)))
      case av: AppliedValue   => Some((ValueHead(av.head), av.args.toVector))
      case v: VCtor           => Some((ValueHead(v.head), v.fields))
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

  // Struct-aware fresh value builder for a given expected type.
  private def freshValueForType(name: String, expectedTy: Value, env: Env)(implicit
      eqStore: EqStore
  ): (Value, BitSet) = {
    val structMeta = Interpreter.resolveInEqStore(expectedTy) match {
      case VConst(_, Inductive(meta), _) if meta.isStruct                => Some((meta, Vector.empty[Value]))
      case VApp(VConst(_, Inductive(meta), _), args, _) if meta.isStruct => Some((meta, args))
      case _                                                             => None
    }

    structMeta match {
      case Some((meta, args)) =>
        val ctorName = meta.constructorNames.head
        val ctor = env.find(ctorName).getOrElse(throw NotFound(ctorName))
        ctor match {
          case h: ConstructorHead =>
            val pi = requirePi(h)
            val envWithParams: Env =
              if (args.isEmpty) pi.env
              else BinderOps.instantiate(pi.binders.take(args.length), pi.env, Util.NEL.mk(args), eqStore)

            val freshVars: Freshened = {
              val remainingFields = pi.binders.toVector.drop(args.length)
              if (remainingFields.isEmpty) Freshened(Vector.empty, envWithParams, BitSet.empty)
              else BinderOps.freshen(NEL.mk(remainingFields), envWithParams, eqStore)
            }

            val ty = pi.codomain(freshVars.env, eqStore)
            val value = VCtor(h, freshVars.vars, ty)
            (value, freshVars.newVars)
          case _ => throw WTF(s"$ctorName is not a constructor head")
        }
      case None =>
        val fresh = FreshVar.freshVar(name, expectedTy)
        (fresh, BitSet(fresh.id))
    }
  }


  private def freshVarInternal(
      env: Env,
      p: TypePattern,
      expectedTy: Option[Value]
  )(implicit eqStore: EqStore): FreshOpened = p match {
    case Capture(name, _) =>
      val exp = expectedTy.getOrElse(throw PatternCaptureNeedsExpectedType(name))
      val (v, newV) = freshValueForType(name, exp, env)
      val caps: Captures = v match { case vv: Var => Vector(name -> vv); case _ => Vector.empty }
      FreshOpened(env.putLocal(name, v), v, caps, newV)

    case t: TypeTerm =>
      val v = evalTypeTerm(t, env)
      FreshOpened(env, v, Vector.empty, BitSet.empty)

    case PatternApp(fn, args, _) =>
      val fnV = evalTypeTerm(fn, env)
      val pi = requirePi(fnV)

      if (pi.binders.length != args.length)
        throw PatternArityMismatch(fnV, pi.binders.length, args.length)

      val allNewVars = collection.mutable.BitSet.empty
      var visibleCaptures = Vector.empty[(String, Var)]

      val (nextUserEnv, _, argVals) =
        pi.binders.toList.zip(args.toList).foldLeft((env, pi.env.newScope, Vector.empty[Value])) {
          case ((curUserEnv, curFamilyEnv, curArgs), (binder, argPat)) =>
            val openedBinderTy = freshVarInternal(curFamilyEnv, binder.ty, None)
            val openedArg = freshVarInternal(curUserEnv, argPat, Some(openedBinderTy.value))

            allNewVars |= openedBinderTy.newVars
            allNewVars |= openedArg.newVars
            visibleCaptures = visibleCaptures ++ openedArg.captures

            (
              openedArg.env,
              openedBinderTy.env.putLocal(binder.name, openedArg.value),
              curArgs :+ openedArg.value
            )
        }

      val value = evalApply(fnV, NEL.mk(argVals))
      FreshOpened(nextUserEnv, value, visibleCaptures, allNewVars.toImmutable)
  }

  private def bindInternal(
      env: Env,
      pat: TypePattern,
      value: Value
  )(implicit eqStore: EqStore): Env = {
    value.tpe match {
      case LevelTpe => bindLevel(env, pat, value)
      case _ =>
        pat match {
          case Capture(name, _) => env.putLocal(name, value)

          case _: TypeTerm => env

          case PatternApp(_, patArgs, _) =>
            val args = decomposeForBinding(value, patArgs.length)
            patArgs.toVector.zip(args).foldLeft(env) { case (curEnv, (nextPat, arg)) =>
              bindInternal(curEnv, nextPat, arg)
            }
        }
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

    actual0.tpe match {
      case LevelTpe => matchLevel(userEnv, p, actual0)
      case _ =>
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
  }

  private def matchLevel(env: Env, p: TypePattern, actualTy: Value)(implicit
      eqStore: EqStore,
      normalizerMap: NormalizerMap
  ): Env = {
    val actualL = Interpreter.getLevel(actualTy)
    val o = freshVarInternal(env, p, Some(LevelTpe))
    val patternL = Interpreter.getLevel(o.value)
    if (o.captures.isEmpty) {
      TypeChecker.checkFits(actualL, patternL)
      env
    } else if (o.captures.length == 1 && patternL.atoms.size == 1 && patternL.c == 0) {
      val offset = patternL.atoms.head._2
      if (Level.geq(actualL, offset)) env.putLocal(o.captures.head._1, Value.Level.addOffset(actualL, -offset))
      else throw LevelPatternMismatch(p, actualTy)
    } else throw LevelPatternMismatch(p, actualTy)
  }

  private def bindLevel(env: Env, p: TypePattern, actualTy: Value)(implicit eqStore: EqStore): Env = {
    val o = freshVarInternal(env, p, Some(LevelTpe))
    if (o.captures.isEmpty) env
    else {
      val offset = Interpreter.getLevel(o.value).atoms.head._2
      env.putLocal(o.captures.head._1, Value.Level.addOffset(Interpreter.getLevel(actualTy), -offset))
    }
  }

  // =========================
  // Public API
  // =========================

  /** Create a fresh value for a binder and return:
    *   - The fresh value (either a Var or a VCtor for struct types)
    *   - The environment extended with any captures introduced by the binder's type pattern
    *   - The set of newly created variable IDs
    */
  def freshVar(env: Env, binder: CoreAst.Binder, meta: EqStore): (Value, Env, BitSet) = {
    implicit val eqStore: EqStore = meta
    val fo = freshVarInternal(env, binder.ty, None)
    val (fresh, extra) = freshValueForType(binder.name, fo.value, fo.env)
    (fresh, fo.env, fo.newVars ++ extra)
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
