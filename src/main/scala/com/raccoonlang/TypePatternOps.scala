package com.raccoonlang

import com.raccoonlang.CoreAst.Term.{Capture, PatternApp}
import com.raccoonlang.CoreAst.{TypePattern, TypeTerm}
import com.raccoonlang.Interpreter._
import com.raccoonlang.Util.NEL
import com.raccoonlang.Value._

import scala.collection.immutable.BitSet

object TypePatternOps {
  private final case class FreshOpened(
      env: Env,
      tpe: Value,
      newVars: BitSet,
      value: Option[Value]
  )

  private sealed trait OpenMode {
    def evalTypeTerm(term: TypeTerm, env: Env)(implicit eqStore: EqStore): Value

    def bindPattern(env: Env, pattern: TypePattern, actual: Value)(implicit eqStore: EqStore): Env
  }

  private case object UncheckedOpenMode extends OpenMode {
    override def evalTypeTerm(term: TypeTerm, env: Env)(implicit eqStore: EqStore): Value =
      Interpreter.evalTypeTerm(term, env)

    override def bindPattern(env: Env, pattern: TypePattern, actual: Value)(implicit eqStore: EqStore): Env =
      bindInternal(env, pattern, actual)
  }

  private final case class CheckedOpenMode(normalizers: NormalizerMap) extends OpenMode {
    override def evalTypeTerm(term: TypeTerm, env: Env)(implicit eqStore: EqStore): Value =
      TypeChecker.evalTypeTerm(term, env)(eqStore, normalizers)

    override def bindPattern(env: Env, pattern: TypePattern, actual: Value)(implicit eqStore: EqStore): Env =
      matchOpenInternal(env, pattern, actual)(eqStore, normalizers)
  }

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
      case Some((SortHead, args)) if fnHead == SortHead => args
      case Some((ValueHead(actualHead), args)) =>
        fnHead match {
          case ValueHead(expectedHead) if TypeChecker.defEq(actualHead, expectedHead) => args
          case _ => throw PatternHeadMismatch(fn, actual)
        }
      case _ => throw PatternHeadMismatch(fn, actual)
    }
  }

  private def decomposeForBinding(actual: Value, expectedArity: Int)(implicit eqStore: EqStore): Vector[Value] =
    actualHeadView(actual) match {
      case Some((_, args)) if args.length == expectedArity => args
      case Some((_, args)) =>
        throw WTF(s"Pattern bind arity mismatch: expected $expectedArity args, got ${args.length} in $actual")
      case None => throw WTF(s"Failed to deconstruct $actual")
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

          case PatternApp(fn, patArgs, sp) =>
            val fnV = env.find(fn.name).getOrElse(throw NotFound(fn.name))
            val pi = requirePi(fnV)
            if (pi.binders.length != patArgs.length)
              throw PatternArityMismatch(fnV, pi.binders.length, patArgs.length, Some(sp))

            val orderedPatArgs = ArgumentOps.reorder(patArgs, pi.binders, Some(sp))
            val args = decomposeForBinding(value, orderedPatArgs.length)
            orderedPatArgs.toVector.zip(args).foldLeft(env) { case (curEnv, (nextPat, arg)) =>
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

          case PatternApp(fn, args, sp) =>
            val fnV = evalTypeTerm(fn, userEnv)
            val pi = requirePi(fnV)

            if (pi.binders.length != args.length)
              throw PatternArityMismatch(fnV, pi.binders.length, args.length, Some(sp))

            val orderedArgs = ArgumentOps.reorder(args, pi.binders, Some(sp))

            val actualArgs = decomposeForPatternHeadDef(fnV, actual0)
            if (actualArgs.length != orderedArgs.length)
              throw PatternArityMismatch(fnV, orderedArgs.length, actualArgs.length, Some(sp))

            val (nextUserEnv, _) =
              pi.binders.toList.zip(orderedArgs.toList).zip(actualArgs).foldLeft((userEnv, pi.env.newScope)) {
                case ((curUserEnv, curPiEnv), ((binder, argPat), actualArg)) =>
                  val nextPiEnv = bindInternal(curPiEnv, binder.ty, actualArg.tpe).putLocal(binder.name, actualArg)
                  val nextUserEnv = matchOpenInternal(curUserEnv, argPat, actualArg)
                  (nextUserEnv, nextPiEnv)
              }
            nextUserEnv
        }
    }
  }

  // TODO: This is very simplified - clean this up
  private def openLevelPattern(env: Env, p: TypePattern)(implicit eqStore: EqStore): (Value, Option[String]) = p match {
    case term: TypeTerm   => (Interpreter.evalTypeTerm(term, env), None)
    case Capture(name, _) => (FreshVar.freshVar(name, LevelTpe), Some(name))
    case PatternApp(fn, args, _) =>
      val fnV = Interpreter.evalTerm(fn, env)
      val pi = requirePi(fnV)
      if (pi.binders.length != args.length)
        throw PatternArityMismatch(fnV, pi.binders.length, args.length, Some(p.span))
      val orderedArgs = ArgumentOps.reorder(args, pi.binders, Some(p.span))
      val openArgs = orderedArgs.map(a => openLevelPattern(env, a))
      val captures = openArgs.map(_._2).toList.collect { case Some(name) => name }
      val capture = if (captures.length > 1) throw MultipleLevelCaptures(p, Some(p.span)) else captures.headOption
      Interpreter.evalApply(fnV, openArgs.map(_._1)) -> capture
  }

  private def matchLevel(env: Env, p: TypePattern, actualTy: Value)(implicit
      eqStore: EqStore,
      normalizerMap: NormalizerMap
  ): Env = {
    val actualL = Interpreter.getLevel(actualTy)
    val (levelTpe, capture) = openLevelPattern(env, p)
    val patternL = Interpreter.getLevel(levelTpe)

    capture match {
      case Some(captureName) =>
        if (patternL.atoms.size != 1 || patternL.c != 0) throw LevelPatternMismatch(p, actualTy)
        val offset = patternL.atoms.head._2
        if (Level.geq(actualL, offset)) env.putLocal(captureName, Value.Level.addOffset(actualL, -offset))
        else throw LevelPatternMismatch(p, actualTy)
      case None =>
        TypeChecker.checkFits(actualL, patternL)
        env
    }
  }

  private def bindLevel(env: Env, p: TypePattern, actualTy: Value)(implicit eqStore: EqStore): Env = {
    val (levelTpe, captures) = openLevelPattern(env, p)

    captures match {
      case Some(captureName) =>
        val offset = Interpreter.getLevel(levelTpe).atoms.head._2
        env.putLocal(captureName, Value.Level.addOffset(Interpreter.getLevel(actualTy), -offset))
      case None => env
    }
  }

  private case class OpenedArgs(env: Env, piEnv: Env, vars: Vector[Value], newVarIds: BitSet)

  private def openArgsAgainstBinders(
      env: Env,
      piEnv: Env,
      args: Vector[TypePattern],
      binders: Vector[CoreAst.Binder],
      mode: OpenMode
  )(implicit
      eqStore: EqStore
  ): OpenedArgs = {
    val newVarIds = collection.mutable.BitSet()
    val vars = collection.mutable.ArrayBuffer[Value]()
    var myEnv = env

    val newPiEnv = args.zip(binders).foldLeft(piEnv) { case (piEnv, (arg, piBinder)) =>
      val piOpened = openPatternInternal(piEnv, piBinder.ty, mode)
      val argV = arg match {
        case tt: TypeTerm => mode.evalTypeTerm(tt, myEnv)
        case Capture(name, _) =>
          val v = piOpened.value.getOrElse {
            val v = FreshVar.freshVar(piBinder.name, piOpened.tpe)
            newVarIds += v.id
            v
          }
          myEnv = myEnv.putLocal(name, v)
          v
        case p: PatternApp =>
          val myOpened = openPatternInternal(myEnv, p, mode)
          newVarIds |= myOpened.newVars
          myOpened.tpe
      }
      vars += argV
      piEnv.putLocal(piBinder.name, argV)
    }

    OpenedArgs(myEnv, newPiEnv, vars.toVector, newVarIds.toImmutable)
  }

  /** Open a type pattern without an expected actual value.
    *
    * This is used when forming binder types: concrete type terms evaluate normally, while captures are only meaningful
    * inside an application pattern where the callee telescope gives them an expected type. For ordinary applications we
    * walk the callee binders left-to-right, recursively opening each binder type, evaluating concrete arguments, and
    * replacing captured or nested pattern arguments with fresh values. The returned environment contains only the
    * user-visible captures introduced by the pattern; derived fresh binders stay private but are reported in `newVars`
    * so equality can later refine them.
    *
    * Struct families get a special path because an argument pattern like `S $A $I` should create a representative
    * struct value, not just the family type. We instantiate constructor params from the supplied param patterns,
    * freshen constructor fields, build the constructor result, and then bind the supplied index patterns against the
    * indexes found in that result type.
    */
  private def openPatternInternal(env: Env, pattern: TypePattern, mode: OpenMode)(implicit
      eqStore: EqStore
  ): FreshOpened = {
    pattern match {
      case tt: TypeTerm => FreshOpened(env, mode.evalTypeTerm(tt, env), BitSet.empty, None)
      case Capture(name, _) =>
        throw PatternCaptureNeedsExpectedType(name)
      case PatternApp(fn, args, sp) =>
        val fnV = env.find(fn.name).getOrElse(throw NotFound(fn.name))
        resolveInEqStore(fnV) match {
          case VConst(_, Inductive(meta), _) if meta.isStruct =>
            val expectedTypeArgs = meta.paramCount + meta.indexCount
            if (args.length != expectedTypeArgs) throw PatternArityMismatch(fnV, expectedTypeArgs, args.length, Some(sp))

            val familyPi = requirePi(fnV)
            val patternArgs = ArgumentOps.reorder(args, familyPi.binders, Some(sp)).toVector
            val ctorName = meta.constructorNames.head
            env.find(ctorName).getOrElse(throw NotFound(ctorName)) match {
              case h: ConstructorHead =>
                val pi = requirePi(h)

                val openedParams = openArgsAgainstBinders(
                  env,
                  pi.env,
                  patternArgs.take(h.numParams),
                  pi.binders.toVector.take(h.numParams),
                  mode
                )

                val openedFields = ConstructorOps.freshFields(pi, h.numParams, openedParams.piEnv, eqStore)
                val res = ConstructorOps.fromFreshFields(h, pi, openedFields, eqStore).value
                val resultTypeArgs = decomposeForBinding(res.tpe, expectedTypeArgs)

                val resultEnv =
                  patternArgs.drop(h.numParams).zip(resultTypeArgs.drop(h.numParams)).foldLeft(openedParams.env) {
                    case (curEnv, (indexPattern, resultIndex)) => mode.bindPattern(curEnv, indexPattern, resultIndex)
                  }

                FreshOpened(resultEnv, res.tpe, openedParams.newVarIds ++ openedFields.newVars, Some(res))
              case _ => throw WTF("Ctor not a constructor head")
            }
          case _ =>
            val pi = requirePi(fnV)
            if (pi.binders.length != args.length)
              throw PatternArityMismatch(fnV, pi.binders.length, args.length, Some(sp))

            val orderedArgs = ArgumentOps.reorder(args, pi.binders, Some(sp))
            val openedArgs = openArgsAgainstBinders(env, pi.env, orderedArgs.toVector, pi.binders.toVector, mode)
            val res = Interpreter.evalApply(fnV, NEL.mk(openedArgs.vars.toList))
            FreshOpened(openedArgs.env, res, openedArgs.newVarIds, None)
        }

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
    val f = openPatternInternal(env, binder.ty, UncheckedOpenMode)
    f.value match {
      case Some(v) =>
        (v, f.env, f.newVars)
      case None =>
        val v = FreshVar.freshVar(binder.name, f.tpe)
        (v, f.env, f.newVars + v.id)
    }
  }

  def freshVarAndCheck(env: Env, binder: CoreAst.Binder, meta: EqStore)(implicit
      normalizers: NormalizerMap
  ): (Value, Env, BitSet) = {
    implicit val eqStore: EqStore = meta
    val f = openPatternInternal(env, binder.ty, CheckedOpenMode(normalizers))
    f.value match {
      case Some(v) =>
        (v, f.env, f.newVars)
      case None =>
        val v = FreshVar.freshVar(binder.name, f.tpe)
        (v, f.env, f.newVars + v.id)
    }
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
