package com.raccoonlang

import com.raccoonlang.CoreAst.{Decl, Program, RawTypeTerm, Term => CTerm}
import com.raccoonlang.Util.NEL
import com.raccoonlang.Value._

object Interpreter {
  private def normalizeLevel(l: Level)(implicit eqStore: EqStore): Level = {
    val pieces = Vector(Level.const(l.c)) ++
      l.atoms.toVector.map { case (atom, k) =>
        val base = eqStore.subst.get(atom) match {
          case Some(sol) =>
            eqStore.force(sol) match {
              case next: Level   => normalizeLevel(next)
              case Var(_, id, _) => Level.mk(id)
              case other         => throw NotALevel(other)
            }
          case None => Level.mk(atom)
        }
        Level.addOffset(base, k)
      }
    Level.max(pieces)
  }

  def resolveInEqStore(v: Value)(implicit eqStore: EqStore): Value = {
    val v0 = eqStore.force(v)
    v0 match {
      case v0: Blocked if eqStore.subst.contains(v0.blockerId) =>
        v0 match {
          case VBlockedApp(h, args, tpe, _) =>
            val h0 = resolveInEqStore(h)
            h0 match {
              case lam: VLam =>
                val res = lam.run(NEL.mk(args), eqStore)
                resolveInEqStore(res)
              case b: Blocker =>
                VBlockedApp(b, args, tpe, b.blockerId)
              case other =>
                resolveInEqStore(evalApply(other, NEL.mk(args)))
            }
          case vm: VBlockedThunk => resolveInEqStore(vm.thunk(eqStore))
        }

      case l: Level if l.atoms.keySet.intersect(eqStore.subst.keySet).nonEmpty => normalizeLevel(l)

      case _ => v0
    }
  }

  private def getEnvWithArgs(fnTpe: VPi, args: NEL[Value])(implicit eqStore: EqStore) =
    BinderOps.instantiateFull(fnTpe.binders, fnTpe.env, args)

  def evalPi(pi: CTerm.Pi[CoreAst.Checked], env: Env, vBinders: NEL[VBinder])(implicit eqStore: EqStore): VPi = {
    val captureVals = FreeNames.getFreeRefs(pi).valuesIn(env)
    val id = ValueId.LocalId(pi.span.start, captureVals)

    val fresh = BinderOps.freshen(vBinders, env)
    val vars = fresh.vars
    val bodyEnv = fresh.env
    val outType = evalTypeTerm(pi.out, bodyEnv)

    val piClassifier: Universe = TypeChecker.getUniverse(outType) match {
      case PropTpe => PropTpe
      case VSort(outLevel) =>
        val domLevels: Vector[Level] = vars
          .map(v => TypeChecker.getUniverse(v.tpe))
          .collect { case VSort(level) => level }

        VSort(Level.max(domLevels :+ outLevel))
    }

    VPi(
      env,
      vBinders,
      codomain = (env, eqStore) => evalTypeTerm(pi.out, env)(eqStore),
      FreeNames.getDeps(pi, env),
      id,
      piClassifier
    )
  }

  private def evalPi(pi: CTerm.Pi[CoreAst.Checked], env: Env)(implicit eqStore: EqStore): VPi = {
    evalPi(pi, env, pi.binders.map(TypePatternOps.toVBinder))
  }

  def evalTypeTerm(tt: CoreAst.CheckedTypeTerm, env: Env)(implicit meta: EqStore): Value = tt match {
    case ref: CTerm.Ref[CoreAst.Checked]  => evalRef(ref, env)
    case CTerm.Select(base, field, span)  => evalSelect(evalTerm(base, env), field, env, span.start)
    case CTerm.App(fn, args, _)           => evalApplyTerm(fn, args, env)
    case CTerm.TSelect(base, field, span) => evalSelect(evalTypeTerm(base, env), field, env, span.start)
    case CTerm.TApp(fn, args, _)          => evalApplyTerm(fn, args.toVector, env)
    case pi: CTerm.Pi[CoreAst.Checked]    => evalPi(pi, env)
  }

  private def evalRef(ref: CoreAst.CheckedRef, env: Env): Value = {
    val res = ref match {
      case CTerm.GlobalRef(name, _) => env(name)
      case CTerm.LocalRef(local, _) => env(local)
    }
    res match {
      case h: ConstructorHead if h.totalArity == 0 => VCtor(h, Vector.empty, h.tpe)
      case _                                       => res
    }
  }

  def evalApply(fn: Value, vArgs: NEL[Value])(implicit eqStore: EqStore): Value = {
    val fn0 = resolveInEqStore(fn)
    val tpe0 = resolveInEqStore(fn0.tpe)

    tpe0 match {
      case pi: VPi =>
        val envWithArgs: Env = getEnvWithArgs(pi, vArgs)
        fn0 match {
          case VLam(_, _, isStable, run) =>
            val res = run(vArgs, eqStore)
            (isStable, res) match {
              case (true, b: Blocked) =>
                b match {
                  case VBlockedApp(VLam(_, _, true, _), _, _, _) => res
                  case _                                         => VBlockedApp(fn0, vArgs.toList, b.tpe, b.blockerId)
                }
              case _ => res
            }
          case h: VConst => VApp(h, vArgs.toVector, pi.codomain(envWithArgs, eqStore))
          case h: ConstructorHead =>
            val resultTy = pi.codomain(envWithArgs, eqStore)
            ConstructorOps.ConstructorShape.require(h).makeCtor(vArgs.toVector, resultTy)
          case b: Blocker => VBlockedApp(b, vArgs.toList, pi.codomain(envWithArgs, eqStore), b.blockerId)
          case _          => throw CannotApplyNonFunction(fn)
        }
      case _ => throw CannotApplyNonFunction(fn.tpe)
    }
  }

  private def evalApplyTerm(fn: CoreAst.CheckedTerm, args: Vector[CoreAst.CheckedTerm], env: Env)(implicit
      eqStore: EqStore
  ): Value = {
    val vf = evalTerm(fn, env)
    val vArgs = args.map(a => evalTerm(a, env))
    if (vArgs.isEmpty) throw CannotApplyNonFunction(Interpreter.resolveInEqStore(vf.tpe))
    evalApply(vf, NEL.mk(vArgs))
  }

  def evalLam(l: CTerm.Lam[CoreAst.Checked], vpi: VPi, env: Env): VLam = {
    val id = l.name match {
      case Some(funcName) => ValueId.Const(funcName)
      case None =>
        val captureVals = FreeNames.getFreeRefs(l).valuesIn(env)
        ValueId.LocalId(l.span.start, captureVals)

    }
    lazy val self: VLam = VLam(
      vpi,
      id,
      l.isStable,
      (args, eqStore) => {
        val bodyEnv = getEnvWithArgs(vpi, args)(eqStore)
        val recurEnv =
          l.name match {
            case Some(name) => bodyEnv.putGlobal(name, self)
            case None       => bodyEnv
          }
        val res = evalTerm(l.body, recurEnv)(eqStore)
        res match {
          case u: UpdatableType =>
            val tpe = vpi.codomain(bodyEnv, eqStore)
            u.withTpe(tpe)
          case _ => res
        }
      }
    )
    self
  }

  private def evalLam(l: CTerm.Lam[CoreAst.Checked], env: Env)(implicit eqStore: EqStore): VLam = {
    val vpi = evalPi(l.ty, env)
    evalLam(l, vpi, env)
  }

  def getLevel(v: Value)(implicit eqStore: EqStore): Level = {
    resolveInEqStore(v) match {
      case l: Level => l
      case v: Var   => Level.mk(v.id)
      case v        => throw NotALevel(v)
    }
  }

  def evalTerm(term: CoreAst.CheckedTerm, env: Env)(implicit eqStore: EqStore): Value = {
    try {
      term match {
        case CTerm.Select(base, field, span) => evalSelect(evalTerm(base, env), field, env, span.start)
        case CTerm.App(fn, args, _)          => evalApplyTerm(fn, args, env)
        case tt: CoreAst.CheckedTypeTerm     => evalTypeTerm(tt, env)
        case l: CTerm.Lam[CoreAst.Checked]   => evalLam(l, env)
        case m: CTerm.Match[CoreAst.Checked] => evalMatch(m, env)
        case b: CTerm.Body[CoreAst.Checked]  => evalBody(b, env)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }
  }

  private def computeSelectResultTypeFrom(vType: Value, field: String, env: Env)(implicit eqStore: EqStore): Value = {
    val vt0 = resolveInEqStore(vType)
    val (indName, meta, typeArgs) = vt0 match {
      case VConst(n, Inductive(m), _)              => (n, m, Vector.empty[Value])
      case VApp(VConst(n, Inductive(m), _), as, _) => (n, m, as)
      case other                                   => throw NotAType(other)
    }

    if (!meta.isStruct) throw NotAStruct(indName)
    val ctorName = meta.constructorNames.head

    env(ctorName) match {
      case head: ConstructorHead =>
        if (!head.isStruct) throw NotAStruct(indName)
        ConstructorOps.structFieldType(head, typeArgs, field)
      case _ => throw NotFound(ctorName)
    }
  }

  def evalSelect(v: Value, field: String, env: Env, locationId: Int)(implicit eqStore: EqStore): Value = {
    val v0 = resolveInEqStore(v)
    v0 match {
      case VCtor(head, fields, _) =>
        if (!head.isStruct) throw NotAStruct(head.name)

        val fieldBinders = ConstructorOps.ConstructorShape.require(head).fieldBinders
        val idx = fieldBinders.indexWhere(_.name == field)
        if (idx >= 0 && idx < fields.length && fieldBinders(idx).name != "_") fields(idx)
        else throw NotFound(field)

      case b: Blocker =>
        val resultTy = computeSelectResultTypeFrom(v0.tpe, field, env)
        val id = ValueId.LocalId(locationId, Vector(v0))
        VBlockedThunk(eqStore => evalSelect(v, field, env, locationId)(eqStore), id, resultTy, b.blockerId)
      case _ =>
        val resultTy = computeSelectResultTypeFrom(v0.tpe, field, env)
        val head = VConst(s"select.$field", Symbol, KernelObject)
        VApp(head, Vector(v), resultTy)
    }
  }

  private def evalMatch(m: CTerm.Match[CoreAst.Checked], env: Env)(implicit eqStore: EqStore): Value = {
    def computeMatchCaptures(): Vector[Value] = FreeNames.getFreeRefs(m).valuesIn(env)

    val scrut = resolveInEqStore(evalTerm(m.scrut, env))

    def outType: Value = m.motive match {
      case Some(motive) => evalTypeTerm(motive, env)
      case None         => scrut.tpe
    }

    def mkStuckMatch(): Value = {
      val head = VConst(s"match#${m.span.start}", Symbol, KernelObject)
      VApp(head, computeMatchCaptures(), outType)
    }

    def mkBlockedMatch(b: Blocker): Value = {
      val lamId = ValueId.LocalId(m.span.start, computeMatchCaptures())
      VBlockedThunk(eqStore => evalMatch(m, env)(eqStore), lamId, outType, b.blockerId)
    }

    val (head, args) = scrut match {
      case VCtor(head, fields, _) => (head, fields)
      case b: Blocker             => return mkBlockedMatch(b)
      case _                      => return mkStuckMatch()
    }

    val ctorName = head.name
    val branch =
      m.cases.find(c => c.ctorName == ctorName).getOrElse(throw UnknownConstructor(ctorName, "", Some(m.span)))
    if (args.length != branch.argRefs.length)
      throw ArityMismatch(branch.argRefs.length, args.length, Some(branch.span))
    val newEnv = args.zip(branch.argRefs).foldLeft(env) { case (curEnv, (argV, argRef)) =>
      argRef match {
        case Some(ref) => curEnv.putLocal(ref, argV)
        case None      => curEnv
      }
    }
    evalTerm(branch.body, newEnv)
  }

  def evalBody(body: CTerm.Body[CoreAst.Checked], env: Env)(implicit eqStore: EqStore): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = evalTerm(l.value, curEnv)
      val withTpe = (res, l.ty) match {
        case (u: UpdatableType, Some(ty)) =>
          u.withTpe(evalTypeTerm(ty, curEnv))
        case _ => res
      }
      val instanceKey = if (l.isInstance) Some(InstanceSearch.instanceKey(l.localRef.name, withTpe, eqStore)) else None
      curEnv.putLocal(l.localRef, withTpe, instanceKey, Some(CTerm.LocalRef[CoreAst.Checked](l.localRef, l.span)))
    }
    evalTerm(body.res, newEnv)
  }

  case class Worlds(checkEnv: Env, runEnv: Env)

  def evalDecl(decl: Decl, worlds: Worlds): Worlds = {
    implicit val eqStore = EqStore.empty
    implicit val normalizers = NormalizerMap.empty

    decl match {
      case Decl.ConstDecl(unfoldStrategy, name, ty, body, _, isInstance) =>
        val checkedTy = TypeChecker.getCheckedType(ty, worlds.checkEnv)
        val tyV = checkedTy.value
        val declConst = VConst(name, Symbol, tyV)

        val checkedBody = TypeChecker.check(body, worlds.checkEnv)
        val bodyV0 = checkedBody.value

        TypeChecker.checkType(bodyV0, tyV)
        val bodyV = Value.ascribe(bodyV0, tyV)

        val checkValue: Value = unfoldStrategy match {
          case Some(_) => bodyV
          case None    => declConst
        }
        val checkInstanceKey = if (isInstance) Some(InstanceSearch.instanceKey(name, checkValue, eqStore)) else None
        val nextCheckEnv = worlds.checkEnv.putGlobal(name, checkValue, checkInstanceKey)

        val runtimeTyV = Interpreter.evalTypeTerm(checkedTy.term, worlds.runEnv)
        val runtimeBodyV = Value.ascribe(Interpreter.evalTerm(checkedBody.term, worlds.runEnv), runtimeTyV)
        val runInstanceKey = if (isInstance) Some(InstanceSearch.instanceKey(name, runtimeBodyV, eqStore)) else None
        val nextRunEnv = worlds.runEnv.putGlobal(name, runtimeBodyV, runInstanceKey)

        Worlds(nextCheckEnv, nextRunEnv)

      case d: Decl.InductiveDecl => InductiveChecks.evalInductiveDecl(d, worlds)

    }

  }

  def run(p: Program): Option[Value] = {
    val baseEnv =
      Env.empty
        .putGlobal("Type", VSort(Level.zero))
        .putGlobal("Normalizer", NormalizerType)
        .putGlobal("Level", LevelTpe)
        .putGlobal("Level::zero", Level.zero)
        .putGlobal("Level::one", Level.const(1))
        .putGlobal("Prop", PropTpe)

    val builtinFuncs = List[(String, RawTypeTerm, (NEL[Value], EqStore) => Value)](
      (
        "add_normalizer",
        parseHeader("(A: Type)(zero: A)(add: A -> A -> A): Normalizer"),
        (args, _) => Normalizers.add_normalizer(args.toVector)
      ),
      (
        "Level::succ",
        parseHeader("(l: Level): Level"),
        (args, eqStore) => Value.Level.succ(getLevel(args.head)(eqStore))
      ),
      (
        "Level::max",
        parseHeader("(l1: Level)(l2: Level): Level"),
        (args, eqStore) => Value.Level.max(args.map(l => getLevel(l)(eqStore)).toVector)
      )
    )

    val env2 = builtinFuncs.foldLeft(baseEnv) { case (curEnv, (name, tpe, lam)) =>
      val tpeV = TypeChecker.evalTypeTerm(tpe, curEnv)(EqStore.empty, NormalizerMap.empty)
      tpeV match {
        case pi: VPi =>
          curEnv.putGlobal(name, VLam(pi, ValueId.Const(name), isStable = true, lam))
        case _ => curEnv
      }
    }

    val nextEnv = env2.putGlobal(
      "Sort",
      VLam(
        {
          val lRef = CoreAst.LocalRef(0, "l")
          val levelRef = CTerm.GlobalRef[CoreAst.Checked]("Level", Span(0, 0))
          VPi(
            env2,
            NEL.one(
              VBinder(
                lRef,
                CoreAst.TypePattern.Type(levelRef),
                levelRef,
                Vector.empty
              )
            ),
            (env, eqStore) => {
              val l = getLevel(env(lRef))(eqStore)
              VSort(Level.succ(l))
            },
            DepSet.empty,
            ValueId.Const("Sort"),
            VSort(Level.zero)
          )
        },
        ValueId.Const("Sort"),
        true,
        (args, eqStore) => {
          val l = getLevel(args(0))(eqStore)
          VSort(l)
        }
      )
    )

    val worlds = p.decls.foldLeft(Worlds(nextEnv, nextEnv)) { case (curWorlds, decl) => evalDecl(decl, curWorlds) }
    p.body.map { b =>
      val checked = TypeChecker.check(b, worlds.checkEnv)(EqStore.empty, NormalizerMap.empty)
      Interpreter.evalTerm(checked.term, worlds.runEnv)(EqStore.empty)
    }
  }

  private def parseHeader(s: String): RawTypeTerm = {
    LanguageParser.parseFuncHeader(s) match {
      case Success(header, _, _) => Elaborator.getType(header)
      case err: Failure          => throw new RuntimeException(err.message)
    }
  }
}
