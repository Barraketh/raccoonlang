package com.raccoonlang

import com.raccoonlang.CoreAst._
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

import scala.collection.immutable.BitSet

object InductiveChecks {

  // ------------ Occurrence and Positivity ------------

  // A positivity target is the thing whose occurrences we are checking.
  // The traversal only needs two queries:
  //
  // - isDirectOccurrence identifies a value that is exactly the target.
  // - mayOccurIn is the conservative fallback for values we do not inspect
  //   structurally, such as neutral computations and opaque leaves.
  private sealed trait PositivityTarget {
    def isDirectOccurrence(value: Value): Boolean
    def mayOccurIn(value: Value): Boolean
  }

  private object PositivityTarget {
    final case class InductiveHead(name: String) extends PositivityTarget {
      override def isDirectOccurrence(value: Value): Boolean =
        value match {
          case VConst(valueName, Inductive(_), _) => valueName == name
          case _                                  => false
        }

      override def mayOccurIn(value: Value): Boolean =
        value match {
          // A lambda's body (and a thunk's code) can mention the inductive without it showing
          // anywhere the traversal looks; be conservative. The surface grammar cannot currently
          // place a lambda in a field type, but that must not be what soundness rests on.
          case _: NeutralThunk => true
          case _: VLam         => true
          case _               => false
        }
    }

    final case class LocalVar(id: VarId) extends PositivityTarget {
      override def isDirectOccurrence(value: Value): Boolean =
        value match {
          case Var(_, valueId, _) => valueId == id
          case _                  => false
        }

      override def mayOccurIn(value: Value): Boolean = value.synDeps.contains(id)
    }
  }

  private def doesNotOccur(target: PositivityTarget, value: Value): Boolean =
    if (target.isDirectOccurrence(value)) false
    else
      value match {
        case _: NeutralThunk => !target.mayOccurIn(value)

        case InductiveFamilyValue(instance) =>
          if (target.isDirectOccurrence(instance.head)) false
          else instance.args.forall(arg => doesNotOccur(target, arg))

        case app: VApp =>
          doesNotOccur(target, app.head) &&
          app.args.forall(arg => doesNotOccur(target, arg)) &&
          doesNotOccur(target, app.tpe)

        case pi: VPi =>
          val freshEnv = BinderOps.freshen(pi)
          val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
          freshArgs.forall(arg => doesNotOccur(target, arg.tpe)) &&
          doesNotOccur(target, pi.codomain(freshEnv))

        // A proof's interior is erased; its type is all that can carry an occurrence.
        case p: VProof => doesNotOccur(target, p.tpe)

        case p: VPacked => doesNotOccur(target, p.tpe)

        case _: ConstructorHead => !target.mayOccurIn(value)

        case _: Level | LevelTpe | _: VLam | _: VSort | _: Var | _: VConst | PropTpe =>
          !target.mayOccurIn(value)
      }

  /**
   * Checks that the target only occurs positively in value: 1) Does not occur in the domain of any Pis 2) Only appears
   * in positive args of Inductives
   */
  private def occursPositively(target: PositivityTarget, value: Value): Boolean =
    if (target.isDirectOccurrence(value)) true
    else
      value match {
        case _: NeutralThunk => !target.mayOccurIn(value)

        case InductiveFamilyValue(instance) =>
          if (target.isDirectOccurrence(instance.head)) true
          else
            instance.args.zipWithIndex.forall { case (arg, idx) =>
              if (instance.meta.positiveArgs.contains(idx)) occursPositively(target, arg)
              else doesNotOccur(target, arg)
            }

        case app: VApp =>
          doesNotOccur(target, app.head) &&
          app.args.forall(arg => doesNotOccur(target, arg)) &&
          occursPositively(target, app.tpe)

        case pi: VPi =>
          val freshEnv = BinderOps.freshen(pi)
          val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
          freshArgs.forall(arg => doesNotOccur(target, arg.tpe)) &&
          occursPositively(target, pi.codomain(freshEnv))

        // Strict: a proof value embedded in a type (e.g. an index) must not mention the target in
        // its proposition at all — positivity through an erased interior is unjustifiable.
        case p: VProof => doesNotOccur(target, p.tpe)

        case p: VPacked => doesNotOccur(target, p.tpe)

        case _: ConstructorHead => true

        case _: Level | LevelTpe | _: VLam | _: VSort | _: Var | _: VConst =>
          true
      }

  /**
   * Checks that we don't have things of the shape Foo(Foo(A)) as a constructor field of Foo.
   */
  private def sameFamilyArgsDoNotContain(inductiveName: String, target: PositivityTarget, value: Value): Boolean =
    value match {
      case _: NeutralThunk => false

      case InductiveFamilyValue(instance) =>
        if (instance.head.name == inductiveName)
          instance.args.forall(arg => doesNotOccur(target, arg))
        else
          instance.args.forall(arg => sameFamilyArgsDoNotContain(inductiveName, target, arg))

      case app: VApp =>
        doesNotOccur(target, app.head) &&
        app.args.forall(arg => sameFamilyArgsDoNotContain(inductiveName, target, arg)) &&
        sameFamilyArgsDoNotContain(inductiveName, target, app.tpe)

      case pi: VPi =>
        val freshEnv = BinderOps.freshen(pi)
        val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
        freshArgs.forall(arg => sameFamilyArgsDoNotContain(inductiveName, target, arg.tpe)) &&
        sameFamilyArgsDoNotContain(inductiveName, target, pi.codomain(freshEnv))

      case p: VProof => sameFamilyArgsDoNotContain(inductiveName, target, p.tpe)

      case p: VPacked => sameFamilyArgsDoNotContain(inductiveName, target, p.tpe)

      case _: ConstructorHead | _: Level | LevelTpe | _: VLam | _: VSort | _: Var | _: VConst =>
        true
    }

  private def positiveArgIndexes(args: Vector[Value], values: Vector[Value]): DepSet = {
    val positive = DepSet.newBuilder
    args.zipWithIndex.foreach { case (arg, idx) =>
      arg match {
        case Var(_, id, _) =>
          val target = PositivityTarget.LocalVar(id)
          if (values.forall(value => occursPositively(target, value)))
            positive.add(idx)
        case _ =>
      }
    }
    positive.result()
  }

  private def constructorFamilyParams(header: InductiveHeader): Vector[Binder] =
    header.params.map(_.copy(isImplicit = true))

  private def constructorBinders(header: InductiveHeader, ctor: ConstructorDecl): Vector[Binder] =
    constructorFamilyParams(header) ++ ctor.binders

  private def referencedLocals(term: Term): Set[LocalRef] = {
    val refs = Set.newBuilder[LocalRef]

    def go(term: Term): Unit =
      term match {
        case _: Term.NatLit | _: Term.StrLit | _: Term.GlobalRef =>
        case Term.LocalRef(ref, _)                               => refs += ref
        case Term.Select(base, _, _)                             => go(base)
        case Term.Proj(_, _, base, _)                            => go(base)
        case Term.Pi(binders, out, _) =>
          binders.foreach(binder => go(binder.ty))
          go(out)
        case Term.App(fn, args, _) =>
          go(fn)
          args.foreach(go)
        case Term.Body(lets, res, _) =>
          lets.foreach { let =>
            let.ty.foreach(go)
            go(let.value)
          }
          go(res)
        case Term.Lam(ty, body, _, _, _) =>
          go(ty)
          go(body)
        case Term.Match(scrut, motive, cases, _) =>
          go(scrut)
          motive.foreach(go)
          cases.foreach(c => go(c.body))
      }

    go(term)
    refs.result()
  }

  /** Precise transitive preceding-field dependencies of each stored field type. */
  private def constructorFieldDependencies(ctor: ConstructorDecl): Vector[BitSet] = {
    val fieldIndex = ctor.binders.zipWithIndex.map { case (binder, idx) => binder.localRef -> idx }.toMap
    val result = Array.fill(ctor.binders.length)(BitSet.empty)
    var idx = 0
    while (idx < ctor.binders.length) {
      val direct = BitSet.fromSpecific(referencedLocals(ctor.binders(idx).ty).flatMap(fieldIndex.get).filter(_ < idx))
      result(idx) = direct.foldLeft(direct) { case (dependencies, dependency) =>
        dependencies ++ result(dependency)
      }
      idx += 1
    }
    result.toVector
  }

  private def installInductive(
      decl: Decl.InductiveDecl,
      baseEnv: Env,
      inductiveHead: VConst
  ): Env = {
    val envWithInductive = baseEnv.putGlobal(decl.header.name, inductiveHead)

    decl.ctors.foldLeft(envWithInductive) { case (curEnv, ctor) =>
      val allBinders = constructorBinders(decl.header, ctor)
      val fullTypeTerm =
        if (allBinders.isEmpty) ctor.resultTy
        else Term.Pi(allBinders, ctor.resultTy, ctor.span)

      val fullType = TypeChecker.getConstructorType(fullTypeTerm, curEnv, decl.header.params.length)
      curEnv.putGlobal(
        ctor.canonicalName,
        ConstructorHead(ctor.canonicalName, decl.header.params.length, allBinders.length, fullType)
      )
    }
  }

  private def checkConstructorParamDiscipline(
      header: InductiveHeader,
      ctor: ConstructorDecl,
      envWithBinders: Env,
      outputArgs: Vector[Value]
  ): Unit =
    header.params.zipWithIndex.foreach { case (param, idx) =>
      val paramValue = envWithBinders(param.localRef)
      val outputArg = outputArgs(idx)
      val error =
        NonUniformInductiveParam(header.name, ctor.canonicalName, param.name, outputArg, Some(ctor.resultTy.span))

      if (!ValueEquivalence.defEq(outputArg, paramValue))
        throw error
    }

  def evalInductiveDecl(decl: Decl.InductiveDecl, env: Env): Env = {
    // All direct Value matches in this function and its private helpers
    // rely on EqStore.empty: no Vars are solved in this pass.

    val header = decl.header
    val name = header.name
    val ty = {
      if (header.binders.isEmpty) decl.header.resultTy
      else Term.Pi(header.binders, decl.header.resultTy, decl.header.span)
    }

    val inductiveType = TypeChecker.getType(ty, env)

    val initialPositiveArgs = DepSet.from(0 until header.arity)
    // projectionInfo stays None while this declaration's own constructors are being checked: the
    // constructor head does not exist yet, so a self-referential field type must not trigger expansion.
    val initialMeta =
      InductiveMeta(
        decl.ctors.map(ctor => ConstructorMeta(ctor.shortName, ctor.canonicalName)),
        decl.header.binders.length,
        initialPositiveArgs,
        projectionInfo = None,
        proofRecovery = None
      )

    val provisionalHead = VConst(name, Inductive(initialMeta), inductiveType)

    val envWithInductive = env.putGlobal(name, provisionalHead)
    val envWithFamilyBinders = {
      inductiveType match {
        case pi: VPi =>
          assert(envWithInductive.locals.isEmpty) // Sanity check
          BinderOps.freshen(pi.binders, envWithInductive)
        case _ => envWithInductive
      }
    }

    val declaredSort = TypeChecker.getType(header.resultTy, envWithFamilyBinders) match {
      case v: VSort => v
      case other    => throw InductiveTypeNotASort(other, Some(header.resultTy.span))
    }

    val recursiveTarget = PositivityTarget.InductiveHead(name)
    val familyArgs =
      inductiveType match {
        case pi: VPi => pi.binders.map(binder => envWithFamilyBinders(binder.localRef))
        case _       => Vector.empty[Value]
      }
    var positiveArgs = positiveArgIndexes(familyArgs, familyArgs.map(_.tpe))
    var hasRecursiveField = false
    // A family whose declared universe is positive under every level assignment can never have a
    // Prop instance, so proof representation metadata would be dead weight. Retain a candidate only
    // for Prop and universe-polymorphic families whose result level may reduce to zero.
    var proofFieldPlan = Option.when(decl.ctors.length == 1 && !Level.isNeverZero(declaredSort.level)) {
      (Vector.empty[ProofFieldSource], false)
    }

    decl.ctors.foreach { ctor =>
      val allConstructorBinders = constructorBinders(header, ctor)
      val checkedBinders =
        BinderOps.checkBinders(allConstructorBinders, envWithInductive, familyParams = header.params.length)
      val binders = checkedBinders.binders
      val envWithBinders = checkedBinders.env
      val binderVars = binders.map(binder => envWithBinders(binder.localRef))
      val ownBinderVars = binderVars.drop(header.params.length)

      val outputTpe = TypeChecker.getType(ctor.resultTy, envWithBinders)

      // 4) Constructor result must be the inductive family head applied to the full family arity.
      val resultErr = InvalidConstructorResult(ctor.canonicalName, name, outputTpe, Some(ctor.span))
      val outputArgs = outputTpe match {
        case ConstSpine(head, args) if head.name == name => args
        case _                                           => throw resultErr
      }

      if (outputArgs.length != header.arity) throw resultErr

      checkConstructorParamDiscipline(header, ctor, envWithBinders, outputArgs)

      // Compile data sources for the one-constructor family's proof-recovery plan. Whether a
      // field is a proof is classified later at the actual family instance, so universe-polymorphic
      // fields that become proofs at u := 0 need no declaration-time special case.
      if (proofFieldPlan.nonEmpty) {
        val sources = ownBinderVars.map { field =>
          val resultIndex = outputArgs.indexWhere(arg => ValueEquivalence.defEq(arg, field))
          if (resultIndex >= 0) ProofFieldSource.ResultArgument(resultIndex)
          else ProofFieldSource.Unavailable
        }
        val definitelyComplete = ownBinderVars.zip(sources).forall { case (field, source) =>
          Value.isPropositionType(field.tpe) || source != ProofFieldSource.Unavailable
        }
        proofFieldPlan = Some((sources, definitelyComplete))
      }

      val constructorUniverse = TypeChecker.getUniverse(outputTpe)
      val constructorArgs = ctor.binders.zip(ownBinderVars)
      val constructorArgTypes = constructorArgs.map(_._2.tpe)

      constructorArgs.foreach { case (binder, field) =>
        // 2) Universe bound: skip for Prop families; enforce for Sort families
        constructorUniverse match {
          case PropTpe => // no universe restriction
          case VSort(inductiveLevel) =>
            TypeChecker.getUniverse(field.tpe) match {
              case Value.PropTpe =>

              case VSort(tpeLevel) =>
                if (!Level.leq(tpeLevel, inductiveLevel))
                  throw InductiveUniverseTooSmall(
                    name,
                    s"${ctor.canonicalName}.${binder.name}",
                    field.tpe,
                    tpeLevel,
                    inductiveLevel,
                    Some(binder.span)
                  )
            }
        }

        if (!doesNotOccur(recursiveTarget, field.tpe)) hasRecursiveField = true

        // 3) Every stored constructor field type must be strictly positive in the inductive
        if (
          !occursPositively(recursiveTarget, field.tpe) || !sameFamilyArgsDoNotContain(name, recursiveTarget, field.tpe)
        )
          throw NonStrictlyPositive(
            inductive = name,
            ctor = ctor.canonicalName,
            field = binder.name,
            fieldTy = field.tpe,
            span = Some(binder.span)
          )
      }

      positiveArgs = positiveArgs & positiveArgIndexes(outputArgs, constructorArgTypes)

    }

    // A one-constructor family gets positional projection metadata regardless of indices or recursion. Structure eta
    // is the narrower Lean gate: zero indices and no recursive occurrence. Prop instances are filtered dynamically by
    // StructEta.eligibleInstance and follow their declaration-compiled recovery plan.
    //
    // The constructor head is a promise completed after installation: constructor types are checked against the
    // installed family head, so the head cannot exist before installInductive runs.
    var installedCtorHead: Option[ConstructorHead] = None
    val projectionInfo =
      if (decl.ctors.length == 1) {
        val ctor = decl.ctors.head
        Some(
          new ProjectionInfo(
            constructorFieldDependencies(ctor),
            etaEligible = header.indices.isEmpty && !hasRecursiveField,
            () => installedCtorHead
          )
        )
      } else None

    val proofRecovery = for {
      (fields, definitelyComplete) <- proofFieldPlan
      info <- projectionInfo
    } yield new ProofRecoveryInfo(fields, info, definitelyComplete)
    val meta = initialMeta.copy(
      positiveArgs = positiveArgs,
      projectionInfo = projectionInfo,
      proofRecovery = proofRecovery
    )

    val inductiveHead = VConst(name, Inductive(meta), inductiveType)

    // Only after all constructor checks succeed do we add the decl to the environment.
    val finalEnv = installInductive(decl, env, inductiveHead)
    if (decl.ctors.length == 1) {
      val ctorName = decl.ctors.head.canonicalName
      installedCtorHead = Some(
        finalEnv(ctorName) match {
          case h: ConstructorHead => h
          case other              => throw WTF(s"Constructor $ctorName resolved to non-constructor $other")
        }
      )
      // Complete and validate the circular metadata/head link before publishing the environment.
      projectionInfo.foreach(_.ctorHead)
    }
    finalEnv
  }
}
