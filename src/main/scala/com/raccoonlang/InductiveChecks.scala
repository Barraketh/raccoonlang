package com.raccoonlang

import com.raccoonlang.CoreAst._
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

object InductiveChecks {

  // A family label stores an argument value. A universe argument costs its own
  // level, while a Pi domain costs its full classifier (the function's graph). A
  // record with structure eta costs the most of its fields, so a `Proto` costs
  // level 0, as its components do: every value of it is its constructor applied
  // to its fields (raccoon-formalization DESIGN.md §10, the elementwise rank
  // lemma).
  private def familyArgumentLevel(tpe: Value): Level = tpe match {
    case LevelTpe | KindTpe | PropTpe => Level.zero
    case VUniv(_, level)              => level
    case InductiveFamilyValue(_) if StructEta.eligible(tpe).isDefined =>
      val fields = StructEta.fields(FreshVar.freshVar("record", tpe)).getOrElse(Vector.empty)
      Level.max(Level.zero +: fields.map(field => familyArgumentLevel(field.tpe)))
    case pi: VPi if pi.tpe != PropTpe =>
      val fresh = BinderOps.freshen(pi)
      val domainLevels =
        pi.binders.map(binder => TypeChecker.classifierLevel(TypeChecker.getUniverse(fresh(binder.localRef).tpe)))
      Level.max(domainLevels :+ familyArgumentLevel(pi.codomain(fresh)))
    case other => TypeChecker.classifierLevel(TypeChecker.getUniverse(other))
  }

  // ------------ Occurrence and Positivity ------------

  // A positivity target is the thing whose occurrences we are checking.
  // The traversal only needs two queries:
  //
  // - isDirectOccurrence identifies a value that is exactly the target.
  // - mayOccurIn is the conservative fallback for opaque leaves, which the
  //   traversal does not inspect structurally.
  private sealed trait PositivityTarget {
    def isDirectOccurrence(value: Value): Boolean
    def mayOccurIn(value: Value): Boolean
  }

  private object PositivityTarget {

    /**
     * The families being declared, one or a mutual block. They are fresh: no value made before their declaration can
     * name them, so a reference to one starts only at its own head, and reaches a value only through what that value is
     * built from.
     */
    final case class InductiveBlock(names: Set[String]) extends PositivityTarget {
      override def isDirectOccurrence(value: Value): Boolean =
        value match {
          case VConst(valueName, Inductive(_), _) => names(valueName)
          case _                                  => false
        }

      override def mayOccurIn(value: Value): Boolean = false
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

  private def lambdaDoesNotContain(target: PositivityTarget, lam: VLam): Boolean =
    lam.id match {
      // A global or native function is closed and declared before the family being checked, so it cannot contain the
      // target. Opening a native function on fresh arguments would also return its own stuck application.
      case ValueId.Const(_) => true
      case _                =>
        // A function-valued family argument has no assumed variance. Its type alone
        // cannot reveal occurrences captured in the body, so require absence in
        // both the type and the body opened on fresh arguments. Blocked results use
        // the conservative occurrence rules below, including for named heads that
        // synDeps (which tracks only local variables) cannot detect.
        doesNotOccur(target, lam.tpe) && {
          val fresh = BinderOps.freshen(lam.tpe)
          val args = lam.tpe.binders.map(binder => fresh(binder.localRef))
          doesNotOccur(target, Interpreter.runLam(lam, args))
        }
    }

  /**
   * Whether every part of a word satisfies `part`, in one loop over its tokens: each layer's payloads and the end;
   * except that `positiveType` checks the layers' types instead, the positions where a word is a cons application
   * rather than an argument of one. Consecutive layers usually share one type object, which is checked once.
   */
  private def forallWordParts(word: VWord, part: Value => Boolean, positiveType: Value => Boolean): Boolean = {
    var checkedType: Value = null
    packed.Words.foreach(word)(
      layer = token =>
        (0 until token.payloadWidth).forall(index => part(token.payload(index))) &&
          ((token.tpe eq checkedType) || {
            checkedType = token.tpe
            positiveType(token.tpe)
          }),
      end = token => part(token.value)
    )
  }

  /**
   * A stuck computation (KERNEL_FOLLOWUPS 2.2; main-new's declaration-time rule): the family is absent from it when its
   * type, its captures, the local values of its environment and its match term do not mention it. By freshness, the
   * code of a computation made before the declaration cannot name the family, so only a term written in the declaration
   * itself, such as a match in a field type, needs its names read.
   */
  private def thunkDoesNotContain(target: PositivityTarget, thunk: NeutralThunk): Boolean =
    target match {
      case PositivityTarget.InductiveBlock(names) =>
        doesNotOccur(target, thunk.tpe) &&
        thunk.id.captures.forall(doesNotOccur(target, _)) &&
        thunk.env.locals.forall(_.valueOption.forall(doesNotOccur(target, _))) &&
        !names.exists(mentionsGlobal(thunk.term, _))
      case local: PositivityTarget.LocalVar => !local.mayOccurIn(thunk)
    }

  /** Whether `term` names the global `name`, anywhere in it. */
  private def mentionsGlobal(term: ElabAst.Term, name: String): Boolean = {
    def terms(ts: Iterable[ElabAst.Term]): Boolean = ts.exists(mentionsGlobal(_, name))
    def pattern(tp: ElabAst.TypePattern): Boolean =
      tp match {
        case ElabAst.TypePattern.Type(t)                   => mentionsGlobal(t, name)
        case ElabAst.TypePattern.App(fn, args, _)          => mentionsGlobal(fn, name) || args.exists(pattern)
        case ElabAst.TypePattern.Capture(_, _, constraint) => constraint.exists(pattern)
      }
    def binderType(bt: ElabAst.BinderType): Boolean =
      bt match {
        case ElabAst.BinderType.TypePattern(tp, _)                   => pattern(tp)
        case ElabAst.BinderType.ConstrainedCapture(_, constraint, _) => pattern(constraint)
      }
    term match {
      case ElabAst.Term.GlobalRef(global, _)                                          => global == name
      case _: ElabAst.Term.LocalRef | _: ElabAst.Term.NatLit | _: ElabAst.Term.StrLit => false
      case ElabAst.Term.Word(_, pieces, _) =>
        terms(pieces.flatMap {
          case ElabAst.Term.WordPiece.Layer(before, after) => before ++ after
          case ElabAst.Term.WordPiece.Splice(list)         => Vector(list)
        })
      case ElabAst.Term.App(fn, args, _)   => terms(fn +: args)
      case proj: ElabAst.Term.Proj         => proj.family == name || mentionsGlobal(proj.base, name)
      case ElabAst.Term.Body(lets, res, _) => terms(lets.flatMap(let => let.ty.toVector :+ let.value) :+ res)
      case ElabAst.Term.Match(scrut, motive, cases, _, _) => terms((scrut +: motive.toVector) ++ cases.map(_.body))
      case ElabAst.Term.Pi(binders, out, _, _, _) => binders.exists(b => binderType(b.ty)) || mentionsGlobal(out, name)
      case ElabAst.Term.Lam(ty, body, _, _, _, _, _) => mentionsGlobal(ty, name) || mentionsGlobal(body, name)
    }
  }

  private def doesNotOccur(target: PositivityTarget, value: Value): Boolean =
    if (target.isDirectOccurrence(value)) false
    else
      value match {
        case thunk: NeutralThunk => thunkDoesNotContain(target, thunk)

        case InductiveFamilyValue(instance) =>
          if (target.isDirectOccurrence(instance.head)) false
          else instance.args.forall(arg => doesNotOccur(target, arg))

        // An operand that is a form recurses through this case.
        case poly: VNatPoly => poly.form.operands.forall(operand => doesNotOccur(target, operand))

        // A cons head is closed and has no dependencies, so the target cannot occur in it.
        case word: VWord =>
          def visit(part: Value): Boolean = doesNotOccur(target, part)
          forallWordParts(word, visit, visit)

        case app: VApp =>
          doesNotOccur(target, app.head) &&
          app.args.forall(arg => doesNotOccur(target, arg)) &&
          doesNotOccur(target, app.tpe)

        case pi: VPi =>
          val freshEnv = BinderOps.freshen(pi)
          val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
          freshArgs.forall(arg => doesNotOccur(target, arg.tpe)) &&
          doesNotOccur(target, pi.codomain(freshEnv))

        case _: ConstructorHead => !target.mayOccurIn(value)

        case lam: VLam => lambdaDoesNotContain(target, lam)

        case _: Level | LevelTpe | _: Kind | KindTpe | _: VUniv | _: Var | _: VConst | PropTpe | KernelObject =>
          !target.mayOccurIn(value)
      }

  /**
   * Checks that the target only occurs positively in value: 1) Does not occur in the domain of any Pis 2) Only appears
   * in positive args of Inductives. A family of the block being declared has the positive arguments `assumed` gives it,
   * since its metadata is provisional; every other family's are its metadata's.
   */
  private def occursPositively(
      target: PositivityTarget,
      value: Value,
      assumed: Map[String, DepSet] = Map.empty
  ): Boolean =
    if (target.isDirectOccurrence(value)) true
    else
      value match {
        // A stuck computation that mentions the target cannot certify that it occurs positively.
        case thunk: NeutralThunk => thunkDoesNotContain(target, thunk)

        case InductiveFamilyValue(instance) =>
          if (target.isDirectOccurrence(instance.head)) true
          else {
            val positiveArgs = assumed.getOrElse(instance.head.name, instance.meta.positiveArgs)
            instance.args.zipWithIndex.forall { case (arg, idx) =>
              if (positiveArgs.contains(idx)) occursPositively(target, arg, assumed)
              else doesNotOccur(target, arg)
            }
          }

        // Factor bases and symbolic exponents are arguments of Nat operations, which have no positive positions.
        case poly: VNatPoly => doesNotOccur(target, poly)

        // Payloads and the end are arguments of constructors; only the layers' types may contain the target.
        case word: VWord => forallWordParts(word, doesNotOccur(target, _), occursPositively(target, _, assumed))

        case app: VApp =>
          doesNotOccur(target, app.head) &&
          app.args.forall(arg => doesNotOccur(target, arg)) &&
          occursPositively(target, app.tpe, assumed)

        case pi: VPi =>
          val freshEnv = BinderOps.freshen(pi)
          val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
          freshArgs.forall(arg => doesNotOccur(target, arg.tpe)) &&
          occursPositively(target, pi.codomain(freshEnv), assumed)

        case _: ConstructorHead => true

        case lam: VLam => lambdaDoesNotContain(target, lam)

        case _: Level | LevelTpe | _: Kind | KindTpe | _: VUniv | _: Var | _: VConst | PropTpe | KernelObject =>
          true
      }

  /**
   * Checks that we don't have things of the shape Foo(Foo(A)) as a constructor field of Foo, nor, in a mutual block,
   * Foo(Bar(A)) for a sibling Bar: the block's families' own arguments do not contain the block.
   */
  private def sameFamilyArgsDoNotContain(target: PositivityTarget, value: Value): Boolean =
    value match {
      // A stuck computation that does not mention the family holds no application of it.
      case thunk: NeutralThunk => thunkDoesNotContain(target, thunk)

      case InductiveFamilyValue(instance) =>
        if (target.isDirectOccurrence(instance.head))
          instance.args.forall(arg => doesNotOccur(target, arg))
        else
          instance.args.forall(arg => sameFamilyArgsDoNotContain(target, arg))

      case poly: VNatPoly =>
        poly.form.operands.forall(operand => sameFamilyArgsDoNotContain(target, operand))

      case word: VWord =>
        def visit(part: Value): Boolean = sameFamilyArgsDoNotContain(target, part)
        forallWordParts(word, visit, visit)

      case app: VApp =>
        doesNotOccur(target, app.head) &&
        app.args.forall(arg => sameFamilyArgsDoNotContain(target, arg)) &&
        sameFamilyArgsDoNotContain(target, app.tpe)

      case pi: VPi =>
        val freshEnv = BinderOps.freshen(pi)
        val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
        freshArgs.forall(arg => sameFamilyArgsDoNotContain(target, arg.tpe)) &&
        sameFamilyArgsDoNotContain(target, pi.codomain(freshEnv))

      case lam: VLam => lambdaDoesNotContain(target, lam)

      case _: ConstructorHead | _: Level | LevelTpe | _: Kind | KindTpe | _: VUniv | _: Var | _: VConst | PropTpe |
          KernelObject =>
        true
    }

  /** The indexes of the variables among `args` that occur positively in every one of `values`, reading `assumed`. */
  private def positiveArgIndexes(
      args: Vector[Value],
      values: Vector[Value],
      assumed: Map[String, DepSet] = Map.empty
  ): DepSet = {
    val positive = DepSet.newBuilder
    args.zipWithIndex.foreach { case (arg, idx) =>
      arg match {
        case Var(_, id, _) =>
          val target = PositivityTarget.LocalVar(id)
          if (values.forall(value => occursPositively(target, value, assumed)))
            positive.add(idx)
        case _ =>
      }
    }
    positive.result()
  }

  /**
   * How a constructor's stored fields recurse: the indexes of fields whose types mention a family of the block being
   * declared, and whether there is exactly one, whose type is the constructor's own family at its own parameters.
   */
  private final case class ConstructorRecursion(
      ctor: ConstructorDecl,
      recursiveFields: Vector[Int],
      soleFieldIsOwnInstance: Boolean
  )

  /**
   * The cons constructor and its shape, when the declaration is list-shaped: a family without indices whose values live
   * in a universe, other than the kernel's Nat, with at least two constructors, exactly one of which has a recursive
   * field. It has exactly one, whose type is the family applied to its own parameters, not nested in another family or
   * under a binder. Nat has the shape with an empty payload, and keeps its compact successor forms instead.
   */
  private def listShape(
      decl: Decl.InductiveDecl,
      familyUniverse: Universe,
      recursion: Vector[ConstructorRecursion]
  ): Option[(String, ListShape)] =
    if (
      familyUniverse == PropTpe || decl.header.indices.nonEmpty || decl.header.name == Kernel.NatName ||
      decl.ctors.length < 2
    ) None
    else
      recursion.filter(_.recursiveFields.nonEmpty) match {
        case Vector(ConstructorRecursion(ctor, Vector(field), true)) =>
          Some(ctor.canonicalName -> ListShape(field, ctor.fields.length - 1))
        case _ => None
      }

  /** The constructors of `decl`, published in `envWithHeads`, which has the final heads of its whole block. */
  private def installConstructors(
      decl: Decl.InductiveDecl,
      envWithHeads: Env,
      listShape: Option[(String, ListShape)]
  ): Env =
    decl.ctors.foldLeft(envWithHeads) { case (curEnv, ctor) =>
      val allBinders = ctor.erasedBinders ++ ctor.fields
      val fullTypeTerm =
        if (allBinders.isEmpty) ctor.resultTy
        else Term.Pi(allBinders, ctor.resultTy, ctor.span, NodeId.fresh())

      val fullType = TypeChecker.getType(fullTypeTerm, curEnv)
      val erasedFamilyArgIndexes = ctor.erasedBinders.map { binder =>
        val idx = decl.header.params.indexWhere(_.name == binder.name)
        if (idx < 0) throw InvalidErasedConstructorBinder(ctor.canonicalName, binder.name, "expected inductive param")
        idx
      }

      curEnv.putGlobal(
        ctor.canonicalName,
        ConstructorHead(
          ctor.canonicalName,
          erasedFamilyArgIndexes,
          allBinders.length,
          fullType,
          listShape.collect { case (consName, shape) if consName == ctor.canonicalName => shape }
        )
      )
    }

  /**
   * One family of a block, checked against the block's provisional heads: its type and initial metadata, its universe,
   * the positive arguments its header allows, each constructor's result arguments with its field types, for the block's
   * positive arguments, how each constructor recurses, and whether it has the shape structure eta needs (`etaShape`):
   * one constructor, no indices, no recursive field, which mentions no family of the block, and not in `Prop`.
   */
  private final case class CheckedFamily(
      decl: Decl.InductiveDecl,
      familyType: Value,
      initialMeta: InductiveMeta,
      universe: Universe,
      headerPositive: DepSet,
      constructorFields: Vector[(Vector[Value], Vector[Value])],
      recursion: Vector[ConstructorRecursion],
      etaShape: Boolean
  ) {
    def name: String = decl.header.name
  }

  /**
   * Which arguments of each family of a block are positive, so may hold a nested occurrence of a later family: the
   * greatest assignment, within what each family's header allows, under which each of them occurs positively in every
   * constructor's fields when the block's own families are read by that assignment. It starts from the headers' and
   * only shrinks, since occurring positively is monotone in the assignment, so it ends. Reading the block's families by
   * their provisional metadata, every argument positive, would accept an argument whose positivity rests on a position
   * that turns out not to be positive.
   */
  private def blockPositiveArgs(families: Vector[CheckedFamily]): Map[String, DepSet] = {
    var assumed = families.map(family => family.name -> family.headerPositive).toMap
    var stable = false
    while (!stable) {
      val next = families.map { family =>
        family.name -> family.constructorFields.foldLeft(family.headerPositive) { case (positive, (args, fields)) =>
          positive & positiveArgIndexes(args, fields, assumed)
        }
      }.toMap
      stable = next == assumed
      assumed = next
    }
    assumed
  }

  /**
   * Inductive families, one or a mutual block (docs/kernel.md, "Mutual blocks"), checked and published together. Each
   * family's type is checked where no family of the block exists yet; its constructors are checked with every family's
   * provisional head, against its own declared universe (L1), uniformity and result, and strict positivity in every
   * family of the block. Each family's universe, size rule and structure eta are its own; a field is recursive when it
   * mentions any family of the block, and the positive arguments are a fixed point over the block. Only when every
   * family has checked are the final heads, then the constructors, published.
   *
   * A family with one constructor is a record (`RecordInfo`), whose template is read from its published constructor, so
   * that a recursive field's type names the final head; each record's template and eta are forced once the block is
   * published.
   */
  def evalInductiveBlock(decls: Vector[Decl.InductiveDecl], env: Env): Env = {
    // All direct Value matches in this function and its private helpers rely on EqStore.empty: no Vars are solved in
    // this pass.
    val provisional = decls.map { decl =>
      val header = decl.header
      val ty =
        if (header.binders.isEmpty) header.resultTy
        else Term.Pi(header.binders, header.resultTy, header.span, NodeId.fresh())
      val familyType = TypeChecker.getType(ty, env)
      val initialMeta =
        InductiveMeta(
          decl.ctors.map(ctor => ConstructorMeta(ctor.shortName, ctor.canonicalName)),
          header.binders.length,
          header.params.length,
          DepSet.from(0 until header.arity)
        )
      (decl, familyType, initialMeta)
    }
    val checkEnv = provisional.foldLeft(env) { case (cur, (decl, familyType, meta)) =>
      cur.putGlobal(decl.header.name, VConst(decl.header.name, Inductive(meta), familyType))
    }
    val target = PositivityTarget.InductiveBlock(decls.map(_.header.name).toSet)
    val checked = provisional.map { case (decl, familyType, meta) =>
      checkFamily(decl, familyType, meta, checkEnv, target)
    }

    val positiveArgs = blockPositiveArgs(checked)
    // Only after all constructor checks succeed do we add the block to the environment: every final head, then the
    // constructors, whose types name the heads. A record reads its constructor from the published block.
    lazy val published: Env = checked.foldLeft(withHeads) { (cur, family) =>
      installConstructors(family.decl, cur, listShape(family.decl, family.universe, family.recursion))
    }
    lazy val records: Map[String, RecordInfo] = checked.flatMap { family =>
      family.decl.ctors match {
        case Vector(ctor) =>
          def constructor = published(ctor.canonicalName) match {
            case head: ConstructorHead => head
            case other                 => throw WTF(s"Constructor ${ctor.canonicalName} is published as $other")
          }
          val fieldNames = ctor.fields.map(_.name)
          val info =
            new RecordInfo(ctor.canonicalName, fieldNames, family.etaShape, family.familyType, () => constructor)
          Some(family.name -> info)
        case _ => None
      }
    }.toMap
    lazy val withHeads: Env = checked.foldLeft(env) { (cur, family) =>
      val meta = family.initialMeta.copy(positiveArgs = positiveArgs(family.name), record = records.get(family.name))
      cur.putGlobal(family.name, VConst(family.name, Inductive(meta), family.familyType))
    }
    records.values.foreach { info =>
      info.template
      info.eta
    }
    published
  }

  /**
   * The family `decl` of the block whose provisional heads `blockEnv` holds, `recursiveTarget` being the block, where
   * `inductiveTypeCheck` is the family's type and `initialMeta` its provisional metadata.
   */
  private def checkFamily(
      decl: Decl.InductiveDecl,
      inductiveTypeCheck: Value,
      initialMeta: InductiveMeta,
      blockEnv: Env,
      recursiveTarget: PositivityTarget
  ): CheckedFamily = {
    val header = decl.header
    val name = header.name
    val envWithFamilyBinders = {
      inductiveTypeCheck match {
        case pi: VPi =>
          assert(blockEnv.locals.isEmpty) // Sanity check
          BinderOps.freshen(pi.binders, blockEnv)
        case _ => blockEnv
      }
    }

    val familyUniverse = TypeChecker.getType(header.resultTy, envWithFamilyBinders) match {
      case v: Universe => v
      case other       => throw InductiveTypeNotASort(other, Some(header.resultTy.span))
    }

    val familyArgs =
      inductiveTypeCheck match {
        case pi: VPi => pi.binders.map(binder => envWithFamilyBinders(binder.localRef))
        case _       => Vector.empty[Value]
      }
    val argumentSizeBound = familyUniverse match {
      case PropTpe => None // Impredicative Prop families have no nominal principles.
      // Families of every kind are nominal, so all obey the size check; kinds cost nothing. Each family of a block is
      // bounded by its own declared level.
      case VUniv(_, level) => Some(level)
    }
    header.binders.zip(familyArgs).foreach { case (binder, argument) =>
      // L2: parameters and indices are unrestricted, as types hold no linear value. So are erased constructor binders
      // and capture witnesses, which name parameters.
      if (Linearity.isLinear(argument.tpe)) throw LinearFamilyArgument(name, binder.name, Some(binder.span))
      argumentSizeBound.foreach { level =>
        val required = familyArgumentLevel(argument.tpe)
        if (!Level.leq(required, level))
          throw FamilyArgumentTooLarge(name, binder.name, required, Some(binder.span))
      }
    }
    // A header names no family of its block, so this needs no assumption about the block's positive arguments.
    val headerPositive = positiveArgIndexes(familyArgs, familyArgs.map(_.tpe))

    val constructors = decl.ctors.map { ctor =>
      val (erasedBinders, _) = BinderOps.toVBinders(ctor.erasedBinders, blockEnv)
      val envWithErased = BinderOps.freshen(erasedBinders, blockEnv)
      val (fieldBinders, _) = BinderOps.toVBinders(ctor.fields, envWithErased)
      val fieldsEnv = BinderOps.freshen(fieldBinders, envWithErased)
      val fieldVars = fieldBinders.map(binder => fieldsEnv(binder.localRef))
      val fieldTypes = fieldVars.map(_.tpe)

      val outputTpe = TypeChecker.getType(ctor.resultTy, fieldsEnv)

      // 4) Constructor result must be the inductive family head applied to the full family arity.
      val resultErr = InvalidConstructorResult(ctor.canonicalName, name, outputTpe, Some(ctor.span))
      val outputArgs = outputTpe match {
        case ConstSpine(head, args) if head.name == name => args
        case _                                           => throw resultErr
      }

      if (outputArgs.length != header.arity) throw resultErr

      // Check param uniformity
      header.params.zip(outputArgs).foreach { case (param, outputArg) =>
        val erasedWitnesses = erasedBinders.collect {
          case binder if binder.name == param.name => envWithErased(binder.localRef)
        }
        val captureWitnesses = fieldBinders.flatMap { binder =>
          binder.captures.collect {
            case capture if capture.localRef.name == param.name => fieldsEnv(capture.localRef)
          }
        }
        val witnesses = erasedWitnesses ++ captureWitnesses
        val error =
          NonUniformInductiveParam(header.name, ctor.canonicalName, param.name, outputArg, Some(ctor.resultTy.span))

        if (witnesses.length != 1) throw error

        if (!ValueEquivalence.defEq(outputArg, witnesses.head))
          throw error
      }

      // No family of the block occurs in a result index (fam-10), as in Coq and Lean. An index constrains the family by
      // an equation, which no fixed point need satisfy: with propositional extensionality, `Bad((h: Bad(True)) -> False)`
      // proves False. A field variable is no occurrence, whatever its type.
      header.indices.zip(outputArgs.drop(header.params.length)).foreach { case (index, outputArg) =>
        if (!doesNotOccur(recursiveTarget, outputArg))
          throw FamilyInResultIndex(name, ctor.canonicalName, index.name, outputArg, Some(ctor.resultTy.span))
      }

      val constructorUniverse = TypeChecker.getUniverse(outputTpe)

      // Whether each stored field's type mentions a family of the block, so recurses.
      val recursiveFieldFlags = ctor.fields.zip(fieldVars).map { case (binder, field) =>
        def requireBelow(tpeLevel: Level, inductiveLevel: Level): Unit =
          if (!Level.leq(tpeLevel, inductiveLevel))
            throw InductiveUniverseTooSmall(
              name,
              s"${ctor.canonicalName}.${binder.name}",
              field.tpe,
              tpeLevel,
              inductiveLevel,
              Some(binder.span)
            )
        def linearField = LinearFieldInUnrestrictedFamily(name, binder.name, Some(binder.span))
        // 2) Universe bound (L1): a field's kind is at most the family's, in the kind lattice, and its level at most the
        // family's, which Prop families skip. A Prop family's fields are of kind copy, or proofs.
        (constructorUniverse, TypeChecker.getUniverse(field.tpe)) match {
          case (_, PropTpe) =>
          case (PropTpe, VUniv(kind, _)) =>
            if (!kind.isCopy) throw linearField
          case (VUniv(inductiveKind, inductiveLevel), VUniv(kind, level)) =>
            if (!Kind.leq(kind, inductiveKind)) throw linearField
            requireBelow(level, inductiveLevel)
        }

        // 3) Every stored constructor field type must be strictly positive in every family of the block
        if (!occursPositively(recursiveTarget, field.tpe) || !sameFamilyArgsDoNotContain(recursiveTarget, field.tpe))
          throw NonStrictlyPositive(
            inductive = name,
            ctor = ctor.canonicalName,
            field = binder.name,
            fieldTy = field.tpe,
            span = Some(binder.span)
          )

        !doesNotOccur(recursiveTarget, field.tpe)
      }

      // The result's arguments are the family's own parameters by the uniformity check above.
      val recursiveFields = recursiveFieldFlags.indices.filter(recursiveFieldFlags).toVector
      val soleFieldIsOwnInstance = recursiveFields match {
        case Vector(idx) =>
          fieldTypes(idx) match {
            case InductiveFamilyValue(instance) =>
              instance.head.name == name && instance.args.length == outputArgs.length &&
              instance.args.zip(outputArgs).forall { case (arg, own) => ValueEquivalence.defEq(arg, own) }
            case _ => false
          }
        case _ => false
      }
      ((outputArgs, fieldTypes), ConstructorRecursion(ctor, recursiveFields, soleFieldIsOwnInstance))
    }
    val recursion = constructors.map(_._2)

    val etaShape = (decl.ctors, recursion) match {
      case (Vector(_), Vector(only)) =>
        header.indices.isEmpty && familyUniverse != PropTpe && only.recursiveFields.isEmpty
      case _ => false
    }
    CheckedFamily(
      decl,
      inductiveTypeCheck,
      initialMeta,
      familyUniverse,
      headerPositive,
      constructors.map(_._1),
      recursion,
      etaShape
    )
  }
}
