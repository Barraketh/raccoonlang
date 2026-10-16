package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.{CoreAst => CA}

import java.util.concurrent.atomic.AtomicLong

/**
 * Match pruning proposals are accepted only when an ordinary term checks as a contradiction. This certifies exclusions;
 * it does not check successful refinement links, and the restricted N1 premise below remains trusted.
 */
private[raccoonlang] object RefinementCertificates {
  private val prefix = "\u0000raccoon.refinement."
  private val eqName = prefix + "Eq"
  private val reflName = eqName + ".refl"
  private val bottomName = prefix + "Bottom"
  private val truthName = prefix + "True"
  private val truthIntroName = truthName + ".intro"
  private val transportName = prefix + "transport"
  private val nextHelper = new AtomicLong(0L)

  private final case class Unsupported() extends RuntimeException

  private def certificateOrElse[A](fallback: => A)(body: => A): A =
    try body
    catch {
      case _: Unsupported                                                  => fallback
      case diagnostic: Diagnostic if diagnostic.error == EvaluationTooDeep => throw diagnostic
      case _: Diagnostic                                                   => fallback
    }

  private val suppressed = new ThreadLocal[Boolean] {
    override def initialValue(): Boolean = false
  }

  private def withCertificatesSuppressed[A](body: => A): A = {
    val previous = suppressed.get()
    suppressed.set(true)
    try body
    finally suppressed.set(previous)
  }

  private def freshName(label: String): String = s"$prefix$label${nextHelper.incrementAndGet()}"

  private def privateName(name: String): String =
    if (name.startsWith("Private.")) prefix + name.stripPrefix("Private.") else name

  // This transform is only for the fixed bootstrap declarations. It is not a general AST renamer.
  private def privateTerm(term: CA.Term): CA.Term = term match {
    case t: CA.Term.GlobalRef => t.copy(name = privateName(t.name))
    case t: CA.Term.LocalRef  => t
    case t: CA.Term.Select    => t.copy(base = privateTerm(t.base))
    case t: CA.Term.Pi =>
      t.copy(binders = t.binders.map(b => b.copy(ty = privateTerm(b.ty))), out = privateTerm(t.out))
    case t: CA.Term.Lam => t.copy(ty = privateTerm(t.ty).asInstanceOf[CA.Term.Pi], body = privateTerm(t.body))
    case t: CA.Term.App => t.copy(fn = privateTerm(t.fn), args = t.args.map(privateTerm))
    case t: CA.Term.Match =>
      t.copy(
        scrut = privateTerm(t.scrut),
        motive = privateTerm(t.motive),
        cases = t.cases.map(c => c.copy(ctorName = privateName(c.ctorName), body = privateTerm(c.body)))
      )
    case t: CA.Term.Body =>
      t.copy(
        lets = t.lets.map(l => l.copy(ty = l.ty.map(privateTerm), value = privateTerm(l.value))),
        res = privateTerm(t.res)
      )
    case t: CA.Term.Sort   => t.copy(level = privateTerm(t.level))
    case t: CA.Term.Prop   => t
    case t: CA.Term.FormOp => t.copy(args = t.args.map(privateTerm))
  }

  /** A checked, prelude-independent equality and transport basis. */
  private lazy val foundation: Env = withCertificatesSuppressed {
    val source =
      """
        |namespace Private {
        |inductive Eq {u: Level}(A: Type { level = u }) indices (x: A)(y: A): Prop
        | | refl(x: A): Eq(A, x, x)
        |inductive Bottom: Prop
        |inductive True: Prop
        | | intro: True
        |def transport {u: Level}{A: Type { level = u }}{x: A}{y: A}
        | (e: Eq(A, x, y))(motive: (z: A) -> Prop)(h: motive(x)): motive(y) := {
        |  match e returning motive(y) with
        |  | Eq.refl z => h
        |}
        |}
        |""".stripMargin
    val core = Prelude.fromSource("<refinement foundation>", source, Set.empty).core
    core.decls.foldLeft(Interpreter.preludeInitialEnv) { (env, declaration) =>
      val renamed = declaration match {
        case d: CA.Decl.InductiveDecl =>
          d.copy(
            header = d.header.copy(
              name = privateName(d.header.name),
              params = d.header.params.map(b => b.copy(ty = privateTerm(b.ty))),
              indices = d.header.indices.map(b => b.copy(ty = privateTerm(b.ty))),
              resultTy = privateTerm(d.header.resultTy)
            ),
            ctors = d.ctors.map(c =>
              c.copy(
                canonicalName = privateName(c.canonicalName),
                binders = c.binders.map(b => b.copy(ty = privateTerm(b.ty))),
                resultTy = privateTerm(c.resultTy)
              )
            )
          )
        case d: CA.Decl.ConstDecl =>
          d.copy(
            name = privateName(d.name),
            ty = privateTerm(d.ty),
            body = d.body match {
              case CA.ConstBody.TermBody(body) => CA.ConstBody.TermBody(privateTerm(body))
              case _                           => throw Unsupported()
            }
          )
        case _ => throw Unsupported()
      }
      Interpreter.addPreludeDecl(env, renamed)
    }
  }

  /** Hooks used only by package tests. They never bypass the checked refutation boundary. */
  private final case class TestState(forceProposals: Boolean, wrongQuotation: Boolean, transform: CA.Term => CA.Term)

  private val testState = new ThreadLocal[TestState] {
    override def initialValue(): TestState = TestState(false, false, identity)
  }

  private[raccoonlang] object Testing {
    def proposes: Boolean = testState.get().forceProposals && !suppressed.get()

    def transform(term: CA.Term): CA.Term = testState.get().transform(term)

    def withProposals[A](body: => A): A = update(_.copy(forceProposals = true))(body)

    def withWrongQuotation[A](body: => A): A = update(_.copy(wrongQuotation = true))(body)

    def withInvalidProof[A](body: => A): A =
      update(_.copy(transform = term => CA.Term.GlobalRef(eqName, term.span)))(body)

    private def update[A](change: TestState => TestState)(body: => A): A = {
      val previous = testState.get()
      testState.set(change(previous))
      try body
      finally testState.set(previous)
    }

    def quotation(term: CA.Term, value: Value, context: Env): CA.Term =
      if (!testState.get().wrongQuotation) term
      else
        context.locals.iterator
          .collectFirst {
            case (ref, bound)
                if ValueEquivalence.defEq(bound.tpe, value.tpe) && !ValueEquivalence.defEq(bound, value) =>
              CA.Term.LocalRef(ref, term.span)
          }
          .getOrElse(term)
  }

  private final case class Equation(left: Value, right: Value, proof: CA.Term)

  /** Reify only terms whose checked value is the value requested. Unsupported forms are left uncertified. */
  private final class Quoter(env: Env, span: Span) {
    private def global(name: String): CA.Term = CA.Term.GlobalRef(name, span)

    private def sameObject(left: Value, right: Value): Boolean =
      left.asInstanceOf[AnyRef] eq right.asInstanceOf[AnyRef]

    private def local(value: Value): Option[CA.Term] = env.locals.iterator.collectFirst {
      case (ref, bound) if sameObject(bound, value) => CA.Term.LocalRef(ref, span)
      case (ref, Var(_, leftId, _)) if (value match {
            case Var(_, rightId, _) => leftId == rightId
            case _                  => false
          }) =>
        CA.Term.LocalRef(ref, span)
      // Proof values carry no witness. Any checked local of the same proposition is a valid quotation by proof
      // irrelevance, and the final check below still verifies the exact requested type.
      case (ref, bound)
          if Sorts.isProposition(value.tpe) && ValueEquivalence.defEq(bound.tpe, value.tpe) &&
            ValueEquivalence.defEq(bound, value) =>
        CA.Term.LocalRef(ref, span)
    }

    private def levelParameter(id: VarId): CA.Term = env.locals.iterator
      .collectFirst {
        case (ref, level: Level) if Level.singleVariableOffset(level).contains(id -> 0) =>
          CA.Term.LocalRef(ref, span)
      }
      .getOrElse(throw Unsupported())

    private def level(level: Level): CA.Term = {
      def offset(term: CA.Term, amount: Int): CA.Term =
        (0 until amount).foldLeft(term)((result, _) => CA.Term.FormOp(CA.LevelForm.LevelSucc, Vector(result), span))

      val constant =
        if (level.c == 0 && level.terms.nonEmpty) Vector.empty
        else Vector(offset(CA.Term.FormOp(CA.LevelForm.LevelZero, Vector.empty, span), level.c))
      val variables = level.terms.toVector.sortBy(_._1).map { case (id, amount) =>
        offset(levelParameter(id), amount)
      }
      (constant ++ variables)
        .reduceLeftOption((left, right) => CA.Term.FormOp(CA.LevelForm.LevelMax, Vector(left, right), span))
        .getOrElse(CA.Term.FormOp(CA.LevelForm.LevelZero, Vector.empty, span))
    }

    private def pi(value: VPi): CA.Term.Pi = {
      var scope = env
      var closure = value.env
      val binders = value.binders.map { source =>
        val binderType = Interpreter.evalTerm(source.ty, closure)
        val quotedType = new Quoter(scope, span)(binderType)
        val ref = SyntheticLocalRef.fresh(source.name)
        val fresh = BinderOps.freshBinderValue(source.name, binderType)
        val binder = CA.Binder(
          ref,
          quotedType,
          span,
          CA.BinderSite.Function,
          isImplicit = source.isImplicit
        )
        scope = scope.putLocal(ref, fresh)
        closure = closure.putLocal(source.localRef, fresh)
        binder
      }
      val output = new Quoter(scope, span)(value.codomain(closure))
      CA.Term.Pi(binders, output, span, NodeId.fresh())
    }

    def apply(value: Value): CA.Term =
      local(value).getOrElse {
        value match {
          case c: VConst          => global(c.name)
          case h: ConstructorHead => global(h.name)
          case ConstructorForm(name, fields) =>
            val head = env(name).asInstanceOf[ConstructorHead]
            val family = value.tpe match {
              case InductiveFamilyValue(instance) => instance
              case _                              => throw Unsupported()
            }
            call(head, family.args.take(head.numErasedFamilyArgs) ++ fields)
          case app: VApp => call(app.head, app.args)
          case sort: VSort =>
            if (sort.isProp) CA.Term.Prop(span)
            else CA.Term.Sort(apply(sort.level), span)
          case parameter: Level                => level(parameter)
          case value: VPi                      => pi(value)
          case VLam(_, ValueId.Const(name), _) => global(name)
          case _                               => throw Unsupported()
        }
      }

    def constructor(head: ConstructorHead, family: InductiveFamilyInstance, fields: Vector[Value]): CA.Term =
      call(head, family.args.take(head.numErasedFamilyArgs) ++ fields)

    private def call(head: Value, args: Vector[Value]): CA.Term = head.tpe match {
      case pi: VPi =>
        val explicit = pi.binders.zip(args).collect { case (binder, arg) if !binder.isImplicit => apply(arg) }
        CA.Term.App(apply(head), explicit, span)
      case _ if args.isEmpty => apply(head)
      case _                 => throw Unsupported()
    }
  }

  private final class Search(original: Env, span: Span) {
    private var env = original.copy(globals = original.globals ++ foundation.globals.filter(_._1.startsWith(prefix)))

    private def global(name: String): CA.Term = CA.Term.GlobalRef(name, span)

    private def app(name: String, args: CA.Term*): CA.Term = CA.Term.App(global(name), args.toVector, span)

    private def quote(value: Value, context: Env): CA.Term = {
      val candidate = Testing.quotation(new Quoter(context, span)(value), value, context)
      val checked = TypeChecker.checkTerm(candidate, value.tpe, context)
      if (!ValueEquivalence.defEq(checked.value, value)) throw Unsupported()
      candidate
    }

    private def isDataType(tpe: Value): Boolean =
      tpe.tpe match {
        case sort: VSort => !sort.isProp
        case _           => false
      }

    private def equality(left: Value, right: Value, context: Env): CA.Term = {
      if (!isDataType(left.tpe) || !ValueEquivalence.defEq(left.tpe, right.tpe)) throw Unsupported()
      app(eqName, quote(left.tpe, context), quote(left, context), quote(right, context))
    }

    private def binder(ref: CA.LocalRef, ty: CA.Term, site: CA.BinderSite): CA.Binder =
      CA.Binder(ref, ty, span, site)

    private def pi(binders: Vector[CA.Binder], output: CA.Term): CA.Term.Pi =
      CA.Term.Pi(binders, output, span, NodeId.fresh())

    private def lam(binders: Vector[CA.Binder], output: CA.Term, body: CA.Term): CA.Term.Lam =
      CA.Term.Lam(pi(binders, output), body, span, NodeId.fresh(), None, None)

    /**
     * Close a helper over only its actual typed captures. An assumed body is used solely for the checked N1 premise;
     * every generated no-confusion and field-injection function has a checked lambda body.
     */
    private def helper(
        signature: CA.Term.Pi,
        body: Option[CA.Term],
        context: Env,
        label: String
    ): (String, Vector[CA.Term]) = {
      val available = context.locals.keySet -- signature.binders.map(_.localRef)
      var refs = (CA.mentionedRefs(signature) ++ body.toSet.flatMap(CA.mentionedRefs)) intersect available
      var frontier = refs
      var types = Map.empty[CA.LocalRef, CA.Term]
      while (frontier.nonEmpty) {
        val dependencies = frontier.flatMap { ref =>
          val quotedType = quote(context(ref).tpe, context)
          types += ref -> quotedType
          CA.mentionedRefs(quotedType) intersect available
        }
        frontier = dependencies -- refs
        refs ++= frontier
      }
      val captures = context.locals.keysIterator.collect {
        case ref if refs(ref) => binder(ref, types(ref), CA.BinderSite.Parameter)
      }.toVector
      val all = signature.copy(binders = captures ++ signature.binders, id = NodeId.fresh())
      val closed = env.closeForEval(Set.empty)
      val checkedType = TypeChecker.checkDeclType(all, closed)
      val name = freshName(label)
      val value = body match {
        case Some(term) =>
          TypeChecker
            .checkTerm(CA.Term.Lam(all, term, span, NodeId.fresh(), None, None), checkedType.value, closed)
            .value
        // The only assumed helper is N1, installed after its complete signature checks.
        case None => Value.canonicalizeProof(VConst(name, Symbol, checkedType.value))
      }
      env = env.putGlobal(name, value)
      (name, captures.map(b => CA.Term.LocalRef(b.localRef, span)))
    }

    private def applyHelper(helper: (String, Vector[CA.Term]), args: Vector[CA.Term]): CA.Term =
      CA.Term.App(global(helper._1), helper._2 ++ args, span)

    /** Restricted N1: same checked data-family head, with a signature-checked premise for one argument only. */
    private def nominal(equation: Equation, index: Int, context: Env): CA.Term = {
      val left = equation.left match {
        case InductiveFamilyValue(family) if !Sorts.isProposition(equation.left) => family
        case _                                                                   => throw Unsupported()
      }
      val right = equation.right match {
        case InductiveFamilyValue(family) if !Sorts.isProposition(equation.right) => family
        case _                                                                    => throw Unsupported()
      }
      if (
        !(left.meta eq right.meta) || !left.meta.block.isInstanceOf[CheckedInductiveBlockSchema] ||
        index < 0 || index >= left.args.length || index >= right.args.length
      )
        throw Unsupported()
      val output = equality(left.args(index), right.args(index), context)
      TypeChecker.checkTypeTerm(output, context)
      val signature = pi(
        Vector(
          binder(
            SyntheticLocalRef.fresh("familyEquality"),
            equality(equation.left, equation.right, context),
            CA.BinderSite.Function
          )
        ),
        output
      )
      val assumed = helper(signature, None, context, "N1")
      applyHelper(assumed, Vector(equation.proof))
    }

    /** A complete constructor discriminator, transported along a homogeneous data equality. */
    private def clash(equation: Equation, context: Env): CA.Term = {
      val leftName = equation.left match {
        case ConstructorForm(name, _) => name
        case _                        => throw Unsupported()
      }
      val leftFamily = equation.left.tpe match {
        case InductiveFamilyValue(family) if !Sorts.isProposition(equation.left.tpe) => family
        case _                                                                       => throw Unsupported()
      }
      val rightName = equation.right match {
        case ConstructorForm(name, _) => name
        case _                        => throw Unsupported()
      }
      val rightFamily = equation.right.tpe match {
        case InductiveFamilyValue(family) if !Sorts.isProposition(equation.right.tpe) => family
        case _                                                                        => throw Unsupported()
      }
      if (
        leftName == rightName || !(leftFamily.meta eq rightFamily.meta) ||
        !leftFamily.meta.constructorNames.contains(leftName) || !leftFamily.meta.constructorNames.contains(rightName)
      )
        throw Unsupported()
      val leftHead = context(leftName).asInstanceOf[ConstructorHead]
      val rightHead = context(rightName).asInstanceOf[ConstructorHead]
      if (!leftHead.noConfusion || !rightHead.noConfusion) throw Unsupported()

      val valueRef = SyntheticLocalRef.fresh("noConfusionValue")
      val trueType = global(truthName)
      val motiveCases = leftFamily.meta.constructorNames.map { name =>
        val head = context(name).asInstanceOf[ConstructorHead]
        val fields = head.fieldBinders.map(b => CA.PatternVar(SyntheticLocalRef.fresh(b.name), span))
        CA.Case(name, true, fields, if (name == leftName) trueType else global(bottomName), span)
      }
      val discriminator = lam(
        Vector(binder(valueRef, quote(equation.left.tpe, context), CA.BinderSite.Function)),
        CA.Term.Prop(span),
        CA.Term.Match(
          CA.Term.LocalRef(valueRef, span),
          CA.Term.Prop(span),
          motiveCases,
          span,
          NodeId.fresh()
        )
      )
      TypeChecker.checkTerm(discriminator, context)
      app(transportName, equation.proof, discriminator, global(truthIntroName))
    }

    /** Same-constructor injection by checked equality elimination; dependent coordinates must be homogeneous. */
    private def inject(equation: Equation, fieldIndex: Int, context: Env): CA.Term = {
      val (name, leftFields) = equation.left match {
        case ConstructorForm(constructor, fields) => (constructor, fields)
        case _                                    => throw Unsupported()
      }
      val rightFields = equation.right match {
        case ConstructorForm(`name`, fields) => fields
        case _                               => throw Unsupported()
      }
      val head = context(name).asInstanceOf[ConstructorHead]
      if (!head.noConfusion || leftFields.length != rightFields.length || fieldIndex >= leftFields.length)
        throw Unsupported()
      val family = equation.left.tpe match {
        case InductiveFamilyValue(instance) => instance
        case _                              => throw Unsupported()
      }

      var leftEnv = head.fieldEnv(family.args)
      var rightEnv = head.fieldEnv(family.args)
      var scope = context
      val parameters = Vector.newBuilder[CA.Binder]
      val arguments = Vector.newBuilder[CA.Term]
      val leftValues = Vector.newBuilder[Value]
      val rightValues = Vector.newBuilder[Value]

      head.fieldBinders.zipWithIndex.foreach { case (source, index) =>
        def fresh(tpe: Value, actual: Value): Value = {
          val ref = SyntheticLocalRef.fresh(source.name)
          parameters += binder(ref, quote(tpe, scope), CA.BinderSite.Function)
          arguments += quote(actual, context)
          val value = BinderOps.freshBinderValue(source.name, tpe)
          scope = scope.putLocal(ref, value)
          value
        }

        val leftType = Interpreter.evalTerm(source.ty, leftEnv)
        val rightType = Interpreter.evalTerm(source.ty, rightEnv)
        val left = fresh(leftType, leftFields(index))
        val right =
          if (
            ValueEquivalence.defEq(leftFields(index), rightFields(index)) &&
            ValueEquivalence.defEq(leftType, rightType)
          ) left
          else fresh(rightType, rightFields(index))
        leftValues += left
        rightValues += right
        leftEnv = leftEnv.putLocal(source.localRef, left)
        rightEnv = rightEnv.putLocal(source.localRef, right)
      }

      val left = leftValues.result()
      val right = rightValues.result()
      val leftType = head.pi.fold(head.tpe)(_.codomain(leftEnv))
      val rightType = head.pi.fold(head.tpe)(_.codomain(rightEnv))
      val leftCtor = VCtor(head, left, leftType)
      val rightCtor = VCtor(head, right, rightType)
      val output = equality(left(fieldIndex), right(fieldIndex), scope)
      val equationRef = SyntheticLocalRef.fresh("constructorEquality")
      val reflValueRef = SyntheticLocalRef.fresh("equalConstructor")
      val body = CA.Term.Match(
        CA.Term.LocalRef(equationRef, span),
        output,
        Vector(
          CA.Case(
            reflName,
            true,
            Vector(CA.PatternVar(reflValueRef, span)),
            app(reflName, quote(left(fieldIndex), scope)),
            span
          )
        ),
        span,
        NodeId.fresh()
      )
      val generated = helper(
        pi(
          parameters.result() :+ binder(equationRef, equality(leftCtor, rightCtor, scope), CA.BinderSite.Function),
          output
        ),
        Some(body),
        scope,
        "noConfusion"
      )
      applyHelper(generated, arguments.result() :+ equation.proof)
    }

    private def refute(equations: Vector[Equation], store: EqStore, depth: Int): CA.Term = {
      if (depth > 512) throw Unsupported()
      val context = ValueOps.materializeEnv(env, store)
      val pending = equations
        .map(e => e.copy(left = ValueOps.materialize(e.left, store), right = ValueOps.materialize(e.right, store)))
        .filterNot(e => ValueEquivalence.defEq(e.left, e.right))
      if (pending.isEmpty) throw Unsupported()

      pending.foreach { equation =>
        (equation.left, equation.right) match {
          case (ConstructorForm(left, _), ConstructorForm(right, _))
              if left != right && ValueEquivalence.defEq(equation.left.tpe, equation.right.tpe) =>
            certificateOrElse[Option[CA.Term]](None)(Some(clash(equation, context))) match {
              case Some(proof) => return proof
              case None        =>
            }
          case _ =>
        }
      }

      pending.zipWithIndex.foreach { case (equation, index) =>
        val solution = (equation.left, equation.right) match {
          case (variable: Var, value) if !value.synDeps.contains(variable.id) => Some(variable -> value)
          case (value, variable: Var) if !value.synDeps.contains(variable.id) => Some(variable -> value)
          case _                                                              => None
        }
        solution.foreach { case (variable, value) =>
          val next = store.allow(DepSet(variable.id)).addLink(variable.id, value)
          val body = refute(pending.patch(index, Nil, 1), next, depth + 1)
          val equalValue = SyntheticLocalRef.fresh("equalValue")
          return CA.Term.Match(
            equation.proof,
            global(bottomName),
            Vector(CA.Case(reflName, true, Vector(CA.PatternVar(equalValue, span)), body, span)),
            span,
            NodeId.fresh()
          )
        }
      }

      pending.zipWithIndex.foreach { case (equation, index) =>
        val pairs = (equation.left, equation.right) match {
          case (ConstructorForm(leftName, left), ConstructorForm(rightName, right)) if leftName == rightName =>
            left.zip(right).zipWithIndex.map { case ((a, b), field) => (a, b, Left(field)) }
          case (InductiveFamilyValue(left), InductiveFamilyValue(right))
              if (left.meta eq right.meta) && !Sorts.isProposition(equation.left) &&
                left.meta.block.isInstanceOf[CheckedInductiveBlockSchema] =>
            left.args.zip(right.args).zipWithIndex.map { case ((a, b), argument) => (a, b, Right(argument)) }
          case _ => Vector.empty
        }
        val derived = pairs.flatMap { case (left, right, coordinate) =>
          if (!ValueEquivalence.defEq(left.tpe, right.tpe) || ValueEquivalence.defEq(left, right)) None
          else
            certificateOrElse[Option[Equation]](None) {
              val premise = coordinate match {
                case Left(field) => inject(equation, field, context)
                case Right(arg)  => nominal(equation, arg, context)
              }
              Some(Equation(left, right, premise))
            }
        }
        if (derived.nonEmpty) return refute(pending.patch(index, derived, 1), store, depth + 1)
      }
      throw Unsupported()
    }

    private def localEquation(left: Value, right: Value, context: Env, label: String): Option[Equation] =
      certificateOrElse[Option[Equation]](None)(
        localEquation(left, right, equality(left, right, context), context, label)
      )

    private def localEquation(
        left: Value,
        right: Value,
        propositionTerm: CA.Term,
        context: Env,
        label: String
    ): Option[Equation] =
      certificateOrElse[Option[Equation]](None) {
        val proposition = TypeChecker.checkTypeTerm(propositionTerm, context).value
        if (!Sorts.isProposition(proposition)) throw Unsupported()
        val ref = SyntheticLocalRef.fresh(label)
        env = env.putLocal(ref, Value.canonicalizeProof(VProof(proposition)))
        Some(Equation(left, right, CA.Term.LocalRef(ref, span)))
      }

    def discharge(
        scrutinee: Value,
        scrutineeTerm: CA.Term,
        family: InductiveFamilyInstance,
        head: ConstructorHead,
        fields: Vector[Value],
        resultType: Value
    ): Boolean = {
      fields.zipWithIndex.foreach { case (value, index) =>
        val ref = SyntheticLocalRef.fresh(head.fieldBinders(index).name)
        val checkedType = TypeChecker.checkTypeTerm(quote(value.tpe, env), env)
        if (!ValueEquivalence.defEq(checkedType.value, value.tpe)) throw Unsupported()
        env = env.putLocal(ref, Value.canonicalizeProof(value))
      }

      val ctor = VCtor(head, fields, resultType)
      val ctorTerm = new Quoter(env, span).constructor(head, family, fields)
      val checkedCtor = TypeChecker.checkTerm(ctorTerm, env)
      if (
        !ValueEquivalence.defEq(checkedCtor.value, ctor) || !ValueEquivalence.defEq(checkedCtor.value.tpe, resultType)
      )
        throw Unsupported()

      val resultFamily = resultType match {
        case InductiveFamilyValue(instance) if instance.meta eq family.meta => instance
        case _                                                              => throw Unsupported()
      }
      val indexPairs = family.args
        .drop(family.meta.block.key.numParams)
        .zip(resultFamily.args.drop(family.meta.block.key.numParams))
        .filter { case (left, right) =>
          !Sorts.isProposition(left.tpe) && ValueEquivalence.defEq(left.tpe, right.tpe) &&
          !ValueEquivalence.defEq(left, right)
        }

      // Each index is independent. One unquotable function index must not hide a usable data-index refutation.
      val equations = indexPairs.flatMap { case (left, right) =>
        localEquation(left, right, env, "constructorIndex")
      }

      val checkedScrutinee = TypeChecker.checkTerm(scrutineeTerm, env)
      if (!ValueEquivalence.defEq(checkedScrutinee.value, scrutinee)) throw Unsupported()
      val valueEquation =
        if (isDataType(scrutinee.tpe) && ValueEquivalence.defEq(scrutinee.tpe, ctor.tpe))
          certificateOrElse[Option[Equation]](None) {
            localEquation(
              scrutinee,
              ctor,
              app(eqName, quote(scrutinee.tpe, env), scrutineeTerm, quote(ctor, env)),
              env,
              "constructorValue"
            )
          }
        else None

      val proof = refute(equations ++ valueEquation, EqStore.empty, 0)
      TypeChecker.checkTerm(Testing.transform(proof), env(bottomName), env)
      true
    }
  }

  /** No candidate store crosses this boundary. A failed certificate keeps the candidate with an empty store. */
  def excludes(
      scrutinee: Value,
      scrutineeTerm: CA.Term,
      family: InductiveFamilyInstance,
      head: ConstructorHead,
      fields: Vector[Value],
      resultType: Value,
      env: Env,
      span: Span
  ): Boolean =
    if (suppressed.get()) false
    else
      withCertificatesSuppressed {
        certificateOrElse(false) {
          new Search(env, span).discharge(scrutinee, scrutineeTerm, family, head, fields, resultType)
        }
      }
}
