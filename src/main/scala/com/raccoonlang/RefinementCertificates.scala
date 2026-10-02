package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.{CoreAst => CA}

/** Pruning proposals acquire authority only through an ordinary checked refutation. Links remain unchanged. */
private[raccoonlang] object RefinementCertificates {
  private val prefix = "\u0000refinement."
  private val eqName = prefix + "Eq"
  private val reflName = eqName + ".refl"
  private val bottomName = prefix + "Bottom"
  private val transportName = prefix + "transport"
  // Checking a certificate must not establish its own missing cases, including while the foundation is built.
  private var checking = false
  private var nextHelper = 0L
  private final case class Unsupported() extends RuntimeException

  private def guarded[A](body: => A): A = {
    val previous = checking
    checking = true
    try body
    finally checking = previous
  }

  private def freshName(label: String): String = {
    nextHelper += 1
    prefix + label + nextHelper
  }

  private def privateName(name: String): String =
    if (name.startsWith("Private.")) prefix + name.stripPrefix("Private.") else name

  // This renaming is confined to the fixed bootstrap below, not a second general AST transformation.
  private def privateTerm(term: CA.Term): CA.Term = term match {
    case t: CA.Term.GlobalRef => t.copy(name = privateName(t.name))
    case t: CA.Term.LocalRef  => t
    case t: CA.Term.Pi => t.copy(binders = t.binders.map(b => b.copy(ty = privateTerm(b.ty))), out = privateTerm(t.out))
    case t: CA.Term.Lam => t.copy(ty = privateTerm(t.ty).asInstanceOf[CA.Term.Pi], body = privateTerm(t.body))
    case t: CA.Term.App =>
      t.copy(fn = privateTerm(t.fn), args = t.args.map(privateTerm), evidence = t.evidence.map(privateTerm))
    case t: CA.Term.Match =>
      t.copy(
        scrut = privateTerm(t.scrut),
        motive = privateTerm(t.motive),
        cases = t.cases.map(c => c.copy(ctorName = privateName(c.ctorName), body = privateTerm(c.body)))
      )
    case t: CA.Term.Sort =>
      t.copy(level = privateTerm(t.level), kind = privateTerm(t.kind), scope = privateTerm(t.scope))
    case t: CA.Term.Prop   => t.copy(scope = privateTerm(t.scope))
    case t: CA.Term.FormOp => t.copy(args = t.args.map(privateTerm))
    case _                 => throw Unsupported()
  }

  /** These are checked inductives/definitions, not native proof values or assumptions about the source prelude. */
  private lazy val foundation: Env = guarded {
    val source =
      """
        |namespace Private {
        |inductive Eq {u: Level}{S: Lifetime}(A: Type { level = u, scope = S }) indices (x:A)(y:A):Prop { scope = S }
        | | refl(x:A):Eq(A,x,x)
        |inductive Bottom:Prop
        |def transport {u: Level}{S: Lifetime}{Sm: Lifetime}{Sc: Lifetime}{A: Type { level = u, scope = S }}{x:A}{y:A}
        | (e:Eq(A,x,y))(motive:{ scope = Sc } A -> Prop { scope = Sm })(h:motive(x)):motive(y) := match e returning motive(y) with
        | | Eq.refl z => h
        |}
        |""".stripMargin
    Prelude
      .fromSource("<refinement foundation>", source, Set.empty)
      .core
      .decls
      .foldLeft(Interpreter.preludeInitialEnv) {
        case (env, d: CA.Decl.InductiveDecl) =>
          val header = d.header.copy(
            name = privateName(d.header.name),
            params = d.header.params.map(b => b.copy(ty = privateTerm(b.ty))),
            indices = d.header.indices.map(b => b.copy(ty = privateTerm(b.ty))),
            resultTy = privateTerm(d.header.resultTy)
          )
          val ctors = d.ctors.map(c =>
            c.copy(
              canonicalName = privateName(c.canonicalName),
              binders = c.binders.map(b => b.copy(ty = privateTerm(b.ty))),
              resultTy = privateTerm(c.resultTy)
            )
          )
          Interpreter.evalDecl(d.copy(header = header, ctors = ctors), env)
        case (env, d: CA.Decl.ConstDecl) =>
          val body = d.body match {
            case CA.ConstBody.TermBody(term) => CA.ConstBody.TermBody(privateTerm(term))
            case _                           => throw Unsupported()
          }
          Interpreter.evalDecl(d.copy(name = privateName(d.name), ty = privateTerm(d.ty), body = body), env)
        case _ => throw Unsupported()
      }
  }

  /** Faults affect proposals or syntax only; the ordinary discharge boundary remains enabled. */
  private[raccoonlang] object Testing {
    private var proposeAll = false
    private var wrongQuotation = false
    private var rewrite: CA.Term => CA.Term = identity
    def proposes: Boolean = proposeAll && !checking
    def transform(term: CA.Term): CA.Term = rewrite(term)
    def withProposals[A](body: => A): A = {
      val before = proposeAll
      proposeAll = true
      try body
      finally proposeAll = before
    }
    def quotation(term: CA.Term, value: Value, context: Env): CA.Term =
      if (!wrongQuotation) term
      else
        context.locals.iterator
          .collectFirst {
            case (ref, bound)
                if ValueEquivalence.defEq(bound.tpe, value.tpe) && !ValueEquivalence.defEq(bound, value) =>
              CA.Term.LocalRef(ref, term.span)
          }
          .getOrElse(term)
    def withWrongQuotation[A](body: => A): A = {
      val before = wrongQuotation
      wrongQuotation = true
      try body
      finally wrongQuotation = before
    }
    def withInvalidProof[A](body: => A): A = {
      val before = rewrite
      rewrite = _ => CA.Term.Prop(CA.Term.FormOp(CA.Form.LifetimeEmpty, Vector.empty, Span(0, 0)), Span(0, 0))
      try body
      finally rewrite = before
    }
  }

  private final case class Equation(left: Value, right: Value, proof: CA.Term)

  /** The ordinary term reifier declines representations it cannot preserve; it never fabricates value aliases. */
  private final class Quoter(env: Env, span: Span) {
    private def global(name: String): CA.Term = CA.Term.GlobalRef(name, span)
    private def local(value: Value): Option[CA.Term] = env.locals.iterator.collectFirst {
      case (ref, bound) if bound.asInstanceOf[AnyRef] eq value.asInstanceOf[AnyRef] => CA.Term.LocalRef(ref, span)
      case (ref, Var(_, id, _)) if (value match { case Var(_, other, _) => id == other; case _ => false }) =>
        CA.Term.LocalRef(ref, span)
    }
    private def ids(set: DepSet): Vector[Int] = {
      val result = Vector.newBuilder[Int]
      set.foreach(result += _)
      result.result()
    }
    private def parameter(id: VarId): CA.Term = env.locals.iterator
      .collectFirst {
        case (ref, value) if (value match {
              case level: Level       => Level.singleVariableOffset(level).contains(id -> 0)
              case kind: Kind         => !kind.isLin && kind.vars == DepSet(id)
              case lifetime: Lifetime => lifetime.vars == DepSet(id)
              case _                  => false
            }) =>
          CA.Term.LocalRef(ref, span)
      }
      .getOrElse(throw Unsupported())

    def apply(value: Value): CA.Term = {
      // Preserve rigid nominal/constructor forms when closing helper signatures. Abstracting an alias of a
      // materialized family instance into an arbitrary Type would turn N2 into an invalid universal theorem.
      val reference = value match {
        case _: Var | _: VLam | _: NeutralThunk | _: VProof => local(value)
        case ConstructorForm(_, _) =>
          local(value).orElse(env.locals.iterator.collectFirst {
            case (ref, bound) if ValueEquivalence.defEq(bound, value) => CA.Term.LocalRef(ref, span)
          })
        case _ => None
      }
      reference.getOrElse {
        value match {
          case _: Var    => throw Unsupported()
          case c: VConst => global(c.name)
          case h: ConstructorHead =>
            CA.Term.GlobalRef(
              h.name,
              env.sealedMembers.get(h.name).fold(span)(seal => span.copy(source = Some(seal.module)))
            )
          case p: VPacked if p.natValue.nonEmpty && env.nativeLiterals.natLayout.nonEmpty =>
            CA.Term.NatLit(p.natValue.get, span)
          case ConstructorForm(name, fields) =>
            val head = env(name).asInstanceOf[ConstructorHead]
            val family = value.tpe match { case InductiveFamilyValue(f) => f; case _ => throw Unsupported() }
            val args = family.args.take(head.numErasedFamilyArgs) ++ fields
            call(head, args)
          case a: VApp                    => call(a.head, a.args)
          case sort: VSort if sort.isProp => CA.Term.Prop(apply(sort.scope), span)
          case sort: VSort                => CA.Term.Sort(apply(sort.level), apply(sort.kind), apply(sort.scope), span)
          case level: Level =>
            def offset(term: CA.Term, n: Int): CA.Term =
              (0 until n).foldLeft(term)((t, _) => CA.Term.FormOp(CA.Form.LevelSucc, Vector(t), span))
            val parts = (if (level.c == 0 && level.terms.nonEmpty) Vector.empty
                         else
                           Vector(
                             offset(CA.Term.FormOp(CA.Form.LevelZero, Vector.empty, span), level.c)
                           )) ++ level.terms.toVector.sortBy(_._1).map { case (id, n) => offset(parameter(id), n) }
            parts.reduceLeft((a, b) => CA.Term.FormOp(CA.Form.LevelMax, Vector(a, b), span))
          case kind: Kind =>
            val base = if (kind.isLin) Vector(CA.Term.FormOp(CA.Form.KindLin, Vector.empty, span)) else Vector.empty
            val parts = base ++ ids(kind.vars).map(parameter)
            if (parts.isEmpty) CA.Term.FormOp(CA.Form.KindUnr, Vector.empty, span)
            else parts.reduceLeft((a, b) => CA.Term.FormOp(CA.Form.KindJoin, Vector(a, b), span))
          case lifetime: Lifetime =>
            val parts = ids(lifetime.vars).map(parameter)
            if (parts.isEmpty) CA.Term.FormOp(CA.Form.LifetimeEmpty, Vector.empty, span)
            else parts.reduceLeft((a, b) => CA.Term.FormOp(CA.Form.LifetimeUnion, Vector(a, b), span))
          case pi: VPi =>
            var scope = env
            var closure = pi.env
            val binders = pi.binders.map { binder =>
              val tpe = Interpreter.evalTerm(binder.ty, closure)
              val ty = new Quoter(scope, span)(tpe)
              val ref = SyntheticLocalRef.fresh(binder.name)
              val fresh = BinderOps.freshBinderValue(binder.name, tpe)
              scope = scope.putLocal(ref, fresh)
              closure = closure.putLocal(binder.localRef, fresh)
              CA.Binder(ref, ty, span, CA.BinderSite.Function, binder.mode)
            }
            val out = new Quoter(scope, span)(pi.codomain(closure))
            CA.Term.Pi(
              binders,
              out,
              CA.Closure(
                CA.ClosureField.Written(apply(pi.closureKind)),
                CA.ClosureField.Written(apply(pi.closureScope))
              ),
              span,
              NodeId.fresh()
            )
          case _ => throw Unsupported()
        }
      }
    }
    def constructor(head: ConstructorHead, family: InductiveFamilyInstance, fields: Vector[Value]): CA.Term =
      call(head, family.args.take(head.numErasedFamilyArgs) ++ fields)

    private def call(head: Value, args: Vector[Value]): CA.Term = head.tpe match {
      case pi: VPi =>
        val explicit = pi.binders.zip(args).collect { case (b, a) if b.mode == BinderMode.Explicit => apply(a) }
        val evidence = pi.binders.zip(args).collect { case (b, a) if b.mode == BinderMode.Evidence => apply(a) }
        CA.Term.App(apply(head), explicit, evidence, span)
      case _ if args.isEmpty => apply(head)
      case _                 => throw Unsupported()
    }
  }

  private final class Search(original: Env, span: Span) {
    var env: Env = original.copy(globals = original.globals ++ foundation.globals.filter(_._1.startsWith(prefix)))
    private def global(name: String): CA.Term = CA.Term.GlobalRef(name, span)
    private def app(name: String, args: CA.Term*): CA.Term =
      CA.Term.App(global(name), args.toVector, Vector.empty, span)
    private def quote(value: Value, context: Env): CA.Term = {
      val term = Testing.quotation(new Quoter(context, span)(value), value, context)
      val checked = TypeChecker.checkTerm(term, value.tpe, context)
      if (!ValueEquivalence.defEq(checked.value, value)) throw Unsupported()
      term
    }
    private def eq(left: Value, right: Value, context: Env): CA.Term = {
      if (Linearity.isLinear(left.tpe) || Sorts.isProposition(left.tpe) || !ValueEquivalence.defEq(left.tpe, right.tpe))
        throw Unsupported()
      app(eqName, quote(left.tpe, context), quote(left, context), quote(right, context))
    }
    private def binder(ref: CA.LocalRef, ty: CA.Term, site: CA.BinderSite): CA.Binder =
      CA.Binder(ref, ty, span, site, BinderMode.Explicit)
    private def pi(binders: Vector[CA.Binder], out: CA.Term): CA.Term.Pi =
      CA.Term.Pi(binders, out, CA.Closure.unrestricted(span), span, NodeId.fresh())
    private def lam(binders: Vector[CA.Binder], out: CA.Term, body: CA.Term): CA.Term.Lam =
      CA.Term.Lam(pi(binders, out), body, span, NodeId.fresh(), None, None)

    /** Close a helper over only its actual typed captures. Its application is checked in the certificate branch. */
    private def helper(
        signature: CA.Term.Pi,
        body: Option[CA.Term],
        context: Env,
        label: String
    ): (String, Vector[CA.Term]) = {
      // mentionedRefs deliberately includes nested binders. Only refs already in this context are
      // captures; fresh Pi binders from quotation must never enlarge the dependency closure.
      val available = context.locals.keySet -- signature.binders.map(_.localRef)
      var refs = (CA.mentionedRefs(signature) ++ body.toSet.flatMap(CA.mentionedRefs)) intersect available
      var frontier = refs
      var types = Map.empty[CA.LocalRef, CA.Term]
      while (frontier.nonEmpty) {
        val dependencies = frontier.flatMap { ref =>
          val ty = quote(context.locals(ref).tpe, context)
          types += ref -> ty
          CA.mentionedRefs(ty) intersect available
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
      val value = body match {
        case Some(term) =>
          TypeChecker
            .checkTerm(CA.Term.Lam(all, term, span, NodeId.fresh(), None, None), checkedType.value, closed)
            .value
        // Only the nominal factory below is permitted to request an assumed body.
        case None => Value.canonicalizeProof(VConst(freshName(label + ".principle"), Symbol, checkedType.value))
      }
      val name = freshName(label)
      env = env.putGlobal(name, value)
      (name, captures.map(b => CA.Term.LocalRef(b.localRef, span)))
    }
    private def applyHelper(helper: (String, Vector[CA.Term]), proof: CA.Term): CA.Term =
      CA.Term.App(global(helper._1), helper._2 :+ proof, Vector.empty, span)

    /** Trusted N1--N3: eligibility is checked from the typed forms, independently of search/unifier stores. */
    private def nominal(e: Equation, index: Option[Int], context: Env): CA.Term = {
      def family(v: Value): Option[InductiveFamilyInstance] = v match {
        case InductiveFamilyValue(f)
            if !Sorts.isProposition(v) && f.meta.block.isInstanceOf[CheckedInductiveBlockSchema] =>
          Some(f)
        case _ => None
      }
      def form(v: Value): Option[String] = v match {
        case _ if family(v).nonEmpty   => Some("family")
        case p: VPi if !p.isPropValued => Some("pi")
        case s: VSort if !s.isProp     => Some("sort")
        case _                         => None
      }
      val output = index match {
        case Some(i) =>
          val a = family(e.left).getOrElse(throw Unsupported())
          val b = family(e.right).getOrElse(throw Unsupported())
          if (!(a.meta eq b.meta) || i >= a.args.length || i >= b.args.length) throw Unsupported()
          eq(a.args(i), b.args(i), context)
        case None =>
          val forms = for (a <- form(e.left); b <- form(e.right)) yield (a, b)
          val clash = forms.exists { case (a, b) =>
            a != b || (a == "family" && !(family(e.left).get.meta eq family(e.right).get.meta))
          }
          if (!clash) throw Unsupported()
          global(bottomName)
      }
      val h = SyntheticLocalRef.fresh("nominalEquation")
      val signature = pi(Vector(binder(h, eq(e.left, e.right, context), CA.BinderSite.Function)), output)
      applyHelper(helper(signature, None, context, if (index.nonEmpty) "N1" else "N2N3"), e.proof)
    }

    /** An ordinary complete constructor discriminator and Eq transport, specialized at the known left constructor. */
    private def clash(e: Equation, context: Env): CA.Term = {
      val (name, _) = e.left match { case ConstructorForm(n, args) => (n, args); case _ => throw Unsupported() }
      val f = e.left.tpe match { case InductiveFamilyValue(f) => f; case _ => throw Unsupported() }
      if (Sorts.isProposition(e.left.tpe) || Linearity.isLinear(e.left.tpe)) throw Unsupported()
      val matchSpan = f.meta.seal.fold(span)(seal => span.copy(source = Some(seal.module)))
      val x = SyntheticLocalRef.fresh("noConfusionValue")
      val truth = app(
        eqName,
        CA.Term.Prop(CA.Term.FormOp(CA.Form.LifetimeEmpty, Vector.empty, span), span),
        global(bottomName),
        global(bottomName)
      )
      val cases = f.meta.constructorNames.map { n =>
        val head = context(n).asInstanceOf[ConstructorHead]
        val fields = head.fieldBinders.map(b => CA.PatternVar(SyntheticLocalRef.fresh(b.name), span))
        CA.Case(n, true, fields, if (n == name) truth else global(bottomName), matchSpan)
      }
      val discriminator = lam(
        Vector(binder(x, quote(e.left.tpe, context), CA.BinderSite.Function)),
        CA.Term.Prop(CA.Term.FormOp(CA.Form.LifetimeEmpty, Vector.empty, span), span),
        CA.Term.Match(
          CA.Term.LocalRef(x, span),
          CA.Term.Prop(CA.Term.FormOp(CA.Form.LifetimeEmpty, Vector.empty, span), span),
          cases,
          None,
          None,
          matchSpan,
          NodeId.fresh()
        )
      )
      TypeChecker.checkTerm(discriminator, context)
      // Keep the actual ordinary checked term in the certificate; no assumed no-confusion value is installed.
      app(transportName, e.proof, discriminator, app(reflName, global(bottomName)))
    }

    /**
     * Same-constructor injection is a checked, fully covered Eq elimination; dependent coordinates must be homogeneous.
     */
    private def inject(e: Equation, field: Int, context: Env): CA.Term = {
      val (name, actualLeft) = e.left match { case ConstructorForm(n, as) => (n, as); case _ => throw Unsupported() }
      val actualRight = e.right match { case ConstructorForm(`name`, as) => as; case _ => throw Unsupported() }
      val head = context(name).asInstanceOf[ConstructorHead]
      if (!head.noConfusion || Sorts.isProposition(e.left.tpe)) throw Unsupported()
      val family = e.left.tpe match { case InductiveFamilyValue(f) => f; case _ => throw Unsupported() }
      var leftEnv = head.fieldEnv(family.args)
      var rightEnv = head.fieldEnv(family.args)
      var scope = context
      val parameters = Vector.newBuilder[CA.Binder]
      val arguments = Vector.newBuilder[CA.Term]
      val left = Vector.newBuilder[Value]
      val right = Vector.newBuilder[Value]
      head.fieldBinders.zipWithIndex.foreach { case (source, i) =>
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
        val a = fresh(leftType, actualLeft(i))
        val b =
          if (ValueEquivalence.defEq(actualLeft(i), actualRight(i)) && ValueEquivalence.defEq(leftType, rightType)) a
          else fresh(rightType, actualRight(i))
        left += a
        right += b
        leftEnv = leftEnv.putLocal(source.localRef, a)
        rightEnv = rightEnv.putLocal(source.localRef, b)
      }
      val as = left.result()
      val bs = right.result()
      val leftType = head.pi.fold(head.tpe)(_.codomain(leftEnv))
      val rightType = head.pi.fold(head.tpe)(_.codomain(rightEnv))
      val leftCtor = Packed.construct(head, as, leftType)
      val rightCtor = Packed.construct(head, bs, rightType)
      val h = SyntheticLocalRef.fresh("constructorEquation")
      val z = SyntheticLocalRef.fresh("equalConstructor")
      val out = eq(as(field), bs(field), scope)
      val body = CA.Term.Match(
        CA.Term.LocalRef(h, span),
        out,
        Vector(CA.Case(reflName, true, Vector(CA.PatternVar(z, span)), app(reflName, quote(as(field), scope)), span)),
        None,
        None,
        span,
        NodeId.fresh()
      )
      val generated = helper(
        pi(parameters.result() :+ binder(h, eq(leftCtor, rightCtor, scope), CA.BinderSite.Function), out),
        Some(body),
        scope,
        "noConfusion"
      )
      CA.Term.App(global(generated._1), generated._2 ++ arguments.result() :+ e.proof, Vector.empty, span)
    }

    def refute(equations: Vector[Equation], store: EqStore, depth: Int): CA.Term = {
      if (depth > 512) throw Unsupported()
      val context = ValueOps.materializeEnv(env, store)
      val pending = equations
        .map(e => e.copy(left = ValueOps.materialize(e.left, store), right = ValueOps.materialize(e.right, store)))
        .filterNot(e => ValueEquivalence.defEq(e.left, e.right))
      if (pending.isEmpty) throw Unsupported()
      pending.foreach { e =>
        (e.left, e.right) match {
          case (ConstructorForm(a, _), ConstructorForm(b, _))
              if a != b && ValueEquivalence.defEq(e.left.tpe, e.right.tpe) =>
            return clash(e, context)
          case _ =>
            val leftFamily = e.left match {
              case InductiveFamilyValue(f) if !Sorts.isProposition(e.left) => Some(f); case _ => None
            }
            val rightFamily = e.right match {
              case InductiveFamilyValue(f) if !Sorts.isProposition(e.right) => Some(f); case _ => None
            }
            val different =
              leftFamily.nonEmpty && rightFamily.nonEmpty && !(leftFamily.get.meta eq rightFamily.get.meta)
            val form = (e.left, e.right) match {
              case (_: VPi, InductiveFamilyValue(_)) | (InductiveFamilyValue(_), _: VPi) |
                  (_: VSort, InductiveFamilyValue(_)) | (InductiveFamilyValue(_), _: VSort) | (_: VPi, _: VSort) |
                  (_: VSort, _: VPi) =>
                true
              case _ => false
            }
            if (different || form) return nominal(e, None, context)
        }
      }
      pending.zipWithIndex.foreach { case (e, idx) =>
        val solution = (e.left, e.right) match {
          case (v: Var, value) if !value.synDeps.contains(v.id) => Some(v -> value)
          case (value, v: Var) if !value.synDeps.contains(v.id) => Some(v -> value)
          case _                                                => None
        }
        solution.foreach { case (v, value) =>
          val next = store.allow(DepSet(v.id)).addLink(v.id, value)
          // Equality elimination is deterministic: retrying all solution orders on failure is factorial
          // in compatible independent hypotheses, including deliberately wrong exclusion proposals.
          val body = refute(pending.patch(idx, Nil, 1), next, depth + 1)
          val z = SyntheticLocalRef.fresh("equalValue")
          return CA.Term.Match(
            e.proof,
            global(bottomName),
            Vector(CA.Case(reflName, true, Vector(CA.PatternVar(z, span)), body, span)),
            None,
            None,
            span,
            NodeId.fresh()
          )
        }
      }
      pending.zipWithIndex.foreach { case (e, idx) =>
        val pairs = (e.left, e.right) match {
          case (ConstructorForm(a, as), ConstructorForm(b, bs)) if a == b =>
            as.zip(bs).zipWithIndex.map { case ((a, b), i) => (a, b, Left(i)) }
          case (InductiveFamilyValue(a), InductiveFamilyValue(b))
              if (a.meta eq b.meta) && !Sorts.isProposition(e.left) =>
            a.args.zip(b.args).zipWithIndex.map { case ((a, b), i) => (a, b, Right(i)) }
          case _ => Vector.empty
        }
        val derived = pairs.flatMap { case (a, b, i) =>
          if (
            Sorts.isProposition(a.tpe) || Linearity
              .isLinear(a.tpe) || !ValueEquivalence.defEq(a.tpe, b.tpe) || ValueEquivalence.defEq(a, b)
          ) None
          else
            try Some(Equation(a, b, i.fold(j => inject(e, j, context), j => nominal(e, Some(j), context))))
            catch {
              case _: Unsupported                                => None
              case e: Diagnostic if e.error == EvaluationTooDeep => throw e
              case _: Diagnostic                                 => None
            }
        }
        // As with variable elimination, do not retry equivalent structural processing orders.
        if (derived.nonEmpty) return refute(pending.patch(idx, derived, 1), store, depth + 1)
      }
      throw Unsupported()
    }

    def discharge(
        scrut: Value,
        scrutTerm: CA.Term,
        family: InductiveFamilyInstance,
        head: ConstructorHead,
        fields: Vector[Value],
        resultTy: Value
    ): Boolean = {
      fields.zipWithIndex.foreach { case (value, i) =>
        val ref = SyntheticLocalRef.fresh(head.fieldBinders(i).name)
        val checked = TypeChecker.checkTypeTerm(quote(value.tpe, env), env)
        TypeChecker.checkFits(checked.value, value.tpe)
        env = env.putLocal(ref, Value.canonicalizeProof(value))
      }
      val ctor = Packed.construct(head, fields, resultTy)
      val ctorTerm = new Quoter(env, span).constructor(head, family, fields)
      val checkedCtor = TypeChecker.checkTerm(ctorTerm, env)
      if (!ValueEquivalence.defEq(checkedCtor.value, ctor)) throw Unsupported()
      TypeChecker.checkFits(checkedCtor.value.tpe, resultTy)
      val result = resultTy match {
        case InductiveFamilyValue(f) if f.meta eq family.meta => f; case _ => throw Unsupported()
      }
      val raw = family.args
        .drop(family.meta.block.key.numParams)
        .zip(result.args.drop(family.meta.block.key.numParams))
        .filter { case (a, b) =>
          !Sorts.isProposition(a.tpe) && !Linearity.isLinear(a.tpe) && ValueEquivalence.defEq(a.tpe, b.tpe)
        }
      val equations = raw.map { case (a, b) =>
        val proposition = TypeChecker.checkTypeTerm(eq(a, b, env), env).value
        val ref = SyntheticLocalRef.fresh("constructorIndex")
        env = env.putLocal(ref, Value.canonicalizeProof(VProof(proposition)))
        Equation(a, b, CA.Term.LocalRef(ref, span))
      }
      val all =
        if (
          !Sorts.isProposition(scrut.tpe) && !Linearity
            .isLinear(scrut.tpe) && ValueEquivalence.defEq(scrut.tpe, ctor.tpe)
        ) {
          val term = app(eqName, quote(scrut.tpe, env), scrutTerm, quote(ctor, env))
          val proposition = TypeChecker.checkTypeTerm(term, env).value
          val ref = SyntheticLocalRef.fresh("constructorValue")
          env = env.putLocal(ref, Value.canonicalizeProof(VProof(proposition)))
          equations :+ Equation(scrut, ctor, CA.Term.LocalRef(ref, span))
        } else equations
      val proof = refute(all, EqStore.empty, 0)
      TypeChecker.checkTerm(Testing.transform(proof), env(bottomName), env)
      true
    }
  }

  /** No candidate store or failure record crosses this boundary. Failure only retains the constructor. */
  def excludes(
      scrut: Value,
      scrutTerm: CA.Term,
      family: InductiveFamilyInstance,
      head: ConstructorHead,
      fields: Vector[Value],
      resultTy: Value,
      env: Env,
      span: Span
  ): Boolean = {
    if (checking) false
    else
      TypeChecker.preservingSynthesisState {
        guarded {
          try new Search(env, span).discharge(scrut, scrutTerm, family, head, fields, resultTy)
          catch {
            case e: Unsupported =>
              if (java.lang.Boolean.getBoolean("raccoon.certificates.trace"))
                System.err.println(s"Certificate ${head.name}: unsupported ${e.getStackTrace.take(5).mkString(" / ")}")
              false
            case e: Diagnostic if e.error == EvaluationTooDeep => throw e
            case e: Diagnostic =>
              if (java.lang.Boolean.getBoolean("raccoon.certificates.trace"))
                System.err.println(s"Certificate ${head.name}: ${e.error}")
              false
          }
        }
      }
  }
}
