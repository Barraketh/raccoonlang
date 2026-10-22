package com.raccoonlang

import com.raccoonlang.{CoreAst => CA, ElabAst => EA}

import java.util.concurrent.{Callable, Executors}

class NodeIdentityTests extends munit.FunSuite {
  private val span = Span(7, 19)
  private val source =
    """
      |inductive N : Type
      | | z : N
      | | s (_: N): N
      |
      |inductive Bottom : Prop
      |""".stripMargin

  private def elaborate(src: String): CA.Program =
    LanguageParser.parseProgram(src) match {
      case Success(parsed, _, _) => Elaborator.elab(parsed, Prelude.test)
      case err: Failure          => fail(s"Failed to parse source: $err")
    }

  private def fixture: Env = {
    val core = elaborate(source)
    core.decls.foldLeft(Interpreter.initialEnv(Prelude.test)) { case (curEnv, decl) =>
      Interpreter.evalDecl(decl, curEnv)
    }
  }

  private def coreType(name: String): CA.TypeTerm = CA.Term.GlobalRef(name, span)

  private def binder(ref: CA.LocalRef, name: String): CA.Binder = {
    val typePattern = CA.TypePattern.Type(coreType(name))
    CA.Binder(ref, CA.BinderType.TypePattern(typePattern, span), span)
  }

  private def corePi(
      domain: String,
      codomain: String,
      piSpan: Span = span,
      argId: Int = 0,
      argName: String = "x"
  ): CA.Term.Pi = {
    val arg = CA.LocalRef(argId, argName)
    val typePattern = CA.TypePattern.Type(CA.Term.GlobalRef(domain, piSpan))
    CA.Term.Pi(
      Vector(CA.Binder(arg, CA.BinderType.TypePattern(typePattern, piSpan), piSpan)),
      CA.Term.GlobalRef(codomain, piSpan),
      piSpan,
      NodeId.fresh()
    )
  }

  private def coreLam(
      pi: CA.Term.Pi,
      body: CA.Term,
      lamSpan: Span = span,
      nodeId: NodeId = NodeId.fresh()
  ): CA.Term.Lam =
    CA.Term.Lam(pi, Vector.empty, body, lamSpan, None, None, nodeId)

  private def declaredLam(program: CA.Program, name: String): CA.Term.Lam =
    program.decls
      .collectFirst { case CA.Decl.ConstDecl(`name`, _, CA.ConstBody.TermBody(lam: CA.Term.Lam), _, _, _) =>
        lam
      }
      .getOrElse(fail(s"No lambda declaration named $name"))

  test("semantic Pi IDs ignore source positions and preserve structural equality") {
    val env = fixture
    val sameSpanNToN = corePi("N", "N")
    val sameSpanNToBottom = corePi("N", "Bottom")
    assertEquals(sameSpanNToN.span, sameSpanNToBottom.span)
    assertNotEquals(sameSpanNToN.nodeId, sameSpanNToBottom.nodeId)

    val nToNValue = TypeChecker.getType(sameSpanNToN, env)
    val nToBottomValue = TypeChecker.getType(sameSpanNToBottom, env)
    assertNotEquals(nToNValue.key, nToBottomValue.key)
    assert(!ValueEquivalence.defEq(nToNValue, nToBottomValue))

    val equivalentNToN = corePi("N", "N")
    val equivalentValue = TypeChecker.getType(equivalentNToN, env)
    assertNotEquals(nToNValue.key, equivalentValue.key)
    assert(ValueEquivalence.defEq(nToNValue, equivalentValue))

    val spanChanged = sameSpanNToN.copy(span = Span(100, 200))
    assertEquals(spanChanged.nodeId, sameSpanNToN.nodeId)
    val spanChangedValue = TypeChecker.getType(spanChanged, env)
    assertEquals(spanChangedValue.key, nToNValue.key)
    assert(ValueEquivalence.defEq(spanChangedValue, nToNValue))
  }

  test("same-span identity lambda cannot inhabit the function-to-empty proposition") {
    val env = fixture
    val expected = corePi("N", "Bottom")
    val functionRef = CA.LocalRef(0, "f")
    val gType = CA.Term.Pi(
      Vector(
        CA.Binder(
          functionRef,
          CA.BinderType.TypePattern(CA.TypePattern.Type(expected), span),
          span
        )
      ),
      CA.Term.GlobalRef("Bottom", span),
      span,
      NodeId.fresh()
    )
    val inhabitedG = coreLam(
      gType,
      CA.Term.App(CA.Term.LocalRef(functionRef, span), Vector(CA.Term.GlobalRef("N.z", span)), span)
    )
    val inhabitant = TypeChecker.checkTerm(inhabitedG, env).value
    val gRef = CA.LocalRef(0, "g")
    val envWithG = env.putLocal(gRef, FreshVar.freshVar("g", inhabitant.tpe))
    val identityType = corePi("N", "N", argId = 1)
    assertEquals(expected.span, identityType.span)
    assertNotEquals(expected.nodeId, identityType.nodeId)

    val x = identityType.binders.head.localRef
    val identity = coreLam(identityType, CA.Term.LocalRef(x, span))
    val app = CA.Term.App(CA.Term.LocalRef(gRef, span), Vector(identity), span)
    intercept[TypeMismatch] {
      val result = TypeChecker.checkTerm(app, envWithG)
      TypeChecker.checkType(result.value, env("Bottom"))
    }
  }

  test("anonymous lambda identity distinguishes code while structural fallback compares equivalent lambdas") {
    val env = fixture
    val pi = corePi("N", "N")
    val x = pi.binders.head.localRef
    val identity = TypeChecker.checkTerm(coreLam(pi, CA.Term.LocalRef(x, span)), env)
    val constant = TypeChecker.checkTerm(coreLam(pi, CA.Term.GlobalRef("N.z", span)), env)
    val equivalent = TypeChecker.checkTerm(coreLam(pi, CA.Term.LocalRef(x, span)), env)

    assertNotEquals(identity.value.key, constant.value.key)
    assert(!ValueEquivalence.defEq(identity.value, constant.value))
    assert(ValueEquivalence.defEq(identity.value, equivalent.value))

    val reevaluated = Interpreter.evalTerm(identity.residual, env)
    assertEquals(reevaluated.key, identity.value.key)
  }

  test("captured data participates in lambda identity and quotation creates closed fresh code") {
    val env = fixture
    val z = Interpreter.evalTerm(EA.Term.GlobalRef("N.z", span), env)
    val succ = Interpreter.evalTerm(EA.Term.GlobalRef("N.s", span), env)
    val succZ = Interpreter.evalApply(succ, Vector(z))
    val capturedRef = CA.LocalRef(0, "captured")
    val argRef = CA.LocalRef(1, "x")
    val pi = CA.Term.Pi(
      Vector(binder(argRef, "N")),
      CA.Term.GlobalRef("N", span),
      span,
      NodeId.fresh()
    )
    val lam = coreLam(pi, CA.Term.LocalRef(capturedRef, span), nodeId = NodeId.fresh())
    val envZ = env.putLocal(capturedRef, z)
    val envSuccZ = env.putLocal(capturedRef, succZ)
    val checkedZ = TypeChecker.checkTerm(lam, envZ)
    val checkedSuccZ = TypeChecker.checkTerm(lam, envSuccZ)

    assertNotEquals(checkedZ.value.key, checkedSuccZ.value.key)
    assert(!ValueEquivalence.defEq(checkedZ.value, checkedSuccZ.value))
    assertEquals(Interpreter.evalTerm(checkedZ.residual, envZ).key, checkedZ.value.key)

    val emptyContext = ValueQuote.QuoteContext(Map.empty, 0)
    val quotedZ = ValueQuote.quoteTerm(checkedZ.value, emptyContext, span).asInstanceOf[EA.Term.Lam]
    val quotedSuccZ = ValueQuote.quoteTerm(checkedSuccZ.value, emptyContext, span).asInstanceOf[EA.Term.Lam]
    assertNotEquals(quotedZ.nodeId, lam.nodeId)
    assertNotEquals(quotedSuccZ.nodeId, lam.nodeId)
    assertNotEquals(quotedZ.ty.nodeId, lam.ty.nodeId)

    val closedZ = Interpreter.evalTerm(quotedZ, env)
    val closedSuccZ = Interpreter.evalTerm(quotedSuccZ, env)
    assertNotEquals(closedZ.key, closedSuccZ.key)
    assert(!ValueEquivalence.defEq(closedZ, closedSuccZ))
    assert(ValueEquivalence.defEq(Interpreter.evalApply(closedZ, Vector(z)), z))
    assert(ValueEquivalence.defEq(Interpreter.evalApply(closedSuccZ, Vector(z)), succZ))
  }

  test("distinct blocked matches retain identity and repeated evaluation preserves it") {
    val env = fixture
    val scrutRef = CA.LocalRef(0, "n")
    val binderRef = CA.LocalRef(1, "k")
    val nValue = env("N")
    val neutral = FreshVar.freshVar("n", nValue)
    val envWithScrut = env.putLocal(scrutRef, neutral)
    val zCase = CA.Case("N.z", true, Vector.empty, CA.Term.GlobalRef("N.z", span), span)
    val succCaseZ = CA.Case(
      "N.s",
      true,
      Vector(Some(binderRef)),
      CA.Term.GlobalRef("N.z", span),
      span
    )
    val succCaseIdentity = succCaseZ.copy(body = CA.Term.LocalRef(binderRef, span))

    val matchA = CA.Term.Match(CA.Term.LocalRef(scrutRef, span), None, Vector(zCase, succCaseZ), span, NodeId.fresh())
    val matchB = CA.Term.Match(
      CA.Term.LocalRef(scrutRef, span),
      None,
      Vector(zCase, succCaseIdentity),
      span,
      NodeId.fresh()
    )
    val checkedA = TypeChecker.checkTerm(matchA, envWithScrut)
    val checkedB = TypeChecker.checkTerm(matchB, envWithScrut)

    assertNotEquals(
      checkedA.residual.asInstanceOf[EA.Term.Match].nodeId,
      checkedB.residual.asInstanceOf[EA.Term.Match].nodeId
    )
    assertNotEquals(checkedA.value.key, checkedB.value.key)
    assert(!ValueEquivalence.defEq(checkedA.value, checkedB.value))
    intercept[UnificationFailed](ValueEquivalence.unify(checkedA.value, checkedB.value, EqStore.empty))

    val first = Interpreter.evalTerm(checkedA.residual, envWithScrut)
    val second = Interpreter.evalTerm(checkedA.residual, envWithScrut)
    assertEquals(first.key, second.key)
    assertEquals(first.asInstanceOf[Value.NeutralThunk].id.nodeId, matchA.nodeId)
  }

  test("checking preserves nested syntax IDs and independent elaboration allocates new ones") {
    val src =
      """
        |inductive N : Type
        | | z : N
        | | s (_: N): N
        |
        |def inspect (h: N -> N)(n: N): N := {
        |  match n returning N with
        |  | N.z => N.z
        |  | N.s k => h(k)
        |}
        |""".stripMargin
    val parsed = LanguageParser.parseProgram(src) match {
      case Success(value, _, _) => value
      case err: Failure         => fail(s"Failed to parse source: $err")
    }
    val core1 = Elaborator.elab(parsed, Prelude.test)
    val core2 = Elaborator.elab(parsed, Prelude.test)
    val lam1 = declaredLam(core1, "inspect")
    val lam2 = declaredLam(core2, "inspect")
    val nestedPi1 = lam1.ty.binders.head.ty
      .asInstanceOf[CA.BinderType.TypePattern]
      .tp
      .asInstanceOf[CA.TypePattern.Type]
      .term
      .asInstanceOf[CA.Term.Pi]
    val nestedPi2 = lam2.ty.binders.head.ty
      .asInstanceOf[CA.BinderType.TypePattern]
      .tp
      .asInstanceOf[CA.TypePattern.Type]
      .term
      .asInstanceOf[CA.Term.Pi]
    val match1 = lam1.body.asInstanceOf[CA.Term.Body].res.asInstanceOf[CA.Term.Match]
    val match2 = lam2.body.asInstanceOf[CA.Term.Body].res.asInstanceOf[CA.Term.Match]
    assertEquals(lam1.span, lam2.span)
    assertEquals(lam1.ty.span, lam2.ty.span)
    assertEquals(match1.span, match2.span)
    assertNotEquals(lam1.nodeId, lam2.nodeId)
    assertNotEquals(lam1.ty.nodeId, lam2.ty.nodeId)
    assertNotEquals(nestedPi1.nodeId, nestedPi2.nodeId)
    assertNotEquals(match1.nodeId, match2.nodeId)

    val inspectDecl = core1.decls.collectFirst {
      case d: CA.Decl.ConstDecl if d.name == "inspect" => d
    }.get
    val env = core1.decls.takeWhile(_ ne inspectDecl).foldLeft(Interpreter.initialEnv(Prelude.test)) {
      case (curEnv, decl) => Interpreter.evalDecl(decl, curEnv)
    }
    val checked = TypeChecker.checkTerm(lam1, env).residual.asInstanceOf[EA.Term.Lam]
    val checkedNestedPi = checked.ty.binders.head.ty
      .asInstanceOf[EA.BinderType.TypePattern]
      .tp
      .asInstanceOf[EA.TypePattern.Type]
      .term
      .asInstanceOf[EA.Term.Pi]
    val checkedMatch = checked.body.asInstanceOf[EA.Term.Body].res.asInstanceOf[EA.Term.Match]
    assertEquals(checked.nodeId, lam1.nodeId)
    assertEquals(checked.ty.nodeId, lam1.ty.nodeId)
    assertEquals(checkedNestedPi.nodeId, nestedPi1.nodeId)
    assertEquals(checkedMatch.nodeId, match1.nodeId)
  }

  test("quotation inlines captures into rebuilt match branches with fresh nested IDs") {
    val src =
      source +
        """
          |
          |def build (captured: N)(n: N): N -> N := {
          |  match n returning N -> N with
          |  | N.z => fun (x: N): N => captured
          |  | N.s k => fun (x: N): N => captured
          |}
          |""".stripMargin
    val core = elaborate(src)
    val env = core.decls.foldLeft(Interpreter.initialEnv(Prelude.test)) { case (curEnv, decl) =>
      Interpreter.evalDecl(decl, curEnv)
    }
    val buildLam = declaredLam(core, "build")
    val matchNode = buildLam.body.asInstanceOf[CA.Term.Body].res.asInstanceOf[CA.Term.Match]
    val sourceBranchIds = matchNode.cases.map(_.body.asInstanceOf[CA.Term.Lam].nodeId)
    val z = Interpreter.evalTerm(EA.Term.GlobalRef("N.z", span), env)
    val succ = Interpreter.evalTerm(EA.Term.GlobalRef("N.s", span), env)
    val succZ = Interpreter.evalApply(succ, Vector(z))
    val neutral = FreshVar.freshVar("n", env("N"))
    val build = env("build")
    val thunkZ = Interpreter.evalApply(build, Vector(z, neutral)).asInstanceOf[Value.NeutralThunk]
    val thunkSuccZ = Interpreter.evalApply(build, Vector(succZ, neutral)).asInstanceOf[Value.NeutralThunk]
    assertEquals(thunkZ.id.nodeId, matchNode.nodeId)
    assertEquals(thunkSuccZ.id.nodeId, matchNode.nodeId)
    assertNotEquals(thunkZ.key, thunkSuccZ.key)
    assert(!ValueEquivalence.defEq(thunkZ, thunkSuccZ))

    val quotedScrutRef = CA.LocalRef(0, "n")
    val quoteContext = ValueQuote.QuoteContext(
      Map(
        neutral.key -> ValueQuote.QuoteEntry(EA.Term.LocalRef(quotedScrutRef, span), LocalResidualPolicy.Residualizable)
      ),
      localEnvLength = 1
    )
    val quotedZ = ValueQuote.quoteTerm(thunkZ, quoteContext, span).asInstanceOf[EA.Term.Match]
    val quotedSuccZ = ValueQuote.quoteTerm(thunkSuccZ, quoteContext, span).asInstanceOf[EA.Term.Match]
    assertNotEquals(quotedZ.nodeId, matchNode.nodeId)
    assertNotEquals(quotedSuccZ.nodeId, matchNode.nodeId)

    val branchZ = quotedZ.cases.head.body.asInstanceOf[EA.Term.Lam]
    val branchSuccZ = quotedSuccZ.cases.head.body.asInstanceOf[EA.Term.Lam]
    val sourceBranchZ = matchNode.cases.head.body.asInstanceOf[CA.Term.Lam]
    assertNotEquals(branchZ.nodeId, sourceBranchIds.head)
    assertNotEquals(branchSuccZ.nodeId, sourceBranchIds.head)
    assertNotEquals(branchZ.ty.nodeId, sourceBranchZ.ty.nodeId)
    assertNotEquals(branchSuccZ.ty.nodeId, sourceBranchZ.ty.nodeId)
    assertEquals(PrettyPrinter.printElabTerm(branchZ.body), "N.z")
    assertEquals(PrettyPrinter.printElabTerm(branchSuccZ.body), "N.s(N.z)")

    val quotedEnv = env.putLocal(quotedScrutRef, neutral)
    val eqStore = EqStore.empty.allow(DepSet(neutral.id)).addLink(neutral.id, z)
    val quotedValueZ = Interpreter.resolveInEqStore(Interpreter.evalTerm(quotedZ, quotedEnv), eqStore)
    val quotedValueSuccZ = Interpreter.resolveInEqStore(Interpreter.evalTerm(quotedSuccZ, quotedEnv), eqStore)
    val originalValueZ = Interpreter.resolveInEqStore(thunkZ, eqStore)
    val originalValueSuccZ = Interpreter.resolveInEqStore(thunkSuccZ, eqStore)
    assertNotEquals(quotedValueZ.key, quotedValueSuccZ.key)
    assert(ValueEquivalence.defEq(Interpreter.evalApply(quotedValueZ, Vector(z)), z))
    assert(ValueEquivalence.defEq(Interpreter.evalApply(quotedValueSuccZ, Vector(z)), succZ))
    assert(ValueEquivalence.defEq(Interpreter.evalApply(originalValueZ, Vector(z)), z))
    assert(ValueEquivalence.defEq(Interpreter.evalApply(originalValueSuccZ, Vector(z)), succZ))
  }

  test("concurrent fresh NodeId allocation is unique") {
    val workers = 4
    val allocationsPerWorker = 500
    val pool = Executors.newFixedThreadPool(workers)
    try {
      val tasks = (0 until workers).map { _ =>
        new Callable[Vector[Long]] {
          override def call(): Vector[Long] = Vector.fill(allocationsPerWorker)(NodeId.fresh().value)
        }
      }
      val ids = tasks.map(task => pool.submit(task)).flatMap(_.get())
      assertEquals(ids.distinct.length, workers * allocationsPerWorker)
    } finally pool.shutdown()
  }
}
