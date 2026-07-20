package com.raccoonlang

import com.raccoonlang.CoreAst.Decl
import com.raccoonlang.Value._
import com.raccoonlang.WfPrimitives._
import com.raccoonlang.telescope.BinderOps

class WfRecursionTests extends munit.FunSuite {
  private val accSource =
    """
      |inductive Acc {u: Level}(A: Sort(u))(r: A -> A -> Prop) indices (a: A) : Prop
      | | intro (x: A)(h: (y: A) -> r(y, x) -> Acc(A, r, y)): Acc(A, r, x)
      |""".stripMargin

  private val concreteSource =
    accSource +
      """
        |def falseRel (left: Nat)(right: Nat): Prop := False
        |
        |def wfMotive (a: Nat)(proof: Acc(Nat, falseRel, a)): Type := Nat
        |
        |def wfMinor
        |  (x: Nat)
        |  (h: (y: Nat) -> falseRel(y, x) -> Acc(Nat, falseRel, y))
        |  (ih: (y: Nat) -> (hr: falseRel(y, x)) -> wfMotive(y, h(y, hr))):
        |  wfMotive(x, Acc.intro(falseRel, x, h)) := x
        |
        |def propMotive (a: Nat)(proof: Acc(Nat, falseRel, a)): Prop := True
        |
        |def propMinor
        |  (x: Nat)
        |  (h: (y: Nat) -> falseRel(y, x) -> Acc(Nat, falseRel, y))
        |  (ih: (y: Nat) -> (hr: falseRel(y, x)) -> propMotive(y, h(y, hr))):
        |  propMotive(x, Acc.intro(falseRel, x, h)) := True.intro
        |
        |def wfProof : Acc(Nat, falseRel, Nat.zero) :=
        |  Acc.intro(
        |    falseRel,
        |    Nat.zero,
        |    fun (y: Nat)(impossible: falseRel(y, Nat.zero)): Acc(Nat, falseRel, y) =>
        |      False.elim(impossible, Acc(Nat, falseRel, y))
        |  )
        |
        |axiom wfAxiom : Acc(Nat, falseRel, Nat.zero)
        |axiom opaqueNatFn (n: Nat): Nat
        |""".stripMargin

  private def elaborate(source: String, prelude: Prelude.Config): CoreAst.Program =
    LanguageParser.parseProgram(source) match {
      case Success(surface, _, _) => Elaborator.elab(surface, prelude)
      case failure: Failure       => fail(s"Parse failed at ${failure.curIdx}: ${failure.message}")
    }

  private def eqDecl(prelude: Prelude.Config): Decl.InductiveDecl =
    prelude.core.decls.collectFirst { case decl: Decl.InductiveDecl if decl.header.name == "Eq" => decl }.get

  private val equalityMetadata =
    EqualityExportMetadata(
      SupportedProducer,
      "Eq",
      Vector("Eq.refl"),
      numParams = 2,
      numIndices = 1,
      isRecursive = false
    )
  private val accMetadata =
    AccExportMetadata(
      SupportedProducer,
      "Acc",
      Vector("Acc.intro"),
      numParams = 2,
      numIndices = 1,
      isRecursive = true
    )

  private def fixture(): (ValidatedEquality, AccRecursorShape, Env) = {
    val equality = validateEquality(eqDecl(Prelude.test), Prelude.test.checkedEnv, equalityMetadata)
    val accDecl = elaborate(accSource, Prelude.test).decls.collectFirst { case decl: Decl.InductiveDecl => decl }.get
    val env = Interpreter.evalDecl(accDecl, Prelude.test.checkedEnv)
    val shape = validateAcc(
      accDecl,
      env,
      accMetadata
    )
    (equality, shape, env)
  }

  private def installFixture(): Installed = {
    val (equality, acc, env) = fixture()
    install(
      equality,
      acc,
      ExportedRecursor(
        Vector(UniverseRole.MotiveResult, UniverseRole.Carrier),
        expectedRecursorType(acc),
        Vector(RecursorRule("Acc.intro", 2)),
        Span(0, 0)
      ),
      env
    )
  }

  private lazy val concreteFixture: Installed = {
    val declarations = elaborate(concreteSource, Prelude.default).decls
    val accDecl = declarations.collectFirst { case decl: Decl.InductiveDecl if decl.header.name == "Acc" => decl }.get
    val env = declarations.foldLeft(Prelude.default.checkedEnv) { case (current, declaration) =>
      Interpreter.evalDecl(declaration, current)
    }
    val equality = validateEquality(eqDecl(Prelude.default), Prelude.default.checkedEnv, equalityMetadata)
    val acc = validateAcc(accDecl, env, accMetadata)
    install(
      equality,
      acc,
      ExportedRecursor(
        Vector(UniverseRole.MotiveResult, UniverseRole.Carrier),
        expectedRecursorType(acc),
        Vector(RecursorRule("Acc.intro", 2)),
        Span(0, 0)
      ),
      env
    )
  }

  private def recursorArgs(
      installed: Installed,
      motiveResult: Level,
      motive: String,
      minor: Value,
      major: Value
  ): Vector[Value] =
    Vector(
      motiveResult,
      Level.one,
      installed.env("Nat"),
      installed.env("falseRel"),
      installed.env(motive),
      minor,
      installed.env("Nat.zero"),
      major
    )

  private def equationArgs(installed: Installed): Vector[Value] = {
    val children = installed.env("wfProof") match {
      case VCtor(_, Vector(_, h), _) => h
      case other                     => fail(s"Expected reconstructed Acc.intro proof, got $other")
    }
    Vector(
      Level.one,
      Level.one,
      installed.env("Nat"),
      installed.env("falseRel"),
      installed.env("wfMotive"),
      installed.env("wfMinor"),
      installed.env("Nat.zero"),
      children
    )
  }

  private def equalitySides(proposition: Value): (Value, Value) =
    proposition match {
      case ConstSpine(VConst("Eq", Inductive(_), _), args) if args.length == 4 => (args(2), args(3))
      case other => fail(s"Expected equality proposition, got $other")
    }

  test("validated Acc.rec installs as a uniformly sealed symbolic constant") {
    val installed = installFixture()
    val recursor = installed.env(SealedRecName)
    recursor match {
      case VConst(SealedRecName, Symbol, _: VPi) =>
      case other                                 => fail(s"Expected sealed symbolic recursor, got $other")
    }

    val recursorPi = recursor.tpe.asInstanceOf[VPi]
    val fresh = BinderOps.freshen(recursorPi)
    val args = recursorPi.binders.map(binder => fresh(binder.localRef))
    Interpreter.evalApply(recursor, args) match {
      case VApp(VConst(SealedRecName, Symbol, _), _, _, blockedOn) => assert(blockedOn.isEmpty)
      case other => fail(s"Constructor-headed/reconstructed Acc proof reduced through the sealed recursor: $other")
    }
  }

  test("constructor equation is a canonical proof and has no definitional effect") {
    val installed = installFixture()
    installed.env(EquationName) match {
      case VLam(_, _, LamBody.ProofEta) =>
      case other                        => fail(s"Expected canonical proof eta-lambda, got $other")
    }

    val equationPi = installed.env(EquationName).tpe.asInstanceOf[VPi]
    val fresh = BinderOps.freshen(equationPi)
    val proposition = equationPi.codomain(fresh)
    val (lhs, rhs) = equalitySides(proposition)
    assert(!ValueEquivalence.defEq(lhs, rhs))
    ValueEquivalence.tryUnify(lhs, rhs, EqStore.empty) match {
      case Left(failure) => assert(!failure.apart)
      case Right(_)      => fail("The constructor equation unexpectedly held definitionally")
    }
  }

  test("equation application canonicalizes without making its sides definitionally equal") {
    val installed = concreteFixture
    val proof = Interpreter.evalApply(installed.env(EquationName), equationArgs(installed))
    assertEquals(proof, Value.canonicalizeProof(VProof(proof.tpe)))

    val (lhs, rhs) = equalitySides(proof.tpe)
    assert(lhs.synDeps.isEmpty)
    assert(rhs.synDeps.isEmpty)
    assert(!ValueEquivalence.defEq(lhs, rhs))
    ValueEquivalence.tryUnify(lhs, rhs, EqStore.empty) match {
      case Left(failure) => assert(!failure.apart)
      case Right(_)      => fail("The closed constructor-equation sides unexpectedly unified")
    }

    val proofRef = CoreAst.LocalRef(-1000000, "equationProof")
    val span = Span(0, 0)
    val emptyMatch = CoreAst.Term.Match(
      CoreAst.Term.LocalRef(proofRef, span),
      Some(CoreAst.Term.GlobalRef("False", span)),
      Vector.empty,
      span
    )
    val error = intercept[MissingCase] {
      TypeChecker.checkTerm(emptyMatch, installed.env.putLocal(proofRef, proof))
    }
    assertEquals(error.ctor, "Eq.refl")
  }

  test("closed opaque applications remain not-apart and keep Eq.refl reachable") {
    val installed = concreteFixture
    val zero = installed.env("Nat.zero")
    val one = Interpreter.evalApply(installed.env("Nat.succ"), Vector(zero))
    val left = Interpreter.evalApply(installed.env("opaqueNatFn"), Vector(zero))
    val right = Interpreter.evalApply(installed.env("opaqueNatFn"), Vector(one))
    assert(left.synDeps.isEmpty)
    assert(right.synDeps.isEmpty)
    ValueEquivalence.tryUnify(left, right, EqStore.empty) match {
      case Left(failure) => assert(!failure.apart)
      case Right(_)      => fail("Distinct opaque applications unexpectedly unified")
    }

    val program = elaborate(
      """
        |axiom genericFn (n: Nat): Nat
        |axiom genericEquality : Eq(Nat, genericFn(0), genericFn(1))
        |def refute : False := {
        |  match genericEquality returning False with
        |}
        |""".stripMargin,
      Prelude.default
    )
    val error = intercept[MissingCase] { Interpreter.run(program, Prelude.default) }
    assertEquals(error.ctor, "Eq.refl")
  }

  test("sealed application never evaluates the minor and seals axiom and blocked majors") {
    val installed = concreteFixture
    val minorType = installed.env("wfMinor").tpe.asInstanceOf[VPi]
    val bombMinor = VLam(
      minorType,
      ValueId.Const("bombMinor"),
      LamBody.Native((_, _) => throw WTF("sealed recursor evaluated its minor"), Env.empty, isRawRecursive = false)
    )
    val majorType = installed.env("wfProof").tpe
    val blockedMajor = FreshVar.freshVar("blockedMajor", majorType)
    val majors = Vector("axiom" -> installed.env("wfAxiom"), "blocked" -> blockedMajor)

    majors.foreach { case (description, major) =>
      Interpreter.evalApply(
        installed.env(SealedRecName),
        recursorArgs(installed, Level.one, "wfMotive", bombMinor, major)
      ) match {
        case VApp(VConst(SealedRecName, Symbol, _), _, _, _) =>
        case other => fail(s"Expected $description major to remain sealed, got $other")
      }
    }
  }

  test("native Nat dispatch safely falls through on a sealed neutral") {
    val installed = concreteFixture
    val zero = installed.env("Nat.zero")
    val neutral = Interpreter.evalApply(
      installed.env(SealedRecName),
      recursorArgs(installed, Level.one, "wfMotive", installed.env("wfMinor"), installed.env("wfProof"))
    )
    neutral match {
      case VApp(VConst(SealedRecName, Symbol, _), _, tpe, _) =>
        assert(ValueEquivalence.defEq(tpe, installed.env("Nat")))
      case other => fail(s"Expected a sealed Nat neutral, got $other")
    }
    val fallback = Interpreter.evalApply(installed.env("Nat.add"), Vector(neutral, zero))
    assert(ValueEquivalence.defEq(fallback, neutral))
    val propResult = Interpreter.evalApply(
      installed.env(SealedRecName),
      recursorArgs(installed, Level.zero, "propMotive", installed.env("propMinor"), installed.env("wfProof"))
    )
    assert(Value.isPropositionType(propResult.tpe))
    propResult match {
      case VApp(VConst(SealedRecName, _, _), _, _, _) => fail("Prop specialization must use ordinary proof collapse")
      case _                                          =>
    }
  }

  test("ordinary declarations cannot claim either K2 identity") {
    val (_, _, env) = fixture()
    val span = Span(0, 0)
    intercept[ReservedKernelName] {
      Interpreter.evalDecl(Decl.AxiomDecl(SealedRecName, CoreAst.Term.GlobalRef("Type", span), span), env)
    }
    intercept[ReservedKernelName] {
      Interpreter.evalDecl(Decl.AxiomDecl(EquationName, CoreAst.Term.GlobalRef("True", span), span), env)
    }
  }

  test("K2 identities have no builtin evaluator or native-operation dispatch entry") {
    assertEquals(WfPrimitives.reservedNames.intersect(Builtins.entryNames), Set.empty[String])
    assertEquals(WfPrimitives.reservedNames.intersect(Packed.opNames), Set.empty[String])
  }

  test("ordinary non-recursive elimination still reconstructs one Acc.intro layer") {
    val program = elaborate(
      accSource +
        """
          |inductive Peano : Type
          | | zero : Peano
          | | succ (n: Peano): Peano
          |
          |inductive Empty : Prop
          |
          |def noRel (left: Peano)(right: Peano): Prop := Empty
          |
          |def accessible : Acc(Peano, noRel, Peano.zero) :=
          |  Acc.intro(
          |    noRel,
          |    Peano.zero,
          |    fun (y: Peano)(impossible: noRel(y, Peano.zero)): Acc(Peano, noRel, y) => {
          |      match impossible returning Acc(Peano, noRel, y) with
          |    }
          |  )
          |
          |def casesOn (a: Peano)(proof: Acc(Peano, noRel, a)): Peano := {
          |  match proof returning Peano with
          |  | Acc.intro x children => x
          |}
          |
          |{ casesOn(Peano.zero, accessible) }
          |""".stripMargin,
      Prelude.test
    )
    Interpreter.run(program, Prelude.test).get match {
      case VCtor(ConstructorHead("Peano.zero", _, _, _, _), Vector(), _) =>
      case other => fail(s"Expected the direct match to expose Peano.zero, got $other")
    }
  }

  test("named but nonstandard equality cannot authorize an equation") {
    val malformed = Prelude.fromSource(
      "malformed-eq",
      """
        |def Sort (l: Level): Type := builtin
        |inductive Eq {u: Level}(A: Sort(u)) indices (x: A)(y: A) : Prop
        |""".stripMargin,
      ignoredImports = Set.empty
    )
    val decl = malformed.core.decls.collectFirst { case d: Decl.InductiveDecl => d }.get
    intercept[UnsupportedWfExportShape] { validateEquality(decl, malformed.checkedEnv, equalityMetadata) }
  }

  test("equality validation rejects extra constructors, non-diagonal refl, and non-Prop results") {
    def rejected(sourceName: String, expectedReason: String, source: String): Unit = {
      val malformed = Prelude.fromSource(sourceName, source, ignoredImports = Set.empty)
      val decl = malformed.core.decls.collectFirst { case d: Decl.InductiveDecl if d.header.name == "Eq" => d }.get
      val error = intercept[UnsupportedWfExportShape] {
        validateEquality(decl, malformed.checkedEnv, equalityMetadata)
      }
      assert(error.reason.contains(expectedReason), error.msg)
    }

    val base =
      """
        |def Sort (l: Level): Type := builtin
        |namespace Level {
        |  def succ (l: Level): Level := builtin
        |}
        |""".stripMargin
    rejected(
      "extra-eq-constructor",
      "expected sole constructor",
      base +
        """
          |inductive Eq {u: Level}(A: Sort(u)) indices (x: A)(y: A) : Prop
          | | refl (x: A) : Eq(A, x, x)
          | | duplicate (x: A) : Eq(A, x, x)
          |""".stripMargin
    )
    rejected(
      "non-diagonal-eq",
      "Eq.refl diagonal result",
      base +
        """
          |axiom choose {u: Level}{A: Sort(u)}(x: A): A
          |inductive Eq {u: Level}(A: Sort(u)) indices (x: A)(y: A) : Prop
          | | refl (x: A) : Eq(A, x, choose(x))
          |""".stripMargin
    )
    rejected(
      "data-valued-eq",
      "result universe",
      base +
        """
          |inductive Eq {u: Level}(A: Sort(u)) indices (x: A)(y: A) : Sort(Level.succ(u))
          | | refl (x: A) : Eq(A, x, x)
          |""".stripMargin
    )
  }

  test("validators pin the translated and installed implicit calling conventions") {
    val standardEq = eqDecl(Prelude.test)
    val explicitUniverse = standardEq.header.params.head.copy(isImplicit = false)
    val malformedEq = standardEq.copy(
      header = standardEq.header.copy(params = explicitUniverse +: standardEq.header.params.tail)
    )
    intercept[UnsupportedWfExportShape] {
      validateEquality(malformedEq, Prelude.test.checkedEnv, equalityMetadata)
    }

    val standardAcc = elaborate(accSource, Prelude.test).decls.collectFirst { case decl: Decl.InductiveDecl =>
      decl
    }.get
    val implicitCarrier = standardAcc.header.params(1).copy(isImplicit = true)
    val malformedAcc = standardAcc.copy(
      header = standardAcc.header.copy(params = standardAcc.header.params.updated(1, implicitCarrier))
    )
    val env = Interpreter.evalDecl(standardAcc, Prelude.test.checkedEnv)
    intercept[UnsupportedWfExportShape] {
      validateAcc(malformedAcc, env, accMetadata)
    }
  }

  test("Acc validation accepts alpha-renamed binders and irrelevant source spans") {
    val renamed = elaborate(
      """
        |inductive Acc {q: Level}(carrier: Sort(q))(below: carrier -> carrier -> Prop) indices (root: carrier) : Prop
        | | intro (node: carrier)(descend: (child: carrier) -> below(child, node) -> Acc(carrier, below, child)): Acc(carrier, below, node)
        |""".stripMargin,
      Prelude.test
    ).decls.collectFirst { case decl: Decl.InductiveDecl => decl }.get
    val env = Interpreter.evalDecl(renamed, Prelude.test.checkedEnv)
    val unrelatedSpan = Span(1000, 2000)
    val shifted = renamed.copy(
      header = renamed.header.copy(span = unrelatedSpan),
      ctors = renamed.ctors.map(_.copy(span = unrelatedSpan)),
      span = unrelatedSpan
    )
    validateAcc(shifted, env, accMetadata)
  }

  test("Core applications are saturated calls and a v=0 result uses ordinary proof collapse") {
    val installed = concreteFixture
    intercept[ArityMismatch] {
      Interpreter.evalApply(installed.env(SealedRecName), Vector(Level.zero))
    }
    val proof = Interpreter.evalApply(
      installed.env(SealedRecName),
      recursorArgs(installed, Level.zero, "propMotive", installed.env("propMinor"), installed.env("wfProof"))
    )
    assertEquals(proof, Value.canonicalizeProof(VProof(proof.tpe)))
  }

  test("export metadata, universe order, rules, and recursor type are all authenticated") {
    val (equality, acc, env) = fixture()
    val firstExpected = TypeChecker.getType(expectedRecursorType(acc), env)
    val secondExpected = TypeChecker.getType(expectedRecursorType(acc), env)
    assert(ValueEquivalence.defEq(firstExpected, secondExpected))
    intercept[UnsupportedWfExportShape] {
      validateEquality(eqDecl(Prelude.test), Prelude.test.checkedEnv, equalityMetadata.copy(numIndices = 2))
    }
    intercept[UnsupportedWfExportShape] {
      validateEquality(
        eqDecl(Prelude.test),
        Prelude.test.checkedEnv,
        equalityMetadata.copy(producer = ProducerVersion("3.2.0", SupportedProducer.lean, SupportedProducer.leanCommit))
      )
    }
    val accDecl = elaborate(accSource, Prelude.test).decls.collectFirst { case decl: Decl.InductiveDecl => decl }.get
    intercept[UnsupportedWfExportShape] {
      validateAcc(
        accDecl,
        env,
        accMetadata.copy(numParams = 1)
      )
    }
    intercept[UnsupportedWfExportShape] {
      validateAcc(
        accDecl,
        env,
        accMetadata.copy(producer = ProducerVersion("3.2.0", SupportedProducer.lean, SupportedProducer.leanCommit))
      )
    }
    intercept[UnsupportedWfExportShape] {
      install(
        equality,
        acc,
        ExportedRecursor(
          Vector(UniverseRole.Carrier, UniverseRole.MotiveResult),
          expectedRecursorType(acc),
          Vector(RecursorRule("Acc.intro", 2)),
          Span(0, 0)
        ),
        env
      )
    }
    val typeError = intercept[UnsupportedWfExportShape] {
      install(
        equality,
        acc,
        ExportedRecursor(
          Vector(UniverseRole.MotiveResult, UniverseRole.Carrier),
          CoreAst.Term.GlobalRef("Type", Span(0, 0)),
          Vector(RecursorRule("Acc.intro", 2)),
          Span(0, 0)
        ),
        env
      )
    }
    assert(typeError.msg.contains("Pi("))
    assert(typeError.msg.length < 600)
  }
}
