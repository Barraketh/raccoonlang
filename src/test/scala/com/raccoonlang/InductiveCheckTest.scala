package com.raccoonlang

class InductiveCheckTest extends munit.FunSuite with DiagnosticAssertions {

  private def elab(src: String, prelude: Prelude.Config): CoreAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        Elaborator.elab(value, prelude)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def elabAndRun(src: String): Env =
    elab(src, Prelude.test).decls.foldLeft(Prelude.test.checkedEnv) { case (curEnv, decl) =>
      Interpreter.evalDecl(decl, curEnv)
    }

  private def elabAndTypecheck(src: String, prelude: Prelude.Config): Unit = {
    Interpreter.run(elab(src, prelude), prelude)
    ()
  }

  /** The test prelude followed by `assumptions`, which may declare axioms. */
  private def assuming(assumptions: String): Prelude.Config =
    TestSupport.preludeAssuming(TestSupport.testPreludeSource, assumptions)

  private def boxDecl: CoreAst.Decl.InductiveDecl =
    elab(
      """
        |inductive Box (A: Type) : Type
        | | mk (value: A): Box(A)
        |""".stripMargin,
      Prelude.test
    ).decls.head.asInstanceOf[CoreAst.Decl.InductiveDecl]

  private val blockSpan = Span(0, 0)

  private def global(name: String): CoreAst.Term = CoreAst.Term.GlobalRef(name, blockSpan)

  /**
   * `env` with a neutral global of type `ty`: an axiom, as only a trusted prelude declares one. These tests build their
   * environments declaration by declaration, so the axiom is added as a prelude declaration after the families its type
   * names.
   */
  private def assume(name: String, ty: CoreAst.Term, env: Env): Env =
    Interpreter.addPreludeDecl(env, CoreAst.Decl.AxiomDecl(name, ty, blockSpan))

  private def sortAt(level: CoreAst.Form): CoreAst.Term = CoreTestTerms.sortAt(level, blockSpan)

  private val typeSort: CoreAst.Term = sortAt(CoreAst.Form.LevelOne)
  private val propSort: CoreAst.Term = sortAt(CoreAst.Form.LevelZero)

  private def mutualEvenOdd(evenRecursiveFieldType: CoreAst.Term = global("Odd")): CoreAst.Decl.InductiveBlock = {
    val oddField =
      CoreAst.Binder(
        CoreAst.LocalRef(1001, "odd"),
        evenRecursiveFieldType,
        blockSpan,
        CoreAst.BinderSite.Field,
        BinderMode.Explicit
      )
    val evenField = CoreAst.Binder(
      CoreAst.LocalRef(1002, "even"),
      global("Even"),
      blockSpan,
      CoreAst.BinderSite.Field,
      BinderMode.Explicit
    )
    val even = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Even", Vector.empty, Vector.empty, typeSort, blockSpan),
      Vector(
        CoreAst.ConstructorDecl("Even.zero", "zero", Vector.empty, global("Even"), blockSpan),
        CoreAst.ConstructorDecl("Even.succ", "succ", Vector(oddField), global("Even"), blockSpan)
      ),
      seal = None,
      blockSpan
    )
    val odd = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Odd", Vector.empty, Vector.empty, typeSort, blockSpan),
      Vector(CoreAst.ConstructorDecl("Odd.succ", "succ", Vector(evenField), global("Odd"), blockSpan)),
      seal = None,
      blockSpan
    )
    CoreAst.Decl.InductiveBlock(Vector(even, odd), blockSpan)
  }

  private def parameterizedMutual(secondParamType: CoreAst.Term): CoreAst.Decl.InductiveBlock = {
    val firstParam = CoreAst.Binder(
      CoreAst.LocalRef(1010, "A"),
      typeSort,
      blockSpan,
      CoreAst.BinderSite.Parameter,
      BinderMode.Explicit
    )
    val secondParam =
      CoreAst.Binder(
        CoreAst.LocalRef(1011, "B"),
        secondParamType,
        blockSpan,
        CoreAst.BinderSite.Parameter,
        BinderMode.Explicit
      )

    def family(name: String, param: CoreAst.Binder): CoreAst.Decl.InductiveDecl = {
      val result = CoreAst.Term.App(
        global(name),
        Vector(CoreAst.Term.LocalRef(param.localRef, blockSpan)),
        Vector.empty,
        blockSpan
      )
      CoreAst.Decl.InductiveDecl(
        CoreAst.InductiveHeader(name, Vector(param), Vector.empty, typeSort, blockSpan),
        Vector(CoreAst.ConstructorDecl(s"$name.mk", "mk", Vector.empty, result, blockSpan)),
        seal = None,
        blockSpan
      )
    }

    CoreAst.Decl.InductiveBlock(Vector(family("First", firstParam), family("Second", secondParam)), blockSpan)
  }

  private def parameterizedMutualWithStrictlyNegativeParam: CoreAst.Decl.InductiveBlock = {
    val firstParam = CoreAst.Binder(
      CoreAst.LocalRef(1012, "A"),
      typeSort,
      blockSpan,
      CoreAst.BinderSite.Parameter,
      BinderMode.Explicit
    )
    val secondParam = CoreAst.Binder(
      CoreAst.LocalRef(1013, "B"),
      typeSort,
      blockSpan,
      CoreAst.BinderSite.Parameter,
      BinderMode.Explicit
    )
    val innerArg = CoreAst.Binder(
      CoreAst.LocalRef(1014, "a"),
      CoreAst.Term.LocalRef(firstParam.localRef, blockSpan),
      blockSpan,
      CoreAst.BinderSite.Function,
      BinderMode.Explicit
    )
    val firstParamTerm = CoreAst.Term.LocalRef(firstParam.localRef, blockSpan)
    val inner = CoreAst.Term.Pi(
      Vector(innerArg),
      firstParamTerm,
      CoreAst.Closure.unrestricted(blockSpan),
      blockSpan,
      NodeId.fresh()
    )
    val outerArg = CoreAst.Binder(
      CoreAst.LocalRef(1015, "consume"),
      inner,
      blockSpan,
      CoreAst.BinderSite.Function,
      BinderMode.Explicit
    )
    val field = CoreAst.Binder(
      CoreAst.LocalRef(1016, "field"),
      CoreAst.Term
        .Pi(Vector(outerArg), firstParamTerm, CoreAst.Closure.unrestricted(blockSpan), blockSpan, NodeId.fresh()),
      blockSpan,
      CoreAst.BinderSite.Field,
      BinderMode.Explicit
    )

    def result(name: String, param: CoreAst.Binder): CoreAst.Term =
      CoreAst.Term.App(global(name), Vector(CoreAst.Term.LocalRef(param.localRef, blockSpan)), Vector.empty, blockSpan)

    val first = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("First", Vector(firstParam), Vector.empty, typeSort, blockSpan),
      Vector(CoreAst.ConstructorDecl("First.mk", "mk", Vector(field), result("First", firstParam), blockSpan)),
      seal = None,
      blockSpan
    )
    val second = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Second", Vector(secondParam), Vector.empty, typeSort, blockSpan),
      Vector(CoreAst.ConstructorDecl("Second.mk", "mk", Vector.empty, result("Second", secondParam), blockSpan)),
      seal = None,
      blockSpan
    )
    CoreAst.Decl.InductiveBlock(Vector(first, second), blockSpan)
  }

  private def nonUniformRecursiveMutual: CoreAst.Decl.InductiveBlock = {
    val firstParam = CoreAst.Binder(
      CoreAst.LocalRef(1030, "A"),
      typeSort,
      blockSpan,
      CoreAst.BinderSite.Parameter,
      BinderMode.Explicit
    )
    val secondParam = CoreAst.Binder(
      CoreAst.LocalRef(1031, "B"),
      typeSort,
      blockSpan,
      CoreAst.BinderSite.Parameter,
      BinderMode.Explicit
    )
    val firstResult =
      CoreAst.Term.App(
        global("First"),
        Vector(CoreAst.Term.LocalRef(firstParam.localRef, blockSpan)),
        Vector.empty,
        blockSpan
      )
    val secondAtCarrier = CoreAst.Term.App(global("Second"), Vector(global("Carrier")), Vector.empty, blockSpan)
    val recursiveField =
      CoreAst.Binder(
        CoreAst.LocalRef(1032, "child"),
        secondAtCarrier,
        blockSpan,
        CoreAst.BinderSite.Field,
        BinderMode.Explicit
      )
    val first = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("First", Vector(firstParam), Vector.empty, typeSort, blockSpan),
      Vector(CoreAst.ConstructorDecl("First.mk", "mk", Vector(recursiveField), firstResult, blockSpan)),
      seal = None,
      blockSpan
    )
    val secondResult =
      CoreAst.Term.App(
        global("Second"),
        Vector(CoreAst.Term.LocalRef(secondParam.localRef, blockSpan)),
        Vector.empty,
        blockSpan
      )
    val second = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Second", Vector(secondParam), Vector.empty, typeSort, blockSpan),
      Vector(CoreAst.ConstructorDecl("Second.mk", "mk", Vector.empty, secondResult, blockSpan)),
      seal = None,
      blockSpan
    )
    CoreAst.Decl.InductiveBlock(Vector(first, second), blockSpan)
  }

  private def recursiveResultIndexMutual: CoreAst.Decl.InductiveBlock = {
    val index =
      CoreAst.Binder(CoreAst.LocalRef(1040, "X"), typeSort, blockSpan, CoreAst.BinderSite.Field, BinderMode.Explicit)
    val firstAtSecond = CoreAst.Term.App(global("First"), Vector(global("Second")), Vector.empty, blockSpan)
    val first = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("First", Vector.empty, Vector(index), typeSort, blockSpan),
      Vector(CoreAst.ConstructorDecl("First.mk", "mk", Vector.empty, firstAtSecond, blockSpan)),
      seal = None,
      blockSpan
    )
    val second = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Second", Vector.empty, Vector.empty, typeSort, blockSpan),
      Vector(CoreAst.ConstructorDecl("Second.mk", "mk", Vector.empty, global("Second"), blockSpan)),
      seal = None,
      blockSpan
    )
    CoreAst.Decl.InductiveBlock(Vector(first, second), blockSpan)
  }

  test("explicit singleton inductive blocks use the common declaration checker") {
    val decl = boxDecl
    val block = CoreAst.Decl.InductiveBlock(Vector(decl), decl.span)

    val env = Interpreter.evalDecl(block, Prelude.test.checkedEnv)

    assert(env.globals.contains("Box"))
    assert(env.globals.contains("Box.mk"))
  }

  test("native singleton declarations never infer source universe coordinates") {
    val universe = CoreAst.Binder(
      CoreAst.LocalRef(1060, "u"),
      global("Level"),
      blockSpan,
      CoreAst.BinderSite.Parameter,
      BinderMode.Explicit
    )
    val universeTerm = CoreAst.Term.LocalRef(universe.localRef, blockSpan)
    val sort = CoreTestTerms.sortAt(universeTerm, blockSpan)
    val result = CoreAst.Term.App(global("Poly"), Vector(universeTerm), Vector.empty, blockSpan)
    val declaration = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Poly", Vector(universe), Vector.empty, sort, blockSpan),
      Vector(CoreAst.ConstructorDecl("Poly.mk", "mk", Vector.empty, result, blockSpan)),
      seal = None,
      blockSpan
    )

    val env = Interpreter.evalDecl(declaration, Prelude.test.checkedEnv)
    env("Poly") match {
      case Value.VConst(_, Value.Inductive(meta), _) =>
        assertEquals(meta.block.key, Value.InductiveBlockKey(Vector("Poly"), 1))
      case other => fail(s"Expected Poly family head, got $other")
    }
  }

  test("mutual families see every provisional head and publish atomically") {
    val env = Interpreter.evalDecl(mutualEvenOdd(), Prelude.test.checkedEnv)

    assert(env.globals.contains("Even"))
    assert(env.globals.contains("Odd"))
    assert(env.globals.contains("Even.zero"))
    assert(env.globals.contains("Even.succ"))
    assert(env.globals.contains("Odd.succ"))
    def meta(name: String): Value.InductiveMeta =
      env(name) match {
        case Value.VConst(_, Value.Inductive(value), _) => value
        case other                                      => fail(s"Expected $name family head, got $other")
      }
    val evenMeta = meta("Even")
    val oddMeta = meta("Odd")
    assert(evenMeta.block eq oddMeta.block)
    assert(oddMeta.block.isInstanceOf[Value.CheckedInductiveBlockSchema])
    assert(oddMeta.block.positiveParams.isEmpty)
    assert(!oddMeta.projectionInfo.get.etaEligible)

    val matchEnv = assume("evenWitness", global("Even"), assume("oddWitness", global("Odd"), env))
    val evenMatch = CoreAst.Term.Match(
      global("evenWitness"),
      motive = global("Even"),
      cases = Vector(
        CoreAst.Case("Even.zero", isFullyQualified = true, Vector.empty, global("evenWitness"), blockSpan),
        CoreAst.Case(
          "Even.succ",
          isFullyQualified = true,
          Vector(CoreAst.PatternVar(CoreAst.LocalRef(1020, "_"), blockSpan)),
          global("evenWitness"),
          blockSpan
        )
      ),
      wildcard = None,
      blockSpan,
      NodeId.fresh()
    )
    val oddMatch = CoreAst.Term.Match(
      global("oddWitness"),
      motive = global("Odd"),
      cases = Vector(
        CoreAst.Case(
          "Odd.succ",
          isFullyQualified = true,
          Vector(CoreAst.PatternVar(CoreAst.LocalRef(1021, "_"), blockSpan)),
          global("oddWitness"),
          blockSpan
        )
      ),
      wildcard = None,
      blockSpan,
      NodeId.fresh()
    )
    TypeChecker.checkTerm(evenMatch, matchEnv)
    TypeChecker.checkTerm(oddMatch, matchEnv)
  }

  test("mutual blocks alpha-canonicalize common parameter binders") {
    val env = Interpreter.evalDecl(parameterizedMutual(typeSort), Prelude.test.checkedEnv)

    assert(env.globals.contains("First.mk"))
    assert(env.globals.contains("Second.mk"))
    val first = env("First").asInstanceOf[Value.VConst].constType.asInstanceOf[Value.Inductive].meta
    val second = env("Second").asInstanceOf[Value.VConst].constType.asInstanceOf[Value.Inductive].meta
    assert(first.block eq second.block)
    assertEquals(first.block.positiveParams, DepSet(0))
  }

  test("mutual positive parameters use a strict block-wide intersection") {
    val env = Interpreter.evalDecl(parameterizedMutualWithStrictlyNegativeParam, Prelude.test.checkedEnv)
    val first = env("First").asInstanceOf[Value.VConst].constType.asInstanceOf[Value.Inductive].meta
    val second = env("Second").asInstanceOf[Value.VConst].constType.asInstanceOf[Value.Inductive].meta

    assert(first.block eq second.block)
    assertEquals(first.block.positiveParams, DepSet.empty)
  }

  test("mutual blocks reject mismatched common parameter types without publication") {
    val base = Prelude.test.checkedEnv
    val error = interceptError[InvalidInductiveBlock] {
      Interpreter.evalDecl(parameterizedMutual(propSort), base)
    }

    assert(error.reason.contains("different type for common parameter 0"))
    assert(!base.globals.contains("First"))
    assert(!base.globals.contains("Second"))
  }

  test("mutual blocks reject negative sibling occurrences without publication") {
    val functionArg = CoreAst.Binder(
      CoreAst.LocalRef(1020, "x"),
      global("Odd"),
      blockSpan,
      CoreAst.BinderSite.Function,
      BinderMode.Explicit
    )
    val negativeField =
      CoreAst.Term.Pi(
        Vector(functionArg),
        global("Even"),
        CoreAst.Closure.unrestricted(blockSpan),
        blockSpan,
        NodeId.fresh()
      )
    val base = Prelude.test.checkedEnv

    interceptError[NonStrictlyPositive] {
      Interpreter.evalDecl(mutualEvenOdd(negativeField), base)
    }

    assert(!base.globals.contains("Even"))
    assert(!base.globals.contains("Odd"))
    assert(!base.globals.contains("Even.zero"))
  }

  test("mutual blocks reject non-uniform parameters on recursive sibling fields") {
    val base = assume("Carrier", typeSort, Prelude.test.checkedEnv)

    interceptError[NonStrictlyPositive] {
      Interpreter.evalDecl(nonUniformRecursiveMutual, base)
    }

    assert(!base.globals.contains("First"))
    assert(!base.globals.contains("Second"))
  }

  test("mutual blocks reject family occurrences in constructor result indices") {
    val base = Prelude.test.checkedEnv

    interceptError[NonStrictlyPositive] {
      Interpreter.evalDecl(recursiveResultIndexMutual, base)
    }

    assert(!base.globals.contains("First"))
    assert(!base.globals.contains("Second"))
  }

  test("mutual siblings each inhabit their own declared universe") {
    val block = mutualEvenOdd()
    val odd = block.families(1)
    val mixed = block.copy(
      families = block.families.updated(1, odd.copy(header = odd.header.copy(resultTy = propSort)))
    )
    val env = Interpreter.evalDecl(mixed, Prelude.test.checkedEnv)

    assert(!Sorts.isProposition(env("Even")))
    assert(Sorts.isProposition(env("Odd")))
    // Odd's field is data from its sibling that no index determines, so Odd eliminates only into propositions.
    assert(!ProofReconstruction.canRecoverAll(env("Odd")))
  }

  test("Inductive type must be a Sort (no Pi): inductive Bad : Peano") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Bad : Peano
        | | mk : Bad
        |
        |""".stripMargin

    interceptError[InductiveTypeNotASort] { elabAndTypecheck(p, Prelude.test) }
  }

  test("Inductive type must be a Sort (Pi case): inductive Bad(A: Type) : A") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Bad(A: Type) : A
        | | mk: Bad(A)
        |
        |""".stripMargin

    interceptError[InductiveTypeNotASort] { elabAndTypecheck(p, Prelude.test) }
  }

  test("Constructor result must be inductive head: ctor returns Peano, not Bad") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Bad : Type
        | | mk : Peano
        |
        |""".stripMargin

    interceptError[InvalidConstructorResult] { elabAndTypecheck(p, Prelude.test) }
  }

  test("Field universe too large: (A: Sort Level.one) in Type inductive") {
    val p =
      """
        |inductive Small : Type
        | | mk (A: Sort { level = one }): Small
        |
        |""".stripMargin

    interceptError[InductiveUniverseTooSmall] { elabAndTypecheck(p, Prelude.test) }
  }

  test("Non-strict positivity: function-typed field with Bad in domain (f: Bad -> Bad)") {
    val p =
      """
        |inductive Bad : Type
        | | con (f: Bad -> Bad): Bad
        |
        |""".stripMargin

    interceptError[NonStrictlyPositive] { elabAndTypecheck(p, Prelude.test) }
  }

  test("Non-strict positivity: aligned universes under other constructor F args (Wrap u (Bad u))") {
    val p =
      """
        |inductive Bad : Sort { level = zero }
        | | con(x: Wrap(Bad)): Bad
        |
        |""".stripMargin

    interceptError[NonStrictlyPositive] {
      elabAndTypecheck(p, assuming("axiom Wrap (A: Sort { level = zero }): Sort { level = zero }\n"))
    }
  }

  test("Constructor result must use family params uniformly") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Sort { level = one }
        | | mk (B: Type)(n: Peano): Vec(B, n)
        |
        |""".stripMargin

    interceptError[NonUniformInductiveParam] { elabAndTypecheck(p, Prelude.test) }
  }

  test("Constructor result must have full family arity") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Sort { level = one }
        | | bad : Vec(A)
        |
        |""".stripMargin

    interceptError[ArityMismatch] { elabAndTypecheck(p, Prelude.test) }
  }

  test("Constructor implicit binders may bind indices after params when a field forces them") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Sort { level = one }
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano}(tail: Vec(A, n))(head: A): Vec(A, Peano.succ(n))
        |
        |""".stripMargin

    elabAndTypecheck(p, Prelude.test)
  }

  test("Constructor-declared implicits must be forced by fields; family demotion does not apply") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Sort { level = one }
        | | bad {n: Peano}: Vec(A, n)
        |
        |""".stripMargin

    interceptError[NonForcedImplicitParam] { elabAndTypecheck(p, Prelude.test) }
  }

  test("Constructor binders may not shadow family params") {
    val p =
      """
        |struct Bad (A: Type) : Sort { level = succ(one) }
        | | mk (A: Type): Bad(A)
        |
        |""".stripMargin

    interceptError[AlreadyDefined] { elabAndTypecheck(p, Prelude.test) }
  }

  test("Constructor implicit binders include inductive params") {
    val p =
      """
        |inductive Bad (A: Type)(B: Type) : Sort { level = one }
        | | inl (a: A) : Bad(A, B)
        |
        |""".stripMargin

    elabAndTypecheck(p, Prelude.test)
  }

  test("Hidden constructor binders may not shadow family params") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Bad (A: Type) : Type
        | | mk {A: Peano}: Bad(A)
        |
        |""".stripMargin

    interceptError[AlreadyDefined] { elabAndTypecheck(p, Prelude.test) }
  }

  test("Nested strictly positive: recursive occurrence under positive List parameter") {
    val p =
      """
        |inductive List (A: Type) : Type
        | | nil : List(A)
        | | cons (head: A) (tail: List(A)) : List(A)
        |
        |inductive Tree : Type
        | | node (children: List(Tree)) : Tree
        |
        |""".stripMargin

    elabAndTypecheck(p, Prelude.test)
  }

  test("Nested non-positive: recursive occurrence under forbidden container parameter") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive BadBox (A: Type) : Type
        | | mk (f: A -> Peano) : BadBox(A)
        |
        |inductive BadTree : Type
        | | node (children: BadBox(BadTree)) : BadTree
        |
        |""".stripMargin

    interceptError[NonStrictlyPositive] { elabAndTypecheck(p, Prelude.test) }
  }

  test("Nested non-positive: container parameter contravariant in later family argument") {
    val p =
      """
        |inductive Box {u: Level}(A: Sort { level = u })(F: A -> Type) : Sort { level = max(u, one) }
        | | mk : Box(A, F)
        |
        |inductive Bad : Sort { level = succ(one) }
        | | con {F: Bad -> Type} (x: Box(Bad, F)) : Bad
        |
        |""".stripMargin

    interceptError[NonStrictlyPositive] { elabAndTypecheck(p, Prelude.test) }
  }

  test("Nested metadata: dependent family argument tracks its own variable") {
    val p =
      """
        |inductive Box (A: Type)(F: A -> Type) : Type
        | | mk : Box(A, F)
        |
        |""".stripMargin

    elabAndRun(p)("Box") match {
      case Value.VConst(_, Value.Inductive(meta), _) =>
        assertEquals(meta.block.positiveParams, DepSet(1))
      case other => fail(s"Expected Box to be an inductive head, got $other")
    }
  }

  test("Nested metadata: true source indices never become positivity capabilities") {
    val p =
      """
        |inductive Indexed (A: Type) indices (F: Type -> A) : Sort { level = succ(one) }
        | | mk (F: Type -> A): Indexed(A, F)
        |""".stripMargin

    elabAndRun(p)("Indexed") match {
      case Value.VConst(_, Value.Inductive(meta), _) =>
        assertEquals(meta.block.positiveParams, DepSet.empty)
      case other => fail(s"Expected Indexed to be an inductive head, got $other")
    }
  }

  test("Nested non-positive: recursive occurrence in its own family argument") {
    val p =
      """
        |inductive Bad (A: Type) : Type
        | | con (x: Bad(Bad(A))) : Bad(A)
        |
        |""".stripMargin

    interceptError[NonStrictlyPositive] { elabAndTypecheck(p, Prelude.test) }
  }

  test("Nested non-positive: recursive occurrence in constructor-valued family argument") {
    val p =
      """
        |inductive BoxType : Type
        | | tag (P: Prop) : BoxType
        |
        |inductive Bad indices (t: BoxType) : Prop
        | | con {t: BoxType} (anchor: Bad(t)) (x: Bad(BoxType.tag(Bad(t)))) : Bad(t)
        |
        |""".stripMargin

    interceptError[NonStrictlyPositive] { elabAndTypecheck(p, Prelude.test) }
  }

  test("Nested metadata: a higher-kinded parameter is positive when only its result is stored") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |inductive Higher (F: Type -> Type) : Type
        | | mk (x: F(Peano)) : Higher(F)
        |
        |""".stripMargin

    elabAndRun(p)("Higher") match {
      case Value.VConst(_, Value.Inductive(meta), _) =>
        assertEquals(meta.block.positiveParams, DepSet(0))
      case other => fail(s"Expected Higher to be an inductive head, got $other")
    }
  }

  test("Nested non-positive: an axiomatized dependent family argument type is conservative") {
    val assumptions =
      """
        |struct TypeBox (A: Type) : Sort { level = succ(one) }
        | | mk (T: Type) : TypeBox(A)
        |
        |axiom typeBox (A: Type): TypeBox(A)
        |""".stripMargin
    val p =
      """
        |inductive Box (A: Type)(F: (typeBox(A).T)) : Type
        | | mk : Box(A, F)
        |
        |inductive Bad : Type
        | | con {F: typeBox(Bad).T} (x: Box(Bad, F)) : Bad
        |
        |""".stripMargin

    interceptError[NonStrictlyPositive] { elabAndTypecheck(p, assuming(assumptions)) }
  }
}
