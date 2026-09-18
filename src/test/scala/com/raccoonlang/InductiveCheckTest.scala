package com.raccoonlang

class InductiveCheckTest extends munit.FunSuite {

  private def elab(src: String): CoreAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        Elaborator.elab(value, Prelude.test)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def elabAndRun(src: String): Env =
    elab(src).decls.foldLeft(Prelude.test.checkedEnv) { case (curEnv, decl) =>
      Interpreter.evalDecl(decl, curEnv)
    }

  private def elabAndTypecheck(src: String): Unit = {
    Interpreter.run(elab(src), Prelude.test)
    ()
  }

  private def boxDecl: CoreAst.Decl.InductiveDecl =
    elab(
      """
        |inductive Box (A: Type) : Type
        | | mk (value: A): Box(A)
        |""".stripMargin
    ).decls.head.asInstanceOf[CoreAst.Decl.InductiveDecl]

  private val blockSpan = Span(0, 0)

  private def global(name: String): CoreAst.Term = CoreAst.Term.GlobalRef(name, blockSpan)

  private def mutualEvenOdd(evenRecursiveFieldType: CoreAst.Term = global("Odd")): CoreAst.Decl.InductiveBlock = {
    val oddField = CoreAst.Binder(CoreAst.LocalRef(1001, "odd"), evenRecursiveFieldType, blockSpan)
    val evenField = CoreAst.Binder(CoreAst.LocalRef(1002, "even"), global("Even"), blockSpan)
    val even = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Even", Vector.empty, Vector.empty, global("Type"), blockSpan),
      Vector(
        CoreAst.ConstructorDecl("Even.zero", "zero", Vector.empty, global("Even"), blockSpan),
        CoreAst.ConstructorDecl("Even.succ", "succ", Vector(oddField), global("Even"), blockSpan)
      ),
      blockSpan
    )
    val odd = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Odd", Vector.empty, Vector.empty, global("Type"), blockSpan),
      Vector(CoreAst.ConstructorDecl("Odd.succ", "succ", Vector(evenField), global("Odd"), blockSpan)),
      blockSpan
    )
    CoreAst.Decl.InductiveBlock(Vector(even, odd), blockSpan)
  }

  private def parameterizedMutual(secondParamType: CoreAst.Term): CoreAst.Decl.InductiveBlock = {
    val firstParam = CoreAst.Binder(CoreAst.LocalRef(1010, "A"), global("Type"), blockSpan)
    val secondParam = CoreAst.Binder(CoreAst.LocalRef(1011, "B"), secondParamType, blockSpan)

    def family(name: String, param: CoreAst.Binder): CoreAst.Decl.InductiveDecl = {
      val result = CoreAst.Term.App(global(name), Vector(CoreAst.Term.LocalRef(param.localRef, blockSpan)), blockSpan)
      CoreAst.Decl.InductiveDecl(
        CoreAst.InductiveHeader(name, Vector(param), Vector.empty, global("Type"), blockSpan),
        Vector(CoreAst.ConstructorDecl(s"$name.mk", "mk", Vector.empty, result, blockSpan)),
        blockSpan
      )
    }

    CoreAst.Decl.InductiveBlock(Vector(family("First", firstParam), family("Second", secondParam)), blockSpan)
  }

  private def parameterizedMutualWithStrictlyNegativeParam: CoreAst.Decl.InductiveBlock = {
    val firstParam = CoreAst.Binder(CoreAst.LocalRef(1012, "A"), global("Type"), blockSpan)
    val secondParam = CoreAst.Binder(CoreAst.LocalRef(1013, "B"), global("Type"), blockSpan)
    val innerArg = CoreAst.Binder(
      CoreAst.LocalRef(1014, "a"),
      CoreAst.Term.LocalRef(firstParam.localRef, blockSpan),
      blockSpan
    )
    val firstParamTerm = CoreAst.Term.LocalRef(firstParam.localRef, blockSpan)
    val inner = CoreAst.Term.Pi(Vector(innerArg), firstParamTerm, blockSpan)
    val outerArg = CoreAst.Binder(CoreAst.LocalRef(1015, "consume"), inner, blockSpan)
    val field = CoreAst.Binder(
      CoreAst.LocalRef(1016, "field"),
      CoreAst.Term.Pi(Vector(outerArg), firstParamTerm, blockSpan),
      blockSpan
    )

    def result(name: String, param: CoreAst.Binder): CoreAst.Term =
      CoreAst.Term.App(global(name), Vector(CoreAst.Term.LocalRef(param.localRef, blockSpan)), blockSpan)

    val first = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("First", Vector(firstParam), Vector.empty, global("Type"), blockSpan),
      Vector(CoreAst.ConstructorDecl("First.mk", "mk", Vector(field), result("First", firstParam), blockSpan)),
      blockSpan
    )
    val second = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Second", Vector(secondParam), Vector.empty, global("Type"), blockSpan),
      Vector(CoreAst.ConstructorDecl("Second.mk", "mk", Vector.empty, result("Second", secondParam), blockSpan)),
      blockSpan
    )
    CoreAst.Decl.InductiveBlock(Vector(first, second), blockSpan)
  }

  private def nonUniformRecursiveMutual: CoreAst.Decl.InductiveBlock = {
    val firstParam = CoreAst.Binder(CoreAst.LocalRef(1030, "A"), global("Type"), blockSpan)
    val secondParam = CoreAst.Binder(CoreAst.LocalRef(1031, "B"), global("Type"), blockSpan)
    val firstResult =
      CoreAst.Term.App(global("First"), Vector(CoreAst.Term.LocalRef(firstParam.localRef, blockSpan)), blockSpan)
    val secondAtCarrier = CoreAst.Term.App(global("Second"), Vector(global("Carrier")), blockSpan)
    val recursiveField = CoreAst.Binder(CoreAst.LocalRef(1032, "child"), secondAtCarrier, blockSpan)
    val first = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("First", Vector(firstParam), Vector.empty, global("Type"), blockSpan),
      Vector(CoreAst.ConstructorDecl("First.mk", "mk", Vector(recursiveField), firstResult, blockSpan)),
      blockSpan
    )
    val secondResult =
      CoreAst.Term.App(global("Second"), Vector(CoreAst.Term.LocalRef(secondParam.localRef, blockSpan)), blockSpan)
    val second = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Second", Vector(secondParam), Vector.empty, global("Type"), blockSpan),
      Vector(CoreAst.ConstructorDecl("Second.mk", "mk", Vector.empty, secondResult, blockSpan)),
      blockSpan
    )
    CoreAst.Decl.InductiveBlock(Vector(first, second), blockSpan)
  }

  private def recursiveResultIndexMutual: CoreAst.Decl.InductiveBlock = {
    val index = CoreAst.Binder(CoreAst.LocalRef(1040, "X"), global("Type"), blockSpan)
    val firstAtSecond = CoreAst.Term.App(global("First"), Vector(global("Second")), blockSpan)
    val first = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("First", Vector.empty, Vector(index), global("Type"), blockSpan),
      Vector(CoreAst.ConstructorDecl("First.mk", "mk", Vector.empty, firstAtSecond, blockSpan)),
      blockSpan
    )
    val second = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Second", Vector.empty, Vector.empty, global("Type"), blockSpan),
      Vector(CoreAst.ConstructorDecl("Second.mk", "mk", Vector.empty, global("Second"), blockSpan)),
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
    val universe = CoreAst.Binder(CoreAst.LocalRef(1060, "u"), global("Level"), blockSpan)
    val universeTerm = CoreAst.Term.LocalRef(universe.localRef, blockSpan)
    val sort = CoreAst.Term.App(global("Sort"), Vector(universeTerm), blockSpan)
    val result = CoreAst.Term.App(global("Poly"), Vector(universeTerm), blockSpan)
    val declaration = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Poly", Vector(universe), Vector.empty, sort, blockSpan),
      Vector(CoreAst.ConstructorDecl("Poly.mk", "mk", Vector.empty, result, blockSpan)),
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

    val matchEnv = Interpreter.evalDecl(
      CoreAst.Decl.AxiomDecl("evenWitness", global("Even"), blockSpan),
      Interpreter.evalDecl(CoreAst.Decl.AxiomDecl("oddWitness", global("Odd"), blockSpan), env)
    )
    val evenMatch = CoreAst.Term.Match(
      global("evenWitness"),
      motive = None,
      cases = Vector(
        CoreAst.Case("Even.zero", isFullyQualified = true, Vector.empty, global("evenWitness"), blockSpan),
        CoreAst.Case("Even.succ", isFullyQualified = true, Vector(None), global("evenWitness"), blockSpan)
      ),
      blockSpan
    )
    val oddMatch = CoreAst.Term.Match(
      global("oddWitness"),
      motive = None,
      cases = Vector(CoreAst.Case("Odd.succ", isFullyQualified = true, Vector(None), global("oddWitness"), blockSpan)),
      blockSpan
    )
    TypeChecker.checkTerm(evenMatch, matchEnv)
    TypeChecker.checkTerm(oddMatch, matchEnv)
  }

  test("mutual blocks alpha-canonicalize common parameter binders") {
    val env = Interpreter.evalDecl(parameterizedMutual(global("Type")), Prelude.test.checkedEnv)

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
    val error = intercept[InvalidInductiveBlock] {
      Interpreter.evalDecl(parameterizedMutual(global("Prop")), base)
    }

    assert(error.msg.contains("different type for common parameter 0"))
    assert(!base.globals.contains("First"))
    assert(!base.globals.contains("Second"))
  }

  test("mutual blocks reject negative sibling occurrences without publication") {
    val functionArg = CoreAst.Binder(CoreAst.LocalRef(1020, "x"), global("Odd"), blockSpan)
    val negativeField = CoreAst.Term.Pi(Vector(functionArg), global("Even"), blockSpan)
    val base = Prelude.test.checkedEnv

    intercept[NonStrictlyPositive] {
      Interpreter.evalDecl(mutualEvenOdd(negativeField), base)
    }

    assert(!base.globals.contains("Even"))
    assert(!base.globals.contains("Odd"))
    assert(!base.globals.contains("Even.zero"))
  }

  test("mutual blocks reject non-uniform parameters on recursive sibling fields") {
    val base = Interpreter.evalDecl(
      CoreAst.Decl.AxiomDecl("Carrier", global("Type"), blockSpan),
      Prelude.test.checkedEnv
    )

    intercept[NonStrictlyPositive] {
      Interpreter.evalDecl(nonUniformRecursiveMutual, base)
    }

    assert(!base.globals.contains("First"))
    assert(!base.globals.contains("Second"))
  }

  test("mutual blocks reject family occurrences in constructor result indices") {
    val base = Prelude.test.checkedEnv

    intercept[NonStrictlyPositive] {
      Interpreter.evalDecl(recursiveResultIndexMutual, base)
    }

    assert(!base.globals.contains("First"))
    assert(!base.globals.contains("Second"))
  }

  test("mutual blocks require every family to inhabit the same universe") {
    val block = mutualEvenOdd()
    val odd = block.families(1)
    val mismatched = block.copy(
      families = block.families.updated(1, odd.copy(header = odd.header.copy(resultTy = global("Prop"))))
    )
    val base = Prelude.test.checkedEnv
    val error = intercept[InvalidInductiveBlock] {
      Interpreter.evalDecl(mismatched, base)
    }

    assert(error.msg.contains("Odd lives in"))
    assert(!base.globals.contains("Even"))
    assert(!base.globals.contains("Odd"))
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

    intercept[InductiveTypeNotASort] { elabAndTypecheck(p) }
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

    intercept[InductiveTypeNotASort] { elabAndTypecheck(p) }
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

    intercept[InvalidConstructorResult] { elabAndTypecheck(p) }
  }

  test("Field universe too large: (A: Sort Level.one) in Type inductive") {
    val p =
      """
        |inductive Small : Type
        | | mk (A: Sort(Level.one)): Small
        |
        |""".stripMargin

    intercept[InductiveUniverseTooSmall] { elabAndTypecheck(p) }
  }

  test("Non-strict positivity: function-typed field with Bad in domain (f: Bad -> Bad)") {
    val p =
      """
        |inductive Bad : Type
        | | con (f: Bad -> Bad): Bad
        |
        |""".stripMargin

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
  }

  test("Non-strict positivity: aligned universes under other constructor F args (Wrap u (Bad u))") {
    val p =
      """
        |opaque def Wrap(A: Sort(Level.zero)): Sort(Level.zero) := A
        |
        |inductive Bad : Sort(Level.zero)
        | | con(x: Wrap(Bad)): Bad
        |
        |""".stripMargin

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
  }

  test("Constructor result must use family params uniformly") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Sort(Level.one)
        | | mk (B: Type)(n: Peano): Vec(B, n)
        |
        |""".stripMargin

    intercept[NonUniformInductiveParam] { elabAndTypecheck(p) }
  }

  test("Constructor result must have full family arity") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Sort(Level.one)
        | | bad : Vec(A)
        |
        |""".stripMargin

    intercept[ArityMismatch] { elabAndTypecheck(p) }
  }

  test("Constructor implicit binders may bind indices after params when a field forces them") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Sort(Level.one)
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano}(tail: Vec(A, n))(head: A): Vec(A, Peano.succ(n))
        |
        |""".stripMargin

    elabAndTypecheck(p)
  }

  test("Constructor-declared implicits must be forced by fields; family demotion does not apply") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Sort(Level.one)
        | | bad {n: Peano}: Vec(A, n)
        |
        |""".stripMargin

    intercept[NonForcedImplicitParam] { elabAndTypecheck(p) }
  }

  test("Constructor binders may not shadow family params") {
    val p =
      """
        |struct Bad (A: Type) : Sort(Level.succ(Level.one))
        | | mk (A: Type): Bad(A)
        |
        |""".stripMargin

    intercept[AlreadyDefined] { elabAndTypecheck(p) }
  }

  test("Constructor implicit binders include inductive params") {
    val p =
      """
        |inductive Bad (A: Type)(B: Type) : Sort(Level.one)
        | | inl (a: A) : Bad(A, B)
        |
        |""".stripMargin

    elabAndTypecheck(p)
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

    intercept[AlreadyDefined] { elabAndTypecheck(p) }
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

    elabAndTypecheck(p)
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

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
  }

  test("Nested non-positive: container parameter contravariant in later family argument") {
    val p =
      """
        |inductive Box {u: Level}(A: Sort(u))(F: A -> Type) : Sort(Level.max(u, Level.one))
        | | mk : Box(A, F)
        |
        |inductive Bad : Sort(Level.succ(Level.one))
        | | con {F: Bad -> Type} (x: Box(Bad, F)) : Bad
        |
        |""".stripMargin

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
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
        |inductive Indexed (A: Type) indices (F: Type -> A) : Sort(Level.succ(Level.one))
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

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
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

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
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

  test("Nested non-positive: opaque dependent family argument type is conservative") {
    val p =
      """
        |struct TypeBox (A: Type) : Sort(Level.succ(Level.one))
        | | mk (T: Type) : TypeBox(A)
        |
        |opaque def typeBox (A: Type): TypeBox(A) := TypeBox.mk(A, A)
        |
        |inductive Box (A: Type)(F: (typeBox(A).T)) : Type
        | | mk : Box(A, F)
        |
        |inductive Bad : Type
        | | con {F: typeBox(Bad).T} (x: Box(Bad, F)) : Bad
        |
        |""".stripMargin

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
  }
}
