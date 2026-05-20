package com.raccoonlang

class TypeClassTests extends munit.FunSuite {
  private def parseProgram(src: String): CoreAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) => Elaborator.elab(value)
      case err: Failure         => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def runProgram(src: String): Value =
    Interpreter.run(parseProgram(src)).getOrElse(fail("Program has no body"))

  private def typecheckProgram(src: String): Unit =
    Interpreter.run(parseProgram(src))

  private def compileWorlds(src: String): Interpreter.Worlds =
    parseProgram(src).decls.foldLeft(Interpreter.initialWorlds) { case (worlds, decl) =>
      Interpreter.evalDecl(decl, worlds)
    }

  private def namedValue(env: TypecheckEnv, name: String): Value =
    env(name) match {
      case h: Value.ConstructorHead if h.totalArity == 0 => Value.VCtor(h, Vector.empty, h.tpe)
      case other                                         => other
    }

  private def applyValue(fn: Value, args: Value*)(implicit eqStore: EqStore): Value =
    Interpreter.evalApply(fn, args.toVector)

  private def ctorName(v: Value): String = v match {
    case Value.VCtor(head, _, _) => head.name
    case other                   => fail(s"Expected constructor value, got $other")
  }

  private val prelude =
    """
      |inductive Nat : Type
      | | zero : Nat
      | | succ (_: Nat) : Nat
      |
      |inductive Bool : Type
      | | true : Bool
      | | false : Bool
      |
      |struct DecEq (A: Type) : Type
      | | mk {A: Type} (ok: Bool) : DecEq(A)
      |
      |""".stripMargin

  test("derive parses to CoreAst only and checks to the resolved term") {
    val worlds = compileWorlds(
      prelude +
        """
          |def instance natEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |""".stripMargin
    )

    val body = parseProgram(
      prelude +
        """
          |def instance natEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |
          |derive[DecEq(Nat)]
          |""".stripMargin
    ).body.getOrElse(fail("Program has no body"))
    assert(body.isInstanceOf[CoreAst.Term.Derive])

    implicit val eqStore: EqStore = EqStore.empty
    val checkedV = TypeChecker.check(body, worlds.checkEnv)
    val ctx = ValueQuote.quoteContext(worlds.checkEnv)
    val term = ValueQuote.quoteTerm(checkedV, ctx, body.span)

    term match {
      case ElabAst.Term.GlobalRef("natEq", _) =>
      case other                              => fail(s"Expected resolved natEq term, got $other")
    }
  }

  test("def instance is found by explicit derive expression") {
    val p =
      prelude +
        """
          |def instance natEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |
          |inline def useEq (A: Type)[eqA: DecEq(A)]: DecEq(A) := eqA
          |
          |{
          |  useEq(Nat, derive[DecEq(Nat)])
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "DecEq.mk")
  }

  test("checked term carries resolved instance result so runtime evaluation does not search") {
    val worlds = compileWorlds(
      prelude +
        """
          |def instance natEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |
          |inline def useEq (A: Type)[eqA: DecEq(A)]: DecEq(A) := eqA
          |
          |inline def useNatEq : DecEq(Nat) := useEq(Nat, derive[DecEq(Nat)])
          |
          |""".stripMargin
    )

    val body = parseProgram(
      prelude +
        """
          |def instance natEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |
          |inline def useEq (A: Type)[eqA: DecEq(A)]: DecEq(A) := eqA
          |
          |inline def useNatEq : DecEq(Nat) := useEq(Nat, derive[DecEq(Nat)])
          |
          |{ useNatEq }
          |""".stripMargin
    ).body.getOrElse(fail("Program has no body"))
    implicit val eqStore: EqStore = EqStore.empty

    val checkedV  = TypeChecker.check(body, worlds.checkEnv)
    val checkedTerm =
      ValueQuote.quoteTerm(checkedV, ValueQuote.quoteContext(worlds.checkEnv), body.span)

    val runEnvWithoutSearch = worlds.runEnv.copy(globalInstances = InstanceRegistry.empty)
    assertEquals(ctorName(Interpreter.evalTerm(checkedTerm, runEnvWithoutSearch)), "DecEq.mk")

  }

  test("parameterized instance recursively derives dependencies") {
    val p =
      prelude +
        """
          |inductive List (A: Type) : Type
          | | nil {A: Type} : List(A)
          |
          |def instance natEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |
          |def instance listEq [ea: DecEq($A)]: DecEq(List(A)) := DecEq.mk(List(A), Bool.true)
          |
          |{
          |  derive[DecEq(List(Nat))]
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "DecEq.mk")
  }

  test("ordinary candidate parameters are inferred from the target") {
    val p =
      prelude +
        """
          |def instance genericEq (A: Type): DecEq(A) := DecEq.mk(A, Bool.true)
          |
          |{
          |  derive[DecEq(Nat)].ok
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool.true")
  }

  test("instance candidate parameters are inferred from the target before recursive search") {
    val p =
      prelude +
        """
          |struct Wrap (A: Type)(eqA: DecEq(A)) : Type
          | | mk {A: Type}{eqA: DecEq(A)} (ok: Bool) : Wrap(A, eqA)
          |
          |def natEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |
          |def instance wrap [eqA: DecEq($A)]: Wrap(A, eqA) := Wrap.mk(A, eqA, Bool.true)
          |
          |{
          |  derive[Wrap(Nat, natEq)].ok
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool.true")
  }

  test("universe-polymorphic parameterized instance derives at concrete Type") {
    val p =
      """
        |inductive BenchUnit : Type
        | | unit : BenchUnit
        |
        |struct Dep (A: Sort($u0)) : Sort(Level.max(Level.one, u0))
        | | mk {A: Sort($u0)} (val: BenchUnit) : Dep(A)
        |
        |struct TC (A: Sort($u0)) : Sort(Level.max(Level.one, u0))
        | | mk {A: Sort($u0)} (val: BenchUnit) : TC(A)
        |
        |inductive Target : Type
        | | mk : Target
        |
        |def instance depTarget : Dep(Target) := Dep.mk(Target, BenchUnit.unit)
        |
        |def instance tcInst [dep: Dep($A)]: TC(A) := TC.mk(A, BenchUnit.unit)
        |
        |{
        |  derive[TC(Target)]
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "TC.mk")
  }

  test("local instance binder participates in derive inside its function body") {
    val p =
      prelude +
        """
          |def natEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |
          |inline def useBinder (A: Type)[eqA: DecEq(A)]: DecEq(A) := derive[DecEq(A)]
          |
          |{
          |  useBinder(Nat, natEq)
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "DecEq.mk")
  }

  test("plain explicit binder is not registered for derive inside its function body") {
    val p =
      prelude +
        """
          |def natEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |
          |inline def usePlainBinder (A: Type)(eqA: DecEq(A)): DecEq(A) := derive[DecEq(A)]
          |
          |{
          |  usePlainBinder(Nat, natEq)
          |}
          |""".stripMargin

    intercept[NoInstanceFound] {
      typecheckProgram(p)
    }
  }

  test("local parameterized instance may close over local type") {
    val p =
      prelude +
        """
          |struct Box (A: Type) : Type
          | | mk {A: Type} : Box(A)
          |
          |def instance natEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |
          |{
          |  let A : Type := Nat
          |  let instance boxInst : [eqA: DecEq(A)] -> Box(A) := fun [eqA: DecEq(A)]: Box(A) => Box.mk(A)
          |  derive[Box(A)]
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Box.mk")
  }

  test("let instance participates in derive") {
    val p =
      prelude +
        """
          |{
          |  let instance localEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |  derive[DecEq(Nat)]
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "DecEq.mk")
  }

  test("ordinary let is not searchable") {
    val p =
      prelude +
        """
          |{
          |  let localEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |  derive[DecEq(Nat)]
          |}
          |""".stripMargin

    intercept[NoInstanceFound] {
      typecheckProgram(p)
    }
  }

  test("local instance has lexical priority over global instance") {
    val p =
      prelude +
        """
          |def instance globalEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |
          |{
          |  let instance localEq : DecEq(Nat) := DecEq.mk(Nat, Bool.false)
          |  derive[DecEq(Nat)].ok
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool.false")
  }

  test("ordinary local binding does not suppress same-named global instance") {
    val p =
      prelude +
        """
          |def instance natEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |
          |{
          |  let natEq : Bool := Bool.false
          |  derive[DecEq(Nat)].ok
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool.true")
  }

  test("newest local instance wins for closed goal") {
    val p =
      prelude +
        """
          |{
          |  let instance localEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |  let instance localEq : DecEq(Nat) := DecEq.mk(Nat, Bool.false)
          |  derive[DecEq(Nat)].ok
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool.false")
  }

  test("first successful global instance wins for closed goal") {
    val p =
      prelude +
        """
          |def instance natEq1 : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |def instance natEq2 : DecEq(Nat) := DecEq.mk(Nat, Bool.false)
          |
          |{
          |  derive[DecEq(Nat)].ok
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool.true")
  }

  test("unsolved dependency fails that candidate only") {
    val p =
      prelude +
        """
          |struct TC (A: Type) : Type
          | | mk {A: Type} (ok: Bool) : TC(A)
          |
          |struct Need (A: Type) : Type
          | | mk {A: Type} : Need(A)
          |
          |def instance bad [need: Need($A)]: TC(A) := TC.mk(A, Bool.false)
          |def instance good : TC(Nat) := TC.mk(Nat, Bool.true)
          |
          |{
          |  derive[TC(Nat)].ok
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool.true")
  }

  test("instance candidate accepts cumulative capture") {
    val p =
      prelude +
        """
          |struct Need (A: Sort(Level.one)) : Sort(Level.one)
          | | mk {A: Sort(Level.one)} : Need(A)
          |
          |struct TC (A: Sort(Level.one)) : Sort(Level.one)
          | | mk {A: Sort(Level.one)} (ok: Bool) : TC(A)
          |
          |def instance needNat : Need(Nat) := Need.mk(Nat)
          |def instance high [need: Need($A)]: TC(A) := TC.mk(A, Bool.true)
          |
          |{
          |  derive[TC(Nat)].ok
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool.true")
  }

  test("closed goal accepts first candidate after recursively choosing first dependency") {
    val p =
      prelude +
        """
          |struct WantEq : Type
          | | mk (ok: Bool) : WantEq
          |
          |def instance natEq1 : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |def instance natEq2 : DecEq(Nat) := DecEq.mk(Nat, Bool.false)
          |
          |def instance badWant [eqA: DecEq(Nat)]: WantEq := WantEq.mk(Bool.false)
          |def instance goodWant : WantEq := WantEq.mk(Bool.true)
          |
          |{
          |  derive[WantEq].ok
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool.false")
  }

  test("cyclic recursive dependency only fails that candidate branch") {
    val p =
      prelude +
        """
          |struct WantEq : Type
          | | mk (ok: Bool) : WantEq
          |
          |def instance loopEq [eqA: DecEq(Nat)]: DecEq(Nat) := eqA
          |
          |def instance badWant [eqA: DecEq(Nat)]: WantEq := WantEq.mk(Bool.false)
          |def instance goodWant : WantEq := WantEq.mk(Bool.true)
          |
          |{
          |  derive[WantEq].ok
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool.true")
  }

  test("cyclic instance search is rejected") {
    val p =
      prelude +
        """
          |def instance loopEq [eqA: DecEq(Nat)]: DecEq(Nat) := eqA
          |
          |{
          |  derive[DecEq(Nat)]
          |}
          |""".stripMargin

    intercept[CyclicInstanceSearch] {
      typecheckProgram(p)
    }
  }

  test("derive fails when no matching instance exists") {
    val p =
      prelude +
        """
          |{
          |  derive[DecEq(Nat)]
          |}
          |""".stripMargin

    intercept[NoInstanceFound] {
      typecheckProgram(p)
    }
  }

  test("derive expression is typechecked like an ordinary expression") {
    val p =
      prelude +
        """
          |def instance natEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |
          |{
          |  let bad : Bool := derive[DecEq(Nat)]
          |  bad
          |}
          |""".stripMargin

    intercept[TypeMismatch] {
      typecheckProgram(p)
    }
  }

  test("derive is term syntax, not type syntax") {
    val p =
      prelude +
        """
          |def bad (x: derive[DecEq(Nat)]): Nat := Nat.zero
          |""".stripMargin

    assert(LanguageParser.parseProgram(p).isInstanceOf[Failure])
  }

  test("instance search does not refine caller equality variables") {
    val worlds = compileWorlds(
      prelude +
        """
          |def instance natEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)
          |""".stripMargin
    )
    val env = worlds.runEnv

    val a = FreshVar.freshVar("A", Value.TypeTpe)
    implicit val eqStore: EqStore = EqStore.empty.allow(DepSet(a.id))
    val aRef = CoreAst.LocalRef(env.locals.length, "A")
    val envWithA = env.putLocal(aRef, a)

    val goal = applyValue(namedValue(envWithA, "DecEq"), a)

    intercept[NoInstanceFound] {
      InstanceSearch.solve(goal, envWithA)
    }

    val eqA = Value.VConst("eqA", Value.Symbol, goal)
    val eqARef = CoreAst.LocalRef(envWithA.locals.length, "eqA")
    val eqAKey = InstanceSearch.instanceKey("eqA", eqA, eqStore)
    val envWithEqA = envWithA.putLocal(eqARef, eqA, Some(eqAKey))

    assertEquals(InstanceSearch.solve(goal, envWithEqA), eqA)
    assertEquals(eqStore.subst, Map.empty[Value.VarId, Value])
  }
}
