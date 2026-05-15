package com.raccoonlang

class TypeClassTests extends munit.FunSuite {
  private def parseHeaderType(src: String): CoreAst.TypeTerm =
    LanguageParser.parseFuncHeader(src) match {
      case Success(header, _, _) => Elaborator.getType(header)
      case err: Failure          => fail(s"Failed to parse header: $err, ${src.substring(err.curIdx)}")
    }

  private def initialWorlds: Interpreter.Worlds = {
    val baseEnv =
      TypecheckEnv.empty
        .putGlobal("Type", Value.VSort(Value.Level.zero))
        .putGlobal("Normalizer", Value.NormalizerType)
        .putGlobal("Level", Value.LevelTpe)
        .putGlobal("Level.zero", Value.Level.zero)
        .putGlobal("Level.one", Value.Level.const(1))
        .putGlobal("Prop", Value.PropTpe)

    val builtinFuncs = List[(String, CoreAst.TypeTerm, (Vector[Value], EqStore) => Value)](
      (
        "add_normalizer",
        parseHeaderType("(A: Type)(zero: A)(add: A -> A -> A): Normalizer"),
        (args, _) => Normalizers.add_normalizer(args)
      ),
      (
        "Level.succ",
        parseHeaderType("(l: Level): Level"),
        (args, eqStore) => Value.Level.succ(Interpreter.getLevel(args.head)(eqStore))
      ),
      (
        "Level.max",
        parseHeaderType("(l1: Level)(l2: Level): Level"),
        (args, eqStore) => Value.Level.max(args.map(l => Interpreter.getLevel(l)(eqStore)))
      )
    )

    val env2 = builtinFuncs.foldLeft(baseEnv) { case (curEnv, (name, tpe, lam)) =>
      val tpeV = TypeChecker.evalTypeTerm(tpe, curEnv)(EqStore.empty, NormalizerMap.empty)
      tpeV match {
        case pi: Value.VPi =>
          curEnv.putGlobal(name, Value.VLam(pi, Value.ValueId.Const(name), isStable = true, Value.LamBody.Native(lam)))
        case _ => curEnv
      }
    }

    val nextEnv = env2.putGlobal(
      "Sort",
      Value.VLam(
        {
          val lRef = CoreAst.LocalRef(0, "l")
          val levelRef = ElabAst.Term.GlobalRef("Level", Span(0, 0))
          val levelPattern = ElabAst.TypePattern.Type(levelRef)
          Value.VPi(
            env2.closeForEval(),
            Vector(
              Value.VBinder(
                lRef,
                ElabAst.BinderType.TypePattern(levelPattern, levelPattern.span),
                levelRef,
                Vector.empty
              )
            ),
            (env, eqStore) => {
              val l = Interpreter.getLevel(env(lRef))(eqStore)
              Value.VSort(Value.Level.succ(l))
            },
            DepSet.empty,
            Value.ValueId.Const("Sort"),
            Value.VSort(Value.Level.zero)
          )
        },
        Value.ValueId.Const("Sort"),
        true,
        Value.LamBody.Native((args, eqStore) => {
          val l = Interpreter.getLevel(args(0))(eqStore)
          Value.VSort(l)
        })
      )
    )

    Interpreter.Worlds(nextEnv, nextEnv)
  }

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
    parseProgram(src).decls.foldLeft(initialWorlds) { case (worlds, decl) =>
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
      |struct Eq (A: Type) : Type
      | | mk {A: Type} (ok: Bool) : Eq(A)
      |
      |""".stripMargin

  test("derive parses to CoreAst only and checks to the resolved term") {
    val worlds = compileWorlds(
      prelude +
        """
          |def instance natEq : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |""".stripMargin
    )

    val body = parseProgram(
      prelude +
        """
          |def instance natEq : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |
          |derive[Eq(Nat)]
          |""".stripMargin
    ).body.getOrElse(fail("Program has no body"))
    assert(body.isInstanceOf[CoreAst.Term.Derive])

    implicit val eqStore: EqStore = EqStore.empty
    implicit val normalizers: NormalizerMap = NormalizerMap.empty
    val checked = TypeChecker.check(body, worlds.checkEnv)

    checked.term match {
      case ElabAst.Term.GlobalRef("natEq", _) =>
      case other                              => fail(s"Expected resolved natEq term, got $other")
    }
  }

  test("def instance is found by explicit derive expression") {
    val p =
      prelude +
        """
          |def instance natEq : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |
          |inline def useEq (A: Type)[eqA: Eq(A)]: Eq(A) := eqA
          |
          |{
          |  useEq(Nat, derive[Eq(Nat)])
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Eq.mk")
  }

  test("checked term carries resolved instance result so runtime evaluation does not search") {
    val worlds = compileWorlds(
      prelude +
        """
          |def instance natEq : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |
          |inline def useEq (A: Type)[eqA: Eq(A)]: Eq(A) := eqA
          |""".stripMargin
    )

    val body = parseProgram(
      prelude +
        """
          |def instance natEq : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |
          |inline def useEq (A: Type)[eqA: Eq(A)]: Eq(A) := eqA
          |
          |{ useEq(Nat, derive[Eq(Nat)]) }
          |""".stripMargin
    ).body.getOrElse(fail("Program has no body"))
    implicit val eqStore: EqStore = EqStore.empty
    implicit val normalizers: NormalizerMap = NormalizerMap.empty

    val checked = TypeChecker.check(body, worlds.checkEnv)
    val runEnvWithoutSearch = worlds.runEnv.copy(globalInstances = InstanceRegistry.empty)

    assertEquals(ctorName(Interpreter.evalTerm(checked.term, runEnvWithoutSearch)), "Eq.mk")
  }

  test("parameterized instance recursively derives dependencies") {
    val p =
      prelude +
        """
          |inductive List (A: Type) : Type
          | | nil {A: Type} : List(A)
          |
          |def instance natEq : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |
          |def instance listEq [ea: Eq($A)]: Eq(List(A)) := Eq.mk(List(A), Bool.true)
          |
          |{
          |  derive[Eq(List(Nat))]
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Eq.mk")
  }

  test("universe-polymorphic parameterized instance derives at concrete Type") {
    val p =
      """
        |inductive BenchUnit : Type
        | | unit : BenchUnit
        |
        |struct Dep (A: Sort($u0)) : Sort(u0)
        | | mk {A: Sort($u0)} (val: BenchUnit) : Dep(A)
        |
        |struct TC (A: Sort($u0)) : Sort(u0)
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
          |def natEq : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |
          |inline def useBinder (A: Type)[eqA: Eq(A)]: Eq(A) := derive[Eq(A)]
          |
          |{
          |  useBinder(Nat, natEq)
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Eq.mk")
  }

  test("plain explicit binder is not registered for derive inside its function body") {
    val p =
      prelude +
        """
          |def natEq : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |
          |inline def usePlainBinder (A: Type)(eqA: Eq(A)): Eq(A) := derive[Eq(A)]
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
          |def instance natEq : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |
          |{
          |  let A : Type := Nat
          |  let instance boxInst : [eqA: Eq(A)] -> Box(A) := fun [eqA: Eq(A)]: Box(A) => Box.mk(A)
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
          |  let instance localEq : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |  derive[Eq(Nat)]
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Eq.mk")
  }

  test("ordinary let is not searchable") {
    val p =
      prelude +
        """
          |{
          |  let localEq : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |  derive[Eq(Nat)]
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
          |def instance globalEq : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |
          |{
          |  let instance localEq : Eq(Nat) := Eq.mk(Nat, Bool.false)
          |  derive[Eq(Nat)].ok
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool.false")
  }

  test("ordinary local binding does not suppress same-named global instance") {
    val p =
      prelude +
        """
          |def instance natEq : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |
          |{
          |  let natEq : Bool := Bool.false
          |  derive[Eq(Nat)].ok
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool.true")
  }

  test("newest local instance wins for closed goal") {
    val p =
      prelude +
        """
          |{
          |  let instance localEq : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |  let instance localEq : Eq(Nat) := Eq.mk(Nat, Bool.false)
          |  derive[Eq(Nat)].ok
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool.false")
  }

  test("first successful global instance wins for closed goal") {
    val p =
      prelude +
        """
          |def instance natEq1 : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |def instance natEq2 : Eq(Nat) := Eq.mk(Nat, Bool.false)
          |
          |{
          |  derive[Eq(Nat)].ok
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
          |def instance natEq1 : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |def instance natEq2 : Eq(Nat) := Eq.mk(Nat, Bool.false)
          |
          |def instance badWant [eqA: Eq(Nat)]: WantEq := WantEq.mk(Bool.false)
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
          |def instance loopEq [eqA: Eq(Nat)]: Eq(Nat) := eqA
          |
          |def instance badWant [eqA: Eq(Nat)]: WantEq := WantEq.mk(Bool.false)
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
          |def instance loopEq [eqA: Eq(Nat)]: Eq(Nat) := eqA
          |
          |{
          |  derive[Eq(Nat)]
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
          |  derive[Eq(Nat)]
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
          |def instance natEq : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |
          |{
          |  let bad : Bool := derive[Eq(Nat)]
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
          |def bad (x: derive[Eq(Nat)]): Nat := Nat.zero
          |""".stripMargin

    assert(LanguageParser.parseProgram(p).isInstanceOf[Failure])
  }

  test("instance search does not refine caller equality variables") {
    val worlds = compileWorlds(
      prelude +
        """
          |def instance natEq : Eq(Nat) := Eq.mk(Nat, Bool.true)
          |""".stripMargin
    )
    val env = worlds.runEnv

    val a = FreshVar.freshVar("A", Value.VSort(Value.Level.zero))
    val aRef = CoreAst.LocalRef(env.locals.length, "A")
    val envWithA = env.putLocal(aRef, a)

    implicit val eqStore: EqStore = EqStore.empty.allow(DepSet(a.id))
    implicit val normalizers: NormalizerMap = NormalizerMap.empty

    val goal = applyValue(namedValue(envWithA, "Eq"), a)

    intercept[NoInstanceFound] {
      InstanceSearch.solve(goal, envWithA)
    }

    val eqA = Value.VConst("eqA", Value.Symbol, goal)
    val eqARef = CoreAst.LocalRef(envWithA.locals.length, "eqA")
    val eqAKey = InstanceSearch.instanceKey("eqA", eqA, eqStore)
    val envWithEqA = envWithA.putLocal(eqARef, eqA, Some(eqAKey))

    assertEquals(InstanceSearch.solve(goal, envWithEqA).value, eqA)
    assertEquals(eqStore.subst, Map.empty[Value.VarId, Value])
  }
}
