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
        .putGlobal("Level::zero", Value.Level.zero)
        .putGlobal("Level::one", Value.Level.const(1))
        .putGlobal("Prop", Value.PropTpe)

    val builtinFuncs = List[(String, CoreAst.TypeTerm, (Vector[Value], EqStore) => Value)](
      (
        "add_normalizer",
        parseHeaderType("(A: Type)(zero: A)(add: A -> A -> A): Normalizer"),
        (args, _) => Normalizers.add_normalizer(args)
      ),
      (
        "Level::succ",
        parseHeaderType("(l: Level): Level"),
        (args, eqStore) => Value.Level.succ(Interpreter.getLevel(args.head)(eqStore))
      ),
      (
        "Level::max",
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
          Value.VPi(
            env2.closeForEval(),
            Vector(Value.VBinder(lRef, ElabAst.TypePattern.Type(levelRef), levelRef, Vector.empty)),
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

  private def runProgram(src: String): Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        Interpreter.run(core).getOrElse(fail("Program has no body"))
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  private def typecheckProgram(src: String): Unit = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        Interpreter.run(core)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  private def compileWorlds(src: String): Interpreter.Worlds = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        core.decls.foldLeft(initialWorlds) { case (worlds, decl) =>
          Interpreter.evalDecl(decl, worlds)
        }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
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
      | | mk (ok: Bool) : Eq(A)
      |
      |""".stripMargin

  test("def instance supplies derived parameter") {
    val p =
      prelude +
        """
          |def instance natEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |
          |inline def useEq (A: Type)[eqA: Eq(A)]: Eq(A) := eqA
          |
          |{
          |  useEq(Nat)
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Eq::mk")
  }

  test("checked term carries derived argument so runtime evaluation does not search") {
    val worlds = compileWorlds(
      prelude +
        """
          |def instance natEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |
          |inline def useEq (A: Type)[eqA: Eq(A)]: Eq(A) := eqA
          |""".stripMargin
    )

    val body = LanguageParser.parseProgram("{ useEq(Nat) }") match {
      case Success(program, _, _) => Elaborator.elab(program).body.getOrElse(fail("Program has no body"))
      case err: Failure           => fail(s"Failed to parse: $err")
    }
    implicit val eqStore: EqStore = EqStore.empty
    implicit val normalizers: NormalizerMap = NormalizerMap.empty

    val checked = TypeChecker.check(body, worlds.checkEnv)
    val runEnvWithoutSearch = worlds.runEnv.copy(globalInstances = InstanceRegistry.empty)

    assertEquals(ctorName(Interpreter.evalTerm(checked.term, runEnvWithoutSearch)), "Eq::mk")
  }

  test("type-position application carries derived argument into runtime type evaluation") {
    val p =
      prelude +
        """
          |def instance natEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |
          |inline def NeedsEqType (A: Type)[eqA: Eq(A)]: Type := A
          |inline def id (A: Type)(x: A): A := x
          |
          |{
          |  let x : NeedsEqType(Nat) := Nat::zero
          |  id(NeedsEqType(Nat), x)
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Nat::zero")
  }

  test("Type pattern") {
    val p = prelude +
      """
        |def instance natEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
        |
        |inline def NeedsEqType (A: Type)[eqA: Eq(A)]: Type := A
        |
        |def idNeeds (x: NeedsEqType(Nat)): NeedsEqType(Nat) := x
        |""".stripMargin

    typecheckProgram(p)
  }

  test("top-level declared type carries derived argument into runtime ascription") {
    val p =
      prelude +
        """
          |def instance natEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |
          |inline def NeedsEqType (A: Type)[eqA: Eq(A)]: Type := A
          |
          |def top : NeedsEqType(Nat) := Nat::zero
          |
          |{
          |  top
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Nat::zero")
  }

  test("parameterized instance recursively derives dependencies") {
    val p =
      prelude +
        """
          |inductive List (A: Type) : Type
          | | nil : List(A)
          |
          |def instance natEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |
          |def instance listEq [ea: Eq($A)]: Eq(List(A)) := Eq::mk(List(A), Bool::true)
          |
          |inline def useListEq [eqA: Eq(List(Nat))]: Eq(List(Nat)) := eqA
          |
          |{
          |  useListEq()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Eq::mk")
  }

  test("direct call rejects captured derived binders") {
    val p =
      prelude +
        """
          |inductive List (A: Type) : Type
          | | nil : List(A)
          |
          |def instance natEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |
          |def instance listEq [ea: Eq($A)]: Eq(List(A)) := Eq::mk(List(A), Bool::true)
          |
          |{
          |  listEq()
          |}
          |""".stripMargin

    intercept[CannotDirectlyApplyCapturedDerivedBinder] {
      typecheckProgram(p)
    }
  }

  test("type-position direct application rejects captured derived binders") {
    val p =
      prelude +
        """
          |def instance natEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |
          |inline def CapturedType (A: Type)[eqB: Eq($B)]: Type := A
          |
          |def bad (x: CapturedType(Nat)): Nat := x
          |""".stripMargin

    intercept[CannotDirectlyApplyCapturedDerivedBinder] {
      typecheckProgram(p)
    }
  }

  test("universe-polymorphic parameterized instance derives at concrete Type") {
    val p =
      """
        |inductive BenchUnit : Type
        | | unit : BenchUnit
        |
        |struct Dep (A: Sort($u0)) : Sort(u0)
        | | mk (val: BenchUnit) : Dep(A)
        |
        |struct TC (A: Sort($u0)) : Sort(u0)
        | | mk (val: BenchUnit) : TC(A)
        |
        |inductive Target : Type
        | | mk : Target
        |
        |def instance depTarget : Dep(Target) := Dep::mk(Target, BenchUnit::unit)
        |
        |def instance tcInst [dep: Dep($A)]: TC(A) := TC::mk(A, BenchUnit::unit)
        |
        |inline def useTC (A: Sort($u0))[tc: TC(A)]: TC(A) := tc
        |
        |{
        |  useTC(Target)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "TC::mk")
  }

  test("local derived dependency enables parameterized instance") {
    val p =
      """
        |inductive Unit : Type
        | | unit : Unit
        |
        |struct Carrier (u: Level)(A: Sort(u)) : Type
        | | mk : Carrier(u, A)
        |
        |struct TC (u: Level)(A: Sort(u)) : Sort(u)
        | | mk : TC(u, A)
        |
        |def instance unitCarrier : Carrier(Level::zero, Unit) := Carrier::mk(Level::zero, Unit)
        |def instance tcInst [carrier: Carrier($u, $A)]: TC(u, A) := TC::mk(u, A)
        |
        |inline def useTC (u: Level)(A: Sort(u))[tc: TC(u, A)]: TC(u, A) := tc
        |inline def poly (u: Level)(A: Sort(u))[carrier: Carrier(u, A)]: TC(u, A) := useTC(u, A)
        |
        |{
        |  poly(Level::zero, Unit)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "TC::mk")
  }

  test("complex level dependency enables parameterized instance") {
    val p =
      """
        |struct Carrier (w: Level) : Type
        | | mk : Carrier(w)
        |
        |struct TC (w: Level) : Type
        | | mk : TC(w)
        |
        |def instance carrier : Carrier(Level::max(Level::max(Level::zero, Level::one), Level::succ(Level::one))) := Carrier::mk(Level::max(Level::max(Level::zero, Level::one), Level::succ(Level::one)))
        |def instance tcInst [carrier: Carrier($w)]: TC(w) := TC::mk(w)
        |
        |inline def useTC (w: Level)[tc: TC(w)]: TC(w) := tc
        |inline def poly (u: Level)(v: Level)(A: Sort(Level::max(Level::max(u, v), Level::succ(Level::one))))[carrier: Carrier(Level::max(Level::max(u, v), Level::succ(Level::one)))]: TC(Level::max(Level::max(u, v), Level::succ(Level::one))) := useTC(Level::max(Level::max(u, v), Level::succ(Level::one)))
        |
        |{
        |  poly(Level::zero, Level::one, Sort(Level::one))
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "TC::mk")
  }

  test("instance functions reject non-derived binders") {
    val p =
      prelude +
        """
          |def instance polyEq (A: Type): Eq(A) := Eq::mk(A, Bool::true)
          |""".stripMargin

    intercept[InvalidInstance] {
      typecheckProgram(p)
    }
  }

  test("function-valued derived instance binders must themselves satisfy the instance invariant") {
    val p =
      prelude +
        """
          |struct HasFn (f: Nat -> Nat) : Type
          | | mk : HasFn(f)
          |
          |def instance hasFn [f: Nat -> Nat]: HasFn(f) := HasFn::mk(f)
          |
          |""".stripMargin

    intercept[InvalidInstance] {
      typecheckProgram(p)
    }
  }

  test("instance search quotes local function payload") {
    val p =
      prelude +
        """
          |struct HasFnValue : Type
          | | mk (f: Nat -> Nat) : HasFnValue
          |
          |inline def useHasFnValue [h: HasFnValue]: HasFnValue := h
          |
          |{
          |  let f := fun (x: Nat): Nat => x
          |  let instance h : HasFnValue := HasFnValue::mk(f)
          |  useHasFnValue()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "HasFnValue::mk")
  }

  test("instance search quotes function expression payload") {
    val p =
      prelude +
        """
          |struct HasFnValue : Type
          | | mk (f: Nat -> Nat) : HasFnValue
          |
          |inline def useHasFnValue [h: HasFnValue]: HasFnValue := h
          |
          |{
          |  let instance h : HasFnValue := HasFnValue::mk(fun (x: Nat): Nat => x)
          |  useHasFnValue()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "HasFnValue::mk")
  }

  test("explicit instance binder does not mutate caller search environment for later derive") {
    val p =
      prelude +
        """
          |def natEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |
          |inline def useBinder (A: Type)(instance eqA: Eq(A))[eqAgain: Eq(A)]: Eq(A) := eqAgain
          |
          |{
          |  useBinder(Nat, natEq)
          |}
          |""".stripMargin

    intercept[NoInstanceFound] {
      typecheckProgram(p)
    }
  }

  test("function equality rejects instance binder mismatch") {
    val p =
      prelude +
        """
          |def natEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |
          |inline def idInst (instance eqA: Eq(Nat)): Eq(Nat) := eqA
          |inline def acceptsPlain (f: (eqA: Eq(Nat)) -> Eq(Nat)): Eq(Nat) := f(natEq)
          |
          |{
          |  acceptsPlain(idInst)
          |}
          |""".stripMargin

    intercept[TypeMismatch] {
      typecheckProgram(p)
    }
  }

  test("later derived binders solve against the caller instance environment") {
    val p =
      prelude +
        """
          |struct NeedsEq (A: Type) : Type
          | | mk (eq: Eq(A)) : NeedsEq(A)
          |
          |def instance natEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |
          |def instance needsEq [eqA: Eq($A)]: NeedsEq(A) := NeedsEq::mk(A, eqA)
          |
          |inline def useBoth [eqA: Eq(Nat)][needs: NeedsEq(Nat)]: NeedsEq(Nat) := needs
          |
          |{
          |  useBoth()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "NeedsEq::mk")
  }

  test("instance search quotes freshened struct instance binder") {
    val p =
      prelude +
        """
          |inline def useEq [eqA: Eq(Nat)]: Eq(Nat) := eqA
          |
          |inline def shadow [eqA: Eq(Nat)]: Eq(Nat) := (fun (eqA: Eq(Nat)) : Eq(Nat) => useEq())(eqA)
          |
          |{
          |  let instance localEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |  shadow()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Eq::mk")
  }

  test("plain inner binder does not suppress outer instance binder during derive") {
    val p =
      """
          |inductive TC : Type
          | | mk : TC
          |
          |inline def useTC [tc: TC]: TC := tc
          |
          |inline def shadow [tc: TC]: TC := (fun (tc: TC) : TC => useTC())(tc)
          |
          |{
          |  let instance localTC : TC := TC::mk
          |  shadow()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "TC::mk")
  }

  test("let instance participates in derive") {
    val p =
      prelude +
        """
          |inline def useEq (A: Type)[eqA: Eq(A)]: Eq(A) := eqA
          |
          |{
          |  let instance localEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |  useEq(Nat)
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Eq::mk")
  }

  test("local instance has lexical priority over global instance") {
    val p =
      prelude +
        """
          |def instance globalEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |
          |inline def useEq [eqA: Eq(Nat)]: Bool := eqA.ok
          |
          |{
          |  let instance localEq : Eq(Nat) := Eq::mk(Nat, Bool::false)
          |  useEq()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool::false")
  }

  test("global ambiguity is ignored when a local unique success exists") {
    val p =
      prelude +
        """
          |def instance globalEq1 : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |def instance globalEq2 : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |
          |inline def useEq [eqA: Eq(Nat)]: Bool := eqA.ok
          |
          |{
          |  let instance localEq : Eq(Nat) := Eq::mk(Nat, Bool::false)
          |  useEq()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool::false")
  }

  test("local unique success ignores cyclic globals") {
    val p =
      prelude +
        """
          |def instance loopEq [eqA: Eq(Nat)]: Eq(Nat) := eqA
          |
          |inline def useEq [eqA: Eq(Nat)]: Bool := eqA.ok
          |
          |{
          |  let instance localEq : Eq(Nat) := Eq::mk(Nat, Bool::false)
          |  useEq()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool::false")
  }

  test("ordinary let is not searchable") {
    val p =
      prelude +
        """
          |inline def useEq (A: Type)[eqA: Eq(A)]: Eq(A) := eqA
          |
          |{
          |  let localEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |  useEq(Nat)
          |}
          |""".stripMargin

    intercept[NoInstanceFound] {
      typecheckProgram(p)
    }
  }

  test("ordinary local binding does not suppress same-named global instance") {
    val p =
      prelude +
        """
          |def instance natEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |
          |inline def useEq [eqA: Eq(Nat)]: Bool := eqA.ok
          |
          |{
          |  let natEq : Bool := Bool::false
          |  useEq()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool::true")
  }

  test("newest local instance wins for closed goal") {
    val p =
      prelude +
        """
          |inline def useEq [eqA: Eq(Nat)]: Bool := eqA.ok
          |
          |{
          |  let instance localEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |  let instance localEq : Eq(Nat) := Eq::mk(Nat, Bool::false)
          |  useEq()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool::false")
  }

  test("first successful local instance wins before globals for closed goal") {
    val p =
      prelude +
        """
          |def instance globalEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |
          |inline def useEq [eqA: Eq(Nat)]: Bool := eqA.ok
          |
          |{
          |  let instance localEq1 : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |  let instance localEq2 : Eq(Nat) := Eq::mk(Nat, Bool::false)
          |  useEq()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool::false")
  }

  test("first successful global instance wins for closed goal") {
    val p =
      prelude +
        """
          |def instance natEq1 : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |def instance natEq2 : Eq(Nat) := Eq::mk(Nat, Bool::false)
          |
          |inline def useEq [eqA: Eq(Nat)]: Bool := eqA.ok
          |
          |{
          |  useEq()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool::true")
  }

  test("semantically closed local alias keeps closed-goal priority semantics") {
    val p =
      prelude +
        """
          |def instance natEq1 : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |def instance natEq2 : Eq(Nat) := Eq::mk(Nat, Bool::false)
          |
          |inline def useEq (A: Type)[eqA: Eq(A)]: Bool := eqA.ok
          |
          |{
          |  let A : Type := Nat
          |  useEq(A)
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool::true")
  }

  test("unsolved derived dependency fails that candidate only") {
    val p =
      prelude +
        """
          |struct TC (A: Type) : Type
          | | mk (ok: Bool) : TC(A)
          |
          |struct Need (A: Type) : Type
          | | mk : Need(A)
          |
          |def instance bad [need: Need($A)]: TC(A) := TC::mk(A, Bool::false)
          |def instance good : TC(Nat) := TC::mk(Nat, Bool::true)
          |
          |inline def useTC [tc: TC(Nat)]: TC(Nat) := tc
          |
          |{
          |  useTC()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "TC::mk")
  }

  test("derived instance candidate accepts cumulative capture") {
    val p =
      prelude +
        """
          |struct Need (A: Sort(Level::one)) : Sort(Level::one)
          | | mk : Need(A)
          |
          |struct TC (A: Sort(Level::one)) : Sort(Level::one)
          | | mk (ok: Bool) : TC(A)
          |
          |def instance needNat : Need(Nat) := Need::mk(Nat)
          |def instance high [need: Need($A)]: TC(A) := TC::mk(A, Bool::true)
          |
          |inline def useTC [tc: TC(Nat)]: TC(Nat) := tc
          |
          |{
          |  useTC()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "TC::mk")
  }

  test("closed goal accepts first candidate after recursively choosing first dependency") {
    val p =
      prelude +
        """
          |struct WantEq : Type
          | | mk (ok: Bool) : WantEq
          |
          |def instance natEq1 : Eq(Nat) := Eq::mk(Nat, Bool::true)
          |def instance natEq2 : Eq(Nat) := Eq::mk(Nat, Bool::false)
          |
          |def instance badWant [eqA: Eq(Nat)]: WantEq := WantEq::mk(Bool::false)
          |def instance goodWant : WantEq := WantEq::mk(Bool::true)
          |
          |inline def useWant [want: WantEq]: Bool := want.ok
          |
          |{
          |  useWant()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool::false")
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
          |def instance badWant [eqA: Eq(Nat)]: WantEq := WantEq::mk(Bool::false)
          |def instance goodWant : WantEq := WantEq::mk(Bool::true)
          |
          |inline def useWant [want: WantEq]: Bool := want.ok
          |
          |{
          |  useWant()
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bool::true")
  }

  test("cyclic instance search is rejected") {
    val p =
      prelude +
        """
          |def instance loopEq [eqA: Eq(Nat)]: Eq(Nat) := eqA
          |
          |inline def useEq [eqA: Eq(Nat)]: Eq(Nat) := eqA
          |
          |{
          |  useEq()
          |}
          |""".stripMargin

    intercept[CyclicInstanceSearch] {
      typecheckProgram(p)
    }
  }

  test("instance search does not refine caller equality variables") {
    val worlds = compileWorlds(
      prelude +
        """
          |def instance natEq : Eq(Nat) := Eq::mk(Nat, Bool::true)
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

    val eqA = Value.VConst("eqA", Symbol, goal)
    val eqARef = CoreAst.LocalRef(envWithA.locals.length, "eqA")
    val eqAKey = InstanceSearch.instanceKey("eqA", eqA, eqStore)
    val envWithEqA = envWithA.putLocal(eqARef, eqA, Some(eqAKey))

    assertEquals(InstanceSearch.solve(goal, envWithEqA).value, eqA)
    assertEquals(eqStore.subst, Map.empty[Value.VarId, Value])
  }

  test("derived parameter syntax parses in the middle of a header") {
    LanguageParser.parseFuncHeader("(a: A)[b: B](c: C): D") match {
      case Success(header, _, _) =>
        assertEquals(header.params(1).isDerived, true)
        assertEquals(header.params(1).isInstance, true)
      case err: Failure => fail(s"Failed to parse header: $err")
    }

    val src =
      """
        |inductive A : Type
        | | mk : A
        |
        |inductive B : Type
        | | mk : B
        |
        |inductive C : Type
        | | mk : C
        |
        |inductive D : Type
        | | mk : D
        |
        |def foo(a: A)[b: B](c: C): D := D::mk
        |""".stripMargin

    typecheckProgram(src)
  }

  test("derived binder without instance registration is rejected at construction") {
    val span = Span(0, 1)
    val ty = SurfaceAst.Term.Ident("A", span)

    intercept[IllegalArgumentException] {
      SurfaceAst.Binder("x", ty, span, isDerived = true)
    }
    intercept[IllegalArgumentException] {
      CoreAst.Binder(CoreAst.LocalRef(0, "x"), CoreAst.TypePattern.Type(CoreAst.Term.GlobalRef("A", span)), span, isDerived = true)
    }
    intercept[IllegalArgumentException] {
      val ty = ElabAst.Term.GlobalRef("A", span)
      Value.VBinder(CoreAst.LocalRef(0, "x"), ElabAst.TypePattern.Type(ty), ty, Vector.empty, isDerived = true)
    }
  }
}
