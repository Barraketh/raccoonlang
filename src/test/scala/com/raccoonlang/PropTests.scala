package com.raccoonlang

class PropTests extends munit.FunSuite {
  test("Prop is Sort 0 and Pi into Prop is impredicative") {
    val prop = TestSupport.eval("{ Prop }")
    assertEquals(prop, Value.PropTpe)
    assertEquals(prop.tpe, Value.TypeTpe)
    val pi = TestSupport.eval("{ (A: Prop) -> A }")
    assertEquals(pi.tpe, Value.PropTpe)
    val nonDependent = TestSupport.eval("inductive True : Prop\n | intro : True\n\n{ (P: Prop) -> True }")
    assertEquals(nonDependent.tpe, Value.PropTpe)
  }

  test("Pi returning the Prop sort has the exact non-cumulative universe") {
    val nonDependent = TestSupport.eval("{ (A: Type) -> Prop }")
    assertEquals(nonDependent.tpe, Value.VSort(Value.Level.const(2)))
    val dependent = TestSupport.eval("{ (A: Type) -> (x: A) -> Prop }")
    assertEquals(dependent.tpe, Value.VSort(Value.Level.const(2)))
    assert(!Value.isPropositionType(nonDependent))
  }

  test("Pi over a proof binder into data remains in Type") {
    val pi = TestSupport.eval("inductive Nat : Type\n | zero : Nat\n\n{ (P: Prop) -> Nat }")
    assertEquals(pi.tpe, Value.TypeTpe)
    assert(!Value.isPropositionType(pi))
  }

  test("proof binders typecheck") {
    TestSupport.check("def idProof (P: Prop)(p: P): P := p")
  }

  test("forced proof implicits reconstruct without a witness hole") {
    TestSupport.check(
      "inductive True : Prop\n" +
        " | intro : True\n\n" +
        "inductive Holds (P: Prop)(p: P) : Prop\n" +
        " | intro : Holds(P, p)\n\n" +
        "def choose {h: True} (e: Holds(True, h)): True := h\n\n" +
        "def chosen : True := choose(Holds.intro(True.intro))\n"
    )
  }

  test("forced Pi proof implicits use structural proposition equality") {
    TestSupport.check(
      "inductive Nat : Type\n" +
        " | zero : Nat\n\n" +
        "inductive True : Prop\n" +
        " | intro : True\n\n" +
        "inductive Holds (P: Prop)(p: P) : Prop\n" +
        " | intro : Holds(P, p)\n\n" +
        "axiom truthFn (n: Nat): True\n\n" +
        "def chooseFn {h: (x: Nat) -> True} (e: Holds((x: Nat) -> True, h)): (x: Nat) -> True := h\n\n" +
        "def chosenFn : (x: Nat) -> True := chooseFn(Holds.intro(truthFn))\n"
    )
  }

  test("unforced implicit proof parameters are rejected") {
    intercept[NonForcedImplicitParam] {
      TestSupport.check(
        "inductive True : Prop\n" +
          " | intro : True\n\n" +
          "inductive Nat : Type\n" +
          " | zero : Nat\n\n" +
          "def bad {h: True} (n: Nat): True := h\n"
      )
    }
  }

  test("predicates returning Prop remain data") {
    val predicate = TestSupport.eval("{ (A: Type) -> Prop }")
    assertEquals(predicate.tpe, Value.VSort(Value.Level.const(2)))
    assert(!Value.isPropositionType(predicate))
  }

  test("distinct predicates are not proof-irrelevant") {
    val (env, _) = TestSupport.check(
      "inductive True : Prop\n" +
        " | intro : True\n\n" +
        "inductive False : Prop\n\n" +
        "def trueP (A: Type): Prop := True\n" +
        "def falseP (A: Type): Prop := False\n"
    )
    assert(!ValueEquivalence.defEq(env("trueP"), env("falseP")))
  }

  test("proof constructors erase and are proof irrelevant") {
    val result = TestSupport.eval("""
                                    |inductive True : Prop
                                    | | intro : True
                                    |{ True.intro }
                                    |""".stripMargin)
    assert(result.isInstanceOf[Value.VProof])
    val proposition = Value.VConst("P", Value.Symbol, Value.PropTpe)
    assert(ValueEquivalence.defEq(Value.VProof(proposition), Value.VProof(proposition.copy())))
  }

  test("proof Pi lambdas use eta representation") {
    val result = TestSupport.eval("""
                                    |inductive True : Prop
                                    | | intro : True
                                    |{ fun (p: True): True => p }
                                    |""".stripMargin)
    result match {
      case Value.VLam(_, _, Value.LamBody.ProofEta) => ()
      case other =>
        fail(
          s"Expected proof eta lambda, got $other / ${other.asInstanceOf[Value.VLam].tpe.isPropValued} / ${other.tpe}"
        )
    }
  }

  test("a proof whose proposition is itself a Pi binds and applies canonically") {
    val result = TestSupport.eval(
      "inductive True : Prop\n" +
        " | intro : True\n\n" +
        "axiom proofFun : (Q: Prop) -> Q\n\n" +
        "def use (p: (Q: Prop) -> Q): True := p(True)\n\n" +
        "{ use(proofFun) }"
    )
    assert(result.isInstanceOf[Value.VProof])
  }

  test("Prop inductives with proof, data, and large-universe fields pass positivity") {
    TestSupport.check(
      "inductive False : Prop\n\n" +
        "inductive True : Prop\n" +
        " | intro : True\n\n" +
        "inductive And (P: Prop)(Q: Prop) : Prop\n" +
        " | intro (p: P)(q: Q) : And(P, Q)\n\n" +
        "inductive Exists (A: Type)(p: A -> Prop) : Prop\n" +
        " | intro (w: A)(pw: p(w)) : Exists(A, p)\n\n" +
        "inductive HasSort (u: Level) : Prop\n" +
        " | intro (A: Sort(u)) : HasSort(u)\n"
    )
  }

  test("Prop inductives retain strict positivity checks") {
    intercept[NonStrictlyPositive] {
      TestSupport.check(
        "inductive False : Prop\n\n" +
          "inductive Bad : Prop\n" +
          " | mk (f: Bad -> False) : Bad\n"
      )
    }
  }

  test("Prop elimination into Prop is allowed") {
    TestSupport.check("""
                        |inductive True : Prop
                        | | intro : True
                        |
                        |def idTrue (p: True): True := {
                        |  match p returning True with
                        |  | True.intro => True.intro
                        |}
                        |""".stripMargin)
  }

  test("large elimination requiring erased fields is rejected") {
    intercept[PropEliminationRestricted] {
      TestSupport.check("""
                          |inductive Nat : Type
                          | | zero : Nat
                          |
                          |inductive Has : Prop
                          | | intro (A: Type) : Has
                          |
                          |def bad (h: Has): Nat := {
                          |  match h returning Nat with
                          |  | Has.intro A => Nat.zero
                          |}
                          |""".stripMargin)
    }
  }

  test("large elimination from Exists is rejected before proof recovery") {
    intercept[PropEliminationRestricted] {
      TestSupport.check(
        "inductive Nat : Type\n" +
          " | zero : Nat\n\n" +
          "inductive Exists (A: Type)(p: A -> Prop) : Prop\n" +
          " | intro (w: A)(pw: p(w)) : Exists(A, p)\n\n" +
          "inductive True : Prop\n" +
          " | intro : True\n\n" +
          "def alwaysTrue (x: Nat): Prop := True\n\n" +
          "def bad (h: Exists(Nat, alwaysTrue)): Nat := {\n" +
          "  match h returning Nat with\n" +
          "  | Exists.intro w pw => Nat.zero\n" +
          "}\n"
      )
    }
  }

  test("returning the Prop sort is not a permitted large elimination motive") {
    intercept[PropEliminationRestricted] {
      TestSupport.check(
        "inductive Exists (A: Type)(p: A -> Prop) : Prop\n" +
          " | intro (w: A)(pw: p(w)) : Exists(A, p)\n\n" +
          "def bad (A: Type)(p: A -> Prop)(h: Exists(A, p)): Prop := {\n" +
          "  match h returning Prop with\n" +
          "  | Exists.intro w pw => p(w)\n" +
          "}\n"
      )
    }
  }

  test("False, fieldless True, and impossible indexed propositions eliminate to data") {
    val source =
      "inductive Nat : Type\n" +
        " | zero : Nat\n" +
        " | succ (n: Nat) : Nat\n\n" +
        "inductive False : Prop\n\n" +
        "def absurd (h: False): Nat := {\n" +
        "  match h returning Nat with\n" +
        "}\n\n" +
        "inductive True : Prop\n" +
        " | intro : True\n\n" +
        "def trueToNat (h: True): Nat := {\n" +
        "  match h returning Nat with\n" +
        "  | True.intro => Nat.zero\n" +
        "}\n\n" +
        "inductive IsZero indices (n: Nat) : Prop\n" +
        " | intro : IsZero(Nat.zero)\n\n" +
        "def impossible (n: Nat)(h: IsZero(Nat.succ(n))): Nat := {\n" +
        "  match h returning Nat with\n" +
        "}\n"
    TestSupport.check(source)
    val result = TestSupport.eval(source + "\n{ trueToNat(True.intro) }\n")
    assertEquals(PrettyPrinter.print(result), "Nat.zero()")
  }

  test("canonical proof functions discard native bodies before application") {
    val pi = TestSupport.eval("{ (P: Prop) -> P }").asInstanceOf[Value.VPi]
    val raw = Value.VLam(
      pi,
      Value.ValueId.LocalId(AstNodeId.synthetic(), Vector.empty),
      Value.LamBody.Native((_, _) => throw new AssertionError("discarded proof body executed"), Env.empty, false)
    )
    val canonical = Value.canonicalizeProof(raw)
    val proposition = Value.VConst("Q", Value.Symbol, Value.PropTpe)
    val result = Interpreter.evalApply(canonical, Vector(proposition))
    assert(result.isInstanceOf[Value.VProof])
    assertEquals(result.tpe, proposition)
  }
}
