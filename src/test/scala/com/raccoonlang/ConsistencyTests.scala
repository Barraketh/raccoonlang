package com.raccoonlang

// See docs/kernel.md#maintained-invariants: these permanent must-reject programs probe
// claims that would undermine consistency. A red test signals unsoundness, not staleness.
// Each test targets a documented kernel invariant.
class ConsistencyTests extends munit.FunSuite with TestSupport {

  private def runTestProgram(src: String): Value = {
    runTestProgramWithEnv(src)._1
  }

  private def runTestProgramWithEnv(src: String): (Value, Env) = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        val env = core.decls.foldLeft(Prelude.test.checkedEnv) { case (current, decl) =>
          Interpreter.evalDecl(decl, current)
        }
        val body = core.body.getOrElse(fail("Program has no body"))
        val checked = TypeChecker.checkTerm(body, env)
        (checked.value, env)
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  // Quotient values provide no constructor no-confusion or injectivity (docs/kernel.md#axioms-opacity-and-quotients).
  test("Quot.mk is not disjoint: refl stays reachable for equalities between distinct representatives") {
    val err = expectTypeError[MissingCase](
      """
        |def TrivRel (a: Bool)(b: Bool): Prop := True
        |
        |def boom (p: Eq(Quot(Bool, TrivRel), Quot.mk(TrivRel, Bool.true), Quot.mk(TrivRel, Bool.false))): False := {
        |  match p returning False with
        |}
        |""".stripMargin
    )
    assertEquals(err.ctor, "Eq.refl")
  }

  // Quotient values provide no constructor no-confusion or injectivity (docs/kernel.md#axioms-opacity-and-quotients).
  test("Quot.mk is not injective: match refinement cannot derive representative equality") {
    expectTypeError[TypeMismatch](
      """
        |def TrivRel (a: Bool)(b: Bool): Prop := True
        |
        |def mkInj (x: Bool)(y: Bool)(p: Eq(Quot(Bool, TrivRel), Quot.mk(TrivRel, x), Quot.mk(TrivRel, y))): Eq(Bool, x, y) := {
        |  match p returning Eq(Bool, x, y) with
        |  | Eq.refl z => Eq.refl(x)
        |}
        |""".stripMargin
    )
  }

  // Quotient values provide no constructor no-confusion or injectivity (docs/kernel.md#axioms-opacity-and-quotients).
  test("congruence failures under opaque heads are not refutations") {
    // Eq(g(mk true), g(mk false)) is provable via congrArg over Quot.sound, so unification failing
    // on the arguments of the non-injective head g must not prune the refl case.
    val err = expectTypeError[MissingCase](
      """
        |def TrivRel (a: Bool)(b: Bool): Prop := True
        |
        |axiom g (q: Quot(Bool, TrivRel)): Nat
        |
        |def gEq : Eq(Nat, g(Quot.mk(TrivRel, Bool.true)), g(Quot.mk(TrivRel, Bool.false))) :=
        |  congrArg(Quot.sound(Bool.true, Bool.false, TrivRel, True.intro), Nat, g)
        |
        |def boom (p: Eq(Nat, g(Quot.mk(TrivRel, Bool.true)), g(Quot.mk(TrivRel, Bool.false)))): False := {
        |  match p returning False with
        |}
        |""".stripMargin
    )
    assertEquals(err.ctor, "Eq.refl")
  }

  // Opaque applications are not invertible refinement frames (docs/kernel.md#refinement-unification).
  test("match refinement negative: opaque function applications do not refine their arguments") {
    // Eq(f(x), f(y)) does not force x = y for a non-injective head: unification must not
    // link x := y beneath the opaque frame f, so the refl branch stays unrefined.
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |opaque def f (n: Peano): Peano := n
        |
        |def injF (x: Peano)(y: Peano)(h: Eq(Peano, f(x), f(y))): Eq(Peano, x, y) := {
        |  match h returning Eq(Peano, x, y) with
        |  | Eq.refl z => Eq.refl(x)
        |}
        |""".stripMargin

    interceptError[TypeMismatch] { typecheckDecls(p, Prelude.test) }
  }

  // Opaque applications are not invertible refinement frames (docs/kernel.md#refinement-unification).
  test("match refinement negative: stuck opaque-head equations keep the refl case required") {
    // The same equation is stuck, not apart: a no-cases match must not prune refl.
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive MyFalse : Prop
        |
        |opaque def f (n: Peano): Peano := n
        |
        |def boom (x: Peano)(y: Peano)(h: Eq(Peano, f(x), f(y))): MyFalse := {
        |  match h returning MyFalse with
        |}
        |""".stripMargin

    interceptError[MissingCase] { typecheckDecls(p, Prelude.test) }
  }

  // Proof constructors provide no apartness evidence (docs/kernel.md#proofs-and-elimination).
  test("Constructor apartness does not apply to proofs (irrelevance makes inl/inr proofs equal)") {
    // Eq(Or(p,p), inl hp, inr hq) is provable by proof irrelevance (getH's body), so match
    // reachability must not prune the refl case on the inl/inr constructor clash.
    val p =
      """
        |inductive False : Prop
        |
        |inductive Or (a: Prop)(b: Prop) : Prop
        | | inl (left: a) : Or(a, b)
        | | inr (right: b) : Or(a, b)
        |
        |opaque def getH {p: Prop}(hp: p)(hq: p): Eq(Or(p, p), Or.inl(p, hp), Or.inr(p, hq)) := Eq.refl(Or.inl(p, hp))
        |
        |def boom {p: Prop}(hp: p)(hq: p): False := {
        |  match getH(hp, hq) returning False with
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[MissingCase] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  // Family-head clashes do not establish apartness for propositions (docs/kernel.md#apartness).
  test("Family-head clashes are not refutations (propext can equate Prop-valued families)") {
    val p =
      """
        |inductive True : Prop
        | | intro : True
        |
        |inductive False : Prop
        |
        |inductive And (a: Prop)(b: Prop) : Prop
        | | intro (l: a)(r: b) : And(a, b)
        |
        |inductive Or (a: Prop)(b: Prop) : Prop
        | | inl (left: a) : Or(a, b)
        | | inr (right: b) : Or(a, b)
        |
        |def boomP (h: Eq(Prop, And(True, True), Or(True, True))): False := {
        |  match h returning False with
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[MissingCase] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  // `Prop` is a sort, not a proposition (docs/kernel.md#universes-and-function-types).
  test("Negative: elimination from Exists into Prop-the-sort is large elimination") {
    // Prop is a sort, not a proposition: returning Prop extracts the witness into data,
    // which proof irrelevance would then contradict.
    val p =
      """
        |inductive Exists (A: Type)(p: A -> Prop) : Prop
        | | intro (w: A)(pw: p(w)) : Exists(A, p)
        |
        |def unpackToProp (A: Type)(p: A -> Prop)(h: Exists(A, p)): Prop := {
        |  match h returning Prop with
        |  | Exists.intro w pw => p(w)
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[PropEliminationRestricted] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  // Predicates are data, not proofs (docs/kernel.md#universes-and-function-types).
  test("Negative: predicates are not proof-irrelevant") {
    // trueP and falseP have type (n: Peano) -> Prop, which lives in Type: they are data,
    // so refl does not identify them.
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |inductive True : Prop
        | | intro : True
        |
        |inductive False : Prop
        |
        |def trueP (n: Peano): Prop := True
        |def falseP (n: Peano): Prop := False
        |
        |def bad : Eq((n: Peano) -> Prop, trueP, falseP) := Eq.refl(trueP)
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[TypeMismatch] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  // Predicates remain data through congrFun and Eq.mp (docs/kernel.md#universes-and-function-types).
  test("predicates are not proof-irrelevant through congrFun and Eq.mp") {
    val src =
      """
        |def trueP (n: Nat): Prop := True
        |def falseP (n: Nat): Prop := False
        |
        |def bad : Eq((n: Nat) -> Prop, trueP, falseP) := Eq.refl(trueP)
        |
        |def boom : False := Eq.mp(congrFun(Nat, Prop, trueP, falseP, bad, Nat.zero), True.intro)
        |
        |{
        |  boom
        |}
        |""".stripMargin
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        interceptError[TypeMismatch] { Interpreter.run(core) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  // NOT a rejection yet: current refinement rules admit type-former injectivity; this is
  // intentionally retained as a consistency probe until those rules change.
  test("currently allowed: inductive family head injectivity via match refinement") {
    runProgram(
      """
        |inductive I (P: Type -> Type) : Type
        | | mk : I(P)
        |
        |def injI (P: Type -> Type)(Q: Type -> Type)(h: Eq(Type, I(P), I(Q))): Eq((T: Type) -> Type, P, Q) := {
        |  match h returning Eq((T: Type) -> Type, P, Q) with
        |  | Eq.refl z => Eq.refl(P)
        |}
        |
        |{
        |  Bool.true
        |}
        |""".stripMargin
    )
  }

  // Abel-Coquand Omega consistency probe (arXiv:1911.08174).
  test("Abel-Coquand Omega terminates because erased proof bodies never execute") {
    // Lean's proof-irrelevant K-like Eq.rec rule repeatedly unfolds acDelta(acOmega). Raccoon
    // must never inspect that proof computation. Once checked, every proof of a Pi proposition is
    // replaced by the type-directed eta-lambda, whose applications reconstruct only their result
    // proposition rather than re-entering the discarded source body.
    val result = runProgram(
      """
        |axiom acPropext (a: Prop)(b: Prop)(h: Iff(a, b)): Eq(Prop, a, b)
        |
        |def acTautext {A: Prop}{B: Prop}(a: A)(b: B): Eq(Prop, A, B) :=
        |  acPropext(A, B, Iff.intro(fun (_: A): B => b, fun (_: B): A => a))
        |
        |def ACTrue : Prop := (A: Prop) -> A -> A
        |def ACEndo : Prop := (x: ACTrue) -> ACTrue
        |def acId (x: ACTrue): ACTrue := x
        |def acDelta (z: ACTrue): ACTrue := z(ACEndo, acId)(z)
        |def acOmega (A: Prop)(a: A): A := Eq.mp(acTautext(acId, a), acDelta)
        |def acOmegaClosed : ACTrue := acDelta(acOmega)
        |
        |{
        |  acOmegaClosed
        |}
        |""".stripMargin
    )

    result match {
      case Value.VLam(_, _, Value.LamBody.ProofEta) =>
      case other                                    => fail(s"Expected the canonical proof eta-lambda, got $other")
    }
  }

  // Distinct source nodes retain distinct identities (docs/kernel.md#value-identity).
  test("separate parses give distinct local Pi identities") {
    def piProgram(domain: String, binder: String): String =
      s"""
         |inductive Peano : Type
         | | zero : Peano
         |
         |inductive Bool : Type
         | | true : Bool
         | | false : Bool
         |
         |{ ($binder: $domain) -> $domain }
         |""".stripMargin

    val natPi = runTestProgram(piProgram("Peano", "x"))
    val boolPi = runTestProgram(piProgram("Bool", "b"))

    assert(!ValueEquivalence.defEq(natPi, boolPi))
  }

  // Synthesized nodes retain distinct identities (docs/kernel.md#value-identity).
  // Eta-adaptation is the only construct that fabricates a Pi node the source did not write. Two
  // sibling adaptations checked at one caller span must still mint distinct identities, or they
  // would share a trusted ValueKey; adapting the same declared type twice must stay defEq.
  test("eta-adapted Pi siblings receive distinct identities while re-adaptations remain definitionally equal") {
    val src =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |inductive Bool : Type
        | | true : Bool
        | | false : Bool
        |
        |def id {A: Type}(a: A): A := a
        |
        |def adaptedNat : (x: Peano) -> Peano := id
        |def adaptedNatAgain : (x: Peano) -> Peano := id
        |def adaptedBool : (x: Bool) -> Bool := id
        |
        |{ Peano.zero }
        |""".stripMargin

    val (_, env) = runTestProgramWithEnv(src)
    val adaptedNat = env("adaptedNat")
    val adaptedNatAgain = env("adaptedNatAgain")
    val adaptedBool = env("adaptedBool")

    assert(!ValueEquivalence.defEq(adaptedNat.tpe, adaptedBool.tpe))
    assert(ValueEquivalence.defEq(adaptedNat.tpe, adaptedNatAgain.tpe))
  }
}
