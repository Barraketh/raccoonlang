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

  // Quotient values provide no constructor no-confusion or injectivity (docs/kernel.md#axioms-and-quotients).
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

  // Quotient values provide no constructor no-confusion or injectivity (docs/kernel.md#axioms-and-quotients).
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

  // Quotient values provide no constructor no-confusion or injectivity (docs/kernel.md#axioms-and-quotients).
  test("congruence failures under neutral non-injective heads are not refutations") {
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

  // Neutral applications are not invertible refinement frames (docs/kernel.md#refinement-unification).
  test("match refinement negative: neutral function applications do not refine their arguments") {
    // Eq(f(x), f(y)) does not force x = y for a non-injective head: unification must not
    // link x := y beneath the neutral frame f, so the refl branch stays unrefined.
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |axiom f (n: Peano): Peano
        |
        |def injF (x: Peano)(y: Peano)(h: Eq(Peano, f(x), f(y))): Eq(Peano, x, y) := {
        |  match h returning Eq(Peano, x, y) with
        |  | Eq.refl z => Eq.refl(x)
        |}
        |""".stripMargin

    interceptError[TypeMismatch] { typecheckDecls(p, Prelude.test) }
  }

  test("match refinement negative: an arbitrary function parameter does not refine its arguments") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def injF (f: (n: Peano) -> Peano)(x: Peano)(y: Peano)(h: Eq(Peano, f(x), f(y))): Eq(Peano, x, y) := {
        |  match h returning Eq(Peano, x, y) with
        |  | Eq.refl z => Eq.refl(x)
        |}
        |""".stripMargin

    interceptError[TypeMismatch] { typecheckDecls(p, Prelude.test) }
  }

  // Neutral applications are not invertible refinement frames (docs/kernel.md#refinement-unification).
  test("match refinement negative: stuck neutral-head equations keep the refl case required") {
    // The same equation is stuck, not apart: a no-cases match must not prune refl.
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive MyFalse : Prop
        |
        |axiom f (n: Peano): Peano
        |
        |def boom (x: Peano)(y: Peano)(h: Eq(Peano, f(x), f(y))): MyFalse := {
        |  match h returning MyFalse with
        |}
        |""".stripMargin

    interceptError[MissingCase] { typecheckDecls(p, Prelude.test) }
  }

  // Proof constructors provide no apartness evidence (docs/kernel.md#proofs-and-elimination).
  test("Constructor apartness does not apply to neutral proof equalities") {
    // A neutral proof of EqProof(p, inl hp, inr hq) must remain stuck at runtime; match
    // reachability must not prune the refl case on the inl/inr constructor clash.
    val p =
      """
        |inductive False : Prop
        |
        |inductive Or (a: Prop)(b: Prop) : Prop
        | | inl (left: a) : Or(a, b)
        | | inr (right: b) : Or(a, b)
        |
        |inductive EqProof (p: Prop) indices (x: Or(p, p))(y: Or(p, p)) : Prop
        | | refl (x: Or(p, p)) : EqProof(p, x, x)
        |
        |axiom getH {p: Prop}(hp: p)(hq: p): EqProof(p, Or.inl(p, hp), Or.inr(p, hq))
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

  test("the closed Russell proof cannot derive False without axioms") {
    val russell =
      """
        |def encode (F: (x: Prop) -> Prop): Prop := { Eq((x: Prop) -> Prop, F, F) }
        |
        |def inject (F: (x: Prop) -> Prop)(G: (x: Prop) -> Prop)(h: Eq(Prop, encode(F), encode(G))):
        |  Eq((x: Prop) -> Prop, F, G) := {
        |  match h returning Eq((x: Prop) -> Prop, F, G) with
        |  | Eq.refl z => Eq.refl(F)
        |}
        |
        |def member (x: Prop): (F: (p: Prop) -> Prop) -> Prop :=
        |  fun (F: (p: Prop) -> Prop): Prop => And(Eq(Prop, x, encode(F)), Not(F(x)))
        |def Russell (x: Prop): Prop := { Exists((p: Prop) -> Prop, member(x)) }
        |
        |def selfNot (r: Russell(encode(Russell))): False := {
        |  match r returning False with
        |  | Exists.intro F evidence => {
        |    match evidence returning False with
        |    | And.intro same negative => {
        |      let equal: Eq((x: Prop) -> Prop, F, Russell) := inject(F, Russell, Eq.symm(same))
        |      let atSelf: Eq(Prop, F(encode(Russell)), Russell(encode(Russell))) :=
        |        congrFun(Prop, Prop, F, Russell, equal, encode(Russell))
        |      negative(Eq.mpr(atSelf, r))
        |    }
        |  }
        |}
        |
        |def selfMember : Russell(encode(Russell)) :=
        |  Exists.intro(member(encode(Russell)), Russell, And.intro(Eq.refl(encode(Russell)), selfNot))
        |def boom : False := selfNot(selfMember)
        |
        |{ boom }
        |""".stripMargin

    expectAnyTypeError(russell)
  }

  test("heterogeneous constructor indices stay stuck across distinct data types") {
    val declarations =
      """
        |inductive Two : Type
        | | one : Two
        |
        |inductive Tagged indices (A: Type)(a: A) : Type
        | | mk : Tagged(Bool, Bool.true)
        |
        |inductive ListedTag indices (A: Type)(a: A) : Type
        | | mk : ListedTag(List(Bool), List.nil(Bool))
        |""".stripMargin

    def matching(tpe: String, cases: String): String =
      declarations +
        s"""
           |def keep (value: $tpe): Nat := {
           |  match value returning Nat with
           |$cases
           |}
           |""".stripMargin

    Vector(
      "Tagged(Two, Two.one)",
      "ListedTag(List(Two), List.cons(Two.one, List.nil(Two)))"
    ).foreach { tpe =>
      expectTypeError[MissingCase](matching(tpe, ""))
      typecheckDecls(matching(tpe, "  | .mk => 0\n"))
    }
  }

  test("constructor clashes stay apart within one family at convertible parameters") {
    typecheckDecls(
      """
        |def eliminateListClash
        |  (h: Eq(List(Bool), List.nil(Bool), List.cons(Bool.true, List.nil(Bool)))): False := {
        |  match h returning False with
        |}
        |""".stripMargin
    )
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

  // A data family may use a type-constructor parameter when its result universe is large enough.
  test("data family injectivity remains for a well-sized family parameter") {
    runProgram(
      """
        |inductive I (P: Type -> Type) : Type { level = one }
        | | mk : I(P)
        |
        |def injI (P: Type -> Type)(Q: Type -> Type)
        |  (h: Eq(Type { level = one }, I(P), I(Q))): Eq((T: Type) -> Type, P, Q) := {
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

    val propext =
      TestSupport.preludeAssuming(
        TestSupport.bundledPreludeSource,
        "axiom acPropext (a: Prop)(b: Prop)(h: Iff(a, b)): Eq(Prop, a, b)\n"
      )
    val result = runProgram(
      """
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
        |""".stripMargin,
      propext
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

  /** `source` is rejected, first with a type mismatch underlining `at`: an ordinary error, not a kernel one. */
  private def expectMismatchAt(source: String, at: String)(implicit loc: munit.Location): Unit = {
    val diagnostic = interceptDiagnostic(typecheckDecls(source))
    assert(diagnostic.error.isInstanceOf[TypeMismatch], diagnostic.error)
    assertEquals(diagnostic.span.map(span => source.substring(span.start, span.end)), Some(at))
  }

  // A key decides conversion, and a function type's key is its node identity, captures, binder count and closure
  // (docs/kernel.md#value-identity). Each program below once gave two different function types one node identity, so
  // the unifier took them for equal: the key assertion failed, and without it the program crashed at run time.
  test("a function type and its function-typed domain have distinct identities") {
    expectMismatchAt(
      """
        |def k {A: Type}(f: (A -> A) -> A) : A := f(f)
        |{ k(fun (g: Nat -> Nat): Nat => g(5)) }
        |""".stripMargin,
      "f(f)"
    )
    val domOf = "def domOf {A: Type}{B: Type}(f: A -> B)(a: A): Nat := 0\n"
    expectMismatchAt(domOf + "def bad (g: (Nat -> Nat) -> Nat): Nat := domOf(g, g)\n", "domOf(g, g)")
    expectMismatchAt(domOf + "def bad (g: ((x: Nat) -> Nat) -> Nat): Nat := domOf(g, g)\n", "domOf(g, g)")
    expectMismatchAt(domOf + "def bad (g: (List(Nat) -> Nat) -> Nat): Nat := domOf(g, g)\n", "domOf(g, g)")
    expectMismatchAt(
      """
        |def Id (X: Type): Type := X
        |def coerce {A: Type}{B: Type}(f: A -> B)(a: Id(A)): A := a
        |def bad (g: ((x: Nat) -> Nat) -> Nat): (x: Nat) -> Nat := coerce(g, g)
        |def boom : Nat := bad(fun (h: (x: Nat) -> Nat): Nat => h(5))(7)
        |{ boom }
        |""".stripMargin,
      "coerce(g, g)"
    )
    expectMismatchAt(
      """
        |def apply {A: Type}{B: Type}(f: A -> B)(a: A): B := f(a)
        |def bad (g: (Nat -> Nat) -> Nat): Nat := apply(g, g)
        |{ bad(fun (h: Nat -> Nat): Nat => h(1)) }
        |""".stripMargin,
      "apply(g, g)"
    )
  }

  test("each struct selector's type is a function type of its own") {
    val struct =
      """
        |struct P : Type
        | | mk (a: Nat) (b: Bool) : P
        |
        |""".stripMargin
    expectMismatchAt(
      struct + "def same {A: Type}(x: A)(y: A): A := y\ndef bad : P -> Nat := same(P.a, P.b)\n",
      "same(P.a, P.b)"
    )
    expectMismatchAt(
      struct + "def first {A: Type}(x: A)(y: A): A := x\ndef bad : P -> Nat := first(P.b, P.a)\n",
      "first(P.b, P.a)"
    )
    expectMismatchAt(struct + "def typeOf {A: Type}(x: A): Type := A\ndef coerced : typeOf(P.b) := P.a\n", "P.a")
  }

  // A selector's result type is its field's, with each earlier field read through its selector. So rewritten, it is a
  // different function type from the field's own, written at the same place.
  test("a selector's rewritten result type is not its field's type") {
    expectMismatchAt(
      """
        |def G {T: Type}(t: T) : Type := T
        |struct P (A: Type) indices (n: Nat) : Type
        | | mk (x: A) (f: G(x) -> Nat) : P(A, 0)
        |
        |open P
        |def wrap (v: P(Nat, 0)) : P(P(Nat, 0), 0) := mk(v, f(v))
        |""".stripMargin,
      "mk(v, f(v))"
    )
  }
}
