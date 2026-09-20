package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

/**
 * Coverage for the forced-implicit projection machinery: which positions force an implicit (Pi domains/codomains, sort
 * levels with offsets), per-constructor demotion of unforced family params, and reconstruction at residual-evaluation
 * time (the run world re-derives implicits from argument values; nothing is quoted into checked syntax).
 */
class ForcedImplicitTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

  private val natDecls =
    """
      |inductive Peano : Type
      | | zero : Peano
      | | succ (_: Peano) : Peano
      |""".stripMargin

  test("Pi domain and codomain positions force implicits (compose)") {
    val p =
      natDecls +
        """
          |def compose {A: Type}{B: Type}{C: Type} (f: B -> C)(g: A -> B)(x: A): C := f(g(x))
          |
          |{
          |  compose(Peano.succ, Peano.succ, Peano.zero)
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Peano.succ")
  }

  test("dependent Pi codomains do not force; the implicit must come from elsewhere") {
    // A non-dependent codomain is a projectable position, so `ok` is legal…
    val ok =
      natDecls +
        """
          |def ok {C: Type} (f: (n: Peano) -> C): Peano := Peano.zero
          |""".stripMargin

    // …but a var-headed dependent codomain is not rigid, so `bad`'s implicit is rejected.
    val bad =
      natDecls +
        """
          |def bad {C: Peano -> Type} (f: (n: Peano) -> C(n)): Peano := Peano.zero
          |""".stripMargin

    runProgram(ok + "\n{ Peano.zero }\n")
    expectTypeError[NonForcedImplicitParam](bad + "\n{ Peano.zero }\n")
  }

  test("sort levels with offsets force level implicits (Sort(Level.succ(u)))") {
    val p =
      natDecls +
        """
          |def idUp {u: Level} (A: Sort(Level.succ(u)))(x: A): A := x
          |
          |{
          |  idUp(Type, Peano)
          |}
          |""".stripMargin

    // Returns the type Peano itself; just verifying it checks and evaluates.
    runProgram(p)
  }

  test("per-constructor demotion: the unforced family param is explicit, the forced one stays implicit") {
    val p =
      natDecls +
        """
          |inductive Either (A: Type)(B: Type) : Type
          | | inl (left: A) : Either(A, B)
          | | inr (right: B) : Either(A, B)
          |
          |def swap (A: Type)(B: Type)(e: Either(A, B)): Either(B, A) := {
          |  match e returning Either(B, A) with
          |  | Either.inl x => Either.inr(B, x)
          |  | Either.inr y => Either.inl(A, y)
          |}
          |
          |{
          |  swap(Peano, Peano, Either.inl(Peano, Peano.zero))
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Either.inr")
  }

  test("demoted family params cannot be omitted") {
    val p =
      natDecls +
        """
          |inductive Either (A: Type)(B: Type) : Type
          | | inl (left: A) : Either(A, B)
          | | inr (right: B) : Either(A, B)
          |
          |{
          |  Either.inl(Peano.zero)
          |}
          |""".stripMargin

    expectTypeError[ArityMismatch](p)
  }

  test("implicits are reconstructed when residuals are re-evaluated in the run world") {
    val p =
      natDecls +
        """
          |inductive Box {u: Level}(A: Sort(u)) : Sort(u)
          | | mk (a: A) : Box(A)
          |
          |def unbox {u: Level}{A: Sort(u)} (b: Box(A)): A := {
          |  match b returning A with
          |  | Box.mk a => a
          |}
          |
          |def twice (b: Box(Peano)): Peano := Peano.succ(Peano.succ(unbox(b)))
          |
          |{
          |  twice(Box.mk(Peano.zero))
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Peano.succ")
  }

  test("recursive definitions reconstruct implicits at every recursive call") {
    val p =
      natDecls +
        """
          |inductive Lst {u: Level}(A: Sort(u)) : Sort(u)
          | | nil : Lst(A)
          | | cons (head: A)(tail: Lst(A)) : Lst(A)
          |
          |def len {u: Level}{A: Sort(u)} (xs: Lst(A)): Peano decreases structural(xs) := {
          |  match xs returning Peano with
          |  | Lst.nil => Peano.zero
          |  | Lst.cons head tail => Peano.succ(len(tail))
          |}
          |
          |{
          |  len(Lst.cons(Peano.zero, Lst.cons(Peano.zero, Lst.nil(Peano))))
          |}
          |""".stripMargin

    val v = runProgram(p)
    assertEquals(ctorName(v), "Peano.succ")
  }

  test("universes are not cumulative: Sort(1) does not fit a Sort(2) binder") {
    // This shape was the check/run coherence hazard when sorts were cumulative: the checker saw
    // the binder-declared Sort(2) while the run world saw Peano's own Sort(1), so `levelOf`
    // projected different levels in the two worlds. Non-cumulative sorts reject it outright.
    val p =
      natDecls +
        """
          |def levelOf {u: Level}(A: Sort(u)): Level := u
          |
          |def g (T: Sort(Level.succ(Level.one))): Level := levelOf(T)
          |
          |{
          |  g(Peano)
          |}
          |""".stripMargin

    expectTypeError[TypeMismatch](p)
  }

  test("run-world level projection agrees with the checker through def bodies") {
    // Coherence regression: runtime binding ascribes args to binder types (Interpreter.ascribeArgs)
    // exactly like the checker's verification pass, so projection inside `g`'s body reads the same
    // type in both worlds and the checked equation `g(Peano) = Level.one` holds at runtime.
    val p =
      natDecls +
        """
          |def levelOf {u: Level}(A: Sort(u)): Level := u
          |
          |def g (T: Type): Level := levelOf(T)
          |
          |def pf : Eq(Level, g(Peano), Level.one) := Eq.refl(g(Peano))
          |
          |{
          |  g(Peano)
          |}
          |""".stripMargin

    runProgram(p) match {
      case l: Value.Level => assertEquals(l, Value.Level.const(1))
      case other          => fail(s"Expected a level, got $other")
    }
  }

  test("generated selectors work for structs with implicit non-Level family params") {
    val p =
      natDecls +
        """
          |struct S {A: Type}(x: A) : Type
          | | mk (y: A) : S(x)
          |
          |{
          |  S.y(S.mk(Peano.zero, Peano.succ(Peano.zero)))
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Peano.succ")
  }

  test("polymorphic functions adapt to expected Pis that keep forced implicit binders") {
    val p =
      natDecls +
        """
          |def idL {u: Level}{A: Sort(u)}(x: A): A := x
          |
          |{
          |  let f : {A: Type} -> (x: A) -> A := idL
          |  f(Peano.succ(Peano.zero))
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Peano.succ")
  }

  // Eta-adaptation needs the expected Pi as syntax valid in the *caller's* env, to serve as the
  // synthetic lambda's residual type. An argument's expected type is its binder's type, whose
  // syntax lives in the callee's telescope env and names the callee's own LocalRefs, so it can
  // never be placed in the caller's residual. Arguments therefore do not adapt; naming the
  // adapted function in a declared-type position first does.
  test("eta-adaptation needs declared-type syntax, which an argument position cannot supply") {
    val p =
      natDecls +
        """
          |def idL {u: Level}{A: Sort(u)}(x: A): A := x
          |
          |def apply1 {A: Type}(a: A)(f: (x: A) -> A): A := f(a)
          |
          |{
          |  apply1(Peano.zero, idL)
          |}
          |""".stripMargin

    expectTypeError[TypeMismatch](p)

    // The same adaptation goes through once the expected Pi is written down as a declared type.
    val adapted =
      natDecls +
        """
          |def idL {u: Level}{A: Sort(u)}(x: A): A := x
          |
          |def apply1 {A: Type}(a: A)(f: (x: A) -> A): A := f(a)
          |
          |def idPeano : (x: Peano) -> Peano := idL
          |
          |{
          |  apply1(Peano.zero, idPeano)
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(adapted)), "Peano.zero")
  }

  test("Quot.mk takes the relation explicitly and the carrier by projection") {
    val p =
      """
        |def R (a: Nat)(b: Nat): Prop := Eq(Nat, a, b)
        |
        |def q : Quot(Nat, R) := Quot.mk(R, Nat.zero)
        |
        |{
        |  Nat.zero
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.default)
        try Interpreter.run(core, Prelude.default)
        catch {
          case diagnostic: Diagnostic => fail(ErrorReporter.pretty(diagnostic, Source(p)))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  /**
   * Grouping is part of a function type's identity. `T` is a type-alias def unfolding to a Pi, so `f : (a: Peano) -> T`
   * is a 1-ary function returning a function, however many binders the two types spell out between them. An application
   * supplies exactly the Pi's own binders, so the second argument needs its own call.
   */
  test("a call supplies exactly the callee Pi's own binders, not its unfolded telescope") {
    val decls =
      natDecls +
        """
          |def T : Type := (b: Peano) -> Peano
          |
          |def f (a: Peano): T := {
          |  fun (b: Peano): Peano => Peano.succ(b)
          |}
          |""".stripMargin

    // One call cannot reach past `f`'s own single binder into the alias's group.
    expectTypeError[ArityMismatch](decls + """
                                             |{
                                             |  f(Peano.zero, Peano.zero)
                                             |}
                                             |""".stripMargin)

    // Applied one group at a time, which is how a nested group is reached.
    assertEquals(
      ctorName(runProgram(decls + """
                                    |{
                                    |  f(Peano.zero)(Peano.zero)
                                    |}
                                    |""".stripMargin)),
      "Peano.succ"
    )
  }

  /**
   * A telescope's extent can depend on argument *values*: `F(b)` is a Pi only for `Bool.true`. Grouping being part of
   * the type's identity makes this a static question anyway — `g : (b: Bool) -> F(b)` takes exactly one argument, and
   * whatever `F(b)` turns out to be is reached by a second call.
   */
  test("a value-dependent codomain is still reached by its own call") {
    val decls =
      natDecls +
        """
          |inductive Bool : Type
          | | false : Bool
          | | true : Bool
          |
          |def F (b: Bool): Type := {
          |  match b with
          |  | Bool.true => (n: Peano) -> Peano
          |  | Bool.false => Peano
          |}
          |
          |def g (b: Bool): F(b) := {
          |  match b returning F(b) with
          |  | Bool.true => fun (n: Peano): Peano => Peano.succ(n)
          |  | Bool.false => Peano.zero
          |}
          |""".stripMargin

    expectTypeError[ArityMismatch](decls + """
                                             |{
                                             |  g(Bool.true, Peano.zero)
                                             |}
                                             |""".stripMargin)

    assertEquals(
      ctorName(runProgram(decls + """
                                    |{
                                    |  g(Bool.true)(Peano.zero)
                                    |}
                                    |""".stripMargin)),
      "Peano.succ"
    )
  }

  /**
   * An implicit forced through a Pi *domain* works when the groupings agree: `Fn` unfolds to a 1-ary Pi and `applyTo`
   * The `A -> Peano` domain of `applyTo` is spelled the same way, so `A := Fn` projects.
   */
  test("an implicit forced through a Pi domain projects when groupings agree") {
    val p =
      natDecls +
        """
          |def Fn : Type := (p: Peano) -> Peano
          |
          |def applyTo {A: Type} (f: A -> Peano)(x: A): Peano := f(x)
          |
          |def idFn : Fn := { fun (p: Peano): Peano => p }
          |
          |{
          |  applyTo(fun (g: Fn): Peano => g(Peano.zero), idFn)
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Peano.zero")
  }

  /**
   * ...and differently grouped function types are NOT convertible. The `Eq` type argument fixes the 2-ary grouping, so
   * a value at the curried type does not fit it.
   */
  test("differently grouped function types are not convertible") {
    val p =
      natDecls +
        """
          |def uncurried (a: Peano)(b: Peano): Peano := a
          |
          |def curried (a: Peano): (b: Peano) -> Peano := {
          |  fun (b: Peano): Peano => a
          |}
          |
          |{
          |  Eq((a: Peano)(b: Peano) -> Peano, uncurried, curried)
          |}
          |""".stripMargin

    expectTypeError[TypeMismatch](p)
  }

}
