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

  test("sort levels with offsets force level implicits (Type { level = succ(u)})") {
    val p =
      natDecls +
        """
          |def idUp {u: Level} (A: Type { level = succ(u)})(x: A): A := x
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
          |inductive Box {u: Level}(A: Type { level = u}) : Type { level = u}
          | | mk (a: A) : Box(A)
          |
          |def unbox {u: Level}{A: Type { level = u}} (b: Box(A)): A := {
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
          |inductive Lst {u: Level}(A: Type { level = u}) : Type { level = u}
          | | nil : Lst(A)
          | | cons (head: A)(tail: Lst(A)) : Lst(A)
          |
          |def len {u: Level}{A: Type { level = u}} (xs: Lst(A)): Peano decreases structural(xs) := {
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

  test("universes are not cumulative: Type does not fit a Type { level = one} binder") {
    // This shape was the check/run coherence hazard when sorts were cumulative: the checker saw
    // the binder-declared level 2 while the run world saw Peano's own level 1, so `levelOf`
    // projected different levels in the two worlds. Non-cumulative sorts reject it outright.
    val p =
      natDecls +
        """
          |def sortOf {u: Level}(A: Type { level = u}): Type { level = succ(u)} := Type { level = u}
          |
          |def g (T: Type { level = one}): Type { level = succ(one)} := sortOf(T)
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
    // type in both worlds and the checked equation `g(Peano) = Type` holds at runtime.
    val p =
      natDecls +
        """
          |def sortOf {u: Level}(A: Type { level = u}): Type { level = succ(u)} := Type { level = u}
          |
          |def g (T: Type): Type { level = one} := sortOf(T)
          |
          |def pf : Eq(Type { level = one}, g(Peano), Type) := Eq.refl(g(Peano))
          |
          |{
          |  g(Peano)
          |}
          |""".stripMargin

    runProgram(p) match {
      case sort: Value.VSort => assert(ValueEquivalence.defEq(sort, Sorts.Type))
      case other             => fail(s"Expected a sort, got $other")
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

  // A declared Pi with fewer implicit binders than a polymorphic function does not adapt it; a
  // lambda at exactly that type, forcing its own implicit, is written instead.
  test("a polymorphic function fits only its own type, not one with fewer forced implicits") {
    def program(value: String): String =
      natDecls +
        s"""
           |def constT {A: Type}{B: Type}(x: A)(y: B): A := x
           |
           |{
           |  let f : {A: Type} -> (x: A)(y: Peano) -> A := $value
           |  f(Peano.succ(Peano.zero), Peano.zero)
           |}
           |""".stripMargin

    assertEquals(ctorName(runProgram(program("fun {A: Type}(x: A)(y: Peano): A => constT(x, y)"))), "Peano.succ")
    expectOnly[TypeMismatch](typecheckDecls(program("constT")))
  }

  // An argument is synthesized and compared with its binder type like any checked term, so a
  // polymorphic function passed bare does not fit a monomorphic parameter; a lambda does.
  test("a polymorphic function argument is not adapted to its parameter's type") {
    def program(argument: String): String =
      natDecls +
        s"""
           |def idT {A: Type}(x: A): A := x
           |
           |def apply1 {A: Type}(a: A)(f: (x: A) -> A): A := f(a)
           |
           |{
           |  apply1(Peano.zero, $argument)
           |}
           |""".stripMargin

    assertEquals(ctorName(runProgram(program("fun (x: Peano): Peano => idT(x)"))), "Peano.zero")
    expectOnly[TypeMismatch](typecheckDecls(program("idT")))
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
          case diagnostic: Diagnostic => fail(ErrorReporter.pretty(diagnostic, Source(p), None))
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
          |  match b returning Type with
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

  // The family parameters later arguments determine are implicit, so writing them is an arity error that says so.
  test("a constructor's arity error names its explicit parameters and its implicit family parameters") {
    def arityMessage(call: String)(implicit loc: munit.Location): String = {
      val structs =
        """
          |struct Cell (A: Type)(n: Peano) : Type
          | | mk (value: A)(index: Peano) : Cell(A, n)
          |struct Same (A: Type) : Type
          | | mk (value: A) : Same(A)
          |""".stripMargin
      ErrorRendering.render(expectTypeError[ArityMismatch](natDecls + structs + "{ " + call + " }"), None)
    }
    assertEquals(
      arityMessage("Cell.mk(Peano.zero, Peano.zero)"),
      "Cannot apply Cell.mk - expected 3 params (n, value, index), got 2; " +
        "family parameter A is implicit, determined by the other arguments"
    )
    assertEquals(
      arityMessage("Same.mk(Peano, Peano.zero)"),
      "Cannot apply Same.mk - expected 1 params (value), got 2; " +
        "family parameter A is implicit, determined by the other arguments"
    )
    assertEquals(arityMessage("Peano.succ()"), "Cannot apply Peano.succ - expected 1 params (_), got 0")
  }

  // A constructor with no fields takes its family's type parameter, which determines the parameters before it.
  test("a fieldless constructor's arity error names the family parameters its explicit one determines") {
    assertEquals(
      ErrorRendering.render(expectTypeError[ArityMismatch]("{ List.nil() }", Prelude.default), None),
      "Cannot apply List.nil - expected 1 params (A), got 0; " +
        "family parameters u, S are implicit, determined by the other arguments"
    )
  }

  test("a function's arity error names its explicit parameters") {
    val p = natDecls + "def pick {A: Type}(a: A)(b: A): A := a\n\n{ pick(Peano.zero) }\n"
    assertEquals(
      ErrorRendering.render(expectTypeError[ArityMismatch](p), None),
      "Cannot apply pick - expected 2 params (a, b), got 1"
    )
  }

}
