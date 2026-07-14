package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

/** Coverage for the forced-implicit projection machinery: which positions force an implicit
  * (Pi domains/codomains, sort levels with offsets), per-constructor demotion of unforced family
  * params, and reconstruction at residual-evaluation time (the run world re-derives implicits from
  * argument values; nothing is quoted into checked syntax).
  */
class ForcedImplicitTests extends munit.FunSuite {

  private def runProgram(src: String): Value =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        try Interpreter.run(core, Prelude.test).getOrElse(fail("Program has no body"))
        catch {
          case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def typeError[T <: TypeError](src: String)(implicit ct: reflect.ClassTag[T]): T =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[T] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def ctorName(v: Value): String = v match {
    case Value.VCtor(h, _, _)                 => h.name
    case Value.ConstructorHead(n, _, _, _, _) => n
    case other                                => fail(s"Expected constructor value, got $other")
  }

  private val natDecls =
    """
      |inductive Nat : Type
      | | zero : Nat
      | | succ (_: Nat) : Nat
      |""".stripMargin

  test("Pi domain and codomain positions force implicits (compose)") {
    val p =
      natDecls +
        """
          |def compose {A: Type}{B: Type}{C: Type} (f: B -> C)(g: A -> B)(x: A): C := f(g(x))
          |
          |{
          |  compose(Nat.succ, Nat.succ, Nat.zero)
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Nat.succ")
  }

  test("dependent Pi codomains do not force; the implicit must come from elsewhere") {
    // A non-dependent codomain is a projectable position, so `ok` is legal…
    val ok =
      natDecls +
        """
          |def ok {C: Type} (f: (n: Nat) -> C): Nat := Nat.zero
          |""".stripMargin

    // …but a var-headed dependent codomain is not rigid, so `bad`'s implicit is rejected.
    val bad =
      natDecls +
        """
          |def bad {C: Nat -> Type} (f: (n: Nat) -> C(n)): Nat := Nat.zero
          |""".stripMargin

    runProgram(ok + "\n{ Nat.zero }\n")
    typeError[NonForcedImplicitParam](bad + "\n{ Nat.zero }\n")
  }

  test("sort levels with offsets force level implicits (Sort(Level.succ(u)))") {
    val p =
      natDecls +
        """
          |def idUp {u: Level} (A: Sort(Level.succ(u)))(x: A): A := x
          |
          |{
          |  idUp(Type, Nat)
          |}
          |""".stripMargin

    // Returns the type Nat itself; just verifying it checks and evaluates.
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
          |  swap(Nat, Nat, Either.inl(Nat, Nat.zero))
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
          |  Either.inl(Nat.zero)
          |}
          |""".stripMargin

    typeError[ArityMismatch](p)
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
          |def twice (b: Box(Nat)): Nat := Nat.succ(Nat.succ(unbox(b)))
          |
          |{
          |  twice(Box.mk(Nat.zero))
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Nat.succ")
  }

  test("recursive definitions reconstruct implicits at every recursive call") {
    val p =
      natDecls +
        """
          |inductive Lst {u: Level}(A: Sort(u)) : Sort(u)
          | | nil : Lst(A)
          | | cons (head: A)(tail: Lst(A)) : Lst(A)
          |
          |def len {u: Level}{A: Sort(u)} (xs: Lst(A)): Nat decreases structural(xs) := {
          |  match xs returning Nat with
          |  | Lst.nil => Nat.zero
          |  | Lst.cons head tail => Nat.succ(len(tail))
          |}
          |
          |{
          |  len(Lst.cons(Nat.zero, Lst.cons(Nat.zero, Lst.nil(Nat))))
          |}
          |""".stripMargin

    val v = runProgram(p)
    assertEquals(ctorName(v), "Nat.succ")
  }

  test("universes are not cumulative: Sort(1) does not fit a Sort(2) binder") {
    // This shape was the check/run coherence hazard when sorts were cumulative: the checker saw
    // the binder-declared Sort(2) while the run world saw Nat's own Sort(1), so `levelOf`
    // projected different levels in the two worlds. Non-cumulative sorts reject it outright.
    val p =
      natDecls +
        """
          |def levelOf {u: Level}(A: Sort(u)): Level := u
          |
          |def g (T: Sort(Level.succ(Level.one))): Level := levelOf(T)
          |
          |{
          |  g(Nat)
          |}
          |""".stripMargin

    typeError[TypeMismatch](p)
  }

  test("run-world level projection agrees with the checker through def bodies") {
    // Coherence regression: runtime binding ascribes args to binder types (Interpreter.ascribeArgs)
    // exactly like the checker's verification pass, so projection inside `g`'s body reads the same
    // type in both worlds and the checked equation `g(Nat) = Level.one` holds at runtime.
    val p =
      natDecls +
        """
          |def levelOf {u: Level}(A: Sort(u)): Level := u
          |
          |def g (T: Type): Level := levelOf(T)
          |
          |def pf : Eq(Level, g(Nat), Level.one) := Eq.refl(g(Nat))
          |
          |{
          |  g(Nat)
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
          |  S.y(S.mk(Nat.zero, Nat.succ(Nat.zero)))
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Nat.succ")
  }

  test("polymorphic functions adapt to expected Pis that keep forced implicit binders") {
    val p =
      natDecls +
        """
          |def idL {u: Level}{A: Sort(u)}(x: A): A := x
          |
          |{
          |  let f : {A: Type} -> (x: A) -> A := idL
          |  f(Nat.succ(Nat.zero))
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Nat.succ")
  }

  test("higher-order binder types close over the callee telescope during eta-adaptation") {
    val p =
      natDecls +
        """
          |def idL {u: Level}{A: Sort(u)}(x: A): A := x
          |
          |def apply1 {A: Type}(a: A)(f: (x: A) -> A): A := f(a)
          |
          |{
          |  apply1(Nat.zero, idL)
          |}
          |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Nat.zero")
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
          case t: TypeError => fail(ErrorReporter.pretty(t, Source(p)))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }
}
