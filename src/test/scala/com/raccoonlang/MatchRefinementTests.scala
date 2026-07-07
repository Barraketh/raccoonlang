package com.raccoonlang

class MatchRefinementTests extends munit.FunSuite {
  private def typecheckDecls(src: String): Unit = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        Interpreter.run(core, Prelude.test)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  test("match refinement: symmEq over neutral VApp scrut succeeds") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (p: Nat) : Nat
        |
        |def symmEq (a: Nat)(b: Nat)(p: Eq(Nat, a, b)): Eq(Nat, b, a) := {
        |  match p returning Eq(Nat, b, a) with
        |  | Eq.refl x => Eq.refl(x)
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("match refinement: congSucc via wrapped scrut succeeds") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (p: Nat) : Nat
        |
        |def congSucc2 (a: Nat)(b: Nat)(p: Eq(Nat, a, b)): Eq(Nat, Nat.succ(a), Nat.succ(b)) := {
        |  match p returning Eq(Nat, Nat.succ(a), Nat.succ(b)) with
        |  | Eq.refl x => Eq.refl(Nat.succ(x))
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("match refinement negative: mismatched motive (extra succ) fails (ctor scrut)") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (p: Nat) : Nat
        |
        |def badCongCtor (a: Nat): Eq(Nat, a, Nat.succ(a)) := {
        |  match Eq.refl(a) returning Eq(Nat, a, Nat.succ(a)) with
        |  | Eq.refl x => Eq.refl(x)
        |}
        |
        |""".stripMargin

    intercept[TypeMismatch] { typecheckDecls(p) }
  }

  test("match refinement: cumulative family parameter on neutral Vec scrut succeeds") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (p: Nat) : Nat
        |
        |inductive Vec (u: Level)(A: Sort(u)) indices (n: Nat) : Sort(Level.max(Level.one, u))
        | | nil : Vec(u, A, Nat.zero)
        | | cons (n: Nat) (xs: Vec(u, A, n)) (x: A) : Vec(u, A, Nat.succ(n))
        |
        |def keepVec (n: Nat)(v: Vec(Level.one, Nat, n)): Vec(Level.one, Nat, n) := {
        |  match v returning Vec(Level.one, Nat, n) with
        |  | Vec.nil => v
        |  | Vec.cons k xs x => v
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("match refinement negative: non-family hidden binder does not refine the requested index") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Type
        | | nil : Vec(A, Nat.zero)
        | | cons {n: Nat} (tail: Vec(A, n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |inductive Hidden indices (n: Nat) : Type
        | | mk {m: Nat} (x: Vec(Nat, m)) : Hidden(Nat.zero)
        |
        |def bad (w: Hidden(Nat.zero)): Vec(Nat, Nat.zero) := {
        |  match w returning Vec(Nat, Nat.zero) with
        |  | Hidden.mk m x => x
        |}
        |""".stripMargin

    intercept[TypeMismatch] { typecheckDecls(p) }
  }

  test("match refinement negative: opaque function applications do not refine their arguments") {
    // Eq(f(x), f(y)) does not force x = y for a non-injective head: unification must not
    // link x := y beneath the opaque frame f, so the refl branch stays unrefined.
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |opaque def f (n: Nat): Nat := n
        |
        |def injF (x: Nat)(y: Nat)(h: Eq(Nat, f(x), f(y))): Eq(Nat, x, y) := {
        |  match h returning Eq(Nat, x, y) with
        |  | Eq.refl z => Eq.refl(x)
        |}
        |""".stripMargin

    intercept[TypeMismatch] { typecheckDecls(p) }
  }

  test("match refinement negative: stuck opaque-head equations keep the refl case required") {
    // The same equation is stuck, not apart: a no-cases match must not prune refl.
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive MyFalse : Prop
        |
        |opaque def f (n: Nat): Nat := n
        |
        |def boom (x: Nat)(y: Nat)(h: Eq(Nat, f(x), f(y))): MyFalse := {
        |  match h returning MyFalse with
        |}
        |""".stripMargin

    intercept[MissingCase] { typecheckDecls(p) }
  }
}
