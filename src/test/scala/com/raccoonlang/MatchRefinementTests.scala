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
        | | nil {u: Level}{A: Sort(u)} : Vec(u, A, Nat.zero)
        | | cons {u: Level}{A: Sort(u)} (n: Nat) (xs: Vec(u, A, n)) (x: A) : Vec(u, A, Nat.succ(n))
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

  test("match refinement negative: non-param erased binders are rejected") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Type
        | | nil {A: Type} : Vec(A, Nat.zero)
        | | cons {A: Type} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |inductive Hidden (n: Nat) : Type
        | | mk {m: Nat} (x: Vec(Nat, m)) : Hidden(Nat.zero)
        |
        |def bad (w: Hidden(Nat.zero)): Vec(Nat, Nat.zero) := {
        |  match w returning Vec(Nat, Nat.zero) with
        |  | Hidden.mk x => x
        |}
        |""".stripMargin

    intercept[InvalidErasedConstructorBinder] { typecheckDecls(p) }
  }
}
