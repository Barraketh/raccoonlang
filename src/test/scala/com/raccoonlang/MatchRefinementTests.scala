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
        |inductive Peano : Type
        | | zero : Peano
        | | succ (p: Peano) : Peano
        |
        |def symmEq (a: Peano)(b: Peano)(p: Eq(Peano, a, b)): Eq(Peano, b, a) := {
        |  match p returning Eq(Peano, b, a) with
        |  | Eq.refl x => Eq.refl(x)
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("match refinement: congSucc via wrapped scrut succeeds") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (p: Peano) : Peano
        |
        |def congSucc2 (a: Peano)(b: Peano)(p: Eq(Peano, a, b)): Eq(Peano, Peano.succ(a), Peano.succ(b)) := {
        |  match p returning Eq(Peano, Peano.succ(a), Peano.succ(b)) with
        |  | Eq.refl x => Eq.refl(Peano.succ(x))
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("match refinement negative: mismatched motive (extra succ) fails (ctor scrut)") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (p: Peano) : Peano
        |
        |def badCongCtor (a: Peano): Eq(Peano, a, Peano.succ(a)) := {
        |  match Eq.refl(a) returning Eq(Peano, a, Peano.succ(a)) with
        |  | Eq.refl x => Eq.refl(x)
        |}
        |
        |""".stripMargin

    intercept[TypeMismatch] { typecheckDecls(p) }
  }

  test("match refinement: cumulative family parameter on neutral Vec scrut succeeds") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (p: Peano) : Peano
        |
        |inductive Vec (u: Level)(A: Sort(u)) indices (n: Peano) : Sort(Level.max(Level.one, u))
        | | nil : Vec(u, A, Peano.zero)
        | | cons (n: Peano) (xs: Vec(u, A, n)) (x: A) : Vec(u, A, Peano.succ(n))
        |
        |def keepVec (n: Peano)(v: Vec(Level.one, Peano, n)): Vec(Level.one, Peano, n) := {
        |  match v returning Vec(Level.one, Peano, n) with
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
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Type
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |inductive Hidden indices (n: Peano) : Type
        | | mk {m: Peano} (x: Vec(Peano, m)) : Hidden(Peano.zero)
        |
        |def bad (w: Hidden(Peano.zero)): Vec(Peano, Peano.zero) := {
        |  match w returning Vec(Peano, Peano.zero) with
        |  | Hidden.mk m x => x
        |}
        |""".stripMargin

    intercept[TypeMismatch] { typecheckDecls(p) }
  }

}
