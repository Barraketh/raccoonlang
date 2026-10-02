package com.raccoonlang

class VecZipTest extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

  test("Indexed Vec zip") {
    val program =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec(u: Level)(A: Type { level = u}) indices (n: Peano) : Type { level = u}
        | | nil : Vec(u, A, Peano.zero)
        | | cons (n: Peano)(vec: Vec(u, A, n))(elem: A): Vec(u, A, Peano.succ(n))
        |
        |inductive Couple(u1: Level)(u2: Level)(A: Type { level = u1})(B: Type { level = u2}): Type { level = max(u1, u2) }
        | | mk (a: A)(b: B): Couple(u1, u2, A, B)
        |
        |def zip(u1: Level)(u2: Level)(A: Type { level = u1})(B: Type { level = u2})(n: Peano)(va: Vec(u1, A, n))(vb: Vec(u2, B, n)): Vec(Level.max(u1, u2), Couple(u1, u2, A, B), n) decreases structural(n) := {
        |  let R := Couple(u1, u2, A, B)
        |  match va returning Vec(Level.max(u1, u2), R, n) with
        |  | Vec.nil => Vec.nil(R)
        |  | Vec.cons x va0 a => {
        |    match vb returning Vec(Level.max(u1, u2), R, n) with
        |    | Vec.cons _ vb0 b => Vec.cons(x, zip(u1, u2, A, B, x, va0, vb0), Couple.mk(a, b))
        |  }
        |}
        |
        |{
        |  Peano.zero
        |}
        |
        |
        |""".stripMargin

    typecheckDecls(program)
  }

  test("Indexed Vec zip with implicit parameters") {
    val program =
      """
        |inductive Peano : Type
        |  | zero : Peano
        |  | succ (_: Peano) : Peano
        |
        |inductive Vec {u: Level}(A: Type { level = u}) indices (n: Peano) : Type { level = u}
        |  | nil : Vec(A, Peano.zero)
        |  | cons (n: Peano)(v: Vec(A, n))(elem: A): Vec(A, Peano.succ(n))
        |
        |inductive Couple {u1: Level}{u2: Level}(A: Type { level = u1})(B: Type { level = u2}): Type { level = max(u1, u2) }
        |  | mk (a: A)(b: B): Couple(A, B)
        |
        |def zip {u1: Level}{u2: Level}{A: Type { level = u1}}{B: Type { level = u2}}{n: Peano} (va: Vec(A, n))(vb: Vec(B, n)): Vec(Couple(A, B), n) decreases measure(n) := {
        |  let ResType := Vec(Couple(A, B), n)
        |  match va returning ResType with
        |  | Vec.nil => Vec.nil(Couple(A, B))
        |  | Vec.cons n0 va0 a => {
        |    match vb returning ResType with
        |    | Vec.cons _ vb0 b => Vec.cons(n0, zip(va0, vb0), Couple.mk(a, b))
        |  }
        |}
        |""".stripMargin

    typecheckDecls(program)
  }

}
