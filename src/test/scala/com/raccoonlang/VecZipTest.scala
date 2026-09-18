package com.raccoonlang

class VecZipTest extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.default

  test("Indexed Vec zip") {
    val program =
      """
        |inductive Vec {u: Level}(A: Sort(u)) indices (n: Nat) : Sort(Level.max(Level.one, u))
        |  | nil : Vec(A, Nat.zero)
        |  | cons (n: Nat)(v: Vec(A, n))(elem: A): Vec(A, Nat.succ(n))
        |
        |inductive Pair {u1: Level}{u2: Level}(A: Sort(u1))(B: Sort(u2)): Sort(Level.max(u1, u2))
        |  | mk (a: A)(b: B): Pair(A, B)
        |
        |def zip {u1: Level}{u2: Level}{A: Sort(u1)}{B: Sort(u2)}{n: Nat} (va: Vec(A, n))(vb: Vec(B, n)): Vec(Pair(A, B), n) decreases measure(n) := {
        |  let R := Pair(A, B)
        |  match va returning Vec(R, n) with
        |  | Vec.nil => Vec.nil(R)
        |  | Vec.cons n0 va0 a => {
        |    match vb returning Vec(R, n) with
        |    | Vec.cons _ vb0 b => Vec.cons(n0, zip(va0, vb0), Pair.mk(a, b))
        |  }
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
        |inductive Vec {u: Level}(A: Sort(u)) indices (n: Peano) : Sort(Level.max(Level.one, u))
        |  | nil : Vec(A, Peano.zero)
        |  | cons (n: Peano)(v: Vec(A, n))(elem: A): Vec(A, Peano.succ(n))
        |
        |inductive Pair {u1: Level}{u2: Level}(A: Sort(u1))(B: Sort(u2)): Sort(Level.max(u1, u2))
        |  | mk (a: A)(b: B): Pair(A, B)
        |
        |def zip {u1: Level}{u2: Level}{A: Sort(u1)}{B: Sort(u2)}{n: Peano} (va: Vec(A, n))(vb: Vec(B, n)): Vec(Pair(A, B), n) decreases measure(n) := {
        |  let ResType := Vec(Pair(A, B), n)
        |  match va returning ResType with
        |  | Vec.nil => Vec.nil(Pair(A, B))
        |  | Vec.cons n0 va0 a => {
        |    match vb returning ResType with
        |    | Vec.cons _ vb0 b => Vec.cons(n0, zip(va0, vb0), Pair.mk(a, b))
        |  }
        |}
        |""".stripMargin

    typecheckDecls(program)
  }

}
