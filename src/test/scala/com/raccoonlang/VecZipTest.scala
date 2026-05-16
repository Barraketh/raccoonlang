package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class VecZipTest extends munit.FunSuite {
  private def typecheckDecls(src: String): Unit = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        try {
          Interpreter.run(core)
        } catch {
          case t: TypeError =>
            val source = Source(src)
            fail(ErrorReporter.pretty(t, source))
        }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  test("Indexed Vec zip") {
    val program =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec(u: Level)(A: Sort(u))(n: Nat) : Sort(Level.max(Level.one, u))
        | | nil {u: Level}{A: Sort(u)}: Vec(u, A, Nat.zero)
        | | cons {u: Level}{A: Sort(u)}(n: Nat)(vec: Vec(u, A, n))(elem: A): Vec(u, A, Nat.succ(n))
        |
        |inductive Pair(u1: Level)(u2: Level)(A: Sort(u1))(B: Sort(u2)): Sort(Level.max(u1, u2))
        | | mk {u1: Level}{u2: Level}{A: Sort(u1)}{B: Sort(u2)}(a: A)(b: B): Pair(u1, u2, A, B)
        |
        |inline def zip(u1: Level)(u2: Level)(A: Sort(u1))(B: Sort(u2))(n: Nat)(va: Vec(u1, A, n))(vb: Vec(u2, B, n)): Vec(Level.max(u1, u2), Pair(u1, u2, A, B), n) := {
        |  let R := Pair(u1, u2, A, B)
        |  let L := Level.max(u1, u2)
        |  match va returning Vec(L, R, n) with
        |  | Vec.nil => Vec.nil(L, R)
        |  | Vec.cons x va0 a => {
        |    match vb returning Vec(L, R, n) with
        |    | Vec.cons _ vb0 b => Vec.cons(L, R, x, zip(u1, u2, A, B, x, va0, vb0), Pair.mk(u1, u2, A, B, a, b))
        |  }
        |}
        |
        |{
        |  Nat.zero
        |}
        |
        |
        |""".stripMargin

    typecheckDecls(program)
  }

  test("Indexed Vec zip with type patterns") {
    val program =
      """
        |inductive Nat : Type
        |  | zero : Nat
        |  | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Sort($u))(n: Nat) : Sort(Level.max(Level.one, u))
        |  | nil {A: Sort($u)}: Vec(A, Nat.zero)
        |  | cons {A: Sort($u)} (v: Vec(A, $n))(elem: A): Vec(A, Nat.succ(n))
        |
        |inductive Pair (A: Sort($u1))(B: Sort($u2)): Sort(Level.max(u1, u2))
        |  | mk(a: $A in Sort($u1))(b: $B in Sort($u2)): Pair(A, B)
        |
        |inline def zip(va: Vec($A, $n))(vb: Vec($B, n)): Vec(Pair(A, B), n) := {
        |  let ResType := Vec(Pair(A, B), n)
        |  match va returning ResType with
        |  | Vec.nil => Vec.nil(Pair(A, B))
        |  | Vec.cons va0 a => {
        |    match vb returning ResType with
        |    | Vec.cons vb0 b => Vec.cons(Pair(A, B), zip(va0, vb0), Pair.mk(a, b))
        |  }
        |}
        |""".stripMargin

    typecheckDecls(program)
  }

}
