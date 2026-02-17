package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class VecZipTest extends munit.FunSuite {
  private def runProgram(src: String): Interpreter2.Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        try {
          Interpreter2.run(core)
        } catch {
          case t: TypeErrWithSpan =>
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
        | | succ : Nat -> Nat
        |
        |inductive Vec(A: Type)(n: Nat) : Type
        | | nil(A: Type): Vec A Nat.zero
        | | cons(A: Type)(n: Nat)(vec: Vec A n)(elem: A): Vec A (Nat.succ n)
        |
        |inductive Pair (A: Type)(B: Type): Type
        | | mk(A: Type)(B: Type)(a: A)(b: B): Pair A B
        |
        |inline def zip(A: Type)(B: Type)(n: Nat)(va: Vec A n)(vb: Vec B n): Vec (Pair A B) n := {
        |  let R := Pair A B
        |  match va as _ returning Vec R n with
        |  | Vec.nil t => Vec.nil R
        |  | Vec.cons _ _ va0 a => {
        |    match vb as _ returning Vec R n with
        |    | Vec.cons _ _ vb0 b => {
        |       match n as _ returning Vec R n with
        |       | Nat.succ x => Vec.cons R x (zip A B x va vb ) (Pair.mk A B a b)
        |    }
        |  }
        |}
        |
        |do {
        |  Nat.zero
        |}
        |
        |
        |""".stripMargin

    runProgram(program)
  }

}
