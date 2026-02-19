package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class VecZipTest extends munit.FunSuite {
  private def runProgram(src: String): Interpreter.Value = {
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
        |  | Vec.cons _ x va0 a => {
        |    match vb as _ returning Vec R n with
        |    | Vec.cons _ _ vb0 b => Vec.cons R x (zip A B x va0 vb0 ) (Pair.mk A B a b)
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
