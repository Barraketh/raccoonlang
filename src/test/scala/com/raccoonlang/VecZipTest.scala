package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class VecZipTest extends munit.FunSuite {
  private def runProgram(src: String): Value = {
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
        |inductive Vec(u: Level)(A: Sort u)(n: Nat) : Sort u
        | | nil(u: Level)(A: Sort u): Vec u A Nat.zero
        | | cons(u: Level)(A: Sort u)(n: Nat)(vec: Vec u A n)(elem: A): Vec u A (Nat.succ n)
        |
        |inductive Pair (A: Type)(B: Type): Sort Level.one
        | | mk(A: Type)(B: Type)(a: A)(b: B): Pair A B
        |
        |inline def zip(A: Type)(B: Type)(n: Nat)(va: Vec Level.zero A n)(vb: Vec Level.zero B n): Vec Level.one (Pair A B) n := {
        |  let R := Pair A B
        |  match va as _ returning Vec R n with
        |  | Vec.nil _ t => Vec.nil Level.one R
        |  | Vec.cons _ _ x va0 a => {
        |    match vb as _ returning Vec R n with
        |    | Vec.cons _ _ _ vb0 b => Vec.cons Level.one R x (zip A B x va0 vb0 ) (Pair.mk A B a b)
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
