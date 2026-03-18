package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class EqualityWithNormalizerTests extends munit.FunSuite {
  val addNormalizerTpe =
    LanguageParser.parseFuncHeader("(A: Type)(zero: A)(add: A -> A -> A): Normalizer") match {
      case Success(header, _, _) => Elaborator.getType(header)
    }

  private def runProgram(src: String): Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        try {
          Interpreter.run(
            core,
            List(("add_normalizer", addNormalizerTpe, (args, _) => Normalizers.add_normalizer(args.toVector)))
          )
        } catch {
          case t: TypeError =>
            val source = Source(src)
            fail(ErrorReporter.pretty(t, source))
        }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  test("Eq proofs via normalizer: comm, zero, assoc") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |stable def add (a: Nat)(b: Nat): Nat := {
        |  match b as _ returning Nat with
        |  | Nat.zero => a
        |  | Nat.succ x => add (Nat.succ a) x
        |}
        |
        |inline def nat_add_normalizer : Normalizer := add_normalizer Nat Nat.zero add
        |
        |inductive Eq : (A: Type) -> A -> A -> Type
        | | refl (A: Type)(x: A) : Eq A x x
        |
        |// Using the additive normalizer over Nat, these equalities become definitional
        |
        |inline def addZeroRight (a: Nat): Eq Nat (add a Nat.zero) a := { 
        |  use nat_add_normalizer
        |  Eq.refl Nat (add a Nat.zero)
        |}
        |
        |inline def addZeroLeft (a: Nat): Eq Nat (add Nat.zero a) a := { 
        |  use nat_add_normalizer
        |  Eq.refl Nat (add Nat.zero a)
        |}
        |
        |inline def addComm (a: Nat)(b: Nat): Eq Nat (add a b) (add b a) := { 
        |  use nat_add_normalizer
        |  Eq.refl Nat (add a b)
        |}
        |
        |inline def addAssoc (x: Nat)(y: Nat)(z: Nat): Eq Nat (add x (add y z)) (add (add x y) z) := { 
        |  use nat_add_normalizer
        |  Eq.refl Nat (add x (add y z))
        |}
        |
        |do {
        |  // Just ensure all proofs typecheck under the normalizer
        |  addComm Nat.zero (Nat.succ Nat.zero)
        |}
        |""".stripMargin

    runProgram(p)
  }

  test("Negative: commutativity proof without normalizer fails") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |stable def add (a: Nat)(b: Nat): Nat := {
        |  match b as _ returning Nat with
        |  | Nat.zero => a
        |  | Nat.succ x => add (Nat.succ a) x
        |}
        |
        |inductive Eq : (A: Type) -> A -> A -> Type
        | | refl (A: Type)(x: A) : Eq A x x
        |
        |inline def addCommNoNorm (a: Nat)(b: Nat): Eq Nat (add a b) (add b a) := Eq.refl Nat (add a b)
        |
        |do { addCommNoNorm Nat.zero (Nat.succ Nat.zero) }
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[TypeError] { Interpreter.run(core) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Negative: left identity proof without normalizer fails") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |stable def add (a: Nat)(b: Nat): Nat := {
        |  match b as _ returning Nat with
        |  | Nat.zero => a
        |  | Nat.succ x => add (Nat.succ a) x
        |}
        |
        |inductive Eq : (A: Type) -> A -> A -> Type
        | | refl (A: Type)(x: A) : Eq A x x
        |
        |inline def addZeroLeftNoNorm (a: Nat): Eq Nat (add Nat.zero a) a := Eq.refl Nat (add Nat.zero a)
        |
        |do { addZeroLeftNoNorm (Nat.succ Nat.zero) }
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[TypeError] { Interpreter.run(core) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }
}
