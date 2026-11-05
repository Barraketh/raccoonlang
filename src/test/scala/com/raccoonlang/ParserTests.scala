package com.raccoonlang

import com.raccoonlang.ProgramFixtures.Programs

/**
 * The parser's layout, binder types, arrows, declaration names and parse errors (KERNEL_FOLLOWUPS §4 and
 * EVALUATION_AND_PORTS #10; README, "Syntax and layout").
 */
class ParserTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = true)
  import programs._

  /** The message of `src`'s parse error, which must not print a parser object. */
  private def parseError(src: String)(implicit loc: munit.Location): String =
    LanguageParser.parseProgram(src) match {
      case Failure(_, _, message) =>
        assert(!message.matches(".*(Parser|FatalRight|@[0-9a-f]|\\.map\\(\\)| ~ ).*"), message)
        message
      case Success(_, _, _) => fail("the program parses")
    }

  // ------------ Layout ------------

  test("blank and comment lines stand between statements, cases and constructors, and right after a brace") {
    assertEquals(
      result(
        """
          |def f (n: Nat): Nat := {
          |  // a comment right after the brace
          |
          |  let a := Nat.add(n, 1)
          |
          |  // a comment before the result
          |  match n returning Nat with
          |  | Nat.zero => a // a trailing comment
          |
          |  // a comment between cases
          |  | Nat.succ k => k
          |}
          |
          |inductive T : Type
          | | a : T
          | // a comment between constructors
          |
          | | b : T
          |def afterInductive : Nat := 0
          |
          |f(5)
          |""".stripMargin
      ),
      "4"
    )
  }

  test("a match's returning clause may start the next line, and a match's cases end their lines") {
    assertEquals(
      result(
        "def f (n: Nat): Nat := {\n  match n\n    returning Nat with\n  | Nat.zero => 0\n  | Nat.succ k => k\n}\nf(3)\n"
      ),
      "2"
    )
    assertEquals(
      parseError("def f (n: Nat): Nat := {\n  match n with | Nat.zero => 0\n}\n"),
      "Failed to parse the end of the line"
    )
    assertEquals(parseError("inductive T : Type | a : T\n"), "Failed to parse the end of the line")
  }

  test("decreases may start the line after the result type, and its specification the line after it") {
    assertEquals(
      result(
        "def g (n: Nat): Nat\n    decreases structural(n) := {\n  match n returning Nat with\n  | Nat.zero => 0\n  | Nat.succ k => g(k)\n}\ng(3)\n"
      ),
      "0"
    )
    assertEquals(
      result(
        "def g (n: Nat): Nat\n  decreases\n    structural(n) := {\n  match n returning Nat with\n  | Nat.zero => 0\n  | Nat.succ k => g(k)\n}\ng(3)\n"
      ),
      "0"
    )
    assertEquals(
      parseError("def f (n: Nat): Nat decreases foo(n) := 0\n"),
      "Failed to parse structural(x), lexicographic(x, ...) or measure(e)"
    )
  }

  test("a lexicographic component is a parameter or a measure, and measure is a whole word") {
    assertEquals(
      result("def f (measured: Nat)(b: Nat): Nat decreases lexicographic(measured, measure(b)) := b\nf(1, 2)\n"),
      "2"
    )
    assertEquals(parseError("def f (n: Nat): Nat decreases lexicographic(n, measure 0) := 0\n"), "Failed to parse '('")
  }

  // ------------ Binder types and arrows ------------

  test("a binder type may be an application followed by an arrow, or an application of an application") {
    assertEquals(
      result(
        """
          |def apply (f: List(Nat) -> Nat)(xs: List(Nat)) : Nat := f(xs)
          |def R (x: Nat): (y: Nat) -> (z: Nat) -> Prop := fun (y: Nat)(z: Nat): Prop => Eq(Nat, x, Nat.add(y, z))
          |def needs (h: R(1)(0, 1))(k: Nat -> List(Nat) -> Nat) : Nat := k(0, List.nil(Nat))
          |
          |Nat.add(apply(fun (xs: List(Nat)): Nat => List.length(xs), List.cons(1, List.nil(Nat))),
          |  needs(Eq.refl(1), fun (n: Nat)(xs: List(Nat)): Nat => 2))
          |""".stripMargin
      ),
      "3"
    )
  }

  test("a binder type may be an application headed by a projection, which then holds no capture") {
    run(
      "def a (P: Protocol.Proto)(x: P.Atom)(h: P.Step(List.cons(x, List.nil(P.Atom)), List.nil(P.Atom))) : Nat := 0\n"
    )
    assertErrorAt[InvalidTypePattern](
      "def a (P: Protocol.Proto)(h: P.Step($A, List.nil(P.Atom))) : Nat := 0\n",
      "P.Step($A, List.nil(P.Atom))"
    )
  }

  test("a capture under a continued pattern application is refused by the parser") {
    parseError("def f (h: List($A)(Nat)) : Nat := 0\n")
    parseError("def f (h: List($A) -> Nat) : Nat := 0\n")
  }

  test("A -> B is a term: an argument may be a non-dependent function type") {
    assertEquals(result("List.length(List.cons(Nat.succ, List.nil(Nat -> Nat)))\n"), "1")
    run(
      """
        |def M (P: Protocol.Proto) : Type :=
        |  Subtype(P.Atom -> List(P.Atom), fun (f: P.Atom -> List(P.Atom)): Prop => True)
        |""".stripMargin
    )
    assertEquals(
      parseError("def f : Nat := List.length(List.nil({ 0 } -> Nat))\n"),
      "A function type's domain must be a type"
    )
  }

  test("an arrow chain is one function type; a parenthesized codomain is a function type of its own") {
    assertEquals(
      result(
        """
          |def flat : Nat -> Nat -> Nat := fun (x: Nat)(y: Nat): Nat => Nat.add(x, y)
          |def nested : Nat -> (Nat -> Nat) := fun (x: Nat): (Nat -> Nat) => fun (y: Nat): Nat => Nat.add(x, y)
          |def h (x: Nat) : Nat -> Nat := fun (y: Nat): Nat => Nat.add(x, y)
          |def named : Nat -> (Nat -> Nat) := h
          |def dep : (x: Nat) -> ((y: Nat) -> Eq(Nat, Nat.add(x, y), Nat.add(x, y))) :=
          |  fun (x: Nat): ((y: Nat) -> Eq(Nat, Nat.add(x, y), Nat.add(x, y))) =>
          |    fun (y: Nat): Eq(Nat, Nat.add(x, y), Nat.add(x, y)) => Eq.refl(Nat.add(x, y))
          |def mixed : (x: Nat) -> Nat -> (y: Nat) -> Nat := fun (x: Nat)(z: Nat)(y: Nat): Nat => Nat.add(x, y)
          |Nat.add(Nat.add(flat(1, 2), nested(1)(2)), Nat.add(named(1)(2), mixed(1, 0, 2)))
          |""".stripMargin
      ),
      "12"
    )
    assertErrorAt[TypeMismatch](
      "def g : Nat -> (Nat -> Nat) := fun (x: Nat)(y: Nat): Nat => y\n",
      "fun (x: Nat)(y: Nat): Nat => y"
    )
    assertErrorAt[TypeMismatch](
      "def g : Nat -> Nat -> Nat := fun (x: Nat): (Nat -> Nat) => fun (y: Nat): Nat => y\n",
      "fun (x: Nat): (Nat -> Nat) => fun (y: Nat): Nat => y"
    )
  }

  test("a named binder heads an arrow chain, and is no type alone") {
    parseError("def f : (x: Nat) := 0\n")
    parseError("def f : Nat -> (x: Nat) := 0\n")
  }

  test("a definition without parameters may have a function type") {
    assertEquals(result("def f : Nat -> Nat := Nat.succ\nf(1)\n"), "2")
    assertEquals(result("def g : (n: Nat) -> Nat := fun (n: Nat): Nat => Nat.succ(n)\ng(1)\n"), "2")
  }

  test("a lambda binds a parameter") {
    assertEquals(parseError("def f : Nat := fun : Nat => 0\n"), "Failed to parse a lambda's parameter")
  }

  // ------------ Names ------------

  test("a dotted declaration name declares in a namespace, as a namespace block would") {
    assertEquals(
      result(
        """
          |namespace A {
          |  def x : Nat := 1
          |}
          |
          |def A.y : Nat := Nat.add(x, 1)
          |
          |def A.B.z (n: Nat) : Nat decreases structural(n) := {
          |  match n with
          |  | Nat.zero => y
          |  | Nat.succ k => z(k)
          |}
          |
          |inductive Data.T : Type
          | | leaf : T
          | | node (l: T)(r: Data.T) : T
          |
          |axiom Data.T.size (t: Data.T) : Nat
          |
          |Nat.add(A.B.z(3), List.length(List.cons(Data.T.node(Data.T.leaf, Data.T.leaf), List.nil(Data.T))))
          |""".stripMargin
      ),
      "3"
    )
  }

  test("use is an identifier except where it starts a statement") {
    assertEquals(
      result(
        "def use (n: Nat) : Nat := Nat.add(n, 1)\ndef f (n: Nat) : Nat := {\n  let use2 := use(n)\n  use(use2)\n}\nf(1)\n"
      ),
      "3"
    )
  }

  // ------------ Parse errors ------------

  test("a parse error names what was expected, never a parser object") {
    assertEquals(parseError("def g (n: Nat): Nat\n := 0\n"), "Failed to parse ':='")
    assertEquals(parseError("def f (x Nat) : Nat := 0\n"), "Failed to parse ':'")
    assertEquals(parseError("def f (x: Nat) : := 0\n"), "Failed to parse a type")
    assertEquals(parseError("def f (x: Nat) : Nat := 0\n)\n"), "Failed to parse end of input")
    assertEquals(parseError("def f (n: Nat) : Nat := { let x := 1 let y := 2\n x }\n"), "Failed to parse a term")
    assertEquals(parseError("import Foo bar\n"), "Failed to parse the end of the line")
    parseError("def f (x: Nat) : Nat := Nat.add(x, 1\n")
  }
}
