package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class TerminationTests extends munit.FunSuite {
  private def runProgram(src: String): Option[Value] =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        try Interpreter.run(core)
        catch {
          case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
        }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def typeError[T <: TypeError](src: String)(implicit ct: reflect.ClassTag[T]): T =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        intercept[T] {
          val core = Elaborator.elab(value)
          Interpreter.run(core)
        }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private val natDecls =
    """
      |inductive Nat : Type
      | | zero : Nat
      | | succ (_: Nat) : Nat
      |""".stripMargin

  sealed trait Shape
  case class SConst(name: String) extends Shape
  case class SApp(head: Shape, args: List[Shape]) extends Shape

  private def toShape(v: Value): Shape = v match {
    case Value.ConstructorHead(n, _, _, _, _) => SConst(n)
    case ctor @ Value.VCtor(h, _, _) =>
      val fields = ctor.fields
      if (fields.isEmpty) SConst(h.name) else SApp(SConst(h.name), fields.toList.map(toShape))
    case Value.VConst(n, _, _)  => SConst(n)
    case Value.VApp(h, args, _) => SApp(toShape(h), args.toList.map(toShape))
    case other                  => SConst(other.toString)
  }

  private val zeroS = SConst("Nat.zero")
  private def succS(s: Shape): Shape = SApp(SConst("Nat.succ"), List(s))

  test("structural recursion accepts direct recursive calls") {
    val p =
      natDecls +
        """
          |stable def add (a: Nat)(b: Nat): Nat decreases structural(b) := {
          |  match b with
          |  | Nat.zero => a
          |  | Nat.succ x => add(Nat.succ(a), x)
          |}
          |
          |{
          |  let one := Nat.succ(Nat.zero)
          |  add(one, one)
          |}
          |""".stripMargin

    assertEquals(toShape(runProgram(p).get), succS(succS(zeroS)))
  }

  test("raw recursive self cannot be stored as a direct local alias") {
    val p =
      natDecls +
        """
          |def bad (n: Nat): Nat decreases structural(n) := {
          |  let go := bad
          |  match n with
          |  | Nat.zero => Nat.zero
          |  | Nat.succ x => go(x)
          |}
          |""".stripMargin

    typeError[InvalidRecursiveOccurrence](p)
  }

  test("structural recursion searches through transitive constructor fields") {
    val p =
      natDecls +
        """
          |inline def skipTwo (n: Nat): Nat decreases structural(n) := {
          |  match n with
          |  | Nat.zero => Nat.zero
          |  | Nat.succ x => {
          |    match x with
          |    | Nat.zero => Nat.zero
          |    | Nat.succ y => skipTwo(y)
          |  }
          |}
          |""".stripMargin

    runProgram(p)
  }

  test("lexicographic recursion accepts an earlier decrease or equal-prefix later decrease") {
    val p =
      natDecls +
        """
          |inline def lex (a: Nat)(b: Nat): Nat decreases lexicographic(a, b) := {
          |  match a with
          |  | Nat.zero => {
          |    match b with
          |    | Nat.zero => Nat.zero
          |    | Nat.succ b0 => lex(Nat.zero, b0)
          |  }
          |  | Nat.succ a0 => lex(a0, b)
          |}
          |""".stripMargin

    runProgram(p)
  }

  test("measure recursion compares the evaluated measure structurally") {
    val p =
      natDecls +
        """
          |inductive List (A: Type) : Type
          | | nil {A: Type} : List(A)
          | | cons {A: Type} (tail: List(A)) (head: A) : List(A)
          |
          |stable def length (A: Type)(xs: List(A)): Nat decreases structural(xs) := {
          |  match xs returning Nat with
          |  | List.nil => Nat.zero
          |  | List.cons tail _ => Nat.succ(length(A, tail))
          |}
          |
          |inline def consume (A: Type)(xs: List(A)): Nat decreases measure(length(A, xs)) := {
          |  match xs returning Nat with
          |  | List.nil => Nat.zero
          |  | List.cons tail _ => consume(A, tail)
          |}
          |""".stripMargin

    runProgram(p)
  }

  test("recursive self call without decreases is rejected") {
    val p =
      natDecls +
        """
          |def bad (n: Nat): Nat := bad(n)
          |""".stripMargin

    typeError[NotFound](p)
  }

  test("non-decreasing structural recursion is rejected") {
    val p =
      natDecls +
        """
          |def bad (n: Nat): Nat decreases structural(n) := bad(n)
          |""".stripMargin

    typeError[NonDecreasingRecursiveCall](p)
  }

  test("proof irrelevance does not create fake structural decreases") {
    val p =
      """
        |inductive P : Prop
        | | base : P
        | | wrap (p: P) : P
        |
        |def bad (p: P): P decreases structural(p) := {
        |  match p returning P with
        |  | P.base => P.base
        |  | P.wrap x => bad(p)
        |}
        |""".stripMargin

    typeError[NonDecreasingRecursiveCall](p)
  }

  test("lexicographic recursion requires some component to decrease") {
    val p =
      natDecls +
        """
          |def bad (a: Nat)(b: Nat): Nat decreases lexicographic(a, b) := bad(a, b)
          |""".stripMargin

    typeError[NonDecreasingRecursiveCall](p)
  }

  test("decreases structural must name a function binder") {
    val p =
      natDecls +
        """
          |def bad (n: Nat): Nat decreases structural(Nat) := n
          |""".stripMargin

    typeError[InvalidDecreaseSpec](p)
  }

  test("measure expression must have an inductive type") {
    val p =
      natDecls +
        """
          |def bad (n: Nat): Nat decreases measure(Type) := n
          |""".stripMargin

    typeError[InvalidDecreaseSpec](p)
  }

  test("raw recursive self cannot be stored inside a residual let value") {
    val p =
      natDecls +
        """
          |def opaqueApply (h: Nat -> Nat)(n: Nat): Nat := h(n)
          |
          |def bad (n: Nat): Nat decreases structural(n) := {
          |  let x := opaqueApply(bad, n)
          |  Nat.zero
          |}
          |""".stripMargin

    typeError[InvalidRecursiveOccurrence](p)
  }


  test("raw recursive self cannot be hidden inside a trusted normalizer value") {
    val p =
      natDecls +
        """
          |def bad (a: Nat)(b: Nat): Nat decreases structural(b) := {
          |  let n := add_normalizer(Nat.zero, bad)
          |  Nat.zero
          |}
          |""".stripMargin

    typeError[InvalidRecursiveOccurrence](p)
  }
}
