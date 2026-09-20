package com.raccoonlang

class MatchExhaustivenessTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

  test("non-exhaustive: missing succ case on Peano") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def onlyZero (n: Peano): Peano := {
        |  match n with
        |  | Peano.zero => Peano.zero
        |}
        |
        |""".stripMargin

    interceptError[MissingCase] { typecheckDecls(p) }
  }

  test("duplicate case: two Peano.zero branches") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def dup (n: Peano): Peano := {
        |  match n with
        |  | Peano.zero => Peano.zero
        |  | Peano.zero => Peano.zero
        |  | Peano.succ x => x
        |}
        |
        |""".stripMargin

    interceptError[DuplicateCase] { typecheckDecls(p) }
  }

  test("unreachable case: Vec.cons on Vec A Peano.zero") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Sort(Level.one)
        | | nil : Vec(A, Peano.zero)
        | | cons (n: Peano) (xs: Vec(A, n)) (x: A): Vec(A, Peano.succ(n))
        |
        |def f (A: Type)(v: Vec(A, Peano.zero)): Peano := {
        |  match v returning Peano with
        |  | Vec.nil => Peano.zero
        |  | Vec.cons n xs x => Peano.zero
        |}
        |
        |""".stripMargin

    interceptError[UnreachableCase] { typecheckDecls(p) }
  }

  test("non-exhaustive: opaque scrutinee application should still require succ case") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |// Opaque on purpose: evaluator will keep this as a Symbol head
        |opaque def g (n: Peano): Peano := Peano.zero
        |
        |def bad (n: Peano): Peano := {
        |  // scrutinee is neutral/opaque application: g n
        |  match g(n) with
        |  | Peano.zero => Peano.zero
        |}
        |
        |""".stripMargin

    interceptError[MissingCase] { typecheckDecls(p) }
  }

  test("exhaustive: opaque scrutinee application should typecheck") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |opaque def g (n: Peano): Peano := n
        |
        |def ok (n: Peano): Peano := {
        |  match g(n) with
        |  | Peano.zero => Peano.zero
        |  | Peano.succ x => x
        |}
        |
        |""".stripMargin

    // Should typecheck (even if it evaluates to a stuck match at runtime for opaque g).
    typecheckDecls(p)
  }

  test("omitted returning: inferred when all reachable constructor result types are equal") {
    val p =
      """
        |inductive Wrap (A: Type) : Type
        | | left (x: A) : Wrap(A)
        | | right (x: A) : Wrap(A)
        |
        |def keepWrap (A: Type)(w: Wrap(A)): Wrap(A) := {
        |  match w with
        |  | Wrap.left x => Wrap.left(x)
        |  | Wrap.right x => Wrap.right(x)
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("omitted returning: expected type permits empty unreachable match") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive IsZero indices (n: Peano) : Type
        | | intro : IsZero(Peano.zero)
        |
        |def absurdSucc (n: Peano)(h: IsZero(Peano.succ(n))): Peano := {
        |  match h with
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("omitted returning: expected type disambiguates differing reachable constructor results") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Shape indices (n: Peano) : Type
        | | zeroCase : Shape(Peano.zero)
        | | succCase (m: Peano) : Shape(Peano.succ(m))
        |
        |def keepShape (n: Peano)(s: Shape(n)): Shape(n) := {
        |  match s with
        |  | Shape.zeroCase => s
        |  | Shape.succCase m => s
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  // A def body's `match` inherits the declared return type, which is syntax in the body's own
  // scope (the Pi's `out`), so it needs no `returning` clause even when it mentions a parameter.
  test("match with no returning clause inherits a declared return type that mentions a parameter") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def f {A: Type}(x: Peano)(y: A): A := {
        |  match x with
        |  | Peano.zero => y
        |  | Peano.succ _ => y
        |}
        |
        |axiom n : Peano
        |axiom a : Peano
        |
        |{ f(n, a) }
        |""".stripMargin

    // Applied to a neutral scrutinee the match is stuck, and its type is the declared return type
    // instantiated at the call: A := Peano.
    val result = runProgram(p)
    result match {
      case Value.VCtor(head, _, _) => fail(s"Expected a stuck match, got constructor ${head.name}")
      case _                       =>
    }
    assertEquals(PrettyPrinter.print(result.tpe), "Peano")
  }

  // A branch body is checked against a bare motive *value* (materialized per branch), so a nested
  // `match` there inherits no syntax. It is accepted only when it can infer its own motive from
  // the scrutinee's type; a result type that differs per branch cannot, and needs `returning`.
  test("nested match under a dependent motive needs a returning clause of its own") {
    def program(returning: String): String =
      s"""
         |inductive Peano : Type
         | | zero : Peano
         | | succ (_: Peano) : Peano
         |
         |inductive Shape indices (n: Peano) : Type
         | | zeroCase : Shape(Peano.zero)
         | | succCase (m: Peano) : Shape(Peano.succ(m))
         |
         |def f (n: Peano)(s: Shape(n))(b: Peano)(c: Peano): Shape(n) := {
         |  match b returning Shape(n) with
         |  | Peano.zero => s
         |  | Peano.succ _ => {
         |    match c$returning with
         |    | Peano.zero => s
         |    | Peano.succ _ => s
         |  }
         |}
         |""".stripMargin

    interceptError[MissingReturningClause] { typecheckDecls(program("")) }
    typecheckDecls(program(" returning Shape(n)"))
  }
}
