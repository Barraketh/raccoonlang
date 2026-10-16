package com.raccoonlang

class MatchRefinementTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

  test("match refinement: symmEq over neutral VApp scrut succeeds") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (p: Peano) : Peano
        |
        |def symmEq (a: Peano)(b: Peano)(p: Eq(Peano, a, b)): Eq(Peano, b, a) := {
        |  match p returning Eq(Peano, b, a) with
        |  | Eq.refl x => Eq.refl(x)
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("match refinement: congSucc via wrapped scrut succeeds") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (p: Peano) : Peano
        |
        |def congSucc2 (a: Peano)(b: Peano)(p: Eq(Peano, a, b)): Eq(Peano, Peano.succ(a), Peano.succ(b)) := {
        |  match p returning Eq(Peano, Peano.succ(a), Peano.succ(b)) with
        |  | Eq.refl x => Eq.refl(Peano.succ(x))
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("match refinement negative: mismatched motive (extra succ) fails (ctor scrut)") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (p: Peano) : Peano
        |
        |def badCongCtor (a: Peano): Eq(Peano, a, Peano.succ(a)) := {
        |  match Eq.refl(a) returning Eq(Peano, a, Peano.succ(a)) with
        |  | Eq.refl x => Eq.refl(x)
        |}
        |
        |""".stripMargin

    interceptError[TypeMismatch] { typecheckDecls(p) }
  }

  test("match refinement on a family parameter of a neutral Vec scrut succeeds at its universe") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (p: Peano) : Peano
        |
        |inductive Vec (u: Level)(A: Type { level = u }) indices (n: Peano) : Type { level = u }
        | | nil : Vec(u, A, Peano.zero)
        | | cons (n: Peano) (xs: Vec(u, A, n)) (x: A) : Vec(u, A, Peano.succ(n))
        |
        |def keepVec (n: Peano)(v: Vec(Level.zero, Peano, n)): Vec(Level.zero, Peano, n) := {
        |  match v returning Vec(Level.zero, Peano, n) with
        |  | Vec.nil => v
        |  | Vec.cons k xs x => v
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("match refinement negative: non-family hidden binder does not refine the requested index") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Type
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |inductive Hidden indices (n: Peano) : Type
        | | mk {m: Peano} (x: Vec(Peano, m)) : Hidden(Peano.zero)
        |
        |def bad (w: Hidden(Peano.zero)): Vec(Peano, Peano.zero) := {
        |  match w returning Vec(Peano, Peano.zero) with
        |  | Hidden.mk m x => x
        |}
        |""".stripMargin

    interceptError[TypeMismatch] { typecheckDecls(p) }
  }

  // A constructor's parameters are the scrutinee type's own, never unknowns, so an index equation
  // that is stuck (here on a neutral `double` application) leaves each field at the scrutinee's
  // parameters. A lambda capturing one derives its closure over variables in scope.
  private def stuckIndex(declarations: String): String =
    """
      |inductive Peano : Type
      | | zero : Peano
      | | succ (p: Peano) : Peano
      |
      |inductive Tick : Type
      | | tick : Tick
      |
      |axiom double (n: Peano): Peano
      |""".stripMargin + declarations

  test("a stuck index equation preserves the field's type parameter") {
    def program(body: String): String =
      stuckIndex(
        s"""
           |inductive H (A: Type ) indices (n: Peano) : Type
           | | mk (x: A) : H(A, Peano.zero)
           |
           |def f {A: Type }(n: Peano)(w: H(A, double(n))): A := match w returning A with
           | | .mk x => $body
           |""".stripMargin
      )

    typecheckDecls(program("x"))
    typecheckDecls(program("(fun (u: Tick): A => x)(Tick.tick)"))
  }

  test("a stuck index equation leaves a field at the scrutinee's type parameter") {
    def program(result: String, body: String): String =
      stuckIndex(
        s"""
           |inductive V (A: Type ) indices (n: Peano) : Type
           | | nil : V(A, Peano.zero)
           | | cons (m: Peano)(head: A)(tail: V(A, m)) : V(A, Peano.succ(m))
           |
           |def headOr {A: Type }(B: Type)(k: Peano)(d: $result)(v: V(A, double(k))): $result :=
           |  match v returning $result with
           |  | .nil => d
           |  | .cons m h t => $body
           |""".stripMargin
      )

    typecheckDecls(program("A", "h"))
    typecheckDecls(program("A", "(fun (u: Tick): A => h)(Tick.tick)"))
    expectOnly[TypeMismatch](typecheckDecls(program("B", "h")))
  }

  test("a stuck index equation keeps every constructor's branch required") {
    def program(cases: String*): String =
      stuckIndex(
        """
          |inductive V (A: Type) indices (n: Peano) : Type
          | | nil : V(A, Peano.zero)
          | | cons (m: Peano)(head: A)(tail: V(A, m)) : V(A, Peano.succ(m))
          |
          |def f (A: Type)(k: Peano)(v: V(A, double(k))): Tick := match v returning Tick with
          |""".stripMargin + cases.mkString("", "\n", "\n")
      )
    val nil = " | .nil => Tick.tick"
    val cons = " | .cons m h t => Tick.tick"

    typecheckDecls(program(nil, cons))
    expectOnly[MissingCase](typecheckDecls(program(nil)))
    expectOnly[MissingCase](typecheckDecls(program(cons)))
  }

  test("a postponed argument retries after a later argument links a variable it reaches") {
    // `g(x) ~ g(c)` is stuck beneath the arbitrary function head. The next constructor argument links x and c, so the
    // postponed equation now reaches a new link and succeeds on retry.
    typecheckDecls(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (p: Peano) : Peano
        |
        |inductive Two : Type
        | | mk (a: Peano)(b: Peano) : Two
        |
        |def congArg (g: (n: Peano) -> Peano)(x: Peano)(c: Peano)
        |  (p: Eq(Two, Two.mk(g(x), x), Two.mk(g(c), c))): Eq(Peano, c, x) := {
        |  match p returning Eq(Peano, c, x) with
        |  | Eq.refl t => Eq.refl(x)
        |}
        |""".stripMargin
    )
  }

  private def nestedApply(head: String, value: String, depth: Int): String =
    (0 until depth).foldLeft(value)((inner, _) => s"$head($inner)")

  test("nested applications of one shared neutral head do not retry unchanged stuck arguments") {
    val depth = 36
    val declarations =
      s"""
         |inductive Peano : Type
         | | zero : Peano
         | | succ (p: Peano) : Peano
         |
         |inductive Indexed (g: (n: Peano) -> Peano) indices (n: Peano) : Type
         | | wrap (x: Peano) : Indexed(g, ${nestedApply("g", "x", depth)})
         |""".stripMargin

    def matching(cases: String): String =
      declarations +
        s"""
           |def use (g: (n: Peano) -> Peano)(n: Peano)(value: Indexed(g, ${nestedApply("g", "n", depth)})): Peano := {
           |  match value returning Peano with
           |$cases
           |}
           |""".stripMargin

    typecheckDecls(matching("  | .wrap x => x\n"))
    expectTypeError[MissingCase](matching(""))
  }

}
