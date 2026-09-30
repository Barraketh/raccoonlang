package com.raccoonlang

/**
 * Pair expressions (docs/PAIRS_AND_PRELUDE.md §4): in a term position `(a, b)` is the active prelude's `Pair.mk(a, b)`,
 * checked as that application, whatever is in scope. Each rule has an admitted program and the smallest mutation that
 * reaches its diagnostic.
 */
class PairExpressionTests extends munit.FunSuite with TestSupport {

  private def evaluatesTo(source: String, expected: String)(implicit loc: munit.Location): Unit =
    assertEquals(PrettyPrinter.print(runProgram(source)), expected)

  /** Where the single diagnostic `source` reports under `prelude` starts, as the text from there on. */
  private def reportedAt(source: String, prelude: Prelude.Config)(implicit loc: munit.Location): String =
    source.substring(interceptDiagnostic(typecheckDecls(source, prelude)).span.get.start)

  /** A linear token and its consumer. */
  private val tokens =
    """
      |inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }
      | | mk : Tok(l)
      |
      |def burn {l: Lifetime}(t: Tok(l)): Nat := match t returning Nat with
      | | Tok.mk => 1
      |""".stripMargin

  test("a pair expression is Pair.mk of its components, at the type they give it") {
    evaluatesTo("{ (1, Bool.true) }", "Pair.mk(1, Bool.true)")
    typecheckDecls("def p : Pair(Nat, Bool) := (1, Bool.true)\n")
    expectOnly[TypeMismatch](typecheckDecls("def p : Pair(Bool, Nat) := (1, Bool.true)\n"))
    // Its type is local: no expected type reaches it, and it is the constructor's application.
    typecheckDecls(
      "def p : Nat := {\n  let q := (1, Bool.true)\n  let h : Eq(Pair(Nat, Bool), q, Pair.mk(1, Bool.true)) := Eq.refl(q)\n" +
        "  0\n}\n"
    )
    // A pair of types is a value, never a type: there is no pair type syntax.
    evaluatesTo("{ (Nat, Bool) }", "Pair.mk(Nat, Bool)")
    typecheckDecls("def p : Pair(Type, Type) := (Nat, Bool)\n")
    expectOnly[TypeMismatch](typecheckDecls("def p : Type := (Nat, Bool)\n"))
  }

  test("a pair nests, and parentheses around a pair or a term only group") {
    evaluatesTo("{ (1, (2, 3)) }", "Pair.mk(1, Pair.mk(2, 3))")
    evaluatesTo("{ ((1, 2), 3) }", "Pair.mk(Pair.mk(1, 2), 3)")
    typecheckDecls("def p : Pair(Nat, Pair(Nat, Nat)) := (1, (2, 3))\n")
    evaluatesTo("{ ((1, 2)) }", "Pair.mk(1, 2)")
    evaluatesTo("{ (1) }", "1")
    evaluatesTo("{ (Nat.add)((1), 2) }", "3")
  }

  test("a pair expression is an argument, a scrutinee and a lambda body") {
    evaluatesTo(
      "def first (p: Pair(Nat, Bool)): Nat := match p returning Nat with\n | Pair.mk n _ => n\n\n{ first((4, Bool.true)) }",
      "4"
    )
    evaluatesTo("{ match (5, Bool.false) returning Nat with\n | Pair.mk n _ => n\n}", "5")
    evaluatesTo("{ (fun (n: Nat): Pair(Nat, Nat) => (n, Nat.succ(n)))(6) }", "Pair.mk(6, 7)")
  }

  test("a linear component makes a linear pair") {
    def program(body: String): String =
      tokens +
        "def spend {l: Lifetime}(p: Pair(Tok(l), Nat)): Nat := match p returning Nat with\n" +
        " | Pair.mk t n => Nat.add(burn(t), n)\n\n" +
        s"def use {l: Lifetime}(t: Tok(l)): Nat := {\n  let p := (t, 2)\n  $body\n}\n"
    evaluatesTo(program("spend(p)") + "{ scope l => use(Tok.mk(l)) }\n", "3")
    assertEquals(expectOnly[LinearReused](typecheckDecls(program("Nat.add(spend(p), spend(p))"))), LinearReused("p"))
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("0"))), LinearUnused("p"))
    // Each component is a use of what it mentions.
    assertEquals(
      expectOnly[LinearReused](
        typecheckDecls(tokens + "def two {l: Lifetime}(t: Tok(l)): Pair(Tok(l), Tok(l)) := (t, t)\n")
      ),
      LinearReused("t")
    )
  }

  test("a pair expression at a kind variable is checked through generic code") {
    val defs =
      tokens +
        """
          |def wrap {k: Kind}{S: Lifetime}{A: Type { kind = k, scope = S }}(a: A): Pair(A, Nat) := (a, 0)
          |
          |def unwrap {k: Kind}{S: Lifetime}{A: Type { kind = k, scope = S }}(p: Pair(A, Nat)): A := {
          |  let (a, _) := p
          |  a
          |}
          |
          |def spend {l: Lifetime}(t: Tok(l)): Nat := burn(unwrap(wrap(t)))
          |""".stripMargin
    evaluatesTo(defs + "{ Nat.add(unwrap(wrap(3)), scope l => spend(Tok.mk(l))) }\n", "4")
    // A value at a kind variable may be linear, so the pair holding it is used once.
    assertEquals(
      expectOnly[LinearUnused](
        typecheckDecls("def lose {k: Kind}{A: Type { kind = k }}(a: A): Nat := {\n  let p := (a, 0)\n  0\n}\n")
      ),
      LinearUnused("p")
    )
  }

  test("no local, namespace, open or user Pair.mk changes what a pair expression means") {
    evaluatesTo("{\n  let Pair := 5\n  (Pair, 1)\n}\n", "Pair.mk(5, 1)")
    evaluatesTo("def f (mk: Nat): Pair(Nat, Nat) := (mk, mk)\n\n{ f(2) }", "Pair.mk(2, 2)")
    val shadow =
      """
        |namespace M {
        |  inductive Pair (A: Type)(B: Type) : Type
        |   | mk (b: B)(a: A) : Pair(A, B)
        |
        |  def own : Pair(Nat, Bool) := Pair.mk(Bool.true, 1)
        |
        |  def pair : _root_.Pair(Nat, Bool) := (1, Bool.true)
        |}
        |""".stripMargin
    evaluatesTo(shadow + "{ M.pair }", "Pair.mk(1, Bool.true)")
    evaluatesTo(shadow + "{ M.own }", "M.Pair.mk(Bool.true, 1)")
    evaluatesTo(shadow + "open M\n\n{ (1, Bool.true) }", "Pair.mk(1, Bool.true)")
    evaluatesTo(shadow + "{\n  open M\n  (1, Bool.true)\n}\n", "Pair.mk(1, Bool.true)")
    evaluatesTo(shadow + "open M.{Pair as Q}\n\n{ (1, Bool.true) }", "Pair.mk(1, Bool.true)")
    val alias = "namespace N {\n  inductive Q : Type\n   | mk (n: Nat)(m: Nat) : Q\n}\n\nopen N.{Q as Pair}\n\n"
    evaluatesTo(alias + "{ (1, 2) }", "Pair.mk(1, 2)")
    evaluatesTo(alias + "{\n  open N.{Q as Pair}\n  (1, 2)\n}\n", "Pair.mk(1, 2)")
    expectOnly[TypeMismatch](
      typecheckDecls(shadow.replace("def pair : _root_.Pair(Nat, Bool)", "def pair : Pair(Nat, Bool)"))
    )
  }

  test("a pair expression is the active prelude's Pair.mk, and NotFound under a prelude with none") {
    val units = "inductive Unit : Type\n | unit : Unit\n"
    val noPair = Prelude.fromSource("no-pair", units)
    val program = "def u : Unit := {\n  let p := (Unit.unit, Unit.unit)\n  Unit.unit\n}\n"
    assertEquals(expectOnly[NotFound](typecheckDecls(program, noPair)), NotFound("Pair.mk"))
    assert(reportedAt(program, noPair).startsWith("(Unit.unit, Unit.unit)\n"))
    // A program's own Pair.mk is not the prelude's, whatever it is named.
    val own = "inductive Pair (A: Type)(B: Type) : Type\n | mk (a: A)(b: B) : Pair(A, B)\n\n"
    typecheckDecls(own + program.replace("(Unit.unit, Unit.unit)", "Pair.mk(Unit.unit, Unit.unit)"), noPair)
    assertEquals(expectOnly[NotFound](typecheckDecls(own + program, noPair)), NotFound("Pair.mk"))
    // A prelude that declares Pair.mk defines what a pair expression applies, in its own declarations too, from where
    // it has declared it.
    val both = "def both : Pair(Unit, Unit) := (Unit.unit, Unit.unit)\n"
    val withPair = Prelude.fromSource("own-pair", units + "\n" + own + both)
    typecheckDecls("def p : Pair(Unit, Unit) := (Unit.unit, Unit.unit)\n", withPair)
    assertEquals(PrettyPrinter.print(runProgram("{ both }", withPair)), "Pair.mk(Unit.unit, Unit.unit)")
    assertEquals(
      interceptError[NotFound](Prelude.fromSource("early-pair", units + "\n" + program + "\n" + own)),
      NotFound("Pair.mk")
    )
  }

  test("a pair expression is a value that trailers select from and apply") {
    // Pair has no selectors, so selecting a field is the selector's NotFound, and a pair is no function.
    assertEquals(expectOnly[NotFound](typecheckDecls("def x : Nat := (1, 2).fst\n")), NotFound("Pair.fst"))
    val applied = "def x : Nat := (Nat.succ, Nat.succ)(1)\n"
    typecheckDecls(applied.replace("(Nat.succ, Nat.succ)(1)", "(Nat.succ)(1)"))
    expectOnly[CannotApplyNonFunction](typecheckDecls(applied))
  }

  test("a pair expression is an argument in a type: in a signature, an annotation and a motive") {
    evaluatesTo(
      "def f (p: Pair(Nat, Nat))(h: Eq(Pair(Nat, Nat), p, (1, (2)))): Nat := 0\n\n{ f((1, 2), Eq.refl((1, 2))) }",
      "0"
    )
    expectOnly[TypeMismatch](
      typecheckDecls(
        "def f (p: Pair(Nat, Nat))(h: Eq(Pair(Nat, Nat), p, (1, 2))): Nat := 0\n\n{ f((2, 1), Eq.refl((2, 1))) }"
      )
    )
    typecheckDecls(
      "def f : Nat := {\n  let h : Eq(Pair(Nat, Pair(Nat, Nat)), (1, (2, 3)), Pair.mk(1, Pair.mk(2, 3))) := Eq.refl((1, (2, 3)))\n  0\n}\n"
    )
    typecheckDecls(
      "def f (b: Bool): Eq(Pair(Nat, Nat), (1, 2), (1, 2)) := match b returning Eq(Pair(Nat, Nat), (1, 2), (1, 2)) with\n" +
        " | Bool.true => Eq.refl((1, 2))\n | Bool.false => Eq.refl(Pair.mk(1, 2))\n"
    )
    expectOnly[TypeMismatch](
      typecheckDecls("def f : Nat := {\n  let h : Eq(Pair(Nat, Nat), (1, 2), (2, 1)) := Eq.refl((1, 2))\n  0\n}\n")
    )
  }

  test("destructuring takes a pair expression apart, transparently") {
    def program(claim: String): String =
      s"def rt (a: Nat)(b: Bool): Nat := {\n  let (x, y) := (a, b)\n  let h : $claim := Eq.refl(a)\n  x\n}\n"
    typecheckDecls(program("Eq(Nat, x, a)"))
    expectOnly[TypeMismatch](typecheckDecls(program("Eq(Nat, x, 0)")))
    evaluatesTo("{\n  let (x, (y, z)) := (1, (2, 3))\n  Nat.add(x, Nat.mul(y, z))\n}\n", "7")
    evaluatesTo("{\n  let (x, y) := (1, Bool.true)\n  (y, x)\n}\n", "Pair.mk(Bool.true, 1)")
  }

  test("function types and binder groups in a term position parse as before") {
    typecheckDecls("def T : Type := (x: Nat)(y: Nat) -> Pair(Nat, Nat)\n")
    evaluatesTo(
      "def T : Type := (x: Nat)(y: Nat) -> Pair(Nat, Nat)\n\n" +
        "def f : T := fun (x: Nat)(y: Nat): Pair(Nat, Nat) => (y, x)\n\n{ f(1, 2) }",
      "Pair.mk(2, 1)"
    )
    evaluatesTo("{ (fun {A: Type}(a: A): Pair(A, A) => (a, a))(1) }", "Pair.mk(1, 1)")
  }
}
