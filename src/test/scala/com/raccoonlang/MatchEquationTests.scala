package com.raccoonlang

/**
 * A match that names its equation (docs/implemented/MATCH_EQUATION.md): `match h : e` binds `h : Eq(T, e, C(p̄, x̄))`
 * in the case of each constructor `C` with fields `x̄`, and evaluation binds it to the canonical proof where a case is
 * taken.
 */
class MatchEquationTests extends munit.FunSuite with TestSupport {

  /** A function that asks, as evidence, for the fact a test computes: `8(c + 1) ≤ n`. */
  private val needs =
    """
      |def needs (n: Nat)(c: Nat)[fits: Nat.le(Nat.mul(8, Nat.succ(c)), n)]: Nat := c
      |""".stripMargin

  private def loadFrom(evidence: String): String =
    needs +
      s"""
         |def loadFrom (n: Nat)(c: Nat)(left: Nat): Nat decreases structural(left) := {
         |  match left returning Nat with
         |  | Nat.zero => 0
         |  | Nat.succ more => {
         |    match fits : Nat.ble(Nat.mul(8, Nat.succ(c)), n) returning Nat with
         |    | Bool.true => Nat.add(needs(n, c)$evidence, loadFrom(n, Nat.succ(c), more))
         |    | Bool.false => 0
         |  }
         |}
         |""".stripMargin

  /** Four constructors, one with a field, and a test that is stuck on a computed color. */
  private val color =
    """
      |inductive Color : Type
      | | red : Color
      | | green : Color
      | | blue : Color
      | | other (n: Nat) : Color
      |
      |def isRed (c: Color): Bool := match c returning Bool with
      | | Color.red => Bool.true
      | | _ => Bool.false
      |
      |def pick (n: Nat): Color := match n returning Color with
      | | Nat.zero => Color.red
      | | Nat.succ m => Color.other(m)
      |""".stripMargin

  test("a case's equation is evidence: a structural recursion passes it on") {
    val program = loadFrom("[fits]")
    typecheckDecls(program)
    // Columns 0 … 3 fit in 32: 0 + 1 + 2 + 3.
    assert(ValueEquivalence.defEq(runProgram(program + "{ loadFrom(32, 0, 10) }\n"), runProgram("{ 6 }\n")))
    assert(ValueEquivalence.defEq(runProgram(program + "{ loadFrom(32, 0, 2) }\n"), runProgram("{ 1 }\n")))
    // Without it, the stuck test discharges nothing.
    interceptError[EvidenceNotDischarged](typecheckDecls(loadFrom("")))
  }

  test("F2: a proof about a function that matches a computed value uses the equation and Eq.subst") {
    val program =
      """
        |def g (n: Nat): Nat := {
        |  match Nat.isZero(n) returning Nat with
        |  | Bool.true => 0
        |  | Bool.false => 1
        |}
        |
        |def gOf (b: Bool): Nat := {
        |  match b returning Nat with
        |  | Bool.true => 0
        |  | Bool.false => 1
        |}
        |
        |def t (n: Nat)(h: Eq(Nat, g(n), 0)): Eq(Bool, Nat.isZero(n), Bool.true) := {
        |  match z : Nat.isZero(n) returning Eq(Bool, Nat.isZero(n), Bool.true) with
        |  | Bool.true => z
        |  | Bool.false => {
        |    let one := Eq.subst(z, Level.zero, fun (b: Bool): Prop => Eq(Nat, gOf(b), 0), h)
        |    False.elim(Nat.succNeZero(0, one), Eq(Bool, Nat.isZero(n), Bool.true))
        |  }
        |}
        |""".stripMargin
    typecheckDecls(program)
  }

  test("an indexed family is MatchEquationIndexed, located at the equation's name") {
    val source =
      """
        |inductive Shape indices (n: Nat) : Type
        | | point : Shape(Nat.zero)
        | | line (a: Nat) : Shape(Nat.succ(Nat.zero))
        |
        |def size (s: Shape(1)): Nat := match h : s returning Nat with
        | | Shape.line a => a
        |""".stripMargin
    val diagnostic = interceptDiagnostic(typecheckDecls(source))
    assertEquals(diagnostic.error, MatchEquationIndexed("Shape"))
    assertEquals(diagnostic.span.map(_.start), Some(source.indexOf("h : s")))
  }

  test("a linear scrutinee is LinearInType: its equation would hold a token") {
    val source =
      """
        |inductive Tok : Type { kind = lin }
        | | mk (n: Nat) : Tok
        |
        |def spend (t: Tok): Nat := match h : t returning Nat with
        | | Tok.mk n => n
        |""".stripMargin
    val diagnostic = interceptDiagnostic(typecheckDecls(source))
    assert(diagnostic.error.isInstanceOf[LinearInType], diagnostic.error.toString)
    assertEquals(diagnostic.span.map(_.start), Some(source.indexOf("t returning")))
    typecheckDecls(source.replace("match h : t", "match t"))
  }

  test("evaluation forces an equation only where it is looked at") {
    val code =
      color +
        """
          |def code (c: Color): Nat := match h : c returning Nat with
          | | Color.red => 1
          | | _ => 0
          |
          |def back (n: Nat): Color := match h : pick(n) returning Color with
          | | Color.other m => {
          |   match h returning Color with
          |   | Eq.refl x => x
          | }
          | | _ => Color.green
          |""".stripMargin
    // `pick(n)` is stuck while `back` is checked, so only running it binds deferred evidence, which its inner match forces.
    val runs =
      Vector("{ code(pick(3)) }" -> "{ 0 }", "{ back(0) }" -> "{ Color.green }", "{ back(3) }" -> "{ Color.other(2) }")
    val forced = runs.map { case (program, value) =>
      forcings(assert(ValueEquivalence.defEq(runProgram(code + program + "\n"), runProgram(color + value + "\n"))))
    }
    assertEquals(forced, Vector(0L, 0L, 1L))
    assertEquals(forcings(typecheckDecls(loadFrom("[fits]") + "def run : Nat := loadFrom(32, 0, 10)\n")), 0L)
  }

  test("a structure's eta view takes its one case, and two blocked matches compare with their equations") {
    val source =
      """
        |def first (p: Prod(Nat, Bool)): Nat := match h : p returning Nat with
        | | Prod.mk a b => a
        |
        |def same (p: Prod(Nat, Bool)): Eq(Nat, first(p), Prod.fst(p)) := Eq.refl(Prod.fst(p))
        |
        |def test (b: Bool): Nat := {
        |  match h : b returning Nat with
        |  | Bool.true => 1
        |  | Bool.false => 0
        |}
        |
        |def testAgain (b: Bool): Nat := {
        |  match k : b returning Nat with
        |  | Bool.true => 1
        |  | Bool.false => 0
        |}
        |
        |def agree (n: Nat): Eq(Nat, test(Nat.isZero(n)), testAgain(Nat.isZero(n))) := Eq.refl(test(Nat.isZero(n)))
        |""".stripMargin
    typecheckDecls(source)
  }

  test("a blocked match takes no case, and its residual prints `match h : e`") {
    val code =
      color +
        """
          |def code (c: Color): Nat := match h : c returning Nat with
          | | Color.red => 1
          | | _ => 0
          |""".stripMargin
    // `code(pick(n))` is stuck on `n`: no case is taken, so it is not the 0 or 1 a case would give.
    val wrong = code + "def wrong (n: Nat): Eq(Nat, code(pick(n)), 0) := Eq.refl(0)\n"
    val message = ErrorRendering.render(interceptError[TypeMismatch](typecheckDecls(wrong)), None)
    assert(message.contains("expected: Eq(Nat, match h : (match n returning Color with"), message)
    // Once the scrutinee is a constructor, its case is taken.
    assert(ValueEquivalence.defEq(runProgram(code + "{ code(pick(0)) }\n"), runProgram("{ 1 }\n")))
    assert(ValueEquivalence.defEq(runProgram(code + "{ code(pick(3)) }\n"), runProgram("{ 0 }\n")))
  }

  test("a wildcard's expansions each bind the equation at their own constructor") {
    // `Eq.refl(Bool.false)` proves `Eq(Bool, isRed(d), Bool.false)` only at a `d` that is not red, so the wildcard's
    // body checks only because each expanded case's `h` names its own constructor.
    val (red, notRed) = ("Eq(Color, pick(n), Color.red)", "Eq(Bool, isRed(pick(n)), Bool.false)")
    val goal = s"Or($red, $notRed)"
    val proof =
      "Eq.subst(Eq.symm(h), Level.zero, fun (d: Color): Prop => Eq(Bool, isRed(d), Bool.false), Eq.refl(Bool.false))"
    def source(cases: String): String =
      color + s"def notRed (n: Nat): $goal := {\n  match h : pick(n) returning $goal with\n$cases  | _ => Or.inr($red, $proof)\n}\n"
    typecheckDecls(source(s"  | Color.red => Or.inl($notRed, h)\n"))
    // Over `red` too, the body fails there, and only there.
    val diagnostics = interceptDiagnostics(typecheckDecls(source("")))
    assertEquals(
      diagnostics.map(_.frames.collect { case f: Frame.InWildcard => f }),
      Vector(Vector(Frame.InWildcard("Color.red")))
    )
  }

  test("evaluation binds the canonical proof, which a case may take apart") {
    // `h` is `Eq.refl(5)` when `back(4)` runs: its field is the scrutinee's value.
    val back =
      """
        |def back (n: Nat): Nat := {
        |  match h : Nat.add(n, 1) returning Nat with
        |  | Nat.succ m => {
        |    match h returning Nat with
        |    | Eq.refl x => x
        |  }
        |}
        |""".stripMargin
    assert(ValueEquivalence.defEq(runProgram(back + "{ back(4) }\n"), runProgram("{ 5 }\n")))
    // A wildcard's body is copied for each case it stands for, the equation of a match inside it included.
    val nested =
      color +
        """
          |def nested (c: Color)(n: Nat): Nat := match c returning Nat with
          | | Color.red => 0
          | | _ => {
          |   match k : pick(n) returning Nat with
          |   | Color.red => 1
          |   | _ => 2
          | }
          |""".stripMargin
    assert(ValueEquivalence.defEq(runProgram(nested + "{ nested(Color.blue, 0) }\n"), runProgram("{ 1 }\n")))
    assert(ValueEquivalence.defEq(runProgram(nested + "{ nested(Color.other(1), 2) }\n"), runProgram("{ 2 }\n")))
  }

  test("the equation is in scope in its cases only") {
    // Not in the scrutinee or the motive.
    val inMotive =
      "def f (b: Bool): Nat := match h : b returning Eq(Bool, b, b) with\n | Bool.true => h\n | Bool.false => h\n"
    typecheckDecls(inMotive.replace("Nat", "Eq(Bool, b, b)"))
    val motive = inMotive.replace("returning Eq(Bool, b, b)", "returning Eq(Eq(Bool, b, b), h, h)")
    assertEquals(interceptError[NotFound](typecheckDecls(motive)), NotFound("h"))
    val scrutinee = "def f (b: Bool): Nat := match h : h returning Nat with\n | Bool.true => 0\n | Bool.false => 1\n"
    assertEquals(interceptError[NotFound](typecheckDecls(scrutinee)), NotFound("h"))
    val afterwards =
      """
        |def f (b: Bool): Nat := {
        |  let n := {
        |    match h : b returning Nat with
        |    | Bool.true => 0
        |    | Bool.false => 1
        |  }
        |  h
        |}
        |""".stripMargin
    assertEquals(interceptError[NotFound](typecheckDecls(afterwards)), NotFound("h"))
    val field = "def f (n: Nat): Nat := match h : n returning Nat with\n | Nat.zero => 0\n | Nat.succ h => 1\n"
    assertEquals(interceptError[AlreadyDefined](typecheckDecls(field)), AlreadyDefined("h"))
  }

  test("the equation's Eq is the prelude's equality family, or there is none") {
    val ownEq =
      """
        |inductive Eq (A: Type) indices (x: A)(y: A) : Prop
        |
        |inductive Bool : Type
        | | true : Bool
        | | false : Bool
        |
        |def f (b: Bool): Bool := match h : b returning Bool with
        | | Bool.true => Bool.true
        | | Bool.false => Bool.false
        |""".stripMargin
    // A module's own `Eq` is no equality the kernel states equations with.
    val none = interceptError[MatchEquationUnavailable](typecheckDecls(ownEq, Prelude.none))
    assertEquals(none, MatchEquationUnavailable("the prelude declares no `Eq`"))
    // Nor is a prelude's that is not the equality family: here an empty one, which would make every `h` false.
    val (prelude, program) = ownEq.splitAt(ownEq.indexOf("def f"))
    val emptyEq =
      interceptError[MatchEquationUnavailable](typecheckDecls(program, Prelude.fromSource("emptyEq", prelude)))
    assertEquals(
      emptyEq,
      MatchEquationUnavailable(
        "the prelude's `Eq` is not a family of three parameters and two indices whose one constructor is `refl`"
      )
    )
    // A prelude's own declarations are checked before it ends, so they name no equation.
    val inPrelude = interceptError[MatchEquationUnavailable](
      Prelude.fromSource("inPrelude", TestSupport.bundledPreludeSource + program).checkedEnv
    )
    assertEquals(inPrelude, MatchEquationUnavailable("no prelude has finished loading"))
  }
}
