package com.raccoonlang

class PrettyPrinterTests extends munit.FunSuite {
  private def parseCore(src: String): CoreAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) => Elaborator.elab(value, Prelude.test)
      case err: Failure         => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def axiomType(src: String, name: String): CoreAst.TypeTerm =
    parseCore(src).decls
      .collectFirst { case CoreAst.Decl.AxiomDecl(n, ty, _, _) if n == name => ty }
      .getOrElse(fail(s"Expected axiom $name"))

  test("anonymous constrained capture binder prints as explicit binder") {
    val src = "axiom f : (_: $A in Type) -> A\n"
    val printed = PrettyPrinter.printTerm(axiomType(src, "f"))

    assertEquals(printed, "(_: $A in Type) -> A")
    parseCore(s"axiom g : $printed\n")

    val span = Span(0, 0)
    val ref = CoreAst.LocalRef(0, "A")
    val typeRef = ElabAst.Term.GlobalRef("Type", span)
    val constraint = ElabAst.TypePattern.Type(typeRef)
    val binder = ElabAst.Binder(
      CoreAst.LocalRef(1, "_"),
      ElabAst.BinderType.ConstrainedCapture(ref, constraint, span),
      span
    )
    val pi = ElabAst.Term.Pi(
      Vector(binder),
      ElabAst.Term.LocalRef(ref, span),
      Value.VSort(Value.Level.zero),
      span,
      NodeId.fresh()
    )

    assertEquals(PrettyPrinter.printElabTerm(pi), printed)
  }

  test("anonymous type-pattern binder prints as explicit binder") {
    val prelude =
      """
        |inductive Box (A: Type) : Type
        | | mk {A: Type} (a: A) : Box(A)
        |
        |""".stripMargin
    val printed = PrettyPrinter.printTerm(axiomType(prelude + "axiom f : (_: Box($A)) -> A\n", "f"))

    assertEquals(printed, "(_: Box($A)) -> A")
    parseCore(prelude + s"axiom g : $printed\n")
  }

  test("anonymous function domain remains parenthesized in arrow shorthand") {
    val printed = PrettyPrinter.printTerm(axiomType("axiom f : (_: Type -> Type) -> Type\n", "f"))

    assertEquals(printed, "(Type -> Type) -> Type")
    parseCore(s"axiom g : $printed\n")
  }
}

/**
 * Values in diagnostics (KERNEL_FOLLOWUPS §4, EVALUATION_AND_PORTS #9): function types, lambdas, levels, record
 * projections and stuck matches print as source-like text.
 */
class ValuePrintingTests extends munit.FunSuite {
  private val programs = new ProgramFixtures.Programs(Prelude.default, allowUserAxioms = true)
  import programs._

  private def mismatch(src: String)(implicit loc: munit.Location): String =
    intercept[TypeMismatch](runChecked(src)).getMessage

  test("a function type prints with its binders, a non-dependent one as its domain") {
    assertEquals(
      mismatch("def h (f: (xs: List($A)) -> List(A)) : (n: Nat) -> Eq(Nat, n, n) := f\n"),
      "Type mismatch: expected type: (n: Nat) -> Eq(Nat, n, n), actual: (xs: List($A)) -> List(A)"
    )
    assertEquals(
      mismatch("def h (f: Nat -> List(Nat) -> Bool) : Nat -> Nat := f\n"),
      "Type mismatch: expected type: Nat -> Nat, actual: Nat -> List(Nat) -> Bool"
    )
    // A codomain that is itself a function type is parenthesized, so the two telescopes stay apart.
    assertEquals(
      mismatch("def k (n: Nat) : (m: Nat) -> Nat := fun (m: Nat): Nat => m\ndef h : Bool := k\n"),
      "Type mismatch: expected type: Bool, actual: (n: Nat) -> ((m: Nat) -> Nat)"
    )
  }

  test("a local lambda prints with its body opened on its binders, a global function by its name") {
    assertEquals(
      mismatch("def h (n: Nat) : Bool := fun (m: Nat): Nat => Nat.add(m, n)\n"),
      "Type mismatch: expected type: Bool, actual: (m: Nat) -> Nat"
    )
    val src =
      "inductive All (p: Nat -> Prop) : Prop\n | mk {p: Nat -> Prop} : All(p)\n\ndef Small (n: Nat) : Prop := Nat.le(n, 3)\n" +
        "def h (n: Nat)(a: All(fun (m: Nat): Prop => Eq(Nat, m, n))) : All(Small) := a\n"
    val message = mismatch(src)
    assert(message.contains("All(Small)"), message)
    assert(message.matches(".*All\\(fun \\(m: Nat\\) => Eq\\(Nat, m, n#[0-9]+\\)\\).*"), message)
  }

  test("a selection from a type former names the missing constructor, and one from a function its type") {
    assertEquals(
      intercept[NotFound](runChecked("def k : Nat := Nat.foo\n")).getMessage,
      "Nat.foo not found: Nat has no constructor foo"
    )
    assertEquals(
      intercept[NotFound](runChecked("def k (f: Nat -> Nat) : Nat := f.x\n")).getMessage,
      "f.x not found: f is of type Nat -> Nat, which is no family, so has no fields"
    )
  }

  test("levels print as Level.zero, Level.succ and Level.max") {
    assertEquals(PrettyPrinter.print(Value.VSort(Value.Level.const(2))), "Sort(Level.succ(Level.one))")
    assertEquals(PrettyPrinter.print(Value.VLin(Value.Level.zero)), "Lin(Level.zero)")
    val u = FreshVar.freshVar("u", Value.LevelTpe)
    val level = Value.Level.max(Vector(Value.Level.addOffset(Value.Level.mk(u.id), 1), Value.Level.const(3)))
    assertEquals(PrettyPrinter.print(level), s"Level.max(Level.succ(u#${u.id}), Level.succ(Level.succ(Level.one)))")
  }

  // A record's projection of a neutral value used to print as `match#LocalId(…)`.
  test("a stuck projection prints as one, and another stuck match as its syntax") {
    val projected = mismatch("def f (P: Protocol.Proto)(x: P.Atom) : Nat := x\n")
    assert(projected.matches("Type mismatch: expected type: Nat, actual: P#[0-9]+\\.Atom"), projected)
    val record =
      "inductive Box : Type\n | mk (n: Nat)(b: Bool) : Box\n\ndef f (x: Box) : Eq(Nat, x.n, 0) := Eq.refl(0)\n"
    assert(mismatch(record).matches(".*Eq\\(Nat, x#[0-9]+\\.n, 0\\).*"), mismatch(record))
    val stuck =
      "def isZero (n: Nat) : Bool := {\n  match n returning Bool with\n  | Nat.zero => Bool.true\n  | Nat.succ k => Bool.false\n}\n" +
        "def f (n: Nat) : Eq(Bool, isZero(n), Bool.true) := Eq.refl(Bool.true)\n"
    val message = mismatch(stuck)
    assert(
      message.matches(
        ".*Eq\\(Bool, match n#[0-9]+ returning Bool with \\| Nat.zero => Bool.true \\| Nat.succ k => Bool.false, Bool.true\\).*"
      ),
      message
    )
  }
}
