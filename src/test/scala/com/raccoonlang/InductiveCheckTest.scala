package com.raccoonlang

class InductiveCheckTest extends munit.FunSuite {

  private def elab(src: String): CoreAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        Elaborator.elab(value, Prelude.test)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def elabAndRun(src: String): Interpreter.Worlds =
    elab(src).decls.foldLeft(Interpreter.initialWorlds(Prelude.test)) { case (curWorlds, decl) =>
      Interpreter.evalDecl(decl, curWorlds)
    }

  private def elabAndTypecheck(src: String): Unit = {
    Interpreter.run(elab(src), Prelude.test)
    ()
  }

  test("Inductive type must be a Sort (no Pi): inductive Bad : Nat") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Bad : Nat
        | | mk : Bad
        |
        |""".stripMargin

    intercept[InductiveTypeNotASort] { elabAndTypecheck(p) }
  }

  test("Inductive type must be a Sort (Pi case): inductive Bad(A: Type) : A") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Bad(A: Type) : A
        | | mk{A: Type}: Bad(A)
        |
        |""".stripMargin

    intercept[InductiveTypeNotASort] { elabAndTypecheck(p) }
  }

  test("Constructor result must be inductive head: ctor returns Nat, not Bad") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Bad : Type
        | | mk : Nat
        |
        |""".stripMargin

    intercept[InvalidConstructorResult] { elabAndTypecheck(p) }
  }

  test("Field universe too large: (A: Sort Level.one) in Type inductive") {
    val p =
      """
        |inductive Small : Type
        | | mk (A: Sort(Level.one)): Small
        |
        |""".stripMargin

    intercept[InductiveUniverseTooSmall] { elabAndTypecheck(p) }
  }

  test("Non-strict positivity: function-typed field with Bad in domain (f: Bad -> Bad)") {
    val p =
      """
        |inductive Bad : Type
        | | con (f: Bad -> Bad): Bad
        |
        |""".stripMargin

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
  }

  test("Non-strict positivity: aligned universes under other constructor F args (Wrap u (Bad u))") {
    val p =
      """
        |opaque def Wrap(A: Sort(Level.zero)): Sort(Level.zero) := A
        |
        |inductive Bad : Sort(Level.zero)
        | | con(x: Wrap(Bad)): Bad
        |
        |""".stripMargin

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
  }

  test("Constructor erased binders must be inductive params") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Sort(Level.one)
        | | mk {B: Type}{n: Nat}: Vec(B, n)
        |
        |""".stripMargin

    intercept[InvalidErasedConstructorBinder] { elabAndTypecheck(p) }
  }

  test("Constructor result must have full family arity") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Sort(Level.one)
        | | bad {A: Type}: Vec(A)
        |
        |""".stripMargin

    intercept[ArityMismatch] { elabAndTypecheck(p) }
  }

  test("Constructor erased binders may not bind indices") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Sort(Level.one)
        | | bad {A: Type}{n: Nat}: Vec(A, n)
        |
        |""".stripMargin

    intercept[InvalidErasedConstructorBinder] { elabAndTypecheck(p) }
  }

  test("Constructor params must come from erased binders or type-pattern captures") {
    val p =
      """
        |struct Bad (A: Type) : Sort(Level.succ(Level.one))
        | | mk (A: Type): Bad(A)
        |
        |""".stripMargin

    intercept[InvalidErasedConstructorBinder] { elabAndTypecheck(p) }
  }

  test("Constructor param witness type is checked after elaboration") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Bad (A: Type) : Type
        | | mk {A: Nat}: Bad(A)
        |
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[TypeError] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Nested strictly positive: recursive occurrence under positive List parameter") {
    val p =
      """
        |inductive List (A: Type) : Type
        | | nil {A: Type} : List(A)
        | | cons {A: Type} (head: A) (tail: List(A)) : List(A)
        |
        |inductive Tree : Type
        | | node (children: List(Tree)) : Tree
        |
        |""".stripMargin

    elabAndTypecheck(p)
  }

  test("Nested non-positive: recursive occurrence under forbidden container parameter") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive BadBox (A: Type) : Type
        | | mk {A: Type} (f: A -> Nat) : BadBox(A)
        |
        |inductive BadTree : Type
        | | node (children: BadBox(BadTree)) : BadTree
        |
        |""".stripMargin

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
  }

  test("Nested non-positive: container parameter contravariant in later family argument") {
    val p =
      """
        |inductive Box (A: Type)(F: A -> Type) : Type
        | | mk {A: Type}{F: A -> Type} : Box(A, F)
        |
        |inductive Bad : Type
        | | con (x: Box(Bad, $F)) : Bad
        |
        |""".stripMargin

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
  }

  test("Nested metadata: dependent family argument tracks its own variable") {
    val p =
      """
        |inductive Box (A: Type)(F: A -> Type) : Type
        | | mk {A: Type}{F: A -> Type} : Box(A, F)
        |
        |""".stripMargin

    elabAndRun(p).checkEnv("Box") match {
      case Value.VConst(_, Value.Inductive(meta), _) =>
        assertEquals(meta.positiveArgs, DepSet(1))
      case other => fail(s"Expected Box to be an inductive head, got $other")
    }
  }

  test("Nested non-positive: recursive occurrence in its own family argument") {
    val p =
      """
        |inductive Bad (A: Type) : Type
        | | con {A: Type} (x: Bad(Bad(A))) : Bad(A)
        |
        |""".stripMargin

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
  }

  test("Nested non-positive: recursive occurrence in constructor-valued family argument") {
    val p =
      """
        |inductive BoxType : Sort(Level.succ(Level.one))
        | | tag (A: Type) : BoxType
        |
        |inductive Bad indices (t: BoxType) : Type
        | | con (anchor: Bad($t)) (x: Bad(BoxType.tag(Bad(t)))) : Bad(t)
        |
        |""".stripMargin

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
  }

  test("Nested metadata: unknown type-function head forbids dependent family argument") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |inductive Higher (F: Type -> Type) : Type
        | | mk {F: Type -> Type} (x: F(Nat)) : Higher(F)
        |
        |""".stripMargin

    elabAndRun(p).checkEnv("Higher") match {
      case Value.VConst(_, Value.Inductive(meta), _) =>
        assertEquals(meta.positiveArgs, DepSet.empty)
      case other => fail(s"Expected Higher to be an inductive head, got $other")
    }
  }

  test("Nested non-positive: opaque dependent family argument type is conservative") {
    val p =
      """
        |struct TypeBox (A: Type) : Sort(Level.succ(Level.one))
        | | mk {A: Type} (T: Type) : TypeBox(A)
        |
        |opaque def typeBox (A: Type): TypeBox(A) := TypeBox.mk(A, A)
        |
        |inductive Box (A: Type)(F: (typeBox(A).T)) : Type
        | | mk {A: Type}{F: (typeBox(A).T)} : Box(A, F)
        |
        |inductive Bad : Type
        | | con (x: Box(Bad, $F)) : Bad
        |
        |""".stripMargin

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
  }
}
