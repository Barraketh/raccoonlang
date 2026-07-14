package com.raccoonlang

class InductiveCheckTest extends munit.FunSuite {

  private def elab(src: String): CoreAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        Elaborator.elab(value, Prelude.test)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def elabAndRun(src: String): Env =
    elab(src).decls.foldLeft(Prelude.test.checkedEnv) { case (curEnv, decl) =>
      Interpreter.evalDecl(decl, curEnv)
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
        | | mk: Bad(A)
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

  test("Constructor result must use family params uniformly") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Sort(Level.one)
        | | mk (B: Type)(n: Nat): Vec(B, n)
        |
        |""".stripMargin

    intercept[NonUniformInductiveParam] { elabAndTypecheck(p) }
  }

  test("Constructor result must have full family arity") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Sort(Level.one)
        | | bad : Vec(A)
        |
        |""".stripMargin

    intercept[ArityMismatch] { elabAndTypecheck(p) }
  }

  test("Constructor implicit binders may bind indices after params when a field forces them") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Sort(Level.one)
        | | nil : Vec(A, Nat.zero)
        | | cons {n: Nat}(tail: Vec(A, n))(head: A): Vec(A, Nat.succ(n))
        |
        |""".stripMargin

    elabAndTypecheck(p)
  }

  test("Constructor-declared implicits must be forced by fields; family demotion does not apply") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Sort(Level.one)
        | | bad {n: Nat}: Vec(A, n)
        |
        |""".stripMargin

    intercept[NonForcedImplicitParam] { elabAndTypecheck(p) }
  }

  test("Constructor binders may not shadow family params") {
    val p =
      """
        |struct Bad (A: Type) : Sort(Level.succ(Level.one))
        | | mk (A: Type): Bad(A)
        |
        |""".stripMargin

    intercept[AlreadyDefined] { elabAndTypecheck(p) }
  }

  test("Constructor implicit binders include inductive params") {
    val p =
      """
        |inductive Bad (A: Type)(B: Type) : Sort(Level.one)
        | | inl (a: A) : Bad(A, B)
        |
        |""".stripMargin

    elabAndTypecheck(p)
  }

  test("Hidden constructor binders may not shadow family params") {
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

    intercept[AlreadyDefined] { elabAndTypecheck(p) }
  }

  test("Nested strictly positive: recursive occurrence under positive List parameter") {
    val p =
      """
        |inductive List (A: Type) : Type
        | | nil : List(A)
        | | cons (head: A) (tail: List(A)) : List(A)
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
        | | mk (f: A -> Nat) : BadBox(A)
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
        |inductive Box {u: Level}(A: Sort(u))(F: A -> Type) : Sort(Level.max(u, Level.one))
        | | mk : Box(A, F)
        |
        |inductive Bad : Sort(Level.succ(Level.one))
        | | con {F: Bad -> Type} (x: Box(Bad, F)) : Bad
        |
        |""".stripMargin

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
  }

  test("Nested metadata: dependent family argument tracks its own variable") {
    val p =
      """
        |inductive Box (A: Type)(F: A -> Type) : Type
        | | mk : Box(A, F)
        |
        |""".stripMargin

    elabAndRun(p)("Box") match {
      case Value.VConst(_, Value.Inductive(meta), _) =>
        assertEquals(meta.positiveArgs, DepSet(1))
      case other => fail(s"Expected Box to be an inductive head, got $other")
    }
  }

  test("Nested non-positive: recursive occurrence in its own family argument") {
    val p =
      """
        |inductive Bad (A: Type) : Type
        | | con (x: Bad(Bad(A))) : Bad(A)
        |
        |""".stripMargin

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
  }

  test("Nested non-positive: recursive occurrence in constructor-valued family argument") {
    val p =
      """
        |inductive BoxType : Type
        | | tag (P: Prop) : BoxType
        |
        |inductive Bad indices (t: BoxType) : Prop
        | | con {t: BoxType} (anchor: Bad(t)) (x: Bad(BoxType.tag(Bad(t)))) : Bad(t)
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
        | | mk (x: F(Nat)) : Higher(F)
        |
        |""".stripMargin

    elabAndRun(p)("Higher") match {
      case Value.VConst(_, Value.Inductive(meta), _) =>
        assertEquals(meta.positiveArgs, DepSet.empty)
      case other => fail(s"Expected Higher to be an inductive head, got $other")
    }
  }

  test("Nested non-positive: opaque dependent family argument type is conservative") {
    val p =
      """
        |struct TypeBox (A: Type) : Sort(Level.succ(Level.one))
        | | mk (T: Type) : TypeBox(A)
        |
        |opaque def typeBox (A: Type): TypeBox(A) := TypeBox.mk(A, A)
        |
        |inductive Box (A: Type)(F: (typeBox(A).T)) : Type
        | | mk : Box(A, F)
        |
        |inductive Bad : Type
        | | con {F: typeBox(Bad).T} (x: Box(Bad, F)) : Bad
        |
        |""".stripMargin

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
  }
}
