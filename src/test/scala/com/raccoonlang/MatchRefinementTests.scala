package com.raccoonlang

class MatchRefinementTests extends munit.FunSuite {
  private def typecheckDecls(src: String): Unit = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        Interpreter.run(core, Prelude.test)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  test("match refinement: symmEq over neutral VApp scrut succeeds") {
    val p =
      """
        |def symmEq (a: Nat)(b: Nat)(p: Eq(Nat, a, b)): Eq(Nat, b, a) := {
        |  match p returning Eq(Nat, b, a) with
        |  | Eq.refl x => Eq.refl(x)
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("match refinement: congSucc via wrapped scrut succeeds") {
    val p =
      """
        |def congSucc2 (a: Nat)(b: Nat)(p: Eq(Nat, a, b)): Eq(Nat, Nat.succ(a), Nat.succ(b)) := {
        |  match p returning Eq(Nat, Nat.succ(a), Nat.succ(b)) with
        |  | Eq.refl x => Eq.refl(Nat.succ(x))
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("match refinement negative: mismatched motive (extra succ) fails (ctor scrut)") {
    val p =
      """
        |def badCongCtor (a: Nat): Eq(Nat, a, Nat.succ(a)) := {
        |  match Eq.refl(a) returning Eq(Nat, a, Nat.succ(a)) with
        |  | Eq.refl x => Eq.refl(x)
        |}
        |
        |""".stripMargin

    intercept[TypeMismatch] { typecheckDecls(p) }
  }

  test("match refinement: a level-polymorphic family parameter at its exact level on neutral Vec scrut succeeds") {
    val p =
      """
        |inductive Vec (u: Level)(A: Sort(u)) indices (n: Nat) : Sort(Level.max(Level.one, u))
        | | nil {u: Level}{A: Sort(u)} : Vec(u, A, Nat.zero)
        | | cons {u: Level}{A: Sort(u)} (n: Nat) (xs: Vec(u, A, n)) (x: A) : Vec(u, A, Nat.succ(n))
        |
        |def keepVec (n: Nat)(v: Vec(Level.zero, Nat, n)): Vec(Level.zero, Nat, n) := {
        |  match v returning Vec(Level.zero, Nat, n) with
        |  | Vec.nil => v
        |  | Vec.cons k xs x => v
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("match refinement negative: non-param erased binders are rejected") {
    val p =
      """
        |inductive Vec (A: Type) indices (n: Nat) : Type
        | | nil {A: Type} : Vec(A, Nat.zero)
        | | cons {A: Type} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |inductive Hidden (n: Nat) : Type
        | | mk {m: Nat} (x: Vec(Nat, m)) : Hidden(Nat.zero)
        |
        |def bad (w: Hidden(Nat.zero)): Vec(Nat, Nat.zero) := {
        |  match w returning Vec(Nat, Nat.zero) with
        |  | Hidden.mk x => x
        |}
        |""".stripMargin

    intercept[InvalidErasedConstructorBinder] { typecheckDecls(p) }
  }

  // A constructor's parameters are the scrutinee type's own, never unknowns, so an index equation that is stuck (here on
  // an unknown `f`) leaves each field at the scrutinee's parameters (main-new f598d033). Before, the fields were over
  // fresh parameters that nothing bound: "expected A#1, actual A#2".
  private val programs = new ProgramFixtures.Programs(Prelude.default, allowUserAxioms = false)

  private val copyableV =
    """
      |inductive V (A: Type) indices (n: Nat) : Type
      | | nil {A: Type} : V(A, Nat.zero)
      | | cons {A: Type} (tail: V(A, $n)) (head: A) : V(A, Nat.succ(n))
      |""".stripMargin

  test("a stuck index equation leaves a field at the scrutinee's type parameter") {
    def program(result: String, body: String): String =
      copyableV +
        s"""
           |def headOr (A: Type)(B: Type)(f: (m: Nat) -> Nat)(n: Nat)(v: V(A, f(n)))(d: $result): $result := {
           |  match v returning $result with
           |  | V.nil => d
           |  | V.cons tail head => $body
           |}
           |""".stripMargin
    programs.run(program("A", "head"))
    // A lambda capturing the field closes over the scrutinee's parameter.
    programs.run(program("A", "(fun (u: Unit): A => head)(Unit.unit)"))
    programs.assertErrorAt[TypeMismatch](program("B", "head"), "head", "=> head")
  }

  test("a stuck index equation leaves a field at the scrutinee's kind and level parameters") {
    // `A`'s kind and level are the scrutinee's variables: the field is of kind `k`, so it is tracked, used once here,
    // and the constructor's own captures `$k` and `$u` are solved by linking `A`.
    val kindPolymorphic =
      """
        |inductive V (A: Univ($k, $u)) indices (n: Nat) : Univ(k, u)
        | | nil {A: Univ($k, $u)} : V(A, Nat.zero)
        | | cons (head: $A in Univ($k, $u))(tail: V(A, $n)) : V(A, Nat.succ(n))
        |""".stripMargin
    def program(body: String): String =
      kindPolymorphic +
        s"""
           |def headOr (A: Univ($$k, $$u))(f: (m: Nat) -> Nat)(n: Nat)(v: V(A, f(n)))(d: A): A := {
           |  match v returning A with
           |  | V.nil => d
           |  | V.cons head tail => $body
           |}
           |""".stripMargin
    programs.run(program("head"))
    programs.assertErrorAt[LinearReused](
      kindPolymorphic +
        """
          |def pair (A: Univ($k, $u))(x: A)(y: A): Nat := 0
          |
          |def both (A: Univ($k, $u))(f: (m: Nat) -> Nat)(n: Nat)(v: V(A, f(n))): Nat := {
          |  match v returning Nat with
          |  | V.nil => 0
          |  | V.cons head tail => pair(A, head, head)
          |}
          |""".stripMargin,
      "head",
      "head)"
    )
  }

  test("a stuck index equation leaves a linear family's field at the scrutinee's parameter") {
    val linearV =
      """
        |inductive LV (A: Lin($u)) indices (n: Nat) : Lin(u)
        | | nil {A: Lin($u)} : LV(A, Nat.zero)
        | | cons {A: Lin($u)} (tail: LV(A, $n)) (head: A) : LV(A, Nat.succ(n))
        |""".stripMargin
    programs.run(
      linearV +
        """
          |def headOr (A: Lin($u))(f: (m: Nat) -> Nat)(n: Nat)(v: LV(A, f(n)))(d: A): A := {
          |  match v returning A with
          |  | LV.nil => d
          |  | LV.cons tail head => head
          |}
          |""".stripMargin
    )
  }

  test("a stuck index equation keeps every constructor's branch required") {
    def program(cases: String*): String =
      copyableV +
        """
          |def f (A: Type)(g: (m: Nat) -> Nat)(k: Nat)(v: V(A, g(k))): Unit := {
          |  match v returning Unit with
          |""".stripMargin + cases.mkString("", "\n", "\n}\n")
    val nil = "  | V.nil => Unit.unit"
    val cons = "  | V.cons tail head => Unit.unit"
    programs.run(program(nil, cons))
    intercept[MissingCase](programs.runChecked(program(nil)))
    intercept[MissingCase](programs.runChecked(program(cons)))
  }

  test("a witness narrower than its parameter is refined as an index: some(x) exists only at copyable types") {
    // `some`'s witness `$A in Sort($u)` cannot be linked to an `A: Univ($k, $u)` of variable kind; the branch's
    // refinement solves `k := copy` instead, as for an index, so the field is copyable there.
    programs.run(
      """
        |inductive CopyOpt (A: Univ($k, $u)) : Univ(k, u)
        | | none {A: Univ($k, $u)} : CopyOpt(A)
        | | some (x: $A in Sort($u)) : CopyOpt(A)
        |
        |def twice (A: Univ($k, $u))(o: CopyOpt(A)): Nat := {
        |  match o returning Nat with
        |  | CopyOpt.none => 0
        |  | CopyOpt.some x => 1
        |}
        |
        |def get (A: Type)(o: CopyOpt(A))(d: A): Prod(A, A) := {
        |  match o returning Prod(A, A) with
        |  | CopyOpt.none => Prod.mk(A, A, d, d)
        |  | CopyOpt.some x => Prod.mk(A, A, x, x)
        |}
        |""".stripMargin
    )
  }
}
