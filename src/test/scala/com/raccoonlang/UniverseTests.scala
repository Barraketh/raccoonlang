package com.raccoonlang

class UniverseTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

  private def freshLevel(name: String): Value.Var =
    FreshVar.freshVar(name, Value.LevelTpe)

  private def parseFailure(source: String): String =
    LanguageParser.parseProgram(source) match {
      case Failure(_, _, message) => message
      case _: Success[_]          => fail("expected a parse error")
    }

  test("Prop is separate from data universes, which begin at zero") {
    typecheckDecls("def p : Type := Prop\ndef t : Type { level = one } := Type\n")
    expectOnly[TypeMismatch](typecheckDecls("def p : Type := Type\n"))
    assert(!ValueEquivalence.defEq(Sorts.Prop, Sorts.Type))
  }

  test("Type fields are optional and Prop permits only scope") {
    def program(sort: String): String = s"def f (u: Level)(A: $sort)(x: A): A := x\n"
    typecheckDecls(program("Type { level = u}"))
    typecheckDecls(program("Type { scope = empty, level = u, kind = unr }"))
    typecheckDecls(program("Type { kind = lin }"))
    typecheckDecls("def p (P: Prop { scope = empty }): Prop := P\n")
    assertEquals(parseFailure(program("Type {}")), "Empty field list")
    assertEquals(parseFailure(program("Type { level = u, level = u}")), "Repeated field level")
    assertEquals(parseFailure(program("Type { level = u, scope = empty, scope = empty }")), "Repeated field scope")
    assertEquals(parseFailure(program("Type { level = u, size = u }")), "Unknown field size")
    assertEquals(parseFailure(program("Prop { level = zero }")), "Misplaced field level: Prop fixes the level")
    assertEquals(parseFailure(program("Prop { kind = lin }")), "Prop has no kind field")
    assert(LanguageParser.parseProgram(program("Sort { level = u }")).isInstanceOf[Failure])
    expectOnly[NotFound](typecheckDecls(program("Sort")))
    expectOnly[NotFound](typecheckDecls(program("Level.imax(u, u)")))
  }

  // A name in a sort field resolves to a local, then to one of the field's forms, then as usual.
  test("a level field resolves its forms ahead of the current namespace and the opens") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |namespace Peano {
        |  def keep (A: Type { level = zero})(x: A): A := x
        |  def two : Peano := succ(succ(zero))
        |}
        |
        |open Peano
        |def keep (A: Type { level = zero})(x: A): A := x
        |
        |{ keep(Peano, Peano.keep(Peano, two)) }
        |""".stripMargin

    assertEquals(PrettyPrinter.print(runProgram(p)), "Peano.succ(Peano.succ(Peano.zero))")
  }

  // A recursive definition's own name and its peers' are not locals, so a field's forms win over them.
  test("a field's forms win over a recursive definition's own name and its peers") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Tok : Type { kind = lin }
        | | mk : Tok
        |
        |def succ {u: Level}(A: Type { level = succ(u)})(n: Peano): Peano decreases structural(n) :=
        |  match n returning Peano with
        |  | Peano.zero => (fun (x: Type { level = succ(u)}): Peano => Peano.zero)(A)
        |  | Peano.succ k => Peano.succ(succ(A, k))
        |
        |mutual {
        |  def lin (n: Peano): Peano decreases structural(n) := {
        |    match n returning Peano with
        |    | Peano.zero => (fun (x: Type { kind = lin }): Peano => Peano.zero)(Tok)
        |    | Peano.succ k => Peano.succ(other(k))
        |  }
        |  def other (n: Peano): Peano decreases structural(n) := {
        |    match n returning Peano with
        |    | Peano.zero => Peano.zero
        |    | Peano.succ k => lin(k)
        |  }
        |}
        |
        |{ lin(succ(Type, Peano.succ(Peano.zero))) }
        |""".stripMargin

    assertEquals(PrettyPrinter.print(runProgram(p)), "Peano.succ(Peano.zero)")
  }

  test("a local shadows a level form in a sort field") {
    def program(name: String): String =
      s"""
         |inductive Peano : Type
         | | zero : Peano
         |
         |def keep ($name: Peano)(A: Type { level = zero})(x: A): A := x
         |""".stripMargin

    typecheckDecls(program("p"))
    expectOnly[TypeMismatch](typecheckDecls(program("zero")))
    // A kind form too: `lin` is the parameter, so `Kind.unr` instantiates it and an unrestricted `Peano` fits.
    val kindLocal =
      "def f (lin: Kind)(A: Type { kind = lin })(x: A): A := x\ndef g : Peano := f(Kind.unr, Peano, Peano.zero)\n"
    typecheckDecls(program("p") + kindLocal)
  }

  // The level forms are forms of the language, not functions: one exists only applied to all of its arguments.
  test("a level form is written applied to all of its arguments") {
    def program(level: String): String =
      s"def s : Type { level = succ(one)} := Type { level = $level}\n"

    typecheckDecls(program("Level.succ(Level.zero)"))
    assertEquals(
      expectOnly[ArityMismatch](typecheckDecls(program("Level.succ"))),
      ArityMismatch(1, 0, ArityMismatch.Arguments)
    )
    expectOnly[ArityMismatch](typecheckDecls(program("Level.max(Level.zero)")))
  }

  test("a form named without its arguments is applied to none of them, and reported at its name") {
    val source = "inductive Peano : Type\n | zero : Peano\n\ndef h (n: Peano): Peano := n\n{ h(Level.succ) }\n"
    val diagnostic = interceptDiagnostic(typecheckDecls(source))

    assertEquals(diagnostic.error, ArityMismatch(1, 0, ArityMismatch.Arguments))
    assertEquals(diagnostic.span.map(span => source.substring(span.start, span.end)), Some("Level.succ"))
  }

  test("the kernel owns the sort formers and level forms; the prelude declares none") {
    Vector("Sort", "Type", "Prop", "Level.zero", "Level.one", "Level.succ", "Level.max", "Level.imax").foreach { name =>
      assert(!Prelude.default.checkedEnv.globals.contains(name), s"the prelude declares $name")
    }
    def program(name: String): String =
      s"namespace Level {\n  def $name (u: Level)(A: Type { level = u}): Type { level = u} := A\n}\n"

    typecheckDecls(program("next"))
    expectOnly[AlreadyDefined](typecheckDecls(program("succ")))
  }

  test("Type 0 fits in Type 1 (simple ascription with inductive)") {
    val p =
      """
        |inductive Peano : Type
        |  | zero: Peano
        |  | succ (_: Peano) : Peano
        |
        |{
        |  let x : Type := Peano
        |  x
        |}
        |""".stripMargin

    runProgram(p)
  }

  test("Type 1 does not fit in Type 0 (let ascription fails)") {
    val p =
      """
        |{
        |  let x : Type := Type
        |  x
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[TypeMismatch] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Type is Sort Level.one and has type Sort Level.succ(Level.one)") {
    val p =
      """
        |{ Type }
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case sort: Value.VSort => assertEquals(sort.level, Value.Level.zero)
      case other             => fail(s"Expected Type (Sort 1), got: $other")
    }

    res.tpe match {
      case sort: Value.VSort => assertEquals(sort.level, Value.Level.succ(Value.Level.zero))
      case other             => fail(s"Expected the type of Type to be Sort 2, got: $other")
    }
  }

  test("Ascribe higher sort: let s : Sort 2 := Type") {
    val p =
      """
        |{
        |  let s : Type { level = succ(zero)} := Type
        |  s
        |}
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case sort: Value.VSort => assertEquals(sort.level, Value.Level.zero)
      case other             => fail(s"Expected Sort 1 value (Type), got: $other")
    }
  }

  test("def f(u: Level)(A: Sort u)(x: A): A := x; apply at u=1, A=Peano, x=Peano.zero") {
    val p =
      """
        |inductive Peano : Type
        |  | zero: Peano
        |  | succ (_: Peano) : Peano
        |
        |def f (u: Level)(A: Type { level = u})(x: A): A := x
        |
        |{ f(Level.zero, Peano, Peano.zero) }
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case v => assertEquals(PrettyPrinter.print(v), "Peano.zero")
    }
  }

  test("Cumulativity: Sort 1 fits into Sort 2 via let ascription (using Type)") {
    val p =
      """
        |{
        |  let s : Type { level = succ(zero)} := Type
        |  s
        |}
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case sort: Value.VSort => assertEquals(sort.level, Value.Level.zero)
      case other             => fail(s"Expected Sort 1 value, got: $other")
    }
  }

  // Downward non-cumulativity is covered by: Type 1 does not fit in Type 0 (let x : Type := Type fails)

  test("Reject lifting: universes are not cumulative (Sort u does not fit Sort (u+2))") {
    val p =
      """
        |inductive Peano : Type
        |  | zero: Peano
        |  | succ (_: Peano) : Peano
        |
        |def up2 (u: Level)(A: Type { level = u}): Type { level = succ(succ(u))} := A
        |
        |{ up2(Level.one, Peano) }
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[TypeMismatch] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Reject lowering: cannot return Sort (succ u) where Sort u is expected") {
    val p =
      """
        |def badDown (u: Level)(A: Type { level = succ(u)}): Type { level = u} := A
        |
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[TypeMismatch] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Pi formation level: (A: Prop)(x: A) -> A has type Prop") {
    val p =
      """
        |{ fun (A: Prop)(x: A): A => x }
        |""".stripMargin

    val res = runProgram(p)
    // The Pi is classified in Prop, so the checked body is discarded after validation and the
    // whole function uses the canonical proof eta-lambda.
    res match {
      case Value.VLam(pi, _, Value.LamBody.ProofEta) =>
        pi.tpe match {
          case sort: Value.VSort => assert(Sorts.isProp(sort))
          case other             => fail(s"Expected Pi type to live in Prop, got: $other")
        }
      case other => fail(s"Expected the canonical eta-lambda for the Prop-valued Pi, got: $other")
    }
  }

  test("Level.of enforces normalized construction") {
    val a = freshLevel("a")

    assertEquals(Value.Level.of(Map(a.id -> 3), 2), Value.Level.of(Map(a.id -> 3), 0))
    intercept[IllegalArgumentException] {
      Value.Level.of(Map(a.id -> -1), 0)
    }
    intercept[IllegalArgumentException] {
      Value.Level.const(-1)
    }
  }

  test("polymorphic data Pi formation has a max classifier") {
    val p =
      """
        |def piType {u: Level}{v: Level}(A: Type { level = u })(B: Type { level = v }): Type { level = max(u, v) } := (x: A) -> B
        |{ Type }
        |""".stripMargin

    runProgram(p)
  }

  test("multi-binder data Pi formation uses max classifiers") {
    val p =
      """
        |def piType2 {u: Level}{v: Level}{w: Level}(A: Type { level = u})(B: Type { level = v})(C: Type { level = w})
        |  : Type { level = max(u, max(v, w)) } := (x: A) -> (y: B) -> C
        |
        |def piType3 {u: Level}{v: Level}{t: Level}{w: Level}
        |  (A: Type { level = u})(B: Type { level = v})(C: Type { level = t})(D: Type { level = w})
        |  : Type { level = max(u, max(v, max(t, w))) } := (x: A) -> (y: B) -> (z: C) -> D
        |{ Type }
        |""".stripMargin

    runProgram(p)
  }

  test("data-polymorphic functions reject a proposition codomain") {
    expectOnly[ImplicitReconstructionFailed](
      typecheckDecls(
        "def polyK {u: Level}{v: Level}(A: Type { level = u })(B: Type { level = v })(b: B): (x: A) -> B := fun (x: A): B => b\ndef bad : Nat := polyK(Type, True, True.intro)\n",
        Prelude.default
      )
    )
  }

  // Instead of constructing Sort in term position, test level-parametric usage via a term at the appropriate level
  test("Level-parametric id at u=1 works for Peano") {
    val p =
      """
        |inductive Peano : Type
        |  | zero: Peano
        |  | succ (_: Peano) : Peano
        |
        |def idAt (u: Level)(A: Type { level = u})(x: A): A := x
        |
        |{ idAt(Level.zero, Peano, Peano.zero) }
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(PrettyPrinter.print(res), "Peano.zero")
  }

  test("Level.leq: constant can be covered by RHS atom") {
    val a = freshLevel("a")
    val lhs = Value.Level.const(3)
    val rhs = Value.Level.of(Map(a.id -> 5), 0)

    assert(Value.Level.leq(lhs, rhs))
  }

  test("Level.leq: atom is not covered by RHS constant") {
    val a = freshLevel("a")
    val lhs = Value.Level.of(Map(a.id -> 5), 0)
    val rhs = Value.Level.const(7)

    assert(!Value.Level.leq(lhs, rhs))
  }

  test("Level.leq: same atom with larger RHS offset succeeds") {
    val a = freshLevel("a")
    val lhs = Value.Level.of(Map(a.id -> 2), 0)
    val rhs = Value.Level.of(Map(a.id -> 5), 0)

    assert(Value.Level.leq(lhs, rhs))
  }

  test("Level.leq: same atom with smaller RHS offset fails") {
    val a = freshLevel("a")
    val lhs = Value.Level.of(Map(a.id -> 5), 0)
    val rhs = Value.Level.of(Map(a.id -> 2), 0)

    assert(!Value.Level.leq(lhs, rhs))
  }

  test("Level.leq: mixed max where RHS atom covers LHS constant and atom") {
    val a = freshLevel("a")
    val lhs = Value.Level.of(Map(a.id -> 2), 3) // max(a+2, 3)
    val rhs = Value.Level.of(Map(a.id -> 5), 0) // max(a+5)

    assert(Value.Level.leq(lhs, rhs))
  }

  test("Level.leq: unrelated RHS atom does not cover LHS atom") {
    val a = freshLevel("a")
    val b = freshLevel("b")
    val lhs = Value.Level.of(Map(a.id -> 2), 0)
    val rhs = Value.Level.of(Map(b.id -> 10), 0)

    assert(!Value.Level.leq(lhs, rhs))
  }

  test("Level.leq: multiple atoms all must be covered") {
    val a = freshLevel("a")
    val b = freshLevel("b")

    val lhs = Value.Level.of(Map(a.id -> 2, b.id -> 1), 0)
    val rhsOk = Value.Level.of(Map(a.id -> 3, b.id -> 1), 0)
    val rhsBad = Value.Level.of(Map(a.id -> 3), 0)

    assert(Value.Level.leq(lhs, rhsOk))
    assert(!Value.Level.leq(lhs, rhsBad))
  }

  test("Level.leq: constant covered by RHS constant") {
    val lhs = Value.Level.const(3)
    val rhs = Value.Level.const(5)

    assert(Value.Level.leq(lhs, rhs))
  }

  test("Level.leq: larger constant not covered by smaller RHS constant") {
    val lhs = Value.Level.const(5)
    val rhs = Value.Level.const(3)

    assert(!Value.Level.leq(lhs, rhs))
  }

  test("Level.leq: reflexive on mixed level") {
    val a = freshLevel("a")
    val lvl = Value.Level.of(Map(a.id -> 4), 0)

    assert(Value.Level.leq(lvl, lvl))
  }

  test("sort unification solves a plain level variable") {
    val u = freshLevel("u")
    val eqStore = EqStore.empty.allow(DepSet(u.id))

    val solved = ValueEquivalence
      .tryUnify(
        Sorts.sort(Value.Level.mk(u.id), Value.Kind.unr, Value.Lifetime.empty),
        Sorts.sort(Value.Level.const(1), Value.Kind.unr, Value.Lifetime.empty),
        eqStore
      )
      .getOrElse(fail("expected sort unification to solve the level variable"))

    assertEquals(solved.subst(u.id), Value.Level.const(1))
  }

  test("sort unification rejects solving u + 1 = 0") {
    val u = freshLevel("u")
    val eqStore = EqStore.empty.allow(DepSet(u.id))

    assert(
      ValueEquivalence
        .tryUnify(
          Sorts.sort(Value.Level.of(Map(u.id -> 1), 0), Value.Kind.unr, Value.Lifetime.empty),
          Sorts.sort(Value.Level.zero, Value.Kind.unr, Value.Lifetime.empty),
          eqStore
        )
        .isLeft
    )
  }

  test("positive: implicit level through Level.succ works") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def idUp {u: Level} (A: Type { level = succ(u)})(x: A): A := x
        |
        |{
        |  idUp(Type, Peano)
        |}
        |""".stripMargin

    runProgram(p)
  }
}
