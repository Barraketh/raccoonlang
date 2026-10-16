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

  test("Prop has its own sort tag and Type follows the data universe hierarchy") {
    val p =
      """
        |def typeZeroAlias : Eq(Type { level = one }, Type, Type { level = zero }) := Eq.refl(Type)
        |{ Type }
        |""".stripMargin

    runProgram(p)
    assert(!ValueEquivalence.defEq(Sorts.Prop, Sorts.Type))
  }

  test("Type level fields name a single known field") {
    def program(typeExpr: String): String = s"def f {u: Level}(A: $typeExpr)(x: A): A := x\n"

    typecheckDecls(program("Type { level = u }"))
    assertEquals(parseFailure(program("Type {}")), "Empty field list")
    assertEquals(parseFailure(program("Type { level = u, level = u }")), "Repeated field level")
    assertEquals(parseFailure(program("Type { level = u, size = u }")), "Unknown field size")
  }

  test("Type accepts a data level field while Prop fixes the proposition sort") {
    def program(typeExpr: String): String = s"def f (A: $typeExpr)(x: A): A := x\n"

    typecheckDecls(program("Type"))
    typecheckDecls(program("Type { level = one }"))
    typecheckDecls(program("Prop"))
    assertEquals(parseFailure(program("Prop { level = zero }")), "Prop does not accept fields")
    assertEquals(parseFailure(program("Type {}")), "Empty field list")
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
        |  def keep (A: Type { level = succ(zero) })(x: A): A := x
        |}
        |
        |open Peano
        |def keep (A: Type { level = succ(zero) })(x: A): A := x
        |
        |{ keep(Type, Peano.keep(Type, Peano)) }
        |""".stripMargin

    assertEquals(PrettyPrinter.print(runProgram(p)), "Peano")
  }

  // A recursive definition's own name and its peers' are not locals, so a field's forms win over them.
  test("a field's forms win over a recursive definition's own name and its peers") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Tok : Type
        | | mk : Tok
        |
        |def succ {u: Level}(A: Type { level = succ(u) })(n: Peano): Peano decreases structural(n) :=
        |  match n returning Peano with
        |  | Peano.zero => (fun (x: Type { level = succ(u) }): Peano => Peano.zero)(A)
        |  | Peano.succ k => Peano.succ(succ(A, k))
        |
        |mutual {
        |  def lin (n: Peano): Peano decreases structural(n) := {
        |    match n returning Peano with
        |    | Peano.zero => (fun (x: Type ): Peano => Peano.zero)(Tok)
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
         |def keep ($name: Peano)(A: Type { level = succ(zero) })(x: A): A := x
         |""".stripMargin

    typecheckDecls(program("p"))
    expectOnly[TypeMismatch](typecheckDecls(program("zero")))
  }

  // The level forms are forms of the language, not functions: one exists only applied to all of its arguments.
  test("a level form is written applied to all of its arguments") {
    def program(level: String): String =
      s"def s : Type { level = succ(succ(zero)) } := Type { level = $level }\n"

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
    Vector("Type", "Prop", "Level.zero", "Level.one", "Level.succ", "Level.max").foreach { name =>
      assert(!Prelude.default.checkedEnv.globals.contains(name), s"the prelude declares $name")
    }
    def program(name: String): String =
      s"namespace Level {\n  def $name (u: Level)(A: Type { level = u }): Type { level = u } := A\n}\n"

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

  test("Type denotes data universe zero and has type Type one") {
    val p =
      """
        |{ Type }
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case sort: Value.VSort =>
        assert(!sort.isProp)
        assertEquals(sort.level, Value.Level.zero)
      case other => fail(s"Expected Type zero, got: $other")
    }

    res.tpe match {
      case sort: Value.VSort =>
        assert(!sort.isProp)
        assertEquals(sort.level, Value.Level.one)
      case other => fail(s"Expected the type of Type to be Type one, got: $other")
    }
  }

  test("a Type one value inhabits exactly Type two") {
    val p =
      """
        |{
        |  let s : Type { level = succ(succ(zero)) } := Type { level = one }
        |  s
        |}
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case sort: Value.VSort =>
        assert(!sort.isProp)
        assertEquals(sort.level, Value.Level.one)
        assert(ValueEquivalence.defEq(sort.tpe, Sorts.sort(Value.Level.const(2))))
      case other => fail(s"Expected Type one value, got: $other")
    }
  }

  test("a universe-polymorphic identity accepts Peano at universe zero") {
    val p =
      """
        |inductive Peano : Type
        |  | zero: Peano
        |  | succ (_: Peano) : Peano
        |
        |def f (u: Level)(A: Type { level = u })(x: A): A := x
        |
        |{ f(Level.zero, Peano, Peano.zero) }
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case v => assertEquals(PrettyPrinter.print(v), "Peano.zero")
    }
  }

  // Type one does not fit Type zero; checked above by the Type : Type ascription rejection.

  test("Reject lifting: data universes are exact, without cumulativity") {
    val p =
      """
        |inductive Peano : Type
        |  | zero: Peano
        |  | succ (_: Peano) : Peano
        |
        |def up2 (u: Level)(A: Type { level = u }): Type { level = succ(succ(u)) } := A
        |
        |{ up2(Level.zero, Peano) }
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[TypeMismatch] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Reject lowering: a type in a higher universe cannot inhabit the lower universe") {
    val p =
      """
        |def badDown (u: Level)(A: Type { level = succ(u) }): Type { level = u } := A
        |
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[TypeMismatch] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("a data-valued Pi over a data type stays in the data universe") {
    val p =
      """
        |{ fun (A: Type { level = zero })(x: A): A => x }
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case Value.VLam(pi, _, _) =>
        assert(!pi.isPropValued)
        assert(ValueEquivalence.defEq(pi.tpe, Sorts.sort(Value.Level.one)))
      case other => fail(s"Expected a data-valued function, got: $other")
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

  test("Level.max normalizes duplicate and smaller operands") {
    val u = Value.Level.mk(freshLevel("u").id)
    val v = Value.Level.mk(freshLevel("v").id)

    assertEquals(Value.Level.max(Vector(u, u)), u)
    assertEquals(Value.Level.max(Vector(Value.Level.zero, v)), v)
    assertEquals(Value.Level.max(Vector(Value.Level.one, Value.Level.zero)), Value.Level.one)
  }

  test("Level.max tracks dependencies and materializes solved levels") {
    val u = freshLevel("u")
    val v = freshLevel("v")
    val max = Value.Level.max(Vector(Value.Level.mk(u.id), Value.Level.mk(v.id)))

    assert(max.synDeps.contains(u.id))
    assert(max.synDeps.contains(v.id))
    assertEquals(Value.Level.singleVariableOffset(max), None)
    assertEquals(
      ValueOps.materialize(max, EqStore(Map(v.id -> Value.Level.zero), DepSet.empty)),
      Value.Level.mk(u.id)
    )
  }

  test("Level.leq handles ordinary maximum bounds") {
    val u = Value.Level.mk(freshLevel("u").id)
    val v = Value.Level.mk(freshLevel("v").id)
    val ordinaryMax = Value.Level.max(Vector(u, v))

    assert(Value.Level.leq(v, ordinaryMax))
    assert(Value.Level.leq(u, ordinaryMax))
  }

  test("maximum normalization and successful bounds are sound on small assignments") {
    val uId = freshLevel("u").id
    val vId = freshLevel("v").id
    val u = Value.Level.mk(uId)
    val v = Value.Level.mk(vId)

    def eval(level: Value.Level, assignment: Map[Value.VarId, Int]): Int = {
      val terms = level.terms.iterator.map { case (id, offset) =>
        val base = assignment(id)
        base + offset
      }
      (terms ++ Iterator.single(level.c)).max
    }

    val operands = Vector(Value.Level.zero, Value.Level.one, u, v, Value.Level.succ(u), Value.Level.max(Vector(u, v)))
    val assignments = for {
      uValue <- 0 to 2
      vValue <- 0 to 2
    } yield Map(uId -> uValue, vId -> vValue)

    operands.foreach { lhs =>
      operands.foreach { rhs =>
        val max = Value.Level.max(Vector(lhs, rhs))
        assignments.foreach { assignment =>
          assertEquals(eval(max, assignment), math.max(eval(lhs, assignment), eval(rhs, assignment)))
          if (Value.Level.leq(lhs, rhs))
            assert(
              eval(lhs, assignment) <= eval(rhs, assignment),
              s"unsound level bound $lhs <= $rhs under $assignment"
            )
        }
      }
    }
  }

  test("Prop remains a fixed sort tag under unification") {
    val u = freshLevel("u")
    val eqStore = EqStore.empty.allow(DepSet(u.id))

    assert(
      ValueEquivalence
        .tryUnify(Sorts.Prop, Sorts.Type, eqStore)
        .isLeft
    )
  }

  test("polymorphic Pi formation uses the maximum data universe") {
    val p =
      """
        |def piType {u: Level}{v: Level}(A: Type { level = u })(B: Type { level = v }): Type { level = max(u, v) } := (x: A) -> B
        |{ Type }
        |""".stripMargin

    runProgram(p)
  }

  test("multi-binder Pi formation uses the maximum of every data universe") {
    val p =
      """
        |def piType2 {u: Level}{v: Level}{w: Level}(A: Type { level = u })(B: Type { level = v })(C: Type { level = w })
        |  : Type { level = max(u, max(v, w)) } := (x: A) -> (y: B) -> C
        |
        |def piType3 {u: Level}{v: Level}{t: Level}{w: Level}
        |  (A: Type { level = u })(B: Type { level = v })(C: Type { level = t })(D: Type { level = w })
        |  : Type { level = max(u, max(v, max(t, w))) } := (x: A) -> (y: B) -> (z: C) -> D
        |{ Type }
        |""".stripMargin

    runProgram(p)
  }

  test("a polymorphic Pi inhabitant canonicalizes when its codomain resolves to Prop") {
    val p =
      """
        |inductive Truth : Prop
        | | intro : Truth
        |
        |def polyK {u: Level}(A: Type { level = u })(h: Truth): (x: A) -> Truth :=
        |  fun (_: A): Truth => h
        |
        |{ polyK(Type, Truth.intro) }
        |""".stripMargin

    runProgram(p) match {
      case Value.VLam(_, _, Value.LamBody.ProofEta) =>
      case other => fail(s"Expected the Prop-instantiated function to canonicalize to an eta-lambda, got $other")
    }
  }

  test("Level-parametric identity accepts Peano at universe zero") {
    val p =
      """
        |inductive Peano : Type
        |  | zero: Peano
        |  | succ (_: Peano) : Peano
        |
        |def idAt (u: Level)(A: Type { level = u })(x: A): A := x
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
        Sorts.sort(Value.Level.mk(u.id)),
        Sorts.sort(Value.Level.const(1)),
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
          Sorts.sort(Value.Level.of(Map(u.id -> 1), 0)),
          Sorts.sort(Value.Level.zero),
          eqStore
        )
        .isLeft
    )
  }

  test("sort unification does not invent a solution through a maximum") {
    val u = freshLevel("u")
    val v = freshLevel("v")
    val eqStore = EqStore.empty.allow(DepSet(u.id, v.id))
    val max = Value.Level.max(Vector(Value.Level.mk(u.id), Value.Level.mk(v.id)))

    assert(
      ValueEquivalence
        .tryUnify(
          Sorts.sort(max),
          Sorts.sort(Value.Level.one),
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
        |def idUp {u: Level} (A: Type { level = succ(u) })(x: A): A := x
        |
        |{
        |  idUp(Type, Peano)
        |}
        |""".stripMargin

    runProgram(p)
  }
}
