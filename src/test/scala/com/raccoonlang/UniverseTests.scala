package com.raccoonlang

import com.raccoonlang.Value.VSort

class UniverseTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

  private def freshLevel(name: String): Value.Var =
    FreshVar.freshVar(name, Value.LevelTpe)

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
      case Value.VSort(lvl) => assertEquals(lvl, Value.Level.one)
      case other            => fail(s"Expected Type (Sort 1), got: $other")
    }

    res.tpe match {
      case Value.VSort(u1) => assertEquals(u1, Value.Level.succ(Value.Level.one))
      case other           => fail(s"Expected the type of Type to be Sort 2, got: $other")
    }
  }

  test("Ascribe higher sort: let s : Sort 2 := Type") {
    val p =
      """
        |{
        |  let s : Sort(Level.succ(Level.succ(Level.zero))) := Type
        |  s
        |}
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case Value.VSort(lvl) => assertEquals(lvl, Value.Level.one)
      case other            => fail(s"Expected Sort 1 value (Type), got: $other")
    }
  }

  test("def f(u: Level)(A: Sort u)(x: A): A := x; apply at u=1, A=Peano, x=Peano.zero") {
    val p =
      """
        |inductive Peano : Type
        |  | zero: Peano
        |  | succ (_: Peano) : Peano
        |
        |def f (u: Level)(A: Sort(u))(x: A): A := x
        |
        |{ f(Level.one, Peano, Peano.zero) }
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
        |  let s : Sort(Level.succ(Level.succ(Level.zero))) := Type
        |  s
        |}
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case Value.VSort(lvl) => assertEquals(lvl, Value.Level.one)
      case other            => fail(s"Expected Sort 1 value, got: $other")
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
        |opaque def up2 (u: Level)(A: Sort(u)): Sort(Level.succ(Level.succ(u))) := A
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
        |def badDown (u: Level)(A: Sort(Level.succ(u))): Sort(u) := A
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
        |{ fun (A: Sort(Level.zero))(x: A): A => x }
        |""".stripMargin

    val res = runProgram(p)
    // The Pi is classified in Prop, so the checked body is discarded after validation and the
    // whole function uses the canonical proof eta-lambda.
    res match {
      case Value.VLam(pi, _, Value.LamBody.ProofEta) =>
        pi.tpe match {
          case Value.VSort(u) => assertEquals(u, Value.Level.zero)
          case other          => fail(s"Expected Pi type to live in Prop, got: $other")
        }
      case other => fail(s"Expected the canonical eta-lambda for the Prop-valued Pi, got: $other")
    }
  }

  test("Level is a type and has type Type") {
    val p =
      """
        |{ Level }
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case Value.LevelTpe =>
        assertEquals(res.tpe, VSort(Value.Level.one))
      case other => fail(s"Expected Level type, got: $other")
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

  test("Level.imax applies the kernel simplification rules") {
    val u = Value.Level.mk(freshLevel("u").id)
    val v = Value.Level.mk(freshLevel("v").id)

    assertEquals(Value.Level.imax(u, Value.Level.zero), Value.Level.zero)
    assertEquals(Value.Level.imax(Value.Level.zero, v), v)
    assertEquals(Value.Level.imax(Value.Level.one, v), v)
    assertEquals(Value.Level.imax(u, u), u)
    assertEquals(
      Value.Level.imax(u, Value.Level.succ(v)),
      Value.Level.max(Vector(u, Value.Level.succ(v)))
    )
  }

  test("unresolved imax is distinct from max and tracks nested dependencies") {
    val u = freshLevel("u")
    val v = freshLevel("v")
    val imax = Value.Level.imax(Value.Level.mk(u.id), Value.Level.mk(v.id))

    assert(Value.Level.containsIMax(imax))
    assert(imax.synDeps.contains(u.id))
    assert(imax.synDeps.contains(v.id))
    assertEquals(Value.Level.singleVariableOffset(imax), None)
    assertNotEquals(imax, Value.Level.max(Vector(Value.Level.mk(u.id), Value.Level.mk(v.id))))
    assert(!ValueEquivalence.defEq(imax, Value.Level.max(Vector(Value.Level.mk(u.id), Value.Level.mk(v.id)))))
  }

  test("materialization reduces imax after its rhs level is solved") {
    val u = freshLevel("u")
    val v = freshLevel("v")
    val imax = Value.Level.imax(Value.Level.mk(u.id), Value.Level.mk(v.id))

    val atProp = ValueOps.materialize(imax, EqStore(Map(v.id -> Value.Level.zero), DepSet.empty))
    assertEquals(atProp, Value.Level.zero)

    val atType = ValueOps.materialize(imax, EqStore(Map(v.id -> Value.Level.one), DepSet.empty))
    assertEquals(atType, Value.Level.max(Vector(Value.Level.mk(u.id), Value.Level.one)))
  }

  test("Level.leq handles conservative imax bounds") {
    val u = Value.Level.mk(freshLevel("u").id)
    val v = Value.Level.mk(freshLevel("v").id)
    val imax = Value.Level.imax(u, v)
    val ordinaryMax = Value.Level.max(Vector(u, v))

    assert(Value.Level.leq(v, imax))
    assert(Value.Level.leq(imax, ordinaryMax))
    assert(!Value.Level.leq(u, imax))
  }

  test("imax normalization and successful bounds are sound on small assignments") {
    val uId = freshLevel("u").id
    val vId = freshLevel("v").id
    val u = Value.Level.mk(uId)
    val v = Value.Level.mk(vId)

    def eval(level: Value.Level, assignment: Map[Value.VarId, Int]): Int = {
      val termValues = level.terms.map { case (atom, offset) =>
        val base = atom match {
          case Value.Level.ParamAtom(id) => assignment(id)
          case Value.Level.IMaxAtom(lhs, rhs) =>
            val rhsValue = eval(rhs, assignment)
            if (rhsValue == 0) 0 else math.max(eval(lhs, assignment), rhsValue)
        }
        base + offset
      }
      (termValues.iterator ++ Iterator.single(level.c)).max
    }

    val operands = Vector(
      Value.Level.zero,
      Value.Level.one,
      u,
      v,
      Value.Level.succ(u),
      Value.Level.max(Vector(u, v)),
      Value.Level.imax(u, v),
      Value.Level.succ(Value.Level.imax(u, v)),
      Value.Level.imax(Value.Level.succ(u), v)
    )
    val assignments = for {
      uValue <- 0 to 2
      vValue <- 0 to 2
    } yield Map(uId -> uValue, vId -> vValue)

    operands.foreach { lhs =>
      operands.foreach { rhs =>
        val normalized = Value.Level.imax(lhs, rhs)
        assignments.foreach { assignment =>
          val rhsValue = eval(rhs, assignment)
          val expected = if (rhsValue == 0) 0 else math.max(eval(lhs, assignment), rhsValue)
          assertEquals(eval(normalized, assignment), expected)
          if (Value.Level.leq(lhs, rhs))
            assert(
              eval(lhs, assignment) <= rhsValue,
              s"unsound level bound $lhs <= $rhs under $assignment"
            )
        }
      }
    }
  }

  test("polymorphic Pi formation has an imax classifier") {
    val p =
      """
        |def piType {u: Level}{v: Level}(A: Sort(u))(B: Sort(v)): Sort(Level.imax(u, v)) := (x: A) -> B
        |{ Type }
        |""".stripMargin

    runProgram(p)
  }

  test("multi-binder Pi formation preserves right-nested imax classifiers") {
    val p =
      """
        |def piType2 {u: Level}{v: Level}{w: Level}(A: Sort(u))(B: Sort(v))(C: Sort(w))
        |  : Sort(Level.imax(u, Level.imax(v, w))) := (x: A) -> (y: B) -> C
        |
        |def piType3 {u: Level}{v: Level}{t: Level}{w: Level}
        |  (A: Sort(u))(B: Sort(v))(C: Sort(t))(D: Sort(w))
        |  : Sort(Level.imax(u, Level.imax(v, Level.imax(t, w)))) := (x: A) -> (y: B) -> (z: C) -> D
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
        |def polyK {u: Level}{v: Level}(A: Sort(u))(B: Sort(v))(b: B): (x: A) -> B :=
        |  fun (x: A): B => b
        |
        |{ polyK(Type, Truth, Truth.intro) }
        |""".stripMargin

    runProgram(p) match {
      case Value.VLam(_, _, Value.LamBody.ProofEta) =>
      case other => fail(s"Expected the Prop-instantiated function to canonicalize to an eta-lambda, got $other")
    }
  }

  // Instead of constructing Sort in term position, test level-parametric usage via a term at the appropriate level
  test("Level-parametric id at u=1 works for Peano") {
    val p =
      """
        |inductive Peano : Type
        |  | zero: Peano
        |  | succ (_: Peano) : Peano
        |
        |def idAt (u: Level)(A: Sort(u))(x: A): A := x
        |
        |{ idAt(Level.one, Peano, Peano.zero) }
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
        VSort(Value.Level.mk(u.id)),
        VSort(Value.Level.const(1)),
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
          Value.VSort(Value.Level.of(Map(u.id -> 1), 0)),
          Value.VSort(Value.Level.zero),
          eqStore
        )
        .isLeft
    )
  }

  test("sort unification does not invent a solution through imax") {
    val u = freshLevel("u")
    val v = freshLevel("v")
    val eqStore = EqStore.empty.allow(DepSet(u.id, v.id))
    val imax = Value.Level.imax(Value.Level.mk(u.id), Value.Level.mk(v.id))

    assert(ValueEquivalence.tryUnify(VSort(imax), VSort(Value.Level.one), eqStore).isLeft)
  }

  test("positive: implicit level through Level.succ works") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def idUp {u: Level} (A: Sort(Level.succ(u)))(x: A): A := x
        |
        |{
        |  idUp(Type, Peano)
        |}
        |""".stripMargin

    runProgram(p)
  }
}
