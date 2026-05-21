package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.Value.VSort

class UniverseTests extends munit.FunSuite {
  private def freshLevel(name: String): Value.Var =
    FreshVar.freshVar(name, Value.LevelTpe)

  private def runProgram(src: String): Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        try {
          Interpreter.run(core, Prelude.test).getOrElse(fail("Program has no body"))
        } catch {
          case t: TypeError =>
            val source = Source(src)
            fail(ErrorReporter.pretty(t, source))
        }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  test("Type 0 fits in Type 1 (simple ascription with inductive)") {
    val p =
      """
        |inductive Nat : Type
        |  | zero: Nat
        |  | succ (_: Nat) : Nat
        |
        |{
        |  let x : Type := Nat
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
        intercept[TypeMismatch] { Interpreter.run(core, Prelude.test) }
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

  test("def f(u: Level)(A: Sort u)(x: A): A := x; apply at u=1, A=Nat, x=Nat.zero") {
    val p =
      """
        |inductive Nat : Type
        |  | zero: Nat
        |  | succ (_: Nat) : Nat
        |
        |inline def f (u: Level)(A: Sort(u))(x: A): A := x
        |
        |{ f(Level.one, Nat, Nat.zero) }
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case v => assertEquals(PrettyPrinter.print(v), "Nat.zero")
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

  test("Function result at lower universe accepted by higher ascription (up by 2)") {
    val p =
      """
        |inductive Nat : Type
        |  | zero: Nat
        |  | succ (_: Nat) : Nat
        |
        |def up2 (u: Level)(A: Sort(u)): Sort(Level.succ(Level.succ(u))) := A
        |
        |{ up2(Level.one, Nat) }
        |""".stripMargin

    val res = runProgram(p)
    // The application stays opaque (non-inline). Just assert its type is Sort 3.
    res.tpe match {
      case Value.VSort(l) => assertEquals(l, Value.Level.succ(Value.Level.succ(Value.Level.one)))
      case other          => fail(s"Expected result type Sort 3, got: $other")
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
        intercept[TypeMismatch] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Pi formation level: (A: Prop)(x: A) -> A has type Prop") {
    val p =
      """
        |{ fun (A: Sort(Level.zero))(x: A): A => x }
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case Value.VLam(pi, _, _, _) =>
        pi.tpe match {
          case Value.VSort(u) => assertEquals(u, Value.Level.zero)
          case other          => fail(s"Expected Pi type to live in Prop, got: $other")
        }
      case other => fail(s"Expected a lambda, got: $other")
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

  // Instead of constructing Sort in term position, test level-parametric usage via a term at the appropriate level
  test("Level-parametric id at u=1 works for Nat") {
    val p =
      """
        |inductive Nat : Type
        |  | zero: Nat
        |  | succ (_: Nat) : Nat
        |
        |inline def idAt (u: Level)(A: Sort(u))(x: A): A := x
        |
        |{ idAt(Level.one, Nat, Nat.zero) }
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(PrettyPrinter.print(res), "Nat.zero")
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
    implicit val eqStore: EqStore = EqStore.empty.allow(DepSet(u.id))

    val solved = ValueEquivalence.unify(
      VSort(Value.Level.mk(u.id)),
      VSort(Value.Level.const(1)),
      eqStore,
      Map.empty
    )

    assertEquals(solved.subst(u.id), Value.Level.const(1))
  }

  test("sort unification rejects solving u + 1 = 0") {
    val u = freshLevel("u")
    implicit val eqStore: EqStore = EqStore.empty.allow(DepSet(u.id))

    intercept[UnificationFailed] {
      ValueEquivalence.unify(
        Value.VSort(Value.Level.of(Map(u.id -> 1), 0)),
        Value.VSort(Value.Level.zero),
        eqStore,
        Map.empty
      )
    }
  }

  test("positive: capture through Level.succ in a type pattern works") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inline def idUp (A: Sort(Level.succ($u)))(x: A): A := x
        |
        |{
        |  idUp(Type, Nat)
        |}
        |""".stripMargin

    runProgram(p)
  }
}
