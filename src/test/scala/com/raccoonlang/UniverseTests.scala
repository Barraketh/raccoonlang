package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.Value.VSort

class UniverseTests extends munit.FunSuite {
  private def runProgram(src: String): Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        try {
          Interpreter.run(core)
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
        |do {
        |  let x : Type := Nat
        |  x
        |}
        |""".stripMargin

    runProgram(p)
  }

  test("Type 1 does not fit in Type 0 (let ascription fails)") {
    val p =
      """
        |do {
        |  let x : Type := Type
        |  x
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[TypeMismatch] { Interpreter.run(core) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Type has type Sort (Level.succ Level.zero)") {
    val p =
      """
        |do { Type }
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case Value.VSort(lvl) => assertEquals(lvl, Value.Level.zero)
      case other            => fail(s"Expected Type (Sort 0), got: $other")
    }

    res.tpe match {
      case Value.VSort(u1) => assertEquals(u1, Value.Level.succ(Value.Level.zero))
      case other           => fail(s"Expected the type of Type to be Sort 1, got: $other")
    }
  }

  test("Ascribe higher sort: let s : Sort 2 := Type") {
    val p =
      """
        |do {
        |  let s : Sort (Level.succ (Level.succ Level.zero)) := Type
        |  s
        |}
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case Value.VSort(lvl) => assertEquals(lvl, Value.Level.zero)
      case other            => fail(s"Expected Sort 0 value (Type), got: $other")
    }
  }

  test("def f(u: Level)(A: Sort u)(x: A): A := x; apply at u=0, A=Nat, x=Nat.zero") {
    val p =
      """
        |inductive Nat : Type
        |  | zero: Nat
        |  | succ (_: Nat) : Nat
        |
        |inline def f (u: Level)(A: Sort u)(x: A): A := x
        |
        |do { f Level.zero Nat Nat.zero }
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case v => assertEquals(PrettyPrinter.print(v), "Nat.zero")
    }
  }

  test("Cumulativity: Sort 0 fits into Sort 2 via let ascription (using Type)") {
    val p =
      """
        |do {
        |  let s : Sort (Level.succ (Level.succ Level.zero)) := Type
        |  s
        |}
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case Value.VSort(lvl) => assertEquals(lvl, Value.Level.zero)
      case other            => fail(s"Expected Sort 0 value, got: $other")
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
        |def up2 (u: Level)(A: Sort u): Sort (Level.succ (Level.succ u)) := A
        |
        |do { up2 Level.zero Nat }
        |""".stripMargin

    val res = runProgram(p)
    // The application stays opaque (non-inline). Just assert its type is Sort 2.
    res.tpe match {
      case Value.VSort(l) => assertEquals(l, Value.Level.succ(Value.Level.succ(Value.Level.zero)))
      case other          => fail(s"Expected result type Sort 2, got: $other")
    }
  }

  test("Reject lowering: cannot return Sort (succ u) where Sort u is expected") {
    val p =
      """
        |def badDown (u: Level)(A: Sort (Level.succ u)): Sort u := A
        |
        |do { Type }
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[TypeMismatch] { Interpreter.run(core) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Pi formation level: (A: Sort 0)(x: A) -> A has type Sort 1") {
    val p =
      """
        |do { fun (A: Sort Level.zero)(x: A): A => x }
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case Value.VLam(pi, _, _, _) =>
        pi.tpe match {
          case Value.VSort(u) => assertEquals(u, Value.Level.succ(Value.Level.zero))
          case other          => fail(s"Expected Pi type to live in Sort 1, got: $other")
        }
      case other => fail(s"Expected a lambda, got: $other")
    }
  }

  test("Level is a type and has type Sort(0)") {
    val p =
      """
        |do { Level }
        |""".stripMargin

    val res = runProgram(p)
    res match {
      case Value.LevelTpe =>
        assertEquals(res.tpe, VSort(Value.Level.zero))
      case other => fail(s"Expected Level type, got: $other")
    }
  }

  // Instead of constructing Sort in term position, test level-parametric usage via a term at the appropriate level
  test("Level-parametric id at u=0 works for Nat") {
    val p =
      """
        |inductive Nat : Type
        |  | zero: Nat
        |  | succ (_: Nat) : Nat
        |
        |inline def idAt (u: Level)(A: Sort u)(x: A): A := x
        |
        |do { idAt Level.zero Nat Nat.zero }
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(PrettyPrinter.print(res), "Nat.zero")
  }

  test("Level.leq: constant can be covered by RHS atom") {
    val a = FreshVar.freshVar("a", Value.LevelTpe)
    val lhs = Value.Level(Map.empty, 3)
    val rhs = Value.Level(Map(a.id -> 5), 0)

    assert(Value.Level.leq(lhs, rhs))
  }

  test("Level.leq: atom is not covered by RHS constant") {
    val a = FreshVar.freshVar("a", Value.LevelTpe)
    val lhs = Value.Level(Map(a.id -> 5), 0)
    val rhs = Value.Level(Map.empty, 7)

    assert(!Value.Level.leq(lhs, rhs))
  }

  test("Level.leq: same atom with larger RHS offset succeeds") {
    val a = FreshVar.freshVar("a", Value.LevelTpe)
    val lhs = Value.Level(Map(a.id -> 2), 0)
    val rhs = Value.Level(Map(a.id -> 5), 0)

    assert(Value.Level.leq(lhs, rhs))
  }

  test("Level.leq: same atom with smaller RHS offset fails") {
    val a = FreshVar.freshVar("a", Value.LevelTpe)
    val lhs = Value.Level(Map(a.id -> 5), 0)
    val rhs = Value.Level(Map(a.id -> 2), 0)

    assert(!Value.Level.leq(lhs, rhs))
  }

  test("Level.leq: mixed max where RHS atom covers LHS constant and atom") {
    val a = FreshVar.freshVar("a", Value.LevelTpe)
    val lhs = Value.Level(Map(a.id -> 2), 3) // max(a+2, 3)
    val rhs = Value.Level(Map(a.id -> 5), 0) // max(a+5)

    assert(Value.Level.leq(lhs, rhs))
  }

  test("Level.leq: unrelated RHS atom does not cover LHS atom") {
    val a = FreshVar.freshVar("a", Value.LevelTpe)
    val b = FreshVar.freshVar("b", Value.LevelTpe)
    val lhs = Value.Level(Map(a.id -> 2), 0)
    val rhs = Value.Level(Map(b.id -> 10), 0)

    assert(!Value.Level.leq(lhs, rhs))
  }

  test("Level.leq: multiple atoms all must be covered") {
    val a = FreshVar.freshVar("a", Value.LevelTpe)
    val b = FreshVar.freshVar("b", Value.LevelTpe)

    val lhs = Value.Level(Map(a.id -> 2, b.id -> 1), 0)
    val rhsOk = Value.Level(Map(a.id -> 3, b.id -> 1), 0)
    val rhsBad = Value.Level(Map(a.id -> 3), 0)

    assert(Value.Level.leq(lhs, rhsOk))
    assert(!Value.Level.leq(lhs, rhsBad))
  }

  test("Level.leq: constant covered by RHS constant") {
    val lhs = Value.Level(Map.empty, 3)
    val rhs = Value.Level(Map.empty, 5)

    assert(Value.Level.leq(lhs, rhs))
  }

  test("Level.leq: larger constant not covered by smaller RHS constant") {
    val lhs = Value.Level(Map.empty, 5)
    val rhs = Value.Level(Map.empty, 3)

    assert(!Value.Level.leq(lhs, rhs))
  }

  test("Level.leq: reflexive on mixed level") {
    val a = FreshVar.freshVar("a", Value.LevelTpe)
    val lvl = Value.Level(Map(a.id -> 4), 0)

    assert(Value.Level.leq(lvl, lvl))
  }
}
