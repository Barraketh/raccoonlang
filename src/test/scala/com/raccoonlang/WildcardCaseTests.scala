package com.raccoonlang

import com.raccoonlang.ProgramFixtures._

/**
 * A wildcard case, `| _ => e` (docs/kernel.md, "Wildcard cases"; KERNEL_FOLLOWUPS 2.6): one case for each reachable
 * constructor the written cases do not name, each binding its fields anonymously and checked under its own refinement.
 */
class WildcardCaseTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs._

  private val color =
    """
      |inductive Color : Type
      | | red : Color
      | | green : Color
      | | blue : Color
      |
      |def isRed (c: Color) : Bool := {
      |  match c returning Bool with
      |  | Color.red => Bool.true
      |  | _ => Bool.false
      |}
      |""".stripMargin

  test("a wildcard stands for the constructors not named, and evaluates as the written-out match") {
    assertEquals(result(color + "\nisRed(Color.green)\n"), "Bool.false")
    assertEquals(result(color + "\nisRed(Color.red)\n"), "Bool.true")
    run(
      color +
        """
          |def written (c: Color) : Bool := {
          |  match c returning Bool with
          |  | Color.red => Bool.true
          |  | Color.green => Bool.false
          |  | Color.blue => Bool.false
          |}
          |
          |def blue : Eq(Bool, isRed(Color.blue), written(Color.blue)) := Eq.refl(Bool.false)
          |
          |def only (c: Color) : Nat := {
          |  match c returning Nat with
          |  | _ => 7
          |}
          |
          |def seven : Eq(Nat, only(Color.green), 7) := Eq.refl(7)
          |""".stripMargin
    )
  }

  test("a wildcard that stands for no constructor is RedundantCase") {
    assertErrorAt[RedundantCase](
      color +
        """
          |def all (c: Color) : Nat := {
          |  match c returning Nat with
          |  | Color.red => 0
          |  | Color.green => 1
          |  | Color.blue => 2
          |  | _ => 3
          |}
          |""".stripMargin,
      "| _ => 3\n"
    )
    // A known constructor stands alone: a wildcard after its case stands for nothing, as a case for another
    // constructor would be unreachable.
    assertErrorAt[RedundantCase](
      color + "\ndef known : Nat := {\n  match Color.red returning Nat with\n  | Color.red => 0\n  | _ => 1\n}\n",
      "| _ => 1\n"
    )
    assertEquals(result(color + "\n{\n  match Color.red returning Nat with\n  | _ => 1\n}\n"), "1")
  }

  test("a wildcard that is not last, or binds fields, is a parse error") {
    def unparsable(src: String): Unit =
      LanguageParser.parseProgram(src) match {
        case Success(_, _, _) => fail(s"parsed: $src")
        case _: Failure       =>
      }
    unparsable("def f (n: Nat) : Nat := {\n  match n returning Nat with\n  | _ => 0\n  | Nat.zero => 1\n}\n")
    unparsable("def f (n: Nat) : Nat := {\n  match n returning Nat with\n  | Nat.zero => 1\n  | _ k => 0\n}\n")
    unparsable("def f (n: Nat) : Nat := {\n  match n returning Nat with\n  | _ => 1\n  | _ => 0\n}\n")
  }

  private val vec =
    """
      |inductive Vec (A: Type) indices (n: Nat) : Type
      | | nil {A: Type} : Vec(A, Nat.zero)
      | | cons {A: Type} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
      |""".stripMargin

  test("a wildcard does not stand for a constructor apart from the scrutinee's type") {
    run(
      vec +
        """
          |def one (A: Type)(n: Nat)(v: Vec(A, Nat.succ(n))) : Nat := {
          |  match v returning Nat with
          |  | _ => 1
          |}
          |""".stripMargin
    )
    assertErrorAt[RedundantCase](
      vec +
        """
          |def two (A: Type)(n: Nat)(v: Vec(A, Nat.succ(n))) : Nat := {
          |  match v returning Nat with
          |  | Vec.cons tail head => 1
          |  | _ => 2
          |}
          |""".stripMargin,
      "| _ => 2\n"
    )
  }

  test("the wildcard's body is checked under each constructor's own refinement") {
    val tagged =
      """
        |inductive T indices (b: Bool) : Type
        | | yes : T(Bool.true)
        | | no : T(Bool.false)
        | | also (x: Nat) : T(Bool.true)
        |
        |def Choose (b: Bool) : Type := {
        |  match b returning Type with
        |  | Bool.true => Nat
        |  | Bool.false => Bool
        |}
        |""".stripMargin
    // `yes` and `also` both refine `b := true`, so `0 : Choose(true)` checks in each.
    run(
      tagged +
        """
          |def pick (b: Bool)(t: T(b)) : Choose(b) := {
          |  match t returning Choose(b) with
          |  | T.no => Bool.true
          |  | _ => 0
          |}
          |""".stripMargin
    )
    // The wildcard stands for `no` too, where `b := false` and `0` is no `Bool`.
    assertErrorAt[TypeMismatch](
      tagged +
        """
          |def bad (b: Bool)(t: T(b)) : Choose(b) := {
          |  match t returning Choose(b) with
          |  | T.yes => 0
          |  | _ => 0
          |}
          |""".stripMargin,
      "0",
      "| _ => 0"
    )
  }

  test("a wildcard drops linear fields, and a linear local is used once on each expanded path") {
    run(
      lnats +
        """
          |def isNil (xs: LNats) : Bool := {
          |  match xs returning Bool with
          |  | LNats.nil => Bool.true
          |  | _ => Bool.false
          |}
          |
          |def other (xs: LNats)(ys: LNats) : Nat := {
          |  match xs returning Nat with
          |  | LNats.nil => count(ys)
          |  | _ => count(ys)
          |}
          |""".stripMargin
    )
    assertErrorAt[LinearReused](
      lnats +
        """
          |def twice (xs: LNats)(ys: LNats) : Nat := {
          |  match xs returning Nat with
          |  | LNats.nil => 0
          |  | _ => Nat.add(count(ys), count(ys))
          |}
          |""".stripMargin,
      "ys",
      "ys))"
    )
    assertErrorAt[LinearReused](
      lnats +
        """
          |def again (xs: LNats) : Nat := {
          |  match xs returning Nat with
          |  | LNats.nil => 0
          |  | _ => count(xs)
          |}
          |""".stripMargin,
      "xs",
      "count(xs)"
    )
  }

  test("in a read extent a wildcard only reads, and each expansion keeps separation per call") {
    run(
      lnats +
        """
          |def Small (xs: LNats) : Prop := Eq(Nat, count(xs), count(xs))
          |
          |def small (xs: LNats) : Small(xs) := {
          |  match xs returning Small(xs) with
          |  | _ => Eq.refl(count(xs))
          |}
          |""".stripMargin
    )
    assertErrorAt[LinearReusedInType](
      lnats + both +
        """
          |def pairCount (p: Both(LNats, LNats)) : Nat := 0
          |
          |def Bad (xs: LNats) : Prop := {
          |  match xs returning Prop with
          |  | LNats.nil => True
          |  | _ => Eq(Nat, pairCount(Both.mk(xs, xs)), 0)
          |}
          |""".stripMargin,
      "xs",
      "xs))"
    )
  }

  test("each expansion of the wildcard's body has its own node identities") {
    val env = declsEnv(
      color +
        """
          |def lifted (c: Color) : (u: Unit) -> Color := {
          |  match c returning (u: Unit) -> Color with
          |  | Color.red => fun (u: Unit): Color => Color.red
          |  | _ => fun (u: Unit): Color => Color.blue
          |}
          |""".stripMargin
    )
    val ids = env("lifted") match {
      case Value.VLam(_, _, Value.LamBody.Core(term, _)) =>
        def lambdas(t: ElabAst.Term): Vector[NodeId] =
          t match {
            case lam: ElabAst.Term.Lam => lam.nodeId +: lambdas(lam.body)
            case m: ElabAst.Term.Match => m.cases.flatMap(c => lambdas(c.body))
            case b: ElabAst.Term.Body  => b.lets.flatMap(l => lambdas(l.value)) ++ lambdas(b.res)
            case app: ElabAst.Term.App => (app.fn +: app.args).flatMap(lambdas)
            case _                     => Vector.empty
          }
        lambdas(term.body)
      case other => fail(s"lifted is $other")
    }
    assertEquals(ids.length, 3)
    assertEquals(ids.distinct.length, 3)
  }
}
