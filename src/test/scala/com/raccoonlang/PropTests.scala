package com.raccoonlang

import com.raccoonlang.Value.{Level, PropTpe, VPi, VSort}

class PropTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

  // Erased shape comparison helpers
  sealed trait Shape
  case class SConst(name: String) extends Shape
  case class SApp(head: Shape, args: List[Shape]) extends Shape

  private def toShape(v: Value): Shape = v match {
    case Value.ConstructorHead(n, _, _, _, _) => SConst(n)
    case Value.VCtor(h, storedArgs, _) =>
      val args = storedArgs
      if (args.isEmpty) SConst(h.name) else SApp(SConst(h.name), args.toList.map(toShape))
    case Value.VConst(n, _, _)     => SConst(n)
    case Value.VApp(h, args, _, _) => SApp(toShape(h), args.toList.map(toShape))
    case other                     => SConst(other.toString)
  }

  private val zeroS = SConst("Peano.zero")

  // ---------------------------------------------------------------------------
  // Universe / Pi-formation tests for Prop
  // ---------------------------------------------------------------------------

  test("Prop is Sort 0 and has type Type") {
    val res = runProgram(
      """
        |{ Prop }
        |""".stripMargin
    )

    res match {
      case PropTpe => ()
      case other   => fail(s"Expected Prop classifier, got: $other")
    }

    res.tpe match {
      case VSort(u) => assertEquals(u, Value.Level.one)
      case other    => fail(s"Expected Prop : Type, got: $other")
    }
  }

  test("Pi into Prop-the-sort from Type lives in Sort 2 (Prop : Sort 1, not a proposition)") {
    val res = runProgram(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |{ (A: Type) -> Prop }
        |""".stripMargin
    )

    res match {
      case _: VPi => ()
      case other  => fail(s"Expected Pi value, got: $other")
    }

    assertEquals(res.tpe, VSort(Level.const(2)))
  }

  test("Dependent Pi into Prop-the-sort lives in Sort 2") {
    val res = runProgram(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |{ (A: Type) -> (x: A) -> Prop }
        |""".stripMargin
    )

    res match {
      case _: VPi => ()
      case other  => fail(s"Expected Pi value, got: $other")
    }

    assertEquals(res.tpe, VSort(Level.const(2)))
  }

  test("Pi over proof binder into Type stays in Type") {
    val res = runProgram(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |{
        |  let F : Type := (P: Prop) -> Peano
        |  F
        |}
        |""".stripMargin
    )

    res match {
      case _: VPi => ()
      case other  => fail(s"Expected Pi value, got: $other")
    }

    res.tpe match {
      case VSort(u) => assertEquals(u, Value.Level.one)
      case other    => fail(s"Expected (P: Prop) -> Peano to live in Type, got: $other")
    }
  }

  test("Negative: Pi into Type is not itself a proposition") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |{
        |  let bad : Prop := (A: Type) -> A
        |  bad
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[TypeMismatch] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Proof binders typecheck: identity over proofs") {
    val p =
      """
        |def idProof (P: Prop)(p: P): P := p
        |""".stripMargin

    typecheckDecls(p)
  }

  test("Proof irrelevance: distinct proofs of the same proposition are definitionally equal") {
    val p =
      """
        |inductive Amb : Prop
        | | left : Amb
        | | right : Amb
        |
        |def sameProof (p: Amb): Eq(Amb, p, Amb.right) := Eq.refl(p)
        |""".stripMargin

    typecheckDecls(p)
  }

  // ---------------------------------------------------------------------------
  // Prop-valued inductives and impredicative constructor fields
  // ---------------------------------------------------------------------------

  test("Prop inductives: False, True, And, Exists, and large-universe fields all typecheck") {
    val p =
      """
        |inductive False : Prop
        |
        |inductive True : Prop
        | | intro : True
        |
        |inductive And (P: Prop)(Q: Prop) : Prop
        | | intro (p: P)(q: Q) : And(P, Q)
        |
        |inductive Exists (A: Type)(p: A -> Prop) : Prop
        | | intro (w: A)(pw: p(w)) : Exists(A, p)
        |
        |inductive HasCarrier : Prop
        | | intro (A: Type) : HasCarrier
        |
        |inductive HasSort (u: Level) : Prop
        | | intro (A: Sort(u)) : HasSort(u)
        |""".stripMargin

    typecheckDecls(p)
  }

  test("Negative: Prop inductives are still checked for strict positivity") {
    val p =
      """
        |inductive False : Prop
        |
        |inductive Bad : Prop
        | | mk (f: Bad -> False) : Bad
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[NonStrictlyPositive] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  // ---------------------------------------------------------------------------
  // Elimination from Prop
  // ---------------------------------------------------------------------------

  test("Elimination from Prop into Prop is allowed (And projection)") {
    val p =
      """
        |inductive And (P: Prop)(Q: Prop) : Prop
        | | intro (p: P)(q: Q) : And(P, Q)
        |
        |def andLeft (P: Prop)(Q: Prop)(h: And(P, Q)): P := {
        |  match h returning P with
        |  | And.intro p q => p
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("Pi into a proposition stays in Prop (impredicativity preserved)") {
    val res = runProgram(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |{ (n: Peano) -> Eq(Peano, n, n) }
        |""".stripMargin
    )

    assertEquals(res.tpe, PropTpe)
  }

  test("Negative: elimination from Exists into Peano is rejected") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive True : Prop
        | | intro : True
        |
        |inductive Exists (A: Type)(p: A -> Prop) : Prop
        | | intro (w: A)(pw: p(w)) : Exists(A, p)
        |
        |def alwaysTrue (x: Peano): Prop := True
        |
        |def badExists (h: Exists(Peano, alwaysTrue)): Peano := {
        |  match h returning Peano with
        |  | Exists.intro w pw => Peano.zero
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[PropEliminationRestricted] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Large elimination from Eq into Peano is allowed") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def eqToNat (n: Peano)(p: Eq(Peano, n, Peano.zero)): Peano := {
        |  match p returning Peano with
        |  | Eq.refl x => Peano.zero
        |}
        |
        |{
        |  eqToNat(Peano.zero, Eq.refl(Peano.zero))
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("Large elimination from Eq into a family in Type is allowed") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def choose (n: Peano)(m: Peano)(p: Eq(Peano, n, m)): Type := {
        |  match p returning Type with
        |  | Eq.refl x => Peano
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("Large elimination from False into Peano is allowed") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive False : Prop
        |
        |def absurdNat (h: False): Peano := {
        |  match h returning Peano with
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("Large elimination from True into Peano is allowed") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive True : Prop
        | | intro : True
        |
        |def trueToNat (h: True): Peano := {
        |  match h returning Peano with
        |  | True.intro => Peano.zero
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("Large elimination from indexed-empty Prop family is allowed") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive IsZero indices (n: Peano) : Prop
        | | intro : IsZero(Peano.zero)
        |
        |def absurdSucc (n: Peano)(h: IsZero(Peano.succ(n))): Peano := {
        |  match h returning Peano with
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("Large elimination is allowed when constructor field is uniquely forced by family arguments") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive IdxWrap (A: Type) indices (x: A) : Prop
        | | intro (y: A) : IdxWrap(A, y)
        |
        |def unwrapIdx (n: Peano)(h: IdxWrap(Peano, n)): Peano := {
        |  match h returning Peano with
        |  | IdxWrap.intro y => y
        |}
        |
        |{
        |  unwrapIdx(Peano.zero, IdxWrap.intro(Peano.zero))
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("Negative: injectively nested index is outside the simple recovery plan") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive SuccIdx indices (n: Peano) : Prop
        | | intro (k: Peano) : SuccIdx(Peano.succ(k))
        |
        |def predecessor (n: Peano)(h: SuccIdx(Peano.succ(n))): Peano := {
        |  match h returning Peano with
        |  | SuccIdx.intro k => k
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[PropEliminationRestricted] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Negative: one reachable constructor does not bypass the recovery policy") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Shape indices (n: Peano) : Prop
        | | zeroCase : Shape(Peano.zero)
        | | succCase (m: Peano) : Shape(Peano.succ(m))
        |
        |def predFromShape (n: Peano)(h: Shape(Peano.succ(n))): Peano := {
        |  match h returning Peano with
        |  | Shape.succCase m => m
        |}
        |
        |{
        |  predFromShape(Peano.zero, Shape.succCase(Peano.zero))
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[PropEliminationRestricted] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Negative: large elimination from Prop with unforced Type-valued field is rejected") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive HasCarrier : Prop
        | | intro (A: Type) : HasCarrier
        |
        |def badCarrier (h: HasCarrier): Peano := {
        |  match h returning Peano with
        |  | HasCarrier.intro A => Peano.zero
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[PropEliminationRestricted] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Negative: large elimination is rejected when two constructors are reachable") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Or (P: Prop)(Q: Prop) : Prop
        | | inl (p: P) : Or(P, Q)
        | | inr (q: Q) : Or(P, Q)
        |
        |inductive True : Prop
        | | intro : True
        |
        |def badOr (h: Or(True, True)): Peano := {
        |  match h returning Peano with
        |  | Or.inl p => Peano.zero
        |  | Or.inr q => Peano.zero
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[PropEliminationRestricted] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  // ---------------------------------------------------------------------------
  // Prop-based equality in Prop
  // ---------------------------------------------------------------------------

  test("Eq in Prop supports ordinary proof-level elimination") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def symm (A: Type)(x: A)(y: A)(p: Eq(A, x, y)): Eq(A, y, x) := {
        |  match p returning Eq(A, y, x) with
        |  | Eq.refl z => Eq.refl(z)
        |}
        |""".stripMargin

    typecheckDecls(p)
  }
}
