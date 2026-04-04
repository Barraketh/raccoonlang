package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.Value.{KernelObject, PropTpe, VPi, VSort}

class PropTests extends munit.FunSuite {

  private def typecheckDecls(src: String): Unit = {
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
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  private def runProgram(src: String): Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        try {
          Interpreter.run(core).getOrElse(fail("Program has no body"))
        } catch {
          case t: TypeError =>
            val source = Source(src)
            fail(ErrorReporter.pretty(t, source))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  // Erased shape comparison helpers
  sealed trait Shape
  case class SConst(name: String) extends Shape
  case class SApp(head: Shape, args: List[Shape]) extends Shape

  private def toShape(v: Value): Shape = v match {
    case Value.ConstructorHead(n, _, _, _) => SConst(n)
    case Value.VCtor(h, fields, _) =>
      if (fields.isEmpty) SConst(h.name) else SApp(SConst(h.name), fields.toList.map(toShape))
    case Value.VConst(n, _, _)  => SConst(n)
    case Value.VApp(h, args, _) => SApp(toShape(h), args.toList.map(toShape))
    case other                  => SConst(other.toString)
  }

  private val zeroS = SConst("Nat.zero")

  // ---------------------------------------------------------------------------
  // Universe / Pi-formation tests for Prop
  // ---------------------------------------------------------------------------

  test("Prop is a classifier and has type KernelObject") {
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
      case KernelObject =>
      case other        => fail(s"Expected Prop : Sort Level.one, got: $other")
    }
  }

  test("Pi into Prop from Type stays in Prop (internal imax behavior)") {
    val res = runProgram(
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |{ (A: Type) -> Prop }
        |""".stripMargin
    )

    res match {
      case _: VPi => ()
      case other  => fail(s"Expected Pi value, got: $other")
    }

    assertEquals(res.tpe, PropTpe)
  }

  test("Dependent Pi into Prop stays in Prop") {
    val res = runProgram(
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |{ (A: Type) -> (x: A) -> Prop }
        |""".stripMargin
    )

    res match {
      case _: VPi => ()
      case other  => fail(s"Expected Pi value, got: $other")
    }

    assertEquals(res.tpe, PropTpe)
  }

  test("Pi over proof binder into Type stays in Type") {
    val res = runProgram(
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |{
        |  let F : Type := (P: Prop) -> Nat
        |  F
        |}
        |""".stripMargin
    )

    res match {
      case _: VPi => ()
      case other  => fail(s"Expected Pi value, got: $other")
    }

    res.tpe match {
      case VSort(u) => assertEquals(u, Value.Level.zero)
      case other    => fail(s"Expected (P: Prop) -> Nat to live in Type, got: $other")
    }
  }

  test("Negative: Pi into Type is not itself a proposition") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |{
        |  let bad : Prop := (A: Type) -> A
        |  bad
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[TypeMismatch] { Interpreter.run(core) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Proof binders typecheck: identity over proofs") {
    val p =
      """
        |inline def idProof (P: Prop)(p: P): P := p
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
        | | intro (p: P)(q: Q) : And P Q
        |
        |inductive Exists (A: Type)(p: A -> Prop) : Prop
        | | intro (w: A)(pw: p w) : Exists A p
        |
        |inductive HasCarrier : Prop
        | | intro (A: Type) : HasCarrier
        |
        |inductive HasSort (u: Level) : Prop
        | | intro (A: Sort u) : HasSort u
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
        val core = Elaborator.elab(value)
        intercept[NonStrictlyPositive] { Interpreter.run(core) }
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
        | | intro (p: P)(q: Q) : And P Q
        |
        |def andLeft (P: Prop)(Q: Prop)(h: And P Q): P := {
        |  match h as _ returning P with
        |  | And.intro p q => p
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("Elimination from Prop into Prop is allowed (Exists returns a proposition)") {
    val p =
      """
        |inductive Exists (A: Type)(p: A -> Prop) : Prop
        | | intro (w: A)(pw: p w) : Exists A p
        |
        |def unpackToProp (A: Type)(p: A -> Prop)(h: Exists A p): Prop := {
        |  match h as _ returning Prop with
        |  | Exists.intro w pw => p w
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("Negative: elimination from Exists into Nat is rejected") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive True : Prop
        | | intro : True
        |
        |inductive Exists (A: Type)(p: A -> Prop) : Prop
        | | intro (w: A)(pw: p w) : Exists A p
        |
        |inline def alwaysTrue (x: Nat): Prop := True
        |
        |def badExists (h: Exists Nat alwaysTrue): Nat := {
        |  match h as _ returning Nat with
        |  | Exists.intro w pw => Nat.zero
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[PropEliminationRestricted] { Interpreter.run(core) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Large elimination from Eq into Nat is allowed") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Eq (A: Type) indices (x: A) (y: A) : Prop
        | | refl (x: A) : Eq A x x
        |
        |def eqToNat (n: Nat)(p: Eq Nat n Nat.zero): Nat := {
        |  match p as _ returning Nat with
        |  | Eq.refl x => Nat.zero
        |}
        |
        |{
        |  eqToNat Nat.zero (Eq.refl Nat Nat.zero)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("Large elimination from Eq into a family in Type is allowed") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Eq (A: Type) indices (x: A) (y: A) : Prop
        | | refl (x: A) : Eq A x x
        |
        |def choose (n: Nat)(m: Nat)(p: Eq Nat n m): Type := {
        |  match p as _ returning Type with
        |  | Eq.refl x => Nat
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("Large elimination from False into Nat is allowed") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive False : Prop
        |
        |def absurdNat (h: False): Nat := {
        |  match h as _ returning Nat with
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("Large elimination from True into Nat is allowed") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive True : Prop
        | | intro : True
        |
        |def trueToNat (h: True): Nat := {
        |  match h as _ returning Nat with
        |  | True.intro => Nat.zero
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("Large elimination from indexed-empty Prop family is allowed") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive IsZero indices (n: Nat) : Prop
        | | intro : IsZero Nat.zero
        |
        |def absurdSucc (n: Nat)(h: IsZero (Nat.succ n)): Nat := {
        |  match h as _ returning Nat with
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("Large elimination is allowed when constructor field is uniquely forced by indices") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive IdxWrap (A: Type) indices (x: A) : Prop
        | | intro (y: A) : IdxWrap A y
        |
        |def unwrapIdx (n: Nat)(h: IdxWrap Nat n): Nat := {
        |  match h as _ returning Nat with
        |  | IdxWrap.intro y => y
        |}
        |
        |{
        |  unwrapIdx Nat.zero (IdxWrap.intro Nat Nat.zero)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("Large elimination is allowed when exactly one constructor is reachable at the given index") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Shape indices (n: Nat) : Prop
        | | zeroCase : Shape Nat.zero
        | | succCase (m: Nat) : Shape (Nat.succ m)
        |
        |def predFromShape (n: Nat)(h: Shape (Nat.succ n)): Nat := {
        |  match h as _ returning Nat with
        |  | Shape.succCase m => m
        |}
        |
        |{
        |  predFromShape Nat.zero (Shape.succCase Nat.zero)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("Negative: large elimination from Prop with unforced Type-valued field is rejected") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive HasCarrier : Prop
        | | intro (A: Type) : HasCarrier
        |
        |def badCarrier (h: HasCarrier): Nat := {
        |  match h as _ returning Nat with
        |  | HasCarrier.intro A => Nat.zero
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[PropEliminationRestricted] { Interpreter.run(core) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Negative: large elimination is rejected when two constructors are reachable") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Or (P: Prop)(Q: Prop) : Prop
        | | inl (p: P) : Or P Q
        | | inr (q: Q) : Or P Q
        |
        |inductive True : Prop
        | | intro : True
        |
        |def badOr (h: Or True True): Nat := {
        |  match h as _ returning Nat with
        |  | Or.inl p => Nat.zero
        |  | Or.inr q => Nat.zero
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[PropEliminationRestricted] { Interpreter.run(core) }
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
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Eq (A: Type) indices (x: A) (y: A) : Prop
        | | refl (x: A) : Eq A x x
        |
        |def symm (A: Type)(x: A)(y: A)(p: Eq A x y): Eq A y x := {
        |  match p as _ returning Eq A y x with
        |  | Eq.refl z => Eq.refl A z
        |}
        |""".stripMargin

    typecheckDecls(p)
  }
}
