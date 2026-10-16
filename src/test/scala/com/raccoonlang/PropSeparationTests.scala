package com.raccoonlang

import com.raccoonlang.Value.{Level, VSort}

class PropSeparationTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.default

  test("Prop lives in data universe zero, and Type u lives in Type (succ u)") {
    val prop = runProgram("{ Prop }")
    assert(ValueEquivalence.defEq(prop.tpe, Sorts.Type))

    val typeAtOne = runProgram("{ Type { level = Level.one } }")
    typeAtOne match {
      case sort: VSort =>
        assert(!sort.isProp)
        assertEquals(sort.level, Level.one)
      case other => fail(s"Expected the Type one sort, got $other")
    }
    typeAtOne.tpe match {
      case sort: VSort =>
        assert(!sort.isProp)
        assertEquals(sort.level, Level.const(2))
      case other => fail(s"Expected Type two as the classifier, got $other")
    }
  }

  test("Pi into Prop is impredicative, and proof domains contribute no data level") {
    val intoProp = runProgram(
      """
        |{ (A: Type { level = Level.one }) -> True }
        |""".stripMargin
    )
    assert(ValueEquivalence.defEq(intoProp.tpe, Sorts.Prop))

    val overProof = runProgram(
      """
        |inductive NatLike : Type
        | | zero : NatLike
        |
        |{ (proof: True) -> NatLike }
        |""".stripMargin
    )
    assert(ValueEquivalence.defEq(overProof.tpe, Sorts.Type))
  }

  test("a data family remains data when instantiated with Prop") {
    val result = runProgram(
      """
        |inductive Box {u: Level}(A: Type { level = u }) : Type { level = u }
        | | mk (value: A) : Box(A)
        |
        |{ Box(Prop) }
        |""".stripMargin
    )

    assert(!Sorts.isProposition(result))
    assert(ValueEquivalence.defEq(result.tpe, Sorts.Type))
  }

  test("False and equality transport can target propositions") {
    typecheckDecls(
      """
        |def falseToAny (h: False)(P: Prop): P := False.elimP(h, P)
        |def eqTransport {P: Prop}{Q: Prop}(h: Eq(Prop, P, Q))(p: P): Q :=
        |  Eq.substP(h, fun (x: Prop): Prop => x, p)
        |""".stripMargin
    )
  }

  test("a proposition family with data fields cannot eliminate into data") {
    expectTypeError[PropEliminationRestricted](
      """
        |inductive HasCarrier : Prop
        | | intro (A: Type) : HasCarrier
        |
        |def bad (h: HasCarrier): Nat := {
        |  match h returning Nat with
        |  | HasCarrier.intro _ => Nat.zero
        |}
        |""".stripMargin
    )
  }

  test("a polymorphic Option proof cannot establish a false boolean equality") {
    expectTypeError[ImplicitReconstructionFailed](
      """
        |def someTrue {u: Level}{A: Type { level = u }}(a: A): Eq(Bool, Option.isSome(Option.some(a)), Bool.true) :=
        |  Eq.refl(Bool.true)
        |def noneFalse {u: Level}(A: Type { level = u }): Eq(Bool, Option.isSome(Option.none(A)), Bool.false) :=
        |  Eq.refl(Bool.false)
        |def impossible : Eq(Bool, Bool.true, Bool.false) :=
        |  Eq.trans(Eq.symm(someTrue(True.intro)), noneFalse(True))
        |""".stripMargin
    )
  }

  test("Option cannot reconstruct a data universe from a proposition") {
    expectTypeError[ImplicitReconstructionFailed](
      """
        |def bad : Option(True) := Option.none(True)
        |""".stripMargin
    )
  }

  test("a polymorphic Sum constructor clash cannot prove False without a prelude") {
    expectTypeError[ImplicitReconstructionFailed](
      """
        |inductive Eq {u: Level}(A: Type { level = u }) indices (x: A)(y: A) : Prop
        | | refl (x: A) : Eq(A, x, x)
        |
        |inductive Bottom : Prop
        |inductive UnitProof : Prop
        | | intro : UnitProof
        |
        |inductive Choice {u: Level}(A: Type { level = u }) : Type { level = u }
        | | left (x: A) : Choice(A)
        | | right (x: A) : Choice(A)
        |
        |def refute {u: Level}(A: Type { level = u })(x: A)
        |    (h: Eq(Choice(A), Choice.left(x), Choice.right(x))): Bottom := {
        |  match h returning Bottom with
        |}
        |
        |def boom : Bottom :=
        |  refute(UnitProof, UnitProof.intro, Eq.refl(Choice.left(UnitProof.intro)))
        |""".stripMargin,
      Prelude.none
    )
  }

  test("a polymorphic Sum constructor clash cannot prove False") {
    expectTypeError[ImplicitReconstructionFailed](
      """
        |def refuteClash {u: Level}(A: Type { level = u })(x: A)
        |    (h: Eq(Sum(A, A), Sum.inl(A, x), Sum.inr(A, x))): False := {
        |  match h returning False with
        |}
        |
        |def boom : False :=
        |  refuteClash(True, True.intro, Eq.refl(Sum.inl(True, True.intro)))
        |""".stripMargin
    )
  }
}
