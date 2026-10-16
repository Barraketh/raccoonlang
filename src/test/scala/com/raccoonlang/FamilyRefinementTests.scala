package com.raccoonlang

class FamilyRefinementTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.default

  test("matching a proposition family at the root refines its index") {
    typecheckDecls(
      """
        |inductive IsTrue indices (b: Bool): Prop
        | | witness : IsTrue(Bool.true)
        |
        |def recoverTrueIndex (b: Bool)(h: IsTrue(b)): Eq(Bool, b, Bool.true) := {
        |  match h returning Eq(Bool, b, Bool.true) with
        |  | IsTrue.witness => Eq.refl(b)
        |}
        |""".stripMargin
    )
  }

  test("proposition families below an equality index do not refine") {
    expectTypeError[MissingCase](
      """
        |inductive IsTrue indices (b: Bool): Prop
        | | witness : IsTrue(Bool.true)
        |
        |def falseFromTypeClash
        |  (h: Eq(Prop, IsTrue(Bool.true), IsTrue(Bool.false))): False := {
        |  match h returning False with
        |}
        |""".stripMargin
    )
  }

  test("data family injectivity still refines beneath an equality family") {
    typecheckDecls(
      """
        |def listInjective (A: Type)(B: Type)(h: Eq(Type, List(A), List(B))): Eq(Type, A, B) := {
        |  match h returning Eq(Type, A, B) with
        |  | Eq.refl value => Eq.refl(A)
        |}
        |""".stripMargin
    )
  }
}
