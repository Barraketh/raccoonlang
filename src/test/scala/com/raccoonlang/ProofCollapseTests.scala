package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

/**
 * Pins the collapsed-proof representation (docs/proof-collapse.md §8): the witness invariant
 * (collapse is erasure, never creation), generic-universe non-collapse, and the diagonal-only
 * reduction rule for subsingleton elimination.
 */
class ProofCollapseTests extends munit.FunSuite {
  private def parse(src: String): CoreAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) => Elaborator.elab(value)
      case err: Failure         => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def typecheckDecls(src: String): Unit =
    try {
      Interpreter.run(parse(src))
    } catch {
      case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
    }

  private def runProgram(src: String): Value =
    try {
      Interpreter.run(parse(src)).getOrElse(fail("Program has no body"))
    } catch {
      case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
    }

  private def assertTypeError[T <: TypeError](src: String)(implicit loc: munit.Location, ct: reflect.ClassTag[T]): T =
    intercept[T] {
      Interpreter.run(parse(src))
    }

  test("proof-typed values collapse to structureless VProofs") {
    val res = runProgram(
      """
        |{
        |  Eq.refl(Nat.zero)
        |}
        |""".stripMargin
    )
    res match {
      case p: Value.VProof =>
        assertEquals(TypeChecker.inductiveFamilyOf(p.tpe).map(_.head.name), Some("Eq"))
      case other => fail(s"Expected a collapsed proof, got $other")
    }
  }

  test("unforced implicit proof params are rejected, never auto-discharged") {
    // Witness invariant: a proof-typed implicit that no later explicit argument type forces
    // cannot be reconstructed at call sites, so the def is rejected at declaration; the proof
    // obligation must never silently vanish, even when the proposition is inhabited.
    assertTypeError[NonForcedImplicitParam](
      """
        |def useProof {x: Nat}{h: Eq(Nat, x, Nat.zero)} (n: Nat): Eq(Nat, x, Nat.zero) := h
        |
        |def bad : Eq(Nat, Nat.zero, Nat.zero) := useProof(Nat.zero)
        |""".stripMargin
    )
  }

  test("instance search does not discharge proof premises from thin air") {
    // A candidate with a non-instance proof premise must not be applied to the freshened
    // placeholder of that premise: that would derive Marker from an unproven False.
    assertTypeError[NoInstanceFound](
      """
        |inductive Marker : Type
        | | mk : Marker
        |
        |def instance markerFromFalse (h: False): Marker := falseElim(h, Marker)
        |
        |def bad : Marker := derive[Marker]
        |""".stripMargin
    )
  }

  test("generic-universe bodies compare uncollapsed values correctly") {
    // At generic u, `x : A` with `A : Sort(u)` is not known to be a proof and stays an ordinary
    // value (irrelevance does not hold at generic u); instantiating at a proposition hands the
    // same body collapsed VProofs. Both must check.
    typecheckDecls(
      """
        |def genRefl {u: Level}{A: Sort(u)} (x: A): Eq(A, x, id(x)) := Eq.refl(x)
        |
        |def atProp (P: Prop)(h: P): Eq(P, h, id(h)) := genRefl(h)
        |""".stripMargin
    )
  }

  test("casts along axiom-stuck proofs stay stuck") {
    val res = runProgram(
      """
        |axiom natIsBool : Eq(Type, Nat, Bool)
        |
        |{
        |  Eq.subst(natIsBool, Level.one, fun (A: Type): Type => A, Nat.zero)
        |}
        |""".stripMargin
    )
    res match {
      case _: Value.NeutralThunk =>
      case other                 => fail(s"Expected the cast to stay stuck, got $other")
    }
  }

  test("subsingleton elimination reduces on definitionally diagonal indices") {
    // Irrelevance makes any proof of Eq(Nat, zero, zero) definitionally equal to refl, so the
    // cast reduces even though the proof is an axiom — the "Eq.rec reduces only on refl" rule
    // with refl-equality decided by the indices.
    val res = runProgram(
      """
        |axiom zeroEq : Eq(Nat, Nat.zero, Nat.zero)
        |
        |{
        |  Eq.subst(zeroEq, Level.one, fun (n: Nat): Type => Bool, Bool.true)
        |}
        |""".stripMargin
    )
    res match {
      case Value.VCtor(head, _, _) => assertEquals(head.name, "Bool.true")
      case other                   => fail(s"Expected the diagonal cast to reduce to Bool.true, got $other")
    }
  }

  test("matches on literal proof constructors do not select branches") {
    // A literal Or-proof scrutinee is a structureless VProof, so both constructors stay
    // reachable and both cases are required.
    assertTypeError[MissingCase](
      """
        |def oneSided (p: Prop)(hp: p): p := {
        |  match Or.inl(p, hp) returning p with
        |  | Or.inl l => l
        |}
        |""".stripMargin
    )
  }

  test("empty elimination on a proof hypothesis stays stuck at check time and typechecks") {
    typecheckDecls(
      """
        |def fromFalse (h: False): Nat := {
        |  match h returning Nat with
        |}
        |""".stripMargin
    )
  }

  test("materialize rebuilds a ground proof's witness under the store") {
    // The witness is excluded from synDeps, so a solved meta inside it is invisible to the
    // materialization gate; the proof must be rebuilt regardless, or quoting later reads a stale
    // witness (spurious CannotQuoteValue for a fully determined proof).
    val prop = Value.VConst("P", Value.Symbol, Value.PropTpe)
    val hole = FreshVar.freshVar("w", prop)
    val solvedWitness = Value.VProof(prop, Value.VConst("axP", Value.Symbol, prop))
    val store = EqStore.empty.allow(DepSet(hole.id)).addLink(hole.id, solvedWitness)

    ValueOps.materialize(Value.VProof(prop, hole), store) match {
      case p: Value.VProof =>
        p.witness match {
          case _: Value.VProof =>
          case other           => fail(s"Expected the witness re-materialized to the solved proof, got $other")
        }
      case other => fail(s"Expected a proof, got $other")
    }
  }

  test("let-ascribed proof values stay collapsed through evalBody") {
    // evalBody's let ascription must go through Value.ascribe (a collapse point); the putLocal
    // collapse-invariant assertion would reject an uncollapsed prop-typed binding.
    val res = runProgram(
      """
        |axiom P : Prop
        |axiom axP : P
        |
        |{
        |  let h : P := axP
        |  h
        |}
        |""".stripMargin
    )
    res match {
      case p: Value.VProof =>
        p.tpe match {
          case Value.VConst(name, _, _) => assertEquals(name, "P")
          case other                    => fail(s"Expected the proposition P, got $other")
        }
      case other => fail(s"Expected a collapsed proof of P, got $other")
    }
  }
}
