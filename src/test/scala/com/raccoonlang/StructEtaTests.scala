package com.raccoonlang

import com.raccoonlang.ProgramFixtures._

/**
 * Structure eta (docs/kernel.md, "Structure eta and projections"): at a family with one constructor, no indices and no
 * recursive field, outside `Prop`, a value converts with its constructor applied to its field projections, at every
 * kind, linear ones included; a match on a neutral value takes its one branch with those projections.
 */
class StructEtaTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = true)
  import programs._

  test("a neutral record converts with its constructor applied to its projections") {
    run(
      lnats +
        """
          |def pairEta (A: Type)(B: Type)(p: Prod(A, B)) : Eq(Prod(A, B), p, Prod.mk(A, B, p.fst, p.snd)) := Eq.refl(p)
          |def pairEtaBack (A: Type)(B: Type)(p: Prod(A, B)) : Eq(Prod(A, B), Prod.mk(A, B, p.fst, p.snd), p) := Eq.refl(p)
          |def unitEta (u: Unit) : Eq(Unit, u, Unit.unit) := Eq.refl(u)
          |def protoEta (P: Protocol.Proto) : Eq(Protocol.Proto, P, Protocol.Proto.mk(P.Atom, P.Step)) := Eq.refl(P)
          |def nested (A: Type)(p: Prod(Prod(A, A), A))
          |    : Eq(Prod(Prod(A, A), A), p, Prod.mk(Prod(A, A), A, Prod.mk(A, A, p.fst.fst, p.fst.snd), p.snd)) := Eq.refl(p)
          |""".stripMargin
    )
  }

  test("a match on a neutral record takes its branch with the projections, so destructuring computes") {
    run(
      lnats +
        """
          |def swap (A: Type)(B: Type)(p: Prod(A, B)) : Prod(B, A) := {
          |  let (a, b) := p
          |  Prod.mk(B, A, b, a)
          |}
          |def swapTwice (A: Type)(B: Type)(p: Prod(A, B)) : Eq(Prod(A, B), swap(B, A, swap(A, B, p)), p) := Eq.refl(p)
          |def firstOf (A: Type)(B: Type)(p: Prod(A, B)) : Eq(A, swap(A, B, p).snd, p.fst) := Eq.refl(p.fst)
          |""".stripMargin
    )
  }

  test("eta holds at linear and kind-polymorphic records, in types") {
    run(
      lnats +
        """
          |def linearEta (p: Prod(LNats, Nat))(h: Eq(Nat, 0, 0)) : Eq(Nat, count(p.fst), count(Prod.mk(LNats, Nat, p.fst, p.snd).fst)) :=
          |  Eq.refl(count(p.fst))
          |""".stripMargin
    )
  }

  test("unification uses eta: a constructor unifies with a neutral record field by field") {
    run(
      lnats +
        """
          |def fstOf (A: Type)(B: Type)(p: Prod(A, B))(e: Eq(Prod(A, B), Prod.mk(A, B, p.fst, p.snd), p)) : A := {
          |  match e returning A with
          |  | Eq.refl q => p.fst
          |}
          |""".stripMargin
    )
  }

  test("structural recursion may descend through a field projection") {
    run(
      lnats +
        """
          |inductive Box (A: Type) : Type
          | | mk {A: Type} (val: A) : Box(A)
          |
          |def depth (n: Nat) : Nat decreases structural(n) := {
          |  match n with
          |  | Nat.zero => 0
          |  | Nat.succ k => Nat.succ(depth(Box.mk(Nat, k).val))
          |}
          |""".stripMargin
    )
  }

  test("no eta for a Prop family, an indexed family, a recursive family, or a hidden dependency") {
    val env = declsEnv(
      lnats +
        """
          |inductive Both2 (P: Prop)(Q: Prop) : Prop
          | | intro {P: Prop}{Q: Prop} (p: P)(q: Q) : Both2(P, Q)
          |
          |inductive Tagged indices (n: Nat) : Type
          | | mk (n: Nat) : Tagged(n)
          |
          |inductive Stream : Type
          | | cons (h: Nat)(t: Nat -> Stream) : Stream
          |
          |inductive Vec (A: Type) indices (n: Nat) : Type
          | | nil {A: Type} : Vec(A, Nat.zero)
          | | cons {A: Type} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
          |
          |inductive Hidden (A: Type) : Type
          | | mk {A: Type} (v: Vec(A, $n)) : Hidden(A)
          |""".stripMargin
    )
    def eta(name: String): Boolean =
      env(name) match {
        case Value.VConst(_, Value.Inductive(meta), _) => meta.eta.isDefined
        case other                                     => fail(s"$name is $other")
      }
    assert(!eta("Both2") && !eta("Tagged") && !eta("Stream") && !eta("Hidden"))
    assert(eta("Prod") && eta("Unit") && eta("Protocol.Proto") && eta("Protocol.Observed") && eta("Protocol.Fresh"))
    // A Prop family's proofs are irrelevant instead, and an indexed one does not convert with its constructor.
    assertErrorAt[TypeMismatch](
      lnats +
        """
          |inductive Tagged indices (n: Nat) : Type
          | | mk (n: Nat) : Tagged(n)
          |
          |def bad (n: Nat)(t: Tagged(n)) : Eq(Tagged(n), t, Tagged.mk(n)) := Eq.refl(t)
          |""".stripMargin,
      "(t)",
      "Eq.refl(t)"
    )
  }

  // KERNEL_FOLLOWUPS 1.3: applying a neutral function value gives a neutral application, whatever made it neutral: a
  // stuck application of an axiom whose codomain is a function type, a stuck match, here a cast along an axiom, or a
  // projection of a call's result.
  test("applying a stuck application, a stuck match or a projection of a call is a neutral application") {
    run(
      """
        |axiom g (n: Nat): (m: Nat) -> Nat
        |
        |def h (k: Nat): Nat := g(k)(2)
        |def again (k: Nat): Eq(Nat, h(k), g(k)(2)) := Eq.refl(g(k)(2))
        |
        |def Endo : Prop := (x: True) -> True
        |axiom ax : Eq(Prop, Endo, Endo)
        |
        |def castThenApply (f: Endo)(t: True): True := Eq.mp(ax, f)(t)
        |def closed : True := castThenApply(fun (x: True): True => x, True.intro)
        |
        |inductive Fns : Type
        | | mk (f: (n: Nat) -> Nat)(g: (n: Nat) -> Nat) : Fns
        |
        |axiom make (n: Nat) : Fns
        |def first (n: Nat): Nat := make(n).f(n)
        |def firstAgain (n: Nat): Eq(Nat, first(n), make(n).f(n)) := Eq.refl(make(n).f(n))
        |
        |def Good (n: Nat): Prop := And(True, (m: Nat) -> Eq(Nat, m, m))
        |
        |def good (n: Nat): Good(n) decreases structural(n) := {
        |  match n returning Good(n) with
        |  | Nat.zero => And.intro(True, (m: Nat) -> Eq(Nat, m, m), True.intro, fun (m: Nat): Eq(Nat, m, m) => Eq.refl(m))
        |  | Nat.succ k => {
        |    let ih := good(k)
        |    And.intro(True, (m: Nat) -> Eq(Nat, m, m), True.intro, fun (m: Nat): Eq(Nat, m, m) => ih.right(m))
        |  }
        |}
        |""".stripMargin
    )
    // Distinct arguments stay apart.
    assertErrorAt[TypeMismatch](
      "axiom g (n: Nat): (m: Nat) -> Nat\n\ndef bad (k: Nat): Eq(Nat, g(k)(2), g(k)(3)) := Eq.refl(g(k)(2))\n",
      "(g(k)(2))",
      "Eq.refl(g(k)(2))"
    )
  }
}
