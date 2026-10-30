package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.ProgramFixtures.{lnats, Programs}

/**
 * Adversarial review of kernel-followups-matching (8c1b4dee..d8a6f50e): branch fields at the scrutinee's parameters
 * (1.5, f007af17), wildcard cases (2.6, b2196478), match equations (2.7, 8601640c), mutual blocks and the
 * positive-argument fixed point (2.5 and 1.6, 4d75b338), and refining the scrutinee type's variables in the root link
 * (2.4, d8a6f50e).
 *
 * An attack test passes when the kernel refuses the program with the expected error; an ACCEPT of one of them would be
 * a break. CONTROL tests are sound programs the kernel must accept. OVER-REJECTION tests pin a sound program the kernel
 * refuses today; DEFECT tests pin an internal error; LIMIT tests pin an acceptance worth knowing about. No break was
 * found. The one DEFECT, mut-13, is fixed and is now a CONTROL.
 */
class MatchingAttackTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs.runChecked

  private def describe(t: Throwable, src: String): String =
    t match {
      case te: TypeError => s"${te.getClass.getSimpleName}: " + ErrorReporter.pretty(te, Source(src)).take(500)
      case other         => s"${other.getClass.getSimpleName}: ${String.valueOf(other.getMessage).take(300)}"
    }

  /** The program checks and runs with no user axioms. */
  private def accepts(src: String)(implicit loc: munit.Location): Unit =
    try { runChecked(src); () }
    catch { case t: TypeError => fail("REJECTED (should accept): " + describe(t, src)) }

  /** The program is refused with `T`; an acceptance is a break, any other refusal a misdiagnosis. */
  private def rejectsWith[T <: TypeError](src: String)(implicit loc: munit.Location, ct: reflect.ClassTag[T]): Unit =
    try {
      runChecked(src)
      fail(s"ACCEPTED (BREAK: should be rejected with ${ct.runtimeClass.getSimpleName})")
    } catch {
      case t: TypeError if ct.runtimeClass.isInstance(t) =>
      case t: TypeError => fail(s"rejected, but not with ${ct.runtimeClass.getSimpleName}: ${describe(t, src)}")
    }

  private val vec =
    """
      |inductive Vec (A: Type) indices (n: Nat) : Type
      | | nil {A: Type} : Vec(A, Nat.zero)
      | | cons {A: Type} (m: Nat)(tail: Vec(A, m)) (head: A) : Vec(A, Nat.succ(m))
      |""".stripMargin

  private val linVec =
    """
      |inductive LV (A: Lin($u)) indices (n: Nat) : Lin(u)
      | | nil {A: Lin($u)} : LV(A, Nat.zero)
      | | cons {A: Lin($u)} (m: Nat)(tail: LV(A, m)) (head: A) : LV(A, Nat.succ(m))
      |
      |inductive Both (A: Lin($u))(B: Lin($v)) : Lin(Level.max(u, v))
      | | mk (fst: $A in Lin($u))(snd: $B in Lin($v)) : Both(A, B)
      |""".stripMargin

  private val copyOpt =
    """
      |inductive CopyOpt (A: Univ($k, $u)) : Univ(k, u)
      | | none {A: Univ($k, $u)} : CopyOpt(A)
      | | some (x: $A in Sort($u)) : CopyOpt(A)
      |""".stripMargin

  private val peano =
    """
      |inductive P indices (n: Nat) : Prop
      | | z : P(0)
      | | s (n: Nat)(h: P(n)) : P(Nat.succ(n))
      |""".stripMargin

  private val color =
    """
      |inductive Color : Type
      | | red : Color
      | | green : Color
      | | blue : Color
      |""".stripMargin

  // ------------------------------------------------------------------------------------------------------------------
  // Mutual recursion (4d75b338): every call between members decreases the caller's own metric.
  // ------------------------------------------------------------------------------------------------------------------

  test("mut-1 a measure and a structural member that call each other at the same argument") {
    rejectsWith[NonDecreasingRecursiveCall](
      """
        |mutual {
        |  def f (n: Nat) : Nat decreases measure(Nat.succ(n)) := g(n)
        |
        |  def g (n: Nat) : Nat decreases structural(n) := f(n)
        |}
        |""".stripMargin
    )
  }

  test("mut-2 two constant measures that each claim to be below the other") {
    rejectsWith[NonDecreasingRecursiveCall](
      """
        |mutual {
        |  def f (n: Nat) : Nat decreases measure(5) := g(n)
        |
        |  def g (n: Nat) : Nat decreases measure(4) := f(n)
        |}
        |""".stripMargin
    )
  }

  test("mut-3 a peer called inside a returned lambda, at the lambda's own argument") {
    rejectsWith[NonDecreasingRecursiveCall](
      """
        |mutual {
        |  def f (n: Nat) : (m: Nat) -> Nat decreases structural(n) := fun (m: Nat): Nat => g(m)
        |
        |  def g (n: Nat) : Nat decreases structural(n) := f(n)(n)
        |}
        |""".stripMargin
    )
  }

  test("mut-4 a peer stored in a let, passed as a value, or eta-expanded into a higher-order function") {
    rejectsWith[CannotQuoteValue](
      """
        |mutual {
        |  def f (n: Nat) : Nat decreases structural(n) := {
        |    let h := g
        |    h(n)
        |  }
        |
        |  def g (n: Nat) : Nat decreases structural(n) := f(n)
        |}
        |""".stripMargin
    )
    rejectsWith[NonDecreasingRecursiveCall](
      """
        |def apply (h: (m: Nat) -> Nat)(n: Nat) : Nat := h(n)
        |
        |mutual {
        |  def f (n: Nat) : Nat decreases structural(n) := apply(g, n)
        |
        |  def g (n: Nat) : Nat decreases structural(n) := f(n)
        |}
        |""".stripMargin
    )
    rejectsWith[NonDecreasingRecursiveCall](
      """
        |def apply (h: (m: Nat) -> Nat)(n: Nat) : Nat := h(n)
        |
        |mutual {
        |  def f (n: Nat) : Nat decreases structural(n) := apply(fun (m: Nat): Nat => g(m), n)
        |
        |  def g (n: Nat) : Nat decreases structural(n) := f(n)
        |}
        |""".stripMargin
    )
  }

  test("mut-5 a non-decreasing peer call hidden in a type annotation") {
    rejectsWith[NonDecreasingRecursiveCall](
      """
        |mutual {
        |  def f (n: Nat) : Nat decreases structural(n) := (fun (e: Eq(Nat, g(n), g(n))): Nat => 0)(Eq.refl(g(n)))
        |
        |  def g (n: Nat) : Nat decreases structural(n) := f(n)
        |}
        |""".stripMargin
    )
  }

  test("mut-6 metrics that swap components or positions across the call, or measures over the other parameter") {
    rejectsWith[NonDecreasingRecursiveCall](
      """
        |mutual {
        |  def f (a: Nat)(b: Nat) : Nat decreases lexicographic(a, b) := {
        |    match a returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ k => g(b, k)
        |  }
        |
        |  def g (x: Nat)(y: Nat) : Nat decreases lexicographic(x, y) := f(x, y)
        |}
        |""".stripMargin
    )
    rejectsWith[NonDecreasingRecursiveCall](
      """
        |mutual {
        |  def f (a: Nat)(b: Nat) : Nat decreases structural(b) := {
        |    match b returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ k => g(Nat.succ(b), k)
        |  }
        |
        |  def g (x: Nat)(y: Nat) : Nat decreases structural(x) := f(y, x)
        |}
        |""".stripMargin
    )
    rejectsWith[NonDecreasingRecursiveCall](
      """
        |mutual {
        |  def f (a: Nat)(b: Nat) : Nat decreases measure(a) := {
        |    match b returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ k => g(k, a)
        |  }
        |
        |  def g (x: Nat)(y: Nat) : Nat decreases measure(y) := f(y, x)
        |}
        |""".stripMargin
    )
  }

  test("mut-7 a wildcard does not dodge the decrease: each expansion's call is checked") {
    rejectsWith[NonDecreasingRecursiveCall](
      """
        |mutual {
        |  def f (n: Nat) : Nat decreases structural(n) := {
        |    match n returning Nat with
        |    | Nat.zero => 0
        |    | _ => g(n)
        |  }
        |
        |  def g (n: Nat) : Nat decreases structural(n) := f(n)
        |}
        |""".stripMargin
    )
  }

  test("mut-8 a proof component and a data component across members, and a proof passed back unchanged") {
    rejectsWith[NonDecreasingRecursiveCall](
      peano +
        """
          |mutual {
          |  def f (n: Nat)(h: P(n)) : True decreases structural(h) := g(n, h)
          |
          |  def g (n: Nat)(h: P(n)) : True decreases structural(n) := f(n, h)
          |}
          |""".stripMargin
    )
    rejectsWith[NonDecreasingRecursiveCall](
      peano +
        """
          |mutual {
          |  def f (n: Nat)(h: P(n)) : True decreases structural(h) := {
          |    match h returning True with
          |    | P.z => True.intro
          |    | P.s m h2 => g(m, h2)
          |  }
          |
          |  def g (n: Nat)(h: P(n)) : True decreases structural(h) := f(n, h)
          |}
          |""".stripMargin
    )
  }

  test("mut-9 CONTROL mutual recursion over mutual indexed families at a variable index, with 2.4") {
    accepts(
      """
        |mutual {
        |  inductive EV indices (n: Nat) : Type
        |   | zero : EV(0)
        |   | succ (n: Nat)(o: OV(n)) : EV(Nat.succ(n))
        |
        |  inductive OV indices (n: Nat) : Type
        |   | succ (n: Nat)(e: EV(n)) : OV(Nat.succ(n))
        |}
        |
        |mutual {
        |  def ev (n: Nat)(e: EV(n)) : Nat decreases structural(e) := {
        |    match e returning Nat with
        |    | EV.zero => 0
        |    | EV.succ m o => Nat.succ(od(m, o))
        |  }
        |
        |  def od (n: Nat)(o: OV(n)) : Nat decreases structural(o) := {
        |    match o returning Nat with
        |    | OV.succ m e => Nat.succ(ev(m, e))
        |  }
        |}
        |
        |def two : Eq(Nat, ev(2, EV.succ(1, OV.succ(0, EV.zero))), 2) := Eq.refl(2)
        |""".stripMargin
    )
  }

  test("mut-10 CONTROL a wildcard and a match equation in a mutual member, evaluated") {
    accepts(
      """
        |mutual {
        |  def f (n: Nat) : Nat decreases structural(n) := {
        |    match h : n returning Nat with
        |    | Nat.zero => 0
        |    | _ => g(Nat.sub(n, 1))
        |  }
        |
        |  def g (n: Nat) : Nat decreases structural(n) := {
        |    match n returning Nat with
        |    | Nat.zero => 1
        |    | Nat.succ k => f(k)
        |  }
        |}
        |
        |def t : Eq(Nat, f(5), 1) := Eq.refl(1)
        |""".stripMargin
    )
  }

  test("mut-11 CONTROL a measure read through the branch's refinement") {
    accepts(
      """
        |def g (n: Nat) : Nat := Nat.add(n, 3)
        |
        |def f (n: Nat) : Nat decreases measure(g(n)) := {
        |  match h : n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => f(k)
        |}
        |""".stripMargin
    )
  }

  test("mut-12 names: a peer is reserved against fields, equations and earlier globals") {
    rejectsWith[AlreadyDefined](
      """
        |mutual {
        |  def f (n: Nat) : Nat decreases structural(n) := {
        |    match g : n returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ k => 1
        |  }
        |
        |  def g (n: Nat) : Nat decreases structural(n) := 0
        |}
        |""".stripMargin
    )
    rejectsWith[AlreadyDefined](
      """
        |mutual {
        |  def f (n: Nat) : Nat decreases structural(n) := {
        |    match n returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ g => g
        |  }
        |
        |  def g (n: Nat) : Nat decreases structural(n) := 0
        |}
        |""".stripMargin
    )
    rejectsWith[AlreadyDefined](
      "def g (n: Nat) : Nat := 7\n\nmutual {\n  def f (n: Nat) : Nat decreases structural(n) := g(n)\n\n" +
        "  def g (n: Nat) : Nat decreases structural(n) := 0\n}\n"
    )
    rejectsWith[AlreadyDefined](
      "mutual {\n  def f (n: Nat) : Nat decreases structural(n) := 0\n\n" +
        "  def f (n: Nat) : Nat decreases structural(n) := 1\n}\n"
    )
  }

  test("mut-13 CONTROL a recursive definition whose parameters are only in its declared Pi type") {
    // Once a DEFECT: the body was elaborated with no parameter slot while the checker opened the Pi, so the peer slot
    // collided (WTF "Local ref f#0 is already bound"). A recursive definition is a function, so one whose header has no
    // parameters takes its type's, unnamed, and its body is applied to them; its peers' and self's slots follow them.
    accepts(
      """
        |mutual {
        |  def f : (n: Nat) -> Nat decreases measure(1) := fun (n: Nat): Nat => g(0)
        |
        |  def g (n: Nat) : Nat decreases structural(n) := 0
        |}
        |
        |def zero : Eq(Nat, f(5), 0) := Eq.refl(0)
        |""".stripMargin
    )
    accepts(
      "def f : (n: Nat) -> Nat decreases measure(0) := fun (n: Nat): Nat => 0\n\ndef z : Eq(Nat, f(3), 0) := Eq.refl(0)\n"
    )
    // Without decreases, a header without parameters declares a constant of its type.
    accepts("def f : (n: Nat) -> Nat := fun (n: Nat): Nat => 0\n")
    // The body is applied to the parameters, so it must take them, and the call it makes must still decrease.
    rejectsWith[TypeMismatch](
      """
        |mutual {
        |  def f : (n: Nat) -> Nat decreases measure(0) := fun (b: Bool): Nat => 0
        |
        |  def g (n: Nat) : Nat decreases structural(n) := 0
        |}
        |""".stripMargin
    )
    rejectsWith[NonDecreasingRecursiveCall](
      "def f : (n: Nat) -> Nat decreases measure(0) := fun (n: Nat): Nat => f(n)\n"
    )
  }

  test("mut-14 OVER-REJECTION a proof-decreasing member cannot call a data-decreasing one, and a measure is not <") {
    // Each component compares by one order, so a proof root never has a data candidate below it.
    rejectsWith[NonDecreasingRecursiveCall](
      peano +
        """
          |mutual {
          |  def f (n: Nat)(h: P(n)) : True decreases structural(h) := {
          |    match h returning True with
          |    | P.z => True.intro
          |    | P.s m h2 => g(m, h2)
          |  }
          |
          |  def g (n: Nat)(h: P(n)) : True decreases structural(n) := f(n, h)
          |}
          |""".stripMargin
    )
    // b < k + b + 1, but the measure order is the structural subterm order.
    rejectsWith[NonDecreasingRecursiveCall](
      """
        |mutual {
        |  def f (a: Nat)(b: Nat) : Nat decreases measure(Nat.add(a, b)) := {
        |    match a returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ k => g(k, b)
        |  }
        |
        |  def g (x: Nat)(y: Nat) : Nat decreases structural(y) := f(y, x)
        |}
        |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Mutual families (4d75b338): strict positivity in every family, the fixed point of positive arguments (1.6), L1 and
  // the size rule per family, large elimination of a Prop member.
  // ------------------------------------------------------------------------------------------------------------------

  test("fam-1 a parameter negative in a sibling is not positive in the family that reaches it") {
    rejectsWith[NonStrictlyPositive](
      """
        |mutual {
        |  inductive T (X: Type) : Type
        |   | leaf {X: Type} : T(X)
        |   | node {X: Type} (u: U(X)) : T(X)
        |
        |  inductive U (X: Type) : Type
        |   | mk {X: Type} (f: (x: X) -> Nat)(t: T(X)) : U(X)
        |}
        |
        |inductive Bad : Type
        | | mk (t: T(Bad)) : Bad
        |""".stripMargin
    )
  }

  test("fam-2 CONTROL a parameter positive in every family of the block nests a later family") {
    accepts(
      """
        |mutual {
        |  inductive T (X: Type) : Type
        |   | leaf {X: Type} : T(X)
        |   | node {X: Type} (u: U(X)) : T(X)
        |
        |  inductive U (X: Type) : Type
        |   | mk {X: Type} (f: (n: Nat) -> X)(t: T(X)) : U(X)
        |}
        |
        |inductive Ok : Type
        | | leaf : Ok
        | | mk (t: T(Ok)) : Ok
        |""".stripMargin
    )
  }

  test("fam-3 the fixed point follows arguments swapped through a sibling, a nested List, and an index") {
    rejectsWith[NonStrictlyPositive](
      """
        |mutual {
        |  inductive T (X: Type)(Y: Type) : Type
        |   | leaf {X: Type}{Y: Type} : T(X, Y)
        |   | node {X: Type}{Y: Type} (u: U(Y, X)) : T(X, Y)
        |
        |  inductive U (X: Type)(Y: Type) : Type
        |   | mk {X: Type}{Y: Type} (f: (x: X) -> Nat)(t: T(Y, X)) : U(X, Y)
        |}
        |
        |inductive Bad : Type
        | | mk (t: T(Nat, Bad)) : Bad
        |""".stripMargin
    )
    rejectsWith[NonStrictlyPositive](
      """
        |inductive F (A: Type)(B: Type) : Type
        | | leaf {A: Type}{B: Type} : F(A, B)
        | | mk {A: Type}{B: Type} (f: (a: A) -> Nat)(xs: List(F(B, A))) : F(A, B)
        |
        |inductive H : Type
        | | mk (h: F(Nat, H)) : H
        |""".stripMargin
    )
    rejectsWith[NonStrictlyPositive](
      """
        |inductive F (A: Type) indices (B: Type) : Type
        | | mk {A: Type} : F(A, (a: A) -> Nat)
        |
        |inductive H : Type
        | | mk (h: F(H, (a: H) -> Nat)) : H
        |""".stripMargin
    )
  }

  test("fam-4 a block family under a sibling's negative position, nested in List, or behind a stuck computation") {
    rejectsWith[NonStrictlyPositive](
      """
        |mutual {
        |  inductive A : Type
        |   | mk (xs: List(B)) : A
        |
        |  inductive B : Type
        |   | leaf : B
        |   | mk (f: List((a: A) -> Nat)) : B
        |}
        |""".stripMargin
    )
    rejectsWith[NonStrictlyPositive](
      """
        |def Neg (b: Bool)(T: Type) : Type := {
        |  match b returning Type with
        |  | Bool.true => (t: T) -> Nat
        |  | Bool.false => T
        |}
        |
        |mutual {
        |  inductive A (b: Bool) : Type
        |   | mk {b: Bool} (x: Neg(b, B(b))) : A(b)
        |
        |  inductive B (b: Bool) : Type
        |   | leaf {b: Bool} : B(b)
        |   | mk {b: Bool} (a: A(b)) : B(b)
        |}
        |""".stripMargin
    )
  }

  test("fam-5 size per family: a low sibling reaching a high one through a function, or naming it in its header") {
    rejectsWith[InductiveUniverseTooSmall](
      """
        |mutual {
        |  inductive Small : Type
        |   | leaf : Small
        |   | mk (f: (n: Nat) -> Big) : Small
        |
        |  inductive Big : Sort(Level.one)
        |   | mk (T: Type)(s: Small) : Big
        |}
        |""".stripMargin
    )
    rejectsWith[NotFound](
      """
        |mutual {
        |  inductive Small (B: Big) : Type
        |   | mk {B: Big} : Small(B)
        |
        |  inductive Big : Sort(Level.one)
        |   | mk (T: Type) : Big
        |}
        |""".stripMargin
    )
  }

  test("fam-6 a Prop sibling holding a large field does not let a small family eliminate it") {
    rejectsWith[PropEliminationRestricted](
      """
        |mutual {
        |  inductive Small : Type
        |   | mk (p: P) : Small
        |
        |  inductive P : Prop
        |   | mk (T: Type)(s: Small) : P
        |}
        |
        |def extract (s: Small) : Type := {
        |  match s returning Type with
        |  | Small.mk p => {
        |    match p returning Type with
        |    | P.mk T s2 => T
        |  }
        |}
        |""".stripMargin
    )
  }

  test("fam-7 L1 per family: copyable or Prop families hold no linear sibling, directly, in a List, or by kind") {
    rejectsWith[LinearFieldInUnrestrictedFamily](
      """
        |mutual {
        |  inductive C : Type
        |   | nil : C
        |   | mk (g: List(L)) : C
        |
        |  inductive L : Lin(Level.zero)
        |   | mk (c: C) : L
        |}
        |""".stripMargin
    )
    rejectsWith[LinearFieldInUnrestrictedFamily](
      """
        |mutual {
        |  inductive P : Prop
        |   | mk (l: L) : P
        |
        |  inductive L : Lin(Level.zero)
        |   | stop : L
        |   | mk (p: P) : L
        |}
        |""".stripMargin
    )
    rejectsWith[LinearFieldInUnrestrictedFamily](
      """
        |mutual {
        |  inductive C (A: Univ($k, $u)) : Sort(u)
        |   | mk {A: Univ($k, $u)} (g: G(A)) : C(A)
        |
        |  inductive G (A: Univ($k, $u)) : Univ(k, u)
        |   | mk (x: $A in Univ($k, $u)) : G(A)
        |}
        |""".stripMargin
    )
  }

  test("fam-8 a mutual Prop and data pair: the proof is not eliminated into its data field") {
    rejectsWith[PropEliminationRestricted](
      """
        |mutual {
        |  inductive D : Type
        |   | leaf : D
        |   | wrap (p: P) : D
        |
        |  inductive P : Prop
        |   | mk (d: D) : P
        |}
        |
        |def out (p: P) : D := {
        |  match p returning D with
        |  | P.mk d => d
        |}
        |""".stripMargin
    )
    accepts(
      """
        |mutual {
        |  inductive P : Prop
        |   | mk (q: Q) : P
        |
        |  inductive Q : Prop
        |   | a : Q
        |   | b (p: P) : Q
        |}
        |
        |def out (p: P) : Nat := {
        |  match p returning Nat with
        |  | P.mk q => 0
        |}
        |""".stripMargin
    )
  }

  test("fam-9 CONTROL selectors of a mutual record, and a copyable family holding a function to a linear sibling") {
    accepts(
      """
        |namespace N {
        |  mutual {
        |    inductive R : Type
        |     | mk (n: Nat)(s: S) : R
        |
        |    inductive S : Type
        |     | stop : S
        |     | go (r: R) : S
        |  }
        |}
        |
        |def one : Eq(Nat, N.R.n(N.R.mk(1, N.S.stop)), 1) := Eq.refl(1)
        |""".stripMargin
    )
    accepts(
      """
        |mutual {
        |  inductive C : Type
        |   | stop : C
        |   | mk (f: (n: Nat) -> L) : C
        |
        |  inductive L : Lin(Level.zero)
        |   | mk (c: C) : L
        |}
        |""".stripMargin
    )
  }

  test("fam-10 a family, or a sibling, may not occur in its constructors' result indices, as in Coq and Lean") {
    rejectsWith[FamilyInResultIndex]("inductive A indices (T: Type) : Type\n | mk : A(A(Nat))\n")
    rejectsWith[FamilyInResultIndex](
      "mutual {\n  inductive A indices (T: Type) : Type\n   | mk : A(B)\n\n  inductive B : Type\n   | leaf : B\n}\n"
    )
    rejectsWith[FamilyInResultIndex]("inductive Bad indices (P: Prop) : Prop\n | mk : Bad((h: Bad(True)) -> False)\n")
    rejectsWith[FamilyInResultIndex](
      "inductive L indices (F: Prop -> Prop) : Prop\n | mk : L(fun (X: Prop): Prop => L(fun (Y: Prop): Prop => X))\n"
    )
  }

  test("fam-10b with propositional extensionality, a family in its own result index proves False") {
    // Before the check, this program checked: matching on `Bad(True)` yields the index equation, so `Not(Bad(True))`
    // holds with no axiom, and `propext` makes `Not(Bad(True))` equal to `True`, along which `Bad.mk` proves `Bad(True)`.
    val withAxioms = new Programs(Prelude.default, allowUserAxioms = true)
    val src =
      """
        |inductive Bad indices (P: Prop) : Prop
        | | mk : Bad((h: Bad(True)) -> False)
        |
        |def toEq (P: Prop)(b: Bad(P)) : Eq(Prop, P, (h: Bad(True)) -> False) := {
        |  match b returning Eq(Prop, P, (h: Bad(True)) -> False) with
        |  | Bad.mk => Eq.refl((h: Bad(True)) -> False)
        |}
        |
        |def notBad (b: Bad(True)) : False := Eq.mp(toEq(True, b), True.intro)(b)
        |
        |axiom propext (a: Prop)(b: Prop)(h: Iff(a, b)) : Eq(Prop, a, b)
        |
        |def notBadIffTrue : Iff(Not(Bad(True)), True) :=
        |  Iff.intro(Not(Bad(True)), True, fun (h: Not(Bad(True))): True => True.intro,
        |    fun (t: True): Not(Bad(True)) => fun (b: Bad(True)): False => notBad(b))
        |
        |def badTrue : Bad(True) :=
        |  Eq.substProp(propext(Not(Bad(True)), True, notBadIffTrue), fun (q: Prop): Prop => Bad(q), Bad.mk)
        |
        |def boom : False := notBad(badTrue)
        |""".stripMargin
    try {
      withAxioms.runChecked(src)
      fail("ACCEPTED (BREAK: should be rejected with FamilyInResultIndex)")
    } catch {
      case _: FamilyInResultIndex =>
      case t: TypeError           => fail(s"rejected, but not with FamilyInResultIndex: ${describe(t, src)}")
    }
  }

  test("fam-10c CONTROL a result index may read a field whose type names the family") {
    // A field is a variable, no occurrence of the family; Lean accepts the same declaration.
    accepts("inductive T indices (n: Nat) : Type\n | leaf : T(0)\n | node (p: Prod(Nat, T(0))) : T(p.fst)\n")
    accepts("inductive P indices (n: Nat) : Prop\n | base : P(0)\n | step (n: Nat)(h: P(n)) : P(Nat.succ(n))\n")
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Wildcard cases (b2196478).
  // ------------------------------------------------------------------------------------------------------------------

  test("wild-1 a wildcard over a linear scrutinee does not free the scrutinee for reuse") {
    rejectsWith[LinearReused](
      lnats +
        """
          |def again (xs: LNats) : Nat := {
          |  match xs returning Nat with
          |  | _ => count(xs)
          |}
          |""".stripMargin
    )
  }

  test("wild-2 in a read extent each expansion keeps separation of the scrutinee with itself") {
    rejectsWith[LinearReusedInType](
      lnats +
        """
          |inductive Pair2 : Lin(Level.zero)
          | | mk (a: LNats)(b: LNats) : Pair2
          |
          |def size2 (p: Pair2) : Nat := 0
          |
          |def Bad (xs: LNats) : Prop := {
          |  match xs returning Prop with
          |  | LNats.nil => True
          |  | _ => Eq(Nat, size2(Pair2.mk(xs, xs)), 0)
          |}
          |""".stripMargin
    )
  }

  test("wild-3 a wildcard stands for no constructor of an empty family") {
    rejectsWith[RedundantCase]("def f (x: False) : Nat := {\n  match x returning Nat with\n  | _ => 0\n}\n")
  }

  test("wild-4 a wildcard keeps Prop elimination's rules: no large elimination of Or") {
    rejectsWith[PropEliminationRestricted](
      """
        |def out (p: Or(True, True)) : Bool := {
        |  match p returning Bool with
        |  | Or.inl a => Bool.true
        |  | _ => Bool.false
        |}
        |""".stripMargin
    )
    rejectsWith[PropEliminationRestricted](
      """
        |def out (p: Or(True, True)) : Bool := {
        |  match p with
        |  | Or.inl a => Bool.true
        |  | _ => Bool.false
        |}
        |""".stripMargin
    )
    rejectsWith[PropEliminationRestricted](
      "def out : Bool := {\n  match Or.inl(True, True.intro) returning Bool with\n  | _ => Bool.true\n}\n"
    )
  }

  test("wild-5 CONTROL a wildcard in proof recursion, and nested wildcards") {
    accepts(
      peano +
        """
          |def allTrue (n: Nat)(h: P(n)) : True decreases structural(h) := {
          |  match h returning True with
          |  | P.z => True.intro
          |  | _ => True.intro
          |}
          |""".stripMargin
    )
    val params = (1 to 12).map(i => s"(b$i: Bool)").mkString
    def body(i: Int): String =
      if (i > 12) "0" else s"{\n  match b$i returning Nat with\n  | _ => ${body(i + 1)}\n}"
    accepts(s"def f $params : Nat := ${body(1)}\n")
  }

  test("wild-6 OVER-REJECTION a wildcard body cannot match the same scrutinee on the other constructors") {
    // Each expansion knows the scrutinee's constructor, so the inner match's other case is UnreachableCase in it. The
    // same holds for the case written out, so it follows the spec, but no single wildcard body can do this.
    rejectsWith[UnreachableCase](
      color +
        """
          |def f (c: Color) : Nat := {
          |  match c returning Nat with
          |  | Color.red => 0
          |  | _ => {
          |    match c returning Nat with
          |    | Color.green => 1
          |    | Color.blue => 2
          |  }
          |}
          |""".stripMargin
    )
    rejectsWith[RedundantCase](
      color +
        """
          |def f (c: Color) : Nat := {
          |  match c returning Nat with
          |  | Color.red => 0
          |  | _ => {
          |    match c returning Nat with
          |    | Color.green => 1
          |    | _ => 2
          |  }
          |}
          |""".stripMargin
    )
  }

  test("wild-7 CONTROL two expansions' closures are distinct values that convert only extensionally") {
    accepts(
      color +
        """
          |def k (c: Color) : (u: Unit) -> Nat := {
          |  match c returning (u: Unit) -> Nat with
          |  | Color.red => fun (u: Unit): Nat => 0
          |  | _ => fun (u: Unit): Nat => 5
          |}
          |
          |def same : Eq((u: Unit) -> Nat, k(Color.green), k(Color.blue)) := Eq.refl(k(Color.green))
          |""".stripMargin
    )
    rejectsWith[TypeMismatch](
      color +
        """
          |def k (c: Color) : (u: Unit) -> Color := {
          |  match c returning (u: Unit) -> Color with
          |  | Color.red => fun (u: Unit): Color => Color.red
          |  | _ => fun (u: Unit): Color => c
          |}
          |
          |def same : Eq((u: Unit) -> Color, k(Color.green), k(Color.blue)) := Eq.refl(k(Color.green))
          |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Match equations (8601640c).
  // ------------------------------------------------------------------------------------------------------------------

  test("eq-1 a false equation at a variable index, in a stuck computation, or under a wildcard") {
    rejectsWith[TypeMismatch](
      vec +
        """
          |def bad (A: Type)(n: Nat)(v: Vec(A, n)) : Eq(Nat, n, 0) := {
          |  match h : v returning Eq(Nat, n, 0) with
          |  | Vec.nil => Eq.refl(0)
          |  | Vec.cons m tail head => Eq.refl(0)
          |}
          |""".stripMargin
    )
    rejectsWith[TypeMismatch](
      """
        |def g (n: Nat) : Nat := Nat.add(n, n)
        |def f (n: Nat) : Eq(Nat, g(n), 0) := {
        |  match h : g(n) returning Eq(Nat, g(n), 0) with
        |  | Nat.zero => h
        |  | Nat.succ k => h
        |}
        |""".stripMargin
    )
    rejectsWith[TypeMismatch](
      """
        |def f (n: Nat) : Eq(Nat, n, 0) := {
        |  match h : n returning Eq(Nat, n, 0) with
        |  | Nat.zero => h
        |  | _ => h
        |}
        |""".stripMargin
    )
    rejectsWith[TypeMismatch]("def f : Eq(Nat, 3, 0) := {\n  match h : 3 returning Eq(Nat, 3, 0) with\n  | _ => h\n}\n")
  }

  test("eq-2 no equation on a stuck index, a variable kind, a function, or a linear value") {
    rejectsWith[MatchEquationIndexed](
      vec +
        """
          |def stuck (A: Type)(f: (m: Nat) -> Nat)(n: Nat)(v: Vec(A, f(n))) : Nat := {
          |  match h : v returning Nat with
          |  | _ => 1
          |}
          |""".stripMargin
    )
    rejectsWith[MatchEquationUnavailable](
      copyOpt +
        """
          |def f (A: Univ($k, $u))(o: CopyOpt(A)) : Nat := {
          |  match h : o returning Nat with
          |  | _ => 1
          |}
          |""".stripMargin
    )
    rejectsWith[NonInductiveMatch](
      "def f (g: (n: Nat) -> Nat) : Nat := {\n  match h : g returning Nat with\n  | _ => 0\n}\n"
    )
    rejectsWith[MatchEquationUnavailable](
      lnats + "def f (xs: LNats) : Nat := {\n  match h : xs returning Nat with\n  | _ => 0\n}\n"
    )
  }

  test("eq-3 CONTROL an equation whose scrutinee is refined later, and at a kind refined to copy") {
    accepts(
      """
        |def f (n: Nat) : Nat := {
        |  match h : n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => {
        |    match k returning Nat with
        |    | Nat.zero => (fun (e: Eq(Nat, n, 1)): Nat => 0)(h)
        |    | Nat.succ j => (fun (e: Eq(Nat, n, Nat.succ(Nat.succ(j)))): Nat => 0)(h)
        |  }
        |}
        |""".stripMargin
    )
    // `some` exists only at a copyable A, so in its branch k := copy and p's type is copyable data: sound.
    accepts(
      copyOpt +
        """
          |def f (A: Univ($k, $u))(o: CopyOpt(A))(p: CopyOpt(A)) : Nat := {
          |  match o returning Nat with
          |  | CopyOpt.none => 0
          |  | CopyOpt.some x => {
          |    match h : p returning Nat with
          |    | _ => 1
          |  }
          |}
          |""".stripMargin
    )
  }

  test("eq-4 CONTROL an equation over a computation that consumes a linear value only reads it in its type") {
    accepts(
      lnats +
        """
          |def f (xs: LNats) : Nat := {
          |  match h : count(xs) returning Nat with
          |  | Nat.zero => 0
          |  | Nat.succ k => k
          |}
          |""".stripMargin
    )
  }

  test("eq-5 CONTROL an indexed family's equation at a known and a variable index") {
    accepts(
      vec +
        """
          |def headEq (A: Type)(n: Nat)(v: Vec(A, Nat.succ(n))) : A := {
          |  match h : v returning A with
          |  | Vec.cons m tail head =>
          |      (fun (e: Eq(Vec(A, Nat.succ(n)), v, Vec.cons(A, n, tail, head))): A => head)(h)
          |}
          |
          |def isNil (A: Type)(n: Nat)(v: Vec(A, n)) : Bool := {
          |  match h : v returning Bool with
          |  | Vec.nil => Bool.true
          |  | _ => Bool.false
          |}
          |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Fields at the scrutinee's parameters (f007af17).
  // ------------------------------------------------------------------------------------------------------------------

  test("par-1 witnesses bound out of order are linked by name, not by position") {
    accepts(
      """
        |inductive P (A: Type)(B: Type) : Type
        | | mk {B: Type}{A: Type} (x: A)(y: B) : P(A, B)
        |
        |def p : P(Bool, Nat) := P.mk(Nat, Bool, Bool.true, 3)
        |
        |def getX (A: Type)(B: Type)(q: P(A, B)) : A := {
        |  match h : q returning A with
        |  | P.mk x y => (fun (e: Eq(P(A, B), q, P.mk(B, A, x, y))): A => x)(h)
        |}
        |
        |def t : Eq(Bool, getX(Bool, Nat, p), Bool.true) := Eq.refl(Bool.true)
        |""".stripMargin
    )
    rejectsWith[TypeMismatch](
      """
        |inductive P (A: Type)(B: Type) : Type
        | | mk {B: Type}{A: Type} (x: A)(y: B) : P(A, B)
        |
        |def getY (A: Type)(B: Type)(q: P(A, B)) : A := {
        |  match q returning A with
        |  | P.mk x y => y
        |}
        |""".stripMargin
    )
  }

  test("par-2 exactly one witness per parameter, never wider than the parameter") {
    rejectsWith[InvalidErasedConstructorBinder](
      "inductive P (A: Type) : Type\n | mk (x: List($A))(y: $A in Type) : P(A)\n"
    )
    rejectsWith[TypeMismatch]("inductive P (A: Type) : Type\n | mk (x: $A in Sort($u)) : P(A)\n")
    rejectsWith[TypeMismatch]("inductive P (A: Type) : Type\n | mk {A: Sort($u)} (x: A) : P(A)\n")
  }

  test("par-3 a narrower witness: no some(x) at a linear type, and x copyable at a variable kind (sound)") {
    rejectsWith[TypeMismatch](
      copyOpt + "\ndef mk (s: Protocol.Supply) : CopyOpt(Protocol.Supply) := CopyOpt.some(s)\n"
    )
    accepts(
      copyOpt +
        """
          |def dupSome (A: Univ($k, $u))(o: CopyOpt(A)) : Option(Prod(A, A)) := {
          |  match o returning Option(Prod(A, A)) with
          |  | CopyOpt.none => Option.none(Prod(A, A))
          |  | CopyOpt.some x => Option.some(Prod.mk(A, A, x, x))
          |}
          |""".stripMargin
    )
    accepts(
      """
        |inductive W (A: Sort($u)) : Sort(u)
        | | mk (x: $A in Type) : W(A)
        |
        |def get (A: Sort($u))(w: W(A))(d: A) : A := {
        |  match w returning A with
        |  | W.mk x => x
        |}
        |""".stripMargin
    )
  }

  test("par-4 a capture witness that also fixes an index refines the index, not the parameter") {
    val q =
      vec +
        """
          |inductive Q (n: Nat) indices (m: Nat) : Type
          | | mk (v: Vec(Nat, $n)) : Q(n, Nat.succ(n))
          |""".stripMargin
    accepts(
      q +
        """
          |def f (a: Nat)(b: Nat)(q: Q(a, b)) : Eq(Nat, b, Nat.succ(a)) := {
          |  match q returning Eq(Nat, b, Nat.succ(a)) with
          |  | Q.mk v => Eq.refl(Nat.succ(a))
          |}
          |""".stripMargin
    )
    rejectsWith[TypeMismatch](
      q +
        """
          |def g (a: Nat)(b: Nat)(q: Q(a, b)) : Eq(Nat, b, a) := {
          |  match q returning Eq(Nat, b, a) with
          |  | Q.mk v => Eq.refl(a)
          |}
          |""".stripMargin
    )
  }

  test("par-5 OVER-REJECTION an outer local of the refined kind stays tracked after k := copy") {
    // In the `some` branch k := copy, so `y : b` with `b : Univ(k, v)` is copyable there, but it was tracked when bound.
    rejectsWith[LinearReused](
      copyOpt +
        """
          |def dup (A: Univ($k, $u))(o: CopyOpt(A))(b: Univ(k, $v))(y: b)(z: b) : Prod(b, b) := {
          |  match o returning Prod(b, b) with
          |  | CopyOpt.none => Prod.mk(b, b, y, z)
          |  | CopyOpt.some x => Prod.mk(b, b, y, y)
          |}
          |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // The root link refines the scrutinee type's variables (d8a6f50e).
  // ------------------------------------------------------------------------------------------------------------------

  test("root-1 at a variable index the linked root is not smaller than itself, nor is a rebuilt or equal value") {
    rejectsWith[NonDecreasingRecursiveCall](
      vec +
        """
          |def loop (A: Type)(n: Nat)(v: Vec(A, n)) : Nat decreases structural(v) := {
          |  match v returning Nat with
          |  | Vec.nil => 0
          |  | Vec.cons m tail head => loop(A, n, v)
          |}
          |""".stripMargin
    )
    rejectsWith[NonDecreasingRecursiveCall](
      """
        |inductive S indices (x: Nat) : Type
        | | mk (y: Nat) : S(y)
        |
        |def f (n: Nat)(s: S(n)) : Nat decreases structural(n) := {
        |  match s returning Nat with
        |  | S.mk y => f(y, S.mk(y))
        |}
        |""".stripMargin
    )
    rejectsWith[NonDecreasingRecursiveCall](
      """
        |inductive S indices (x: Nat) : Type
        | | mk (y: Nat) : S(y)
        |
        |def f (n: Nat)(s: S(n)) : Nat decreases structural(s) := {
        |  match s returning Nat with
        |  | S.mk y => f(y, S.mk(y))
        |}
        |""".stripMargin
    )
  }

  test("root-2 a variable shared with another binder's type: only the matched binder's fields are smaller") {
    rejectsWith[NonDecreasingRecursiveCall](
      vec +
        """
          |def two (A: Type)(n: Nat)(v: Vec(A, n))(w: Vec(A, n)) : Nat decreases structural(w) := {
          |  match v returning Nat with
          |  | Vec.nil => 0
          |  | Vec.cons m tail head => two(A, m, tail, tail)
          |}
          |""".stripMargin
    )
    accepts(
      vec +
        """
          |def two (A: Type)(n: Nat)(v: Vec(A, n))(w: Vec(A, n)) : Nat decreases structural(w) := {
          |  match v returning Nat with
          |  | Vec.nil => 0
          |  | Vec.cons m tail head => {
          |    match w returning Nat with
          |    | Vec.cons m2 tail2 head2 => two(A, m, tail, tail2)
          |  }
          |}
          |
          |def byIndex (A: Type)(n: Nat)(v: Vec(A, n)) : Nat decreases structural(n) := {
          |  match v returning Nat with
          |  | Vec.nil => 0
          |  | Vec.cons m tail head => byIndex(A, m, tail)
          |}
          |""".stripMargin
    )
  }

  test("root-3 a linked linear root is no second copy of its fields") {
    rejectsWith[LinearReused](
      linVec +
        """
          |def dup (A: Lin($u))(n: Nat)(v: LV(A, n))(d: A) : Both(A, A) := {
          |  match v returning Both(A, A) with
          |  | LV.nil => Both.mk(d, d)
          |  | LV.cons m tail head => {
          |    match v returning Both(A, A) with
          |    | LV.cons m2 tail2 head2 => Both.mk(head, head2)
          |  }
          |}
          |""".stripMargin
    )
    rejectsWith[LinearReused](
      linVec +
        """
          |def dup (A: Lin($u))(n: Nat)(v: LV(A, Nat.succ(n))) : Both(A, A) := {
          |  match v returning Both(A, A) with
          |  | LV.cons m tail head => {
          |    match v returning Both(A, A) with
          |    | LV.cons m2 tail2 head2 => Both.mk(head, head2)
          |  }
          |}
          |""".stripMargin
    )
  }

  test("root-4 CONTROL structural recursion on a linear family and on a captured index, and the root's value") {
    accepts(
      linVec +
        """
          |def drop (A: Lin($u))(n: Nat)(v: LV(A, n)) : Nat decreases structural(v) := {
          |  match v returning Nat with
          |  | LV.nil => 0
          |  | LV.cons m tail head => Nat.succ(drop(A, m, tail))
          |}
          |""".stripMargin
    )
    accepts(
      vec +
        """
          |def len (v: Vec($A, $n)) : Nat decreases structural(v) := {
          |  match v returning Nat with
          |  | Vec.nil => 0
          |  | _ => {
          |    match v returning Nat with
          |    | Vec.cons m tail head => Nat.succ(len(tail))
          |  }
          |}
          |
          |def again (A: Type)(k: Nat)(v: Vec(A, k)) : Nat := {
          |  match v returning Nat with
          |  | Vec.nil => 0
          |  | Vec.cons m tail head => (fun (e: Eq(Vec(A, k), v, Vec.cons(A, m, tail, head))): Nat => m)(Eq.refl(v))
          |}
          |""".stripMargin
    )
  }

  test("root-5 OVER-REJECTION a nested match on the linked root may no longer name every constructor of its index") {
    // Before 2.4, `t: T(b)` was not linked in the `yes` branch, only `b := true`, so the inner match needed both of
    // T(true)'s constructors. Now `t := yes` and `also` is UnreachableCase, as it already was for a family without
    // indices (second program).
    rejectsWith[UnreachableCase](
      """
        |inductive T indices (b: Bool) : Type
        | | yes : T(Bool.true)
        | | also (x: Nat) : T(Bool.true)
        | | no : T(Bool.false)
        |
        |def f (b: Bool)(t: T(b)) : Nat := {
        |  match t returning Nat with
        |  | T.yes => {
        |    match t returning Nat with
        |    | T.yes => 0
        |    | T.also x => x
        |  }
        |  | T.also x => 1
        |  | T.no => 2
        |}
        |""".stripMargin
    )
    rejectsWith[UnreachableCase](
      """
        |inductive T : Type
        | | yes : T
        | | also (x: Nat) : T
        |
        |def f (t: T) : Nat := {
        |  match t returning Nat with
        |  | T.yes => {
        |    match t returning Nat with
        |    | T.yes => 0
        |    | T.also x => x
        |  }
        |  | T.also x => 1
        |}
        |""".stripMargin
    )
  }
}
