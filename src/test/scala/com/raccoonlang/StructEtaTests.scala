package com.raccoonlang

/**
 * Structure eta as rules (StructEta): `s ≡ mk(s.f1, …, s.fn)` holds definitionally for binders, axioms, and blocked
 * matches alike, decided fieldwise through the eta view rather than by any representation — and never for recursive,
 * indexed, or Prop-instantiated structs.
 */
class StructEtaTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

  private val natAndCouple =
    """
      |inductive Peano : Type
      | | zero : Peano
      | | succ (_: Peano) : Peano
      |
      |struct Couple (A: Type)(B: Type) : Type
      | | mk (fst: A)(snd: B) : Couple(A, B)
      |""".stripMargin

  test("binder eta: a struct binder equals the constructor of its projections") {
    typecheckDecls(
      natAndCouple +
        """
          |def eta {A: Type}{B: Type} (p: Couple(A, B)): Eq(Couple(A, B), p, Couple.mk(p.fst, p.snd)) :=
          |  Eq.refl(p)
          |""".stripMargin
    )
  }

  test("plain one-constructor inductive receives eta without named selectors") {
    typecheckDecls(
      """
        |inductive PlainCouple (A: Type)(B: Type) : Type
        | | mk (left: A)(right: B) : PlainCouple(A, B)
        |
        |def getLeft {A: Type}{B: Type} (p: PlainCouple(A, B)): A := {
        |  match p returning A with
        |  | PlainCouple.mk left right => left
        |}
        |def getRight {A: Type}{B: Type} (p: PlainCouple(A, B)): B := {
        |  match p returning B with
        |  | PlainCouple.mk left right => right
        |}
        |def eta {A: Type}{B: Type} (p: PlainCouple(A, B)):
        |  Eq(PlainCouple(A, B), p, PlainCouple.mk(getLeft(p), getRight(p))) := Eq.refl(p)
        |""".stripMargin
    )
  }

  test("an implicit parameter at an automatically eta-expanded type remains forceable") {
    typecheckDecls(
      """
        |inductive Tag : Type
        | | mk (P: Prop) : Tag
        |
        |inductive Tagged indices (tag: Tag) : Type
        | | mk (tag: Tag) : Tagged(tag)
        |
        |def recover {tag: Tag}(value: Tagged(tag)): Tag := tag
        |def demo (P: Prop): Tag := recover(Tagged.mk(Tag.mk(P)))
        |""".stripMargin
    )
  }

  test("binder eta: dependent fields (Sigma-like)") {
    typecheckDecls(
      natAndCouple +
        """
          |struct Sig (A: Type)(B: A -> Type) : Type
          | | mk (fst: A)(snd: B(fst)) : Sig(A, B)
          |
          |// B is not forced by the fields (B(fst) is not invertible), so it stays explicit.
          |def eta {A: Type}{B: A -> Type} (s: Sig(A, B)): Eq(Sig(A, B), s, Sig.mk(B, s.fst, s.snd)) :=
          |  Eq.refl(s)
          |""".stripMargin
    )
  }

  test("binder eta: proof fields compare by proof irrelevance (Subtype-like)") {
    typecheckDecls(
      natAndCouple +
        """
          |struct Sub (A: Type)(p: A -> Prop) : Type
          | | mk (val: A)(property: p(val)) : Sub(A, p)
          |
          |// p is not forced by the fields (p(val) is not invertible), so it stays explicit.
          |def eta {A: Type}{p: A -> Prop} (s: Sub(A, p)): Eq(Sub(A, p), s, Sub.mk(p, s.val, s.property)) :=
          |  Eq.refl(s)
          |""".stripMargin
    )
  }

  test("axiom eta: a prelude axiom of struct type is its constructor of projections") {
    // Only the trusted prelude declares axioms (spec §7.3).
    val prelude =
      TestSupport.preludeAssuming(TestSupport.testPreludeSource, natAndCouple + "\naxiom a : Couple(Peano, Peano)\n")
    typecheckDecls("def eta : Eq(Couple(Peano, Peano), a, Couple.mk(a.fst, a.snd)) := Eq.refl(a)\n", prelude)
  }

  test("unit-like struct: any two values are definitionally equal") {
    typecheckDecls(
      """
        |struct One : Type
        | | mk : One
        |
        |def uniq (a: One)(b: One): Eq(One, a, b) := Eq.refl(a)
        |""".stripMargin
    )
  }

  test("blocked match eta: a stuck struct-valued match equals the constructor of its projections") {
    typecheckDecls(
      natAndCouple +
        """
          |def pick (n: Peano): Couple(Peano, Peano) := {
          |  match n returning Couple(Peano, Peano) with
          |  | Peano.zero => Couple.mk(Peano.zero, Peano.zero)
          |  | Peano.succ k => Couple.mk(k, n)
          |}
          |
          |def eta (n: Peano): Eq(Couple(Peano, Peano), pick(n), Couple.mk(pick(n).fst, pick(n).snd)) :=
          |  Eq.refl(pick(n))
          |""".stripMargin
    )
  }

  test("match on a struct binder fires with projection fields") {
    // The scrutinee is constructor-headed by the invariant, so the single case is entered
    // directly — "assume the single constructor" as a consequence of representation.
    typecheckDecls(
      natAndCouple +
        """
          |def swap {A: Type}{B: Type} (p: Couple(A, B)): Couple(B, A) := {
          |  match p returning Couple(B, A) with
          |  | Couple.mk f s => Couple.mk(s, f)
          |}
          |
          |def swapEta {A: Type}{B: Type} (p: Couple(A, B)): Eq(Couple(B, A), swap(p), Couple.mk(p.snd, p.fst)) :=
          |  Eq.refl(swap(p))
          |""".stripMargin
    )
  }

  test("nested struct fields expand recursively") {
    typecheckDecls(
      natAndCouple +
        """
          |struct Box (A: Type) : Type
          | | mk (inner: A) : Box(A)
          |
          |def eta {A: Type} (b: Box(Couple(A, A))): Eq(Couple(A, A), b.inner, Couple.mk(b.inner.fst, b.inner.snd)) :=
          |  Eq.refl(b.inner)
          |""".stripMargin
    )
  }

  test("concrete evaluation is unaffected by expansion") {
    val res = runProgram(
      natAndCouple +
        """
          |def pick (n: Peano): Couple(Peano, Peano) := {
          |  match n returning Couple(Peano, Peano) with
          |  | Peano.zero => Couple.mk(Peano.zero, Peano.succ(Peano.zero))
          |  | Peano.succ k => Couple.mk(k, n)
          |}
          |
          |{
          |  let p := pick(Peano.zero)
          |  p.snd
          |}
          |""".stripMargin
    )
    res match {
      case Value.VCtor(head, _, _) => assertEquals(head.name, "Peano.succ")
      case other                   => fail(s"Expected Peano.succ constructor value, got $other")
    }
  }

  test("negative: recursive struct gets no eta") {
    // Wrap is strictly positive (direct recursive field) and a legal struct, but recursive
    // structs must never expand: eta-expanding them would not terminate, and the recursive
    // singleton shape is excluded from structure eta (docs/kernel.md#structure-eta-and-projections).
    val err = expectAnyTypeError(
      """
        |struct Wrap : Type
        | | mk (w: Wrap) : Wrap
        |
        |def eta (a: Wrap): Eq(Wrap, a, Wrap.mk(a.w)) := Eq.refl(a)
        |""".stripMargin
    )
    assert(err.isInstanceOf[TypeMismatch], s"expected TypeMismatch, got $err")
  }

  test("negative: indexed struct gets no eta") {
    val err = expectAnyTypeError(
      natAndCouple +
        """
          |struct Tag (A: Type) indices (n: Peano) : Type
          | | mk (k: Peano) : Tag(A, k)
          |
          |def eta {A: Type}{n: Peano} (t: Tag(A, n)): Eq(Tag(A, n), t, Tag.mk(t.k)) := Eq.refl(t)
          |""".stripMargin
    )
    assert(err.isInstanceOf[TypeError], s"expected a type error, got $err")
  }

  test("Prop instantiation of a sort-polymorphic struct collapses instead of expanding") {
    // The dichotomy boundary: at u1 = u2 = 0 the instance is a proposition, so values are
    // VProofs and equality is proof irrelevance — expansion must never fire there.
    typecheckDecls(
      """
        |struct CoupleU {u1: Level}{u2: Level}(A: Sort { level = u1 })(B: Sort { level = u2 }) : Sort { level = max(u1, u2) }
        | | mk (fst: A)(snd: B) : CoupleU(A, B)
        |
        |def irr (p: Prop)(q: Prop)(h1: CoupleU(p, q))(h2: CoupleU(p, q)): Eq(CoupleU(p, q), h1, h2) :=
        |  Eq.refl(h1)
        |""".stripMargin
    )
  }

  test("a user selector and the kernel's own field projection are the same value") {
    // `Couple.fst(p)` is a thunk of the SELECTOR's match term; the eta view of a neutral `p` builds a
    // thunk of the kernel's canonical projection term. Different node ids, same stuck computation:
    // they must be identified by tryUnifyNeutralMatches, or the `refl`s below cannot check.
    typecheckDecls(
      natAndCouple +
        """
          |def selectorIsProjection (p: Couple(Peano, Peano)): Eq(Peano, Couple.fst(p), p.fst) := Eq.refl(p.fst)
          |def etaThroughSelectors (p: Couple(Peano, Peano)): Eq(Couple(Peano, Peano), p, Couple.mk(p.fst, p.snd)) :=
          |  Eq.refl(p)
          |""".stripMargin
    )
  }

  test("eta holds for a variable refined to a struct type inside a branch") {
    // The refined-variable gap. `x : A` is created at a bare type variable, so under eta-by-
    // representation it could never be constructor-headed. The branch refines `A := Couple(...)`,
    // and only there does eta apply — which the rule-based statement handles and the old
    // representation invariant could not, because `x` already existed in the wrong form.
    typecheckDecls(
      natAndCouple +
        """
          |inductive Tag indices (A: Type) : Type
          | | isCouple : Tag(Couple(Peano, Peano))
          |
          |def refinedEta (A: Type)(x: A)(t: Tag(A)): Peano := {
          |  match t returning Peano with
          |  | Tag.isCouple => {
          |    let same : Eq(Couple(Peano, Peano), x, Couple.mk(x.fst, x.snd)) := Eq.refl(x)
          |    x.fst
          |  }
          |}
          |""".stripMargin
    )
  }

  test("dependent selectors check against a branch's own pattern variables") {
    // MatchChecker reachability unifies `scrut` against `mk(fresh fields)`; rule 3 links each fresh
    // field to the corresponding projection, so a motive stated with selectors checks in the branch.
    typecheckDecls(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |struct Sig (A: Type)(B: A -> Type) : Type
        | | mk (fst: A)(snd: B(fst)) : Sig(A, B)
        |
        |def useDependent (anyA: Type)(anyB: anyA -> Type)(s: Sig(anyA, anyB)): anyB(s.fst) := {
        |  match s returning anyB(s.fst) with
        |  | Sig.mk a b => b
        |}
        |""".stripMargin
    )
  }

  test("termination: measure on a projected field decreases through refinement") {
    typecheckDecls(
      natAndCouple +
        """
          |def countdown (p: Couple(Peano, Peano)): Peano decreases measure(p.fst) := {
          |  match p.fst returning Peano with
          |  | Peano.zero => Peano.zero
          |  | Peano.succ k => countdown(Couple.mk(k, p.snd))
          |}
          |""".stripMargin
    )
  }

  test("two distinct struct neutrals with fields are unequal, and comparing them terminates") {
    // Regression: fieldwise decomposition must not fire for two neutrals. Each virtual field is a
    // projection thunk capturing its base, so decomposing would compare the bases again, forever.
    val src =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (pred: Peano) : Peano
        |
        |struct Couple (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Couple(A, B)
        |
        |def flat (a: Couple(Peano, Peano))(b: Couple(Peano, Peano)): Eq(Couple(Peano, Peano), a, b) := Eq.refl(a)
        |""".stripMargin
    assert(expectAnyTypeError(src).isInstanceOf[TypeMismatch])

    val nested =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (pred: Peano) : Peano
        |
        |struct Couple (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Couple(A, B)
        |
        |def deep (a: Couple(Couple(Peano, Peano), Peano))(b: Couple(Couple(Peano, Peano), Peano)):
        |    Eq(Couple(Couple(Peano, Peano), Peano), a, b) := Eq.refl(a)
        |""".stripMargin
    assert(expectAnyTypeError(nested).isInstanceOf[TypeMismatch])
  }
}
