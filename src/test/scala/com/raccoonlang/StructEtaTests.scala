package com.raccoonlang

/**
 * Structure eta as rules (StructEta): `s ≡ mk(s.f1, …, s.fn)` holds definitionally for binders, opaque constants,
 * axioms, and blocked matches alike, decided fieldwise through the eta view rather than by any representation — and
 * never for recursive, indexed, or Prop-instantiated structs.
 */
class StructEtaTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

  private val natAndPair =
    """
      |inductive Peano : Type
      | | zero : Peano
      | | succ (_: Peano) : Peano
      |
      |struct Pair (A: Type)(B: Type) : Type
      | | mk (fst: A)(snd: B) : Pair(A, B)
      |""".stripMargin

  test("binder eta: a struct binder equals the constructor of its projections") {
    typecheckDecls(
      natAndPair +
        """
          |def eta {A: Type}{B: Type} (p: Pair(A, B)): Eq(Pair(A, B), p, Pair.mk(p.fst, p.snd)) :=
          |  Eq.refl(p)
          |""".stripMargin
    )
  }

  test("plain one-constructor inductive receives eta without named selectors") {
    typecheckDecls(
      """
        |inductive PlainPair (A: Type)(B: Type) : Type
        | | mk (left: A)(right: B) : PlainPair(A, B)
        |
        |def getLeft {A: Type}{B: Type} (p: PlainPair(A, B)): A := {
        |  match p returning A with
        |  | PlainPair.mk left right => left
        |}
        |def getRight {A: Type}{B: Type} (p: PlainPair(A, B)): B := {
        |  match p returning B with
        |  | PlainPair.mk left right => right
        |}
        |def eta {A: Type}{B: Type} (p: PlainPair(A, B)):
        |  Eq(PlainPair(A, B), p, PlainPair.mk(getLeft(p), getRight(p))) := Eq.refl(p)
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
      natAndPair +
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
      natAndPair +
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

  test("opaque constant eta: an opaque struct global is its constructor of projections") {
    typecheckDecls(
      natAndPair +
        """
          |opaque def c : Pair(Peano, Peano) := Pair.mk(Peano.zero, Peano.zero)
          |
          |def eta : Eq(Pair(Peano, Peano), c, Pair.mk(c.fst, c.snd)) := Eq.refl(c)
          |""".stripMargin
    )
  }

  test("axiom eta: an axiom of struct type is its constructor of projections") {
    typecheckDecls(
      natAndPair +
        """
          |axiom a : Pair(Peano, Peano)
          |
          |def eta : Eq(Pair(Peano, Peano), a, Pair.mk(a.fst, a.snd)) := Eq.refl(a)
          |""".stripMargin
    )
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
      natAndPair +
        """
          |def pick (n: Peano): Pair(Peano, Peano) := {
          |  match n returning Pair(Peano, Peano) with
          |  | Peano.zero => Pair.mk(Peano.zero, Peano.zero)
          |  | Peano.succ k => Pair.mk(k, n)
          |}
          |
          |def eta (n: Peano): Eq(Pair(Peano, Peano), pick(n), Pair.mk(pick(n).fst, pick(n).snd)) :=
          |  Eq.refl(pick(n))
          |""".stripMargin
    )
  }

  test("match on a struct binder fires with projection fields") {
    // The scrutinee is constructor-headed by the invariant, so the single case is entered
    // directly — "assume the single constructor" as a consequence of representation.
    typecheckDecls(
      natAndPair +
        """
          |def swap {A: Type}{B: Type} (p: Pair(A, B)): Pair(B, A) := {
          |  match p returning Pair(B, A) with
          |  | Pair.mk f s => Pair.mk(s, f)
          |}
          |
          |def swapEta {A: Type}{B: Type} (p: Pair(A, B)): Eq(Pair(B, A), swap(p), Pair.mk(p.snd, p.fst)) :=
          |  Eq.refl(swap(p))
          |""".stripMargin
    )
  }

  test("nested struct fields expand recursively") {
    typecheckDecls(
      natAndPair +
        """
          |struct Box (A: Type) : Type
          | | mk (inner: A) : Box(A)
          |
          |def eta {A: Type} (b: Box(Pair(A, A))): Eq(Pair(A, A), b.inner, Pair.mk(b.inner.fst, b.inner.snd)) :=
          |  Eq.refl(b.inner)
          |""".stripMargin
    )
  }

  test("concrete evaluation is unaffected by expansion") {
    val res = runProgram(
      natAndPair +
        """
          |def pick (n: Peano): Pair(Peano, Peano) := {
          |  match n returning Pair(Peano, Peano) with
          |  | Peano.zero => Pair.mk(Peano.zero, Peano.succ(Peano.zero))
          |  | Peano.succ k => Pair.mk(k, n)
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
      natAndPair +
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
        |struct PairU {u1: Level}{u2: Level}(A: Sort(u1))(B: Sort(u2)) : Sort(Level.max(u1, u2))
        | | mk (fst: A)(snd: B) : PairU(A, B)
        |
        |def irr (p: Prop)(q: Prop)(h1: PairU(p, q))(h2: PairU(p, q)): Eq(PairU(p, q), h1, h2) :=
        |  Eq.refl(h1)
        |""".stripMargin
    )
  }

  test("a user selector and the kernel's own field projection are the same value") {
    // `Pair.fst(p)` is a thunk of the SELECTOR's match term; the eta view of a neutral `p` builds a
    // thunk of the kernel's canonical projection term. Different node ids, same stuck computation:
    // they must be identified by tryUnifyNeutralMatches, or the `refl`s below cannot check.
    typecheckDecls(
      natAndPair +
        """
          |axiom p : Pair(Peano, Peano)
          |def selectorIsProjection : Eq(Peano, Pair.fst(p), p.fst) := Eq.refl(p.fst)
          |def etaThroughSelectors : Eq(Pair(Peano, Peano), p, Pair.mk(p.fst, p.snd)) := Eq.refl(p)
          |""".stripMargin
    )
  }

  test("eta holds for a variable refined to a struct type inside a branch") {
    // The refined-variable gap. `x : A` is created at a bare type variable, so under eta-by-
    // representation it could never be constructor-headed. The branch refines `A := Pair(...)`,
    // and only there does eta apply — which the rule-based statement handles and the old
    // representation invariant could not, because `x` already existed in the wrong form.
    typecheckDecls(
      natAndPair +
        """
          |inductive Tag indices (A: Type) : Type
          | | isPair : Tag(Pair(Peano, Peano))
          |
          |def refinedEta (A: Type)(x: A)(t: Tag(A)): Peano := {
          |  match t returning Peano with
          |  | Tag.isPair => {
          |    let same : Eq(Pair(Peano, Peano), x, Pair.mk(x.fst, x.snd)) := Eq.refl(x)
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
        |axiom anyA : Type
        |axiom anyB : anyA -> Type
        |
        |def useDependent (s: Sig(anyA, anyB)): anyB(s.fst) := {
        |  match s returning anyB(s.fst) with
        |  | Sig.mk a b => b
        |}
        |""".stripMargin
    )
  }

  test("termination: measure on a projected field decreases through refinement") {
    typecheckDecls(
      natAndPair +
        """
          |def countdown (p: Pair(Peano, Peano)): Peano decreases measure(p.fst) := {
          |  match p.fst returning Peano with
          |  | Peano.zero => Peano.zero
          |  | Peano.succ k => countdown(Pair.mk(k, p.snd))
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
        |struct Pair (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Pair(A, B)
        |
        |def flat (a: Pair(Peano, Peano))(b: Pair(Peano, Peano)): Eq(Pair(Peano, Peano), a, b) := Eq.refl(a)
        |""".stripMargin
    assert(expectAnyTypeError(src).isInstanceOf[TypeMismatch])

    val nested =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (pred: Peano) : Peano
        |
        |struct Pair (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Pair(A, B)
        |
        |def deep (a: Pair(Pair(Peano, Peano), Peano))(b: Pair(Pair(Peano, Peano), Peano)):
        |    Eq(Pair(Pair(Peano, Peano), Peano), a, b) := Eq.refl(a)
        |""".stripMargin
    assert(expectAnyTypeError(nested).isInstanceOf[TypeMismatch])
  }
}
