package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

/**
 * Structure eta as representation (StructEta): every value of an eta-eligible struct type is constructor-headed, so
 * `s ≡ mk(s.f1, …, s.fn)` holds definitionally for binders, opaque constants, axioms, and blocked matches alike — and
 * never for recursive, indexed, or Prop-instantiated structs.
 */
class StructEtaTests extends munit.FunSuite {

  private def typecheckDecls(src: String): Unit = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        try {
          Interpreter.run(core, Prelude.test)
        } catch {
          case t: TypeError =>
            val source = Source(src)
            fail(ErrorReporter.pretty(t, source))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  private def expectTypeError(src: String): TypeError = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[TypeError] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  private def runProgram(src: String): Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        try {
          Interpreter.run(core, Prelude.test).getOrElse(fail("Program has no body"))
        } catch {
          case t: TypeError =>
            val source = Source(src)
            fail(ErrorReporter.pretty(t, source))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

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
    // singleton shape is exactly the Acc trap (kernel-theory §5).
    val err = expectTypeError(
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
    val err = expectTypeError(
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
}
