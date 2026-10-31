package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.ProgramFixtures.Programs

/**
 * Adversarial review of field projection as a kernel operation (docs/kernel.md, "Structure eta and projections"), which
 * replaced the elaborator's generated selectors. A test that ACCEPTS a program it labels a break is a break.
 *
 * Every program runs without user axioms. The suite covers duplication of linear fields through projections, in
 * programs and in read extents; large elimination through projections of `Prop` records; recursive records, which have
 * no eta; projections under refinement and in types; eta between projections and constructors; projections as
 * termination candidates; hidden dependencies and indexed families; and names, where a field is named like a namespace
 * member, a method or a constructor.
 */
class ProjectionAttackTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs.runChecked

  private def describe(t: Throwable, src: String): String =
    t match {
      case te: TypeError => s"${te.getClass.getSimpleName}: " + ErrorReporter.pretty(te, Source(src)).take(600)
      case other         => s"${other.getClass.getSimpleName}: ${String.valueOf(other.getMessage).take(300)}"
    }

  /** The program checks and runs. */
  private def accepts(src: String)(implicit loc: munit.Location): Unit =
    try { runChecked(src); () }
    catch { case t: TypeError => fail("REJECTED (should accept): " + describe(t, src)) }

  /** The program is rejected with a `T`; an acceptance is a break. */
  private def rejectsWith[T <: TypeError](src: String)(implicit loc: munit.Location, ct: reflect.ClassTag[T]): T =
    try {
      runChecked(src)
      fail(s"ACCEPTED (BREAK: should be rejected with ${ct.runtimeClass.getSimpleName})")
    } catch {
      case ct(e) => e
      case t: TypeError =>
        fail(s"rejected by ${describe(t, src).take(400)}, not ${ct.runtimeClass.getSimpleName}")
    }

  // ==================================================================================================================
  // 1. Linear fields: programs use their record once; reads keep fields separate, a field from its record, and one
  //    field from itself.
  // ==================================================================================================================

  private val linear =
    ProgramFixtures.lnats +
      """
        |inductive LPair : Lin(Level.zero)
        | | mk (a: LNats)(b: LNats) : LPair
        |
        |inductive LBox : Lin(Level.zero)
        | | mk (inner: LPair)(c: LNats) : LBox
        |
        |// Erased and captured binders are no stored fields: n is field 0, a field 1, b field 2.
        |inductive LTagged (A: Type) : Lin(Level.zero)
        | | mk {A: Type} (n: A)(a: LNats)(b: LNats) : LTagged(A)
        |
        |def pairCount (xs: LNats)(ys: LNats) : Nat := Nat.add(count(xs), count(ys))
        |
        |def pairWith (p: LPair)(xs: LNats) : Nat := 0
        |
        |""".stripMargin

  test("program: one projection of a linear record uses it, and drops the other fields") {
    accepts(linear + "def ok (p: LPair) : Nat := count(p.a)\n")
    accepts(linear + "def ok (bx: LBox) : Nat := count(bx.inner.b)\n")
    accepts(linear + "def ok (p: LPair) : Nat := count(LPair.b(p))\n")
  }

  test("program: two projections of one linear record are a second use, however written") {
    rejectsWith[LinearReused](linear + "def bad (p: LPair) : Nat := pairCount(p.a, p.b)\n")
    rejectsWith[LinearReused](linear + "def bad (p: LPair) : Nat := pairCount(p.a, p.a)\n")
    rejectsWith[LinearReused](linear + "def bad (p: LPair) : Nat := pairCount(LPair.a(p), p.b)\n")
    rejectsWith[LinearReused](linear + "def bad (p: LPair) : Nat := {\n  let q := p\n  pairCount(q.a, p.b)\n}\n")
    rejectsWith[LinearReused](linear + "def bad (p: LPair) : Nat := {\n  let x := p.a\n  pairCount(x, p.b)\n}\n")
    rejectsWith[LinearReused](linear + "def bad (bx: LBox) : Nat := pairCount(bx.inner.a, bx.c)\n")
    rejectsWith[LinearReused](linear + "def bad (p: LPair) : Nat := {\n  let (x, y) := p\n  count(p.a)\n}\n")
    rejectsWith[LinearReused](
      linear + "def bad (p: LPair) : Nat := {\n  match p with\n  | LPair.mk x y => pairCount(x, p.b)\n}\n"
    )
  }

  test("read: sibling fields are separate, as destructured fields are") {
    accepts(linear + "def ok (p: LPair)(h: Eq(Nat, pairCount(p.a, p.b), 0)) : Nat := 0\n")
    accepts(linear + "def ok (p: LPair)(h: Eq(Nat, pairCount(LPair.a(p), LPair.b(p)), 0)) : Nat := 0\n")
    accepts(linear + "def ok (bx: LBox)(h: Eq(Nat, pairCount(bx.inner.a, bx.inner.b), 0)) : Nat := 0\n")
    accepts(linear + "def ok (bx: LBox)(h: Eq(Nat, pairCount(bx.inner.a, bx.c), 0)) : Nat := 0\n")
    accepts(linear + "def ok (p: LTagged(Nat))(h: Eq(Nat, pairCount(p.a, p.b), 0)) : Nat := 0\n")
    // A projection beside a match field of the same record, at another field, in a proposition's body.
    accepts(
      linear +
        "def ok (p: LTagged(Nat)) : Prop := {\n  match p returning Prop with\n  | LTagged.mk n x y => Eq(Nat, pairCount(x, p.b), 0)\n}\n"
    )
  }

  test("read: one field twice, a field with its record, or a field beside its own match field, overlaps") {
    rejectsWith[LinearReusedInType](linear + "def bad (p: LPair)(h: Eq(Nat, pairCount(p.a, p.a), 0)) : Nat := 0\n")
    rejectsWith[LinearReusedInType](
      linear + "def bad (p: LPair)(h: Eq(Nat, pairCount(p.a, LPair.a(p)), 0)) : Nat := 0\n"
    )
    rejectsWith[LinearReusedInType](linear + "def bad (p: LPair)(h: Eq(Nat, pairWith(p, p.b), 0)) : Nat := 0\n")
    rejectsWith[LinearReusedInType](
      linear + "def bad (bx: LBox)(h: Eq(Nat, pairWith(bx.inner, bx.inner.a), 0)) : Nat := 0\n"
    )
    rejectsWith[LinearReusedInType](
      linear + "def bad (bx: LBox)(h: Eq(Nat, pairCount(bx.inner.a, bx.inner.a), 0)) : Nat := 0\n"
    )
    // Through a let alias of the record, and of the field, in a proposition's body.
    rejectsWith[LinearReusedInType](
      linear + "def bad (p: LPair) : Prop := {\n  let q := p\n  let x := q.a\n  Eq(Nat, pairCount(x, p.a), 0)\n}\n"
    )
    // The index paths of projections and of match fields agree: n is field 0 of LTagged, so a is field 1.
    rejectsWith[LinearReusedInType](
      linear +
        "def bad (p: LTagged(Nat)) : Prop := {\n  match p returning Prop with\n  | LTagged.mk n x y => Eq(Nat, pairCount(x, p.a), 0)\n}\n"
    )
    rejectsWith[LinearReusedInType](
      linear +
        "def bad (p: LTagged(Nat)) : Prop := {\n  match p returning Prop with\n  | LTagged.mk n x y => Eq(Nat, pairCount(p.b, y), 0)\n}\n"
    )
  }

  test("read: a projection of a constructed record covers its whole provenance") {
    // `LPair.mk(xs, ys).a` is xs itself: it must not count as a part separate from xs.
    rejectsWith[LinearReusedInType](
      linear + "def bad (xs: LNats)(ys: LNats)(h: Eq(Nat, pairCount(LPair.mk(xs, ys).a, xs), 0)) : Nat := 0\n"
    )
    rejectsWith[LinearReusedInType](
      linear + "def bad (p: LPair)(h: Eq(Nat, pairCount(LPair.mk(p.b, p.a).a, p.b), 0)) : Nat := 0\n"
    )
    rejectsWith[LinearReusedInType](
      linear + "def bad (xs: LNats)(ys: LNats)(h: Eq(Nat, pairCount(LPair.mk(xs, ys).a, LPair.mk(xs, ys).b), 0)) : Nat := 0\n"
    )
  }

  test("read: a binder bound after its record was consumed is not jointly live with its field") {
    val src =
      linear +
        """
          |def bad (p: LPair) : Nat := {
          |  FIRST
          |  SECOND
          |  0
          |}
          |""".stripMargin
    val consume = "let gone := count(p.a)"
    val form = "let T : Prop := (u: LNats) -> Eq(Nat, pairCount(u, p.b), 0)"
    rejectsWith[LinearNotJointlyLive](src.replace("FIRST", consume).replace("SECOND", form))
    accepts(src.replace("FIRST", form).replace("SECOND", consume))
  }

  // A projection's type is a value, so a lambda in it over an earlier copyable field captures nothing (F5 is about
  // lambdas written in terms); a lambda over an earlier linear field is refused in the constructor's own telescope.
  test("a linear record whose field type holds a lambda over an earlier field") {
    val holds = "inductive Holds (P: Nat -> Prop) : Prop\n | mk {P: Nat -> Prop} (h: P(0)) : Holds(P)\n\n"
    val lr =
      linear + holds +
        "inductive LR : Lin(Level.zero)\n | mk (bound: Nat)(tok: LNats)(ok: Holds(fun (x: Nat): Prop => Eq(Nat, x, bound))) : LR\n\n"
    accepts(lr + "def ok (r: LR) : Nat := {\n  let h := r.ok\n  count(r.tok)\n}\n")
    rejectsWith[LinearReused](lr + "def bad (r: LR) : Nat := {\n  let n := r.bound\n  count(r.tok)\n}\n")
    rejectsWith[LinearCapture](
      linear + holds +
        "inductive Bad : Lin(Level.zero)\n | mk (tok: LNats)(ok: Holds(fun (x: Nat): Prop => Eq(Nat, x, count(tok)))) : Bad\n"
    )
  }

  test("kind-polymorphic: a record of a variable kind is tracked, so its projections use it") {
    accepts("def ok (A: Univ($k, $u))(p: Prod(A, A)) : A := p.fst\n")
    rejectsWith[LinearReused]("def bad (A: Univ($k, $u))(p: Prod(A, A)) : Prod(A, A) := Prod.mk(A, A, p.snd, p.fst)\n")
    rejectsWith[LinearReused](
      "def bad (A: Univ($k, $u))(p: Prod(A, A)) : Prod(A, A) := Prod.mk(A, A, p.fst, Prod.fst(p))\n"
    )
  }

  test("a measure is a read: it may read sibling fields, not one field twice") {
    accepts(linear + "def ok (p: LPair) : Nat decreases measure(pairCount(p.a, p.b)) := 0\n")
    rejectsWith[LinearReusedInType](linear + "def bad (p: LPair) : Nat decreases measure(pairCount(p.a, p.a)) := 0\n")
  }

  test("a field whose type reads an earlier linear field: the type reads its record, the term consumes it once") {
    val dep =
      linear +
        """
          |inductive Tag indices (n: Nat) : Type
          | | mk (n: Nat) : Tag(n)
          |
          |inductive Dep : Lin(Level.zero)
          | | mk (xs: LNats)(tag: Tag(count(xs))) : Dep
          |
          |""".stripMargin
    accepts(dep + "def ok (d: Dep) : Tag(count(d.xs)) := d.tag\n")
    rejectsWith[LinearReused](dep + "def bad (d: Dep) : Nat := {\n  let t := d.tag\n  count(d.xs)\n}\n")
    rejectsWith[TypeMismatch](dep + "def bad (d: Dep) : Tag(0) := d.tag\n")
  }

  // ==================================================================================================================
  // 2. Prop records: a projection out of a proof is the elimination its one-branch match would be.
  // ==================================================================================================================

  private val selfEq = "Exists(Nat, fun (x: Nat): Prop => Eq(Nat, x, x))"

  test("Prop: the witness of an Exists is data out of a proof, however written") {
    rejectsWith[PropEliminationRestricted](s"def bad (e: $selfEq) : Nat := e.witness\n")
    rejectsWith[PropEliminationRestricted](s"def bad (e: $selfEq) : Nat := Exists.witness(e)\n")
    rejectsWith[PropEliminationRestricted](
      s"def bad (e: $selfEq) : Nat := Exists.witness(Exists.intro(Nat, fun (x: Nat): Prop => Eq(Nat, x, x), 5, Eq.refl(5)))\n"
    )
  }

  // The proof's type reads the witness, so projecting it would hold the witness's projection in a type, where the
  // elimination of Eq into Nat reads it back; with proof irrelevance that equates 5 and 6.
  test("BREAK attempt: an Exists's proof field smuggles its witness out through Eq") {
    val exploit =
      s"""
         |def w (e: $selfEq) : Nat := {
         |  match PROOF returning Nat with
         |  | Eq.refl z => z
         |}
         |
         |def F (e: $selfEq) : Type := {
         |  match Nat.beq(w(e), 5) returning Type with
         |  | Bool.true => Unit
         |  | Bool.false => Empty
         |}
         |
         |def cast (p: $selfEq)(q: $selfEq)(x: F(p)) : F(q) := x
         |
         |def e5 : $selfEq := Exists.intro(Nat, fun (x: Nat): Prop => Eq(Nat, x, x), 5, Eq.refl(5))
         |
         |def e6 : $selfEq := Exists.intro(Nat, fun (x: Nat): Prop => Eq(Nat, x, x), 6, Eq.refl(6))
         |
         |def boom : Empty := cast(e5, e6, Unit.unit)
         |""".stripMargin
    rejectsWith[PropEliminationRestricted](exploit.replace("PROOF", "e.proof"))
    rejectsWith[PropEliminationRestricted](exploit.replace("PROOF", "Exists.proof(e)"))
    // Nested: a proof field of a proof field.
    rejectsWith[PropEliminationRestricted](
      s"inductive Wrap : Prop\n | mk (e: $selfEq) : Wrap\n\n" +
        exploit
          .replace(s"def w (e: $selfEq)", "def w (u: Wrap)")
          .replace("PROOF", "u.e.proof")
          .replace("w(e)", "w(Wrap.mk(e))")
    )
  }

  test("Prop: Protocol.Valid's fields: data, and a proof whose type reads the data field rest") {
    val p = "def P : Protocol.Proto := Protocol.Proto.mk(Nat, fun (A: List(Nat))(B: List(Nat)): Prop => False)\n\n"
    val v = "(v: Protocol.Valid(P, List.nil(Nat), List.nil(Nat)))"
    rejectsWith[PropEliminationRestricted](p + s"def bad $v : List(Nat) := v.rest\n")
    rejectsWith[PropEliminationRestricted](p + s"def bad $v : List(Nat) := v.C\n")
    rejectsWith[PropEliminationRestricted](p + s"def bad $v : Nat := {\n  let r := v.r\n  0\n}\n")
  }

  test("Prop: a type field and a field typed by it are refused; a proof field of proofs is small elimination") {
    val typed = "inductive HasType : Prop\n | mk (T: Type)(t: T) : HasType\n\n"
    rejectsWith[PropEliminationRestricted](typed + "def bad (h: HasType) : Type := h.T\n")
    rejectsWith[PropEliminationRestricted](typed + "def bad (h: HasType) : Nat := {\n  let x := h.t\n  0\n}\n")
    accepts("def ok (P: Prop)(Q: Prop)(h: And(P, Q)) : Q := h.right\n")
    accepts("def ok (P: Prop)(Q: Prop)(h: Iff(P, Q))(p: P) : Q := Iff.mp(h)(p)\n")
    accepts(
      "def ok (h: Subsingleton(Unit)) : Eq(Unit, Unit.unit, Unit.unit) := Subsingleton.elim(h)(Unit.unit, Unit.unit)\n"
    )
  }

  test("Prop, sound controls: a data field its index determines, and a proof field over the index") {
    // One proof per index, whose field is that index: the large elimination a match allows.
    accepts(
      "inductive IsN indices (n: Nat) : Prop\n | mk (n: Nat) : IsN(n)\n\n" +
        "def get (k: Nat)(h: IsN(k)) : Nat := h.n\n\n" +
        "def five : Eq(Nat, IsN.mk(5).n, 5) := Eq.refl(5)\n"
    )
    // m is undetermined, so no data field projects; h's type reads n, which the index solves, so h reads no data.
    val w = "inductive W indices (n: Nat) : Prop\n | mk (n: Nat)(m: Nat)(h: Eq(Nat, n, n)) : W(n)\n\n"
    accepts(w + "def ok (k: Nat)(x: W(k)) : Eq(Nat, k, k) := x.h\n")
    rejectsWith[PropEliminationRestricted](w + "def bad (k: Nat)(x: W(k)) : Nat := x.m\n")
  }

  // ==================================================================================================================
  // 3. Recursive records: projections, no eta, and the family's final head.
  // ==================================================================================================================

  private val tree =
    """
      |inductive Tree : Type
      | | node (val: Nat)(kids: List(Tree)) : Tree
      |
      |""".stripMargin

  test("recursive: projections type and compute on constructors, and stay stuck on neutral values") {
    accepts(tree + "def v (t: Tree) : Nat := t.val\n\ndef ks (t: Tree) : List(Tree) := Tree.kids(t)\n")
    accepts(tree + "def one : Eq(Nat, Tree.node(1, List.nil(Tree)).val, 1) := Eq.refl(1)\n")
    rejectsWith[TypeMismatch](tree + "def bad (t: Tree) : Eq(Nat, t.val, 0) := Eq.refl(0)\n")
    rejectsWith[TypeMismatch](tree + "def bad (t: Tree) : Eq(Nat, t.val, Tree.node(0, t.kids).val) := Eq.refl(t.val)\n")
  }

  test("recursive: no eta, so a neutral tree is not its constructor applied to its projections") {
    rejectsWith[TypeMismatch](tree + "def bad (t: Tree) : Eq(Tree, t, Tree.node(t.val, t.kids)) := Eq.refl(t)\n")
    rejectsWith[TypeMismatch](tree + "def bad (t: Tree) : Eq(Tree, Tree.node(t.val, t.kids), t) := Eq.refl(t)\n")
  }

  test("recursive: a field's type names the final family, so its elements project") {
    accepts(
      tree +
        "def firstVal (t: Tree) : Nat := {\n  match t.kids with\n  | List.nil => 0\n  | List.cons k rest => k.val\n}\n"
    )
    accepts(
      """
        |mutual {
        |  inductive A : Type
        |   | mk (bs: List(B)) : A
        |
        |  inductive B : Type
        |   | mk (n: Nat)(a: Option(A)) : B
        |}
        |
        |def firstN (a: A) : Nat := {
        |  match a.bs with
        |  | List.nil => 0
        |  | List.cons b rest => b.n
        |}
        |
        |def back (b: B) : Nat := {
        |  match b.a with
        |  | Option.none => 0
        |  | Option.some a => firstN(a)
        |}
        |""".stripMargin
    )
  }

  // ==================================================================================================================
  // 4. Termination: a projection of a neutral record is a structural subterm exactly when eta makes it a field.
  // ==================================================================================================================

  test("termination: a recursive record's projection of a neutral root is no subterm") {
    rejectsWith[NonDecreasingRecursiveCall](
      tree +
        "def bad (t: Tree) : Nat decreases structural(t) := {\n  match t.kids with\n  | List.nil => 0\n  | List.cons k rest => bad(k)\n}\n"
    )
    rejectsWith[NonDecreasingRecursiveCall](
      "inductive Loop : Type\n | mk (next: Option(Loop)) : Loop\n\n" +
        "def bad (l: Loop) : Nat decreases structural(l) := {\n  match l.next with\n  | Option.none => 0\n  | Option.some m => bad(m)\n}\n"
    )
  }

  test("termination, sound controls: after the root is matched, its projections are its fields") {
    accepts(
      tree +
        "def size (t: Tree) : Nat decreases structural(t) := {\n  match t with\n  | Tree.node v ks => {\n    match t.kids with\n    | List.nil => 1\n    | List.cons k rest => Nat.add(1, size(k))\n  }\n}\n"
    )
    accepts(
      "inductive Loop : Type\n | mk (next: Option(Loop)) : Loop\n\n" +
        "def ok (l: Loop) : Nat decreases structural(l) := {\n  match l with\n  | Loop.mk n => {\n    match l.next with\n    | Option.none => 0\n    | Option.some m => ok(m)\n  }\n}\n"
    )
  }

  test("termination: an eta rebuild of a record, or a projection of it, is no smaller than it") {
    rejectsWith[NonDecreasingRecursiveCall](
      "def bad (p: Prod(Nat, Nat)) : Nat decreases structural(p) := bad(Prod.mk(Nat, Nat, Prod.fst(p), p.snd))\n"
    )
    rejectsWith[NonDecreasingRecursiveCall](
      "def bad (p: Prod(Prod(Nat, Nat), Nat)) : Nat decreases structural(p) := bad(Prod.mk(Prod(Nat, Nat), Nat, p.fst, p.snd))\n"
    )
  }

  // ==================================================================================================================
  // 5. Eta between projections and constructors.
  // ==================================================================================================================

  test("eta: projections and constructors convert, field by field, however projections are written") {
    accepts(
      "def a (p: Prod(Nat, Nat)) : Eq(Prod(Nat, Nat), p, Prod.mk(Nat, Nat, p.fst, Prod.snd(p))) := Eq.refl(p)\n"
    )
    accepts("def b (p: Prod(Nat, Nat)) : Eq(Nat, Prod.mk(Nat, Nat, p.snd, p.fst).fst, p.snd) := Eq.refl(p.snd)\n")
    accepts("def c (p: Prod(Nat, Nat)) : Eq(Nat, Prod.fst(p), p.fst) := Eq.refl(p.fst)\n")
    accepts(
      "def swap (p: Prod(Nat, Nat)) : Prod(Nat, Nat) := Prod.mk(Nat, Nat, p.snd, p.fst)\n\n" +
        "def d (p: Prod(Nat, Nat)) : Eq(Prod(Nat, Nat), swap(swap(p)), p) := Eq.refl(p)\n"
    )
    accepts(
      "def e (s: Sigma(Nat, Level.zero, fun (n: Nat): Type => Nat))\n" +
        "    : Eq(Sigma(Nat, Level.zero, fun (n: Nat): Type => Nat), s, Sigma.mk(Nat, Level.zero, fun (n: Nat): Type => Nat, s.fst, s.snd)) := Eq.refl(s)\n"
    )
  }

  test("eta: a neutral record's projections are built once each, so a wide record converts quickly") {
    // Each projection's type holds the earlier ones; building them recursively doubled the work with every field.
    val count = 40
    val fields = (0 until count).map(i => s"(f$i: Nat)").mkString
    val projections = (0 until count).map(i => s"r.f$i").mkString(", ")
    accepts(s"inductive R : Type\n | mk $fields : R\n\ndef eta (r: R) : Eq(R, r, R.mk($projections)) := Eq.refl(r)\n")
  }

  test("eta: different fields, and fields of different records, stay apart") {
    rejectsWith[TypeMismatch]("def bad (p: Prod(Nat, Nat)) : Eq(Nat, p.fst, p.snd) := Eq.refl(p.fst)\n")
    rejectsWith[TypeMismatch](
      "def bad (p: Prod(Nat, Nat))(q: Prod(Nat, Nat)) : Eq(Nat, p.fst, q.fst) := Eq.refl(p.fst)\n"
    )
    rejectsWith[TypeMismatch](
      "def bad (p: Prod(Nat, Nat)) : Eq(Prod(Nat, Nat), p, Prod.mk(Nat, Nat, p.snd, p.fst)) := Eq.refl(p)\n"
    )
  }

  test("eta: a quoted projection evaluates back to the same projection, at a record without eta") {
    // The match's result type is inferred by quoting its branch's, which holds `t.val`.
    accepts(
      tree +
        "def same (t: Tree)(b: Bool) : Eq(Nat, t.val, t.val) := {\n  let r := match b with\n  | Bool.true => Eq.refl(t.val)\n  | Bool.false => Eq.refl(t.val)\n  r\n}\n"
    )
  }

  // ==================================================================================================================
  // 6. Projections under refinement and in types.
  // ==================================================================================================================

  test("refinement: a projection of a value whose type a branch refines to a record") {
    val f =
      "def F (b: Bool) : Type := {\n  match b returning Type with\n  | Bool.true => Prod(Nat, Nat)\n  | Bool.false => Nat\n}\n\n"
    accepts(
      f + "def g (b: Bool)(x: F(b)) : Nat := {\n  match b returning Nat with\n  | Bool.true => x.fst\n  | Bool.false => x\n}\n"
    )
    rejectsWith[NotFound](f + "def bad (b: Bool)(x: F(b)) : Nat := x.fst\n")
  }

  test("in types: a binder type and a codomain read projections, which follow the record") {
    accepts(
      "def ty (p: Prod(Type, Nat))(x: p.fst) : p.fst := x\n\n" +
        "def use : Eq(Nat, ty(Prod.mk(Type, Nat, Nat, 0), 5), 5) := Eq.refl(5)\n"
    )
    rejectsWith[TypeMismatch]("def bad (p: Prod(Type, Type))(x: p.fst) : p.snd := x\n")
    accepts("def ok (r: Prod(Nat -> Type, Nat))(x: (r.fst(0))) : (r.fst(0)) := x\n")
    rejectsWith[TypeMismatch]("def bad (r: Prod(Nat -> Type, Nat))(x: (r.fst(0))) : (r.fst(1)) := x\n")
  }

  // ==================================================================================================================
  // 7. Hidden dependencies and indexed families.
  // ==================================================================================================================

  private val vec =
    """
      |inductive Vec (A: Type) indices (n: Nat) : Type
      | | nil {A: Type} : Vec(A, Nat.zero)
      | | cons {A: Type} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
      |
      |def sameLen (v1: Vec(Nat, $n))(v2: Vec(Nat, n)) : Nat := n
      |
      |""".stripMargin

  test("hidden dependency: a field whose type no argument determines has no projection, nor one typed by it") {
    val hv =
      vec + "inductive HV (A: Type) : Type\n | mk {A: Type} (k: Nat)(v: Vec(A, $n))(e: Eq(Vec(A, n), v, v)) : HV(A)\n\n"
    accepts(hv + "def k (h: HV(Nat)) : Nat := h.k\n")
    rejectsWith[InvalidStruct](hv + "def bad (h: HV(Nat)) : Nat := sameLen(h.v, h.v)\n")
    rejectsWith[InvalidStruct](hv + "def bad (h: HV(Nat)) : Nat := {\n  let x := h.e\n  0\n}\n")
    rejectsWith[InvalidStruct](hv + "def bad (h: HV(Nat)) : Nat := sameLen(HV.v(h), HV.v(h))\n")
    // A constructed record's field is its stored field, typed as stored.
    accepts(hv + "def ok (v: Vec(Nat, $n)) : Nat := sameLen(HV.mk(Nat, 0, v, Eq.refl(v)).v, v)\n")
    // A record that hides a dependency has no eta: a neutral value is not its constructor.
    rejectsWith[TypeMismatch](
      vec + "inductive H2 : Type\n | mk (v: Vec(Nat, $n)) : H2\n\ndef bad (x: H2)(y: H2) : Eq(H2, x, y) := Eq.refl(x)\n"
    )
  }

  test("indexed: a field typed by the index projects at it, and the index does not leak into other fields") {
    val wrap =
      vec + "inductive WrapIdx (A: Type) indices (n: Nat) : Type\n | mk {A: Type} (x: Vec(A, $n)) : WrapIdx(A, n)\n\n"
    accepts(wrap + "def get (n: Nat)(w: WrapIdx(Nat, n)) : Vec(Nat, n) := w.x\n")
    rejectsWith[TypeMismatch](wrap + "def bad (n: Nat)(w: WrapIdx(Nat, n)) : Vec(Nat, Nat.succ(n)) := w.x\n")
    val sized = vec + "inductive Sized indices (n: Nat) : Type\n | mk (k: Nat)(v: Vec(Nat, k)) : Sized(k)\n\n"
    accepts(sized + "def len (n: Nat)(s: Sized(n)) : Vec(Nat, n) := s.v\n")
    // k is the index for every constructor value, but its projection is not definitionally the index.
    rejectsWith[TypeMismatch](sized + "def bad (n: Nat)(s: Sized(n)) : Eq(Nat, s.k, n) := Eq.refl(n)\n")
  }

  test("indexed: a stuck index equation leaves the fields their own, and a solved one solves them") {
    val g = vec + "inductive G indices (k: Nat) : Type\n | mk (m: Nat)(v: Vec(Nat, m)) : G(Nat.succ(m))\n\n"
    accepts(g + "def gv (k: Nat)(x: G(k)) : Vec(Nat, x.m) := x.v\n")
    accepts(g + "def g3 (x: G(3)) : Vec(Nat, 2) := x.v\n")
    rejectsWith[TypeMismatch](g + "def bad (x: G(3)) : Vec(Nat, 3) := x.v\n")
    rejectsWith[TypeMismatch](g + "def bad (k: Nat)(x: G(k)) : Vec(Nat, k) := x.v\n")
    // At an instance no constructor reaches, the field keeps its own type, as a match's unreachable branch would.
    accepts(g + "def none (x: G(0)) : Nat := x.m\n")
  }

  test("indexed: a field that names a global like the index reads the global") {
    rejectsWith[TypeMismatch](
      "def n : Nat := 0\n\ninductive T indices (n: Nat) : Type\n | mk (h: Eq(Nat, n, 0)) : T(5)\n\n" +
        "def bad (t: T(5)) : Eq(Nat, 5, 0) := t.h\n"
    )
  }

  // ==================================================================================================================
  // 8. Names: fields beside namespace members, constructors, globals and opens.
  // ==================================================================================================================

  private val r = "inductive R : Type\n | mk (len: Nat) : R\n\n"

  test("names: a field is declared in its record's namespace, so no member there shares its name") {
    rejectsWith[AlreadyDefined](r + "def R.len (r: R) : Nat := 0\n")
    rejectsWith[AlreadyDefined](r + "namespace R {\n  def len : Nat := 0\n}\n")
    rejectsWith[AlreadyDefined]("namespace R {\n  def len : Nat := 0\n}\n\n" + r)
    rejectsWith[AlreadyDefined]("inductive R : Type\n | mk (mk: Nat) : R\n")
    rejectsWith[AlreadyDefined](
      "mutual {\n  inductive S : Type\n   | mk (len: Nat) : S\n\n  inductive T : Type\n   | node : T\n}\n\ndef S.len : Nat := 0\n"
    )
  }

  test("names: a selection names a field only; a global in the record's namespace is applied as written") {
    val twice = r + "def R.twice (r: R) : Nat := Nat.add(r.len, r.len)\n\n"
    accepts(twice + "def ok (r: R) : Nat := R.twice(r)\n")
    rejectsWith[NotFound](twice + "def bad (r: R) : Nat := r.twice\n")
    // A global named like a field is another name: the field is selected from a record, the global is not.
    accepts(r + "def len : Nat := 5\n\ndef ok : Eq(Nat, Nat.add(R.mk(1).len, len), 6) := Eq.refl(6)\n")
    rejectsWith[NotFound](r + "def bad (r: R) : Nat := r.size\n")
  }

  test("names: an open aliases a field, and the alias is its selection") {
    accepts(r + "open R\n\ndef ok (r: R) : Nat := len(r)\n")
    accepts(r + "open R.{len as size}\n\ndef ok (r: R) : Eq(Nat, size(R.mk(3)), 3) := Eq.refl(3)\n")
    // A local of the field's name shadows the alias, and a dotted local path is its projection.
    accepts(r + "open R\n\ndef ok (r: R)(len: Nat) : Nat := Nat.add(len, r.len)\n")
  }

  test("names: Fam.field(e) needs e of the family Fam, exactly one argument, and is no function value") {
    val fstOf = "inductive Mine : Type\n | mk (fst: Nat)(snd: Nat) : Mine\n\n"
    rejectsWith[TypeMismatch](fstOf + "def bad (m: Mine) : Nat := Prod.fst(m)\n")
    rejectsWith[TypeMismatch](fstOf + "def bad (p: Prod(Nat, Nat)) : Nat := Mine.fst(p)\n")
    rejectsWith[ArityMismatch]("def bad (p: Prod(Nat, Nat)) : Nat := Prod.fst(p, 1)\n")
    rejectsWith[UnappliedField]("def bad : Prod(Nat, Nat) -> Nat := Prod.fst\n")
    rejectsWith[UnappliedField](
      "def bad (ps: List(Prod(Nat, Nat))) : List(Nat) := List.map(ps, Nat, Prod.fst)\n"
    )
    accepts(fstOf + "def ok (m: Mine)(p: Prod(Nat, Nat)) : Nat := Nat.add(Mine.fst(m), Prod.fst(p))\n")
  }

  test("names: a multi-constructor family has no fields, nor has a non-family base") {
    rejectsWith[NotFound]("def bad (b: Bool) : Nat := b.len\n")
    rejectsWith[NotFound]("def bad (f: Nat -> Nat) : Nat := f.fst\n")
  }
}
