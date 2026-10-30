package com.raccoonlang

import com.raccoonlang.ProgramFixtures._
import com.raccoonlang.Value._

/**
 * The resource-protocol primitives and the root supply (docs/kernel.md, "Resource protocols"): `Protocol.new`,
 * `Protocol.step` and `Protocol.observe`, their reductions R1–R3, the ghosts they build, and the entry, a program body
 * of type `(sup: Protocol.Supply) -> R` that `Interpreter.run` applies to the root supply. Every program runs without
 * user axioms, except those that show S3, which `--no-user-axioms` would reject first.
 */
class ProtocolPrimitivesTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs._

  /** For the tests of S3, which `--no-user-axioms` would preempt with `UserAxiom`. */
  private val withUserAxioms = new Programs(Prelude.default, allowUserAxioms = true)

  /** `Shares`: atoms are amounts; `split` into positive parts, `join`, and `release : [q] -> []`. */
  private val shares =
    """
      |def l0 : List(Nat) := List.nil(Nat)
      |def l1 (a: Nat) : List(Nat) := List.cons(a, List.nil(Nat))
      |def l2 (a: Nat)(b: Nat) : List(Nat) := List.cons(a, List.cons(b, List.nil(Nat)))
      |
      |inductive Shares indices (consumed: List(Nat))(produced: List(Nat)) : Prop
      | | split (q: Nat)(r: Nat) : Shares(l1(Nat.add(Nat.succ(q), Nat.succ(r))), l2(Nat.succ(q), Nat.succ(r)))
      | | join (q: Nat)(r: Nat) : Shares(l2(q, r), l1(Nat.add(q, r)))
      | | release (q: Nat) : Shares(l1(q), l0)
      |
      |def total (xs: List(Nat)) : Nat decreases structural(xs) := {
      |  match xs with
      |  | List.nil => 0
      |  | List.cons x rest => Nat.add(x, total(rest))
      |}
      |
      |inductive Le (a: Nat)(b: Nat) : Prop
      | | mk {a: Nat}{b: Nat} (k: Nat)(e: Eq(Nat, Nat.add(a, k), b)) : Le(a, b)
      |
      |def addZero (q: Nat)(k: Nat)(h: Eq(Nat, Nat.add(q, k), 0)) : Eq(Nat, q, 0) := {
      |  match q returning Eq(Nat, q, 0) with
      |  | Nat.zero => Eq.refl(0)
      |  | Nat.succ q1 => {
      |    match h returning Eq(Nat, Nat.succ(q1), 0) with
      |  }
      |}
      |
      |def permTotal (xs: List(Nat))(ys: List(Nat))(p: List.Perm(Nat, xs, ys))
      |    : Eq(Nat, total(xs), total(ys)) decreases structural(p) := {
      |  match p returning Eq(Nat, total(xs), total(ys)) with
      |  | List.Perm.nil => Eq.refl(0)
      |  | List.Perm.cons x xs1 ys1 q =>
      |      congrArg(permTotal(xs1, ys1, q), Nat, fun (m: Nat): Nat => Nat.add(x, m))
      |  | List.Perm.swap x y zs => Eq.refl(total(List.cons(y, List.cons(x, zs))))
      |  | List.Perm.trans as1 bs1 cs1 q r => Eq.trans(permTotal(as1, bs1, q), permTotal(bs1, cs1, r))
      |}
      |
      |def reachBound (n: Nat)(C: List(Nat))(r: Protocol.Reach(Protocol.Proto.mk(Nat, Shares), l1(n), C))
      |    : Le(total(C), n) decreases structural(r) := {
      |  match r returning Le(total(C), n) with
      |  | Protocol.Reach.initial => Le.mk(total(l1(n)), n, 0, Eq.refl(n))
      |  | Protocol.Reach.step A B frame h prev => {
      |    match h returning Le(total(List.append(B, frame)), n) with
      |    | Shares.split q r1 => reachBound(n, List.append(A, frame), prev)
      |    | Shares.join q r1 => reachBound(n, List.append(A, frame), prev)
      |    | Shares.release q => {
      |      match reachBound(n, List.append(A, frame), prev) returning Le(total(frame), n) with
      |      | Le.mk k e => Le.mk(total(frame), n, Nat.add(q, k), e)
      |    }
      |  }
      |  | Protocol.Reach.perm C1 D1 prev p =>
      |      Eq.substProp(permTotal(C1, D1, p), fun (x: Nat): Prop => Le(x, n), reachBound(n, C1, prev))
      |}
      |
      |def pairBound (n: Nat)(q: Nat)(r: Nat)(v: Protocol.Valid(Protocol.Proto.mk(Nat, Shares), l1(n), l2(q, r))) : Le(Nat.add(q, r), n) := {
      |  match v returning Le(Nat.add(q, r), n) with
      |  | Protocol.Valid.mk C rest r1 => {
      |    match reachBound(n, List.append(C, rest), r1) returning Le(Nat.add(q, r), n) with
      |    | Le.mk k e => Le.mk(Nat.add(q, r), n, Nat.add(total(rest), k), e)
      |  }
      |}
      |
      |def heldCoverage (n: Nat)(q: Nat)(v: Protocol.Valid(Protocol.Proto.mk(Nat, Shares), l1(n), l2(n, q))) : Eq(Nat, q, 0) := {
      |  match pairBound(n, n, q, v) returning Eq(Nat, q, 0) with
      |  | Le.mk k e => addZero(q, k, congrArg(e, Nat, fun (x: Nat): Nat => Nat.sub(x, n)))
      |}
      |
      |def Spent (n: Nat)(C: List(Nat))(rest: List(Nat)) : Prop :=
      |  And(Protocol.Reach(Protocol.Proto.mk(Nat, Shares), l1(n), List.append(C, rest)), Eq(Nat, total(rest), 0))
      |
      |def NoOtherShares (n: Nat)(C: List(Nat)) : Prop :=
      |  Exists(List(Nat), fun (rest: List(Nat)): Prop => Spent(n, C, rest))
      |
      |def noOtherShares (n: Nat)(v: Protocol.Valid(Protocol.Proto.mk(Nat, Shares), l1(n), l1(n))) : NoOtherShares(n, l1(n)) := {
      |  match v returning NoOtherShares(n, l1(n)) with
      |  | Protocol.Valid.mk C rest r => {
      |    match reachBound(n, List.append(C, rest), r) returning NoOtherShares(n, l1(n)) with
      |    | Le.mk k e =>
      |        Exists.intro(List(Nat), fun (rest1: List(Nat)): Prop => Spent(n, l1(n), rest1), rest,
      |          And.intro(Protocol.Reach(Protocol.Proto.mk(Nat, Shares), l1(n), List.append(l1(n), rest)), Eq(Nat, total(rest), 0), r,
      |            addZero(total(rest), k, congrArg(e, Nat, fun (x: Nat): Nat => Nat.sub(x, n)))))
      |  }
      |}
      |
      |""".stripMargin

  /** Consuming packets of `Shares`: releasing one or two shares, and ending on an empty packet. */
  private val releases =
    shares +
      """
        |def releaseOne (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), init))(a: Nat)
        |    (toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), init, s, l1(a))) : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), init, s, l0) :=
        |  Protocol.step(Protocol.Proto.mk(Nat, Shares), init, s, l1(a), l0, Shares.release(a), toks)
        |
        |def releaseTwo (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), init))(q: Nat)(r: Nat)
        |    (toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), init, s, l2(q, r))) : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), init, s, l0) := {
        |  let whole := Protocol.step(Protocol.Proto.mk(Nat, Shares), init, s, l2(q, r), l1(Nat.add(q, r)), Shares.join(q, r), toks)
        |  releaseOne(init, s, Nat.add(q, r), whole)
        |}
        |
        |def done (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), init))(toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), init, s, l0))
        |    (R: Type)(x: R) : R := {
        |  match toks with
        |  | Protocol.Toks.nil => x
        |}
        |
        |""".stripMargin

  /** Packet split and join (`ProgramFixtures.packets`), over `Both`. */
  private val packets = ProgramFixtures.packets

  test("Shares: Reach induction bounds every configuration, and observed pairs and held coverage follow") {
    run(shares)
  }

  test("an entry creates, splits, observes, joins and releases, drops its last supply, and run computes its result") {
    val entry =
      shares +
        """
          |fun (sup: Protocol.Supply): Nat => {
          |  let (next, s, toks) := Protocol.new(Protocol.Proto.mk(Nat, Shares), l1(2), sup)
          |  let halves := Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2), l2(1, 1), Shares.split(0, 0), toks)
          |  let (seen, valid) := Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1), halves)
          |  let bound : Le(Nat.add(1, 1), 2) := pairBound(2, 1, 1, valid)
          |  let whole := Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1), l1(2), Shares.join(1, 1), seen)
          |  let (held, all) := Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2), whole)
          |  let complete : NoOtherShares(2, l1(2)) := noOtherShares(2, all)
          |  match held with
          |  | Protocol.Toks.cons a t C rest => {
          |    let gone := Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(a), l0, Shares.release(a),
          |      Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(2), s, a, t, C, rest))
          |    match gone with
          |    | Protocol.Toks.nil => a
          |  }
          |}
          |""".stripMargin
    assertEquals(result(entry), "2")
  }

  test("an entry's result is stuck while checking sees a supply variable, and computed by run from the root") {
    val src =
      releases +
        """
          |fun (sup: Protocol.Supply): Nat => {
          |  let (next, s, toks) := Protocol.new(Protocol.Proto.mk(Nat, Shares), l1(7), sup)
          |  match toks with
          |  | Protocol.Toks.cons a t C rest =>
          |      done(l1(7), s, releaseOne(l1(7), s, a, Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(7), s, a, t, C, rest)), Nat,
          |        a)
          |}
          |""".stripMargin
    val program = parse(src)
    val env = program.decls.foldLeft(Interpreter.initialEnv(Prelude.default)) { case (env, decl) =>
      Interpreter.evalDecl(decl, env)
    }
    // Checking yields a closure; applied to a supply variable, as its body was checked, R1 cannot fire.
    val entry = TypeChecker.checkTerm(program.body.get, env).value
    val sup = FreshVar.freshVar("sup", Kernel.supplyType)
    val stuck = Interpreter.evalApply(entry, Vector(sup))
    assert(ReductionBlockers.of(stuck).contains(sup.id), PrettyPrinter.print(stuck))
    // Solving the variable as the root supply resumes R1, as run's application does directly.
    val store = EqStore.empty.allow(DepSet.single(sup.id)).addLink(sup.id, ProtocolPrimitives.rootSupply)
    assertEquals(PrettyPrinter.print(Interpreter.resolveInEqStore(stuck, store)), "7")
    assertEquals(result(src), "7")
  }

  test("a global function of entry type named as the body is an entry; a body of another type runs as before") {
    assertEquals(result(shares + "def main (sup: Protocol.Supply) : Nat := 3\n\nmain\n"), "3")
    // Two binders are not an entry's type, so the body is a function value, printed as such.
    assertEquals(
      result(shares + "def two (sup: Protocol.Supply)(n: Nat) : Nat := n\n\ntwo\n"),
      "func#two"
    )
  }

  test("two instances from one supply are distinct identities, stored in a list and returned") {
    val src =
      releases +
        """
          |fun (sup: Protocol.Supply): List(Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(1))) => {
          |  let (sup1, s1, toks1) := Protocol.new(Protocol.Proto.mk(Nat, Shares), l1(1), sup)
          |  let (sup2, s2, toks2) := Protocol.new(Protocol.Proto.mk(Nat, Shares), l1(1), sup1)
          |  let ids := List.cons(s1, List.cons(s2, List.nil(Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(1)))))
          |  let ids1 := done(l1(1), s1, releaseOne(l1(1), s1, 1, toks1), List(Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(1))), ids)
          |  let ids2 := done(l1(1), s2, releaseOne(l1(1), s2, 1, toks2), List(Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(1))), ids1)
          |  ids2
          |}
          |""".stripMargin
    assertEquals(
      result(src),
      "[inst#(Protocol.Proto.mk(Nat, Shares), [1], 0), inst#(Protocol.Proto.mk(Nat, Shares), [1], 1)]"
    )
  }

  test("a builder returns the next supply and an identity packaged with its packet, which its caller steps") {
    val src =
      releases +
        """
          |inductive Built (init: List(Nat)) : Lin(Level.zero)
          | | mk {init: List(Nat)} (next: Protocol.Supply)(s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), init))
          |     (toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), init, s, init)) : Built(init)
          |
          |def build (init: List(Nat))(sup: Protocol.Supply) : Built(init) := {
          |  let (next, s, toks) := Protocol.new(Protocol.Proto.mk(Nat, Shares), init, sup)
          |  Built.mk(init, next, s, toks)
          |}
          |
          |fun (sup: Protocol.Supply): Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)) => {
          |  let (next, s, toks) := build(l1(2), sup)
          |  let halves := Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2), l2(1, 1), Shares.split(0, 0), toks)
          |  done(l1(2), s, releaseTwo(l1(2), s, 1, 1, halves), Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)), s)
          |}
          |""".stripMargin
    assertEquals(result(src), "inst#(Protocol.Proto.mk(Nat, Shares), [2], 0)")
  }

  test("a step without inputs mints tokens from the empty packet") {
    val src =
      shares +
        """
          |inductive Mint indices (consumed: List(Nat))(produced: List(Nat)) : Prop
          | | mint (k: Nat) : Mint(l0, l1(k))
          | | burn (k: Nat) : Mint(l1(k), l0)
          |
          |fun (sup: Protocol.Supply): Nat => {
          |  let (next, s, toks) := Protocol.new(Protocol.Proto.mk(Nat, Mint), l0, sup)
          |  match toks with
          |  | Protocol.Toks.nil => {
          |    let minted := Protocol.step(Protocol.Proto.mk(Nat, Mint), l0, s, l0, l1(5), Mint.mint(5), Protocol.Toks.nil(Protocol.Proto.mk(Nat, Mint), l0, s))
          |    match minted with
          |    | Protocol.Toks.cons a t C rest => {
          |      let gone := Protocol.step(Protocol.Proto.mk(Nat, Mint), l0, s, l1(a), l0, Mint.burn(a), Protocol.Toks.cons(Protocol.Proto.mk(Nat, Mint), l0, s, a, t, C, rest))
          |      match gone with
          |      | Protocol.Toks.nil => a
          |    }
          |  }
          |}
          |""".stripMargin
    assertEquals(result(src), "5")
  }

  test("a token-first wrapper returns two tokens with their bound") {
    val src =
      releases +
        """
          |inductive Pair (n: Nat)(s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(n))) : Lin(Level.zero)
          | | mk {n: Nat}{s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(n))} (q: Nat)(r: Nat)(tq: Protocol.Tok(Protocol.Proto.mk(Nat, Shares), l1(n), s, q))
          |     (tr: Protocol.Tok(Protocol.Proto.mk(Nat, Shares), l1(n), s, r))(bound: Le(Nat.add(q, r), n)) : Pair(n, s)
          |
          |def observePair (n: Nat)(s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(n)))(q: Nat)(r: Nat)
          |    (toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(n), s, l2(q, r))) : Pair(n, s) := {
          |  let (seen, valid) := Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(n), s, l2(q, r), toks)
          |  match seen with
          |  | Protocol.Toks.cons a tq C rest => {
          |    match rest with
          |    | Protocol.Toks.cons b tr D last => {
          |      match last with
          |      | Protocol.Toks.nil => Pair.mk(n, s, q, r, tq, tr, pairBound(n, q, r, valid))
          |    }
          |  }
          |}
          |
          |fun (sup: Protocol.Supply): Nat => {
          |  let (next, s, toks) := Protocol.new(Protocol.Proto.mk(Nat, Shares), l1(3), sup)
          |  let parts := Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(3), s, l1(3), l2(1, 2), Shares.split(0, 1), toks)
          |  let (q, r, tq, tr, bound) := observePair(3, s, 1, 2, parts)
          |  let packet := Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(3), s, q, tq, l1(r),
          |    Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(3), s, r, tr, l0, Protocol.Toks.nil(Protocol.Proto.mk(Nat, Shares), l1(3), s)))
          |  done(l1(3), s, releaseTwo(l1(3), s, q, r, packet), Nat, Nat.add(q, r))
          |}
          |""".stripMargin
    assertEquals(result(src), "3")
  }

  test("a framed step acts on part of a packet") {
    val src =
      releases + packets +
        """
          |def stepFramed (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), init))(A: List(Nat))(B: List(Nat))(F: List(Nat))
          |    (h: Shares(A, B))(toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), init, s, List.append(A, F)))
          |    : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), init, s, List.append(B, F)) := {
          |  let (part, frame) := splitToks(Nat, Shares, init, s, A, F, toks)
          |  joinToks(Nat, Shares, init, s, B, F, Protocol.step(Protocol.Proto.mk(Nat, Shares), init, s, A, B, h, part), frame)
          |}
          |
          |fun (sup: Protocol.Supply): Nat => {
          |  let (next, s, toks) := Protocol.new(Protocol.Proto.mk(Nat, Shares), l1(5), sup)
          |  let parts := Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(5), s, l1(5), l2(1, 4), Shares.split(0, 3), toks)
          |  let left := stepFramed(l1(5), s, l1(1), l0, l1(4), Shares.release(1), parts)
          |  match left with
          |  | Protocol.Toks.cons a t C rest =>
          |      done(l1(5), s, releaseOne(l1(5), s, a, Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(5), s, a, t, C, rest)), Nat,
          |        a)
          |}
          |""".stripMargin
    assertEquals(result(src), "4")
  }

  test("CountedShares: an authority atom counting live shares gives completeness without exit accounting") {
    run(
      """
        |inductive CAtom : Type
        | | out (k: Nat) : CAtom
        | | share (q: Nat) : CAtom
        |
        |def c1 (a: CAtom) : List(CAtom) := List.cons(a, List.nil(CAtom))
        |def c2 (a: CAtom)(b: CAtom) : List(CAtom) := List.cons(a, c1(b))
        |def c3 (a: CAtom)(b: CAtom)(c: CAtom) : List(CAtom) := List.cons(a, c2(b, c))
        |
        |inductive CountedShares indices (consumed: List(CAtom))(produced: List(CAtom)) : Prop
        | | split (k: Nat)(q: Nat)(r: Nat)
        |     : CountedShares(c2(CAtom.out(k), CAtom.share(Nat.add(Nat.succ(q), Nat.succ(r)))),
        |         c3(CAtom.out(Nat.succ(k)), CAtom.share(Nat.succ(q)), CAtom.share(Nat.succ(r))))
        | | join (k: Nat)(q: Nat)(r: Nat)
        |     : CountedShares(c3(CAtom.out(Nat.succ(k)), CAtom.share(q), CAtom.share(r)), c2(CAtom.out(k), CAtom.share(Nat.add(q, r))))
        | | release (k: Nat)(q: Nat) : CountedShares(c2(CAtom.out(Nat.succ(k)), CAtom.share(q)), c1(CAtom.out(k)))
        |
        |def sumBy (f: CAtom -> Nat)(xs: List(CAtom)) : Nat decreases structural(xs) := {
        |  match xs with
        |  | List.nil => 0
        |  | List.cons a rest => Nat.add(f(a), sumBy(f, rest))
        |}
        |
        |def isOut (a: CAtom) : Nat := {
        |  match a with
        |  | CAtom.out k => 1
        |  | CAtom.share q => 0
        |}
        |
        |def outOf (a: CAtom) : Nat := {
        |  match a with
        |  | CAtom.out k => k
        |  | CAtom.share q => 0
        |}
        |
        |def isShare (a: CAtom) : Nat := {
        |  match a with
        |  | CAtom.out k => 0
        |  | CAtom.share q => 1
        |}
        |
        |def permSum (f: CAtom -> Nat)(xs: List(CAtom))(ys: List(CAtom))(p: List.Perm(CAtom, xs, ys))
        |    : Eq(Nat, sumBy(f, xs), sumBy(f, ys)) decreases structural(p) := {
        |  match p returning Eq(Nat, sumBy(f, xs), sumBy(f, ys)) with
        |  | List.Perm.nil => Eq.refl(0)
        |  | List.Perm.cons x xs1 ys1 q => congrArg(permSum(f, xs1, ys1, q), Nat, fun (m: Nat): Nat => Nat.add(f(x), m))
        |  | List.Perm.swap x y zs => Eq.refl(sumBy(f, List.cons(y, List.cons(x, zs))))
        |  | List.Perm.trans as1 bs1 cs1 q r => Eq.trans(permSum(f, as1, bs1, q), permSum(f, bs1, cs1, r))
        |}
        |
        |def pred (h: Eq(Nat, $a, $b)) : Eq(Nat, Nat.pred(a), Nat.pred(b)) := congrArg(h, Nat, fun (m: Nat): Nat => Nat.pred(m))
        |def succ (h: Eq(Nat, $a, $b)) : Eq(Nat, Nat.succ(a), Nat.succ(b)) := congrArg(h, Nat, fun (m: Nat): Nat => Nat.succ(m))
        |
        |// One authority atom, whose count is the number of live shares.
        |def Inv (C: List(CAtom)) : Prop := And(Eq(Nat, sumBy(isOut, C), 1), Eq(Nat, sumBy(outOf, C), sumBy(isShare, C)))
        |
        |def inv (C: List(CAtom))(one: Eq(Nat, sumBy(isOut, C), 1))(count: Eq(Nat, sumBy(outOf, C), sumBy(isShare, C)))
        |    : Inv(C) :=
        |  And.intro(Eq(Nat, sumBy(isOut, C), 1), Eq(Nat, sumBy(outOf, C), sumBy(isShare, C)), one, count)
        |
        |def counted (n: Nat)(C: List(CAtom))(r: Protocol.Reach(Protocol.Proto.mk(CAtom, CountedShares), c2(CAtom.out(1), CAtom.share(n)), C))
        |    : Inv(C) decreases structural(r) := {
        |  match r returning Inv(C) with
        |  | Protocol.Reach.initial => inv(c2(CAtom.out(1), CAtom.share(n)), Eq.refl(1), Eq.refl(1))
        |  | Protocol.Reach.step A B frame h prev => {
        |    let (one, count) := counted(n, List.append(A, frame), prev)
        |    match h returning Inv(List.append(B, frame)) with
        |    | CountedShares.split k q r1 => inv(List.append(B, frame), one, succ(count))
        |    | CountedShares.join k q r1 => inv(List.append(B, frame), one, pred(count))
        |    | CountedShares.release k q => inv(List.append(B, frame), one, pred(count))
        |  }
        |  | Protocol.Reach.perm C1 D1 prev p => {
        |    let (one, count) := counted(n, C1, prev)
        |    inv(D1, Eq.trans(Eq.symm(permSum(isOut, C1, D1, p)), one),
        |      Eq.trans(Eq.symm(permSum(outOf, C1, D1, p)), Eq.trans(count, permSum(isShare, C1, D1, p))))
        |  }
        |}
        |
        |def noOuts (xs: List(CAtom))(h: Eq(Nat, sumBy(isOut, xs), 0))
        |    : Eq(Nat, sumBy(outOf, xs), 0) decreases structural(xs) := {
        |  match xs returning Eq(Nat, sumBy(outOf, xs), 0) with
        |  | List.nil => Eq.refl(0)
        |  | List.cons a rest => {
        |    match a returning Eq(Nat, sumBy(outOf, List.cons(a, rest)), 0) with
        |    | CAtom.out k => {
        |      match h returning Eq(Nat, sumBy(outOf, List.cons(CAtom.out(k), rest)), 0) with
        |    }
        |    | CAtom.share q => noOuts(rest, h)
        |  }
        |}
        |
        |def authority (n: Nat)(q: Nat)(r: Nat)
        |    (v: Protocol.Valid(Protocol.Proto.mk(CAtom, CountedShares), c2(CAtom.out(1), CAtom.share(n)), c3(CAtom.out(1), CAtom.share(q), CAtom.share(r))))
        |    : False := {
        |  match v returning False with
        |  | Protocol.Valid.mk C rest r1 => {
        |    let (one, count) := counted(n, List.append(C, rest), r1)
        |    let none := noOuts(rest, pred(one))
        |    match Eq.trans(Eq.symm(succ(none)), count) returning False with
        |  }
        |}
        |""".stripMargin
    )
  }

  test("no theorem combines separate observations: Valid(C) -> Valid(D) -> Valid(C ++ D) is refuted for Shares") {
    run(
      shares +
        """
          |def noCombination
          |    (combine: (C: List(Nat)) -> (D: List(Nat)) -> (vc: Protocol.Valid(Protocol.Proto.mk(Nat, Shares), l1(1), C))
          |      -> (vd: Protocol.Valid(Protocol.Proto.mk(Nat, Shares), l1(1), D)) -> Protocol.Valid(Protocol.Proto.mk(Nat, Shares), l1(1), List.append(C, D)))
          |    : False := {
          |  let one := Protocol.Valid.mk(Protocol.Proto.mk(Nat, Shares), l1(1), l1(1), l0, Protocol.Reach.initial(Protocol.Proto.mk(Nat, Shares), l1(1)))
          |  match pairBound(1, 1, 1, combine(l1(1), l1(1), one, one)) returning False with
          |  | Le.mk k e => {
          |    match e returning False with
          |  }
          |}
          |""".stripMargin
    )
  }

  test("R1 and R2 are stuck on an unknown supply or list and resume once it is solved; ghosts are unquotable") {
    val env = parse(shares).decls.foldLeft(Interpreter.initialEnv(Prelude.default)) { case (env, decl) =>
      Interpreter.evalDecl(decl, env)
    }
    def apply(name: String, args: Value*): Value = Interpreter.evalApply(env(name), args.toVector)
    val listNat = apply("List", Kernel.natType)
    val two = apply("l1", NatNormalForm.literal(2))
    val proto = apply("Protocol.Proto.mk", Kernel.natType, env("Shares"))
    def solved(variable: Var, value: Value): EqStore =
      EqStore.empty.allow(DepSet.single(variable.id)).addLink(variable.id, value)

    // R1 waits for a canonical supply, and for a known initial list.
    val sup = FreshVar.freshVar("sup", Kernel.supplyType)
    val waiting = apply("Protocol.new", proto, two, sup)
    assertEquals(ReductionBlockers.of(waiting), DepSet.single(sup.id))
    val fresh = Interpreter.resolveInEqStore(waiting, solved(sup, ProtocolPrimitives.rootSupply))
    val protocol = "Protocol.Proto.mk(Nat, Shares)"
    val identity = s"inst#($protocol, [2], 0)"
    assertEquals(
      PrettyPrinter.print(fresh),
      s"Protocol.Fresh.mk(supply#(1), $identity, Protocol.Toks.cons(2, tok#($protocol, [2], $identity, 2), [], " +
        "Protocol.Toks.nil))"
    )
    val init = FreshVar.freshVar("init", listNat)
    val unknownInit = apply("Protocol.new", proto, init, ProtocolPrimitives.rootSupply)
    assertEquals(ReductionBlockers.of(unknownInit), DepSet.single(init.id))

    // R2 waits for a known output list; the input packet is never read.
    val (_, Vector(_, s, packet)) = ConstructorValue.unapply(fresh).get
    val output = FreshVar.freshVar("B", listNat)
    val rule = FreshVar.freshVar("h", apply("Shares", two, output))
    val stepped = apply("Protocol.step", proto, two, s, two, output, rule, packet)
    assertEquals(ReductionBlockers.of(stepped), DepSet.single(output.id))
    val resumed = Interpreter.resolveInEqStore(
      stepped,
      solved(output, apply("l2", NatNormalForm.literal(1), NatNormalForm.literal(1)))
    )
    assertEquals(
      PrettyPrinter.print(resumed),
      s"Protocol.Toks.cons(1, tok#($protocol, [2], $identity, 1), [1], " +
        s"Protocol.Toks.cons(1, tok#($protocol, [2], $identity, 1), [], Protocol.Toks.nil))"
    )

    // Identities of one run are distinct; a valid# converts with every proof of its proposition.
    val (_, Vector(next, _, _)) = ConstructorValue.unapply(fresh).get
    val (_, Vector(_, second, _)) =
      ConstructorValue.unapply(apply("Protocol.new", proto, two, next)).get
    assert(!ValueEquivalence.defEq(s, second))
    val (_, Vector(_, valid)) =
      ConstructorValue.unapply(apply("Protocol.observe", proto, two, s, two, packet)).get
    assert(ValueEquivalence.defEq(valid, FreshVar.freshVar("v", valid.tpe)))

    // No residual names a ghost, whether it is linear or not.
    Vector(s, valid).foreach { ghostValue =>
      val error =
        intercept[CannotQuoteValue](ValueQuote.quoteTerm(ghostValue, ValueQuote.quoteContext(env), Span(0, 0)))
      assert(error.reason.contains("ghost"), error.getMessage)
    }
  }

  test("dropping a token is accepted: use is affine, and forgetting tokens keeps the invariant") {
    // The branch releases the first half and drops `rest`, the other.
    val src =
      releases +
        """
          |fun (sup: Protocol.Supply): Nat => {
          |  let (next, s, toks) := Protocol.new(Protocol.Proto.mk(Nat, Shares), l1(2), sup)
          |  let halves := Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2), l2(1, 1), Shares.split(0, 0), toks)
          |  match halves with
          |  | Protocol.Toks.cons a t C rest =>
          |      done(l1(2), s, releaseOne(l1(2), s, a, Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(2), s, a, t, l0,
          |        Protocol.Toks.nil(Protocol.Proto.mk(Nat, Shares), l1(2), s))), Nat, a)
          |}
          |""".stripMargin
    assertEquals(result(src), "1")
  }

  test("observing one packet twice is LinearReused") {
    assertErrorAt[LinearReused](
      releases + packets +
        """
          |def twice (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Both(Protocol.Observed(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)), Protocol.Observed(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) :=
          |  Both.mk(Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2), toks), Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2), toks))
          |""".stripMargin,
      "toks",
      "toks))"
    )
  }

  test("separately observed facts do not combine into a joint bound") {
    assertErrorAt[TypeMismatch](
      shares +
        """
          |def combine (n: Nat)(q: Nat)(r: Nat)(vq: Protocol.Valid(Protocol.Proto.mk(Nat, Shares), l1(n), l1(q)))
          |    (vr: Protocol.Valid(Protocol.Proto.mk(Nat, Shares), l1(n), l1(r))) : Le(Nat.add(q, r), n) :=
          |  pairBound(n, q, r, vq)
          |""".stripMargin,
      "(n, q, r, vq)"
    )
  }

  // Formerly S1 negatives, now reads (DESIGN.md §6): the codomain reads t in one call (R3, R4), and the proof observes a
  // closed packet (R2, R5), a hypothetical run from no linear input.
  test("a token in a type, and an observation inside a proof, are reads") {
    val size =
      releases +
        """
          |def size (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(a: Nat)(toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(a))) : Nat :=
          |  done(l1(2), s, releaseOne(l1(2), s, a, toks), Nat, 1)
          |
          |""".stripMargin
    run(
      size +
        "def sized (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(a: Nat)(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(a)))" +
        " : Eq(Nat, size(s, a, t), 1) := Eq.refl(1)\n"
    )
    run(
      releases +
        """
          |def seen (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(o: Protocol.Observed(Protocol.Proto.mk(Nat, Shares), l1(2), s, l0)) : Nat := {
          |  let (toks, valid) := o
          |  done(l1(2), s, toks, Nat, 0)
          |}
          |
          |def closed (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2))) : Eq(Nat, 0, 0) :=
          |  Eq.refl(seen(s, Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l0, Protocol.Toks.nil(Protocol.Proto.mk(Nat, Shares), l1(2), s))))
          |""".stripMargin
    )
  }

  /** `observe` inside a proof over held tokens, which must be separate and jointly live. */
  private val observing =
    releases + packets +
      """
        |def observedBound (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(q: Nat)(r: Nat)
        |    (both: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(q, r))) : Le(Nat.add(q, r), 2) := {
        |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(q, r), both) with
        |  | Protocol.Observed.mk seen v => pairBound(2, q, r, v)
        |}
        |
        |""".stripMargin

  test("a proof may observe held tokens without consuming them, and the tokens are used afterwards") {
    run(
      observing +
        """
          |def keep (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(halves: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1))) : Nat := {
          |  let bound : Le(Nat.add(1, 1), 2) := observedBound(s, 1, 1, halves)
          |  let inline : Le(Nat.add(1, 1), 2) := {
          |    match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1), halves) with
          |    | Protocol.Observed.mk seen v => pairBound(2, 1, 1, v)
          |  }
          |  done(l1(2), s, releaseTwo(l1(2), s, 1, 1, halves), Nat, 0)
          |}
          |""".stripMargin
    )
  }

  // The key soundness control: observing one packet joined with itself would prove Valid([2], [2, 2]), so 2 + 2 <= 2.
  test("a proof observing a packet joined with itself is LinearReusedInType") {
    assertErrorAt[LinearReusedInType](
      observing +
        """
          |def bad (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2), joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), t, t)) with
          |  | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |}
          |""".stripMargin,
      "t",
      "t)) with"
    )
  }

  // R7: `whole` aliases `halves`, the region it was stepped from, so the two overlap.
  test("a proof combining a consumed packet with its successor is LinearReusedInType") {
    assertErrorAt[LinearReusedInType](
      observing +
        """
          |def bad (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(halves: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1))) : Nat := {
          |  let whole := Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1), l1(2), Shares.join(1, 1), halves)
          |  let fact : True := {
          |    match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, List.append(l2(1, 1), l1(2)),
          |        joinToks(Nat, Shares, l1(2), s, l2(1, 1), l1(2), halves, whole)) with
          |    | Protocol.Observed.mk seen v => True.intro
          |  }
          |  done(l1(2), s, releaseOne(l1(2), s, 2, whole), Nat, 0)
          |}
          |""".stripMargin,
      "whole",
      "whole)) with"
    )
  }

  test("a supply global, a supply axiom, and an entry with a linear result are rejected before anything runs") {
    // S2 is decided from the declared type, before the body.
    assertErrorAt[LinearGlobal](
      shares + "def root : Protocol.Supply := root\n",
      "Protocol.Supply",
      "Protocol.Supply :="
    )
    withUserAxioms.assertErrorAt[LinearAxiom](
      shares + "axiom root : Protocol.Supply\n",
      "Protocol.Supply",
      "Protocol.Supply\n"
    )
    // Under --no-user-axioms, which protocol theorems assume, any program axiom is rejected first.
    assertErrorAt[UserAxiom](shares + "axiom root : Protocol.Supply\n", "axiom root : Protocol.Supply")
    val entry =
      "fun (sup: Protocol.Supply): Protocol.Fresh(Protocol.Proto.mk(Nat, Shares), l1(2)) => Protocol.new(Protocol.Proto.mk(Nat, Shares), l1(2), sup)"
    assertErrorAt[LinearGlobal](shares + entry + "\n", entry)
  }

  test("a supply used twice is LinearReused, and a last supply may be dropped") {
    assertErrorAt[LinearReused](
      shares + packets +
        """
          |def twice (sup: Protocol.Supply) : Both(Protocol.Fresh(Protocol.Proto.mk(Nat, Shares), l0), Protocol.Fresh(Protocol.Proto.mk(Nat, Shares), l0)) :=
          |  Both.mk(Protocol.new(Protocol.Proto.mk(Nat, Shares), l0, sup), Protocol.new(Protocol.Proto.mk(Nat, Shares), l0, sup))
          |""".stripMargin,
      "sup",
      "sup))"
    )
    assertEquals(
      result(
        shares +
          """
            |fun (sup: Protocol.Supply): Nat => {
            |  let (next, s, toks) := Protocol.new(Protocol.Proto.mk(Nat, Shares), l0, sup)
            |  match toks with
            |  | Protocol.Toks.nil => 0
            |}
            |""".stripMargin
      ),
      "0"
    )
  }

  test("a step with another instance's tokens, or with a rule that does not match its packets, is TypeMismatch") {
    assertErrorAt[TypeMismatch](
      shares +
        """
          |def other (s1: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(s2: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))
          |    (toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s2, l1(2))) : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s1, l2(1, 1)) :=
          |  Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s1, l1(2), l2(1, 1), Shares.split(0, 0), toks)
          |""".stripMargin,
      "(Protocol.Proto.mk(Nat, Shares), l1(2), s1, l1(2), l2(1, 1), Shares.split(0, 0), toks)"
    )
    assertErrorAt[TypeMismatch](
      shares +
        """
          |def wrongRule (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1)) :=
          |  Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2), l2(1, 1), Shares.join(1, 1), toks)
          |""".stripMargin,
      "(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2), l2(1, 1), Shares.join(1, 1), toks)"
    )
  }

  test("an axiom that produces or consumes a token is LinearAxiom, even inside another type") {
    val axioms = Vector(
      "axiom forge (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(a: Nat) : Protocol.Tok(Protocol.Proto.mk(Nat, Shares), l1(2), s, a)\n" ->
        " (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(a: Nat) : Protocol.Tok(Protocol.Proto.mk(Nat, Shares), l1(2), s, a)",
      "axiom burn (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Tok(Protocol.Proto.mk(Nat, Shares), l1(2), s, 2)) : Nat\n" ->
        " (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Tok(Protocol.Proto.mk(Nat, Shares), l1(2), s, 2)) : Nat",
      "inductive Box (A: Type) : Type\n | mk {A: Type} (val: A) : Box(A)\n\n" +
        "axiom mint (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2))) : Box((a: Nat) -> Protocol.Tok(Protocol.Proto.mk(Nat, Shares), l1(2), s, a))\n" ->
        " (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2))) : Box((a: Nat) -> Protocol.Tok(Protocol.Proto.mk(Nat, Shares), l1(2), s, a))"
    )
    axioms.foreach { case (axiom, at) =>
      withUserAxioms.assertErrorAt[LinearAxiom](shares + axiom, at)
    }
    // An identity is unrestricted data, so an axiom of one passes S3, though --no-user-axioms rejects it.
    withUserAxioms.run(shares + "axiom someone : Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2))\n")
  }
}
