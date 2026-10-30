package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.ProgramFixtures.Programs
import com.raccoonlang.Value._

/**
 * Adversarial review of the S1 relaxation (branch `relaxed-separation`): read extents with per-call separation and
 * joint liveness. Each attack tries to forge a false `Valid` or otherwise escape a read extent, or probes a seam of the
 * bottom-up ledger. The canonical target is `Valid(Shares, [2], [2, 2])`, refuted by `pairBound` to get
 * `Le(Nat.add(2, 2), 2)`, an absurd `Le(4, 2)`.
 */
class RelaxedSeparationAttackTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs.{assertErrorAt, runChecked}

  /** Accept: the program checks and runs with no user axioms. */
  private def accepts(src: String): Unit =
    try { runChecked(src); () }
    catch { case t: TypeError => fail("REJECTED (should accept): " + ErrorReporter.pretty(t, Source(src))) }

  /** The program is rejected by some TypeError; returns it. A pass means no break here. */
  private def rejects(src: String): TypeError =
    try {
      runChecked(src)
      fail("ACCEPTED (BREAK: should be rejected)")
    } catch { case t: TypeError => t }

  private def rejectsWith[T <: TypeError](src: String)(implicit ct: reflect.ClassTag[T]): T = {
    val t = rejects(src)
    t match {
      case ct(e) => e
      case other =>
        fail(s"rejected by ${other.getClass.getSimpleName} (${other.getMessage}), not ${ct.runtimeClass.getSimpleName}")
    }
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Shared prelude: the inline `Shares` of ProtocolPrimitivesTests, with pairBound/heldCoverage, plus packet ops.
  // ------------------------------------------------------------------------------------------------------------------

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
      |def eqFalse (h: Eq(Nat, 2, 0)) : False := {
      |  match h returning False with
      |}
      |
      |""".stripMargin

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

  private val packets = ProgramFixtures.packets

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

  // ------------------------------------------------------------------------------------------------------------------
  // Controls: the documented soundness barriers must hold.
  // ------------------------------------------------------------------------------------------------------------------

  test("CONTROL: observe(join(t, t)) in a proof is LinearReusedInType") {
    rejectsWith[LinearReusedInType](
      observing +
        """
          |def bad (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2), joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), t, t)) with
          |  | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |}
          |""".stripMargin
    )
  }

  // `whole` aliases the region of `halves` it was stepped from, so the two overlap.
  test("CONTROL: a consumed packet combined with its successor is LinearReusedInType") {
    rejectsWith[LinearReusedInType](
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
          |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Attacks: forging Valid([2],[2,2]) through various laundering paths. Each must be rejected.
  // ------------------------------------------------------------------------------------------------------------------

  test("ATTACK let-launder: `let u := t; join(u, t)` to forge [2,2]") {
    // Binding u from t marks t dead; so {u, t} are not jointly live at the join.
    rejects(
      observing +
        """
          |def forge (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  let u := t
          |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2), joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), u, t)) with
          |  | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |}
          |""".stripMargin
    )
  }

  test("ATTACK copyable-linear id applied twice to one token") {
    // Sort <= Lin cumulativity makes `lid` take Nat and tokens alike; each lid(t) still has provenance {t}.
    rejects(
      observing +
        """
          |def lid (A: Lin($u))(x: $A in Lin($u)) : A := x
          |
          |def forge (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  let dup := joinToks(Nat, Shares, l1(2), s, l1(2), l1(2),
          |    lid(Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)), t),
          |    lid(Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)), t))
          |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2), dup) with
          |  | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |}
          |""".stripMargin
    )
  }

  test("ATTACK match-field recombine: split a token off and join it back with the packet") {
    // Matching the packet gives field `t` of the scrutinee; joining t with the rebuilt remainder duplicates.
    rejects(
      observing +
        """
          |def forge (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(p: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  match p with
          |  | Protocol.Toks.cons a t C rest => {
          |    let packet := Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(2), s, a, t, C, rest)
          |    match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2),
          |        joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), packet,
          |          Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(2), s, a, t, C, rest))) with
          |    | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |  }
          |}
          |""".stripMargin
    )
  }

  test("ATTACK g(xs, lemma(xs)): observe one packet then step the same packet in one call") {
    // Both inputs of the constructor are the packet t; separation must flag it even though lemma(t) is a proof.
    rejects(
      observing +
        """
          |def forge (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2),
          |      joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), t, lidTok(s, t))) with
          |  | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |}
          |
          |def lidTok (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)) := t
          |""".stripMargin
    )
  }

  // ================================================================================================================
  // BREAK. `let a := t; let b := t` gives a and b the provenances {a} and {b}, not {t}. Separation at join(a, b) sees
  // disjoint provenances, and joint liveness passes because binding a marks t dead (not a), so a never enters b's
  // deadBefore. The single token t is duplicated inside a read extent, forging Valid([2], [2, 2]).
  // Root cause: TypeChecker.checkTypeTerm Ref case (a tracked local is its own provenance root) together with
  // checkBody, which only substitutes let provenance into the BLOCK RESULT, never into internal references, and never
  // links a let's liveness to the locals its value consumed.
  // ================================================================================================================
  private val forge =
    observing +
      """
        |def forgeValid (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
        |    : Protocol.Valid(Protocol.Proto.mk(Nat, Shares), l1(2), l2(2, 2)) := {
        |  let a := t
        |  let b := t
        |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2), joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), a, b)) with
        |  | Protocol.Observed.mk seen v => v
        |}
        |
        |""".stripMargin

  // Fixed: a let aliases its value's provenance, so `a` and `b` are both the region of `t`.
  test("BREAK minimal: `let a := t; let b := t` cannot forge Valid([2],[2,2]): LinearReusedInType") {
    assertErrorAt[LinearReusedInType](
      forge +
        """
          |def twoIsZero (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Eq(Nat, 2, 0) := heldCoverage(2, 2, forgeValid(s, t))
          |""".stripMargin,
      "b",
      "b)) with"
    )
  }

  // The same break driven to a concrete, runnable program on a real token obtained from the root supply. No user
  // axioms, no hypotheses: the entry allocates one legitimate [2] share, derives False from it, releases the token to
  // satisfy the ledger, and returns a Nat via False.elim.
  test("BREAK end-to-end: an entry cannot derive False from one real token: LinearReusedInType") {
    assertErrorAt[LinearReusedInType](
      forge +
        """
          |def boom (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) : False :=
          |  eqFalse(heldCoverage(2, 2, forgeValid(s, t)))
          |
          |fun (sup: Protocol.Supply): Nat => {
          |  let (next, s, toks) := Protocol.new(Protocol.Proto.mk(Nat, Shares), l1(2), sup)
          |  let contradiction : False := boom(s, toks)
          |  done(l1(2), s, releaseOne(l1(2), s, 2, toks), Nat, False.elim(contradiction, Nat))
          |}
          |""".stripMargin,
      "b",
      "b)) with"
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Provenance by region: lets alias, fields are sub-regions of an exact scrutinee.
  // ------------------------------------------------------------------------------------------------------------------

  private val regions =
    observing +
      """
        |def single (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(a: Nat)(tok: Protocol.Tok(Protocol.Proto.mk(Nat, Shares), l1(2), s, a))
        |    : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(a)) :=
        |  Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(2), s, a, tok, l0, Protocol.Toks.nil(Protocol.Proto.mk(Nat, Shares), l1(2), s))
        |
        |""".stripMargin

  test("REGIONS: the same field taken by two matches of one packet overlaps") {
    assertErrorAt[LinearReusedInType](
      regions +
        """
          |def bad (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  match t with
          |  | Protocol.Toks.cons a tok C rest => {
          |    match t with
          |    | Protocol.Toks.cons a2 tok2 C2 rest2 => {
          |      match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2),
          |          joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), single(s, a, tok), single(s, a2, tok2))) with
          |      | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |    }
          |  }
          |}
          |""".stripMargin,
      "single(s, a2, tok2)"
    )
  }

  test("REGIONS: a let alias of a field joined with its scrutinee overlaps") {
    assertErrorAt[LinearReusedInType](
      regions +
        """
          |def bad (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  match t with
          |  | Protocol.Toks.cons a tok C rest => {
          |    let k := tok
          |    match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2),
          |        joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), single(s, a, k), t)) with
          |    | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |  }
          |}
          |""".stripMargin,
      "t",
      "t)) with"
    )
  }

  test("REGIONS: an alias through a let chain overlaps its source") {
    assertErrorAt[LinearReusedInType](
      regions +
        """
          |def bad (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  let a := t
          |  let c := a
          |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2), joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), c, t)) with
          |  | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |}
          |""".stripMargin,
      "t",
      "t)) with"
    )
  }

  test("REGIONS: sibling fields of one match recombine, and a fresh let joins a held packet") {
    accepts(
      regions +
        """
          |def whole (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) : True := {
          |  match t with
          |  | Protocol.Toks.cons a tok C rest => {
          |    match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, List.append(l1(a), C),
          |        joinToks(Nat, Shares, l1(2), s, l1(a), C, single(s, a, tok), rest)) with
          |    | Protocol.Observed.mk seen v => True.intro
          |  }
          |}
          |
          |def fresh (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) : True := {
          |  let e := Protocol.Toks.nil(Protocol.Proto.mk(Nat, Shares), l1(2), s)
          |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2), joinToks(Nat, Shares, l1(2), s, l0, l1(2), e, t)) with
          |  | Protocol.Observed.mk seen v => True.intro
          |}
          |""".stripMargin
    )
  }

  // A type formed after a root is consumed: its binder was never live with that root.
  test("JOINT LIVENESS: a Pi binder bound after a packet is consumed cannot be read with it") {
    val seen =
      regions +
        """
          |def Seen (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(C: List(Nat))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, C)) : Prop :=
          |  True
          |
          |def bad (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) : Nat := {
          |  FIRST
          |  SECOND
          |  done(l1(2), s, gone, Nat, 0)
          |}
          |""".stripMargin
    val consume = "let gone := releaseOne(l1(2), s, 2, t)"
    val form =
      "let T : Prop := (u: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) ->" +
        " Seen(s, l2(2, 2), joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), u, t))"
    assertErrorAt[LinearNotJointlyLive](
      seen.replace("FIRST", consume).replace("SECOND", form),
      "joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), u, t)"
    )
    accepts(seen.replace("FIRST", form).replace("SECOND", consume))
  }

  test("ATTACK pair-field duplication: pack one token into a pair and read both components") {
    rejects(
      observing +
        """
          |def forge (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  let pair := Both.mk(Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)),
          |    Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)), t, t)
          |  let (x, y) := pair
          |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2), joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), x, y)) with
          |  | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |}
          |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Measure / termination seam.
  // ------------------------------------------------------------------------------------------------------------------

  test("ATTACK measure term duplicating a linear local") {
    // A `measure` is a read extent; join(xs, xs) inside it must be flagged.
    rejects(
      observing +
        """
          |def drain (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(n: Nat)(xs: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Nat decreases measure(total2(s, joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), xs, xs))) := {
          |  done(l1(2), s, releaseOne(l1(2), s, 2, xs), Nat, 0)
          |}
          |
          |def total2 (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2))) : Nat := {
          |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2), t) with
          |  | Protocol.Observed.mk seen v => 4
          |}
          |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // F5 and lambda captures.
  // ------------------------------------------------------------------------------------------------------------------

  test("ATTACK F5: a lambda inside a proof capturing a token") {
    // A lambda cannot capture a linear local, in a proof or not (F5).
    rejectsWith[LinearCapture](
      observing +
        """
          |def forge (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  let f : (u: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) -> Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2)) :=
          |    fun (u: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))): Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2)) =>
          |      joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), u, t)
          |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2), f(t)) with
          |  | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |}
          |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Positive cases (must be accepted): the relaxation's whole point. Rejecting these is an over-rejection.
  // ------------------------------------------------------------------------------------------------------------------

  test("POSITIVE: a proof observing held tokens, with the tokens still used afterwards (R2)") {
    accepts(
      observing +
        """
          |def keep (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(halves: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1))) : Nat := {
          |  let bound : Le(Nat.add(1, 1), 2) := observedBound(s, 1, 1, halves)
          |  done(l1(2), s, releaseTwo(l1(2), s, 1, 1, halves), Nat, 0)
          |}
          |""".stripMargin
    )
  }

  test("POSITIVE: Eq(Nat, count, count) reading one token twice (R1)") {
    accepts(
      releases +
        """
          |def size (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(a: Nat)(toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(a))) : Nat :=
          |  done(l1(2), s, releaseOne(l1(2), s, a, toks), Nat, 1)
          |
          |def sized (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(a: Nat)(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(a)))
          |    : Eq(Nat, Nat.add(size(s, a, t), size(s, a, t)), 2) := Eq.refl(2)
          |""".stripMargin
    )
  }

  test("POSITIVE: a full entry creates, splits, observes, joins and releases") {
    val entry =
      shares +
        """
          |fun (sup: Protocol.Supply): Nat => {
          |  let (next, s, toks) := Protocol.new(Protocol.Proto.mk(Nat, Shares), l1(2), sup)
          |  let halves := Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2), l2(1, 1), Shares.split(0, 0), toks)
          |  let (seen, valid) := Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1), halves)
          |  let bound : Le(Nat.add(1, 1), 2) := pairBound(2, 1, 1, valid)
          |  let whole := Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1), l1(2), Shares.join(1, 1), seen)
          |  match whole with
          |  | Protocol.Toks.cons a t C rest => {
          |    let gone := Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(a), l0, Shares.release(a),
          |      Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(2), s, a, t, C, rest))
          |    match gone with
          |    | Protocol.Toks.nil => a
          |  }
          |}
          |""".stripMargin
    accepts(entry)
  }
}
