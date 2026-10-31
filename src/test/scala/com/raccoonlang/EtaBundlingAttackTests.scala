package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.ProgramFixtures.Programs

/**
 * Adversarial review of structure eta (1dfe1412), declaration-time positivity of stuck computations (d6ad4846) and
 * bundled protocol families with the record size rule (0eec1a6e). A test that ACCEPTS a program it labels a break is a
 * break; OVER-REJECTION labels a sound program the kernel refuses.
 */
class EtaBundlingAttackTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs.runChecked

  private def describe(t: Throwable, src: String): String =
    t match {
      case te: TypeError => s"${te.getClass.getSimpleName}: " + ErrorReporter.pretty(te, Source(src)).take(600)
      case other =>
        val msg = String.valueOf(other.getMessage)
        val at = msg.indexOf("Failed to parse")
        s"${other.getClass.getSimpleName}: ${(if (at >= 0) msg.substring(at) else msg).take(300).replace('\n', ' ')}"
    }

  /** Accept: the program checks and runs with no user axioms. */
  private def accepts(src: String): Unit =
    try { runChecked(src); () }
    catch { case t: TypeError => fail("REJECTED (should accept): " + describe(t, src)) }

  /** The program is rejected by some TypeError; a pass means no break here. An ACCEPT is a break. */
  private def rejects(src: String): TypeError =
    try {
      runChecked(src)
      fail("ACCEPTED (BREAK: should be rejected)")
    } catch {
      case t: TypeError => t
    }

  // ------------------------------------------------------------------------------------------------------------------
  // Shares and its refutation (from the relaxed-separation attack suites), bundled.
  // ------------------------------------------------------------------------------------------------------------------

  private val shares =
    """
      |def l0 : List(Nat) := List.nil(Nat)
      |
      |def l1 (a: Nat) : List(Nat) := List.cons(a, List.nil(Nat))
      |
      |def l2 (a: Nat)(b: Nat) : List(Nat) := List.cons(a, List.cons(b, List.nil(Nat)))
      |
      |inductive Shares indices (consumed: List(Nat))(produced: List(Nat)) : Prop
      | | split (q: Nat)(r: Nat) : Shares(l1(Nat.add(Nat.succ(q), Nat.succ(r))), l2(Nat.succ(q), Nat.succ(r)))
      | | join (q: Nat)(r: Nat) : Shares(l2(q, r), l1(Nat.add(q, r)))
      | | release (q: Nat) : Shares(l1(q), l0)
      |
      |def SP : Protocol.Proto := Protocol.Proto.mk(Nat, Shares)
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
      |def refute (v: Protocol.Valid(Protocol.Proto.mk(Nat, Shares), l1(2), l2(2, 2))) : False := eqFalse(heldCoverage(2, 2, v))
      |
      |""".stripMargin

  private val packets = ProgramFixtures.packets

  private val base = shares + packets

  private def rejectsWith[T <: TypeError](src: String)(implicit ct: reflect.ClassTag[T]): T =
    rejects(src) match {
      case ct(e) => e
      case other => fail(s"rejected by ${describe(other, src).take(300)}, not ${ct.runtimeClass.getSimpleName}")
    }

  private val pick =
    """
      |def Pick (b: Bool) : Sort(Level.one) := {
      |  match b returning Sort(Level.one) with
      |  | Bool.true => (x: Type) -> Type
      |  | Bool.false => Type
      |}
      |
      |""".stripMargin

  private val stuckPair =
    """
      |def g (b: Bool) : Prod(Nat, Nat) := {
      |  match b with
      |  | Bool.true => Prod.mk(Nat, Nat, 0, 1)
      |  | Bool.false => Prod.mk(Nat, Nat, 1, 0)
      |}
      |
      |""".stripMargin

  private val anyRel =
    """
      |inductive Any indices (consumed: List(Nat))(produced: List(Nat)) : Prop
      | | mk (xs: List(Nat))(ys: List(Nat)) : Any(xs, ys)
      |
      |""".stripMargin

  // ==================================================================================================================
  // Sanity: the refutation is live, so a forged Valid really is False.
  // ==================================================================================================================

  test("sanity: the Shares refutation and the packet fixtures check") {
    accepts(base + "def done : Nat := 0\n")
  }

  // ==================================================================================================================
  // 1. The size rule, charging a record by its fields.
  // ==================================================================================================================

  test("size: a record holding Type -> Type does not index a Type family") {
    rejectsWith[FamilyArgumentTooLarge](
      """
        |inductive RF : Sort(Level.one)
        | | mk (F: (x: Type) -> Type) : RF
        |
        |inductive I (r: RF) : Type
        |""".stripMargin
    )
  }

  test("size: a record holding Type -> Prop does not index a Type family") {
    rejectsWith[FamilyArgumentTooLarge](
      """
        |inductive RP : Sort(Level.one)
        | | mk (F: (x: Type) -> Prop) : RP
        |
        |inductive I (r: RP) : Type
        |""".stripMargin
    )
  }

  test("size: a record holding a record holding Sort(1) costs level 1") {
    val decls =
      """
        |inductive R1 : Sort(Level.succ(Level.one))
        | | mk (A: Sort(Level.one)) : R1
        |
        |inductive R2 : Sort(Level.succ(Level.one))
        | | mk (r: R1) : R2
        |
        |""".stripMargin
    rejectsWith[FamilyArgumentTooLarge](decls + "inductive I (r: R2) : Type\n")
    accepts(decls + "inductive I (r: R2) : Sort(Level.one)\n")
  }

  test("size: Prod and Sigma hiding a large component are charged it") {
    rejectsWith[FamilyArgumentTooLarge]("inductive I (p: Prod((x: Type) -> Type, Nat)) : Type\n")
    // A dependent second component that is Type -> Type at one first component: the stuck field type costs its
    // classifier, Sort(1).
    rejectsWith[FamilyArgumentTooLarge](pick + "inductive I (s: Sigma(Bool, Level.one, Pick)) : Type\n")
    rejectsWith[FamilyArgumentTooLarge](
      "def Fam (A: Type) : Sort(Level.one) := (f: (x: A) -> Type) -> Type\n\n" +
        "inductive I (s: Sigma(Type, Level.one, Fam)) : Type\n"
    )
  }

  test("size: a record of Sort(u) at a level parameter costs u") {
    rejectsWith[FamilyArgumentTooLarge](
      """
        |inductive RU (u: Level) : Sort(Level.succ(u))
        | | mk {u: Level} (A: Sort(u)) : RU(u)
        |
        |inductive I (v: Level)(r: RU(v)) : Type
        |""".stripMargin
    )
  }

  test("size: a record cannot bundle a Level with a Sort of it") {
    rejectsWith[InductiveUniverseTooSmall](
      """
        |inductive RL : Sort(Level.one)
        | | mk (u: Level)(A: Sort(u)) : RL
        |""".stripMargin
    )
  }

  test("size, sound controls: small records cost level 0, as their components would") {
    accepts("inductive I (p: Prod(Type, Type)) : Type\n")
    accepts("inductive I (p: Prod(Protocol.Proto, Nat)) : Type\n")
    accepts(
      "def Fam (A: Type) : Sort(Level.one) := (x: A) -> Type\n\ninductive I (s: Sigma(Type, Level.one, Fam)) : Type\n"
    )
    accepts("inductive RPP : Type\n | mk (F: (x: Prop) -> Prop) : RPP\n\ninductive I (r: RPP) : Type\n")
    accepts(
      """
        |inductive RA : Sort(Level.one)
        | | mk (P: Protocol.Proto)(x: (a: P.Atom) -> Type) : RA
        |
        |inductive I (r: RA) : Type
        |""".stripMargin
    )
  }

  // ==================================================================================================================
  // 2. Positivity of stuck computations.
  // ==================================================================================================================

  test("positivity: a stuck call that takes the family as an argument is refused") {
    rejectsWith[NonStrictlyPositive](
      """
        |def Pick (b: Bool)(T: Type) : Type := {
        |  match b returning Type with
        |  | Bool.true => (x: T) -> Nat
        |  | Bool.false => T
        |}
        |
        |inductive Bad : Type
        | | mk (b: Bool)(f: Pick(b, Bad)) : Bad
        |""".stripMargin
    )
  }

  test("positivity: a stuck call over a capture of a recursive field's type is refused") {
    rejectsWith[NonStrictlyPositive](
      """
        |def PickC (b: Bool)(x: $T in Sort(Level.zero)) : Type := {
        |  match b returning Type with
        |  | Bool.true => (y: T) -> Nat
        |  | Bool.false => Nat
        |}
        |
        |inductive Bad : Type
        | | mk (b: Bool)(x: Bad)(f: PickC(b, x)) : Bad
        |""".stripMargin
    )
  }

  test("positivity: a stuck call whose argument is a function type out of the family is refused") {
    rejectsWith[NonStrictlyPositive](
      """
        |def App2 (b: Bool)(T: Type) : Type := {
        |  match b returning Type with
        |  | Bool.true => T
        |  | Bool.false => Nat
        |}
        |
        |inductive Bad : Type
        | | mk (b: Bool)(x: App2(b, (y: Bad) -> Nat)) : Bad
        |""".stripMargin
    )
  }

  test("positivity: nesting in a parameter that sits under a stuck computation is refused") {
    rejectsWith[NonStrictlyPositive](
      """
        |def Neg (b: Bool)(A: Type) : Type := {
        |  match b returning Type with
        |  | Bool.true => (x: A) -> Nat
        |  | Bool.false => A
        |}
        |
        |inductive Wrap (b: Bool)(A: Type) : Type
        | | mk {b: Bool}{A: Type} (f: Neg(b, A)) : Wrap(b, A)
        |
        |inductive Bad : Type
        | | mk (w: Wrap(Bool.true, Bad)) : Bad
        |""".stripMargin
    )
  }

  test("positivity: the family cannot reach a record parameter's function field, by level") {
    // r.F(Bad(r)) is refused before positivity: RF holds a Type -> Type, so Bad must live in Sort(1), and then
    // Bad(r) is no argument of F.
    rejects(
      """
        |inductive RF : Sort(Level.one)
        | | mk (F: (x: Type) -> Type) : RF
        |
        |inductive Bad (r: RF) : Type
        | | mk {r: RF} (x: (r.F(Bad(r)))) : Bad(r)
        |""".stripMargin
    )
    rejects(
      """
        |inductive RF : Sort(Level.one)
        | | mk (F: (x: Type) -> Type) : RF
        |
        |inductive Bad (r: RF) : Sort(Level.one)
        | | mk {r: RF} (x: (r.F(Bad(r)))) : Bad(r)
        |""".stripMargin
    )
  }

  test("positivity, sound control: a recursive family over a parameter's projection") {
    accepts(
      """
        |inductive Tree (P: Protocol.Proto) : Type
        | | leaf {P: Protocol.Proto} (a: List(P.Atom)) : Tree(P)
        | | node {P: Protocol.Proto} (l: Tree(P))(r: Tree(P)) : Tree(P)
        |""".stripMargin
    )
  }

  // ==================================================================================================================
  // 3. Eta at linear kinds, selectors of Fresh and Observed, S1 reads.
  // ==================================================================================================================

  test("linear: fresh.next twice, and fresh.next with fresh.toks, are LinearReused") {
    rejectsWith[LinearReused](
      shares + "def bad (f: Protocol.Fresh(SP, l1(2))) : Protocol.Supply := {\n  let a := f.next\n  f.next\n}\n"
    )
    rejectsWith[LinearReused](
      base +
        """
          |def bad (f: Protocol.Fresh(SP, l1(2))) : Both(Protocol.Supply, Protocol.Toks(SP, l1(2), f.s, l1(2))) :=
          |  Both.mk(f.next, f.toks)
          |""".stripMargin
    )
    rejectsWith[LinearReused](
      shares + "def run (sup: Protocol.Supply) : Nat := {\n  let f := Protocol.new(SP, l1(2), sup)\n  let t := f.toks\n  let n := f.next\n  0\n}\n\nrun\n"
    )
  }

  test("linear: a destructured record is consumed") {
    rejectsWith[LinearReused](
      base +
        """
          |def bad (s: Protocol.Inst(SP, l1(2)))(p: Both(Protocol.Toks(SP, l1(2), s, l1(2)), Protocol.Toks(SP, l1(2), s, l1(2))))
          |    : Protocol.Toks(SP, l1(2), s, l1(2)) := {
          |  let (a, b) := p
          |  p.fst
          |}
          |""".stripMargin
    )
  }

  test("linear: in a proof, two allocations from one supply cannot be joined") {
    rejectsWith[LinearReusedInType](
      base +
        """
          |def bad (sup: Protocol.Supply) : False := {
          |  let v : Protocol.Valid(SP, l1(2), l2(2, 2)) :=
          |    Protocol.observe(SP, l1(2), Protocol.new(SP, l1(2), sup).s, l2(2, 2),
          |      joinToks(Nat, Shares, l1(2), Protocol.new(SP, l1(2), sup).s, l1(2), l1(2),
          |        Protocol.new(SP, l1(2), sup).toks, Protocol.new(SP, l1(2), sup).toks)).valid
          |  refute(v)
          |}
          |""".stripMargin
    )
    // Destructured, the two identities are separate fresh locals, so the packets do not even have one type.
    rejects(
      base +
        """
          |def bad (sup: Protocol.Supply) : False := {
          |  let v : Protocol.Valid(SP, l1(2), l2(2, 2)) := {
          |    let (n1, s1, t1) := Protocol.new(SP, l1(2), sup)
          |    let (n2, s2, t2) := Protocol.new(SP, l1(2), sup)
          |    Protocol.observe(SP, l1(2), s1, l2(2, 2), joinToks(Nat, Shares, l1(2), s1, l1(2), l1(2), t1, t2)).valid
          |  }
          |  refute(v)
          |}
          |""".stripMargin
    )
    rejects(
      base +
        """
          |def bad (sup: Protocol.Supply) : False := {
          |  let v : Protocol.Valid(SP, l1(2), l2(2, 2)) := {
          |    match Protocol.new(SP, l1(2), sup) returning Protocol.Valid(SP, l1(2), l2(2, 2)) with
          |    | Protocol.Fresh.mk n s t =>
          |        Protocol.observe(SP, l1(2), s, l2(2, 2), joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), t, Protocol.new(SP, l1(2), sup).toks)).valid
          |  }
          |  refute(v)
          |}
          |""".stripMargin
    )
  }

  test("linear: in a proof, a packet joined with an eta rebuild of its own record is refused") {
    rejectsWith[LinearReusedInType](
      base +
        """
          |def bad (s: Protocol.Inst(SP, l1(2)))(o: Protocol.Observed(SP, l1(2), s, l1(2))) : False := {
          |  let v : Protocol.Valid(SP, l1(2), l2(2, 2)) :=
          |    Protocol.observe(SP, l1(2), s, l2(2, 2), joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), o.toks, Protocol.Observed.mk(SP, l1(2), s, l1(2), o.toks, o.valid).toks)).valid
          |  refute(v)
          |}
          |""".stripMargin
    )
    rejectsWith[LinearReusedInType](
      base +
        """
          |def bad (s: Protocol.Inst(SP, l1(2)))(o: Protocol.Observed(SP, l1(2), s, l1(2))) : False := {
          |  let v : Protocol.Valid(SP, l1(2), l2(2, 2)) := {
          |    match o returning Protocol.Valid(SP, l1(2), l2(2, 2)) with
          |    | Protocol.Observed.mk t w =>
          |        Protocol.observe(SP, l1(2), s, l2(2, 2), joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), t, o.toks)).valid
          |  }
          |  refute(v)
          |}
          |""".stripMargin
    )
    rejectsWith[LinearReusedInType](
      base +
        """
          |def bad (s: Protocol.Inst(SP, l1(2)))(t: Protocol.Toks(SP, l1(2), s, l1(2))) : False := {
          |  let v : Protocol.Valid(SP, l1(2), l2(2, 2)) := {
          |    match Both.mk(t, t) returning Protocol.Valid(SP, l1(2), l2(2, 2)) with
          |    | Both.mk a b => Protocol.observe(SP, l1(2), s, l2(2, 2), joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), a, b)).valid
          |  }
          |  refute(v)
          |}
          |""".stripMargin
    )
  }

  test("linear, sound controls: obs.valid then obs.toks; a proof over a destructured pair; an entry run") {
    accepts(
      base +
        """
          |def ok (s: Protocol.Inst(SP, l1(2)))(o: Protocol.Observed(SP, l1(2), s, l1(2))) : Protocol.Toks(SP, l1(2), s, l1(2)) := {
          |  let v : Protocol.Valid(SP, l1(2), l1(2)) := o.valid
          |  o.toks
          |}
          |""".stripMargin
    )
    accepts(
      base +
        """
          |def ok (s: Protocol.Inst(SP, l1(4)))(p: Both(Protocol.Toks(SP, l1(4), s, l1(2)), Protocol.Toks(SP, l1(4), s, l1(2))))
          |    : Protocol.Valid(SP, l1(4), l2(2, 2)) := {
          |  match p returning Protocol.Valid(SP, l1(4), l2(2, 2)) with
          |  | Both.mk a b => Protocol.observe(SP, l1(4), s, l2(2, 2), joinToks(Nat, Shares, l1(4), s, l1(2), l1(2), a, b)).valid
          |}
          |""".stripMargin
    )
    accepts(
      shares +
        """
          |def run (sup: Protocol.Supply) : Nat := {
          |  let (next, s, toks) := Protocol.new(SP, l1(4), sup)
          |  let split := Protocol.step(SP, l1(4), s, l1(4), l2(2, 2), Shares.split(1, 1), toks)
          |  match Protocol.observe(SP, l1(4), s, l2(2, 2), split) with
          |  | Protocol.Observed.mk seen v => 0
          |}
          |
          |run
          |""".stripMargin
    )
  }

  // Once documented as conservative, when a selector application was a call whose result covered its whole record: a
  // projection reads its field's region (docs/kernel.md, S1), as destructuring the same record (above) does, so two
  // sibling fields are separate. The same field twice still overlaps.
  test("linear: observe(join(p.fst, p.snd)) in a proof reads separate fields; join(p.fst, p.fst) overlaps") {
    accepts(
      base +
        """
          |def ok (s: Protocol.Inst(SP, l1(4)))(p: Both(Protocol.Toks(SP, l1(4), s, l1(2)), Protocol.Toks(SP, l1(4), s, l1(2))))
          |    : Protocol.Valid(SP, l1(4), l2(2, 2)) :=
          |  Protocol.observe(SP, l1(4), s, l2(2, 2), joinToks(Nat, Shares, l1(4), s, l1(2), l1(2), p.fst, p.snd)).valid
          |""".stripMargin
    )
    rejectsWith[LinearReusedInType](
      base +
        """
          |def bad (s: Protocol.Inst(SP, l1(4)))(p: Both(Protocol.Toks(SP, l1(4), s, l1(2)), Protocol.Toks(SP, l1(4), s, l1(2))))
          |    : Protocol.Valid(SP, l1(4), l2(2, 2)) :=
          |  Protocol.observe(SP, l1(4), s, l2(2, 2), joinToks(Nat, Shares, l1(4), s, l1(2), l1(2), p.fst, p.fst)).valid
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // 4. Unification, coverage and termination through eta.
  // ==================================================================================================================

  test("coverage: a branch whose record index is eta-reachable stays required") {
    val fam =
      """
        |inductive T indices (p: Prod(Nat, Nat)) : Type
        | | a : T(Prod.mk(Nat, Nat, 0, 0))
        | | b (n: Nat) : T(Prod.mk(Nat, Nat, Nat.succ(n), 0))
        |
        |""".stripMargin
    accepts(fam + "def f (p: Prod(Nat, Nat))(t: T(p)) : Nat := {\n  match t with\n  | T.a => 0\n  | T.b n => n\n}\n")
    rejectsWith[MissingCase](fam + "def f (p: Prod(Nat, Nat))(t: T(p)) : Nat := {\n  match t with\n  | T.a => 0\n}\n")
    // An equation between a constructor and a neutral record is no contradiction.
    rejectsWith[MissingCase](
      "def f (p: Prod(Nat, Nat))(e: Eq(Prod(Nat, Nat), Prod.mk(Nat, Nat, 0, 0), p)) : False := {\n  match e returning False with\n}\n"
    )
  }

  test("conversion: distinct zero-field records stay apart; unit eta holds") {
    rejectsWith[TypeMismatch]("inductive U2 : Type\n | mk : U2\n\ndef g (x: U2) : Unit := x\n")
    accepts("def f (u: Unit) : Eq(Unit, u, Unit.unit) := Eq.refl(u)\n")
  }

  test("termination: eta does not make a record smaller than itself") {
    rejectsWith[NonDecreasingRecursiveCall](
      "inductive Box (A: Type) : Type\n | mk {A: Type} (val: A) : Box(A)\n\n" +
        "def loop (p: Box(Nat)) : False decreases structural(p) := loop(Box.mk(Nat, p.val))\n"
    )
    rejectsWith[NonDecreasingRecursiveCall]("def loop (u: Unit) : False decreases structural(u) := loop(Unit.unit)\n")
    rejectsWith[NonDecreasingRecursiveCall](
      "def loop (p: Prod(Unit, Unit)) : False decreases structural(p) := loop(Prod.mk(Unit, Unit, p.fst, p.snd))\n"
    )
    rejectsWith[NonDecreasingRecursiveCall](
      "def m (n: Nat) : Prod(Nat, Nat) := Prod.mk(Nat, Nat, n, n)\n\ndef loop (n: Nat) : False decreases measure(m(n)) := loop(n)\n"
    )
  }

  // ==================================================================================================================
  // 5. Selectors on indexed families, and neutral application.
  // ==================================================================================================================

  test("indexed selectors: a field type that names a global like the index is caught by the selector's body") {
    rejectsWith[TypeMismatch](
      """
        |def n : Nat := 0
        |
        |inductive T indices (n: Nat) : Type
        | | mk (h: Eq(Nat, n, 0)) : T(5)
        |
        |def bad (t: T(5)) : Eq(Nat, 5, 0) := t.h
        |
        |def boom (t: T(5)) : False := {
        |  match bad(t) returning False with
        |}
        |""".stripMargin
    )
  }

  test("indexed selectors, sound controls") {
    accepts(
      "inductive V indices (k: Nat) : Type\n | mk (m: Nat)(e: Eq(Nat, m, m)) : V(Nat.succ(m))\n\n" +
        "def get (k: Nat)(v: V(k)) : Nat := v.m\n\ndef empty (v: V(0)) : Nat := v.m\n"
    )
    accepts(
      "def A : Type := Nat\n\ninductive R (A: Type) : Type\n | mk {A: Type} (x: A) : R(A)\n\ndef get (r: R(Bool)) : Bool := r.x\n"
    )
  }

  test("neutral application: distinct arguments stay apart, and it resumes under refinement") {
    rejectsWith[TypeMismatch](
      "inductive RF : Sort(Level.one)\n | mk (F: (x: Nat) -> Type) : RF\n\n" +
        "def cast (r: RF)(x: (r.F(0))) : (r.F(1)) := x\n"
    )
    val pickFn =
      """
        |def pick (b: Bool) : (x: Nat) -> Nat := {
        |  match b returning (x: Nat) -> Nat with
        |  | Bool.true => fun (x: Nat): Nat => x
        |  | Bool.false => fun (x: Nat): Nat => 0
        |}
        |
        |""".stripMargin
    rejectsWith[TypeMismatch](pickFn + "def bad (b: Bool)(e: (Eq(Nat, pick(b)(1), 0))) : Eq(Nat, 1, 0) := e\n")
    accepts(
      pickFn +
        """
          |def inBranch (b: Bool)(e: Eq(Bool, b, Bool.true)) : Eq(Nat, pick(b)(1), 1) := {
          |  match e returning Eq(Nat, pick(b)(1), 1) with
          |  | Eq.refl x => Eq.refl(1)
          |}
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // 6. Bundled protocols.
  // ==================================================================================================================

  test("bundled: packets, identities and Valid of one relation are not another's") {
    rejectsWith[TypeMismatch](
      shares + anyRel +
        """
          |def cast (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))
          |    (t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Protocol.Toks(Protocol.Proto.mk(Nat, Any), l1(2), s, l1(2)) := t
          |""".stripMargin
    )
    rejectsWith[TypeMismatch](
      shares + anyRel + "def cast (s: Protocol.Inst(Protocol.Proto.mk(Nat, Any), l1(2))) : Protocol.Inst(SP, l1(2)) := s\n"
    )
    rejectsWith[TypeMismatch](
      shares + anyRel +
        """
          |def anyValid : Protocol.Valid(Protocol.Proto.mk(Nat, Any), l1(2), l2(2, 2)) :=
          |  Protocol.Valid.mk(Protocol.Proto.mk(Nat, Any), l1(2), l2(2, 2), l0,
          |    Protocol.Reach.step(Protocol.Proto.mk(Nat, Any), l1(2), l1(2), l2(2, 2), l0, Any.mk(l1(2), l2(2, 2)),
          |      Protocol.Reach.initial(Protocol.Proto.mk(Nat, Any), l1(2))))
          |
          |def boom : False := refute(anyValid)
          |""".stripMargin
    )
  }

  test("bundled, sound controls: a variable protocol and Proto.mk of its projections agree") {
    accepts(
      """
        |def gen (P: Protocol.Proto)(init: List(P.Atom))(C: List(P.Atom))(v: Protocol.Valid(Protocol.Proto.mk(P.Atom, P.Step), init, C))
        |    : Protocol.Valid(P, init, C) := v
        |
        |def obs (P: Protocol.Proto)(init: List(P.Atom))(s: Protocol.Inst(P, init))(C: List(P.Atom))
        |    (t: Protocol.Toks(Protocol.Proto.mk(P.Atom, P.Step), init, s, C)) : Protocol.Valid(P, init, C) :=
        |  Protocol.observe(Protocol.Proto.mk(P.Atom, P.Step), init, s, C, t).valid
        |""".stripMargin
    )
  }

  // ==================================================================================================================
  // 7. Over-rejection: a branch on a neutral record whose field type is an opaque application of a witness.
  // ==================================================================================================================

  test("sound control: in a branch on a stuck pair, a field converts with its projection") {
    accepts(
      stuckPair +
        "def t (b: Bool) : Nat := {\n  match g(b) with\n  | Prod.mk x y => {\n    let e : Eq(Nat, x, g(b).fst) := Eq.refl(x)\n    x\n  }\n}\n"
    )
  }

  // The eta case of the unifier unified the field pairs before the type pair, so a field of type Inst(P_t, init_t), an
  // opaque symbol application, met Inst(SP, [2]) before the type pair had solved P_t and init_t: the value refinement
  // was Stuck, MatchChecker.computeReachableCtors fell back to the result-only refinement, and the branch's fields were
  // not linked to the projections. Prod (above) has no such field. The type pair now comes first.
  test("eta unification: a destructured allocation's identity converts with the allocation's projection") {
    accepts(
      shares +
        """
          |def t (sup: Protocol.Supply) : Nat := {
          |  let (n, s, k) := Protocol.new(SP, l1(2), sup)
          |  let e : Eq(Protocol.Inst(SP, l1(2)), s, Protocol.new(SP, l1(2), sup).s) := Eq.refl(s)
          |  0
          |}
          |""".stripMargin
    )
    accepts(
      shares +
        """
          |inductive Holder (P: Protocol.Proto)(init: List(P.Atom)) : Type
          | | mk {P: Protocol.Proto}{init: List(P.Atom)} (s: Protocol.Inst(P, init)) : Holder(P, init)
          |
          |def g (b: Bool)(h1: Holder(SP, l1(2)))(h2: Holder(SP, l1(2))) : Holder(SP, l1(2)) := {
          |  match b with
          |  | Bool.true => h1
          |  | Bool.false => h2
          |}
          |
          |def t (b: Bool)(h1: Holder(SP, l1(2)))(h2: Holder(SP, l1(2))) : Nat := {
          |  match g(b, h1, h2) with
          |  | Holder.mk s => {
          |    let e : Eq(Protocol.Inst(SP, l1(2)), s, g(b, h1, h2).s) := Eq.refl(s)
          |    0
          |  }
          |}
          |""".stripMargin
    )
  }
}
