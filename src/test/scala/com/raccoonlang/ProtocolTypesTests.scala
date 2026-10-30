package com.raccoonlang

import com.raccoonlang.ProgramFixtures._
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/**
 * Protocol kernel types (docs/kernel.md, "Resource protocols"): the opaque builtins `Protocol.Supply`, `Protocol.Inst`
 * and `Protocol.Tok`, and the linear families `Protocol.Toks`, `Protocol.Observed` and `Protocol.Fresh`, each taking a
 * protocol's atom type and step relation as parameters. The primitives are tested in `ProtocolPrimitivesTests`, so
 * identities and packets here are parameters. Every program runs without user axioms.
 */
class ProtocolTypesTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.test, allowUserAxioms = false)
  import programs._

  private val swap =
    """
      |inductive Swap indices (consumed: List(Nat))(produced: List(Nat)) : Prop
      | | swap (x: Nat)(y: Nat) : Swap(List.cons(x, List.cons(y, List.nil(Nat))), List.cons(y, List.cons(x, List.nil(Nat))))
      |
      |""".stripMargin

  /** A token of `s` for `a`, as the only one of a packet. */
  private val single =
    """
      |def single (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(a: Nat)(t: Protocol.Tok(Protocol.Proto.mk(Nat, Swap), init, s, a))
      |    : Protocol.Toks(Protocol.Proto.mk(Nat, Swap), init, s, List.cons(a, List.nil(Nat))) :=
      |  Protocol.Toks.cons(Protocol.Proto.mk(Nat, Swap), init, s, a, t, List.nil(Nat), Protocol.Toks.nil(Protocol.Proto.mk(Nat, Swap), init, s))
      |
      |""".stripMargin

  /** Packet split and join (`ProgramFixtures.packets`), over `Both`. */
  private val packets = swap + ProgramFixtures.packets

  private def codomain(value: Value): Value =
    value.tpe match {
      case pi: VPi => pi.codomain(BinderOps.freshen(pi))
      case other   => other
    }

  test("Supply, Inst and Tok are opaque symbols, and Toks, Observed and Fresh are Lin(0) inductives") {
    def symbol(name: String): VConst =
      Kernel.env(name) match {
        case const @ VConst(`name`, Symbol, _) => const
        case other                             => fail(s"$name is $other")
      }
    assertEquals(symbol("Protocol.Supply").tpe, VLin(Level.zero))
    assertEquals(codomain(symbol("Protocol.Inst")), TypeTpe)
    assertEquals(codomain(symbol("Protocol.Tok")), VLin(Level.zero))
    // The size check charges a Proto by its fields, a Type and a relation into Prop, which cost nothing, so the packet
    // families fit Lin(0).
    Vector("Protocol.Toks" -> 4, "Protocol.Observed" -> 4, "Protocol.Fresh" -> 2).foreach { case (name, arity) =>
      Kernel.env(name) match {
        case family @ VConst(`name`, Inductive(meta), _) =>
          assertEquals(meta.familyArity, arity, name)
          // Observed and Fresh have one constructor and no indices, so they have selectors and structure eta.
          assertEquals(meta.eta.isDefined, name != "Protocol.Toks", name)
          assertEquals(codomain(family), VLin(Level.zero), name)
        case other => fail(s"$name is $other")
      }
    }
    // Toks has an index, so a packet is a constructor value, never a packed word.
    assertEquals(Kernel.env("Protocol.Toks.cons").asInstanceOf[ConstructorHead].listShape, None)
    // Every kernel environment holds the same symbols.
    assert(Interpreter.initialEnv(Prelude.none)("Protocol.Tok") eq Kernel.env("Protocol.Tok"))
  }

  test("the protocol types are present and usable without a prelude") {
    new Programs(Prelude.none, allowUserAxioms = false).run(
      swap + single +
        """
          |def pass (sup: Protocol.Supply) : Protocol.Supply := sup
          |
          |def refresh (init: List(Nat))(f: Protocol.Fresh(Protocol.Proto.mk(Nat, Swap), init)) : Protocol.Fresh(Protocol.Proto.mk(Nat, Swap), init) := {
          |  let (next, s, toks) := f
          |  Protocol.Fresh.mk(Protocol.Proto.mk(Nat, Swap), init, next, s, toks)
          |}
          |
          |def reobserve (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(C: List(Nat))
          |    (o: Protocol.Observed(Protocol.Proto.mk(Nat, Swap), init, s, C)) : Protocol.Observed(Protocol.Proto.mk(Nat, Swap), init, s, C) := {
          |  let (toks, valid) := o
          |  Protocol.Observed.mk(Protocol.Proto.mk(Nat, Swap), init, s, C, toks, valid)
          |}
          |""".stripMargin
    )
  }

  test("opaque applications convert only by congruence and give unification nothing") {
    val env = declsEnv(swap)
    val listNat = Interpreter.evalApply(env("List"), Vector(Kernel.natType))
    val x = FreshVar.freshVar("x", listNat)
    val y = FreshVar.freshVar("y", listNat)
    val proto = Interpreter.evalApply(env("Protocol.Proto.mk"), Vector(Kernel.natType, env("Swap")))
    def inst(init: Value): Value =
      Interpreter.evalApply(env("Protocol.Inst"), Vector(proto, init))
    inst(x) match {
      case VApp(VConst("Protocol.Inst", Symbol, _), args, TypeTpe, blockers) =>
        assertEquals(args.length, 2)
        assert(blockers.isEmpty)
      case other => fail(s"Inst(Nat, Swap, x) is $other")
    }
    assert(ValueEquivalence.defEq(inst(x), inst(x)))
    assertEquals(inst(x).key, inst(x).key)
    assert(!ValueEquivalence.defEq(inst(x), inst(y)))
    // A nominal family would unify x with y; an opaque symbol is stuck.
    val refinable = EqStore.empty.allow(DepSet.single(x.id) ++ DepSet.single(y.id))
    assert(ValueEquivalence.tryUnify(inst(x), inst(y), refinable).left.exists {
      case _: ValueEquivalence.UnificationFailure.Stuck => true
      case _                                            => false
    })
    // So an equation between identity types refines nothing, unlike one between packet types.
    assertErrorAt[TypeMismatch](
      swap +
        """
          |def injective (x: List(Nat))(y: List(Nat))(h: Eq(Type, Protocol.Inst(Protocol.Proto.mk(Nat, Swap), x), Protocol.Inst(Protocol.Proto.mk(Nat, Swap), y)))
          |    : Eq(List(Nat), x, y) := {
          |  match h returning Eq(List(Nat), x, y) with
          |  | Eq.refl z => Eq.refl(x)
          |}
          |""".stripMargin,
      "(x)",
      "Eq.refl(x)"
    )
    run(
      swap +
        """
          |def injective (s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), List.nil(Nat)))(x: List(Nat))(y: List(Nat))
          |    (h: Eq(Lin(Level.zero), Protocol.Toks(Protocol.Proto.mk(Nat, Swap), List.nil(Nat), s, x), Protocol.Toks(Protocol.Proto.mk(Nat, Swap), List.nil(Nat), s, y)))
          |    : Eq(List(Nat), x, y) := {
          |  match h returning Eq(List(Nat), x, y) with
          |  | Eq.refl z => Eq.refl(x)
          |}
          |""".stripMargin
    )
  }

  test("packets split and join by structural recursion on the first list, and join is split's converse") {
    run(
      packets +
        """
          |def roundTrip (Atom: Type)(Step: (consumed: List(Atom)) -> (produced: List(Atom)) -> Prop)(init: List(Atom))
          |    (s: Protocol.Inst(Protocol.Proto.mk(Atom, Step), init))(A: List(Atom))(B: List(Atom))
          |    (left: Protocol.Toks(Protocol.Proto.mk(Atom, Step), init, s, A))(right: Protocol.Toks(Protocol.Proto.mk(Atom, Step), init, s, B))
          |    : Both(Protocol.Toks(Protocol.Proto.mk(Atom, Step), init, s, A), Protocol.Toks(Protocol.Proto.mk(Atom, Step), init, s, B)) :=
          |  splitToks(Atom, Step, init, s, A, B, joinToks(Atom, Step, init, s, A, B, left, right))
          |""".stripMargin
    )
  }

  // Structural recursion on an indexed linear family with a variable index (KERNEL_FOLLOWUPS 2.4): matching the packet
  // refines its index and links the packet to its constructor, whose field is then a structural subterm.
  test("a packet recursion at a variable index decreases structurally on the packet, or by a measure") {
    def join(decreases: String): String =
      swap +
        s"""
           |def join (left: Protocol.Toks(Protocol.Proto.mk($$Atom, $$Step), $$init, $$s, $$A))(right: Protocol.Toks(Protocol.Proto.mk(Atom, Step), init, s, $$B))
           |    : Protocol.Toks(Protocol.Proto.mk(Atom, Step), init, s, List.append(A, B)) decreases $decreases := {
           |  match left with
           |  | Protocol.Toks.nil => right
           |  | Protocol.Toks.cons a t C rest =>
           |      Protocol.Toks.cons(Protocol.Proto.mk(Atom, Step), init, s, a, t, List.append(C, B), join(rest, right))
           |}
           |""".stripMargin
    run(join("measure(List.length(A))"))
    run(join("structural(left)"))
    // The rest is smaller than the packet; the packet itself is not.
    assertErrorAt[NonDecreasingRecursiveCall](
      join("structural(left)").replace(
        "join(rest, right)",
        "join(Protocol.Toks.cons(Protocol.Proto.mk(Atom, Step), init, s, a, t, C, rest), right)"
      ),
      "(Protocol.Toks.cons(Protocol.Proto.mk(Atom, Step), init, s, a, t, C, rest), right)"
    )
  }

  test("Reach induction bounds the atoms of an observed packet by the initial inventory") {
    run(
      swap +
        """
          |def Le (a: Nat)(b: Nat) : Prop := Eq(Bool, Nat.ble(a, b), Bool.true)
          |
          |def transport (A: Type)(x: A)(y: A)(p: Eq(A, x, y))(motive: A -> Prop)(h: motive(x)) : motive(y) := {
          |  match p returning motive(y) with
          |  | Eq.refl z => h
          |}
          |
          |def congSucc (a: Nat)(b: Nat)(h: Eq(Nat, a, b)): Eq(Nat, Nat.succ(a), Nat.succ(b)) := {
          |  match h returning Eq(Nat, Nat.succ(a), Nat.succ(b)) with
          |  | Eq.refl z => Eq.refl(Nat.succ(a))
          |}
          |
          |def eqSymm (a: Nat)(b: Nat)(h: Eq(Nat, a, b)): Eq(Nat, b, a) := {
          |  match h returning Eq(Nat, b, a) with
          |  | Eq.refl z => Eq.refl(a)
          |}
          |
          |def eqTrans (a: Nat)(b: Nat)(c: Nat)(h1: Eq(Nat, a, b))(h2: Eq(Nat, b, c)): Eq(Nat, a, c) := {
          |  match h2 returning Eq(Nat, a, c) with
          |  | Eq.refl z => h1
          |}
          |
          |def permLength (xs: List(Nat))(ys: List(Nat))(p: List.Perm(Nat, xs, ys)):
          |    Eq(Nat, List.length(xs), List.length(ys)) decreases structural(p) := {
          |  match p returning Eq(Nat, List.length(xs), List.length(ys)) with
          |  | List.Perm.nil => Eq.refl(List.length(List.nil(Nat)))
          |  | List.Perm.cons x xs1 ys1 q => congSucc(List.length(xs1), List.length(ys1), permLength(xs1, ys1, q))
          |  | List.Perm.swap x y zs => Eq.refl(List.length(List.cons(y, List.cons(x, zs))))
          |  | List.Perm.trans as1 bs1 cs1 q r =>
          |      eqTrans(List.length(as1), List.length(bs1), List.length(cs1), permLength(as1, bs1, q), permLength(bs1, cs1, r))
          |}
          |
          |def conserved (init: List(Nat))(C: List(Nat))(r: Protocol.Reach(Protocol.Proto.mk(Nat, Swap), init, C)):
          |    Eq(Nat, List.length(C), List.length(init)) decreases structural(r) := {
          |  match r returning Eq(Nat, List.length(C), List.length(init)) with
          |  | Protocol.Reach.initial => Eq.refl(List.length(init))
          |  | Protocol.Reach.step A B frame h prev => {
          |    match h returning Eq(Nat, List.length(List.append(B, frame)), List.length(init)) with
          |    | Swap.swap x y => conserved(init, List.append(A, frame), prev)
          |  }
          |  | Protocol.Reach.perm C1 D1 prev q =>
          |      eqTrans(List.length(D1), List.length(C1), List.length(init),
          |        eqSymm(List.length(C1), List.length(D1), permLength(C1, D1, q)), conserved(init, C1, prev))
          |}
          |
          |def validBound (init: List(Nat))(C: List(Nat))(v: Protocol.Valid(Protocol.Proto.mk(Nat, Swap), init, C))
          |    : Le(List.length(C), List.length(init)) := {
          |  match v returning Le(List.length(C), List.length(init)) with
          |  | Protocol.Valid.mk C1 rest r =>
          |      transport(Nat, List.length(List.append(C1, rest)), List.length(init), conserved(init, List.append(C1, rest), r),
          |        fun (n: Nat): Prop => Le(List.length(C1), n), Eq.refl(Bool.true))
          |}
          |
          |inductive Bounded (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(C: List(Nat)) : Lin(Level.zero)
          | | mk {init: List(Nat)}{s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init)}{C: List(Nat)}
          |     (toks: Protocol.Toks(Protocol.Proto.mk(Nat, Swap), init, s, C))(bound: Le(List.length(C), List.length(init))) : Bounded(init, s, C)
          |
          |def observedBound (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(C: List(Nat))
          |    (o: Protocol.Observed(Protocol.Proto.mk(Nat, Swap), init, s, C)) : Bounded(init, s, C) := {
          |  let (toks, valid) := o
          |  Bounded.mk(init, s, C, toks, validBound(init, C, valid))
          |}
          |""".stripMargin
    )
  }

  test("identities are first-class: listed, stored, returned, and hidden with a packet of their own") {
    run(
      swap +
        """
          |def pair (init: List(Nat))(s1: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(s2: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))
          |    : List(Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init)) :=
          |  List.cons(s1, List.cons(s2, List.nil(Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))))
          |
          |inductive Named (init: List(Nat)) : Type
          | | mk {init: List(Nat)} (tag: Nat)(id: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init)) : Named(init)
          |
          |def idOf (init: List(Nat))(n: Named(init)) : Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init) := n.id
          |
          |def pick (b: Bool)(init: List(Nat))(s1: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(s2: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))
          |    : Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init) := {
          |  match b with
          |  | Bool.true => s1
          |  | Bool.false => s2
          |}
          |
          |inductive Hide (init: List(Nat)) : Lin(Level.zero)
          | | mk {init: List(Nat)} (s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(C: List(Nat))(toks: Protocol.Toks(Protocol.Proto.mk(Nat, Swap), init, s, C))
          |     : Hide(init)
          |
          |def hide (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(C: List(Nat))(toks: Protocol.Toks(Protocol.Proto.mk(Nat, Swap), init, s, C))
          |    : Hide(init) :=
          |  Hide.mk(init, s, C, toks)
          |
          |def unhide (init: List(Nat))(h: Hide(init))(R: Lin(Level.zero))
          |    (k: (s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init)) -> (C: List(Nat)) -> (toks: Protocol.Toks(Protocol.Proto.mk(Nat, Swap), init, s, C)) -> R)
          |    : R := {
          |  let (s, C, toks) := h
          |  k(s, C, toks)
          |}
          |
          |def rehide (init: List(Nat))(h: Hide(init)) : Hide(init) :=
          |  unhide(init, h, Hide(init),
          |    fun (s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(C: List(Nat))(toks: Protocol.Toks(Protocol.Proto.mk(Nat, Swap), init, s, C)): Hide(init) =>
          |      hide(init, s, C, toks))
          |""".stripMargin
    )
  }

  test("a token is used at most once") {
    run(swap + single)
    assertErrorAt[LinearReused](
      swap +
        """
          |def twice (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(a: Nat)(t: Protocol.Tok(Protocol.Proto.mk(Nat, Swap), init, s, a))
          |    : Protocol.Toks(Protocol.Proto.mk(Nat, Swap), init, s, List.cons(a, List.cons(a, List.nil(Nat)))) :=
          |  Protocol.Toks.cons(Protocol.Proto.mk(Nat, Swap), init, s, a, t, List.cons(a, List.nil(Nat)),
          |    Protocol.Toks.cons(Protocol.Proto.mk(Nat, Swap), init, s, a, t, List.nil(Nat), Protocol.Toks.nil(Protocol.Proto.mk(Nat, Swap), init, s)))
          |""".stripMargin,
      "t",
      "t, List.nil(Nat), Protocol"
    )
    // A token may be dropped: use is affine.
    run(
      swap +
        """
          |def drop (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(a: Nat)(t: Protocol.Tok(Protocol.Proto.mk(Nat, Swap), init, s, a))
          |    : Protocol.Toks(Protocol.Proto.mk(Nat, Swap), init, s, List.nil(Nat)) :=
          |  Protocol.Toks.nil(Protocol.Proto.mk(Nat, Swap), init, s)
          |""".stripMargin
    )
    assertErrorAt[LinearReused](
      packets + single +
        """
          |def dup (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(a: Nat)(t: Protocol.Tok(Protocol.Proto.mk(Nat, Swap), init, s, a))
          |    : Protocol.Toks(Protocol.Proto.mk(Nat, Swap), init, s, List.cons(a, List.cons(a, List.nil(Nat)))) := {
          |  let p := single(init, s, a, t)
          |  joinToks(Nat, Swap, init, s, List.cons(a, List.nil(Nat)), List.cons(a, List.nil(Nat)), p, p)
          |}
          |""".stripMargin,
      "p",
      "p)\n}"
    )
  }

  test("a token cannot be forged: Tok has no constructor and cannot be matched, nor can a Supply") {
    // A missing name below a global is a selection from that global's value, a type with no constructor of that name.
    val noCtor = assertErrorAt[NotFound](swap + "def bad : Nat := Protocol.Tok.mk\n", "Protocol.Tok.mk")
    assertEquals(noCtor.getMessage, "Protocol.Tok.mk not found: Protocol.Tok has no constructor mk")
    assertErrorAt[NotFound](
      swap + "def bad (b: Bool) : Nat := {\n  match b with\n  | Protocol.Tok.mk => 0\n}\n",
      "| Protocol.Tok.mk => 0"
    )
    // An empty match would turn a token into a supply, or a supply into a token.
    assertErrorAt[NonInductiveMatch](
      swap +
        "def bad (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(a: Nat)(t: Protocol.Tok(Protocol.Proto.mk(Nat, Swap), init, s, a))" +
        " : Protocol.Supply := {\n  match t returning Protocol.Supply with\n}\n",
      "match t returning Protocol.Supply with"
    )
    assertErrorAt[NonInductiveMatch](
      swap +
        "def bad (sup: Protocol.Supply)(init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(a: Nat)" +
        " : Protocol.Tok(Protocol.Proto.mk(Nat, Swap), init, s, a) := {\n  match sup returning Protocol.Tok(Protocol.Proto.mk(Nat, Swap), init, s, a) with\n}\n",
      "match sup returning Protocol.Tok(Protocol.Proto.mk(Nat, Swap), init, s, a) with"
    )
  }

  // Structure eta: Observed and Fresh have one constructor, so they have selectors. A selector returning data consumes
  // its struct and drops the other fields; one returning a proof, such as `valid`, is a read extent and only reads it.
  test("Observed and Fresh have selectors; a proof selector reads its struct, a data selector consumes it") {
    run(
      swap +
        """
          |def toksOf (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(C: List(Nat))
          |    (o: Protocol.Observed(Protocol.Proto.mk(Nat, Swap), init, s, C)) : Protocol.Toks(Protocol.Proto.mk(Nat, Swap), init, s, C) := o.toks
          |
          |def nextOf (f: Protocol.Fresh(Protocol.Proto.mk(Nat, Swap), List.nil(Nat))) : Protocol.Supply := f.next
          |
          |def both (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(C: List(Nat))
          |    (o: Protocol.Observed(Protocol.Proto.mk(Nat, Swap), init, s, C)) : Protocol.Toks(Protocol.Proto.mk(Nat, Swap), init, s, C) := {
          |  let v : Protocol.Valid(Protocol.Proto.mk(Nat, Swap), init, C) := o.valid
          |  o.toks
          |}
          |""".stripMargin
    )
    assertErrorAt[LinearReused](
      swap +
        """
          |def bad (f: Protocol.Fresh(Protocol.Proto.mk(Nat, Swap), List.nil(Nat))) : Protocol.Supply := {
          |  let i := f.s
          |  f.next
          |}
          |""".stripMargin,
      "f.next"
    )
  }

  test("a Tok or Supply field in a Sort inductive is LinearFieldInUnrestrictedFamily") {
    assertErrorAt[LinearFieldInUnrestrictedFamily](
      swap +
        """
          |inductive Held (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init)) : Type
          | | mk {init: List(Nat)}{s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init)} (a: Nat)(t: Protocol.Tok(Protocol.Proto.mk(Nat, Swap), init, s, a))
          |     : Held(init, s)
          |""".stripMargin,
      "(t: Protocol.Tok(Protocol.Proto.mk(Nat, Swap), init, s, a))"
    )
    assertErrorAt[LinearFieldInUnrestrictedFamily](
      swap + "inductive Stash : Type\n | mk (sup: Protocol.Supply) : Stash\n",
      "(sup: Protocol.Supply)"
    )
  }

  test("a packet is not a List element: List's Sort parameter does not take a linear type") {
    assertErrorAt[TypeMismatch](
      swap +
        """
          |def Packets (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(C: List(Nat)) : Type :=
          |  List(Protocol.Toks(Protocol.Proto.mk(Nat, Swap), init, s, C))
          |""".stripMargin,
      "(Protocol.Toks(Protocol.Proto.mk(Nat, Swap), init, s, C))"
    )
  }

  test("the protocol types and Lin cannot be redeclared in a program or a prelude") {
    val redeclarations = Vector(
      "Protocol.Supply" -> "namespace Protocol {\n  def Supply : Lin(Level.zero) := builtin\n}\n",
      "Protocol.Tok" -> "namespace Protocol {\n  inductive Tok : Lin(Level.zero)\n}\n",
      "Protocol.Toks" -> "namespace Protocol {\n  def Toks : Nat := 0\n}\n",
      "Lin" -> "def Lin (l: Level): Type := builtin\n"
    )
    // Each is located at the redeclared name (KERNEL_FOLLOWUPS 1.4).
    redeclarations.foreach { case (name, src) =>
      val inProgram = intercept[AlreadyDefined](parse(src))
      assertEquals(inProgram.name, name)
      val span = inProgram.span.getOrElse(fail(s"$name has no span"))
      assertEquals(src.substring(span.start, span.end), name.split('.').last)
      assertEquals(intercept[AlreadyDefined](Prelude.fromSource("redeclaring prelude", src)).name, name)
    }
  }

  // The families take a Proto (KERNEL_FOLLOWUPS 2.3); by structure eta a variable protocol and its constructor applied
  // to its projections give the same packet types, and a concrete protocol is its constructor.
  test("a variable protocol and Proto.mk of its projections give the same packet types") {
    run(
      """
        |def same (P: Protocol.Proto)(init: List(P.Atom))(s: Protocol.Inst(P, init))(t: Protocol.Toks(P, init, s, List.nil(P.Atom)))
        |    : Protocol.Toks(Protocol.Proto.mk(P.Atom, P.Step), init, s, List.nil(P.Atom)) := t
        |
        |def back (P: Protocol.Proto)(init: List(P.Atom))(s: Protocol.Inst(Protocol.Proto.mk(P.Atom, P.Step), init))
        |    : Protocol.Inst(P, init) := s
        |""".stripMargin
    )
  }

  test("tokens of different instances have different types") {
    assertErrorAt[TypeMismatch](
      swap +
        """
          |def bad (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(s2: Protocol.Inst(Protocol.Proto.mk(Nat, Swap), init))(a: Nat)
          |    (t: Protocol.Tok(Protocol.Proto.mk(Nat, Swap), init, s, a)) : Protocol.Toks(Protocol.Proto.mk(Nat, Swap), init, s2, List.cons(a, List.nil(Nat))) :=
          |  Protocol.Toks.cons(Protocol.Proto.mk(Nat, Swap), init, s2, a, t, List.nil(Nat), Protocol.Toks.nil(Protocol.Proto.mk(Nat, Swap), init, s2))
          |""".stripMargin,
      "(Protocol.Proto.mk(Nat, Swap), init, s2, a, t, List.nil(Nat), Protocol.Toks.nil(Protocol.Proto.mk(Nat, Swap), init, s2))"
    )
  }
}
