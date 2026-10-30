package com.raccoonlang

import java.nio.file.{Path, Paths}

import com.raccoonlang.ProgramFixtures._

/**
 * The protocol library in `lib/Protocol` (docs/kernel.md, "The protocol library"), loaded from the library root as
 * `--root lib` loads it. Every program runs without user axioms. The acceptance programs apply the library's laws,
 * morphisms, building blocks and packet operations to concrete protocols; one entry runs on real tokens.
 */
class ProtocolLibraryTests extends munit.FunSuite {
  private val library: Path = Paths.get("lib").toAbsolutePath.normalize

  private val modules = Vector("Logic", "Lists", "Nats", "Laws", "Morphism", "Packets", "Exclusive", "Shares")

  private val programs = new Programs(Prelude.default, allowUserAxioms = false, roots = Vector(library))
  import programs._

  test("every library module checks without user axioms") {
    modules.foreach(module => run(s"import Protocol.$module\n"))
  }

  test("the Derives laws, Reach.iff_derives and Reach.frame, the Valid laws, and the bundled forms on a concrete protocol") {
    run(
    """
      |import Protocol.Laws
      |
      |def l1 (a: Nat): List(Nat) := List.cons(a, List.nil(Nat))
      |def l2 (a: Nat)(b: Nat): List(Nat) := List.cons(a, l1(b))
      |def l3 (a: Nat)(b: Nat)(c: Nat): List(Nat) := List.cons(a, l2(b, c))
      |
      |inductive Swap indices (consumed: List(Nat))(produced: List(Nat)) : Prop
      | | swap (x: Nat)(y: Nat) : Swap(l2(x, y), l2(y, x))
      |
      |open Protocol.{Reach, Valid, Derives}
      |
      |def swapped : Derives(Protocol.Proto.mk(Nat, Swap), l2(1, 2), l2(2, 1)) := Derives.single(Protocol.Proto.mk(Nat, Swap), l2(1, 2), l2(2, 1), Swap.swap(1, 2))
      |
      |def roundTrip : Derives(Protocol.Proto.mk(Nat, Swap), l2(1, 2), l2(1, 2)) :=
      |  Derives.trans(Protocol.Proto.mk(Nat, Swap), l2(1, 2), l2(2, 1), l2(1, 2), swapped, Derives.single(Protocol.Proto.mk(Nat, Swap), l2(2, 1), l2(1, 2), Swap.swap(2, 1)))
      |
      |def framedRight : Derives(Protocol.Proto.mk(Nat, Swap), l3(1, 2, 3), l3(2, 1, 3)) := Derives.frame(Protocol.Proto.mk(Nat, Swap), l2(1, 2), l2(2, 1), l1(3), swapped)
      |
      |def framedLeft : Derives(Protocol.Proto.mk(Nat, Swap), l3(0, 1, 2), l3(0, 2, 1)) := Derives.frame_left(Protocol.Proto.mk(Nat, Swap), l2(1, 2), l2(2, 1), l1(0), swapped)
      |
      |def reordered : Derives(Protocol.Proto.mk(Nat, Swap), l2(1, 2), l2(2, 1)) := Derives.of_perm(Protocol.Proto.mk(Nat, Swap), l2(1, 2), l2(2, 1), List.Perm.swap(Nat, 2, 1, List.nil(Nat)))
      |
      |// Reach and Derives agree, in both directions.
      |def reached : Reach(Protocol.Proto.mk(Nat, Swap), l2(1, 2), l2(2, 1)) := {
      |  let (toDerives, toReach) := Reach.iff_derives(Protocol.Proto.mk(Nat, Swap), l2(1, 2), l2(2, 1))
      |  toReach(swapped)
      |}
      |
      |def derived : Derives(Protocol.Proto.mk(Nat, Swap), l2(1, 2), l2(2, 1)) := {
      |  let (toDerives, toReach) := Reach.iff_derives(Protocol.Proto.mk(Nat, Swap), l2(1, 2), l2(2, 1))
      |  toDerives(reached)
      |}
      |
      |def framedReach : Reach(Protocol.Proto.mk(Nat, Swap), l3(1, 2, 3), l3(2, 1, 3)) := Reach.frame(Protocol.Proto.mk(Nat, Swap), l2(1, 2), l2(2, 1), l1(3), reached)
      |
      |def fromNothing : Reach(Protocol.Proto.mk(Nat, Swap), l2(7, 8), l2(7, 8)) :=
      |  Reach.of_empty(Protocol.Proto.mk(Nat, Swap), l2(7, 8), List.nil(Nat), Reach.initial(Protocol.Proto.mk(Nat, Swap), List.nil(Nat)))
      |
      |// The Valid laws.
      |def whole : Valid(Protocol.Proto.mk(Nat, Swap), l3(1, 2, 3), l3(2, 1, 3)) := Valid.of_reach(Protocol.Proto.mk(Nat, Swap), l3(1, 2, 3), l3(2, 1, 3), framedReach)
      |
      |def front : Valid(Protocol.Proto.mk(Nat, Swap), l3(1, 2, 3), l2(2, 1)) := Valid.left(Protocol.Proto.mk(Nat, Swap), l3(1, 2, 3), l2(2, 1), l1(3), whole)
      |
      |def back : Valid(Protocol.Proto.mk(Nat, Swap), l3(1, 2, 3), l1(3)) := Valid.right(Protocol.Proto.mk(Nat, Swap), l3(1, 2, 3), l2(2, 1), l1(3), whole)
      |
      |def rotated : Valid(Protocol.Proto.mk(Nat, Swap), l3(1, 2, 3), l3(3, 2, 1)) :=
      |  Valid.perm(Protocol.Proto.mk(Nat, Swap), l3(1, 2, 3), l3(2, 1, 3), l3(3, 2, 1), whole, List.Perm.append_comm(l2(2, 1), l1(3)))
      |
      |def one : Valid(Protocol.Proto.mk(Nat, Swap), l3(1, 2, 3), l1(1)) :=
      |  Valid.restrict(Protocol.Proto.mk(Nat, Swap), l3(1, 2, 3), l3(2, 1, 3), l1(1), l2(2, 3), whole, List.Perm.swap(Nat, 1, 2, l1(3)))
      |
      |def stepped : Valid(Protocol.Proto.mk(Nat, Swap), l3(1, 2, 3), l3(1, 2, 3)) := Valid.step(Protocol.Proto.mk(Nat, Swap), l3(1, 2, 3), l2(2, 1), l2(1, 2), l1(3), Swap.swap(2, 1), whole)
      |
      |def empty : Valid(Protocol.Proto.mk(Nat, Swap), l3(1, 2, 3), List.nil(Nat)) := Valid.nil(Protocol.Proto.mk(Nat, Swap), l3(1, 2, 3))
      |
      |def lifted : Valid(Protocol.Proto.mk(Nat, Swap), l1(5), List.append(l1(5), List.nil(Nat))) := Valid.of_empty(Protocol.Proto.mk(Nat, Swap), l1(5), List.nil(Nat), Valid.nil(Protocol.Proto.mk(Nat, Swap), List.nil(Nat)))
      |
      |// The bundled forms agree with the component forms.
      |def swaps : Protocol.Proto := Protocol.Proto.mk(Nat, Swap)
      |
      |def bundled : Protocol.Valid(swaps, l3(1, 2, 3), l2(2, 1)) := front
      |
      |def bundledStep : Protocol.Reach(swaps, l2(1, 2), l2(2, 1)) :=
      |  Protocol.Reach.step(swaps, l2(1, 2), l2(1, 2), l2(2, 1), List.nil(Nat), Swap.swap(1, 2), Protocol.Reach.initial(swaps, l2(1, 2)))
      |""".stripMargin
    )
  }

  test("a footprint morphism into Exclusive gives disjointness, and transport, pullback and comp apply") {
    run(
    """
      |import Protocol.Morphism
      |import Protocol.Exclusive
      |
      |// Cells own word keys; `fuse` and `part` keep the footprint, `free` releases it.
      |inductive Cell : Type
      | | one (k: Nat) : Cell
      | | two (a: Nat)(b: Nat) : Cell
      |
      |def c1 (x: Cell): List(Cell) := List.cons(x, List.nil(Cell))
      |def c2 (x: Cell)(y: Cell): List(Cell) := List.cons(x, c1(y))
      |
      |inductive CellStep indices (consumed: List(Cell))(produced: List(Cell)) : Prop
      | | fuse (a: Nat)(b: Nat) : CellStep(c2(Cell.one(a), Cell.one(b)), c1(Cell.two(a, b)))
      | | part (a: Nat)(b: Nat) : CellStep(c1(Cell.two(a, b)), c2(Cell.one(a), Cell.one(b)))
      | | free (k: Nat) : CellStep(c1(Cell.one(k)), List.nil(Cell))
      |
      |def cells : Protocol.Proto := Protocol.Proto.mk(Cell, CellStep)
      |
      |def Keys : Protocol.Proto := Exclusive.proto(Nat)
      |
      |def keys (x: Cell): List(Nat) := {
      |  match x returning List(Nat) with
      |  | Cell.one k => List.cons(k, List.nil(Nat))
      |  | Cell.two a b => List.cons(a, List.cons(b, List.nil(Nat)))
      |}
      |
      |// Each step's footprint is a permutation of its inputs', or a key release.
      |def keysSim (A: List(Cell))(B: List(Cell))(s: CellStep(A, B)):
      |    Protocol.Derives(Keys, List.flatMap(A, Nat, keys), List.flatMap(B, Nat, keys)) := {
      |  match s returning Protocol.Derives(Keys, List.flatMap(A, Nat, keys), List.flatMap(B, Nat, keys)) with
      |  | .fuse a b => Protocol.Derives.refl(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), List.flatMap(A, Nat, keys))
      |  | .part a b => Protocol.Derives.refl(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), List.flatMap(A, Nat, keys))
      |  | .free k => Protocol.Derives.single(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), List.cons(k, List.nil(Nat)), List.nil(Nat), Exclusive.Step.drop(k))
      |}
      |
      |def footprint : Protocol.Morphism(cells, Keys) :=
      |  Protocol.Morphism.mk(cells, Keys, keys, fun (A: List(Cell))(B: List(Cell))(s: CellStep(A, B)):
      |    Protocol.Derives(Keys, List.flatMap(A, Nat, keys), List.flatMap(B, Nat, keys)) => keysSim(A, B, s))
      |
      |// Disjointness of jointly valid cells, from Exclusive through the morphism.
      |def disjoint (init: List(Cell))(n: List.Nodup(List.flatMap(init, Nat, keys)))(x: Cell)(y: Cell)
      |    (v: Protocol.Valid(cells, init, c2(x, y)))(k: Nat)(left: List.Mem(Nat, k, keys(x)))(right: List.Mem(Nat, k, keys(y))): False :=
      |  Exclusive.disjoint(Nat, List.flatMap(init, Nat, keys), keys(x), keys(y),
      |    Protocol.Morphism.transport_valid(cells, Keys, footprint, init, c2(x, y), v), n, k, left, right)
      |
      |// Exclusive's invariant pulled back: every reachable configuration of cells holds each key once.
      |def keysOnce (init: List(Cell))(n: List.Nodup(List.flatMap(init, Nat, keys)))(C: List(Cell))(r: Protocol.Reach(cells, init, C)):
      |    Exclusive.Good(Nat, List.flatMap(init, Nat, keys), List.flatMap(C, Nat, keys)) :=
      |  Protocol.Morphism.pullback(cells, Keys, footprint, init,
      |    fun (D: List(Nat)): Prop => Exclusive.Good(Nat, List.flatMap(init, Nat, keys), D),
      |    fun (D: List(Nat))(rd: Protocol.Reach(Keys, List.flatMap(init, Nat, keys), D)): Exclusive.Good(Nat, List.flatMap(init, Nat, keys), D) =>
      |      Exclusive.reach_good(Nat, List.flatMap(init, Nat, keys), D, rd, n), C, r)
      |
      |// The same for held packets: jointly valid cells hold each key once.
      |def heldOnce (init: List(Cell))(n: List.Nodup(List.flatMap(init, Nat, keys)))(C: List(Cell))(v: Protocol.Valid(cells, init, C)):
      |    Exclusive.Good(Nat, List.flatMap(init, Nat, keys), List.flatMap(C, Nat, keys)) :=
      |  Protocol.Morphism.pullback_valid(cells, Keys, footprint, init,
      |    fun (D: List(Nat)): Prop => Exclusive.Good(Nat, List.flatMap(init, Nat, keys), D),
      |    fun (D: List(Nat))(vd: Protocol.Valid(Keys, List.flatMap(init, Nat, keys), D)): Exclusive.Good(Nat, List.flatMap(init, Nat, keys), D) =>
      |      Exclusive.valid_good(Nat, List.flatMap(init, Nat, keys), D, vd, n), C, v)
      |
      |// Composition with the identity acts as the footprint.
      |def throughId : Protocol.Morphism(cells, Keys) := Protocol.Morphism.comp(cells, Keys, Keys, footprint, Protocol.Morphism.id(Keys))
      |
      |def throughIdMap : Eq(List(Nat), Protocol.Morphism.map(cells, Keys, throughId)(Cell.two(1, 2)), List.cons(1, List.cons(2, List.nil(Nat)))) :=
      |  Protocol.Morphism.comp_map(cells, Keys, Keys, footprint, Protocol.Morphism.id(Keys), Cell.two(1, 2))
      |
      |def fused : Protocol.Reach(cells, c2(Cell.one(1), Cell.one(2)), c1(Cell.two(1, 2))) :=
      |  Protocol.Reach.step(cells, c2(Cell.one(1), Cell.one(2)), c2(Cell.one(1), Cell.one(2)), c1(Cell.two(1, 2)), List.nil(Cell),
      |    CellStep.fuse(1, 2), Protocol.Reach.initial(cells, c2(Cell.one(1), Cell.one(2))))
      |
      |def fusedKeys : Protocol.Reach(Keys, List.cons(1, List.cons(2, List.nil(Nat))), List.cons(1, List.cons(2, List.nil(Nat)))) :=
      |  Protocol.Morphism.transport(cells, Keys, throughId, c2(Cell.one(1), Cell.one(2)), c1(Cell.two(1, 2)), fused)
      |
      |def fusedDerives : Protocol.Derives(Keys, List.cons(1, List.cons(2, List.nil(Nat))), List.nil(Nat)) :=
      |  Protocol.Morphism.derives(cells, Keys, footprint, c1(Cell.two(1, 2)), List.nil(Cell),
      |    Protocol.Derives.step(Protocol.Proto.mk(Cell, CellStep), c1(Cell.two(1, 2)), c2(Cell.one(1), Cell.one(2)), List.nil(Cell), List.nil(Cell), CellStep.part(1, 2),
      |      Protocol.Derives.step(Protocol.Proto.mk(Cell, CellStep), c1(Cell.one(1)), List.nil(Cell), c1(Cell.one(2)), List.nil(Cell), CellStep.free(1),
      |        Protocol.Derives.single(Protocol.Proto.mk(Cell, CellStep), c1(Cell.one(2)), List.nil(Cell), CellStep.free(2)))))
      |""".stripMargin
    )
  }

  test("the building blocks' theorems: Exclusive, and Track A's Shares theorems with their statements unchanged") {
    run(
    """
      |import Protocol.Exclusive
      |import Protocol.Shares
      |import Protocol.Nats
      |
      |def k3 : List(Nat) := List.cons(10, List.cons(20, List.cons(30, List.nil(Nat))))
      |
      |def k2 : List(Nat) := List.cons(10, List.cons(20, List.nil(Nat)))
      |
      |def nodup3 : List.Nodup(k3) :=
      |  Logic.both(Logic.both(Nat.lt_ne(10, 20, Eq.refl(Bool.true)), Logic.both(Nat.lt_ne(10, 30, Eq.refl(Bool.true)), True.intro)),
      |    Logic.both(Logic.both(Nat.lt_ne(20, 30, Eq.refl(Bool.true)), True.intro), Logic.both(True.intro, True.intro)))
      |
      |def held : Protocol.Valid(Exclusive.proto(Nat), k3, k2) :=
      |  Protocol.Valid.left(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), k3, k2, List.cons(30, List.nil(Nat)), Protocol.Valid.of_reach(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), k3, k3, Protocol.Reach.initial(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), k3)))
      |
      |def apart : Not(Eq(Nat, 10, 20)) := Exclusive.distinct(Nat, k3, 10, 20, held, nodup3)
      |
      |def initialKey : List.Mem(Nat, 20, k3) := Exclusive.within(Nat, k3, k2, held, nodup3, 20, List.Mem.tail(20, 10, List.cons(20, List.nil(Nat)), List.Mem.head(20, List.nil(Nat))))
      |
      |def onlyOnce (v: Protocol.Valid(Exclusive.proto(Nat), k3, List.cons(20, List.cons(20, List.nil(Nat))))): False :=
      |  Exclusive.not_twice(Nat, k3, 20, v, nodup3)
      |
      |// Shares: Track A's statements.
      |def bound (q: Nat)(r: Nat)(v: Protocol.Valid(Shares.proto, List.cons(5, List.nil(Nat)), List.cons(q, List.cons(r, List.nil(Nat))))): Nat.le(Nat.add(q, r), 5) :=
      |  Shares.pair_bound(5, q, r, v)
      |
      |def whole (q: Nat)(v: Protocol.Valid(Shares.proto, List.cons(5, List.nil(Nat)), List.cons(5, List.cons(q, List.nil(Nat))))): Eq(Nat, q, 0) :=
      |  Shares.whole_excl(5, q, v)
      |
      |def total (C: List(Nat))(r: Protocol.Reach(Shares.proto, List.cons(5, List.nil(Nat)), C)): Eq(Nat, Shares.total(C), 5) :=
      |  Shares.reach_total(List.cons(5, List.nil(Nat)), C, r)
      |""".stripMargin
    )
  }

  test("the support lemmas, the reordering lemmas and the bundled constructors apply to concrete lists") {
    run(
    """
      |import Protocol.Packets
      |import Protocol.Nats
      |
      |def l1 (a: Nat): List(Nat) := List.cons(a, List.nil(Nat))
      |def l2 (a: Nat)(b: Nat): List(Nat) := List.cons(a, l1(b))
      |def l3 (a: Nat)(b: Nat)(c: Nat): List(Nat) := List.cons(a, l2(b, c))
      |
      |inductive Swap indices (consumed: List(Nat))(produced: List(Nat)) : Prop
      | | swap (x: Nat)(y: Nat) : Swap(l2(x, y), l2(y, x))
      |
      |def swaps : Protocol.Proto := Protocol.Proto.mk(Nat, Swap)
      |
      |// Logic and Nats.
      |def fromFalse (h: False): Eq(Nat, 0, 1) := Logic.absurd(h, Eq(Nat, 0, 1))
      |
      |def belowZero (g: Nat)(h: Nat.lt(g, 0)): False := Nat.lt_zero(g, h, False)
      |
      |def widened : Nat.lt(2, 7) := Nat.lt_le(2, 5, 7, Eq.refl(Bool.true), Eq.refl(Bool.true))
      |
      |// Lists.
      |def appended : List.Perm(Nat, l2(1, 2), List.append(l1(1), l1(2))) :=
      |  List.Perm.of_eq(l2(1, 2), List.append(l1(1), l1(2)), Eq.refl(l2(1, 2)))
      |
      |def notInNil (a: Nat)(m: List.Mem(Nat, a, List.nil(Nat))): False := List.Mem.nil_absurd(a, m, False)
      |
      |def around (n: Nat): List(Nat) := l2(n, Nat.add(n, 1))
      |
      |def three : List.Mem(Nat, 3, List.flatMap(l2(1, 2), Nat, around)) :=
      |  List.flatMap.mem(Nat, Nat, around, l2(1, 2), 2, 3, List.Mem.tail(2, 1, l1(2), List.Mem.head(2, List.nil(Nat))),
      |    List.Mem.tail(3, 2, l1(3), List.Mem.head(3, List.nil(Nat))))
      |
      |// The invariant family: a unary part and a pair part.
      |def Pos (n: Nat): Prop := Nat.lt(0, n)
      |
      |def Any (a: Nat)(b: Nat): Prop := True
      |
      |def inv12 : List.Inv(l2(1, 2), Pos, List.Ne(Nat)) :=
      |  Logic.both(Logic.both(Eq.refl(Bool.true), Logic.both(Eq.refl(Bool.true), True.intro)),
      |    Logic.both(Logic.both(Nat.lt_ne(1, 2, Eq.refl(Bool.true)), True.intro), Logic.both(True.intro, True.intro)))
      |
      |def inv21 : List.Inv(l2(2, 1), Pos, List.Ne(Nat)) :=
      |  List.Inv.perm(Nat, Pos, List.Ne(Nat), fun (x: Nat)(y: Nat)(h: Not(Eq(Nat, x, y))): Not(Eq(Nat, y, x)) => List.Nodup.ne_symm(x, y, h),
      |    l2(1, 2), l2(2, 1), List.Perm.swap(Nat, 2, 1, List.nil(Nat)), inv12)
      |
      |def inv1 : List.Inv(l1(1), Pos, List.Ne(Nat)) := List.Inv.left(Nat, Pos, List.Ne(Nat), l1(1), l1(2), inv12)
      |
      |def any12 : List.Inv(l2(1, 2), Pos, Any) :=
      |  Logic.both(Logic.both(Eq.refl(Bool.true), Logic.both(Eq.refl(Bool.true), True.intro)),
      |    Logic.both(Logic.both(True.intro, True.intro), Logic.both(True.intro, True.intro)))
      |
      |// Replacing the 1 in front of the frame [2] by a 3.
      |def any32 : List.Inv(l2(3, 2), Pos, Any) :=
      |  List.Inv.framed(Nat, Pos, Any, l1(1), l1(3), l1(2), any12,
      |    fun (h: List.Inv(l1(1), Pos, Any)): List.Inv(l1(3), Pos, Any) =>
      |      Logic.both(Logic.both(Eq.refl(Bool.true), True.intro), Logic.both(True.intro, True.intro)),
      |    fun (h: List.Inv(l1(1), Pos, Any))(y: Nat)(e: List.Every(l1(1), List.into(Nat, Any, y))): List.Every(l1(3), List.into(Nat, Any, y)) =>
      |      Logic.both(True.intro, True.intro))
      |
      |// Each packet reordering's permutation lemma carries validity along.
      |def swappedValid (init: List(Nat))(A: List(Nat))(B: List(Nat))(v: Protocol.Valid(Protocol.Proto.mk(Nat, Swap), init, List.append(A, B))):
      |    Protocol.Valid(Protocol.Proto.mk(Nat, Swap), init, List.append(B, A)) :=
      |  Protocol.Valid.perm(Protocol.Proto.mk(Nat, Swap), init, List.append(A, B), List.append(B, A), v, Protocol.Toks.swap_perm(Nat, A, B))
      |
      |def exchangedValid (init: List(Nat))(A: List(Nat))(B: List(Nat))(C: List(Nat))
      |    (v: Protocol.Valid(Protocol.Proto.mk(Nat, Swap), init, List.append(A, List.append(B, C)))): Protocol.Valid(Protocol.Proto.mk(Nat, Swap), init, List.append(B, List.append(A, C))) :=
      |  Protocol.Valid.perm(Protocol.Proto.mk(Nat, Swap), init, List.append(A, List.append(B, C)), List.append(B, List.append(A, C)), v,
      |    Protocol.Toks.exchange_perm(Nat, A, B, C))
      |
      |// The bundled constructors.
      |def r0 : Protocol.Reach(swaps, l2(1, 2), l2(1, 2)) := Protocol.Reach.initial(swaps, l2(1, 2))
      |
      |def r1 : Protocol.Reach(swaps, l2(1, 2), l2(2, 1)) :=
      |  Protocol.Reach.perm(swaps, l2(1, 2), l2(1, 2), l2(2, 1), r0, List.Perm.swap(Nat, 2, 1, List.nil(Nat)))
      |
      |def v1 : Protocol.Valid(swaps, l2(1, 2), l1(2)) := Protocol.Valid.mk(swaps, l2(1, 2), l1(2), l1(1), r1)
      |
      |def d0 : Protocol.Derives(swaps, l2(1, 2), l2(1, 2)) := Protocol.Derives.refl(swaps, l2(1, 2))
      |
      |def d1 : Protocol.Derives(swaps, l2(1, 2), l2(2, 1)) :=
      |  Protocol.Derives.of_perm(swaps, l2(1, 2), l2(2, 1), List.Perm.swap(Nat, 2, 1, List.nil(Nat)))
      |
      |def d2 : Protocol.Derives(swaps, l3(1, 2, 3), l3(2, 1, 3)) :=
      |  Protocol.Derives.step(swaps, l2(1, 2), l2(2, 1), l1(3), l3(2, 1, 3), Swap.swap(1, 2), Protocol.Derives.refl(swaps, l3(2, 1, 3)))
      |
      |def d3 : Protocol.Derives(swaps, l2(2, 1), l2(2, 1)) :=
      |  Protocol.Derives.perm(swaps, l2(2, 1), l2(1, 2), l2(2, 1), List.Perm.swap(Nat, 1, 2, List.nil(Nat)), d1)
      |""".stripMargin
    )
  }

  test("an entry allocates, steps through library wrappers, observes and applies a library theorem") {
    val entry =
    """
      |import Protocol.Packets
      |import Protocol.Exclusive
      |import Protocol.Nats
      |
      |def l0 : List(Nat) := List.nil(Nat)
      |def l1 (a: Nat): List(Nat) := List.cons(a, l0)
      |def l2 (a: Nat)(b: Nat): List(Nat) := List.cons(a, l1(b))
      |def keys : List(Nat) := List.cons(10, l2(20, 30))
      |
      |def nodup : List.Nodup(keys) :=
      |  Logic.both(Logic.both(Nat.lt_ne(10, 20, Eq.refl(Bool.true)), Logic.both(Nat.lt_ne(10, 30, Eq.refl(Bool.true)), True.intro)),
      |    Logic.both(Logic.both(Nat.lt_ne(20, 30, Eq.refl(Bool.true)), True.intro), Logic.both(True.intro, True.intro)))
      |
      |// Allocate keys 10, 20 and 30; move 30 forward and release it in a framed step; observe the other two, keeping them, and
      |// learn from Exclusive that they are distinct; read the first key, release both, and return the sum of the keys read.
      |fun (sup: Protocol.Supply): Nat => {
      |  let (next, s, toks) := Protocol.new(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), keys, sup)
      |  let moved := Protocol.Toks.exchange(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), keys, s, l2(10, 20), l1(30), l0, toks)
      |  let rest := Protocol.Toks.stepFramed(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), keys, s, l1(30), l0, l2(10, 20), Exclusive.Step.drop(30), moved)
      |  let (kept, fact) := Protocol.Toks.inspect(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), keys, s, l2(10, 20), Not(Eq(Nat, 10, 20)),
      |    fun (v: Protocol.Valid(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), keys, l2(10, 20))): Not(Eq(Nat, 10, 20)) => Exclusive.distinct(Nat, keys, 10, 20, v, nodup), rest)
      |  let (apart) := fact
      |  let known : Not(Eq(Nat, 10, 20)) := apart
      |  match kept with
      |  | Protocol.Toks.cons a t C more => {
      |    let first := Protocol.step(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), keys, s, l1(a), l0, Exclusive.Step.drop(a),
      |      Protocol.Toks.cons(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), keys, s, a, t, l0, Protocol.Toks.nil(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), keys, s)))
      |    let second := Protocol.step(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), keys, s, C, l0, Exclusive.Step.drop(20), more)
      |    Nat.add(a, 20)
      |  }
      |}
      |""".stripMargin
    assertEquals(PrettyPrinter.print(run(entry).getOrElse(fail("Program has no body"))), "30")
  }

  test("a token-first wrapper returns Shares halves with their bound, and a framed step joins them after a swap") {
    run(
    """
      |import Protocol.Packets
      |import Protocol.Shares
      |
      |def l1 (a: Nat): List(Nat) := List.cons(a, List.nil(Nat))
      |def l2 (a: Nat)(b: Nat): List(Nat) := List.cons(a, l1(b))
      |
      |// Token-first: split the whole of 2 and return the halves with their joint bound.
      |def halves (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares.Step), l1(2)))(toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l1(2))):
      |    Prod(Protocol.Toks(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l2(1, 1)), Fact(Nat.le(Nat.add(1, 1), 2))) := {
      |  let parts := Protocol.step(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l1(2), l2(1, 1), Shares.split_one, toks)
      |  Protocol.Toks.inspect(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l2(1, 1), Nat.le(Nat.add(1, 1), 2),
      |    fun (v: Protocol.Valid(Protocol.Proto.mk(Nat, Shares.Step), l1(2), l2(1, 1))): Nat.le(Nat.add(1, 1), 2) => Shares.pair_bound(2, 1, 1, v), parts)
      |}
      |
      |// Joining the halves back through a framed step, after swapping them.
      |def rejoin (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares.Step), l1(2)))(toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l2(1, 1))):
      |    Protocol.Toks(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l1(2)) := {
      |  let swapped := Protocol.Toks.swap(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l1(1), l1(1), toks)
      |  Protocol.Toks.stepFramed(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l2(1, 1), l1(2), List.nil(Nat), Shares.Step.join(1, 1), swapped)
      |}
      |""".stripMargin
    )
  }

  test("packet operations keep affine use: a split packet used again is LinearReused, and a half may be dropped") {
    assertErrorAt[LinearReused](
    """
      |import Protocol.Packets
      |import Protocol.Shares
      |
      |def l1 (a: Nat): List(Nat) := List.cons(a, List.nil(Nat))
      |def l2 (a: Nat)(b: Nat): List(Nat) := List.cons(a, l1(b))
      |
      |def bad (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares.Step), l1(2)))(toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l2(1, 1))): Prod(Protocol.Toks(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l2(1, 1)), Protocol.Toks(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l2(1, 1))) := {
      |  let (a, b) := Protocol.Toks.split(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l1(1), l1(1), toks)
      |  Prod.mk(Protocol.Toks(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l2(1, 1)), Protocol.Toks(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l2(1, 1)),
      |    Protocol.Toks.append(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l1(1), l1(1), a, b), toks)
      |}
      |""".stripMargin,
      "toks",
      "toks)\n}"
    )
    run(
    """
      |import Protocol.Packets
      |import Protocol.Shares
      |
      |def l1 (a: Nat): List(Nat) := List.cons(a, List.nil(Nat))
      |def l2 (a: Nat)(b: Nat): List(Nat) := List.cons(a, l1(b))
      |
      |def firstHalf (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares.Step), l1(2)))(toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l2(1, 1))): Protocol.Toks(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l1(1)) := {
      |  let (a, b) := Protocol.Toks.split(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l1(1), l1(1), toks)
      |  a
      |}
      |""".stripMargin
    )
  }

  test("a fact about another packet, separate observations, and a reordered packet give no library theorem") {
    assertErrorAt[TypeMismatch](
    """
      |import Protocol.Packets
      |import Protocol.Shares
      |
      |def l1 (a: Nat): List(Nat) := List.cons(a, List.nil(Nat))
      |def l2 (a: Nat)(b: Nat): List(Nat) := List.cons(a, l1(b))
      |
      |def bad (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares.Step), l1(2)))(toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l2(1, 1))): Prod(Protocol.Toks(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l2(1, 1)), Fact(Nat.le(2, 2))) :=
      |  Protocol.Toks.inspect(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l2(1, 1), Nat.le(2, 2),
      |    fun (v: Protocol.Valid(Protocol.Proto.mk(Nat, Shares.Step), l1(2), l1(2))): Nat.le(2, 2) => Eq.refl(Bool.true), toks)
      |""".stripMargin,
      "(Protocol.Proto.mk(Nat, Shares.Step), l1(2), s, l2(1, 1), Nat.le(2, 2),\n    fun (v: Protocol.Valid(Protocol.Proto.mk(Nat, Shares.Step), l1(2), l1(2))): Nat.le(2, 2) => Eq.refl(Bool.true), toks)"
    )
    assertErrorAt[TypeMismatch](
    """
      |import Protocol.Exclusive
      |
      |def keys : List(Nat) := List.cons(10, List.cons(20, List.nil(Nat)))
      |
      |def bad (n: List.Nodup(keys))(va: Protocol.Valid(Exclusive.proto(Nat), keys, List.cons(10, List.nil(Nat))))
      |    (vb: Protocol.Valid(Exclusive.proto(Nat), keys, List.cons(20, List.nil(Nat)))): Not(Eq(Nat, 10, 20)) :=
      |  Exclusive.distinct(Nat, keys, 10, 20, va, n)
      |""".stripMargin,
      "(Nat, keys, 10, 20, va, n)"
    )
    assertErrorAt[TypeMismatch](
    """
      |import Protocol.Packets
      |import Protocol.Shares
      |
      |def l1 (a: Nat): List(Nat) := List.cons(a, List.nil(Nat))
      |def l2 (a: Nat)(b: Nat): List(Nat) := List.cons(a, l1(b))
      |
      |def bad (q: Nat)(v: Protocol.Valid(Shares.proto, l1(5), l2(q, 5))): Eq(Nat, q, 0) := Shares.whole_excl(5, q, v)
      |""".stripMargin,
      "(5, q, v)"
    )
  }

  test("a footprint that forgets a key is not a morphism into Exclusive") {
    assertErrorAt[TypeMismatch](
    """
      |import Protocol.Morphism
      |import Protocol.Exclusive
      |
      |// Cells own word keys; `fuse` and `part` keep the footprint, `free` releases it.
      |inductive Cell : Type
      | | one (k: Nat) : Cell
      | | two (a: Nat)(b: Nat) : Cell
      |
      |def c1 (x: Cell): List(Cell) := List.cons(x, List.nil(Cell))
      |def c2 (x: Cell)(y: Cell): List(Cell) := List.cons(x, c1(y))
      |
      |inductive CellStep indices (consumed: List(Cell))(produced: List(Cell)) : Prop
      | | fuse (a: Nat)(b: Nat) : CellStep(c2(Cell.one(a), Cell.one(b)), c1(Cell.two(a, b)))
      | | part (a: Nat)(b: Nat) : CellStep(c1(Cell.two(a, b)), c2(Cell.one(a), Cell.one(b)))
      | | free (k: Nat) : CellStep(c1(Cell.one(k)), List.nil(Cell))
      |
      |def cells : Protocol.Proto := Protocol.Proto.mk(Cell, CellStep)
      |
      |def Keys : Protocol.Proto := Exclusive.proto(Nat)
      |
      |def keys (x: Cell): List(Nat) := {
      |  match x returning List(Nat) with
      |  | Cell.one k => List.cons(k, List.nil(Nat))
      |  | Cell.two a b => List.cons(a, List.nil(Nat))
      |}
      |
      |// Each step's footprint is a permutation of its inputs', or a key release.
      |def keysSim (A: List(Cell))(B: List(Cell))(s: CellStep(A, B)):
      |    Protocol.Derives(Keys, List.flatMap(A, Nat, keys), List.flatMap(B, Nat, keys)) := {
      |  match s returning Protocol.Derives(Keys, List.flatMap(A, Nat, keys), List.flatMap(B, Nat, keys)) with
      |  | .fuse a b => Protocol.Derives.refl(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), List.flatMap(A, Nat, keys))
      |  | .part a b => Protocol.Derives.refl(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), List.flatMap(A, Nat, keys))
      |  | .free k => Protocol.Derives.single(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), List.cons(k, List.nil(Nat)), List.nil(Nat), Exclusive.Step.drop(k))
      |}
      |""".stripMargin,
      "(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), List.flatMap(A, Nat, keys))",
      "| .fuse a b => Protocol.Derives.refl(Protocol.Proto.mk(Nat, Exclusive.rel(Nat)), List.flatMap(A, Nat, keys))"
    )
  }
}
