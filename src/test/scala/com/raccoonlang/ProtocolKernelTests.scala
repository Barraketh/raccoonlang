package com.raccoonlang

import com.raccoonlang.ProgramFixtures._

/**
 * The kernel's resource-protocol mathematics (docs/kernel.md, "Resource protocols"): `List.Perm`, `Protocol.Proto`,
 * `Protocol.Reach` and `Protocol.Valid`. Every program runs without user axioms.
 */
class ProtocolKernelTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.test, allowUserAxioms = false)
  import programs._

  private def typeError[T <: TypeError](src: String)(implicit ct: reflect.ClassTag[T]): T =
    intercept[T](runChecked(src))

  private val swapProtocol =
    """
      |inductive Swap indices (consumed: List(Nat))(produced: List(Nat)) : Prop
      | | swap (x: Nat)(y: Nat) : Swap(List.cons(x, List.cons(y, List.nil(Nat))), List.cons(y, List.cons(x, List.nil(Nat))))
      |""".stripMargin

  test("kernel protocol declarations are present without a prelude") {
    new Programs(Prelude.none, allowUserAxioms = false).run(
      swapProtocol +
        """
          |def swaps : Protocol.Proto := Protocol.Proto.mk(Nat, Swap)
          |
          |def validOfReach (init: List(Nat))(C: List(Nat))(r: Protocol.Reach(Protocol.Proto.mk(Nat, Swap), init, C)):
          |    Protocol.Valid(Protocol.Proto.mk(Nat, Swap), init, C) :=
          |  Protocol.Valid.mk(Protocol.Proto.mk(Nat, Swap), init, C, List.nil(Nat), r)
          |
          |def swapped (x: Nat)(y: Nat): List.Perm(Nat, List.cons(y, List.cons(x, List.nil(Nat))), List.cons(x, List.cons(y, List.nil(Nat)))) :=
          |  List.Perm.swap(Nat, x, y, List.nil(Nat))
          |""".stripMargin
    )
  }

  test("reachability induction proves a conservation law through framed steps and permutations") {
    run(
      swapProtocol +
        """
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
          |""".stripMargin
    )
  }

  test("kernel protocol declarations cannot be redeclared") {
    typeError[AlreadyDefined](
      """
        |namespace Protocol {
        |  inductive Reach : Prop
        |}
        |""".stripMargin
    )
    typeError[AlreadyDefined](
      """
        |namespace List {
        |  def Perm : Nat := Nat.zero
        |}
        |""".stripMargin
    )
  }
}
