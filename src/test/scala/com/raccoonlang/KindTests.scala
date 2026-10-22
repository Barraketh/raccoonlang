package com.raccoonlang

/** Kinds remain second-class sort parameters with their own syntax, normalization, and containment rules. */
class KindTests extends munit.FunSuite with TestSupport {
  test("kind parameters bind in declarations and families, but not function binders") {
    typecheckDecls("def keep {k: Kind}{A: Type { kind = k }}(x: A): A := x\n")
    typecheckDecls("inductive Box {k: Kind}(A: Type { kind = k }) : Type { kind = k }\n | mk (value: A) : Box(A)\n")

    expectOnly[NotAType](typecheckDecls("inductive Bad indices (k: Kind) : Type\n | mk : Bad(Kind.unr)\n"))
    expectOnly[NotAType](typecheckDecls("inductive Bad : Type\n | mk (k: Kind) : Bad\n"))
    expectOnly[NotAType](typecheckDecls("def bad (f: (k: Kind) -> Nat): Nat := 0\n"))
    expectOnly[NotAType](typecheckDecls("def bad : Nat := fun (k: Kind): Nat => 0\n"))
  }

  test("Kind is second-class and kind values only appear in sort fields") {
    typecheckDecls("def use (A: Type { kind = lin }): Type { kind = lin } := A\n")
    expectOnly[NotAType](typecheckDecls("def bad : Kind := Kind.lin\n"))
    expectOnly[NotAType](typecheckDecls("def bad (A: Type): Nat := List.length(List.cons(Kind.lin, List.nil(A)))\n"))
    expectOnly[TypeMismatch](typecheckDecls("def bad (A: Type { kind = lin })(x: A): Type := A\n"))
  }

  test("a kind expression must be applied with both operands") {
    assertEquals(
      expectOnly[ArityMismatch](typecheckDecls("def bad : Nat := Kind.join\n")),
      ArityMismatch(2, 0, ArityMismatch.Arguments)
    )
    assertEquals(
      expectOnly[ArityMismatch](typecheckDecls("def bad : Nat := Kind.join(Kind.unr)\n")),
      ArityMismatch(2, 1, ArityMismatch.Arguments)
    )
  }

  test("kind join is normalized at birth and retains its laws") {
    val laws =
      """
        |inductive K (k: Kind) : Type
        | | mk : K(k)
        |
        |def joinLin (k: Kind): Eq(Type, K(Kind.join(Kind.lin, k)), K(Kind.lin)) := Eq.refl(K(Kind.lin))
        |def joinUnr (k: Kind): Eq(Type, K(Kind.join(Kind.unr, k)), K(k)) := Eq.refl(K(k))
        |def joinComm (a: Kind)(b: Kind): Eq(Type, K(Kind.join(a, b)), K(Kind.join(b, a))) := Eq.refl(K(Kind.join(a, b)))
        |def joinAssoc (a: Kind)(b: Kind)(c: Kind):
        |  Eq(Type, K(Kind.join(a, Kind.join(b, c))), K(Kind.join(Kind.join(a, b), c))) :=
        |  Eq.refl(K(Kind.join(a, Kind.join(b, c))))
        |""".stripMargin
    typecheckDecls(laws)
    expectOnly[TypeMismatch](
      typecheckDecls(
        "inductive K (k: Kind) : Type\n | mk : K(k)\ndef bad : Eq(Type, K(Kind.unr), K(Kind.lin)) := Eq.refl(K(Kind.unr))\n"
      )
    )
    assertEquals(
      expectOnly[ArityMismatch](typecheckDecls("def bad : Nat := Kind.join(Kind.unr)\n")),
      ArityMismatch(2, 1, ArityMismatch.Arguments)
    )
  }

  test("sort kind containment and exact instance kinds are preserved") {
    val source =
      """
        |inductive Holder {k: Kind}(A: Type { kind = k }) : Type { kind = k }
        | | mk (held: A) : Holder(A)
        |
        |def linear : Type { kind = lin } := Holder({ kind = lin } Nat -> Nat)
        |def plain : Type := Holder(Nat)
        |""".stripMargin
    typecheckDecls(source)
    expectOnly[TypeMismatch](
      typecheckDecls(source.replace("def linear : Type { kind = lin }", "def linear : Type"))
    )
    val exceeded =
      expectOnly[KindExceeded](
        typecheckDecls("inductive Holder {k: Kind}(A: Type { kind = k }) : Type\n | mk (held: A) : Holder(A)\n")
      )
    assert(PartialFunction.cond(exceeded.part) { case ContainedPart.Field("Holder.mk.held", _) => true })
  }

  test("a kind variable is forced only when a field has exactly that kind") {
    typecheckDecls("def keep {k: Kind}{A: Type { kind = k }}(x: A): A := x\ndef use : Nat := keep(1)\n")
    expectOnly[NonForcedImplicitParam](
      typecheckDecls("def bad {k: Kind}(j: Kind)(A: Type { kind = join(k, j) })(x: A): A := x\n")
    )
    expectTypeError[TypeMismatch](
      "inductive K (k: Kind) : Type\n | mk : K(k)\n" +
        "def both {k: Kind}{A: Type { kind = k }}{B: Type { kind = k }}(x: A)(y: B): Pair(A, B) := (x, y)\n" +
        "def use (a: K(Kind.unr))(b: K(Kind.lin)): K(Kind.unr) := both(a, b)\n"
    )
  }

  test("equality refinement links a lone kind variable in a family instance") {
    typecheckDecls(
      """
        |inductive K (k: Kind) : Type
        | | mk : K(k)
        |
        |def toLin (k: Kind)(p: Eq(Type, K(k), K(Kind.lin)))(x: K(k)): K(Kind.lin) :=
        |  match p returning K(Kind.lin) with
        |  | .refl _ => x
        |""".stripMargin
    )
  }

  test("data sorts admit kind fields and Prop rejects them") {
    typecheckDecls("def keep (u: Level)(k: Kind)(A: Type { level = u, kind = k })(x: A): A := x\n")
    assert(LanguageParser.parseProgram("def bad (P: Prop { kind = lin }): Prop := P\n").isInstanceOf[Failure])
  }
}
