package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/**
 * The bundled prelude's lifetime polymorphism (spec §2.7, §7.3): its declarations take forced lifetime variables for
 * their type parameters' scopes, their type-family parameters' result sorts and their function-typed parameters'
 * closures, and it declares nothing linear and no sealed family. Its axioms are audited by the same walk, since only
 * the trusted prelude declares axioms.
 */
class PreludeLifetimeTests extends munit.FunSuite with TestSupport {

  /** A family scoped by its lifetime, and a consumer of it. */
  private val scoped =
    """
      |inductive W (l: Lifetime) : Type { scope = l }
      | | mk : W(l)
      |
      |def useW {l: Lifetime}(w: W(l)): Nat := 0
      |""".stripMargin

  private def withScoped(decls: String): String = scoped + "\n" + decls

  /**
   * The globals of a prelude that are sealed families, or whose types mention a kind other than Kind.unr (a sort's, a
   * closure's or a family instance's included), a kind variable, or an atom, walking every declaration's type, axioms
   * included, under fresh binders. Lifetime variables are admitted: `Quot` binds them.
   */
  private def nonconforming(prelude: Prelude.Config): Set[String] = {
    val env = prelude.checkedEnv

    def conformsSort(sort: VSort): Boolean = sort.kind.isUnr && !sort.scope.vars.intersects(Atoms.all)

    def conforms(v: Value): Boolean = {
      val classifier = v.tpe match {
        case sort: VSort => conformsSort(sort)
        case _           => true
      }
      classifier && (v match {
        case kind: Kind         => kind.isUnr
        case lifetime: Lifetime => !lifetime.vars.intersects(Atoms.all)
        case sort: VSort        => conformsSort(sort)
        case pi: VPi =>
          val fresh = BinderOps.freshen(pi)
          val binderTypes = pi.binders.map(binder => fresh(binder.localRef).tpe)
          pi.closureKind.isUnr && !pi.closureScope.vars.intersects(Atoms.all) &&
          !binderTypes.exists(_ eq KindTpe) && binderTypes.forall(conforms) && conforms(pi.codomain(fresh))
        case ConstSpine(_, args) => args.forall(conforms)
        case _                   => true
      })
    }

    def sealedFamily(v: Value): Boolean = v match {
      case VConst(_, Inductive(meta), _) => meta.seal.nonEmpty
      case _                             => false
    }

    env.globals.keys.filter(name => sealedFamily(env(name)) || !conforms(env(name).tpe)).toSet
  }

  test("the prelude declares nothing at a kind other than Kind.unr, no kind variable, only variable scopes, no seal") {
    assertEquals(nonconforming(Prelude.default), Set.empty[String])

    val linear =
      """
        |inductive Unit : Type
        | | unit : Unit
        |
        |inductive Tok : Type { kind = lin }
        | | mk : Tok
        |
        |def keep {k: Kind}{A: Type { kind = k }}(x: A): A := x
        |
        |def apply (f: { kind = lin } Unit -> Unit): Unit := f(Unit.unit)
        |
        |axiom eat {A: Type { kind = lin }}(x: A): Unit
        |
        |sealed inductive Permit : Prop
        | | mk : Permit
        |""".stripMargin
    assertEquals(
      nonconforming(Prelude.fromSource("linear", linear)),
      Set("Tok", "Tok.mk", "keep", "apply", "eat", "Permit")
    )
  }

  test("a prelude family instance is at the scope its arguments' types give it") {
    def program(sort: String, family: String): String =
      withScoped(s"def at (l: Lifetime)(m: Lifetime): $sort := $family\n")

    typecheckDecls(program("Type { scope = l }", "List(W(l))"))
    typecheckDecls(program("Type { scope = l }", "Option(W(l))"))
    typecheckDecls(program("Type { scope = union(l, m) }", "Prod(W(l), W(m))"))
    typecheckDecls(program("Type", "List(Nat)"))
    expectOnly[TypeMismatch](typecheckDecls(program("Type", "List(W(l))")))
    expectOnly[TypeMismatch](typecheckDecls(program("Type { scope = l }", "Prod(W(l), W(m))")))
  }

  test("an Eq over scoped values is at the matching Prop scope, and the lemmas apply at it") {
    def program(sort: String): String =
      withScoped(s"def at (l: Lifetime)(a: W(l))(b: W(l)): $sort := Eq(W(l), a, b)\n")

    typecheckDecls(program("Prop { scope = l }"))
    expectOnly[TypeMismatch](typecheckDecls(program("Prop")))
    typecheckDecls(
      withScoped(
        """
          |def flip (l: Lifetime)(a: W(l))(b: W(l))(p: Eq(W(l), a, b)): Eq(W(l), b, a) := Eq.symm(p)
          |
          |def back (l: Lifetime)(a: Prop { scope = l })(b: Prop { scope = l })(p: Eq(Prop { scope = l }, a, b))(h: b): a :=
          |  Eq.mpr(p, h)
          |""".stripMargin
      )
    )
  }

  test("a lambda capturing a scoped value forces List.map's closure-scope variable") {
    val lambda = "fun (n: Nat): Nat => Nat.add(n, useW(w))"
    def program(call: String): String =
      withScoped(
        s"""
           |def mapAt {A: Type}{B: Type}(xs: List(A))(f: A -> B): List(B) := List.map(xs, B, f)
           |
           |def tag (l: Lifetime)(w: W(l))(xs: List(Nat)): List(Nat) := $call
           |
           |{ scope l => List.length(tag(l, W.mk(l), List.cons(1, List.cons(2, List.nil(Nat))))) }
           |""".stripMargin
      )

    // The lambda captures `w: W(l)`, so its closure is `{ scope = l }`, which forces `Sf := l`.
    assert(ValueEquivalence.defEq(runProgram(program(s"List.map(xs, Nat, $lambda)")), runProgram("{ 2 }")))
    // A declaration without the variable accepts only closures at Lifetime.empty.
    expectOnly[TypeMismatch](typecheckDecls(program(s"mapAt(xs, $lambda)")))
  }

  test("a family's function-typed field closes over the family's scope") {
    def program(beq: String): String =
      withScoped(
        s"""
           |def wBEq (l: Lifetime)(w: W(l)): BEq(W(l)) := BEq.mk($beq)
           |
           |{
           |  scope l => {
           |    let w := W.mk(l)
           |    let ws := List.cons(w, List.cons(w, List.nil(W(l))))
           |    let refuted := Decidable.not(Decidable.isTrue(Eq.refl(w)))
           |    Bool.and(beq(listBEq(wBEq(l, w)), ws, ws), Bool.not(decide(refuted)))
           |  }
           |}
           |""".stripMargin
      )

    // The field's closure is `{ scope = l }`, so a lambda capturing `w: W(l)` fits it, `listBEq` builds one that
    // captures a `BEq(W(l))`, and `Decidable.not` one that captures a proof at `Prop { scope = l }`.
    val captures = "fun (a: W(l))(b: W(l)): Bool => Nat.beq(useW(w), useW(a))"
    assert(ValueEquivalence.defEq(runProgram(program(captures)), runProgram("{ Bool.true }")))
    typecheckDecls(program("fun { scope = l } (a: W(l))(b: W(l)): Bool => Bool.true"))
    // A lambda that captures nothing is at `Lifetime.empty`, and sorts are exact.
    expectOnly[TypeMismatch](typecheckDecls(program("fun (a: W(l))(b: W(l)): Bool => Bool.true")))
  }

  test("the quotient builtins locate their arguments by name at a scoped carrier") {
    val program =
      withScoped(
        """
          |{
          |  scope l => {
          |    let r := fun (a: W(l))(b: W(l)): Prop => True
          |    let q := Quot.mk(r, W.mk(l))
          |    let proof := Quot.ind(q, fun (x: Quot(W(l), r)): Prop => True, fun (a: W(l)): True => True.intro)
          |    Quot.lift(
          |      q,
          |      Nat,
          |      fun (w: W(l)): Nat => 7,
          |      fun (a: W(l))(b: W(l))(h: r(a, b)): Eq(Nat, 7, 7) => Eq.refl(7)
          |    )
          |  }
          |}
          |""".stripMargin
      )

    assert(ValueEquivalence.defEq(runProgram(program), runProgram("{ 7 }")))
  }
}
