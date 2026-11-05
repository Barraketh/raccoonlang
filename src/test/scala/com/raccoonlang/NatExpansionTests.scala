package com.raccoonlang

import com.raccoonlang.NatFixtures._
import com.raccoonlang.ProgramFixtures.Programs
import com.raccoonlang.Value._

/**
 * The kernel's `Nat.expand` and the prelude's `Nat.expand_eq` (docs/nat-normal-forms.md, "Expansion"). Expansion
 * multiplies every product of sums out and collects like terms, and never looks inside atoms. `Nat.expand` is the
 * identity on closed values and otherwise stuck on the expansion, so it expands again under substitution.
 * `Nat.expand_eq` proves that it preserves its argument, which makes distributivity, `Nat.mul_add`, a prelude theorem.
 * Default conversion still does not distribute.
 */
class NatExpansionTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs._

  private val span = Span(0, 0)
  private val one = constant(1)

  private def sameKey(left: Value, right: Value)(implicit loc: munit.Location): Unit = assertEquals(left.key, right.key)

  private def differentKey(left: Value, right: Value)(implicit loc: munit.Location): Unit =
    assertNotEquals(left.key, right.key)

  private def expansion(value: Value): Value = NatNormalForm.expansion(value)

  /** No numeral power of a sum, at any depth: the invariant of expanded forms. */
  private def distributed(value: Value): Boolean =
    value match {
      case poly: VNatPoly =>
        poly.form.terms.forall(_.monomial.factors.forall {
          case power: NatNormalForm.NumeralPower  => !power.base.isInstanceOf[VNatPoly]
          case power: NatNormalForm.SymbolicPower => distributed(power.base) && distributed(power.exponent)
        })
      case _ => true
    }

  /** The argument of a stuck `Nat.expand`, or none when `value` is not one. */
  private def stuckExpansion(value: Value): Option[Value] =
    value match {
      case VApp(head, Vector(argument), _, _) if head eq Kernel.expand => Some(argument)
      case _                                                           => None
    }

  /** A store that solves each variable as the given value. */
  private def solving(links: (Var, Value)*): EqStore =
    links.foldLeft(EqStore.empty.allow(DepSet(links.map(_._1.id): _*))) { case (store, (variable, value)) =>
      store.addLink(variable.id, value)
    }

  /** `Eq(Nat, lhs, rhs)` over `x`, `y` and `z`, proved by the expansions of both sides. */
  private def byExpansion(name: String, lhs: String, rhs: String): String =
    s"""def $name (x: Nat)(y: Nat)(z: Nat): Eq(Nat, $lhs, $rhs) :=
       |  Eq.trans(Nat.expand_eq($lhs), Eq.symm(Nat.expand_eq($rhs)))
       |""".stripMargin

  // ------------------------------------------------------------------------------------------------------------------
  // Expansion
  // ------------------------------------------------------------------------------------------------------------------

  test("expansion multiplies out products of sums and collects like terms") {
    val Vector(a, b, c, d) = Vector("a", "b", "c", "d").map(fresh)
    sameKey(expansion(mul(add(a, b), add(c, d))), sum(Vector(mul(a, c), mul(a, d), mul(b, c), mul(b, d))))
    sameKey(expansion(add(mul(a, add(b, c)), mul(a, b))), add(mul(constant(2), mul(a, b)), mul(a, c)))
    sameKey(expansion(mul(add(a, one), add(b, one))), sum(Vector(mul(a, b), a, b, one)))
    // (2a + 2b) * c is 2 * (a + b) * c in the normal forms, and 2ac + 2bc expanded.
    sameKey(
      expansion(mul(add(mul(constant(2), a), mul(constant(2), b)), c)),
      mul(constant(2), add(mul(a, c), mul(b, c)))
    )
    // A product of k sums of two atoms has 2^k terms, each with coefficient one.
    val expanded = expansion(product(Vector.tabulate(10)(index => add(fresh(s"x$index"), fresh(s"y$index")))))
    assertEquals(termCount(expanded), 1024)
    assert(form(expanded).terms.forall(_.coefficient == 1))
    assert(distributed(expanded))
  }

  test("nested sums multiply out at every level") {
    val Vector(a, b, c, d, e, f) = Vector("a", "b", "c", "d", "e", "f").map(fresh)
    sameKey(
      expansion(mul(a, add(mul(b, add(c, d)), e))),
      sum(Vector(mul(a, mul(b, c)), mul(a, mul(b, d)), mul(a, e)))
    )
    val nested = expansion(mul(add(mul(add(a, b), add(c, d)), e), add(f, one)))
    val products = Vector(mul(a, c), mul(a, d), mul(b, c), mul(b, d), e)
    sameKey(nested, add(sum(products.map(mul(_, f))), sum(products)))
    assert(distributed(nested))
    // A sum inside a sum factor inside a power.
    sameKey(expansion(pow(add(mul(a, add(b, one)), c), 2)), expansion(pow(add(add(mul(a, b), a), c), 2)))
  }

  test("powers of sums multiply out and agree with repeated products") {
    val Vector(a, b, c, d) = Vector("a", "b", "c", "d").map(fresh)
    sameKey(expansion(pow(add(a, b), 2)), sum(Vector(pow(a, 2), mul(constant(2), mul(a, b)), pow(b, 2))))
    sameKey(
      expansion(pow(add(a, one), 3)),
      sum(Vector(pow(a, 3), mul(constant(3), pow(a, 2)), mul(constant(3), a), one))
    )
    sameKey(expansion(pow(add(a, b), 3)), expansion(mul(add(a, b), mul(add(b, a), add(a, b)))))
    // (a + b + c + d)^4 has as many terms as monomials of degree four in four atoms: C(7, 3) = 35.
    assertEquals(termCount(expansion(pow(sum(Vector(a, b, c, d)), 4))), 35)
    // The power has more terms than the exponent, so an exponent beyond an Int is a representation limit.
    val huge = pow(add(a, b), BigInt(1) << 40)
    assertEquals(intercept[NatValueTooLarge](expansion(huge)).exponent, BigInt(1) << 40)
  }

  test("symbolic powers stay powers, of expanded bases to expanded exponents") {
    val Vector(a, b, c, d, e, f, x) = Vector("a", "b", "c", "d", "e", "f", "x").map(fresh)
    sameKey(expansion(pow(x, mul(a, add(b, c)))), pow(x, add(mul(a, b), mul(a, c))))
    sameKey(expansion(pow(mul(a, add(b, c)), e)), pow(add(mul(a, b), mul(a, c)), e))
    // Powers of bases that expand to the same form merge by the product law.
    val expandedBase = sum(Vector(mul(a, c), mul(a, d), mul(b, c), mul(b, d)))
    sameKey(expansion(mul(pow(mul(add(a, b), add(c, d)), e), pow(expandedBase, f))), pow(expandedBase, add(e, f)))
    // An exponent that gains a known part splits it off, and a sum base's numeral power multiplies out.
    sameKey(expansion(pow(x, mul(add(a, one), add(b, one)))), mul(x, pow(x, sum(Vector(mul(a, b), a, b)))))
    val power = pow(add(a, b), sum(Vector(mul(c, d), c, d)))
    sameKey(expansion(pow(add(a, b), mul(add(c, one), add(d, one)))), add(mul(a, power), mul(b, power)))
    // 0^((a + 1) * (b + 1)) is 0^(a*b + a + b + 1), which is zero, and so is every term it multiplies.
    val vanishing = pow(constant(0), mul(add(a, one), add(b, one)))
    assertEquals(termCount(vanishing), 1)
    sameKey(expansion(vanishing), Kernel.zeroValue)
    sameKey(expansion(add(x, mul(vanishing, add(c, d)))), x)
    // Expansion adds no exponent law: powers of products and powers of powers stay as they are.
    differentKey(expansion(pow(mul(x, a), e)), mul(pow(x, e), pow(a, e)))
    differentKey(expansion(pow(pow(x, a), e)), pow(x, mul(a, e)))
  }

  test("closed values, atoms and expanded forms are their own expansions") {
    val Vector(a, b, x) = Vector("a", "b", "x").map(fresh)
    for (
      value <- Vector(
        Kernel.zeroValue,
        one,
        constant(BigInt(10).pow(40)),
        x,
        sum(Vector(mul(a, b), a, constant(3))),
        pow(x, add(a, b)),
        pow(add(a, b), x),
        expansion(mul(add(a, b), add(x, constant(2))))
      )
    ) assert(expansion(value) eq value, PrettyPrinter.print(value))
    for (value <- Vector(Kernel.zeroValue, one, constant(BigInt(10).pow(40))))
      assert(NatNormalForm.expand(value) eq value)
    sameKey(NatNormalForm.expand(mul(add(constant(2), constant(3)), constant(4))), constant(20))
    run(
      """
        |def closed : Eq(Nat, Nat.expand(Nat.mul(Nat.add(2, 3), Nat.pow(10, 30))), Nat.mul(5, Nat.pow(10, 30))) :=
        |  Eq.refl(Nat.mul(5, Nat.pow(10, 30)))
        |def zero : Eq(Nat, Nat.expand(Nat.zero), 0) := Eq.refl(0)
        |""".stripMargin
    )
    assertEquals(result("{ Nat.expand(Nat.mul(Nat.add(2, 3), 4)) }"), "20")
  }

  test("atoms are opaque: stuck divisions, remainders and subtractions are not expanded inside") {
    val Vector(a, b, c, d, x) = Vector("a", "b", "c", "d", "x").map(fresh)
    val product = mul(x, add(a, one))
    for (
      atom <- Vector(
        NatNormalForm.div(product, constant(2)),
        NatNormalForm.mod(product, add(b, one)),
        NatNormalForm.sub(product, b)
      )
    ) {
      assert(expansion(atom) eq atom, PrettyPrinter.print(atom))
      sameKey(expansion(mul(atom, add(c, d))), add(mul(atom, c), mul(atom, d)))
    }
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Nat.expand
  // ------------------------------------------------------------------------------------------------------------------

  test("an open Nat.expand is a sum of stuck monomials and converts exactly when the expansions do") {
    val Vector(r, c, x) = Vector("r", "c", "x").map(fresh)
    val left = NatNormalForm.expand(mul(r, add(c, one)))
    val right = NatNormalForm.expand(add(mul(r, c), r))
    sameKey(left, right)
    // Each monomial of the expansion r*c + r is its own stuck application, which resumes when a dependency of it is
    // solved.
    val monomials = Vector(mul(r, c), r)
    val stuck = monomials.map(NatNormalForm.expand)
    stuck.zip(monomials).foreach { case (application, monomial) =>
      sameKey(stuckExpansion(application).getOrElse(fail(s"Expected a stuck expansion, got $application")), monomial)
      assertEquals(ReductionBlockers.of(application), monomial.synDeps)
      sameKey(application.tpe, Kernel.natType)
    }
    sameKey(left, add(stuck(0), stuck(1)))
    // A variable is stuck too: expand(x) is not x, which keeps expansion stable under substitution.
    sameKey(stuckExpansion(NatNormalForm.expand(x)).getOrElse(fail("Expected a stuck expansion")), x)
    differentKey(NatNormalForm.expand(x), x)
    // Default conversion does not distribute, and stuck monomials convert only with each other.
    assert(!ValueEquivalence.defEq(mul(r, add(c, one)), add(mul(r, c), r)))
    assert(!ValueEquivalence.defEq(left, add(mul(r, c), r)))
    assert(!ValueEquivalence.defEq(left, NatNormalForm.expand(add(mul(r, c), c))))
    // Coefficients and constants stay outside, so expansion is additive, a known successor shows, and subtraction and
    // comparisons cancel common monomials.
    val square = pow(add(r, c), 2)
    sameKey(NatNormalForm.expand(add(mul(r, add(c, one)), square)), add(left, NatNormalForm.expand(square)))
    sameKey(NatNormalForm.expand(mul(constant(3), square)), mul(constant(3), NatNormalForm.expand(square)))
    val successor = NatNormalForm.expand(mul(add(r, one), add(c, one)))
    assert(ConstructorValue.unapply(successor).exists(_._1.name == Kernel.SuccName), PrettyPrinter.print(successor))
    sameKey(NatNormalForm.sub(left, stuck(0)), stuck(1))
    sameKey(NatNormalForm.ble(stuck(0), left), Kernel.trueValue)
    sameKey(NatNormalForm.sub(add(left, constant(3)), right), constant(3))
  }

  test("an open Nat.expand resumes under substitution and expands the substituted argument") {
    val Vector(x, y, a, b) = Vector("x", "y", "a", "b").map(fresh)
    def resolved(value: Value, links: (Var, Value)*): Value = ValueOps.materialize(value, solving(links: _*))

    val stuck = NatNormalForm.expand(mul(x, y))
    // x := a + b: the normal forms keep (a + b) * y a product, and the resumed expansion multiplies it out.
    val resumed = resolved(stuck, x -> add(a, b))
    sameKey(resumed, NatNormalForm.expand(mul(add(a, b), y)))
    sameKey(resumed, add(NatNormalForm.expand(mul(a, y)), NatNormalForm.expand(mul(b, y))))
    sameKey(resolved(NatNormalForm.expand(x), x -> mul(a, add(b, one))), NatNormalForm.expand(add(mul(a, b), a)))
    // Solving every atom computes, inside forms too.
    sameKey(resolved(stuck, x -> constant(3), y -> constant(4)), constant(12))
    sameKey(resolved(add(stuck, x), x -> add(a, one), a -> constant(2), y -> constant(5)), constant(18))
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Nat.expand_eq and Nat.mul_add
  // ------------------------------------------------------------------------------------------------------------------

  test("Nat.expand_eq proves identities that default conversion does not decide") {
    run(
      """
        |def succStep (r: Nat)(c: Nat): Eq(Nat, Nat.mul(r, Nat.add(c, 1)), Nat.add(Nat.mul(r, c), r)) :=
        |  Eq.trans(Nat.expand_eq(Nat.mul(r, Nat.add(c, 1))), Eq.symm(Nat.expand_eq(Nat.add(Nat.mul(r, c), r))))
        |""".stripMargin +
        byExpansion(
          "square",
          "Nat.pow(Nat.add(x, y), 2)",
          "Nat.add(Nat.add(Nat.mul(x, x), Nat.mul(2, Nat.mul(x, y))), Nat.mul(y, y))"
        ) +
        byExpansion(
          "nested",
          "Nat.mul(Nat.add(Nat.mul(x, Nat.add(y, 1)), z), Nat.succ(y))",
          "Nat.add(Nat.add(Nat.mul(x, Nat.mul(y, y)), Nat.mul(2, Nat.mul(x, y))), Nat.add(x, Nat.add(Nat.mul(y, z), z)))"
        ) +
        byExpansion(
          "exponent",
          "Nat.pow(2, Nat.mul(x, Nat.add(y, 1)))",
          "Nat.mul(Nat.pow(2, Nat.mul(x, y)), Nat.pow(2, x))"
        ) +
        byExpansion(
          "base",
          "Nat.pow(Nat.mul(x, Nat.add(y, 1)), z)",
          "Nat.pow(Nat.add(Nat.mul(x, y), x), z)"
        )
    )
    for (
      invalid <- Vector(
        "def refl (r: Nat)(c: Nat): Eq(Nat, Nat.mul(r, Nat.add(c, 1)), Nat.add(Nat.mul(r, c), r)) := Eq.refl(Nat.mul(r, Nat.add(c, 1)))\n",
        byExpansion("wrong", "Nat.mul(x, Nat.add(y, 1))", "Nat.add(Nat.mul(x, y), 1)"),
        byExpansion("powerOfProduct", "Nat.pow(Nat.mul(x, y), z)", "Nat.mul(Nat.pow(x, z), Nat.pow(y, z))")
      )
    ) intercept[TypeMismatch](runChecked(invalid))
  }

  test("Nat.expand_eq does not reach inside atoms; congruence does") {
    run(
      """
        |def before (n: Nat): Nat := {
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => k
        |}
        |""".stripMargin +
        byExpansion(
          "matchAtom",
          "Nat.mul(before(x), Nat.add(y, 1))",
          "Nat.add(Nat.mul(before(x), y), before(x))"
        ) +
        byExpansion(
          "divisionAtom",
          "Nat.mul(Nat.div(x, 2), Nat.add(Nat.sub(y, z), 1))",
          "Nat.add(Nat.mul(Nat.div(x, 2), Nat.sub(y, z)), Nat.div(x, 2))"
        ) +
        """
          |def inside (x: Nat)(y: Nat): Eq(Nat, Nat.div(Nat.mul(x, Nat.add(y, 1)), 2), Nat.div(Nat.add(Nat.mul(x, y), x), 2)) :=
          |  congrArg(Nat.mul_add(x, y, 1), Nat, fun (n: Nat): Nat => Nat.div(n, 2))
          |""".stripMargin
    )
    intercept[TypeMismatch](
      runChecked(
        byExpansion("inside", "Nat.div(Nat.mul(x, Nat.add(y, 1)), 2)", "Nat.div(Nat.add(Nat.mul(x, y), x), 2)")
      )
    )
  }

  test("Nat.mul_add is a prelude theorem, not an axiom") {
    assert(!Interpreter.axioms(Prelude.default.core).exists(_.name == "Nat.mul_add"))
    val env = Interpreter.initialEnv(Prelude.default)
    env("Nat.mul_add") match {
      case VLam(_, _, LamBody.Core(_, _)) => ()
      case other                          => fail(s"Nat.mul_add is not a checked definition: $other")
    }
    // Its instances, and the exponent laws proved with it, check with no user axioms.
    run(
      """
        |def left (a: Nat)(b: Nat)(c: Nat): Eq(Nat, Nat.mul(a, Nat.add(b, c)), Nat.add(Nat.mul(a, b), Nat.mul(a, c))) := Nat.mul_add(a, b, c)
        |def right (a: Nat)(b: Nat)(c: Nat): Eq(Nat, Nat.mul(Nat.add(a, b), c), Nat.add(Nat.mul(a, c), Nat.mul(b, c))) := Nat.mul_add(c, a, b)
        |def succRight (a: Nat)(b: Nat): Eq(Nat, Nat.mul(a, Nat.succ(b)), Nat.add(Nat.mul(a, b), a)) := Nat.mul_add(a, b, 1)
        |def closed : Eq(Nat, Nat.mul(2, Nat.add(3, 4)), 14) := Nat.mul_add(2, 3, 4)
        |def powMul (x: Nat)(a: Nat)(b: Nat): Eq(Nat, Nat.pow(Nat.pow(x, a), b), Nat.pow(x, Nat.mul(a, b))) := Nat.pow_mul(x, a, b)
        |def mulPow (x: Nat)(y: Nat)(a: Nat): Eq(Nat, Nat.pow(Nat.mul(x, y), a), Nat.mul(Nat.pow(x, a), Nat.pow(y, a))) := Nat.mul_pow(x, y, a)
        |""".stripMargin
    )
  }

  test("Nat.expand is a kernel native and Nat.expand_eq a prelude builtin: neither can be redeclared or declared") {
    val bare = new Programs(Prelude.none, allowUserAxioms = false)
    assertEquals(bare.result("{ Nat.expand(Nat.mul(Nat.add(2, 3), 4)) }"), "20")
    for (prelude <- Vector(Prelude.none, Prelude.default))
      intercept[AlreadyDefined] {
        new Programs(prelude, allowUserAxioms = false)
          .runChecked("namespace Nat {\n  def expand (n: Nat): Nat := n\n}\n")
      }
    intercept[AlreadyDefined] {
      runChecked("namespace Nat {\n  def expand_eq (n: Nat): Eq(Nat, n, n) := Eq.refl(n)\n}\n")
    }
    // Without the bundled prelude, a program cannot assume the proof by declaring the builtin itself, whatever the
    // axiom policy.
    val declared = "namespace Nat {\n  def expand_eq (n: Nat): Eq(Nat, n, Nat.expand(n)) := builtin\n}\n"
    for (allowUserAxioms <- Vector(true, false))
      intercept[ProgramBuiltin](new Programs(Prelude.test, allowUserAxioms).runChecked(declared))
    // A custom prelude may declare it, as the bundled one does.
    val source =
      """inductive Eq (A: Sort($u)) indices (x: A)(y: A) : Prop
        | | refl (x: $A in Sort($u)) : Eq(A, x, x)
        |""".stripMargin + declared
    val custom = new Programs(Prelude.fromSource("custom prelude", source), allowUserAxioms = false)
    custom.run(
      """
        |def symmetric (a: Nat)(b: Nat): Eq(Nat, Nat.expand(Nat.mul(a, Nat.add(b, 1))), Nat.expand(Nat.add(Nat.mul(b, a), a))) :=
        |  Eq.refl(Nat.expand(Nat.mul(a, Nat.add(b, 1))))
        |def proof (a: Nat): Eq(Nat, Nat.mul(a, Nat.add(a, 1)), Nat.expand(Nat.add(Nat.pow(a, 2), a))) :=
        |  Nat.expand_eq(Nat.mul(a, Nat.add(a, 1)))
        |""".stripMargin
    )
    // Every native is a different function (`Builtins`), so conversion never opens them.
    val env = Interpreter.initialEnv(Prelude.default)
    for (other <- Vector("Nat.add", "Nat.mul", "Nat.pred", "Nat.div"))
      assert(!ValueEquivalence.defEq(env("Nat.expand"), env(other)), other)
  }

  test("Nat.expand in types is stable under refinement") {
    run(
      """
        |def refined (x: Nat)(y: Nat)(h: Eq(Nat, x, Nat.add(y, 1)))(p: Eq(Nat, Nat.expand(Nat.mul(x, x)), 4))
        |    : Eq(Nat, Nat.expand(Nat.add(Nat.add(Nat.mul(y, y), Nat.mul(2, y)), 1)), 4) := {
        |  match h returning Eq(Nat, Nat.expand(Nat.add(Nat.add(Nat.mul(y, y), Nat.mul(2, y)), 1)), 4) with
        |  | Eq.refl v => p
        |}
        |def byCases (n: Nat): Eq(Nat, Nat.expand(Nat.mul(n, Nat.add(n, 1))), Nat.expand(Nat.add(Nat.pow(n, 2), n))) := {
        |  match n returning Eq(Nat, Nat.expand(Nat.mul(n, Nat.add(n, 1))), Nat.expand(Nat.add(Nat.pow(n, 2), n))) with
        |  | Nat.zero => Eq.refl(0)
        |  | Nat.succ k => Eq.refl(Nat.expand(Nat.add(Nat.add(Nat.pow(k, 2), Nat.mul(3, k)), 2)))
        |}
        |inductive Vec (A: Type) indices (n: Nat) : Type
        | | nil {A: Type} : Vec(A, Nat.zero)
        | | cons {A: Type} (m: Nat)(tail: Vec(A, m)) (head: A) : Vec(A, Nat.succ(m))
        |def rows (r: Nat)(c: Nat)(v: Vec(Nat, Nat.expand(Nat.mul(r, Nat.add(c, 1))))): Vec(Nat, Nat.expand(Nat.add(Nat.mul(r, c), r))) := v
        |""".stripMargin
    )
  }

  test("comparisons cancel the stuck monomials of expansions, and Nat.expand_eq carries the result back") {
    run(
      """
        |def bound (r: Nat)(c: Nat): Nat.le(Nat.expand(Nat.mul(r, c)), Nat.expand(Nat.mul(r, Nat.add(c, 1)))) := Eq.refl(Bool.true)
        |def lifted (r: Nat)(c: Nat): Nat.le(Nat.mul(r, c), Nat.mul(r, Nat.add(c, 1))) :=
        |  Eq.substProp(
        |    Eq.symm(Nat.expand_eq(Nat.mul(r, Nat.add(c, 1)))),
        |    fun (z: Nat): Prop => Nat.le(Nat.mul(r, c), z),
        |    Eq.substProp(
        |      Eq.symm(Nat.expand_eq(Nat.mul(r, c))),
        |      fun (z: Nat): Prop => Nat.le(z, Nat.expand(Nat.mul(r, Nat.add(c, 1)))),
        |      bound(r, c)
        |    )
        |  )
        |def positive (a: Nat)(b: Nat): Nat.lt(0, Nat.expand(Nat.mul(Nat.add(a, 1), Nat.add(b, 1)))) := Eq.refl(Bool.true)
        |def additive (a: Nat)(b: Nat): Eq(Nat, Nat.expand(Nat.add(Nat.mul(a, Nat.add(b, 1)), Nat.pow(Nat.add(a, b), 2))), Nat.add(Nat.expand(Nat.add(Nat.mul(a, b), a)), Nat.expand(Nat.pow(Nat.add(b, a), 2)))) :=
        |  Eq.refl(Nat.expand(Nat.add(Nat.mul(a, Nat.add(b, 1)), Nat.pow(Nat.add(a, b), 2))))
        |""".stripMargin
    )
    // Without expansion, the bound is a product of a sum, which cancellation keeps opaque.
    intercept[TypeMismatch](
      runChecked("def bound (r: Nat)(c: Nat): Nat.le(Nat.mul(r, c), Nat.mul(r, Nat.add(c, 1))) := Eq.refl(Bool.true)\n")
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Display and quotation
  // ------------------------------------------------------------------------------------------------------------------

  test("a stuck expansion and its proof print and quote as calls of the natives, and round trip") {
    val x = VConst("x", Symbol, Kernel.natType)
    assertEquals(PrettyPrinter.print(NatNormalForm.expand(x)), "Nat.expand(x)")
    assertEquals(PrettyPrinter.print(NatNormalForm.expand(mul(constant(2), pow(x, 2)))), "2 * Nat.expand(x^2)")
    assert(
      Set("Nat.expand(x^2) + Nat.expand(x) + 1", "Nat.expand(x) + Nat.expand(x^2) + 1")
        .contains(PrettyPrinter.print(NatNormalForm.expand(add(mul(x, add(x, one)), one))))
    )

    val env = Interpreter.initialEnv(Prelude.default)
    val a = fresh("a")
    val b = fresh("b")
    val quoteEnv = env.putLocal(CoreAst.LocalRef(0, "a"), a).putLocal(CoreAst.LocalRef(1, "b"), b)
    val context = ValueQuote.quoteContext(quoteEnv)
    for (
      (value, captures) <- Vector(
        NatNormalForm.expand(a) -> 1,
        NatNormalForm.expand(mul(a, add(b, one))) -> 2,
        add(NatNormalForm.expand(pow(add(a, b), 2)), a) -> 2,
        Interpreter.evalApply(env("Nat.expand_eq"), Vector(mul(a, add(b, one)))) -> 2
      )
    ) {
      val residual = ValueQuote.quoteTerm(value, context, span)
      assertEquals(CapturedIndexes.getCapturedIndexes(residual, quoteEnv).getCardinality, captures)
      sameKey(Interpreter.evalTerm(residual, quoteEnv), value)
    }
  }
}
