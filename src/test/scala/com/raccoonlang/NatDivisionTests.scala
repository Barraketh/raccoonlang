package com.raccoonlang

import com.raccoonlang.NatFixtures._
import com.raccoonlang.ProgramFixtures.Programs
import com.raccoonlang.Value._

/**
 * The kernel's native `Nat.div` and `Nat.mod` (docs/nat-normal-forms.md, "Division and remainder"). Closed arguments
 * compute, with division by zero zero and modulus by zero the dividend; a divisor of zero or one, or a dividend of
 * zero, reduces an open application; every other open application is a stuck atom that resumes under substitution. No
 * law about them is definitional, and the prelude assumes none.
 *
 * ADVERSARIAL tests state claims that are false at some instance, so their acceptance would be a break. OVER-REJECTION
 * tests pin true claims that need a law. No break was found.
 */
class NatDivisionTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs._

  private val span = Span(0, 0)

  private def sameKey(left: Value, right: Value)(implicit loc: munit.Location): Unit = assertEquals(left.key, right.key)

  /** The arguments of a stuck application of `function`, or none when `value` is not one. */
  private def stuckOn(function: VLam, value: Value): Option[Vector[Value]] =
    value match {
      case VApp(head, args, _, _) if head eq function => Some(args)
      case _                                          => None
    }

  /** A store that solves each variable as the given value. */
  private def solving(links: (Var, Value)*): EqStore =
    links.foldLeft(EqStore.empty.allow(DepSet(links.map(_._1.id): _*))) { case (store, (variable, value)) =>
      store.addLink(variable.id, value)
    }

  /** Each `(lhs, rhs)` over `x` and `y` is not definitional: `Eq.refl(lhs)` does not prove it. */
  private def notDefinitional(equations: (String, String)*)(implicit loc: munit.Location): Unit =
    equations.foreach { case (lhs, rhs) =>
      intercept[TypeMismatch] {
        runChecked(s"def claim (x: Nat)(y: Nat): Eq(Nat, $lhs, $rhs) := Eq.refl($lhs)\n")
      }
    }

  private val vec =
    """
      |inductive Vec (A: Type) indices (n: Nat) : Type
      | | nil {A: Type} : Vec(A, Nat.zero)
      | | cons {A: Type} (m: Nat)(tail: Vec(A, m)) (head: A) : Vec(A, Nat.succ(m))
      |""".stripMargin

  // ------------------------------------------------------------------------------------------------------------------
  // Closed arguments
  // ------------------------------------------------------------------------------------------------------------------

  test("closed arguments compute on numbers of any size, with division by zero zero and modulus by zero the dividend") {
    val big = BigInt(2).pow(200) + 5
    val huge = BigInt(10).pow(1000) + 12345
    val pairs = Vector[(BigInt, BigInt)](
      (7, 2),
      (7, 0),
      (0, 0),
      (0, 5),
      (5, 7),
      (12, 4),
      (9, 1),
      (big, BigInt(2).pow(100)),
      (huge, 7),
      (huge, big),
      (big, huge),
      (huge, 0),
      (huge, huge)
    )
    pairs.foreach { case (a, b) =>
      sameKey(NatNormalForm.div(constant(a), constant(b)), constant(if (b == 0) 0 else a / b))
      sameKey(NatNormalForm.mod(constant(a), constant(b)), constant(if (b == 0) a else a % b))
    }
    run(
      """
        |def halves : Eq(Nat, Nat.div(7, 2), 3) := Eq.refl(3)
        |def odd : Eq(Nat, Nat.mod(7, 2), 1) := Eq.refl(1)
        |def byZero : Eq(Nat, Nat.div(7, 0), 0) := Eq.refl(0)
        |def modByZero : Eq(Nat, Nat.mod(7, 0), 7) := Eq.refl(7)
        |def zeroByZero : Eq(Nat, Nat.add(Nat.div(0, 0), Nat.mod(0, 0)), 0) := Eq.refl(0)
        |def powers : Eq(Nat, Nat.div(Nat.add(Nat.pow(2, 200), 5), Nat.pow(2, 100)), Nat.pow(2, 100)) := Eq.refl(Nat.pow(2, 100))
        |def lowBits : Eq(Nat, Nat.mod(Nat.add(Nat.pow(2, 200), 5), Nat.pow(2, 100)), 5) := Eq.refl(5)
        |def constructors : Eq(Nat, Nat.div(Nat.succ(Nat.succ(Nat.succ(Nat.zero))), Nat.succ(Nat.succ(Nat.zero))), Nat.succ(Nat.zero)) := Eq.refl(1)
        |""".stripMargin
    )
    assertEquals(result("{ Nat.div(Nat.pow(10, 40), 3) }"), "3" * 40)
    assertEquals(result("{ Nat.mod(Nat.pow(10, 40), 3) }"), "1")
  }

  test("division and remainder are kernel natives: present without a prelude and never redeclared") {
    val bare = new Programs(Prelude.none, allowUserAxioms = false)
    assertEquals(bare.result("{ Nat.add(Nat.div(7, 2), Nat.mod(7, 2)) }"), "4")
    for (prelude <- Vector(Prelude.none, Prelude.default); name <- Vector("div", "mod"))
      intercept[AlreadyDefined] {
        new Programs(prelude, allowUserAxioms = false)
          .runChecked(s"namespace Nat {\n  def $name (a: Nat)(b: Nat): Nat := a\n}\n")
      }
    // Every native is a different function (`Builtins`), so conversion never opens them.
    val env = Interpreter.initialEnv(Prelude.default)
    for (other <- Vector("Nat.mod", "Nat.sub", "Nat.mul", "Nat.pow"))
      assert(!ValueEquivalence.defEq(env("Nat.div"), env(other)), other)
    assert(!ValueEquivalence.defEq(env("Nat.mod"), env("Nat.sub")))
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Open applications
  // ------------------------------------------------------------------------------------------------------------------

  test("an open application is a stuck atom that converts with itself and by congruence") {
    val n = fresh("n")
    val m = fresh("m")
    for ((function, operation) <- Vector(Kernel.div -> NatNormalForm.div _, Kernel.mod -> NatNormalForm.mod _))
      for ((a, b) <- Vector((n, constant(4)), (n, m), (constant(5), m), (add(n, constant(1)), constant(2)))) {
        val result = operation(a, b)
        val args = stuckOn(function, result).getOrElse(fail(s"Expected a stuck application, got $result"))
        sameKey(args(0), a)
        sameKey(args(1), b)
        sameKey(operation(a, b), result)
        sameKey(result.tpe, Kernel.natType)
        // It resumes when a dependency of either argument is solved.
        assertEquals(ReductionBlockers.of(result), a.synDeps ++ b.synDeps)
      }
    assert(!ValueEquivalence.defEq(NatNormalForm.div(n, constant(4)), NatNormalForm.mod(n, constant(4))))
    assert(!ValueEquivalence.defEq(NatNormalForm.div(n, m), NatNormalForm.div(m, n)))
    // An atom of the normal forms: it rearranges, collects coefficients, and cancels.
    val quotient = NatNormalForm.div(n, constant(4))
    sameKey(add(quotient, n), add(n, quotient))
    sameKey(add(quotient, quotient), mul(constant(2), quotient))
    sameKey(NatNormalForm.sub(add(quotient, constant(3)), quotient), constant(3))
    run(
      """
        |def same (x: Nat): Eq(Nat, Nat.div(x, 4), Nat.div(x, 4)) := Eq.refl(Nat.div(x, 4))
        |def congruent (a: Nat)(b: Nat)(c: Nat): Eq(Nat, Nat.mod(Nat.add(a, Nat.succ(b)), c), Nat.mod(Nat.succ(Nat.add(b, a)), c)) :=
        |  Eq.refl(Nat.mod(Nat.add(a, Nat.succ(b)), c))
        |def collected (x: Nat): Eq(Nat, Nat.add(Nat.div(x, 4), Nat.mul(2, Nat.div(x, 4))), Nat.mul(Nat.div(x, 4), 3)) :=
        |  Eq.refl(Nat.mul(3, Nat.div(x, 4)))
        |def nested (x: Nat): Eq(Nat, Nat.mod(Nat.div(x, 8), 64), Nat.mod(Nat.div(Nat.add(x, 0), 8), 64)) := Eq.refl(Nat.mod(Nat.div(x, 8), 64))
        |""".stripMargin
    )
    notDefinitional(
      "Nat.div(x, 4)" -> "Nat.mod(x, 4)",
      "Nat.div(x, y)" -> "Nat.div(y, x)",
      "Nat.div(x, 2)" -> "Nat.div(x, 4)",
      "Nat.mod(Nat.div(x, 2), 3)" -> "Nat.div(Nat.mod(x, 2), 3)"
    )
  }

  test("a divisor of zero or one, or a dividend of zero, reduces an open application") {
    val n = fresh("n")
    val m = fresh("m")
    for (a <- Vector(n, add(mul(n, m), constant(3)), NatNormalForm.div(n, m))) {
      sameKey(NatNormalForm.div(a, Kernel.zeroValue), Kernel.zeroValue)
      assert(NatNormalForm.mod(a, Kernel.zeroValue) eq a)
      assert(NatNormalForm.div(a, constant(1)) eq a)
      sameKey(NatNormalForm.mod(a, constant(1)), Kernel.zeroValue)
      sameKey(NatNormalForm.div(Kernel.zeroValue, a), Kernel.zeroValue)
      sameKey(NatNormalForm.mod(Kernel.zeroValue, a), Kernel.zeroValue)
    }
    run(
      """
        |def divZero (a: Nat): Eq(Nat, Nat.div(a, 0), 0) := Eq.refl(0)
        |def modZero (a: Nat): Eq(Nat, Nat.mod(a, Nat.zero), a) := Eq.refl(a)
        |def divOne (a: Nat)(b: Nat): Eq(Nat, Nat.div(Nat.mul(a, b), Nat.succ(Nat.zero)), Nat.mul(b, a)) := Eq.refl(Nat.mul(a, b))
        |def modOne (a: Nat): Eq(Nat, Nat.mod(a, 1), 0) := Eq.refl(0)
        |def zeroDiv (b: Nat): Eq(Nat, Nat.div(0, b), 0) := Eq.refl(0)
        |def zeroMod (b: Nat): Eq(Nat, Nat.mod(Nat.sub(b, b), b), 0) := Eq.refl(0)
        |def computedOne (a: Nat)(b: Nat): Eq(Nat, Nat.div(a, Nat.sub(Nat.add(b, 1), b)), a) := Eq.refl(a)
        |""".stripMargin
    )
    // At every other numeral the result depends on the other argument's value, so these stay stuck. So do the valid
    // identities that need the other argument's structure, which the design leaves out.
    for (
      (function, result) <- Vector(
        Kernel.div -> NatNormalForm.div(n, constant(2)),
        Kernel.div -> NatNormalForm.div(constant(1), m),
        Kernel.mod -> NatNormalForm.mod(n, constant(2)),
        Kernel.mod -> NatNormalForm.mod(constant(1), m),
        Kernel.div -> NatNormalForm.div(n, add(m, constant(1))),
        Kernel.mod -> NatNormalForm.mod(n, n),
        Kernel.div -> NatNormalForm.div(mul(constant(4), n), constant(4)),
        Kernel.mod -> NatNormalForm.mod(add(mul(constant(4), n), constant(1)), constant(4)),
        Kernel.div -> NatNormalForm.div(NatNormalForm.div(n, constant(2)), constant(2))
      )
    ) assert(stuckOn(function, result).isDefined, PrettyPrinter.print(result))
  }

  test("an open application resumes when its arguments are solved, and reduces once its result is fixed") {
    val n = fresh("n")
    val m = fresh("m")
    val k = fresh("k")
    val quotient = NatNormalForm.div(n, m)
    val remainder = NatNormalForm.mod(n, m)
    def resolved(value: Value, links: (Var, Value)*): Value = ValueOps.materialize(value, solving(links: _*))

    sameKey(resolved(quotient, n -> constant(10), m -> constant(4)), constant(2))
    sameKey(resolved(remainder, n -> constant(10), m -> constant(4)), constant(2))
    // A divisor solved as zero or one, or a dividend solved as zero, reduces whatever the other argument is.
    sameKey(resolved(quotient, m -> Kernel.zeroValue), Kernel.zeroValue)
    sameKey(resolved(remainder, m -> Kernel.zeroValue), n)
    sameKey(resolved(quotient, m -> constant(1)), n)
    sameKey(resolved(remainder, m -> constant(1)), Kernel.zeroValue)
    sameKey(resolved(quotient, n -> Kernel.zeroValue), Kernel.zeroValue)
    sameKey(resolved(remainder, n -> Kernel.zeroValue), Kernel.zeroValue)
    // An open solution keeps it stuck, on the solved arguments; solving those as well computes, transitively.
    sameKey(resolved(quotient, n -> add(k, constant(8))), NatNormalForm.div(add(k, constant(8)), m))
    sameKey(resolved(quotient, n -> add(k, constant(8)), k -> constant(2), m -> constant(5)), constant(2))
    // Inside forms and nested applications: mod(div(n, 4), 3) + 2 * mod(n, m) at n := 100, m := 7.
    val nested = add(NatNormalForm.mod(NatNormalForm.div(n, constant(4)), constant(3)), mul(constant(2), remainder))
    sameKey(resolved(nested, n -> constant(100), m -> constant(7)), constant(1 + 2 * 2))
    run(
      """
        |def refined (x: Nat)(h: Eq(Nat, x, 10)): Eq(Nat, Nat.add(Nat.div(x, 4), Nat.mod(x, 4)), 4) := {
        |  match h returning Eq(Nat, Nat.add(Nat.div(x, 4), Nat.mod(x, 4)), 4) with
        |  | Eq.refl v => Eq.refl(4)
        |}
        |def byDivisor (a: Nat)(b: Nat)(h: Eq(Nat, b, 0)): Eq(Nat, Nat.mod(a, b), a) := {
        |  match h returning Eq(Nat, Nat.mod(a, b), a) with
        |  | Eq.refl v => Eq.refl(a)
        |}
        |def byCases (n: Nat): Eq(Nat, Nat.div(Nat.mul(n, 8), 4), Nat.div(Nat.mul(8, n), 4)) := {
        |  match n returning Eq(Nat, Nat.div(Nat.mul(n, 8), 4), Nat.div(Nat.mul(8, n), 4)) with
        |  | Nat.zero => Eq.refl(0)
        |  | Nat.succ k => Eq.refl(Nat.div(Nat.add(Nat.mul(8, k), 8), 4))
        |}
        |def atTen : Eq(Nat, Nat.add(Nat.div(10, 4), Nat.mod(10, 4)), 4) := refined(10, Eq.refl(10))
        |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Matching, refinement, types, comparisons, and termination
  // ------------------------------------------------------------------------------------------------------------------

  test("a match on an open result waits with every case, and refinement treats the result as an atom") {
    run(
      """
        |def parity (x: Nat): Nat := {
        |  match Nat.mod(x, 2) returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => 1
        |}
        |def named (x: Nat)(y: Nat)(h: Eq(Nat, Nat.div(x, 4), y)): Eq(Nat, Nat.succ(y), Nat.add(Nat.div(x, 4), 1)) := {
        |  match h returning Eq(Nat, Nat.succ(y), Nat.add(Nat.div(x, 4), 1)) with
        |  | Eq.refl v => Eq.refl(Nat.succ(y))
        |}
        |def closedCase : Nat := {
        |  match Nat.mod(7, 2) returning Nat with
        |  | Nat.succ k => k
        |}
        |def byZeroIsZero (x: Nat)(h: Eq(Nat, Nat.div(x, 0), 1)): False := {
        |  match h returning False with
        |}
        |def closedApart (h: Eq(Nat, Nat.div(7, 2), 2)): False := {
        |  match h returning False with
        |}
        |""".stripMargin
    )
    assertEquals(
      result(
        """
          |def parity (x: Nat): Nat := {
          |  match Nat.mod(x, 2) returning Nat with
          |  | Nat.zero => 0
          |  | Nat.succ k => 1
          |}
          |{ Nat.add(parity(7), parity(10)) }
          |""".stripMargin
      ),
      "1"
    )
    intercept[MissingCase] {
      runChecked("def half (x: Nat): Nat := {\n  match Nat.mod(x, 2) returning Nat with\n  | Nat.zero => 0\n}\n")
    }
  }

  test("ADVERSARIAL refinement neither inverts division nor refutes a satisfiable equation") {
    // x = 2, y = 3: div(x, 2) = div(y, 2), and x is not y. The case refines nothing, so its body fails.
    intercept[TypeMismatch] {
      runChecked(
        """
          |def inverts (x: Nat)(y: Nat)(h: Eq(Nat, Nat.div(x, 2), Nat.div(y, 2))): Eq(Nat, x, y) := {
          |  match h returning Eq(Nat, x, y) with
          |  | Eq.refl v => Eq.refl(x)
          |}
          |""".stripMargin
      )
    }
    // x = 4: mod(x, 4) = 0, and x is not 0.
    intercept[TypeMismatch] {
      runChecked(
        """
          |def inverts (x: Nat)(h: Eq(Nat, Nat.mod(x, 4), 0)): Eq(Nat, x, 0) := {
          |  match h returning Eq(Nat, x, 0) with
          |  | Eq.refl v => Eq.refl(x)
          |}
          |""".stripMargin
      )
    }
    // Each equation holds at some instance, so no match may omit its case: x = 6, x = 0, x = 0.
    for (
      equation <- Vector(
        "Eq(Nat, Nat.div(x, 2), 3)",
        "Eq(Nat, Nat.mod(x, 0), 0)",
        "Eq(Nat, Nat.div(Nat.succ(x), 2), 0)"
      )
    )
      intercept[MissingCase] {
        runChecked(s"def refutes (x: Nat)(h: $equation): False := {\n  match h returning False with\n}\n")
      }
  }

  test("open and closed applications inside types") {
    run(
      vec +
        """
          |def keep (n: Nat)(v: Vec(Nat, Nat.div(n, 4))): Vec(Nat, Nat.div(n, 4)) := v
          |def closed (v: Vec(Nat, Nat.div(9, 4))): Vec(Nat, 2) := v
          |def reduced (n: Nat)(v: Vec(Nat, Nat.mod(n, 1))): Vec(Nat, Nat.zero) := v
          |def onlyNil (n: Nat)(v: Vec(Nat, Nat.mod(n, 1))): Nat := {
          |  match v returning Nat with
          |  | Vec.nil => 0
          |}
          |def grow (n: Nat)(v: Vec(Nat, Nat.div(n, 4)))(x: Nat): Vec(Nat, Nat.add(Nat.div(n, 4), 1)) := Vec.cons(Nat, Nat.div(n, 4), v, x)
          |
          |inductive Box indices (n: Nat) : Type
          | | mk (n: Nat) : Box(n)
          |
          |inductive Wrap (n: Nat)(m: Nat) : Type
          | | mk {n: Nat}{m: Nat} (b: Box(Nat.div(n, m)))(c: Box(Nat.mod(n, m))) : Wrap(n, m)
          |""".stripMargin
    )
    intercept[TypeMismatch](runChecked(vec + "def lost (n: Nat)(v: Vec(Nat, Nat.div(n, 4))): Vec(Nat, n) := v\n"))
  }

  test("comparisons decide by cancelling the atoms, and no bound is definitional") {
    run(
      """
        |def bounded (x: Nat): Nat.le(Nat.div(x, 4), Nat.add(Nat.div(x, 4), 3)) := Eq.refl(Bool.true)
        |def below (x: Nat)(y: Nat): Nat.lt(Nat.mod(x, y), Nat.add(Nat.mod(x, y), Nat.succ(y))) := Eq.refl(Bool.true)
        |def irrefl (x: Nat)(h: Nat.lt(Nat.mod(x, 4), Nat.mod(x, 4))): False := {
        |  match h returning False with
        |}
        |def same (x: Nat): Eq(Bool, Nat.beq(Nat.div(x, 4), Nat.div(x, 4)), Bool.true) := Eq.refl(Bool.true)
        |def apart (x: Nat): Eq(Bool, Nat.beq(Nat.succ(Nat.div(x, 4)), Nat.div(x, 4)), Bool.false) := Eq.refl(Bool.false)
        |def wrapped : Nat.lt(Nat.mod(4294967297, 4294967296), 2) := Eq.refl(Bool.true)
        |def byOne (x: Nat): Nat.lt(Nat.mod(x, 1), 1) := Eq.refl(Bool.true)
        |""".stripMargin
    )
    // OVER-REJECTION: each bound holds but needs a law, which is neither definitional nor assumed.
    for (claim <- Vector("Nat.lt(Nat.mod(x, 4), 4)", "Nat.le(Nat.div(x, 4), x)", "Nat.le(Nat.mod(x, 4), x)"))
      intercept[TypeMismatch](runChecked(s"def bound (x: Nat): $claim := Eq.refl(Bool.true)\n"))
  }

  test("measures over division and remainder compare them as atoms") {
    assertEquals(
      result(
        """
          |def count (n: Nat)(k: Nat): Nat decreases measure(Nat.add(Nat.div(n, 4), k)) := {
          |  match k returning Nat with
          |  | Nat.zero => Nat.mod(n, 4)
          |  | Nat.succ j => count(n, j)
          |}
          |{ count(10, 3) }
          |""".stripMargin
      ),
      "2"
    )
    def refused(src: String)(implicit loc: munit.Location): Unit =
      intercept[NonDecreasingRecursiveCall](runChecked(src))
    // div(n, 1) = n and mod(n, 0) = n: each loops at every argument.
    refused("def f (n: Nat): Nat decreases measure(n) := f(Nat.div(n, 1))\n")
    refused("def f (n: Nat): Nat decreases measure(n) := f(Nat.mod(n, 0))\n")
    // div(n + 1, 2) and div(n, 2) are unrelated atoms; loops at every argument.
    refused("def f (n: Nat): Nat decreases measure(Nat.div(n, 2)) := f(Nat.succ(n))\n")
    // OVER-REJECTION: div(k + 1, 2) < k + 1 holds, but needs a law.
    refused(
      """
        |def bits (n: Nat): Nat decreases measure(n) := {
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => Nat.succ(bits(Nat.div(n, 2)))
        |}
        |""".stripMargin
    )
    refused("def f (n: Nat): Nat decreases structural(n) := f(Nat.div(n, 2))\n")
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Laws
  // ------------------------------------------------------------------------------------------------------------------

  test("the reductions agree with the division law and the remainder bound, which are not definitional") {
    run(
      """
        |def lawByZero (a: Nat): Eq(Nat, a, Nat.add(Nat.mul(0, Nat.div(a, 0)), Nat.mod(a, 0))) := Eq.refl(a)
        |def lawByOne (a: Nat): Eq(Nat, a, Nat.add(Nat.mul(1, Nat.div(a, 1)), Nat.mod(a, 1))) := Eq.refl(a)
        |def lawOfZero (b: Nat): Eq(Nat, 0, Nat.add(Nat.mul(b, Nat.div(0, b)), Nat.mod(0, b))) := Eq.refl(0)
        |def lawClosed : Eq(Nat, Nat.add(Nat.pow(10, 50), 7), Nat.add(Nat.mul(97, Nat.div(Nat.add(Nat.pow(10, 50), 7), 97)), Nat.mod(Nat.add(Nat.pow(10, 50), 7), 97))) :=
        |  Eq.refl(Nat.add(Nat.pow(10, 50), 7))
        |def boundByOne (a: Nat): Nat.lt(Nat.mod(a, 1), 1) := Eq.refl(Bool.true)
        |def boundOfZero (k: Nat): Nat.lt(Nat.mod(0, Nat.succ(k)), Nat.succ(k)) := Eq.refl(Bool.true)
        |""".stripMargin
    )
    // OVER-REJECTION: at a symbolic divisor the law relates stuck atoms, which no reduction does; nor is the GPU
    // prelude's source definition of the remainder definitional.
    notDefinitional(
      "x" -> "Nat.add(Nat.mul(y, Nat.div(x, y)), Nat.mod(x, y))",
      "Nat.mod(x, y)" -> "Nat.sub(x, Nat.mul(Nat.div(x, y), y))",
      "Nat.mod(x, x)" -> "0"
    )
  }

  test(
    "ADVERSARIAL with the laws as user axioms, the conventions satisfy the guarded bound and refute the unguarded one"
  ) {
    val axioms = new Programs(Prelude.default, allowUserAxioms = true)
    // The division law holds at a zero divisor by reduction alone, and the guarded bound is vacuous there.
    axioms.run(
      """
        |axiom divMod (a: Nat)(b: Nat): Eq(Nat, a, Nat.add(Nat.mul(b, Nat.div(a, b)), Nat.mod(a, b)))
        |axiom modLt (a: Nat)(b: Nat)(h: Nat.lt(0, b)): Nat.lt(Nat.mod(a, b), b)
        |def atZero (a: Nat): Eq(Nat, a, a) := divMod(a, 0)
        |def vacuous (a: Nat)(h: Nat.lt(0, 0)): Nat.lt(a, 0) := modLt(a, 0, h)
        |def word (offset: Nat): Nat.lt(Nat.mod(offset, 4), 4) := modLt(offset, 4, Eq.refl(Bool.true))
        |""".stripMargin
    )
    // Without the guard, `mod(a, 0) = a` makes the bound at zero `a < 0`, which is false.
    axioms.run(
      """
        |axiom modLtUnguarded (a: Nat)(b: Nat): Nat.lt(Nat.mod(a, b), b)
        |def inconsistent : False := Nat.lt_zero(0, modLtUnguarded(0, 0), False)
        |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Display, quotation, and a sample in the style of the GPU sources
  // ------------------------------------------------------------------------------------------------------------------

  test("stuck applications print and quote as calls of the natives, and round trip") {
    val x = VConst("x", Symbol, Kernel.natType)
    assertEquals(PrettyPrinter.print(NatNormalForm.div(x, constant(4))), "Nat.div(x, 4)")
    assertEquals(PrettyPrinter.print(add(NatNormalForm.mod(x, constant(4)), constant(1))), "Nat.mod(x, 4) + 1")

    val env = Interpreter.initialEnv(Prelude.default)
    val a = fresh("a")
    val b = fresh("b")
    val quoteEnv = env.putLocal(CoreAst.LocalRef(0, "a"), a).putLocal(CoreAst.LocalRef(1, "b"), b)
    val context = ValueQuote.quoteContext(quoteEnv)
    for (
      (value, captures) <- Vector(
        NatNormalForm.div(a, b) -> 2,
        add(NatNormalForm.mod(mul(a, b), constant(7)), a) -> 2,
        NatNormalForm.div(NatNormalForm.mod(a, constant(262144)), constant(16)) -> 1
      )
    ) {
      val residual = ValueQuote.quoteTerm(value, context, span)
      assertEquals(CapturedIndexes.getCapturedIndexes(residual, quoteEnv).getCardinality, captures)
      sameKey(Interpreter.evalTerm(residual, quoteEnv), value)
    }
  }

  test("a sample in the style of the GPU sources: u32 wraparound and word offsets") {
    run(
      """
        |def u32Limit : Nat := 4294967296
        |
        |inductive Word : Type
        | | mk (location: Nat)(value: Nat) : Word
        |
        |def wordValue (w: Word): Nat := {
        |  match w returning Nat with
        |  | Word.mk location value => value
        |}
        |
        |def rows (base: Nat)(value: Nat)(count: Nat): List(Word) decreases structural(count) := {
        |  match count returning List(Word) with
        |  | Nat.zero => List.nil(Word)
        |  | Nat.succ n => List.cons(Word.mk(base, Nat.mod(value, u32Limit)), rows(Nat.succ(base), Nat.succ(value), n))
        |}
        |
        |def nth (ws: List(Word))(lane: Nat): Nat decreases structural(ws) := {
        |  match ws returning Nat with
        |  | List.nil => 0
        |  | List.cons w rest => {
        |    match lane returning Nat with
        |    | Nat.zero => wordValue(w)
        |    | Nat.succ l => nth(rest, l)
        |  }
        |}
        |
        |// The value of every active lane, by induction, with the wrapped values as stuck atoms.
        |def valueAt (base: Nat)(value: Nat)(count: Nat)(lane: Nat)(active: Nat.lt(lane, count)):
        |    Eq(Nat, nth(rows(base, value, count), lane), Nat.mod(Nat.add(value, lane), u32Limit)) decreases structural(count) := {
        |  match count returning Eq(Nat, nth(rows(base, value, count), lane), Nat.mod(Nat.add(value, lane), u32Limit)) with
        |  | Nat.zero => Nat.lt_zero(lane, active, Eq(Nat, 0, Nat.mod(Nat.add(value, lane), u32Limit)))
        |  | Nat.succ n => {
        |    match lane returning Eq(Nat, nth(rows(base, value, Nat.succ(n)), lane), Nat.mod(Nat.add(value, lane), u32Limit)) with
        |    | Nat.zero => Eq.refl(Nat.mod(value, u32Limit))
        |    | Nat.succ l => valueAt(Nat.succ(base), Nat.succ(value), n, l, active)
        |  }
        |}
        |
        |def lanes (lane: Nat)(active: Nat.lt(lane, 32)): Eq(Nat, nth(rows(0, 100, 32), lane), Nat.mod(Nat.add(100, lane), u32Limit)) :=
        |  valueAt(0, 100, 32, lane, active)
        |def wraps : Eq(Nat, nth(rows(0, 4294967294, 4), 3), 1) := Eq.refl(1)
        |def product : Eq(Nat, Nat.mod(Nat.mul(65536, 65537), u32Limit), 65536) := Eq.refl(65536)
        |
        |inductive Command : Type
        | | issue (word: Nat) : Command
        | | unsupported : Command
        |
        |def decode (offset: Nat): Command :=
        |  Bool.cond(Nat.beq(Nat.mod(offset, 4), 0), Command, Command.issue(Nat.div(offset, 4)), Command.unsupported)
        |
        |// An aligned offset decodes to its word, by rewriting the stuck alignment test.
        |def decodeIssue (offset: Nat)(aligned: Eq(Nat, Nat.mod(offset, 4), 0)):
        |    Eq(Command, decode(offset), Command.issue(Nat.div(offset, 4))) :=
        |  congrArg(congrArg(aligned, Bool, fun (n: Nat): Bool => Nat.beq(n, 0)), Command,
        |    fun (flag: Bool): Command => Bool.cond(flag, Command, Command.issue(Nat.div(offset, 4)), Command.unsupported))
        |
        |def aligned : Eq(Command, decode(4096), Command.issue(1024)) := decodeIssue(4096, Eq.refl(0))
        |def misaligned : Eq(Command, decode(4098), Command.unsupported) := Eq.refl(Command.unsupported)
        |
        |// A shared-memory descriptor field: the low 18 bits of a byte address, shifted right by 4.
        |def encode (bytes: Nat): Nat := Nat.div(Nat.mod(bytes, 262144), 16)
        |def encoded : Eq(Nat, encode(Nat.add(262144, 1024)), 64) := Eq.refl(64)
        |""".stripMargin
    )
    // Without the alignment premise the decoder stays stuck on the test.
    intercept[TypeMismatch] {
      runChecked(
        """
          |inductive Command : Type
          | | issue (word: Nat) : Command
          | | unsupported : Command
          |def decode (offset: Nat): Command :=
          |  Bool.cond(Nat.beq(Nat.mod(offset, 4), 0), Command, Command.issue(Nat.div(offset, 4)), Command.unsupported)
          |def unaligned (offset: Nat): Eq(Command, decode(offset), Command.issue(Nat.div(offset, 4))) := Eq.refl(decode(offset))
          |""".stripMargin
      )
    }
  }
}
