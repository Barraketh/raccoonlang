package com.raccoonlang

import com.raccoonlang.Value._

/** Source programs and kernel integration for native Nat arithmetic and comparisons. */
class NatNormalFormProgramTests extends munit.FunSuite {
  private def program(source: String, prelude: Prelude.Config = Prelude.default): Option[Value] =
    LanguageParser.parseProgram(source) match {
      case Success(parsed, _, _) =>
        Interpreter.run(Elaborator.elab(parsed, prelude), prelude)
      case failure: Failure => fail(s"Failed to parse: $failure")
    }

  private def value(source: String): Value = program(source).getOrElse(fail("Missing result"))

  private val constants =
    """
      |def z: Nat := Nat.zero
      |def o: Nat := Nat.succ(z)
      |def t: Nat := Nat.succ(o)
      |""".stripMargin

  private val convertibleAtoms =
    """
      |axiom observe (f: Nat -> Nat): Nat
      |def first: Nat := observe(fun (n: Nat): Nat => n)
      |def second: Nat := observe(fun (m: Nat): Nat => m)
      |def sameAtom: Eq(Nat, first, second) := Eq.refl(first)
      |""".stripMargin

  test("associativity, commutativity, units, and numeral laws check by reflexivity") {
    program(
      constants +
        """
          |def comm (a: Nat)(b: Nat): Eq(Nat, Nat.add(a, b), Nat.add(b, a)) := Eq.refl(Nat.add(a, b))
          |def assoc (a: Nat)(b: Nat)(c: Nat): Eq(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c))) := Eq.refl(Nat.add(a, Nat.add(b, c)))
          |def prod (a: Nat)(b: Nat): Eq(Nat, Nat.mul(a, b), Nat.mul(b, a)) := Eq.refl(Nat.mul(a, b))
          |def prodAssoc (a: Nat)(b: Nat)(c: Nat): Eq(Nat, Nat.mul(Nat.mul(a, b), c), Nat.mul(a, Nat.mul(b, c))) := Eq.refl(Nat.mul(a, Nat.mul(b, c)))
          |def sums (a: Nat)(b: Nat)(c: Nat): Eq(Nat, Nat.mul(Nat.add(a, b), c), Nat.mul(c, Nat.add(b, a))) := Eq.refl(Nat.mul(c, Nat.add(b, a)))
          |def coeff (a: Nat): Eq(Nat, Nat.add(a, a), Nat.mul(t, a)) := Eq.refl(Nat.add(a, a))
          |def numeral (a: Nat)(b: Nat): Eq(Nat, Nat.mul(t, Nat.add(a, b)), Nat.add(Nat.add(a, b), Nat.add(b, a))) := Eq.refl(Nat.mul(t, Nat.add(a, b)))
          |def square (a: Nat)(b: Nat): Eq(Nat, Nat.pow(Nat.add(a, b), t), Nat.mul(Nat.add(b, a), Nat.add(a, b))) := Eq.refl(Nat.pow(Nat.add(a, b), t))
          |def units (a: Nat): Eq(Nat, Nat.add(Nat.mul(a, o), Nat.mul(a, z)), a) := Eq.refl(a)
          |""".stripMargin
    )
  }

  test("symbolic distributivity is not definitional") {
    for (
      equation <- Vector(
        "Eq(Nat, Nat.mul(a, Nat.add(b, c)), Nat.add(Nat.mul(a, b), Nat.mul(a, c)))",
        "Eq(Nat, Nat.mul(a, Nat.succ(b)), Nat.add(Nat.mul(a, b), a))",
        "Eq(Nat, Nat.pow(Nat.add(a, b), Nat.succ(Nat.succ(Nat.zero))), Nat.add(Nat.add(Nat.mul(a, a), Nat.mul(Nat.succ(Nat.succ(Nat.zero)), Nat.mul(a, b))), Nat.mul(b, b)))"
      )
    )
      intercept[TypeMismatch] {
        program(s"def invalid (a: Nat)(b: Nat)(c: Nat): $equation := Eq.refl(Nat.mul(a, Nat.add(b, c)))")
      }
  }

  test("Nat.mul_add proves distributivity and its instances by conversion") {
    program(
      constants +
        """
          |def left (a: Nat)(b: Nat)(c: Nat): Eq(Nat, Nat.mul(a, Nat.add(b, c)), Nat.add(Nat.mul(a, b), Nat.mul(a, c))) := Nat.mul_add(a, b, c)
          |def right (a: Nat)(b: Nat)(c: Nat): Eq(Nat, Nat.mul(Nat.add(a, b), c), Nat.add(Nat.mul(a, c), Nat.mul(b, c))) := Nat.mul_add(c, a, b)
          |def succRight (a: Nat)(b: Nat): Eq(Nat, Nat.mul(a, Nat.succ(b)), Nat.add(Nat.mul(a, b), a)) := Nat.mul_add(a, b, o)
          |def succLeft (a: Nat)(b: Nat): Eq(Nat, Nat.mul(Nat.succ(a), b), Nat.add(Nat.mul(a, b), b)) := Nat.mul_add(b, a, o)
          |def scaled (a: Nat)(b: Nat)(c: Nat): Eq(Nat, Nat.mul(Nat.mul(t, a), Nat.add(b, c)), Nat.add(Nat.mul(t, Nat.mul(a, b)), Nat.mul(a, Nat.mul(t, c)))) := Nat.mul_add(Nat.mul(a, t), c, b)
          |""".stripMargin
    )
  }
  test("conversion aligns different-key convertible atoms, including inside sum factors") {
    program(
      constants + convertibleAtoms +
        """
          |axiom h: Nat
          |axiom k: Nat
          |def collect: Eq(Nat, Nat.add(first, second), Nat.mul(t, first)) := Eq.refl(Nat.add(first, second))
          |def factors: Eq(Nat, Nat.mul(first, second), Nat.pow(first, t)) := Eq.refl(Nat.mul(first, second))
          |def nested: Eq(Nat, Nat.mul(Nat.add(first, second), Nat.add(second, first)), Nat.mul(Nat.mul(t, t), Nat.mul(first, first))) := Eq.refl(Nat.mul(Nat.add(first, second), Nat.add(second, first)))
          |def inside: Eq(Nat, Nat.mul(Nat.add(first, k), h), Nat.mul(h, Nat.add(k, second))) := Eq.refl(Nat.mul(Nat.add(first, k), h))
          |def content: Eq(Nat, Nat.mul(Nat.add(first, second), h), Nat.mul(t, Nat.mul(first, h))) := Eq.refl(Nat.mul(t, Nat.mul(first, h)))
          |def merged: Eq(Nat, Nat.mul(Nat.add(first, k), Nat.add(k, second)), Nat.pow(Nat.add(k, first), t)) := Eq.refl(Nat.pow(Nat.add(k, first), t))
          |""".stripMargin
    )
    intercept[TypeMismatch] {
      program(
        convertibleAtoms +
          """
            |axiom h: Nat
            |axiom k: Nat
            |def invalid: Eq(Nat, Nat.mul(Nat.add(first, k), h), Nat.add(Nat.mul(second, h), Nat.mul(k, h))) := Eq.refl(Nat.mul(Nat.add(first, k), h))
            |""".stripMargin
      )
    }
  }
  test("subtraction and comparisons cancel different-key convertible atoms and monomials") {
    program(
      constants + convertibleAtoms +
        """
          |def cancel: Eq(Nat, Nat.sub(first, second), z) := Eq.refl(z)
          |def cancelReverse: Eq(Nat, Nat.sub(second, first), z) := Eq.refl(z)
          |def partial (extra: Nat): Eq(Nat, Nat.sub(Nat.add(first, extra), second), extra) := Eq.refl(extra)
          |def collect: Eq(Nat, Nat.sub(Nat.add(first, second), first), first) := Eq.refl(first)
          |def factors: Eq(Nat, Nat.sub(Nat.mul(first, second), Nat.pow(first, t)), z) := Eq.refl(z)
          |def collectedFactors: Eq(Nat, Nat.sub(Nat.add(Nat.mul(first, first), Nat.mul(first, second)), Nat.pow(second, t)), Nat.pow(first, t)) := Eq.refl(Nat.pow(first, t))
          |def equal: Eq(Bool, Nat.beq(first, second), Bool.true) := Eq.refl(Bool.true)
          |def sameOrder: Eq(Bool, Nat.ble(first, second), Bool.true) := Eq.refl(Bool.true)
          |def unequal: Eq(Bool, Nat.beq(Nat.succ(first), second), Bool.false) := Eq.refl(Bool.false)
          |def greater: Eq(Bool, Nat.ble(Nat.succ(first), second), Bool.false) := Eq.refl(Bool.false)
          |def smaller: Eq(Bool, Nat.ble(first, Nat.succ(second)), Bool.true) := Eq.refl(Bool.true)
          |def absorb (extra: Nat): Eq(Nat, Nat.pred(Nat.sub(Nat.add(first, extra), second)), Nat.pred(extra)) := Eq.refl(Nat.pred(extra))
          |""".stripMargin
    )
  }

  test("stuck Boolean equality converts in either operand orientation") {
    val first = value(convertibleAtoms + "{ first }")
    val second = value(convertibleAtoms + "{ second }")
    val unrelated = NatFixtures.fresh("unrelated")
    assertNotEquals(first.key, second.key)
    assert(ValueEquivalence.defEq(first, second))

    // Equivalent atoms can sort on opposite sides of an unrelated atom. Exercise both residual orientations directly
    // so this regression does not depend on the incidental hash order of fresh syntax ids.
    val left = VBlockedApp(Kernel.beq, Vector(first, unrelated), Kernel.boolType, unrelated.synDeps)
    val right = VBlockedApp(Kernel.beq, Vector(unrelated, second), Kernel.boolType, unrelated.synDeps)
    assert(ValueEquivalence.defEq(left, right))
    assert(ValueEquivalence.defEq(right, left))
    val other = NatFixtures.fresh("other")
    assert(!ValueEquivalence.defEq(left, NatNormalForm.beq(second, other)))
    assert(!ValueEquivalence.defEq(left, NatNormalForm.ble(second, unrelated)))
    assert(!ValueEquivalence.defEq(NatNormalForm.ble(first, unrelated), NatNormalForm.ble(unrelated, second)))

    program(
      convertibleAtoms +
        """
          |axiom unrelated: Nat
          |def compare: Eq(Bool, Nat.beq(first, unrelated), Nat.beq(second, unrelated)) := Eq.refl(Nat.beq(first, unrelated))
          |""".stripMargin
    )
  }

  test("cancellation aligns convertible atoms inside sum factors and keeps the factors opaque") {
    program(
      constants + convertibleAtoms +
        """
          |axiom h: Nat
          |axiom k: Nat
          |def cancel: Eq(Nat, Nat.sub(Nat.add(Nat.mul(Nat.add(first, k), h), t), Nat.mul(h, Nat.add(k, second))), t) := Eq.refl(t)
          |def compare: Eq(Bool, Nat.ble(Nat.mul(Nat.add(first, k), h), Nat.add(Nat.mul(Nat.add(second, k), h), o)), Bool.true) := Eq.refl(Bool.true)
          |def stuck: Eq(Nat, Nat.sub(Nat.mul(Nat.add(first, k), h), Nat.mul(second, h)), Nat.sub(Nat.mul(h, Nat.add(k, second)), Nat.mul(first, h))) := Eq.refl(Nat.sub(Nat.mul(Nat.add(first, k), h), Nat.mul(first, h)))
          |""".stripMargin
    )
    // Cancelling second * h against (first + k) * h would need distributivity.
    intercept[TypeMismatch] {
      program(
        convertibleAtoms +
          """
            |axiom h: Nat
            |axiom k: Nat
            |def invalid: Eq(Nat, Nat.sub(Nat.mul(Nat.add(first, k), h), Nat.mul(second, h)), Nat.mul(k, h)) := Eq.refl(Nat.mul(k, h))
            |""".stripMargin
      )
    }
  }
  test("equal symbolic remainders cancel directly") {
    val first = value(convertibleAtoms + "{ first }")
    val second = value(convertibleAtoms + "{ second }")
    val sum = NatNormalForm.add(first, second)
    val successor = NatNormalForm.successor(sum)
    assertEquals(NatNormalForm.sub(sum, sum).key, Kernel.zeroValue.key)
    assertEquals(NatNormalForm.sub(successor, sum).key, NatNormalForm.literal(1).key)
    assertEquals(NatNormalForm.sub(sum, successor).key, Kernel.zeroValue.key)
    assertEquals(NatNormalForm.beq(sum, sum).key, Kernel.trueValue.key)
    assertEquals(NatNormalForm.beq(sum, successor).key, Kernel.falseValue.key)
    assertEquals(NatNormalForm.ble(sum, successor).key, Kernel.trueValue.key)
    assertEquals(NatNormalForm.ble(successor, sum).key, Kernel.falseValue.key)
  }
  test("unequal form constants and coefficients fail conversion normally") {
    intercept[TypeMismatch] {
      program(constants + "def invalid: Eq(Nat, Nat.add(o, o), Nat.add(t, o)) := Eq.refl(t)")
    }
    intercept[TypeMismatch] {
      program(constants + "def invalid (n: Nat): Eq(Nat, Nat.add(n, n), n) := Eq.refl(n)")
    }
    intercept[TypeMismatch] {
      program(convertibleAtoms + "def invalid: Eq(Nat, Nat.add(first, first), first) := Eq.refl(first)")
    }
  }

  test("a symbolic coefficient mismatch cannot justify excluding an equality constructor") {
    intercept[MissingCase] {
      program(
        """
          |def invalid (n: Nat)(h: Eq(Nat, Nat.add(n, n), n)): False := {
          | match h returning False with
          |}
          |""".stripMargin
      )
    }
  }

  test("known constant part exposes successors for source predecessor and Boolean comparison") {
    program(
      constants +
        """
          |def peel (a: Nat)(b: Nat): Eq(Nat, Nat.pred(Nat.add(Nat.add(a, b), o)), Nat.add(a, b)) := Eq.refl(Nat.add(a, b))
          |def positive (a: Nat)(b: Nat): Eq(Bool, Nat.isZero(Nat.add(o, Nat.mul(a, b))), Bool.false) := Eq.refl(Bool.false)
          |def subtract (a: Nat)(b: Nat): Eq(Nat, Nat.sub(Nat.add(Nat.add(a, b), t), t), Nat.add(a, b)) := Eq.refl(Nat.add(a, b))
          |""".stripMargin
    )
  }

  test("a blocked arithmetic match resumes when only the second factor becomes zero") {
    val classify = value(
      """
        |def classify (a: Nat)(b: Nat): Nat := {
        | match Nat.mul(a, b) returning Nat with
        | | Nat.zero => Nat.zero
        | | Nat.succ p => Nat.succ(Nat.zero)
        |}
        |{ classify }
        |""".stripMargin
    )
    val env = Interpreter.initialEnv()
    val a = FreshVar.freshVar("a", env("Nat"))
    val b = FreshVar.freshVar("b", env("Nat"))
    val zero = Interpreter.evalTerm(ElabAst.Term.GlobalRef("Nat.zero", Span(0, 0)), env)
    val stuck = Interpreter.evalApply(classify, Vector(a, b))
    assert(stuck.synDeps.contains(a.id) && stuck.synDeps.contains(b.id))
    val store = EqStore.empty.allow(DepSet(b.id)).addLink(b.id, zero)
    val resumed = ValueOps.materialize(stuck, store)
    assert(ValueEquivalence.defEq(resumed, zero), s"Match did not resume: $resumed")
  }

  test("dependent constructor indices accept reordered and regrouped arithmetic") {
    program(
      """
        |inductive Sized indices (n: Nat): Type
        | | mk (n: Nat): Sized(n)
        |
        |def reorder (a: Nat)(b: Nat)(item: Sized(Nat.add(a, b))): Sized(Nat.add(b, a)) := item
        |def regroup (a: Nat)(b: Nat)(c: Nat)(item: Sized(Nat.mul(a, Nat.mul(Nat.add(b, c), a)))): Sized(Nat.mul(Nat.pow(a, Nat.succ(Nat.succ(Nat.zero))), Nat.add(c, b))) := item
        |""".stripMargin
    )
  }

  test("refinement substitutes a sum into an already normalized product as a factor") {
    program(
      """
        |def substitute (n: Nat)(m: Nat)(a: Nat)(b: Nat)(h: Eq(Nat, n, Nat.add(a, b))): Eq(Nat, Nat.add(Nat.mul(n, m), n), Nat.add(Nat.mul(m, Nat.add(b, a)), Nat.add(a, b))) := {
        | match h returning Eq(Nat, Nat.add(Nat.mul(n, m), n), Nat.add(Nat.mul(m, Nat.add(b, a)), Nat.add(a, b))) with
        | | Eq.refl v => Eq.refl(Nat.add(Nat.mul(n, m), n))
        |}
        |""".stripMargin
    )
  }

  test("type-pattern captures see the predecessor of a form successor") {
    program(
      """
        |inductive Sized indices (n: Nat): Type
        | | mk (n: Nat): Sized(n)
        |
        |def predecessor (item: Sized(Nat.succ($n))): Nat := n
        |def capture (a: Nat)(b: Nat)(item: Sized(Nat.succ(Nat.add(a, b)))): Eq(Nat, predecessor(item), Nat.add(a, b)) := Eq.refl(Nat.add(a, b))
        |""".stripMargin
    )
  }

  test("constructor successor equation for power holds with a symbolic exponent") {
    program(
      """
        |def powerStep (a: Nat)(n: Nat): Eq(Nat, Nat.pow(a, Nat.succ(n)), Nat.mul(Nat.pow(a, n), a)) := Eq.refl(Nat.mul(Nat.pow(a, n), a))
        |""".stripMargin
    )
  }

  test("the product law and powers of one check by reflexivity") {
    program(
      constants +
        """
          |def product (x: Nat)(a: Nat)(b: Nat): Eq(Nat, Nat.mul(Nat.pow(x, a), Nat.pow(x, b)), Nat.pow(x, Nat.add(b, a))) := Eq.refl(Nat.pow(x, Nat.add(a, b)))
          |def known (x: Nat)(a: Nat): Eq(Nat, Nat.mul(Nat.pow(x, a), Nat.pow(x, t)), Nat.pow(x, Nat.add(a, t))) := Eq.refl(Nat.pow(x, Nat.succ(Nat.succ(a))))
          |def doubling (a: Nat)(b: Nat): Eq(Nat, Nat.mul(Nat.pow(t, a), Nat.pow(t, b)), Nat.pow(t, Nat.add(a, b))) := Eq.refl(Nat.pow(t, Nat.add(a, b)))
          |def scaled (x: Nat)(a: Nat): Eq(Nat, Nat.pow(Nat.pow(x, a), t), Nat.pow(x, Nat.mul(t, a))) := Eq.refl(Nat.pow(x, Nat.add(a, a)))
          |def unit (e: Nat): Eq(Nat, Nat.pow(o, e), o) := Eq.refl(o)
          |def zeroBase (e: Nat): Eq(Nat, Nat.pow(z, Nat.succ(e)), z) := Eq.refl(z)
          |""".stripMargin
    )
  }

  test("powers of products and powers of powers are not definitional") {
    for (
      (left, right) <- Vector(
        "Nat.pow(Nat.mul(x, y), a)" -> "Nat.mul(Nat.pow(x, a), Nat.pow(y, a))",
        "Nat.pow(Nat.pow(x, a), b)" -> "Nat.pow(x, Nat.mul(a, b))"
      )
    )
      intercept[TypeMismatch] {
        program(s"def invalid (x: Nat)(y: Nat)(a: Nat)(b: Nat): Eq(Nat, $left, $right) := Eq.refl($left)")
      }
  }

  test("Nat.mul_pow and Nat.pow_mul prove the exponent laws left out of the normal forms") {
    program(
      constants +
        """
          |def product (x: Nat)(y: Nat)(a: Nat): Eq(Nat, Nat.pow(Nat.mul(y, x), a), Nat.mul(Nat.pow(x, a), Nat.pow(y, a))) := Nat.mul_pow(x, y, a)
          |def numerals (a: Nat): Eq(Nat, Nat.pow(Nat.mul(t, t), a), Nat.pow(t, Nat.add(a, a))) := Nat.mul_pow(t, t, a)
          |def nested (x: Nat)(a: Nat)(b: Nat): Eq(Nat, Nat.pow(Nat.pow(x, a), b), Nat.pow(x, Nat.mul(b, a))) := Nat.pow_mul(x, a, b)
          |def square (x: Nat)(b: Nat): Eq(Nat, Nat.pow(Nat.mul(x, x), b), Nat.pow(x, Nat.mul(t, b))) := Nat.pow_mul(x, t, b)
          |""".stripMargin
    )
  }

  test("ordinary source arithmetic does not acquire builtin laws from its name") {
    val source =
      """
        |def plus (a: Nat)(b: Nat): Nat decreases structural(b) := {
        |  match b returning Nat with
        |  | Nat.zero => a
        |  | Nat.succ p => plus(Nat.succ(a), p)
        |}
        |def invalid (a: Nat)(b: Nat): Eq(Nat, plus(a, b), plus(b, a)) := Eq.refl(plus(a, b))
        |""".stripMargin
    intercept[TypeMismatch] { program(source) }
  }

  test("arithmetic indices do not hide an inductive occurrence from positivity") {
    for (
      index <- Vector(
        "Nat.add(encode(Bad), o)",
        "Nat.mul(k, Nat.add(encode(Bad), o))",
        "Nat.mul(k, Nat.add(Nat.mul(k, Nat.add(encode(Bad), o)), o))",
        "Nat.pow(k, encode(Bad))",
        "Nat.pow(Nat.mul(k, encode(Bad)), k)"
      )
    )
      intercept[NonStrictlyPositive] {
        program(
          constants +
            s"""
               |axiom encode (A: Type): Nat
               |axiom k: Nat
               |inductive Indexed indices (n: Nat): Type
               | | mk (n: Nat): Indexed(n)
               |
               |inductive Bad: Type
               | | mk (field: Indexed($index)): Bad
               |""".stripMargin
        )
      }
    program(
      constants +
        """
          |axiom k: Nat
          |inductive Indexed indices (n: Nat): Type
          | | mk (n: Nat): Indexed(n)
          |
          |inductive Good: Type
          | | mk (field: Indexed(Nat.mul(k, Nat.add(k, o)))): Good
          |""".stripMargin
    )
  }
  test("a summand or factor is not a structural decrease") {
    intercept[NonDecreasingRecursiveCall] {
      program(
        """
          |def bad (a: Nat)(b: Nat): Nat decreases measure(Nat.add(a, b)) := bad(a, Nat.zero)
          |""".stripMargin
      )
    }
    intercept[NonDecreasingRecursiveCall] {
      program(
        """
          |def bad (a: Nat)(b: Nat): Nat decreases measure(Nat.mul(a, b)) := bad(a, Nat.zero)
          |""".stripMargin
      )
    }
  }

  test("structural recursion accepts a metric with a known successor offset") {
    program(
      constants +
        """
          |def down (n: Nat): Nat decreases measure(Nat.add(n, o)) := {
          | match n returning Nat with
          | | Nat.zero => Nat.zero
          | | Nat.succ p => down(p)
          |}
          |def evaluated: Eq(Nat, down(Nat.mul(t, t)), z) := Eq.refl(z)
          |""".stripMargin
    )
  }

  test("quotation of an escaping arithmetic closure preserves and substitutes its capture") {
    val maker = value(
      """
        |def maker (n: Nat): Nat -> Nat := fun (m: Nat): Nat => Nat.add(Nat.mul(n, m), Nat.succ(Nat.zero))
        |{ maker }
        |""".stripMargin
    )
    val env = Interpreter.initialEnv()
    val n = FreshVar.freshVar("n", env("Nat"))
    val a = FreshVar.freshVar("a", env("Nat"))
    val b = FreshVar.freshVar("b", env("Nat"))
    val ref = CoreAst.LocalRef(0, "n")
    val localEnv = env.putLocal(ref, n)
    val closure = Interpreter.evalApply(maker, Vector(n))
    val quoted = ValueQuote.quoteTerm(closure, ValueQuote.quoteContext(localEnv), Span(0, 0))
    val captures = CapturedIndexes.getCapturedIndexes(quoted, localEnv)
    assert(captures.contains(ref.id))
    val restored = Interpreter.evalTerm(quoted, localEnv)
    assert(ValueEquivalence.defEq(closure, restored))

    val replacement = Interpreter.evalApply(env("Nat.add"), Vector(a, b))
    val store = EqStore.empty.allow(DepSet(n.id)).addLink(n.id, replacement)
    val rewritten = ValueOps.materialize(restored, store)
    val two = value("{ Nat.succ(Nat.succ(Nat.zero)) }")
    val actual = Interpreter.evalApply(rewritten, Vector(two))
    val expectedClosure = Interpreter.evalApply(maker, Vector(replacement))
    val expected = Interpreter.evalApply(expectedClosure, Vector(two))
    assert(ValueEquivalence.defEq(actual, expected))
    assert(!actual.synDeps.contains(n.id))
    assert(actual.synDeps.contains(a.id) && actual.synDeps.contains(b.id))
  }

  test("matching blocked power does not refine the variables which only schedule reduction") {
    intercept[TypeMismatch] {
      program(
        """
          |def invalid (a: Nat)(n: Nat): Eq(Nat, a, Nat.zero) := {
          | match Nat.pow(a, n) returning Eq(Nat, a, Nat.zero) with
          | | Nat.zero => Eq.refl(Nat.zero)
          | | Nat.succ p => Eq.refl(Nat.zero)
          |}
          |""".stripMargin
      )
    }
  }

  test("symbolic power resumes through simultaneous transitive exponent substitution") {
    val env = Interpreter.initialEnv()
    val a = NatFixtures.fresh("a")
    val b = NatFixtures.fresh("b")
    val n = NatFixtures.fresh("n")
    val m = NatFixtures.fresh("m")
    val sum = NatNormalForm.add(a, b)
    val symbolic = NatNormalForm.pow(sum, n)
    val two = NatNormalForm.literal(2)
    val store = EqStore.empty.allow(DepSet(n.id, m.id)).addLink(n.id, m).addLink(m.id, two)
    val result = ValueOps.materialize(symbolic, store)
    assert(ValueEquivalence.defEq(result, NatNormalForm.mul(sum, sum)))
    assert(!result.synDeps.contains(n.id) && !result.synDeps.contains(m.id))
  }

  test("kernel Nat declarations exist without a prelude and cannot be redeclared") {
    val two = program("{ Nat.add(Nat.succ(Nat.zero), Nat.succ(Nat.zero)) }", Prelude.none)
    assert(two.exists(value => ValueEquivalence.defEq(value, NatNormalForm.literal(2))))
    intercept[AlreadyDefined] {
      program("namespace Nat {\n  def mul (a: Nat)(b: Nat): Nat := a\n}\n", Prelude.none)
    }
    intercept[AlreadyDefined] { program("inductive Nat : Type\n | zero : Nat\n", Prelude.none) }
    intercept[AlreadyDefined] { program("inductive Bool : Type\n | false : Bool\n", Prelude.none) }
  }

  test("a closed power too large to represent points to the user's call site") {
    val two = "Nat.succ(Nat.succ(Nat.zero))"
    val six = "Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))"
    val source = s"def trigger: Nat := Nat.pow($two, Nat.pow($two, Nat.pow($two, $six)))\n"
    val error = intercept[NatValueTooLarge] { program(source) }
    assertEquals(error.exponent, BigInt(1) << 64)
    val callSpan = error.span.getOrElse(fail("Missing span"))
    // The outer call raises the error: its span starts before the first nested call.
    assert(
      callSpan.start >= source.indexOf("Nat.pow(") && callSpan.start < source.indexOf("Nat.pow(", 21),
      s"$callSpan"
    )
  }
  test("native subtraction and comparisons decide huge constants without recursing per successor") {
    val big = "Nat.pow(Nat.add(Nat.succ(Nat.succ(Nat.zero)), Nat.zero), Nat.pow(Nat.succ(Nat.succ(Nat.zero)), " +
      "Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))))"
    def evaluate(expression: String): Value = value(s"{ $expression }")
    assertEquals(evaluate(s"Nat.sub($big, $big)").key, NatNormalForm.literal(0).key)
    assertEquals(evaluate(s"Nat.pred($big)").key, NatNormalForm.literal((BigInt(1) << 64) - 1).key)
    assertEquals(evaluate(s"Nat.sub($big, Nat.succ(Nat.zero))").key, evaluate(s"Nat.pred($big)").key)
    assertEquals(PrettyPrinter.print(evaluate(s"Nat.ble($big, $big)")), "Bool.true")
    assertEquals(PrettyPrinter.print(evaluate(s"Nat.beq($big, Nat.succ($big))")), "Bool.false")
    assertEquals(PrettyPrinter.print(evaluate(s"Nat.isZero(Nat.sub($big, $big))")), "Bool.true")
  }

  test("stuck subtraction absorbs only constants, so substitution commutes with normalization") {
    val n = NatFixtures.fresh("n")
    val m = NatFixtures.fresh("m")
    val k = NatFixtures.fresh("k")
    val difference = NatNormalForm.sub(n, m)
    val nested = NatNormalForm.sub(difference, k)
    nested match {
      case VApp(head, Vector(minuend, subtrahend), _, _) =>
        assert(head eq Kernel.sub)
        assertEquals(minuend.key, difference.key)
        assertEquals(subtrahend.key, k.key)
      case other => fail(s"Expected a stuck subtraction, got $other")
    }
    val store = EqStore.empty.allow(DepSet(k.id)).addLink(k.id, difference)
    assertEquals(ValueOps.materialize(nested, store).key, Kernel.zeroValue.key)

    program(
      """
        |def direct (a: Nat)(b: Nat): Eq(Nat, Nat.sub(Nat.sub(a, b), Nat.sub(a, b)), Nat.zero) := Eq.refl(Nat.zero)
        |def refined (a: Nat)(b: Nat)(x: Nat)(h: Eq(Nat, Nat.sub(a, b), x)): Eq(Nat, Nat.sub(Nat.sub(a, b), x), Nat.zero) := {
        |  match h returning Eq(Nat, Nat.sub(Nat.sub(a, b), x), Nat.zero) with
        |  | Eq.refl v => Eq.refl(Nat.zero)
        |}
        |""".stripMargin
    )
  }

  test("native Nat functions satisfy the recursive equations") {
    program(
      """
        |def subZero (a: Nat): Eq(Nat, Nat.sub(a, Nat.zero), a) := Eq.refl(a)
        |def subSucc (a: Nat)(b: Nat): Eq(Nat, Nat.sub(a, Nat.succ(b)), Nat.pred(Nat.sub(a, b))) :=
        |  Eq.refl(Nat.sub(a, Nat.succ(b)))
        |def predSucc (a: Nat): Eq(Nat, Nat.pred(Nat.succ(a)), a) := Eq.refl(a)
        |def bleSucc (a: Nat)(b: Nat): Eq(Bool, Nat.ble(Nat.succ(a), Nat.succ(b)), Nat.ble(a, b)) :=
        |  Eq.refl(Nat.ble(a, b))
        |def bleZero (b: Nat): Eq(Bool, Nat.ble(Nat.zero, b), Bool.true) := Eq.refl(Bool.true)
        |def beqZero (b: Nat): Eq(Bool, Nat.beq(Nat.zero, b), Nat.isZero(b)) := Eq.refl(Nat.isZero(b))
        |def beqSucc (a: Nat)(b: Nat): Eq(Bool, Nat.beq(Nat.succ(a), Nat.succ(b)), Nat.beq(a, b)) :=
        |  Eq.refl(Nat.beq(a, b))
        |def leSum (a: Nat)(b: Nat): Nat.le(a, Nat.add(a, b)) := Eq.refl(Bool.true)
        |""".stripMargin
    )
  }

  test("a positive constant captured by a type-pattern binder quotes as a type term") {
    program(
      """
        |inductive Tagged (A: Type) indices (n: Nat) : Type
        | | mk {A: Type} (n: Nat) : Tagged(A, n)
        |
        |def mk (n: Nat): (item: Tagged($A, n)) -> Nat := fun (item: Tagged($A, n)): Nat => n
        |def pick (b: Bool): Nat := {
        |  let f := match b with
        |    | Bool.true => mk(Nat.succ(Nat.zero))
        |    | Bool.false => mk(Nat.succ(Nat.zero))
        |  Nat.zero
        |}
        |""".stripMargin
    )
  }

  test("positivity and conversion stop at stuck native applications") {
    program(
      """
        |inductive Box indices (n: Nat) : Type
        | | mk (n: Nat) : Box(n)
        |
        |inductive Wrap (n: Nat)(m: Nat) : Type
        | | mk {n: Nat}{m: Nat} (b: Box(Nat.sub(n, m))) : Wrap(n, m)
        |""".stripMargin
    )
    val env = Interpreter.initialEnv(Prelude.default)
    assert(!ValueEquivalence.defEq(env("Nat.beq"), env("Nat.ble")))
    assert(!ValueEquivalence.defEq(env("Nat.pow"), env("Nat.sub")))
  }
}
