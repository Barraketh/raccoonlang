package com.raccoonlang

import com.raccoonlang.NatFixtures._
import com.raccoonlang.Value._

class NatNormalFormTests extends munit.FunSuite {
  private val span = Span(10, 20)
  private lazy val env = Interpreter.initialEnv(Prelude.default)

  private def sameKey(left: Value, right: Value)(implicit loc: munit.Location): Unit = assertEquals(left.key, right.key)

  private def differentKey(left: Value, right: Value)(implicit loc: munit.Location): Unit =
    assertNotEquals(left.key, right.key)

  /** Replace atoms by key; other atoms are unchanged. */
  private def substitute(value: Value, replacements: (Value, Value)*): Value = {
    val byKey = replacements.map { case (atom, replacement) => atom.key -> replacement }.toMap
    value match {
      case poly: VNatPoly => NatNormalForm.substituteAtoms(poly, atom => byKey.getOrElse(atom.key, atom))
      case atom           => byKey.getOrElse(atom.key, atom)
    }
  }

  private def descendants(term: ElabAst.Term): Vector[ElabAst.Term] =
    term match {
      case app @ ElabAst.Term.App(fn, args, _) => Vector(app) ++ descendants(fn) ++ args.flatMap(descendants)
      case other                               => Vector(other)
    }

  private def depth(term: ElabAst.Term): Int = term match {
    case ElabAst.Term.App(head, args, _) => 1 + (head +: args).map(depth).max
    case _                               => 1
  }

  test("associative and commutative rearrangements share keys") {
    val a = fresh("a")
    val b = fresh("b")
    val c = fresh("c")
    val d = fresh("d")
    sameKey(add(a, b), add(b, a))
    sameKey(add(add(a, b), c), add(a, add(c, b)))
    sameKey(mul(a, b), mul(b, a))
    sameKey(mul(mul(a, b), c), mul(a, mul(c, b)))
    // Sums as factors: the factors are reordered, and the sums themselves are canonical.
    val left = mul(mul(add(a, b), c), add(d, constant(1)))
    val right = mul(add(constant(1), d), mul(c, add(b, a)))
    sameKey(left, right)
    sameKey(mul(constant(2), mul(a, constant(3))), mul(constant(6), a))
    sameKey(add(mul(a, constant(0)), mul(b, constant(1))), b)
    sameKey(add(a, a), mul(constant(2), a))
  }

  test("the normal forms of the design's example table") {
    val n = fresh("n")
    val m = fresh("m")
    val a = fresh("a")
    val b = fresh("b")
    val c = fresh("c")
    val x = fresh("x")

    // (n + 1) * (m + 2) is one term whose factors are the two sums.
    val product = form(mul(add(n, constant(1)), add(m, constant(2))))
    assertEquals(product.constant, BigInt(0))
    assertEquals(product.terms.length, 1)
    assertEquals(product.terms.head.coefficient, BigInt(1))
    assertEquals(
      product.terms.head.monomial.factors.map(factor => (factor.base.key, numeralExponent(factor))).toSet,
      Set((add(n, constant(1)).key, BigInt(1)), (add(m, constant(2)).key, BigInt(1)))
    )

    // 2 * (a + b) distributes, because the multiplier is a numeral.
    val doubled = mul(constant(2), add(a, b))
    sameKey(doubled, add(mul(constant(2), a), mul(constant(2), b)))
    assertEquals(form(doubled).terms.map(_.coefficient), Vector(BigInt(2), BigInt(2)))

    // (2a + 2b) * c extracts the content: 2 * (a + b) * c.
    val extracted = form(mul(doubled, c))
    assertEquals(extracted.terms.length, 1)
    assertEquals(extracted.terms.head.coefficient, BigInt(2))
    assertEquals(extracted.terms.head.monomial.factors.map(_.base.key).toSet, Set(add(a, b).key, c.key))
    sameKey(mul(doubled, c), mul(constant(2), mul(add(a, b), c)))

    // x * x + x is x^2 + x.
    val square = form(add(mul(x, x), x))
    assertEquals(square.terms.length, 2)
    sameKey(add(mul(x, x), x), add(pow(x, 2), x))

    // (a + b) * (b + a) is (a + b)^2.
    val sumSquare = form(mul(add(a, b), add(b, a)))
    assertEquals(sumSquare.terms.length, 1)
    assertEquals(sumSquare.terms.head.monomial.factors.map(numeralExponent), Vector(BigInt(2)))
    sameKey(mul(add(a, b), add(b, a)), pow(add(a, b), 2))

    // (a + 1) * b + b keeps two terms and differs from (a + 2) * b.
    val twoTerms = add(mul(add(a, constant(1)), b), b)
    assertEquals(termCount(twoTerms), 2)
    differentKey(twoTerms, mul(add(a, constant(2)), b))
  }

  test("symbolic distributivity and powers of sums are not normalized") {
    val a = fresh("a")
    val b = fresh("b")
    val c = fresh("c")
    differentKey(mul(a, add(b, c)), add(mul(a, b), mul(a, c)))
    differentKey(mul(a, add(b, constant(1))), add(mul(a, b), a))
    differentKey(pow(add(a, b), 2), add(add(mul(a, a), mul(constant(2), mul(a, b))), mul(b, b)))
    assert(!ValueEquivalence.defEq(mul(a, add(b, c)), add(mul(a, b), mul(a, c))))
  }

  test("content extraction makes products of non-primitive sums canonical") {
    val a = fresh("a")
    val b = fresh("b")
    val c = fresh("c")
    val d = fresh("d")
    sameKey(mul(add(mul(constant(2), a), mul(constant(2), b)), c), mul(mul(constant(2), c), add(a, b)))
    sameKey(
      mul(add(mul(constant(6), a), constant(4)), add(mul(constant(3), b), mul(constant(3), d))),
      mul(constant(6), mul(add(mul(constant(3), a), constant(2)), add(b, d)))
    )
    // Equal sum products collect their coefficients.
    sameKey(add(mul(add(a, b), c), mul(c, add(b, a))), mul(constant(2), mul(add(a, b), c)))
  }

  test("powers of sums stay factored and merge exponents") {
    val a = fresh("a")
    val b = fresh("b")
    val c = fresh("c")
    val sum = add(a, b)
    sameKey(mul(pow(sum, 2), sum), pow(sum, 3))
    sameKey(pow(pow(sum, 2), 3), pow(sum, 6))
    sameKey(pow(mul(sum, c), 2), mul(pow(sum, 2), pow(c, 2)))
    val scaled = form(pow(mul(constant(2), sum), 3))
    assertEquals(scaled.terms.length, 1)
    assertEquals(scaled.terms.head.coefficient, BigInt(8))
    assertEquals(scaled.terms.head.monomial.factors.map(numeralExponent), Vector(BigInt(3)))
    assertEquals(termCount(pow(sum, 20)), 1)
    sameKey(pow(add(a, constant(1)), 0), constant(1))
    sameKey(pow(constant(0), 5), constant(0))
    sameKey(pow(constant(3), 4), constant(81))
  }

  test("powers of equal bases add symbolic exponents") {
    val x = fresh("x")
    val a = fresh("a")
    val b = fresh("b")
    val two = constant(2)
    sameKey(mul(pow(x, a), pow(x, b)), pow(x, add(a, b)))
    sameKey(mul(pow(two, a), pow(two, b)), pow(two, add(b, a)))
    sameKey(pow(two, add(a, constant(1))), mul(two, pow(two, a)))
    sameKey(mul(pow(x, a), pow(x, 2)), pow(x, add(a, constant(2))))
    sameKey(pow(pow(x, a), 2), pow(x, mul(two, a)))
    sameKey(mul(pow(x, a), pow(x, a)), pow(x, add(a, a)))

    // x^2 * x^a keeps the base once as each kind, the numeral power first.
    val mixed = form(pow(x, add(a, constant(2))))
    assertEquals(mixed.terms.length, 1)
    mixed.terms.head.monomial.factors match {
      case Vector(numeral: NatNormalForm.NumeralPower, symbolic: NatNormalForm.SymbolicPower) =>
        assertEquals((numeral.base.key, numeral.exponent), (x.key, BigInt(2)))
        assertEquals((symbolic.base.key, symbolic.exponent.key), (x.key, a.key))
      case other => fail(s"Expected x^2 * x^a, got $other")
    }
    // A symbolic power has no known successor, so it is blocked on its base and its exponent.
    assertEquals(ConstructorValue.unapply(pow(x, a)), None)
    assertEquals(ReductionBlockers.of(pow(x, a)), DepSet(x.id, a.id))
  }

  test("powers of one and zero") {
    val x = fresh("x")
    val e = fresh("e")
    sameKey(pow(constant(1), e), constant(1))
    sameKey(pow(constant(1), add(e, constant(3))), constant(1))
    sameKey(mul(x, pow(constant(1), e)), x)
    sameKey(pow(constant(0), add(e, constant(1))), constant(0))
    sameKey(pow(x, constant(0)), constant(1))
    // 0^e is zero only when e is positive, so it stays a power and merges like any other.
    assertEquals(termCount(pow(constant(0), e)), 1)
    sameKey(mul(pow(constant(0), e), pow(constant(0), x)), pow(constant(0), add(e, x)))
  }

  test("symbolic powers keep their whole base") {
    val x = fresh("x")
    val y = fresh("y")
    val a = fresh("a")
    val b = fresh("b")
    val two = constant(2)
    val doubled = mul(two, x)
    sameKey(mul(pow(doubled, a), pow(doubled, b)), pow(doubled, add(a, b)))
    sameKey(pow(add(x, x), a), pow(doubled, a))
    differentKey(pow(doubled, a), mul(pow(two, a), pow(x, a)))
    // A known part of the exponent is a numeral power, which extracts content: (2x)^(a+2) = 4 * x^2 * (2x)^a.
    sameKey(pow(doubled, add(a, constant(2))), mul(constant(4), mul(pow(x, 2), pow(doubled, a))))
    // Powers of products and powers of powers are not normalized.
    differentKey(pow(mul(x, y), a), mul(pow(x, a), pow(y, a)))
    differentKey(pow(pow(x, a), b), pow(x, mul(a, b)))
    differentKey(pow(pow(x, 2), a), pow(x, mul(two, a)))
    differentKey(pow(constant(4), a), pow(two, mul(two, a)))
    differentKey(pow(constant(6), a), mul(pow(two, a), pow(constant(3), a)))
    assert(!ValueEquivalence.defEq(pow(mul(x, y), a), mul(pow(x, a), pow(y, a))))
  }

  test("substitution into symbolic exponents and bases") {
    val x = fresh("x")
    val y = fresh("y")
    val e = fresh("e")
    val c = fresh("c")
    val source = mul(pow(x, e), y)
    sameKey(substitute(source, e -> constant(0)), y)
    sameKey(substitute(source, e -> constant(2)), mul(pow(x, 2), y))
    sameKey(substitute(source, e -> add(c, constant(1))), mul(mul(pow(x, c), x), y))
    sameKey(substitute(mul(pow(x, e), pow(x, c)), e -> c), pow(x, mul(constant(2), c)))
    sameKey(substitute(mul(pow(x, e), pow(x, 2)), e -> constant(1)), pow(x, 3))
    // A base that becomes one vanishes; a base that becomes zero leaves 0^e, which is not zero.
    sameKey(substitute(source, x -> constant(1)), y)
    sameKey(substitute(source, x -> constant(0)), mul(pow(constant(0), e), y))
    sameKey(substitute(source, x -> constant(0), e -> add(c, constant(1))), constant(0))
    // A base that becomes a product stays whole, and equal bases merge.
    sameKey(substitute(source, x -> mul(y, c)), mul(pow(mul(y, c), e), y))
    sameKey(substitute(mul(pow(x, e), pow(y, c)), x -> y), pow(y, add(e, c)))
    // Exponents of exponents are rebuilt too.
    sameKey(substitute(pow(x, pow(constant(2), e)), e -> constant(3)), pow(x, 8))
  }

  test("substitution flattens a lone sum and keeps products of sums") {
    val x = fresh("x")
    val a = fresh("a")
    val b = fresh("b")
    val c = fresh("c")
    val d = fresh("d")
    val sum = add(a, b)
    val source = mul(x, sum)
    sameKey(substitute(source, x -> constant(1)), sum)
    sameKey(substitute(source, x -> constant(2)), add(mul(constant(2), a), mul(constant(2), b)))
    sameKey(substitute(source, x -> constant(0)), constant(0))
    sameKey(substitute(source, x -> add(c, d)), mul(add(c, d), sum))
    sameKey(substitute(mul(constant(3), source), x -> constant(1)), mul(constant(3), sum))
    // A sum base that substitution makes non-primitive gives up its content.
    sameKey(substitute(source, a -> b), mul(constant(2), mul(x, b)))
    // A sum base that becomes a sum scaled by a numeral times x stays a product.
    sameKey(substitute(mul(x, add(a, constant(1))), a -> add(b, constant(1))), mul(x, add(b, constant(2))))
    // A sum base that becomes zero removes its term.
    sameKey(substitute(add(mul(x, sum), c), a -> constant(0), b -> constant(0)), c)
  }

  test("normalizing then substituting agrees with substituting then normalizing") {
    val n = fresh("n")
    val m = fresh("m")
    val a = fresh("a")
    val b = fresh("b")
    val source = add(mul(n, m), n)
    val sum = add(a, b)
    sameKey(substitute(source, n -> sum), add(mul(sum, m), sum))
    sameKey(substitute(source, n -> sum, m -> constant(2)), add(mul(constant(3), a), mul(constant(3), b)))
    // Atoms that become equal merge their factors.
    val merged = form(substitute(mul(n, m), n -> a, m -> a))
    assertEquals(merged.terms.head.monomial.factors.map(numeralExponent), Vector(BigInt(2)))
    sameKey(substitute(mul(n, n), n -> sum), mul(sum, sum))
  }

  test("the design's substitution counterexamples stay consistent") {
    val p = fresh("p")
    val q = fresh("q")
    val x = fresh("x")
    val y = fresh("y")
    val a = fresh("a")
    val b = fresh("b")
    val c = fresh("c")
    val d = fresh("d")

    // Regrouping a sum gives one form, before and after p := x*a, q := x*b.
    val leftGrouped = add(add(p, q), y)
    val rightGrouped = add(p, add(q, y))
    sameKey(leftGrouped, rightGrouped)
    val replacements = Seq(p -> mul(x, a), q -> mul(x, b))
    sameKey(substitute(leftGrouped, replacements: _*), substitute(rightGrouped, replacements: _*))
    sameKey(substitute(leftGrouped, replacements: _*), add(add(mul(x, a), mul(x, b)), y))

    // Factored and unfactored products are different forms, and stay different under c := 1, d := 0.
    val unfactored = mul(add(mul(x, a), mul(x, b)), add(c, d))
    val factored = mul(mul(x, add(a, b)), add(c, d))
    differentKey(unfactored, factored)
    val unit = Seq(c -> constant(1), d -> constant(0))
    val unfactoredUnit = substitute(unfactored, unit: _*)
    val factoredUnit = substitute(factored, unit: _*)
    sameKey(unfactoredUnit, add(mul(x, a), mul(x, b)))
    sameKey(factoredUnit, mul(x, add(a, b)))
    differentKey(unfactoredUnit, factoredUnit)
    assert(!ValueEquivalence.defEq(unfactoredUnit, factoredUnit))
  }

  test("unchanged substitution returns the original value, including through sum bases") {
    val n = fresh("n")
    val m = fresh("m")
    val poly = add(mul(add(n, constant(1)), add(m, constant(2))), n).asInstanceOf[VNatPoly]
    assert(NatNormalForm.substituteAtoms(poly, identity) eq poly)
    var calls = Map.empty[ValueKey.Key, Int]
    NatNormalForm.substituteAtoms(
      poly,
      atom => {
        calls = calls.updated(atom.key, calls.getOrElse(atom.key, 0) + 1)
        atom
      }
    )
    assertEquals(calls, Map(n.key -> 1, m.key -> 1))
  }

  test("identity operations reuse values and constant increments share terms") {
    val a = fresh("a")
    val b = fresh("b")
    val poly = add(a, b)
    val originalTerms = form(poly).terms
    val zero = constant(0)
    val one = constant(1)
    assert(add(poly, zero) eq poly)
    assert(add(zero, poly) eq poly)
    assert(add(a, zero) eq a)
    assert(mul(poly, one) eq poly)
    assert(mul(one, poly) eq poly)
    assert(pow(poly, 1) eq poly)
    assert(form(NatNormalForm.successor(poly)).terms eq originalTerms)
    assert(form(add(poly, constant(7))).terms eq originalTerms)

    // Scaling keeps every monomial object.
    val scaled = form(mul(constant(5), add(add(constant(3), mul(constant(2), a)), mul(constant(4), b))))
    assertEquals(scaled.constant, BigInt(15))
    assertEquals(scaled.terms.map(_.coefficient).toSet, Set(BigInt(10), BigInt(20)))
  }

  test("successors fold into shared terms and the constructor view peels one at a time") {
    val a = fresh("a")
    val b = fresh("b")
    val n = fresh("n")
    val poly = add(a, b)
    assertEquals(ConstructorValue.unapply(constant(0)).map(_._1), Some(Kernel.zero))
    val inner = ConstructorValue(Kernel.succ, Vector(poly), Kernel.natType)
    val prefixed = ConstructorValue(Kernel.succ, Vector(inner), Kernel.natType)
    assertEquals(form(prefixed).constant, BigInt(2))
    assert(form(prefixed).terms eq form(poly).terms)
    val (firstHead, firstFields) = ConstructorValue.unapply(prefixed).get
    assertEquals(firstHead, Kernel.succ)
    val (secondHead, secondFields) = ConstructorValue.unapply(firstFields.head).get
    assertEquals(secondHead, Kernel.succ)
    sameKey(secondFields.head, poly)

    val successorOfN = ConstructorValue(Kernel.succ, Vector(n), Kernel.natType)
    sameKey(successorOfN, add(n, constant(1)))
    val store = EqStore.empty.allow(DepSet(n.id)).addLink(n.id, poly)
    sameKey(ValueOps.materialize(successorOfN, store), Interpreter.evalApply(Kernel.succ, Vector(poly)))
    intercept[IllegalArgumentException] { VCtor(Kernel.succ, Vector(n), Kernel.natType) }
  }

  test("products of successors are blocked on all their dependencies") {
    val n = fresh("n")
    val m = fresh("m")
    val product = mul(add(n, constant(1)), add(m, constant(1)))
    assertEquals(ConstructorValue.unapply(product), None)
    assertEquals(ReductionBlockers.of(product), DepSet(n.id, m.id))
    // A known successor of a product of sums peels.
    val (head, fields) = ConstructorValue.unapply(add(product, constant(1))).get
    assertEquals(head, Kernel.succ)
    sameKey(fields.head, product)
  }

  test("unification cancels successor offsets and leaves noninjective equations stuck") {
    import ValueEquivalence.UnificationFailure._
    val a = fresh("a")
    val b = fresh("b")
    val refinable = EqStore.empty.allow(DepSet(a.id, b.id))
    val offsetStore = ValueEquivalence.tryUnify(add(a, constant(3)), add(b, constant(3)), refinable).toOption.get
    assert(ValueEquivalence.defEq(ValueOps.materialize(a, offsetStore), ValueOps.materialize(b, offsetStore)))

    val linked = ValueEquivalence.tryUnify(a, add(b, constant(1)), EqStore.empty.allow(DepSet(a.id)))
    assert(ValueEquivalence.defEq(ValueOps.materialize(a, linked.toOption.get), add(b, constant(1))))

    val zero = Kernel.zeroValue
    assert(
      ValueEquivalence.tryUnify(zero, add(a, constant(1)), EqStore.empty).left.exists(_.isInstanceOf[Contradiction])
    )
    assert(ValueEquivalence.tryUnify(mul(a, b), zero, EqStore.empty).left.exists(_.isInstanceOf[Stuck]))
    val sums = ValueEquivalence.tryUnify(mul(add(a, constant(1)), b), add(mul(a, b), b), EqStore.empty)
    assert(sums.left.exists(_.isInstanceOf[Stuck]))
    val occurs = ValueEquivalence.tryUnify(a, add(a, constant(1)), EqStore.empty.allow(DepSet(a.id)))
    assert(occurs.left.exists(_.isInstanceOf[Stuck]))

    // Failure orientation survives cancellation.
    val successor = ConstructorValue(Kernel.succ, Vector(a), Kernel.natType)
    val doubled = mul(constant(2), b)
    ValueEquivalence.tryUnify(successor, add(doubled, constant(1)), EqStore.empty) match {
      case Left(Stuck(left, right)) =>
        assert(left eq a)
        sameKey(right, doubled)
      case other => fail(s"Expected a stuck equation between the canceled remainders, got $other")
    }
    val positive = constant(2)
    assertEquals(ValueEquivalence.tryUnify(zero, positive, EqStore.empty), Left(Contradiction(zero, positive)))
  }

  test("structural decrease compares equal symbolic remainders with fewer successors") {
    val n = fresh("n")
    val m = fresh("m")
    assert(NatNormalForm.isStrictlySmaller(add(n, constant(2)), add(n, constant(3)).asInstanceOf[VNatPoly]))
    assert(NatNormalForm.isStrictlySmaller(n, add(n, constant(1)).asInstanceOf[VNatPoly]))
    assert(!NatNormalForm.isStrictlySmaller(add(n, m), add(n, constant(2)).asInstanceOf[VNatPoly]))
    assert(!NatNormalForm.isStrictlySmaller(n, add(n, m).asInstanceOf[VNatPoly]))
    val product = mul(add(n, constant(1)), m)
    assert(NatNormalForm.isStrictlySmaller(product, add(product, constant(2)).asInstanceOf[VNatPoly]))
    // Without distributivity, n * m is not the root (n + 1) * m with successors removed.
    assert(!NatNormalForm.isStrictlySmaller(mul(n, m), add(product, constant(1)).asInstanceOf[VNatPoly]))
  }

  test("subtraction and comparisons depend only on the signed difference") {
    val n = fresh("n")
    val m = fresh("m")
    sameKey(NatNormalForm.sub(add(n, constant(3)), add(n, constant(1))), constant(2))
    sameKey(NatNormalForm.sub(n, add(n, m)), constant(0))
    sameKey(NatNormalForm.sub(add(n, m), m), n)
    sameKey(NatNormalForm.sub(add(n, constant(2)), add(m, constant(2))), NatNormalForm.sub(n, m))
    sameKey(NatNormalForm.sub(NatNormalForm.sub(n, m), constant(1)), NatNormalForm.sub(n, add(m, constant(1))))
    sameKey(NatNormalForm.pred(NatNormalForm.sub(n, m)), NatNormalForm.sub(n, add(m, constant(1))))
    sameKey(NatNormalForm.ble(n, add(n, m)), Kernel.trueValue)
    sameKey(NatNormalForm.ble(add(n, constant(1)), n), Kernel.falseValue)
    sameKey(NatNormalForm.ble(add(n, constant(1)), add(m, constant(1))), NatNormalForm.ble(n, m))
    sameKey(NatNormalForm.beq(add(n, m), add(m, n)), Kernel.trueValue)
    sameKey(NatNormalForm.beq(add(n, constant(1)), n), Kernel.falseValue)
    sameKey(NatNormalForm.beq(constant(0), n), NatNormalForm.isZero(n))
    sameKey(NatNormalForm.beq(n, m), NatNormalForm.beq(m, n))

    val store = EqStore.empty.allow(DepSet(m.id)).addLink(m.id, n)
    sameKey(ValueOps.materialize(NatNormalForm.sub(n, m), store), constant(0))
    sameKey(ValueOps.materialize(NatNormalForm.ble(n, m), store), Kernel.trueValue)
  }

  test("cancellation treats sum factors as opaque") {
    val x = fresh("x")
    val y = fresh("y")
    val a = fresh("a")
    val b = fresh("b")
    val product = mul(x, add(a, b))
    // Whole terms cancel, including the constant.
    sameKey(NatNormalForm.sub(add(product, constant(3)), product), constant(3))
    sameKey(NatNormalForm.sub(add(product, y), product), y)
    sameKey(NatNormalForm.ble(product, add(product, y)), Kernel.trueValue)
    sameKey(NatNormalForm.beq(add(product, constant(1)), product), Kernel.falseValue)
    sameKey(NatNormalForm.ble(add(product, constant(1)), product), Kernel.falseValue)
    // x * (a + b) - x * a would need distributivity, so it stays stuck on both parts.
    NatNormalForm.sub(product, mul(x, a)) match {
      case VApp(head, Vector(minuend, subtrahend), _, _) =>
        assert(head eq Kernel.sub)
        sameKey(minuend, product)
        sameKey(subtrahend, mul(x, a))
      case other => fail(s"Expected a stuck subtraction, got $other")
    }
    NatNormalForm.ble(product, mul(x, a)) match {
      case VApp(head, _, _, _) => assert(head eq Kernel.ble)
      case other               => fail(s"Expected a stuck comparison, got $other")
    }
    // A stuck difference absorbs only constants.
    val difference = NatNormalForm.sub(product, x)
    sameKey(NatNormalForm.sub(difference, constant(2)), NatNormalForm.sub(product, add(x, constant(2))))
  }

  test("closed powers too large to represent raise a typed error") {
    val x = fresh("x")
    val huge = BigInt(1) << 40
    intercept[NatValueTooLarge] { pow(constant(2), huge) }
    intercept[NatValueTooLarge] { pow(mul(constant(2), x), huge) }
    intercept[NatValueTooLarge] { pow(add(mul(constant(2), x), constant(2)), huge) }
    intercept[NatValueTooLarge] { NatNormalForm.pow(constant(2), add(fresh("e"), constant(huge))) }
    intercept[NatValueTooLarge] { pow(constant(2), Int.MaxValue) }
    // Content one, zero, and one have no numeral to grow; powers of symbolic bases keep arbitrary-precision exponents.
    sameKey(pow(constant(1), huge), constant(1))
    sameKey(pow(constant(0), huge), constant(0))
    assertEquals(numeralExponent(form(pow(x, huge)).terms.head.monomial.factors.head), huge)
    assertEquals(numeralExponent(form(pow(add(x, constant(1)), huge)).terms.head.monomial.factors.head), huge)
    sameKey(mul(pow(x, huge), x), pow(x, huge + 1))
  }

  test("a zero factor wins over a power too large to represent in either factor order") {
    val x = fresh("x")
    val y = fresh("y")
    val huge = BigInt(1) << 40
    // Factors sort by key, so these two cases visit the huge power before and after the zero, in some order.
    sameKey(substitute(mul(pow(x, huge), y), x -> constant(2), y -> constant(0)), constant(0))
    sameKey(substitute(mul(pow(y, huge), x), y -> constant(2), x -> constant(0)), constant(0))
    intercept[NatValueTooLarge] { substitute(mul(pow(x, huge), y), x -> constant(2), y -> constant(1)) }
  }

  test("BigInt keys are deterministic across full-width constants and coefficients") {
    val n = fresh("n")
    val large = (BigInt(1) << 130) + 37
    sameKey(constant(large), constant(BigInt(large.toString)))
    differentKey(constant(large), constant((BigInt(1) << 129) + 37))
    differentKey(constant(large), constant(large + 1))
    differentKey(constant(Long.MaxValue), constant(BigInt(Long.MaxValue) + 1))
    sameKey(mul(constant(large), n), add(mul(constant(large / 2), n), mul(constant(large - large / 2), n)))
    differentKey(pow(n, BigInt(Long.MaxValue)), pow(n, BigInt(Long.MaxValue) + 1))
  }

  test("large Nat literals quote compactly and evaluate") {
    val huge = BigInt(1) << 90
    val value = constant(huge)
    val residual = ValueQuote.quoteTerm(value, ValueQuote.quoteContext(env), span)
    assertEquals(residual, ElabAst.Term.NatLit(huge, span))
    assertEquals(PrettyPrinter.printElabTerm(residual), huge.toString)
    assertEquals(CapturedIndexes.getCapturedIndexes(residual, env).getCardinality, 0)
    sameKey(Interpreter.evalTerm(residual, env), value)
  }

  test("nested sums quote as their own sums and round trip with captured atoms") {
    val a = fresh("a")
    val b = fresh("b")
    val c = fresh("c")
    val atoms = Vector(a, b, c)
    val quoteEnv = atoms.zipWithIndex.foldLeft(env) { case (current, (atom, index)) =>
      current.putLocal(CoreAst.LocalRef(index, atom.name), atom)
    }
    val inner = mul(c, add(a, constant(1)))
    val nested = add(mul(constant(2), mul(a, pow(add(inner, b), 2))), add(b, constant(3)))
    val residual = ValueQuote.quoteTerm(nested, ValueQuote.quoteContext(quoteEnv), span)
    val names = descendants(residual).collect { case ElabAst.Term.App(ElabAst.Term.GlobalRef(name, _), _, _) => name }
    assertEquals(names.toSet, Set("Nat.add", "Nat.mul", "Nat.pow"))
    // Each distinct atom is quoted once, even when it occurs inside several sum bases.
    val references = descendants(residual).collect { case reference: ElabAst.Term.LocalRef => reference }
    assertEquals(
      references.foldLeft(List.empty[AnyRef])((seen, r) => if (seen.exists(_ eq r)) seen else r :: seen).size,
      3
    )
    assertEquals(CapturedIndexes.getCapturedIndexes(residual, quoteEnv).getCardinality, 3)
    sameKey(Interpreter.evalTerm(residual, quoteEnv), nested)
  }

  test("wide sums and products quote to shallow syntax with all captures preserved") {
    val atoms = Vector.tabulate(257)(index => fresh(s"q$index"))
    val quoteEnv = atoms.zipWithIndex.foldLeft(env) { case (current, (atom, index)) =>
      current.putLocal(CoreAst.LocalRef(index, atom.name), atom)
    }
    val context = ValueQuote.quoteContext(quoteEnv)
    val sums = atoms.grouped(2).map(pair => add(pair.head, pair.last)).toVector
    for (value <- Vector(sum(atoms), product(atoms), product(sums))) {
      val residual = ValueQuote.quoteTerm(value, context, span)
      assert(depth(residual) <= 14, s"depth ${depth(residual)}")
      assertEquals(CapturedIndexes.getCapturedIndexes(residual, quoteEnv).getCardinality, atoms.length)
      sameKey(Interpreter.evalTerm(residual, quoteEnv), value)
    }
  }

  test("symbolic powers quote as native powers and round trip") {
    val x = fresh("x")
    val a = fresh("a")
    val b = fresh("b")
    val atoms = Vector(x, a, b)
    val quoteEnv = atoms.zipWithIndex.foldLeft(env) { case (current, (atom, index)) =>
      current.putLocal(CoreAst.LocalRef(index, atom.name), atom)
    }
    val context = ValueQuote.quoteContext(quoteEnv)
    for (
      value <- Vector(
        pow(x, a),
        mul(pow(x, add(a, b)), pow(x, 2)),
        pow(mul(constant(2), x), mul(a, b)),
        add(pow(pow(x, a), b), pow(constant(0), a)),
        pow(add(x, constant(1)), pow(constant(2), a))
      )
    ) {
      val residual = ValueQuote.quoteTerm(value, context, span)
      sameKey(Interpreter.evalTerm(residual, quoteEnv), value)
    }
  }

  test("display writes symbolic powers with parenthesized form operands") {
    val x = VConst("x", Symbol, Kernel.natType)
    val a = VConst("a", Symbol, Kernel.natType)
    val b = VConst("b", Symbol, Kernel.natType)
    assertEquals(PrettyPrinter.print(pow(x, a)), "x^a")
    assert(Set("x^(a + b)", "x^(b + a)").contains(PrettyPrinter.print(pow(x, add(a, b)))))
    assertEquals(PrettyPrinter.print(pow(constant(2), a)), "2^a")
    assertEquals(PrettyPrinter.print(pow(constant(0), a)), "0^a")
    assertEquals(PrettyPrinter.print(pow(mul(constant(2), x), a)), "(2 * x)^a")
    assertEquals(PrettyPrinter.print(pow(add(x, constant(1)), a)), "(x + 1)^a")
    assertEquals(PrettyPrinter.print(pow(x, mul(constant(2), a))), "x^(2 * a)")
    assertEquals(PrettyPrinter.print(pow(pow(x, a), b)), "(x^a)^b")
    // A numeral power precedes a symbolic power of the same base.
    assertEquals(PrettyPrinter.print(pow(x, add(a, constant(2)))), "x^2 * x^a")
  }

  test("display parenthesizes sum bases") {
    val a = VConst("a", Symbol, Kernel.natType)
    val b = VConst("b", Symbol, Kernel.natType)
    val value = add(mul(constant(2), mul(a, pow(add(b, constant(1)), 2))), add(b, constant(3)))
    // Terms and factors are in key order, so only the constant's position is fixed.
    val monomials = Vector("2 * a * (b + 1)^2", "2 * (b + 1)^2 * a")
    val expected = monomials.flatMap(monomial => Vector(s"$monomial + b + 3", s"b + $monomial + 3"))
    val printed = PrettyPrinter.print(value)
    assert(expected.contains(printed), printed)
    assertEquals(PrettyPrinter.print(constant(3)), "3")
    assertEquals(PrettyPrinter.print(constant(9)), "9")
  }
}
