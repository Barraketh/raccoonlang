package com.raccoonlang

import com.raccoonlang.NatFixtures._
import com.raccoonlang.Value._

import scala.util.Random

private object NatNormalFormRandomTests {
  sealed trait Expr
  final case class Atom(index: Int) extends Expr
  final case class Num(value: Int) extends Expr
  final case class Add(left: Expr, right: Expr) extends Expr
  final case class Mul(left: Expr, right: Expr) extends Expr
  final case class Pow(base: Expr, exponent: Expr) extends Expr
  final case class Succ(predecessor: Expr) extends Expr
}

/** Seeded differential tests of Nat normal forms against arithmetic on numbers. */
class NatNormalFormRandomTests extends munit.FunSuite {
  import NatNormalFormRandomTests._

  private val atoms: Vector[Value] = Vector(fresh("a"), fresh("b"), fresh("c"))
  private val atomIndex: Map[ValueKey.Key, Int] = atoms.zipWithIndex.map { case (atom, index) =>
    atom.key -> index
  }.toMap

  private def generate(random: Random, depth: Int, exponent: Random => Expr = symbolicExponent): Expr =
    if (depth == 0 || random.nextInt(4) == 0) {
      if (random.nextInt(3) == 0) Num(random.nextInt(4)) else Atom(random.nextInt(atoms.length))
    } else
      random.nextInt(11) match {
        case 0 | 1 | 2 => Add(generate(random, depth - 1, exponent), generate(random, depth - 1, exponent))
        case 3 | 4 | 5 => Mul(generate(random, depth - 1, exponent), generate(random, depth - 1, exponent))
        case 6 | 7     => Pow(generate(random, depth - 1, exponent), Num(random.nextInt(4)))
        case 8         => Pow(generate(random, depth - 1, exponent), exponent(random))
        case _         => Succ(generate(random, depth - 1, exponent))
      }

  /** A small exponent over the atoms, at most 8 under the assignments' range, so evaluation stays bounded. */
  private def symbolicExponent(random: Random): Expr = {
    def atom = Atom(random.nextInt(atoms.length))
    random.nextInt(5) match {
      case 0 | 1 => atom
      case 2     => Add(atom, Num(random.nextInt(3)))
      case 3     => Add(atom, atom)
      case _     => Mul(Num(2), atom)
    }
  }

  /**
   * A symbolic exponent, or sometimes a product of sums, which the normal forms keep as a product and expansion
   * multiplies out, exposing a known part when both sums have one. At most 20 under the assignments' range.
   */
  private def expandingExponent(random: Random): Expr =
    if (random.nextInt(3) == 0)
      Mul(
        Add(Atom(random.nextInt(atoms.length)), Num(1)),
        Add(Atom(random.nextInt(atoms.length)), Num(random.nextInt(2)))
      )
    else symbolicExponent(random)

  private def build(expr: Expr, atomValues: Vector[Value]): Value =
    expr match {
      case Atom(index)         => atomValues(index)
      case Num(value)          => constant(value)
      case Add(left, right)    => add(build(left, atomValues), build(right, atomValues))
      case Mul(left, right)    => mul(build(left, atomValues), build(right, atomValues))
      case Pow(base, exponent) => pow(build(base, atomValues), build(exponent, atomValues))
      case Succ(predecessor)   => ConstructorValue(Kernel.succ, Vector(build(predecessor, atomValues)), Kernel.natType)
    }

  private def build(expr: Expr): Value = build(expr, atoms)

  private def evaluate(expr: Expr, assignment: Vector[BigInt]): BigInt =
    expr match {
      case Atom(index)         => assignment(index)
      case Num(value)          => value
      case Add(left, right)    => evaluate(left, assignment) + evaluate(right, assignment)
      case Mul(left, right)    => evaluate(left, assignment) * evaluate(right, assignment)
      case Pow(base, exponent) => evaluate(base, assignment).pow(evaluate(exponent, assignment).toInt)
      case Succ(predecessor)   => evaluate(predecessor, assignment) + 1
    }

  private def replaceAtom(expr: Expr, index: Int, replacement: Expr): Expr =
    expr match {
      case Atom(`index`)    => replacement
      case Atom(_) | Num(_) => expr
      case Add(left, right) => Add(replaceAtom(left, index, replacement), replaceAtom(right, index, replacement))
      case Mul(left, right) => Mul(replaceAtom(left, index, replacement), replaceAtom(right, index, replacement))
      case Pow(base, exponent) =>
        Pow(replaceAtom(base, index, replacement), replaceAtom(exponent, index, replacement))
      case Succ(predecessor) => Succ(replaceAtom(predecessor, index, replacement))
    }

  /** Rewrite by instances of the definitional laws only. */
  private def rearrange(random: Random, expr: Expr): Expr =
    expr match {
      case Atom(_) | Num(_) => expr
      case Add(Add(x, y), z) if random.nextBoolean() =>
        Add(rearrange(random, x), Add(rearrange(random, y), rearrange(random, z)))
      case Add(left, right) =>
        if (random.nextBoolean()) Add(rearrange(random, right), rearrange(random, left))
        else Add(rearrange(random, left), rearrange(random, right))
      case Mul(Mul(x, y), z) if random.nextBoolean() =>
        Mul(rearrange(random, x), Mul(rearrange(random, y), rearrange(random, z)))
      case Mul(Num(n), x) if n <= 3 && random.nextBoolean() =>
        Vector.fill(n)(rearrange(random, x)).reduceOption(Add(_, _)).getOrElse(Num(0))
      case Mul(Pow(base, first), Pow(other, second)) if base == other && random.nextBoolean() =>
        Pow(rearrange(random, base), Add(rearrange(random, first), rearrange(random, second)))
      case Mul(left, right) =>
        if (random.nextBoolean()) Mul(rearrange(random, right), rearrange(random, left))
        else Mul(rearrange(random, left), rearrange(random, right))
      case Pow(Num(1), _) if random.nextBoolean() => Num(1)
      case Pow(base, Num(exponent)) if exponent > 0 && random.nextBoolean() =>
        Mul(rearrange(random, base), Pow(rearrange(random, base), Num(exponent - 1)))
      case Pow(base, Add(first, second)) if random.nextBoolean() =>
        Mul(
          Pow(rearrange(random, base), rearrange(random, first)),
          Pow(rearrange(random, base), rearrange(random, second))
        )
      case Pow(base, Succ(predecessor)) if random.nextBoolean() =>
        Mul(Pow(rearrange(random, base), rearrange(random, predecessor)), rearrange(random, base))
      case Pow(base, exponent) => Pow(rearrange(random, base), rearrange(random, exponent))
      case Succ(predecessor) =>
        if (random.nextBoolean()) Add(Num(1), rearrange(random, predecessor)) else Succ(rearrange(random, predecessor))
    }

  /**
   * Rewrite by distributivity in either direction, `x * (y + z) = x*y + x*z` and `(y + z) * x = y*x + z*x`, at any
   * depth, including inside bases and exponents. Counts the rewrites in `distributions`.
   */
  private def distribute(random: Random, expr: Expr, distributions: Array[Int]): Expr = {
    def again(next: Expr): Expr = distribute(random, next, distributions)
    expr match {
      case Atom(_) | Num(_) => expr
      case Mul(x, Add(y, z)) if random.nextBoolean() =>
        distributions(0) += 1
        Add(Mul(again(x), again(y)), Mul(again(x), again(z)))
      case Mul(Add(y, z), x) if random.nextBoolean() =>
        distributions(0) += 1
        Add(Mul(again(y), again(x)), Mul(again(z), again(x)))
      case Add(Mul(x, y), Mul(other, z)) if x == other && random.nextBoolean() =>
        distributions(0) += 1
        Mul(again(x), Add(again(y), again(z)))
      case Add(left, right)    => Add(again(left), again(right))
      case Mul(left, right)    => Mul(again(left), again(right))
      case Pow(base, exponent) => Pow(again(base), again(exponent))
      case Succ(predecessor)   => Succ(again(predecessor))
    }
  }

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

  private def substituteNumerals(value: Value, assignment: Vector[BigInt]): Value =
    value match {
      case poly: VNatPoly => NatNormalForm.substituteAtoms(poly, atom => constant(assignment(atomIndex(atom.key))))
      case VCtor(_, _, _) => value
      case atom           => constant(assignment(atomIndex(atom.key)))
    }

  private def assignments(random: Random): Vector[Vector[BigInt]] =
    Vector.fill(8)(Vector.fill(atoms.length)(BigInt(random.nextInt(5))))

  private def stuckOn(function: VLam, value: Value): Boolean =
    value match {
      case VApp(head, _, _, _) => head eq function
      case _                   => false
    }

  private def hasSymbolicPower(expr: Expr): Boolean =
    expr match {
      case Atom(_) | Num(_)  => false
      case Add(left, right)  => hasSymbolicPower(left) || hasSymbolicPower(right)
      case Mul(left, right)  => hasSymbolicPower(left) || hasSymbolicPower(right)
      case Pow(base, Num(_)) => hasSymbolicPower(base)
      case Pow(_, _)         => true
      case Succ(predecessor) => hasSymbolicPower(predecessor)
    }

  test("rearrangements by the definitional laws share keys") {
    val random = new Random(20261027L)
    var symbolic = 0
    for (_ <- 0 until 400) {
      val expr = generate(random, 4)
      if (hasSymbolicPower(expr)) symbolic += 1
      val rearranged = rearrange(random, expr)
      assertEquals(build(rearranged).key, build(expr).key, s"$expr versus $rearranged")
    }
    assert(symbolic > 50, s"only $symbolic expressions with symbolic powers")
  }

  test("equal keys denote equal numbers, and substituting numerals evaluates") {
    val random = new Random(7L)
    val points = assignments(random)
    val byKey = scala.collection.mutable.HashMap.empty[ValueKey.Key, (Expr, Vector[BigInt])]
    var collisions = 0
    for (_ <- 0 until 600) {
      val expr = generate(random, 4)
      val value = build(expr)
      val numbers = points.map(evaluate(expr, _))
      points.zip(numbers).foreach { case (point, number) =>
        assertEquals(substituteNumerals(value, point).key, constant(number).key, s"$expr at $point")
      }
      byKey.get(value.key) match {
        case Some((earlier, earlierNumbers)) =>
          collisions += 1
          assertEquals(numbers, earlierNumbers, s"$earlier and $expr share a key")
        case None => byKey.update(value.key, (expr, numbers))
      }
    }
    assert(collisions > 0, "the generator should produce some equal forms")
  }

  test("substitution commutes with normalization") {
    val random = new Random(99L)
    for (_ <- 0 until 400) {
      val expr = generate(random, 3)
      val index = random.nextInt(atoms.length)
      val replacement = generate(random, 2)
      val replaced = atoms.updated(index, build(replacement))
      val substituted = build(expr) match {
        case poly: VNatPoly => NatNormalForm.substituteAtoms(poly, atom => replaced(atomIndex(atom.key)))
        case VCtor(_, _, _) => Kernel.zeroValue
        case atom           => replaced(atomIndex(atom.key))
      }
      assertEquals(
        substituted.key,
        build(replaceAtom(expr, index, replacement)).key,
        s"$expr with $index := $replacement"
      )
      assertEquals(substituted.key, build(expr, replaced).key)
    }
  }

  test("subtraction and comparisons agree with arithmetic whenever they decide") {
    val random = new Random(4242L)
    val points = assignments(random)
    var decided = 0
    for (_ <- 0 until 600) {
      val base = generate(random, 3)
      val other = random.nextInt(3) match {
        case 0 => generate(random, 3)
        case 1 => Add(base, generate(random, 2))
        case _ => rearrange(random, Add(generate(random, 1), base))
      }
      val (left, right) = if (random.nextBoolean()) (base, other) else (other, base)
      val leftValue = build(left)
      val rightValue = build(right)

      val difference = NatNormalForm.sub(leftValue, rightValue)
      if (!stuckOn(Kernel.sub, difference)) {
        decided += 1
        points.foreach { point =>
          val expected = (evaluate(left, point) - evaluate(right, point)).max(0)
          assertEquals(substituteNumerals(difference, point).key, constant(expected).key, s"$left - $right at $point")
        }
      }
      for (
        (result, holds) <- Vector(
          NatNormalForm.beq(leftValue, rightValue) -> ((l: BigInt, r: BigInt) => l == r),
          NatNormalForm.ble(leftValue, rightValue) -> ((l: BigInt, r: BigInt) => l <= r)
        )
      ) {
        val decision =
          if (result.key == Kernel.trueValue.key) Some(true)
          else if (result.key == Kernel.falseValue.key) Some(false)
          else None
        decision.foreach { expected =>
          decided += 1
          points.foreach { point =>
            assertEquals(holds(evaluate(left, point), evaluate(right, point)), expected, s"$left, $right at $point")
          }
        }
      }
    }
    assert(decided > 300, s"only $decided decisions")
  }

  test("division and remainder agree with arithmetic, and substitution commutes with them") {
    val random = new Random(31337L)
    val points = assignments(random)
    val variables = atoms.collect { case variable: Var => variable }
    def solving(links: Vector[(Var, Value)]): EqStore =
      links.foldLeft(EqStore.empty.allow(DepSet(links.map(_._1.id): _*))) { case (store, (variable, value)) =>
        store.addLink(variable.id, value)
      }
    // Numerals 0 and 1 reduce an open application, and 2 does not.
    def operand(): Expr = if (random.nextInt(3) == 0) Num(random.nextInt(3)) else generate(random, 2)
    val operations = Vector[(VLam, (Value, Value) => Value, (BigInt, BigInt) => BigInt)](
      (Kernel.div, NatNormalForm.div, (a, b) => if (b == 0) 0 else a / b),
      (Kernel.mod, NatNormalForm.mod, (a, b) => if (b == 0) a else a % b)
    )
    var reduced = 0
    var stuck = 0
    for (_ <- 0 until 300; (function, operation, arithmetic) <- operations) {
      val dividend = operand()
      val divisor = operand()
      val result = operation(build(dividend), build(divisor))
      if (stuckOn(function, result)) stuck += 1 else reduced += 1
      // Solving every atom as a numeral resumes a stuck application and evaluates a reduced one.
      points.foreach { point =>
        val expected = arithmetic(evaluate(dividend, point), evaluate(divisor, point))
        assertEquals(
          ValueOps.materialize(result, solving(variables.zip(point.map(constant)))).key,
          constant(expected).key,
          s"$dividend, $divisor at $point"
        )
      }
      // Solving one atom as an expression over the others gives the operation of the substituted arguments.
      val index = random.nextInt(atoms.length)
      val replacement = replaceAtom(generate(random, 2), index, Num(2))
      assertEquals(
        ValueOps.materialize(result, solving(Vector(variables(index) -> build(replacement)))).key,
        operation(
          build(replaceAtom(dividend, index, replacement)),
          build(replaceAtom(divisor, index, replacement))
        ).key,
        s"$dividend, $divisor with $index := $replacement"
      )
    }
    assert(reduced > 100 && stuck > 100, s"$reduced reduced and $stuck stuck")
  }

  test("expansion preserves value, multiplies every sum out, and is its own expansion") {
    val random = new Random(5150L)
    val points = assignments(random)
    var changed = 0
    for (_ <- 0 until 400) {
      val expr = generate(random, 4, expandingExponent)
      val value = build(expr)
      val expanded = NatNormalForm.expansion(value)
      if (!(expanded eq value)) changed += 1
      assert(distributed(expanded), s"$expr expands to $expanded")
      assert(NatNormalForm.expansion(expanded) eq expanded, s"$expr")
      points.foreach { point =>
        assertEquals(substituteNumerals(expanded, point).key, constant(evaluate(expr, point)).key, s"$expr at $point")
      }
    }
    assert(changed > 100, s"only $changed expressions changed")
  }

  test("expressions equal by distributivity and the definitional laws have identical expansions") {
    val random = new Random(8086L)
    val distributions = Array(0)
    var distinctForms = 0
    for (_ <- 0 until 1000) {
      val expr = generate(random, 4, expandingExponent)
      val rewritten = rearrange(random, distribute(random, expr, distributions))
      if (build(rewritten).key != build(expr).key) distinctForms += 1
      assertEquals(
        NatNormalForm.expansion(build(rewritten)).key,
        NatNormalForm.expansion(build(expr)).key,
        s"$expr versus $rewritten"
      )
    }
    assert(distributions(0) > 150 && distinctForms > 75, s"${distributions(0)} rewrites, $distinctForms distinct")
  }

  test("an open Nat.expand resumes under substitution to Nat.expand of the substituted argument") {
    val random = new Random(6502L)
    val points = assignments(random)
    val variables = atoms.collect { case variable: Var => variable }
    def solving(links: Vector[(Var, Value)]): EqStore =
      links.foldLeft(EqStore.empty.allow(DepSet(links.map(_._1.id): _*))) { case (store, (variable, value)) =>
        store.addLink(variable.id, value)
      }
    var open = 0
    for (_ <- 0 until 300) {
      val expr = generate(random, 3, expandingExponent)
      val result = NatNormalForm.expand(build(expr))
      if (termCount(result) > 0 || stuckOn(Kernel.expand, result)) open += 1
      points.foreach { point =>
        assertEquals(
          ValueOps.materialize(result, solving(variables.zip(point.map(constant)))).key,
          constant(evaluate(expr, point)).key,
          s"$expr at $point"
        )
      }
      val index = random.nextInt(atoms.length)
      val replacement = replaceAtom(generate(random, 2), index, Num(2))
      assertEquals(
        ValueOps.materialize(result, solving(Vector(variables(index) -> build(replacement)))).key,
        NatNormalForm.expand(build(replaceAtom(expr, index, replacement))).key,
        s"$expr with $index := $replacement"
      )
    }
    assert(open > 200, s"only $open open expansions")
  }
}
