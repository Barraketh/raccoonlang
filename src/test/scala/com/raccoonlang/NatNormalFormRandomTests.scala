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

  private def generate(random: Random, depth: Int): Expr =
    if (depth == 0 || random.nextInt(4) == 0) {
      if (random.nextInt(3) == 0) Num(random.nextInt(4)) else Atom(random.nextInt(atoms.length))
    } else
      random.nextInt(11) match {
        case 0 | 1 | 2 => Add(generate(random, depth - 1), generate(random, depth - 1))
        case 3 | 4 | 5 => Mul(generate(random, depth - 1), generate(random, depth - 1))
        case 6 | 7     => Pow(generate(random, depth - 1), Num(random.nextInt(4)))
        case 8         => Pow(generate(random, depth - 1), symbolicExponent(random))
        case _         => Succ(generate(random, depth - 1))
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
}
