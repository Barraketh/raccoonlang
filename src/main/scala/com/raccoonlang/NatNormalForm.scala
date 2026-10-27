package com.raccoonlang

import com.raccoonlang.Value._

import scala.annotation.tailrec
import scala.collection.mutable

/**
 * Canonical sums of products for the kernel's Nat; docs/nat-normal-forms.md is the design. Addition and multiplication
 * are associative and commutative with units, `0 * x = 0`, closed arithmetic computes, and multiplying by a numeral
 * distributes. Powers of equal bases multiply by adding exponents, symbolic or not, and `1^e = 1`. Nothing symbolic
 * distributes, so a product of sums stays a product whose factors are the sums, and a power of a product stays a power.
 * Each operation does work linear in its operands and result, plus sorting factor bases and computing gcds.
 */
private[raccoonlang] object NatNormalForm {

  /**
   * A base raised to an exponent. The base and a symbolic exponent are the factor's operands: arguments of the Nat
   * operations, which substitution, alignment, metadata, and positivity visit.
   */
  sealed abstract class Factor {
    def base: Value
  }

  /**
   * A base raised to a positive known exponent. The base is an atom, a Nat value that is neither zero nor a `VNatPoly`,
   * or a primitive sum: the published value of a form with content one and at least two summands.
   */
  final class NumeralPower private[NatNormalForm] (val base: Value, val exponent: BigInt) extends Factor

  /**
   * A base raised to a symbolic exponent: a published Nat value with zero constant and at least one term. The base is
   * any Nat value except one, including zero, numerals, and products, and is never split or content-extracted, because
   * a power of a product is not a product of powers. A known part of an exponent is a separate numeral power (see
   * `Product.multiplyPower`).
   */
  final class SymbolicPower private[NatNormalForm] (val base: Value, val exponent: Value) extends Factor

  /**
   * Monomial order: base key, then a numeral power before a symbolic power. Factors equal in this order have the same
   * base and kind, so a product merges them by adding exponents.
   */
  private val factorOrder: java.util.Comparator[Factor] = (left: Factor, right: Factor) => {
    val compare = ValueKey.Key.ordering.compare(left.base.key, right.base.key)
    if (compare != 0) compare else Integer.compare(kindRank(left), kindRank(right))
  }

  private def kindRank(factor: Factor): Int =
    factor match {
      case _: NumeralPower  => 0
      case _: SymbolicPower => 1
    }

  /** The product of two factors equal in `factorOrder`. */
  private def mergeFactors(left: Factor, right: Factor): Factor =
    left match {
      case power: NumeralPower =>
        new NumeralPower(power.base, power.exponent + right.asInstanceOf[NumeralPower].exponent)
      case power: SymbolicPower =>
        new SymbolicPower(power.base, add(power.exponent, right.asInstanceOf[SymbolicPower].exponent))
    }

  /**
   * Raise a factor to a known exponent greater than one. A symbolic exponent is scaled, so `(x^a)^2 = x^(2*a)` agrees
   * with `x^a * x^a`; the scaled exponent keeps zero constant and its terms.
   */
  private def raiseFactor(factor: Factor, exponent: BigInt): Factor =
    factor match {
      case power: NumeralPower  => new NumeralPower(power.base, power.exponent * exponent)
      case power: SymbolicPower => new SymbolicPower(power.base, scale(fromValue(power.exponent), exponent).toValue)
    }

  /**
   * Nonempty factors in `factorOrder`, no two equal in it. A monomial is never a single primitive sum with numeral
   * exponent one; such a product is the sum's summands scaled by the coefficient (see `Product.result`).
   */
  final class Monomial private[NatNormalForm] (val factors: Vector[Factor]) {
    lazy val key: ValueKey.Key = ValueKey.natMonomialKey(factors)
  }

  /** A positive coefficient times a monomial. */
  final class Term private[NatNormalForm] (val coefficient: BigInt, val monomial: Monomial)

  /**
   * Terms with distinct monomials in key order, shared by forms that differ only in their constant, such as successors
   * and predecessors. `synDeps` and `needsStructuralDefEq` summarize the distinct operands; sums and products derive
   * them from their operands' metadata, which equals the result's because nothing cancels: a merged exponent carries
   * the union of its parts' metadata, and a base of one or an exponent of zero contributes no factor.
   */
  private final class Terms(val values: Vector[Term], val synDeps: DepSet, val needsStructuralDefEq: Boolean) {
    lazy val key: ValueKey.Key = ValueKey.natTermsKey(values)

    /** Distinct factor bases and symbolic exponents in first-occurrence order. */
    lazy val operands: Vector[Value] = {
      val seen = mutable.HashSet.empty[ValueKey.Key]
      val distinct = Vector.newBuilder[Value]
      foreachOperand(values)(operand => if (seen.add(operand.key)) distinct += operand)
      distinct.result()
    }

    /** Distinct atoms, including atoms inside operands that are forms. Zero is not an atom. */
    lazy val leafAtoms: Vector[Value] = {
      val seen = mutable.HashSet.empty[ValueKey.Key]
      val atoms = Vector.newBuilder[Value]
      operands.foreach {
        case poly: VNatPoly => poly.form.shared.leafAtoms.foreach(atom => if (seen.add(atom.key)) atoms += atom)
        case VCtor(_, _, _) => ()
        case atom           => if (seen.add(atom.key)) atoms += atom
      }
      atoms.result()
    }

    /** Zero when there are no terms. */
    lazy val coefficientGcd: BigInt = values.foldLeft(BigInt(0))((gcd, term) => gcd.gcd(term.coefficient))
  }

  private object Terms {
    val empty: Terms = new Terms(Vector.empty, DepSet.empty, false)

    /** Terms whose metadata cannot be derived from operands, such as what remains after cancellation. */
    def collected(values: Vector[Term]): Terms =
      if (values.isEmpty) empty
      else {
        val operands = mutable.ArrayBuffer.empty[Value]
        foreachOperand(values)(operands += _)
        new Terms(values, DepSet.unionAll(operands.map(_.synDeps)), operands.exists(_.needsStructuralDefEq))
      }
  }

  /** Each factor's base, then its exponent when symbolic, with repetitions. */
  private def foreachOperand(values: Vector[Term])(visit: Value => Unit): Unit =
    values.foreach(_.monomial.factors.foreach { factor =>
      visit(factor.base)
      factor match {
        case power: SymbolicPower => visit(power.exponent)
        case _: NumeralPower      => ()
      }
    })

  /** A nonnegative constant plus terms. Only this module constructs forms. */
  final class Form private[NatNormalForm] (val constant: BigInt, private[NatNormalForm] val shared: Terms) {
    def terms: Vector[Term] = shared.values

    def synDeps: DepSet = shared.synDeps

    def needsStructuralDefEq: Boolean = shared.needsStructuralDefEq

    def termsKey: ValueKey.Key = shared.key

    /**
     * Distinct factor bases and symbolic exponents: the arguments of the Nat operations. An operand that is a
     * `VNatPoly` has operands of its own.
     */
    def operands: Vector[Value] = shared.operands

    private[NatNormalForm] def isZeroForm: Boolean = constant == 0 && terms.isEmpty

    /** The gcd of the constant and the coefficients. Requires a form with terms; numerals are handled separately. */
    private[NatNormalForm] lazy val content: BigInt = shared.coefficientGcd.gcd(constant)

    /** This form divided by its content; the form itself when the content is one. Requires a form with terms. */
    private[NatNormalForm] lazy val primitive: Form =
      if (content == 1) this
      else
        new Form(
          constant / content,
          new Terms(
            terms.map(term => new Term(term.coefficient / content, term.monomial)),
            synDeps,
            needsStructuralDefEq
          )
        )

    /**
     * The single publication boundary: zero is `Nat.zero`, a lone atom with coefficient and numeral exponent one is the
     * atom, and anything else is a `VNatPoly` of this form. Cached, so a published sum is the value of its own form.
     */
    private[NatNormalForm] lazy val toValue: Value =
      if (isZeroForm) Kernel.zeroValue
      else if (
        constant == 0 && terms.length == 1 && terms.head.coefficient == 1 && terms.head.monomial.factors.length == 1
      )
        terms.head.monomial.factors.head match {
          // A single primitive sum with exponent one is never a monomial, so this base is an atom.
          case power: NumeralPower if power.exponent == 1 => power.base
          case _                                          => new Value.VNatPoly(this)
        }
      else new Value.VNatPoly(this)

    /** Subtract a known constructor prefix, sharing the terms. Requires 0 <= count <= constant. */
    private[NatNormalForm] def dropPrefix(count: BigInt): Form =
      if (count == 0) this else new Form(constant - count, shared)
  }

  private val Zero = new Form(0, Terms.empty)
  private val One = new Form(1, Terms.empty)

  private def numeral(value: BigInt): Form =
    if (value == 0) Zero else if (value == 1) One else new Form(value, Terms.empty)

  private def atomForm(atom: Value): Form = new Form(0, atomTerms(atom))

  private def atomTerms(atom: Value): Terms =
    new Terms(
      Vector(new Term(1, new Monomial(Vector(new NumeralPower(atom, 1))))),
      atom.synDeps,
      atom.needsStructuralDefEq
    )

  /** Conversion may compare values of different types; only Nat values have normal forms. */
  private def isNat(value: Value): Boolean =
    ValueEquivalence.defEq(value.tpe, Kernel.natType)

  /** Nat's only stored constructor is zero. */
  private def isZeroValue(value: Value): Boolean =
    value match {
      case VCtor(_, _, _) => true
      case _              => false
    }

  private def isUnitValue(value: Value): Boolean =
    value match {
      case poly: VNatPoly => poly.form.constant == 1 && poly.form.terms.isEmpty
      case _              => false
    }

  /** Lift a Nat value. Successors are compact (see ConstructorValue), so any other non-form value is an atom. */
  private def fromValue(value: Value): Form =
    value match {
      case poly: VNatPoly => poly.form
      case VCtor(_, _, _) => Zero
      case atom           => atomForm(atom)
    }

  /** Add a known amount; the terms are shared. */
  private def addConstant(form: Form, amount: BigInt): Form =
    if (amount == 0) form else new Form(form.constant + amount, form.shared)

  /** Merge the sorted terms of both forms, adding the coefficients of equal monomials and the constants. */
  private def addForms(left: Form, right: Form): Form =
    if (left.terms.isEmpty) addConstant(right, left.constant)
    else if (right.terms.isEmpty) addConstant(left, right.constant)
    else {
      val merged = Vector.newBuilder[Term]
      var leftIndex = 0
      var rightIndex = 0
      while (leftIndex < left.terms.length && rightIndex < right.terms.length) {
        val leftTerm = left.terms(leftIndex)
        val rightTerm = right.terms(rightIndex)
        val compare = ValueKey.Key.ordering.compare(leftTerm.monomial.key, rightTerm.monomial.key)
        if (compare < 0) {
          merged += leftTerm
          leftIndex += 1
        } else if (compare > 0) {
          merged += rightTerm
          rightIndex += 1
        } else {
          merged += new Term(leftTerm.coefficient + rightTerm.coefficient, leftTerm.monomial)
          leftIndex += 1
          rightIndex += 1
        }
      }
      while (leftIndex < left.terms.length) {
        merged += left.terms(leftIndex)
        leftIndex += 1
      }
      while (rightIndex < right.terms.length) {
        merged += right.terms(rightIndex)
        rightIndex += 1
      }
      new Form(
        left.constant + right.constant,
        new Terms(
          merged.result(),
          left.synDeps ++ right.synDeps,
          left.needsStructuralDefEq || right.needsStructuralDefEq
        )
      )
    }

  /** Sum in a balanced tree, so each term is merged a logarithmic number of times. Reuses `parts` as scratch space. */
  private def sumAll(parts: mutable.ArrayBuffer[Form]): Form = {
    if (parts.isEmpty) return Zero
    var width = parts.length
    while (width > 1) {
      var next = 0
      var index = 0
      while (index + 1 < width) {
        parts(next) = addForms(parts(index), parts(index + 1))
        next += 1
        index += 2
      }
      if (index < width) {
        parts(next) = parts(index)
        next += 1
      }
      width = next
    }
    parts(0)
  }

  /** Adding zero returns the other operand without lifting either. */
  def add(left: Value, right: Value): Value =
    if (isZeroValue(right)) left
    else if (isZeroValue(left)) right
    else addForms(fromValue(left), fromValue(right)).toValue

  /** Multiply every coefficient and the constant by a numeral, keeping the monomials and their order. */
  private def scale(form: Form, scalar: BigInt): Form =
    if (scalar == 0) Zero
    else if (scalar == 1) form
    else
      new Form(
        form.constant * scalar,
        new Terms(
          form.terms.map(term => new Term(term.coefficient * scalar, term.monomial)),
          form.synDeps,
          form.needsStructuralDefEq
        )
      )

  /**
   * A known power of a numeral. A base of at least two with an exponent beyond an Int, or a result beyond what a JVM
   * integer can hold, is a representation limit rather than a budget.
   */
  private def numeralPower(base: BigInt, exponent: BigInt): BigInt =
    if (exponent == 0) 1
    else if (base <= 1) base
    else if (!exponent.isValidInt) throw NatValueTooLarge(exponent)
    else
      try base.pow(exponent.toInt)
      catch { case _: ArithmeticException => throw NatValueTooLarge(exponent) }

  /**
   * One n-ary product of a coefficient and powers of Nat values. A numeral multiplies the coefficient. Any other form
   * raised to a known exponent contributes its content to the coefficient and its primitive part's factors: those of a
   * single monomial, or the primitive part itself as a sum factor. A symbolic exponent contributes a symbolic power of
   * the whole base. Once the coefficient is zero the product is zero, so later operands are skipped, and known powers
   * of numerals are computed only at the end, so a zero operand wins regardless of operand order.
   */
  private final class Product(private var coefficient: BigInt) {
    private val factors = mutable.ArrayBuffer.empty[Factor]
    private val depSources = mutable.ArrayBuffer.empty[DepSet]
    private var structural = false
    // Known powers of numerals of at least two wait for `result`, so a zero operand makes the product zero whatever the
    // operand order, rather than a power too large to represent raising first. Allocated on first use.
    private var numeralPowers: mutable.ArrayBuffer[(BigInt, BigInt)] = null

    /** Multiply the coefficient by `base^exponent` for a positive exponent. */
    private def multiplyNumeral(base: BigInt, exponent: BigInt): Unit =
      if (base == 0) coefficient = 0
      else if (base != 1) {
        if (exponent == 1) coefficient *= base
        else {
          if (numeralPowers eq null) numeralPowers = mutable.ArrayBuffer.empty
          numeralPowers += ((base, exponent))
        }
      }

    /** Multiply by `form^exponent` for a positive exponent. */
    def multiply(form: Form, exponent: BigInt): Unit =
      if (coefficient != 0) {
        if (form.terms.isEmpty) multiplyNumeral(form.constant, exponent)
        else {
          multiplyNumeral(form.content, exponent)
          val primitive = form.primitive
          if (primitive.constant == 0 && primitive.terms.length == 1)
            primitive.terms.head.monomial.factors.foreach { factor =>
              factors += (if (exponent == 1) factor else raiseFactor(factor, exponent))
            }
          else factors += new NumeralPower(primitive.toValue, exponent)
          depSources += form.synDeps
          structural ||= form.needsStructuralDefEq
        }
      }

    /** Multiply by a Nat value raised to a positive exponent, without lifting an atom into a form. */
    def multiplyValue(value: Value, exponent: BigInt): Unit =
      value match {
        case poly: VNatPoly => multiply(poly.form, exponent)
        case VCtor(_, _, _) => coefficient = 0 // Nat's only stored constructor is zero
        case atom =>
          if (coefficient != 0) {
            factors += new NumeralPower(atom, exponent)
            depSources += atom.synDeps
            structural ||= atom.needsStructuralDefEq
          }
      }

    /**
     * Multiply by `base^exponent` for any Nat exponent `e + k` with known part k: `base^k`, then the symbolic power of
     * the whole base to `e`. So a zero base with positive k makes the product zero.
     */
    def multiplyPower(base: Value, exponent: Value): Unit =
      exponent match {
        case poly: VNatPoly =>
          val form = poly.form
          if (form.constant > 0) multiplyValue(base, form.constant)
          if (form.terms.nonEmpty)
            multiplySymbolic(base, if (form.constant == 0) poly else form.dropPrefix(form.constant).toValue)
        case VCtor(_, _, _) => () // x^0 = 1
        case atom           => multiplySymbolic(base, atom)
      }

    /** Multiply by `base^exponent` for an exponent with zero constant and terms; `1^e = 1` adds no factor. */
    private def multiplySymbolic(base: Value, exponent: Value): Unit =
      if (coefficient != 0 && !isUnitValue(base)) {
        factors += new SymbolicPower(base, exponent)
        depSources += base.synDeps
        depSources += exponent.synDeps
        structural ||= base.needsStructuralDefEq || exponent.needsStructuralDefEq
      }

    /** A binary product is the common case, where one union is cheaper than an aggregation. */
    private def deps: DepSet =
      depSources.length match {
        case 1 => depSources(0)
        case 2 => depSources(0) ++ depSources(1)
        case _ => DepSet.unionAll(depSources)
      }

    /**
     * Sort the factor occurrences in `factorOrder` and merge equal ones by adding exponents. A lone sum with numeral
     * exponent one, which arises only when every other operand was a numeral, is published as the scaled sum.
     */
    def result(): Form =
      if (coefficient == 0) Zero
      else {
        if (numeralPowers ne null)
          numeralPowers.foreach { case (base, exponent) => coefficient *= numeralPower(base, exponent) }
        if (factors.isEmpty) numeral(coefficient) else monomialResult()
      }

    /** The single term over the collected factors; requires a nonzero coefficient and at least one factor. */
    private def monomialResult(): Form = {
      val sorted = factors.toArray
      // TimSort merges presorted runs linearly, so a product of two monomials costs a merge.
      java.util.Arrays.sort(sorted, factorOrder)
      val merged = Vector.newBuilder[Factor]
      var current = sorted(0)
      var index = 1
      while (index < sorted.length) {
        val next = sorted(index)
        // Equal in `factorOrder`, tested by equality, which is cheaper than the unsigned comparison.
        if (next.base.key == current.base.key && kindRank(next) == kindRank(current))
          current = mergeFactors(current, next)
        else {
          merged += current
          current = next
        }
        index += 1
      }
      merged += current
      val monomial = merged.result()
      monomial.head match {
        case power: NumeralPower if monomial.length == 1 && power.exponent == 1 && power.base.isInstanceOf[VNatPoly] =>
          scale(fromValue(power.base), coefficient)
        case _ =>
          new Form(0, new Terms(Vector(new Term(coefficient, new Monomial(monomial))), deps, structural))
      }
    }
  }

  /** Multiplying by zero or one returns without lifting either operand; a numeral scales the other operand. */
  def mul(left: Value, right: Value): Value =
    if (isZeroValue(left)) left
    else if (isZeroValue(right)) right
    else if (isUnitValue(right)) left
    else if (isUnitValue(left)) right
    else
      (left, right) match {
        case (poly: VNatPoly, other) if poly.form.terms.isEmpty => scale(fromValue(other), poly.form.constant).toValue
        case (other, poly: VNatPoly) if poly.form.terms.isEmpty => scale(fromValue(other), poly.form.constant).toValue
        case _ =>
          val product = new Product(1)
          product.multiplyValue(left, 1)
          product.multiplyValue(right, 1)
          product.result().toValue
      }

  /** Raise to a known exponent: repeated multiplication, so content and exponents multiply. */
  private def power(base: Form, exponent: BigInt): Form =
    if (exponent == 0) One
    else if (exponent == 1) base
    else {
      val product = new Product(1)
      product.multiply(base, exponent)
      product.result()
    }

  /** Quotation produces literals only from constants of evaluated values, which are nonnegative. */
  def literal(value: BigInt): Value = {
    require(value >= 0, s"Nat constant $value is negative")
    numeral(value).toValue
  }

  /**
   * A known exponent computes. A symbolic exponent `e + k` gives `base^k` times the symbolic power of the whole base to
   * `e`, so equal bases add exponents (`x^a * x^b = x^(a+b)`), `1^e = 1`, and `0^(e+1) = 0`.
   */
  def pow(base: Value, exponent: Value): Value =
    exponent match {
      case poly: VNatPoly if poly.form.terms.isEmpty => power(fromValue(base), poly.form.constant).toValue
      case VCtor(_, _, _)                            => One.toValue
      case _ =>
        val product = new Product(1)
        product.multiplyPower(base, exponent)
        product.result().toValue
    }

  /** The compact successor of any Nat value; an atom's successor shares no intermediate form. */
  def successor(value: Value): Value =
    value match {
      case poly: VNatPoly => addConstant(poly.form, 1).toValue
      case VCtor(_, _, _) => One.toValue
      case atom           => new Form(1, atomTerms(atom)).toValue
    }

  /** The predecessor of a form with a known successor. */
  def predecessor(poly: VNatPoly): Option[Value] =
    if (poly.form.constant == 0) None else Some(poly.form.dropPrefix(1).toValue)

  /**
   * Rebuild `form` through the operations with each distinct atom, including atoms inside operands that are forms,
   * replaced once by `replace`, which must preserve the Nat type. Returns `form` itself when no atom changes. Unchanged
   * terms keep their order; each changed monomial is rebuilt as one n-ary product, which drops a term whose numeral
   * power base became zero, drops a symbolic power whose base became one or whose exponent became zero, and splits an
   * exponent that gained a constant.
   */
  private def substitute(form: Form, replace: Value => Value): Form = {
    val replaced = mutable.HashMap.empty[ValueKey.Key, Value]

    def replaceOperand(operand: Value): Value =
      replaced.getOrElse(operand.key, null) match { // unlike get, allocates no Some
        case null =>
          val next = operand match {
            case poly: VNatPoly =>
              val rebuilt = rebuild(poly.form)
              if (rebuilt eq poly.form) poly else rebuilt.toValue
            case VCtor(_, _, _) => operand // zero is not an atom
            case atom           => replace(atom)
          }
          replaced.update(operand.key, next)
          next
        case known => known
      }

    // Both lookups follow `rebuild`'s pass over the source's operands.
    def unchanged(operand: Value): Boolean = replaced(operand.key) eq operand

    def factorUnchanged(factor: Factor): Boolean =
      factor match {
        case power: NumeralPower  => unchanged(power.base)
        case power: SymbolicPower => unchanged(power.base) && unchanged(power.exponent)
      }

    def rebuild(source: Form): Form = {
      var changed = false
      source.operands.foreach(operand => if (!(replaceOperand(operand) eq operand)) changed = true)
      if (!changed) source
      else {
        val unchangedTerms = Vector.newBuilder[Term]
        val parts = mutable.ArrayBuffer[Form](numeral(source.constant))
        source.terms.foreach { term =>
          val factors = term.monomial.factors
          if (factors.forall(factorUnchanged)) unchangedTerms += term
          else {
            val product = new Product(term.coefficient)
            factors.foreach {
              case power: NumeralPower => product.multiplyValue(replaced(power.base.key), power.exponent)
              case power: SymbolicPower =>
                product.multiplyPower(replaced(power.base.key), replaced(power.exponent.key))
            }
            parts += product.result()
          }
        }
        parts += new Form(0, Terms.collected(unchangedTerms.result()))
        sumAll(parts)
      }
    }

    rebuild(form)
  }

  /** Callers supply replacements that preserve the Nat type; `ValueOps.materialize` owns transitive substitution. */
  def substituteAtoms(poly: VNatPoly, replace: Value => Value): Value = {
    val result = substitute(poly.form, replace)
    if (result eq poly.form) poly else result.toValue
  }

  /**
   * Map the leaf atoms of both forms to definitionally equal representatives, without refinement, keeping only atoms
   * that change. Ordinary atoms only search structural representatives, since two ordinary atoms convert exactly when
   * their keys are equal; structural atoms search every representative.
   */
  private def atomAliases(left: Form, right: Form): scala.collection.Map[ValueKey.Key, Value] = {
    val byKey = mutable.HashMap.empty[ValueKey.Key, Value]
    val structuralRepresentatives = mutable.ArrayBuffer.empty[Value]
    val ordinaryRepresentatives = mutable.ArrayBuffer.empty[Value]
    def represent(atom: Value): Unit =
      if (!byKey.contains(atom.key)) {
        val candidates =
          if (atom.needsStructuralDefEq) structuralRepresentatives.iterator ++ ordinaryRepresentatives.iterator
          else structuralRepresentatives.iterator
        val equivalent = candidates.find(candidate => ValueEquivalence.defEq(candidate, atom))
        byKey.update(atom.key, equivalent.getOrElse(atom))
        if (equivalent.isEmpty) {
          if (atom.needsStructuralDefEq) structuralRepresentatives += atom
          else ordinaryRepresentatives += atom
        }
      }

    left.shared.leafAtoms.foreach(represent)
    right.shared.leafAtoms.foreach(represent)
    byKey.filterInPlace((key, representative) => key != representative.key)
    byKey
  }

  /** Rebuild both forms over one representative per class of definitionally equal atoms; constants are unchanged. */
  private def align(left: Form, right: Form): (Form, Form) = {
    val aliases = atomAliases(left, right)
    if (aliases.isEmpty) (left, right)
    else {
      def representative(atom: Value): Value = aliases.getOrElse(atom.key, atom)
      (substitute(left, representative), substitute(right, representative))
    }
  }

  /** Callers have established that the terms' keys differ, so only aligning convertible atoms can equate them. */
  private def alignedTermsEqual(left: Form, right: Form): Boolean = {
    val (a, b) = align(left, right)
    ((a ne left) || (b ne right)) && a.termsKey == b.termsKey
  }

  /**
   * Conversion for a pair with at least one form; atoms are never unified or refined here. Conversion calls this only
   * after the keys differ and some atom needs structural conversion, so equal constants imply different terms.
   */
  def equivalent(left: Value, right: Value): Boolean =
    isNat(left) && isNat(right) && {
      val leftForm = fromValue(left)
      val rightForm = fromValue(right)
      leftForm.constant == rightForm.constant && alignedTermsEqual(leftForm, rightForm)
    }

  /**
   * Cancel the common part over the same atom equivalence as conversion. Shared or equal terms cancel without comparing
   * atoms; with no terms on one side, or only key-comparable atoms, key cancellation suffices.
   */
  private def cancelCommon(left: Form, right: Form): (Form, Form) =
    if (left.shared eq right.shared) cancelConstants(left.constant, right.constant)
    else if (left.terms.isEmpty || right.terms.isEmpty || !(left.needsStructuralDefEq || right.needsStructuralDefEq))
      cancelByKey(left, right)
    else if (left.termsKey == right.termsKey) cancelConstants(left.constant, right.constant)
    else {
      val (a, b) = align(left, right)
      cancelByKey(a, b)
    }

  private def cancelConstants(left: BigInt, right: BigInt): (Form, Form) =
    if (left >= right) (numeral(left - right), Zero)
    else (Zero, numeral(right - left))

  /**
   * Remove the coefficient-wise common part of whole terms by monomial key, leaving forms that share no monomial and at
   * most one of which has a positive constant. Sum factors are opaque here.
   */
  private def cancelByKey(left: Form, right: Form): (Form, Form) = {
    val common = left.constant.min(right.constant)
    val leftTerms = Vector.newBuilder[Term]
    val rightTerms = Vector.newBuilder[Term]
    var cancelled = false
    var leftIndex = 0
    var rightIndex = 0
    while (leftIndex < left.terms.length && rightIndex < right.terms.length) {
      val leftTerm = left.terms(leftIndex)
      val rightTerm = right.terms(rightIndex)
      val compare = ValueKey.Key.ordering.compare(leftTerm.monomial.key, rightTerm.monomial.key)
      if (compare < 0) {
        leftTerms += leftTerm
        leftIndex += 1
      } else if (compare > 0) {
        rightTerms += rightTerm
        rightIndex += 1
      } else {
        cancelled = true
        val coefficient = leftTerm.coefficient.min(rightTerm.coefficient)
        if (leftTerm.coefficient > coefficient)
          leftTerms += new Term(leftTerm.coefficient - coefficient, leftTerm.monomial)
        if (rightTerm.coefficient > coefficient)
          rightTerms += new Term(rightTerm.coefficient - coefficient, rightTerm.monomial)
        leftIndex += 1
        rightIndex += 1
      }
    }
    if (!cancelled) (left.dropPrefix(common), right.dropPrefix(common))
    else {
      leftTerms ++= left.terms.iterator.drop(leftIndex)
      rightTerms ++= right.terms.iterator.drop(rightIndex)
      (
        new Form(left.constant - common, Terms.collected(leftTerms.result())),
        new Form(right.constant - common, Terms.collected(rightTerms.result()))
      )
    }
  }

  /** A native application whose result is unknown until a dependency of its arguments is solved. */
  private def stuck(function: VLam, result: Value, arg: Value): Value =
    VBlockedApp(function, Vector(arg), result, arg.synDeps)

  private def stuck(function: VLam, result: Value, first: Value, second: Value): Value =
    VBlockedApp(function, Vector(first, second), result, first.synDeps ++ second.synDeps)

  /**
   * Truncated subtraction. Its result depends only on the signed difference: `a - b` reduces to the positive part when
   * the negative part is zero, to zero when the positive part is, and otherwise stays stuck on both parts. A stuck
   * difference absorbs a known constant, since `(p - q) - c = p - (q + c)`, so `sub(a, succ(b)) = pred(sub(a, b))`.
   *
   * Absorption is limited to constants so that results are stable under substitution: `sub(sub(p, q), c)` and
   * `sub(p, q + c)` cancel to the same parts for every instance of p and q. Absorbing a symbolic subtrahend would hide
   * the stuck difference as an atom; `sub(sub(a, b), x)` with `x := sub(a, b)` must still reduce to zero.
   */
  def sub(left: Value, right: Value): Value = subtractForms(fromValue(left), fromValue(right))

  @tailrec
  private def subtractForms(left: Form, right: Form): Value = {
    val (positive, negative) = cancelCommon(left, right)
    if (negative.isZeroForm) positive.toValue
    else if (positive.isZeroForm) Kernel.zeroValue
    else
      positive.toValue match {
        case VApp(head, Vector(minuend, subtrahend), _, _) if (head eq Kernel.sub) && negative.terms.isEmpty =>
          subtractForms(fromValue(minuend), addConstant(fromValue(subtrahend), negative.constant))
        case minuend => stuck(Kernel.sub, Kernel.natType, minuend, negative.toValue)
      }
  }

  def pred(value: Value): Value = sub(value, One.toValue)

  def isZero(value: Value): Value =
    value match {
      case VCtor(_, _, _)                           => Kernel.trueValue
      case poly: VNatPoly if poly.form.constant > 0 => Kernel.falseValue
      case _                                        => stuck(Kernel.isZero, Kernel.boolType, value)
    }

  /**
   * Boolean equality of the signed difference's parts. Comparing with zero is `isZero`, and a stuck comparison orders
   * its parts by key, since equality is symmetric.
   */
  def beq(left: Value, right: Value): Value = {
    val (positive, negative) = cancelCommon(fromValue(left), fromValue(right))
    if (positive.isZeroForm) isZero(negative.toValue)
    else if (negative.isZeroForm) isZero(positive.toValue)
    else {
      val (first, second) =
        if (ValueKey.Key.ordering.compare(positive.toValue.key, negative.toValue.key) <= 0) (positive, negative)
        else (negative, positive)
      stuck(Kernel.beq, Kernel.boolType, first.toValue, second.toValue)
    }
  }

  /** `a <= b` holds when the positive part of `a - b` is zero and fails when `a` exceeds `b` by a known successor. */
  def ble(left: Value, right: Value): Value = {
    val (positive, negative) = cancelCommon(fromValue(left), fromValue(right))
    if (positive.isZeroForm) Kernel.trueValue
    else if (negative.isZeroForm && positive.constant > 0) Kernel.falseValue
    else stuck(Kernel.ble, Kernel.boolType, positive.toValue, negative.toValue)
  }

  /**
   * Unify a pair with at least one form after definitional equality and whole-variable linking fail: cancel only common
   * positive successor prefixes. Other arithmetic equations remain stuck.
   */
  def unifySuccessorPrefixes(
      left: Value,
      right: Value,
      store: EqStore
  ): Either[ValueEquivalence.UnificationFailure, EqStore] = {
    import ValueEquivalence.UnificationFailure._

    if (!isNat(left) || !isNat(right)) Left(Stuck(left, right))
    else {
      val a = fromValue(left)
      val b = fromValue(right)
      if (a.terms.isEmpty && b.terms.isEmpty || a.isZeroForm && b.constant > 0 || b.isZeroForm && a.constant > 0)
        Left(Contradiction(left, right))
      else {
        val common = a.constant.min(b.constant)
        if (common == 0) Left(Stuck(left, right))
        else ValueEquivalence.tryUnify(a.dropPrefix(common).toValue, b.dropPrefix(common).toValue, store)
      }
    }
  }

  /** A candidate is smaller when it converts to the root with a positive number of known successors removed. */
  def isStrictlySmaller(candidate: Value, root: VNatPoly): Boolean = {
    val rootForm = root.form
    rootForm.constant > 0 && isNat(candidate) && {
      val candidateForm = fromValue(candidate)
      candidateForm.constant < rootForm.constant && (
        candidateForm.termsKey == rootForm.termsKey ||
          (candidateForm.needsStructuralDefEq || rootForm.needsStructuralDefEq) &&
          alignedTermsEqual(candidateForm, rootForm)
      )
    }
  }
}
