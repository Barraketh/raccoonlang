package com.raccoonlang

import com.raccoonlang.Value._

/** Shared Nat values for normal-form tests and benchmarks. */
object NatFixtures {
  def fresh(name: String): Var = FreshVar.freshVar(name, Kernel.natType)

  def constant(value: BigInt): Value = NatNormalForm.literal(value)

  def add(left: Value, right: Value): Value = NatNormalForm.add(left, right)

  def mul(left: Value, right: Value): Value = NatNormalForm.mul(left, right)

  def pow(base: Value, exponent: BigInt): Value = NatNormalForm.pow(base, constant(exponent))

  def pow(base: Value, exponent: Value): Value = NatNormalForm.pow(base, exponent)

  /** Combine nonempty values in a balanced tree, so construction cost stays logarithmic in depth. */
  def balanced(values: Vector[Value])(combine: (Value, Value) => Value): Value = {
    require(values.nonEmpty)
    def loop(from: Int, until: Int): Value =
      if (until - from == 1) values(from)
      else {
        val middle = from + (until - from) / 2
        combine(loop(from, middle), loop(middle, until))
      }
    loop(0, values.length)
  }

  def sum(values: Vector[Value]): Value = balanced(values)(add)

  def product(values: Vector[Value]): Value = balanced(values)(mul)

  def termCount(value: Value): Int =
    value match {
      case poly: VNatPoly => poly.form.terms.length
      case _              => 0
    }

  def form(value: Value): NatNormalForm.Form = value.asInstanceOf[VNatPoly].form

  def numeralExponent(factor: NatNormalForm.Factor): BigInt = factor.asInstanceOf[NatNormalForm.NumeralPower].exponent
}
