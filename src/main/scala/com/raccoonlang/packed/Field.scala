package com.raccoonlang.packed

/** Arithmetic in the field F = Z_p, p = 2^61 - 1, on canonical representatives in [0, p). */
private[packed] object Field {
  val P: Long = (1L << 61) - 1

  /** Any 64-bit value, read as unsigned, reduced into F; 2^61 is 1 in F. */
  def reduce(x: Long): Long = {
    val r = (x & P) + (x >>> 61)
    if (r >= P) r - P else r
  }

  def add(a: Long, b: Long): Long = {
    val s = a + b
    if (s >= P) s - P else s
  }

  def sub(a: Long, b: Long): Long = {
    val d = a - b
    if (d < 0) d + P else d
  }

  def mul(a: Long, b: Long): Long = {
    val low = a * b
    val high = Math.multiplyHigh(a, b)
    // a * b < 2^122, so splitting it at bit 61 gives two parts below 2^61 whose sum is a * b in F.
    reduce((low & P) + ((low >>> 61) | (high << 3)))
  }

  def pow(base: Long, exponent: Long): Long = {
    var result = 1L
    var square = base
    var remaining = exponent
    while (remaining > 0) {
      if ((remaining & 1L) != 0) result = mul(result, square)
      square = mul(square, square)
      remaining >>>= 1
    }
    result
  }

  def inverse(a: Long): Long = pow(a, P - 2)
}
