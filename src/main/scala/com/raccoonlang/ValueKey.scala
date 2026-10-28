package com.raccoonlang

/**
 * Structural keys. Equal keys are trusted to mean convertible values (see `ValueEquivalence.defEq`); keys guard against
 * accidental collisions, not crafted ones. A key has two lanes that are separate hash chains: the `hi` lane reads only
 * the `hi` lanes of child keys, and the `lo` lane only their `lo` lanes.
 */
object ValueKey {
  final class Key private[ValueKey] (val hi: Long, val lo: Long) {
    override def equals(other: Any): Boolean =
      other match {
        case that: Key => hi == that.hi && lo == that.lo
        case _         => false
      }

    override def hashCode(): Int = {
      val h = hi ^ java.lang.Long.rotateLeft(lo, 32)
      (h ^ (h >>> 32)).toInt
    }

    override def toString: String = s"Key($hi,$lo)"
  }

  object Key {
    def apply(hi: Long, lo: Long): Key = new Key(hi, lo)

    implicit val ordering: Ordering[Key] = new Ordering[Key] {
      override def compare(x: Key, y: Key): Int = {
        val hi = java.lang.Long.compareUnsigned(x.hi, y.hi)
        if (hi != 0) hi else java.lang.Long.compareUnsigned(x.lo, y.lo)
      }
    }
  }

  private object Tag {
    val LevelTpe = 1
    val Level = 2
    val Sort = 3
    val Prop = 4
    val KernelObject = 5
    val Const = 6
    val Var = 7
    val App = 8
    val Lam = 9
    val NeutralThunk = 10
    val Pi = 11
    val ConstructorHead = 12
    val ConstId = 13
    val LocalId = 14
    val PropTpe = 15
    val NatPoly = 16
    val NatTerms = 17
    val NatMonomial = 18
    val NatNumeralPower = 19
    val NatSymbolicPower = 20
    val WordLayer = 21
    val WordTerminator = 22
  }

  /**
   * The tags from which `packed.PolynomialKeys` mixes the symbols of words: a layer's payload tuple and a terminator.
   * They are reserved with the other tags so that no two kinds of key share one.
   */
  private[raccoonlang] object WordTag {
    val Layer: Int = Tag.WordLayer
    val Terminator: Int = Tag.WordTerminator
  }

  /** A mixer starting from the tag `id`, one of `WordTag`, for keys that `packed` builds from child keys. */
  private[raccoonlang] def mixer(id: Int): Mixer = new Mixer(tag(id))

  private val SeedHi = -7046029254386353131L
  private val SeedLo = -4417276706812531889L
  private val Mul1 = -49064778989728563L
  private val Mul2 = -4265267296055464877L
  private val BigIntSmallEncoding = 0x534d414c4c000001L
  private val BigIntLargeEncoding = 0x4c41524745000001L

  private def avalanche(x0: Long): Long = {
    var x = x0
    x ^= x >>> 33
    x *= Mul1
    x ^= x >>> 33
    x *= Mul2
    x ^ (x >>> 33)
  }

  private def tag(id: Int): Key =
    Key(avalanche(SeedHi ^ id.toLong), avalanche(SeedLo + id.toLong))

  private def mixLong(key: Key, value: Long): Key = Key(mixLongHi(key.hi, value), mixLongLo(key.lo, value))

  private def mixLongHi(hi: Long, value: Long): Long = avalanche(hi ^ (value + SeedHi))

  private def mixLongLo(lo: Long, value: Long): Long = avalanche(lo + java.lang.Long.rotateLeft(value ^ SeedLo, 31))

  private def mixString(key: Key, value: String): Key = {
    var cur = mixLong(key, value.length.toLong)
    var idx = 0
    while (idx < value.length) {
      cur = mixLong(cur, value.charAt(idx).toLong)
      idx += 1
    }
    cur
  }

  private def mixBigInt(key: Key, value: BigInt): Key = {
    val mixer = new Mixer(key)
    mixer.bigInt(value)
    mixer.result
  }

  private def mixKey(key: Key, value: Key): Key = Key(mixKeyHi(key.hi, value), mixKeyLo(key.lo, value))

  private def mixKeyHi(hi: Long, value: Key): Long = avalanche(hi ^ value.hi)

  private def mixKeyLo(lo: Long, value: Key): Long = avalanche(lo + java.lang.Long.rotateLeft(value.lo, 27))

  /** Mixes a sequence into one key without allocating a key per step; each step matches the functional mixers. */
  private[raccoonlang] final class Mixer private[ValueKey] (start: Key) {
    private var hi = start.hi
    private var lo = start.lo

    def long(value: Long): Unit = {
      hi = mixLongHi(hi, value)
      lo = mixLongLo(lo, value)
    }

    def key(value: Key): Unit = {
      hi = mixKeyHi(hi, value)
      lo = mixKeyLo(lo, value)
    }

    /**
     * Length-tagged binary encoding avoids decimal conversion and distinguishes small and full-width integer chunks.
     */
    def bigInt(value: BigInt): Unit =
      if (value.isValidLong) {
        long(BigIntSmallEncoding)
        long(value.longValue)
      } else {
        val bytes = value.toByteArray
        long(BigIntLargeEncoding)
        long(bytes.length.toLong)
        var offset = 0
        while (offset < bytes.length) {
          val end = math.min(offset + java.lang.Long.BYTES, bytes.length)
          var word = 0L
          while (offset < end) {
            word = (word << 8) | (bytes(offset) & 0xffL)
            offset += 1
          }
          long(word)
        }
      }

    def result: Key = Key(hi, lo)
  }

  private def mixValues(key: Key, values: Iterable[Value]): Key = {
    val iter = values.iterator
    var cur = key
    var count = 0
    while (iter.hasNext) {
      cur = mixKey(cur, iter.next().key)
      count += 1
    }
    mixLong(cur, count.toLong)
  }

  private def valueIdKey(key: Key, id: Value.ValueId): Key =
    id match {
      case Value.ValueId.Const(name) =>
        mixString(mixKey(key, tag(Tag.ConstId)), name)
      case Value.ValueId.LocalId(nodeId, captures) =>
        mixValues(mixLong(mixKey(key, tag(Tag.LocalId)), nodeId.value), captures)
    }

  private def levelKey(atoms: Map[Value.VarId, Int], c: Int): Key = {
    var cur = mixLong(tag(Tag.Level), c.toLong)
    val sortedAtoms = atoms.toArray.sortBy(_._1)
    var idx = 0
    while (idx < sortedAtoms.length) {
      val (varId, offset) = sortedAtoms(idx)
      cur = mixLong(mixLong(cur, varId.toLong), offset.toLong)
      idx += 1
    }
    mixLong(cur, sortedAtoms.length.toLong)
  }

  def orderKey(v: Value): Key = v match {
    case Value.LevelTpe        => tag(Tag.LevelTpe)
    case level: Value.Level    => levelKey(level.atoms, level.c)
    case Value.PropTpe         => tag(Tag.Prop)
    case Value.VSort(lvl)      => mixKey(tag(Tag.Sort), lvl.key)
    case Value.KernelObject    => tag(Tag.KernelObject)
    case Value.VConst(n, _, _) => mixString(tag(Tag.Const), n)
    case Value.Var(_, id, _)   => mixLong(tag(Tag.Var), id.toLong)
    case Value.VApp(h, args, tpe, _) =>
      val appKey = mixValues(mixKey(tag(Tag.App), h.key), args)
      h match {
        case _: Value.ConstructorHead => mixKey(appKey, tpe.key)
        case _                        => appKey
      }
    case Value.VLam(_, id, _) =>
      valueIdKey(tag(Tag.Lam), id)
    case m: Value.NeutralThunk =>
      valueIdKey(tag(Tag.NeutralThunk), m.id)
    case p: Value.VPi =>
      mixLong(valueIdKey(tag(Tag.Pi), p.id), p.binders.length.toLong)
    case Value.ConstructorHead(n, _, _, _, _) =>
      mixString(tag(Tag.ConstructorHead), n)
    case poly: Value.VNatPoly =>
      mixBigInt(mixKey(tag(Tag.NatPoly), poly.form.termsKey), poly.form.constant)
    case word: Value.VWord => word.repr.key
  }

  /** Nat terms in order; each term contributes its coefficient and its monomial's cached key. */
  private[raccoonlang] def natTermsKey(terms: Vector[NatNormalForm.Term]): Key = {
    val mixer = new Mixer(tag(Tag.NatTerms))
    mixer.long(terms.length.toLong)
    var index = 0
    while (index < terms.length) {
      val term = terms(index)
      mixer.bigInt(term.coefficient)
      mixer.key(term.monomial.key)
      index += 1
    }
    mixer.result
  }

  /**
   * A monomial's factors in order; each contributes its base's key, so a form base contributes its own form's key, then
   * its kind and its exponent: a numeral, or a symbolic exponent's key.
   */
  private[raccoonlang] def natMonomialKey(factors: Vector[NatNormalForm.Factor]): Key = {
    val mixer = new Mixer(tag(Tag.NatMonomial))
    mixer.long(factors.length.toLong)
    var index = 0
    while (index < factors.length) {
      val factor = factors(index)
      mixer.key(factor.base.key)
      factor match {
        case power: NatNormalForm.NumeralPower =>
          mixer.long(Tag.NatNumeralPower.toLong)
          mixer.bigInt(power.exponent)
        case power: NatNormalForm.SymbolicPower =>
          mixer.long(Tag.NatSymbolicPower.toLong)
          mixer.key(power.exponent.key)
      }
      index += 1
    }
    mixer.result
  }
}
