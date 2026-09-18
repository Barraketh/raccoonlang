package com.raccoonlang

/** Stable structural keys for the value forms available before universes and proofs. */
object ValueKey {
  final class Key private[ValueKey] (val hi: Long, val lo: Long) {
    override def equals(other: Any): Boolean = other match {
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
        val high = java.lang.Long.compareUnsigned(x.hi, y.hi)
        if (high != 0) high else java.lang.Long.compareUnsigned(x.lo, y.lo)
      }
    }
  }

  private val SeedHi = -7046029254386353131L
  private val SeedLo = -4417276706812531889L
  private val Mul1 = -49064778989728563L
  private val Mul2 = -4265267296055464877L

  private def avalanche(value0: Long): Long = {
    var value = value0
    value ^= value >>> 33
    value *= Mul1
    value ^= value >>> 33
    value *= Mul2
    value ^ (value >>> 33)
  }

  private def tag(tag: Int): Key = Key(avalanche(SeedHi ^ tag.toLong), avalanche(SeedLo + tag.toLong))
  private def mix(key: Key, value: Long): Key =
    Key(avalanche(key.hi ^ (value + SeedHi)), avalanche(key.lo + java.lang.Long.rotateLeft(value ^ SeedLo, 31)))
  private def mix(key: Key, value: Key): Key =
    Key(avalanche(key.hi ^ value.hi), avalanche(key.lo + java.lang.Long.rotateLeft(value.lo, 27)))
  private def text(key: Key, value: String): Key = {
    var current = mix(key, value.length.toLong)
    value.foreach(ch => current = mix(current, ch.toLong))
    current
  }
  private[raccoonlang] def mixLong(key: Key, value: Long): Key = mix(key, value)
  private[raccoonlang] def mixKey(key: Key, value: Key): Key = mix(key, value)
  private[raccoonlang] def mixBytes(key: Key, bytes: Array[Byte]): Key = {
    var out = mix(key, bytes.length.toLong)
    bytes.foreach(b => out = mix(out, b.toLong & 0xffL))
    out
  }

  // Level atoms need a structural key of their own.  In particular, using the
  // level's pretty-printed form here would make ordering depend on presentation
  // and (more seriously) the old Level case below collapsed every level to one
  // key.  Keep nested imax atoms in the key so the key fast path cannot equate
  // unresolved imax with an ordinary max.
  private val LevelParamAtomTag = 19
  private val LevelIMaxAtomTag = 20

  private def levelAtomKey(atom: Value.Level.Atom): Key = atom match {
    case Value.Level.ParamAtom(id) => mix(tag(LevelParamAtomTag), id.toLong)
    case Value.Level.IMaxAtom(lhs, rhs) =>
      mix(mix(tag(LevelIMaxAtomTag), lhs.key), rhs.key)
  }

  private def levelKey(terms: Map[Value.Level.Atom, Int], c: Int): Key = {
    var current = mix(tag(2), c.toLong)
    val sorted = terms.iterator.map { case (atom, offset) => levelAtomKey(atom) -> offset }.toArray.sortBy(_._1)
    sorted.foreach { case (atom, offset) => current = mix(mix(current, atom), offset.toLong) }
    mix(current, sorted.length.toLong)
  }
  private def values(key: Key, items: Iterable[Value]): Key = {
    var current = key
    var count = 0L
    items.foreach { item => current = mix(current, item.key); count += 1 }
    mix(current, count)
  }
  private def idKey(key: Key, id: Value.ValueId): Key = id match {
    case Value.ValueId.Const(name) => text(mix(key, 16L), name)
    case Value.ValueId.LocalId(node, captures) =>
      values(mix(mix(key, 17L), node.start.toLong), captures)
  }
  private def headKey(head: Value): Key = head match {
    case constructor: Value.ConstructorHead => text(tag(12), constructor.name)
    case other                              => other.key
  }

  def orderKey(value: Value): Key = value match {
    case Value.LevelTpe           => tag(1)
    case level: Value.Level       => levelKey(level.terms, level.c)
    case Value.VSort(level)       => mix(tag(3), level.key)
    case Value.VConst(name, _, _) => text(tag(6), name)
    case Value.Var(_, id, _)      => mix(tag(7), id.toLong)
    case Value.VApp(head, args, tpe, _) =>
      val base = values(mix(tag(8), headKey(head)), args)
      head match {
        case _: Value.ConstructorHead => mix(base, tpe.key)
        case _                        => base
      }
    case Value.VLam(_, id, _)      => idKey(tag(9), id)
    case Value.VProof(tpe)         => mix(tag(13), tpe.key)
    case packed: Value.VPacked     => packed.codec.mixPayloadKey(mix(tag(14), packed.tpe.key), packed.payload)
    case thunk: Value.NeutralThunk => idKey(tag(10), thunk.id)
    case pi: Value.VPi             => mix(idKey(tag(11), pi.id), pi.binders.length.toLong)
    case head: Value.ConstructorHead if head.totalArity == 0 =>
      mix(values(mix(tag(8), headKey(head)), Vector.empty), head.tpe.key)
    case head: Value.ConstructorHead => headKey(head)
  }
}
