package com.raccoonlang

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
    val BlockedThunk = 10
    val Pi = 11
    val ConstructorHead = 12
    val Ctor = 13
    val NormalizerType = 14
    val Normalizer = 15
    val ConstId = 16
    val LocalId = 17
  }

  private val SeedHi = -7046029254386353131L
  private val SeedLo = -4417276706812531889L
  private val Mul1 = -49064778989728563L
  private val Mul2 = -4265267296055464877L

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

  private def mixLong(key: Key, value: Long): Key =
    Key(
      avalanche(key.hi ^ (value + SeedHi)),
      avalanche(key.lo + java.lang.Long.rotateLeft(value ^ SeedLo, 31))
    )

  private def mixString(key: Key, value: String): Key = {
    var cur = mixLong(key, value.length.toLong)
    var idx = 0
    while (idx < value.length) {
      cur = mixLong(cur, value.charAt(idx).toLong)
      idx += 1
    }
    cur
  }

  private def mixKey(key: Key, value: Key): Key =
    Key(
      avalanche(key.hi ^ value.hi),
      avalanche(key.lo + java.lang.Long.rotateLeft(value.lo, 27))
    )

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

  private def mixAstNodeId(key: Key, nodeId: AstNodeId): Key = {
    val withSource =
      nodeId.source match {
        case Some(sourceId) => mixLong(mixLong(key, 1L), sourceId.value.toLong)
        case None           => mixLong(key, 0L)
      }
    mixLong(withSource, nodeId.start.toLong)
  }

  private def valueIdKey(key: Key, id: Value.ValueId): Key =
    id match {
      case Value.ValueId.Const(name) =>
        mixString(mixKey(key, tag(Tag.ConstId)), name)
      case Value.ValueId.LocalId(nodeId, captures) =>
        mixValues(mixAstNodeId(mixKey(key, tag(Tag.LocalId)), nodeId), captures)
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
    case Value.VSort(lvl)      => mixKey(tag(Tag.Sort), lvl.key)
    case Value.PropTpe         => tag(Tag.Prop)
    case Value.KernelObject    => tag(Tag.KernelObject)
    case Value.VConst(n, _, _) => mixString(tag(Tag.Const), n)
    case Value.Var(_, id, _)   => mixLong(tag(Tag.Var), id.toLong)
    case Value.VApp(h, args, _) =>
      mixValues(mixKey(tag(Tag.App), h.key), args)
    case Value.VBlockedApp(h, args, _, _) =>
      mixValues(mixKey(tag(Tag.App), h.key), args)
    case Value.VLam(_, id, _, _) =>
      valueIdKey(tag(Tag.Lam), id)
    case m: Value.VBlockedThunk =>
      valueIdKey(tag(Tag.BlockedThunk), m.id)
    case p: Value.VPi =>
      mixLong(valueIdKey(tag(Tag.Pi), p.id), p.binders.length.toLong)
    case av: Value.AppliedValue =>
      mixValues(mixKey(tag(Tag.App), av.head.key), av.args)
    case Value.ConstructorHead(n, _, _, _, _) =>
      mixString(tag(Tag.ConstructorHead), n)
    case Value.VCtor(h, fields, tpe) =>
      mixKey(mixValues(mixKey(tag(Tag.Ctor), h.key), fields), tpe.key)
    case Value.NormalizerType =>
      tag(Tag.NormalizerType)
    case n: Value.Normalizer =>
      mixString(tag(Tag.Normalizer), n.name)
  }
}
