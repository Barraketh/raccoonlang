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
    val KernelObject = 5
    val Const = 6
    val Var = 7
    val App = 8
    val Lam = 9
    val NeutralThunk = 10
    val Pi = 11
    val ConstructorHead = 12
    val Proof = 13
    val ConstId = 16
    val LocalId = 17
    val Packed = 18
    val LevelParamAtom = 19
    val SortParameter = 21
    val Large = 22
    val KindTpe = 23
    val LifetimeTpe = 24
    val Kind = 25
    val Lifetime = 26
    val Count = 27
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

  // Tags are mixed into every key built, so each is avalanched once.
  private val tags: Array[Key] =
    Array.tabulate(Tag.Count)(id => Key(avalanche(SeedHi ^ id.toLong), avalanche(SeedLo + id.toLong)))

  private def tag(id: Int): Key = tags(id)

  private[raccoonlang] def mixLong(key: Key, value: Long): Key =
    Key(
      avalanche(key.hi ^ (value + SeedHi)),
      avalanche(key.lo + java.lang.Long.rotateLeft(value ^ SeedLo, 31))
    )

  private def modeKey(mode: BinderMode): Long =
    mode match {
      case BinderMode.Explicit => 0L
      case BinderMode.Implicit => 1L
      case BinderMode.Evidence => 2L
    }

  private def mixString(key: Key, value: String): Key = {
    var cur = mixLong(key, value.length.toLong)
    var idx = 0
    while (idx < value.length) {
      cur = mixLong(cur, value.charAt(idx).toLong)
      idx += 1
    }
    cur
  }

  private[raccoonlang] def mixBytes(key: Key, bytes: Array[Byte]): Key = {
    var cur = mixLong(key, bytes.length.toLong)
    var acc = 0L
    var n = 0
    var idx = 0
    while (idx < bytes.length) {
      acc = (acc << 8) | (bytes(idx) & 0xffL)
      n += 1
      if (n == 8) {
        cur = mixLong(cur, acc)
        acc = 0L
        n = 0
      }
      idx += 1
    }
    if (n > 0) cur = mixLong(cur, acc)
    cur
  }

  private[raccoonlang] def mixKey(key: Key, value: Key): Key =
    Key(
      avalanche(key.hi ^ value.hi),
      avalanche(key.lo + java.lang.Long.rotateLeft(value.lo, 27))
    )

  /** The identity of a constructor head itself, independent of whether it stands alone or heads an application. */
  private[raccoonlang] def constructorName(name: String): Key = mixString(tag(Tag.ConstructorHead), name)

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
        mixValues(mixLong(mixKey(key, tag(Tag.LocalId)), nodeId.value.toLong), captures)
    }

  /** A set of variables in ascending id order, so the key depends on the set and not on how it was built. */
  private def mixVars(key: Key, vars: DepSet): Key = {
    var cur = key
    vars.foreach(id => cur = mixLong(cur, id.toLong))
    mixLong(cur, vars.size.toLong)
  }

  /*
   * A value's key, one function per value form. Each value computes its key when it is built, from its components and
   * its children's keys, which were computed when they were built, so no key is computed by a walk.
   */

  val levelTpe: Key = tag(Tag.LevelTpe)
  val kindTpe: Key = tag(Tag.KindTpe)
  val lifetimeTpe: Key = tag(Tag.LifetimeTpe)
  val sortParameter: Key = tag(Tag.SortParameter)
  val large: Key = tag(Tag.Large)

  def level(terms: Map[Value.VarId, Int], c: Int): Key = {
    var cur = mixLong(tag(Tag.Level), c.toLong)
    val sortedTerms = terms.iterator
      .map { case (atom, offset) => (mixLong(tag(Tag.LevelParamAtom), atom.toLong), offset) }
      .toArray
      .sortBy(_._1)
    var idx = 0
    while (idx < sortedTerms.length) {
      val (atomKey, offset) = sortedTerms(idx)
      cur = mixLong(mixKey(cur, atomKey), offset.toLong)
      idx += 1
    }
    mixLong(cur, sortedTerms.length.toLong)
  }

  def kind(isLin: Boolean, vars: DepSet): Key = mixVars(mixLong(tag(Tag.Kind), if (isLin) 1L else 0L), vars)

  def lifetime(vars: DepSet): Key = mixVars(tag(Tag.Lifetime), vars)

  /** Every field explicitly: two sorts at one level differ when their kinds or scopes do. */
  def sort(isProp: Boolean, level: Value.Level, kind: Value.Kind, scope: Value.Lifetime): Key =
    mixKey(mixKey(mixKey(mixLong(tag(Tag.Sort), if (isProp) 1 else 0), level.key), kind.key), scope.key)

  def constant(name: String): Key = mixString(tag(Tag.Const), name)

  def variable(id: Value.VarId): Key = mixLong(tag(Tag.Var), id.toLong)

  /**
   * An application's key mixes its head and the arguments it is given, `args`, which leave out its evidence arguments
   * (`VApp.determiningArgs`); a constructor's mixes its type too. A nullary constructor's bare head keys as its
   * application to no arguments.
   */
  def application(head: Value, args: Vector[Value], tpe: Value): Key =
    head match {
      case h: Value.ConstructorHead => mixKey(mixValues(mixKey(tag(Tag.App), h.nameKey), args), tpe.key)
      case other                    => mixValues(mixKey(tag(Tag.App), other.key), args)
    }

  def lambda(id: Value.ValueId): Key = valueIdKey(tag(Tag.Lam), id)

  def neutralThunk(id: Value.ValueId): Key = valueIdKey(tag(Tag.NeutralThunk), id)

  /**
   * The closure and the binders' modes explicitly, not through the node: both are part of the function type's identity
   * (spec §2.5, PROOF_BY_EVALUATION §1.5), and a checked node's modes may differ from its source's.
   */
  def pi(
      id: Value.ValueId,
      binders: Vector[CoreAst.Binder],
      closureKind: Value.Kind,
      closureScope: Value.Lifetime,
      mentionedScope: Value.Lifetime
  ): Key = {
    val modes = binders.foldLeft(mixLong(valueIdKey(tag(Tag.Pi), id), binders.length.toLong)) { (key, binder) =>
      mixLong(key, modeKey(binder.mode))
    }
    mixKey(mixKey(mixKey(modes, closureKind.key), closureScope.key), mentionedScope.key)
  }

  def packed(codec: Value.PackedCodec, payload: Value.PackedPayload, tpe: Value): Key = {
    val codecId = codec match {
      case Value.NatCodec         => 1L
      case _: Value.CharListCodec => 2L
    }
    mixKey(codec.mixPayloadKey(mixLong(tag(Tag.Packed), codecId), payload), tpe.key)
  }

  /** All erased proofs of defEq propositions share a key; VProof contains only its proposition. */
  def proof(tpe: Value): Key = mixKey(tag(Tag.Proof), tpe.key)
}
