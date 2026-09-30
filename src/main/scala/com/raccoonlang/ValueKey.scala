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
    val LevelIMaxAtom = 20
    val SortParameter = 21
    val Large = 22
    val KindTpe = 23
    val LifetimeTpe = 24
    val Kind = 25
    val Lifetime = 26
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
  private def headKey(head: Value): Key =
    head match {
      case h: Value.ConstructorHead => mixString(tag(Tag.ConstructorHead), h.name)
      case other                    => other.key
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
        mixValues(mixLong(mixKey(key, tag(Tag.LocalId)), nodeId.value.toLong), captures)
    }

  private[raccoonlang] def levelAtomKey(atom: Value.Level.Atom): Key =
    atom match {
      case Value.Level.ParamAtom(id) => mixLong(tag(Tag.LevelParamAtom), id.toLong)
      case Value.Level.IMaxAtom(lhs, rhs) =>
        mixKey(mixKey(tag(Tag.LevelIMaxAtom), lhs.key), rhs.key)
    }

  private def levelKey(terms: Map[Value.Level.Atom, Int], c: Int): Key = {
    var cur = mixLong(tag(Tag.Level), c.toLong)
    val sortedTerms = terms.iterator
      .map { case (atom, offset) => (levelAtomKey(atom), offset) }
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

  /** A set of variables in ascending id order, so the key depends on the set and not on how it was built. */
  private def mixVars(key: Key, vars: DepSet): Key = {
    var cur = key
    vars.foreach(id => cur = mixLong(cur, id.toLong))
    mixLong(cur, vars.size.toLong)
  }

  def orderKey(v: Value): Key = v match {
    case Value.LevelTpe           => tag(Tag.LevelTpe)
    case Value.KindTpe            => tag(Tag.KindTpe)
    case Value.LifetimeTpe        => tag(Tag.LifetimeTpe)
    case Value.SortParameter      => tag(Tag.SortParameter)
    case Value.Large              => tag(Tag.Large)
    case level: Value.Level       => levelKey(level.terms, level.c)
    case kind: Value.Kind         => mixVars(mixLong(tag(Tag.Kind), if (kind.isLin) 1L else 0L), kind.vars)
    case lifetime: Value.Lifetime => mixVars(tag(Tag.Lifetime), lifetime.vars)
    case sort: Value.VSort        =>
      // Every field explicitly: two sorts at one level differ when their kinds or scopes do.
      mixKey(mixKey(mixKey(tag(Tag.Sort), sort.level.key), sort.kind.key), sort.scope.key)
    case Value.VConst(n, _, _) => mixString(tag(Tag.Const), n)
    case Value.Var(_, id, _)   => mixLong(tag(Tag.Var), id.toLong)
    case Value.VApp(h, args, tpe, _) =>
      val appKey = mixValues(mixKey(tag(Tag.App), headKey(h)), args)
      h match {
        case _: Value.ConstructorHead => mixKey(appKey, tpe.key)
        case _                        => appKey
      }
    case Value.VLam(_, id, _) =>
      valueIdKey(tag(Tag.Lam), id)
    case m: Value.NeutralThunk =>
      valueIdKey(tag(Tag.NeutralThunk), m.id)
    case p: Value.VPi =>
      // The closure and the binders' modes explicitly, not through the node: both are part of the function type's
      // identity (spec §2.5, PROOF_BY_EVALUATION §1.5), and a checked node's modes may differ from its source's.
      val binders = p.binders.foldLeft(mixLong(valueIdKey(tag(Tag.Pi), p.id), p.binders.length.toLong)) {
        (key, binder) => mixLong(key, modeKey(binder.mode))
      }
      mixKey(mixKey(binders, p.closureKind.key), p.closureScope.key)
    case p: Value.VPacked =>
      val codecId = p.codec match {
        case Value.NatCodec         => 1L
        case _: Value.CharListCodec => 2L
      }
      mixKey(p.codec.mixPayloadKey(mixLong(tag(Tag.Packed), codecId), p.payload), p.tpe.key)
    // A nullary constructor is already a value in constructor form: a global lookup hands back the
    // bare head where `evalRef` hands back `VCtor(h, [], tpe)`. Both spellings denote the same
    // value, so the bare head keys exactly as that application would, or defEq's key fast path
    // would call one unequal to the other.
    case head: Value.ConstructorHead if head.totalArity == 0 =>
      mixKey(mixValues(mixKey(tag(Tag.App), headKey(head)), Vector.empty), head.tpe.key)
    case head: Value.ConstructorHead => headKey(head)
    // All erased proofs of defEq propositions share a key; VProof contains only its proposition.
    case p: Value.VProof =>
      mixKey(tag(Tag.Proof), p.tpe.key)
    case deferred: Value.DeferredEvidence => deferred.escaped
  }
}
