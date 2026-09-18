package com.raccoonlang

sealed trait Value {
  def tpe: Value
  def synDeps: DepSet
  def needsStructuralDefEq: Boolean = false
  lazy val key: ValueKey.Key = ValueKey.orderKey(this)
  override def toString: String = PrettyPrinter.print(this)
}

sealed trait TopLevelValue extends Value { override val synDeps: DepSet = DepSet.empty }

object Value {
  type VarId = Int

  sealed trait ValueId
  object ValueId {
    final case class Const(name: String) extends ValueId
    final case class LocalId(nodeId: AstNodeId, captures: Vector[Value]) extends ValueId
  }

  sealed trait LamBody { def synDeps: DepSet }
  object LamBody {
    final case class Core(term: CoreAst.Term.Lam, env: Env) extends LamBody {
      override lazy val synDeps: DepSet = env.dependencies
    }
    final case class Native(run: (Vector[Value], Env) => Value, env: Env, isRawRecursive: Boolean) extends LamBody {
      override lazy val synDeps: DepSet = env.dependencies
    }
  }

  private[raccoonlang] def envDeps(env: Env): DepSet = {
    val deps = DepSet.newBuilder
    env.locals.values.foreach(value => deps.unionInPlace(value.synDeps))
    deps.result()
  }

  case object LevelTpe extends TopLevelValue { override def tpe: Value = TypeTpe }

  final class Level private (val terms: Map[Level.Atom, Int], val c: Int) extends Value {
    override val tpe: Value = LevelTpe
    private val cachedHashCode: Int = 31 * terms.hashCode() + c
    private lazy val neverZero: Boolean = c > 0 || terms.exists {
      case (_, offset) if offset > 0   => true
      case (Level.IMaxAtom(_, rhs), _) => rhs.neverZero
      case (_: Level.ParamAtom, _)     => false
    }
    private lazy val hasIMax: Boolean = terms.keysIterator.exists(_.isInstanceOf[Level.IMaxAtom])
    override lazy val synDeps: DepSet = {
      val deps = DepSet.newBuilder
      terms.keys.foreach {
        case Level.ParamAtom(id)      => deps.add(id)
        case Level.IMaxAtom(lhs, rhs) => deps.unionInPlace(lhs.synDeps); deps.unionInPlace(rhs.synDeps)
      }
      deps.result()
    }
    override def equals(obj: Any): Boolean = obj match {
      case other: Level => cachedHashCode == other.cachedHashCode && c == other.c && terms == other.terms
      case _            => false
    }
    override def hashCode(): Int = cachedHashCode
    override def toString: String = {
      if (terms.isEmpty) return c.toString
      val atoms = terms.toVector.sortBy(_._1.toString).map { case (atom, offset) =>
        val base = atom match {
          case Level.ParamAtom(id)      => s"u$id"
          case Level.IMaxAtom(lhs, rhs) => s"imax($lhs, $rhs)"
        }
        if (offset == 0) base else s"$base+$offset"
      }
      (atoms ++ (if (c > 0) Vector(c.toString) else Vector.empty)).mkString("max(", ", ", ")")
    }
  }
  object Level {
    sealed trait Atom
    final case class ParamAtom(id: VarId) extends Atom
    final case class IMaxAtom(lhs: Level, rhs: Level) extends Atom
    private def ofTerms(terms: Map[Atom, Int], c: Int): Level = {
      require(c >= 0 && terms.values.forall(_ >= 0), "Level components must be non-negative")
      new Level(terms, if (terms.nonEmpty && c <= terms.values.max) 0 else c)
    }
    def of(atoms: Map[VarId, Int], c: Int): Level = ofTerms(atoms.map { case (id, k) => ParamAtom(id) -> k }, c)
    def const(c: Int): Level = ofTerms(Map.empty, c)
    def addOffset(l: Level, offset: Int): Level = {
      if (offset == 0) l
      else {
        val terms = l.terms.map { case (a, k) => a -> (k + offset) }
        ofTerms(terms, if (l.c > 0 || l.terms.isEmpty) l.c + offset else 0)
      }
    }
    def succ(l: Level): Level = addOffset(l, 1)
    def geq(l: Level, offset: Int): Boolean =
      l.terms.values.forall(_ >= offset) && (l.c >= offset || (l.c == 0 && l.terms.nonEmpty))
    def max(xs: Vector[Level]): Level = {
      require(xs.nonEmpty, "Level.max requires at least one level")
      val terms = scala.collection.mutable.HashMap.empty[Atom, Int]
      var c = 0
      xs.foreach { l =>
        c = math.max(c, l.c)
        l.terms.foreach { case (a, k) => if (k > terms.getOrElse(a, -1)) terms.update(a, k) }
      }
      ofTerms(terms.toMap, c)
    }
    def isNeverZero(l: Level): Boolean = l.neverZero
    def imax(lhs: Level, rhs: Level): Level =
      if (rhs == zero) zero
      else if (isNeverZero(rhs)) max(Vector(lhs, rhs))
      else if (lhs == zero || lhs == one || lhs == rhs) rhs
      else ofTerms(Map(IMaxAtom(lhs, rhs) -> 0), 0)
    def containsIMax(l: Level): Boolean = l.hasIMax
    def singleVariableOffset(l: Level): Option[(VarId, Int)] =
      if (l.c != 0 || l.terms.size != 1) None
      else
        l.terms.head match {
          case (ParamAtom(id), k) => Some(id -> k)
          case _                  => None
        }
    private def regularLeq(a: Level, b: Level): Boolean =
      (a.c <= b.c || b.terms.values.exists(_ >= a.c)) && a.terms.forall { case (atom, k) =>
        k <= b.terms.getOrElse(atom, -1)
      }
    def leq(a: Level, b: Level): Boolean = {
      if (!containsIMax(a) && !containsIMax(b)) regularLeq(a, b)
      else {
        val memo = scala.collection.mutable.Map.empty[(Level, Level), Boolean]
        def covered(c: Int, out: Level): Boolean = c <= out.c || out.terms.values.exists(_ >= c)
        def atomLevel(atom: Atom, offset: Int): Level = ofTerms(Map(atom -> offset), 0)
        def termLeq(atom: Atom, offset: Int, out: Level): Boolean = {
          val direct = out.terms.exists {
            case (`atom`, outOffset)           => offset <= outOffset
            case (IMaxAtom(_, rhs), outOffset) => loop(atomLevel(atom, offset), addOffset(rhs, outOffset))
            case _                             => false
          }
          direct || (atom match {
            case IMaxAtom(lhs, rhs) =>
              covered(offset, out) && loop(addOffset(lhs, offset), out) && loop(addOffset(rhs, offset), out)
            case _: ParamAtom => false
          })
        }
        def loop(lhs: Level, rhs: Level): Boolean =
          if (lhs == rhs) true
          else
            memo.getOrElseUpdate(
              (lhs, rhs),
              if (!containsIMax(lhs) && !containsIMax(rhs)) regularLeq(lhs, rhs)
              else covered(lhs.c, rhs) && lhs.terms.forall { case (atom, offset) => termLeq(atom, offset, rhs) }
            )
        loop(a, b)
      }
    }
    def mk(id: VarId): Level = ofTerms(Map(ParamAtom(id) -> 0), 0)
    def fromValue(v: Value): Option[Level] = v match {
      case l: Level             => Some(l)
      case Var(_, id, LevelTpe) => Some(mk(id))
      case _                    => None
    }
    val zero: Level = const(0)
    val one: Level = const(1)
  }

  case class VSort(level: Level) extends Value {
    override def tpe: Value = VSort(Level.succ(level))
    override lazy val synDeps: DepSet = level.synDeps
  }
  val TypeTpe: VSort = VSort(Level.one)
  val TypeValue: VSort = TypeTpe
  val PropTpe: VSort = VSort(Level.zero)

  def sortOf(value: Value): VSort = value match {
    case other => other.tpe match { case sort: VSort => sort; case _ => throw NotAType(other) }
  }

  final case class VPi(
      env: Env,
      binders: Vector[CoreAst.Binder],
      codomain: Env => Value,
      override val synDeps: DepSet,
      id: ValueId,
      classifier0: () => VSort,
      knownPropValued: Option[Boolean] = None
  ) extends Value {
    override val needsStructuralDefEq: Boolean = true
    require(binders.nonEmpty, "VPi requires at least one binder")
    override lazy val tpe: VSort = classifier0()
  }

  final case class VLam(tpe: VPi, id: ValueId, body: LamBody) extends Value {
    override val needsStructuralDefEq: Boolean = true
    override lazy val synDeps: DepSet = {
      val deps = DepSet.newBuilder
      deps.unionInPlace(tpe.synDeps)
      deps.unionInPlace(body.synDeps)
      id match {
        case ValueId.Const(_)           =>
        case ValueId.LocalId(_, values) => values.foreach(value => deps.unionInPlace(value.synDeps))
      }
      deps.result()
    }
  }

  final case class VApp(head: Value, args: Vector[Value], tpe: Value, blockedOn: DepSet = DepSet.empty) extends Value {
    override lazy val needsStructuralDefEq: Boolean =
      head.needsStructuralDefEq || args.exists(_.needsStructuralDefEq) || tpe.needsStructuralDefEq
    override lazy val synDeps: DepSet = {
      val deps = DepSet.newBuilder
      deps.unionInPlace(head.synDeps)
      args.foreach(value => deps.unionInPlace(value.synDeps))
      deps.unionInPlace(tpe.synDeps)
      deps.result()
    }
    require(args.nonEmpty || blockedOn.isEmpty, "Blocked application requires at least one argument")
    head match {
      case head: ConstructorHead =>
        require(
          args.length == head.totalArity - head.numErasedFamilyArgs,
          s"Constructor ${head.name} stores ${args.length} args, expected ${head.totalArity - head.numErasedFamilyArgs}"
        )
      case _ =>
    }
  }

  /** A stuck match retains its syntax, lexical closure, stable identity, and computed result type. */
  final case class NeutralThunk(
      term: CoreAst.Term.Match,
      env: Env,
      id: ValueId.LocalId,
      tpe: Value,
      blockedOn: DepSet
  ) extends Value {
    override val needsStructuralDefEq: Boolean = true
    override lazy val synDeps: DepSet = {
      val deps = DepSet.newBuilder
      deps.unionInPlace(env.dependencies)
      deps.unionInPlace(tpe.synDeps)
      id.captures.foreach(value => deps.unionInPlace(value.synDeps))
      deps.unionInPlace(blockedOn)
      deps.result()
    }
  }

  final case class Var(name: String, id: VarId, tpe: Value) extends Value {
    override lazy val synDeps: DepSet = tpe.synDeps + id
  }

  sealed trait ConstType
  final case class Inductive(meta: InductiveMeta) extends ConstType
  case object Symbol extends ConstType

  final case class ConstructorMeta(shortName: String, canonicalName: String)
  final case class InductiveMeta(constructors: Vector[ConstructorMeta], familyArity: Int)

  final case class VConst(name: String, constType: ConstType, tpe: Value) extends Value {
    override lazy val synDeps: DepSet = tpe.synDeps
  }

  final case class ConstructorHead(
      name: String,
      numErasedFamilyArgs: Int,
      totalArity: Int,
      tpe: Value,
      noConfusion: Boolean = true
  ) extends TopLevelValue

  object VCtor {
    def apply(head: ConstructorHead, fields: Vector[Value], tpe: Value): VApp = VApp(head, fields, tpe)

    def unapply(value: Value): Option[(ConstructorHead, Vector[Value], Value)] = value match {
      case VApp(head: ConstructorHead, fields, tpe, blockedOn) if blockedOn.isEmpty => Some((head, fields, tpe))
      case _                                                                        => None
    }
  }

  object ConstructorForm {
    def unapply(value: Value): Option[(String, Vector[Value])] = value match {
      case VCtor(head, fields, _) => Some(head.name -> fields)
      case _                      => None
    }
  }

  object Blocker {
    def unapply(value: Value): Option[DepSet] = value match {
      case Var(_, id, _)                                             => Some(DepSet(id))
      case VApp(_, _, _, blockedOn) if blockedOn.nonEmpty            => Some(blockedOn)
      case NeutralThunk(_, _, _, _, blockedOn) if blockedOn.nonEmpty => Some(blockedOn)
      case _                                                         => None
    }
  }

  object Blocked {
    def unapply(value: Value): Option[DepSet] = value match {
      case VApp(_, _, _, blockedOn) if blockedOn.nonEmpty            => Some(blockedOn)
      case NeutralThunk(_, _, _, _, blockedOn) if blockedOn.nonEmpty => Some(blockedOn)
      case _                                                         => None
    }
  }

  object ConstSpine {
    def unapply(value: Value): Option[(VConst, Vector[Value])] = value match {
      case c: VConst                                                   => Some(c -> Vector.empty)
      case VApp(head: VConst, args, _, blockedOn) if blockedOn.isEmpty => Some(head -> args)
      case _                                                           => None
    }
  }

  final case class InductiveFamilyInstance(head: VConst, meta: InductiveMeta, args: Vector[Value])

  object InductiveFamilyValue {
    def unapply(value: Value): Option[InductiveFamilyInstance] = value match {
      case ConstSpine(head @ VConst(_, Inductive(meta), _), args) if args.length == meta.familyArity =>
        Some(InductiveFamilyInstance(head, meta, args))
      case _ => None
    }
  }

  private[raccoonlang] def constructorStoredArgs(head: ConstructorHead, args: Vector[Value]): Vector[Value] = {
    if (args.length != head.totalArity)
      throw WTF(s"Constructor ${head.name} was given ${args.length} args, expected ${head.totalArity}")
    args.drop(head.numErasedFamilyArgs)
  }
}
