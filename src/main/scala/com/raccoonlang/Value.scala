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
  }

  private[raccoonlang] def envDeps(env: Env): DepSet = {
    val deps = DepSet.newBuilder
    env.locals.values.foreach(value => deps.unionInPlace(value.synDeps))
    deps.result()
  }

  final case class VSort(level: Int) extends TopLevelValue {
    require(level >= 0, "Sort level must be non-negative")
    // C04 intentionally has one universe: Type and every sort are self-typed.
    override val tpe: Value = this
  }

  case object LevelTpe extends TopLevelValue { override val tpe: Value = TypeValue }
  val TypeValue: Value = VSort(0)
  val TypeTpe: Value = TypeValue
  val PropTpe: Value = TypeValue

  def sortOf(value: Value): VSort = value match {
    case sort: VSort => sort
    case other       => other.tpe match { case sort: VSort => sort; case _ => throw NotAType(other) }
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

  private[raccoonlang] def constructorStoredArgs(head: ConstructorHead, args: Vector[Value]): Vector[Value] = {
    if (args.length != head.totalArity)
      throw WTF(s"Constructor ${head.name} was given ${args.length} args, expected ${head.totalArity}")
    args.drop(head.numErasedFamilyArgs)
  }
}
