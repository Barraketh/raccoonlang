package com.raccoonlang

import com.raccoonlang.Value.{
  Kind,
  KindTpe,
  Large,
  Level,
  Lifetime,
  LifetimeTpe,
  ParameterTpe,
  SortParameter,
  VPi,
  VSort
}

/**
 * The one place sorts are built and classified (docs/kernel.md#universes-and-function-types). `VSort` is constructed
 * only here, read through its fields, and compared only by conversion. Whether a sort is `Prop`, and whether a type is
 * a proposition, is answered here and nowhere else, so proof irrelevance and the checker cannot disagree about it.
 */
object Sorts {

  /**
   * A sort. The checker has already refused a kind other than `Kind.unr` at a level that may be zero (`LinearProp`,
   * spec §2.3); substitution preserves both a level that is never zero and the kind `Kind.unr`, so no sort built later
   * breaks it either.
   */
  def sort(level: Level, kind: Kind, scope: Lifetime): VSort = {
    if (!admitsKind(level, kind)) wtf(s"Sort at level $level cannot have the kind $kind")
    new VSort(level, kind, scope)
  }

  /**
   * A sort whose fields were just checked, where a kind other than `Kind.unr` at a level that may be zero is
   * `LinearProp` (spec §2.3): a written sort, and a function type's classifier. Sorts built on already-checked paths
   * use `sort`.
   */
  def checkedSort(level: Level, kind: Kind, scope: Lifetime): VSort = {
    if (!admitsKind(level, kind)) fail(LinearProp(kind, level))
    sort(level, kind, scope)
  }

  val Prop: VSort = sort(Level.zero, Kind.unr, Lifetime.empty)
  val Type: VSort = sort(Level.one, Kind.unr, Lifetime.empty)

  /** A sort of a kind other than `Kind.unr` needs a level that is never zero, since proofs are unrestricted. */
  def admitsKind(level: Level, kind: Kind): Boolean = kind.isUnr || Level.isNeverZero(level)

  def isProp(sort: VSort): Boolean = sort.level == Level.zero

  /**
   * The sort of the type `tpe`, which says what its values hold: their kind and scope. A large type and a sort
   * parameter have none, since no sort classifies either, so their values hold nothing. Anything else is not a type,
   * and asking is a bug. Linearity, confinement, a lambda's captures and propositions read a type's sort here; where a
   * position requires a type, `TypeChecker.getUniverse` refuses one without a sort instead.
   */
  def sortOf(tpe: Value): Option[VSort] =
    tpe.tpe match {
      case sort: VSort           => Some(sort)
      case Large | SortParameter => None
      case classifier            => wtf(s"The type $tpe is classified by $classifier, which is no classifier")
    }

  /** A sort's kind or its scope: the two fields a function type's closure also has. */
  sealed abstract class Field[P <: Value](val parameter: ParameterTpe) {
    def of(sort: VSort): P

    /** A checked expression of the field's sort parameter, which denotes a normal form. */
    def normalForm(value: Value): P

    def join(parts: Iterable[P]): P

    /** `Kind.unr` or `Lifetime.empty`: the unit of the join, and what every substitution keeps. */
    def isLeast(part: P): Boolean

    def contains(declared: P, part: P): Boolean

    private[Sorts] def exceeded(declaration: String, declared: P, part: ContainedPart, partValue: P): TypeError
  }

  object KindField extends Field[Kind](KindTpe) {
    def of(sort: VSort): Kind = sort.kind
    def normalForm(value: Value): Kind = Interpreter.getKind(value)
    def join(parts: Iterable[Kind]): Kind = Kind.join(parts)
    def isLeast(part: Kind): Boolean = part.isUnr
    def contains(declared: Kind, part: Kind): Boolean = Kind.contains(declared, part)
    private[Sorts] def exceeded(declaration: String, declared: Kind, part: ContainedPart, partValue: Kind): TypeError =
      KindExceeded(declaration, declared, part, partValue)
  }

  object ScopeField extends Field[Lifetime](LifetimeTpe) {
    def of(sort: VSort): Lifetime = sort.scope
    def normalForm(value: Value): Lifetime = Interpreter.getLifetime(value)
    def join(parts: Iterable[Lifetime]): Lifetime = Lifetime.union(parts)
    def isLeast(part: Lifetime): Boolean = part.isEmpty
    def contains(declared: Lifetime, part: Lifetime): Boolean = Lifetime.contains(declared, part)
    private[Sorts] def exceeded(
        declaration: String,
        declared: Lifetime,
        part: ContainedPart,
        partValue: Lifetime
    ): TypeError =
      ScopeExceeded(declaration, declared, part, partValue)
  }

  /**
   * The one containment rule (spec §2.6): something that declares a kind or scope must contain each of its parts', else
   * `KindExceeded` or `ScopeExceeded` naming the part, at `site`. A lambda's written closure bounds its captures (spec
   * §4.3), a family's declared kind its fields' kinds, and its declared scope its lifetime parameters (spec §5.1).
   */
  def requireContains[P <: Value](
      field: Field[P],
      declaration: String,
      declared: P,
      part: ContainedPart,
      partValue: P,
      site: Span
  ): Unit =
    if (!field.contains(declared, partValue)) at(site)(fail(field.exceeded(declaration, declared, part, partValue)))

  /**
   * The type is a proposition: its values are proofs. A type in `Prop` is one, and so is a large function type into a
   * proposition (spec §2.4), whose instances are all propositions. A sort never qualifies, `Prop` included (`Prop :
   * Sort 1`): predicates are data, not proofs.
   */
  def isProposition(tpe: Value): Boolean =
    tpe match {
      case _: VSort => false
      // Impredicativity: a Pi is a proposition exactly when its codomain is Prop-valued, large or not. Answered
      // via the dedicated lazy val so proof canonicalization checks skip the full classifier computation.
      case pi: VPi => pi.isPropValued
      case tpe     => sortOf(tpe).exists(isProp)
    }
}
