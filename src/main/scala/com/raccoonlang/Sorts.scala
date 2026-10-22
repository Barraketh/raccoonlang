package com.raccoonlang

import com.raccoonlang.Value.{Kind, KindTpe, Large, Level, ParameterTpe, SortParameter, VPi, VSort}

/**
 * The one place sorts are built and classified (docs/kernel.md#universes-and-function-types). `VSort` is constructed
 * only here, read through its fields, and compared only by conversion. Whether a sort is `Prop`, and whether a type is
 * a proposition, is answered here and nowhere else, so proof irrelevance and the checker cannot disagree about it.
 */
object Sorts {

  /** Data universes start at zero; Prop has a distinct tag and unrestricted proofs. */
  def sort(level: Level, kind: Kind): VSort = new VSort(false, level, kind)

  val Prop: VSort = new VSort(true, Level.zero, Kind.unr)

  val Type: VSort = sort(Level.zero, Kind.unr)

  def isProp(sort: VSort): Boolean = sort.isProp

  /**
   * The sort of the type `tpe`, which says what its values hold: their kind. A large type and a sort parameter have
   * none, since no sort classifies either, so their values hold nothing. Anything else is not a type, and asking is a
   * bug. Linearity, a lambda's captures and propositions read a type's sort here; where a position requires a type,
   * `TypeChecker.getUniverse` refuses one without a sort instead.
   */
  def sortOf(tpe: Value): Option[VSort] =
    tpe.tpe match {
      case sort: VSort           => Some(sort)
      case Large | SortParameter => None
      case classifier            => wtf(s"The type $tpe is classified by $classifier, which is no classifier")
    }

  /** A sort's kind, also the field a function type's closure carries. */
  sealed abstract class Field[P <: Value](val parameter: ParameterTpe) {
    def of(sort: VSort): P

    /** A checked expression of the field's sort parameter, which denotes a normal form. */
    def normalForm(value: Value): P

    def join(parts: Iterable[P]): P

    /**
     * What a lambda that captures a local holding `value` holds of this field: its type's sort's kind. A level
     * variable, a kind variable and a recursive definition's reference to itself, whose type may be large, contribute
     * the least: none is a value the lambda holds.
     */
    def ofCapture(value: Value): P

    /** `Kind.unr`: the unit of the join, and what every substitution keeps. */
    def isLeast(part: P): Boolean

    def contains(declared: P, part: P): Boolean

    private[Sorts] def exceeded(declaration: String, declared: P, part: ContainedPart, partValue: P): TypeError
  }

  object KindField extends Field[Kind](KindTpe) {
    def of(sort: VSort): Kind = sort.kind
    def normalForm(value: Value): Kind = Interpreter.getKind(value)
    def join(parts: Iterable[Kind]): Kind = Kind.join(parts)
    def ofCapture(value: Value): Kind = sortOf(value.tpe).fold(Kind.unr)(_.kind)
    def isLeast(part: Kind): Boolean = part.isUnr
    def contains(declared: Kind, part: Kind): Boolean = Kind.contains(declared, part)
    private[Sorts] def exceeded(declaration: String, declared: Kind, part: ContainedPart, partValue: Kind): TypeError =
      KindExceeded(declaration, declared, part, partValue)
  }

  /**
   * A declaration's kind must contain each part's kind, else `KindExceeded` identifies the part at its source site.
   * This applies to lambda captures and a family's fields.
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
   * Type`): predicates are data, not proofs.
   */
  def isProposition(tpe: Value): Boolean =
    tpe match {
      case _: VSort => false
      // Impredicativity: a Pi is a proposition exactly when its codomain is Prop-valued, large or not. Answered
      // via the classification recorded at formation so proof canonicalization skips the full classifier computation.
      case pi: VPi => pi.isPropValued
      case tpe     => sortOf(tpe).exists(isProp)
    }
}
