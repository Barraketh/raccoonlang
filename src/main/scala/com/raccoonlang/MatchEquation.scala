package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/**
 * The equation a match names (docs/implemented/MATCH_EQUATION.md): in the case of constructor `C` with fields `x̄`, `h`
 * proves `Eq(T, e, C(p̄, x̄))`, `T` the scrutinee's type and `p̄` its parameters. Its `Eq` is the trusted prelude's,
 * validated at the end of prelude loading as the equality family, so the hypothesis a case is checked under is one
 * reflexivity proves whenever the case runs, whatever a program declares. A prelude whose `Eq` is not that has no named
 * equations, and nor do its own declarations, which are checked before it ends.
 */
object MatchEquation {
  val familyName = "Eq"
  val reflName = "Eq.refl"

  /** The prelude's `Eq`, validated as the equality family: only `validate` makes one. */
  final class ValidatedEquality private[MatchEquation] (val family: Value)

  /**
   * The prelude's `Eq` if it is exactly the equality family the bundled prelude declares,
   * `{u: Level}(A: Type { level = u }) indices (x: A)(y: A) : Prop`, unsealed, whose one constructor is
   * `Eq.refl (x: A) : Eq(A, x, x)`, and otherwise why a named equation is unavailable.
   */
  private[raccoonlang] def validate(env: Env): Either[String, ValidatedEquality] = {
    def global(name: String): Option[Value] = env.globals.get(name).map(_.value(env))
    def require(holds: Boolean, reason: String): Either[String, Unit] = Either.cond(holds, (), reason)
    val modes = Vector(BinderMode.Implicit) ++ Vector.fill(3)(BinderMode.Explicit)
    for {
      family <- global(familyName).toRight("the prelude declares no `Eq`")
      meta <- family match {
        case VConst(`familyName`, Inductive(meta), _)
            if meta.familyArity == 4 && meta.block.key.numParams == 2 && meta.constructorNames == Vector(reflName) =>
          Right(meta)
        case _ =>
          Left("the prelude's `Eq` is not a family of two parameters and two indices whose one constructor is `refl`")
      }
      _ <- require(meta.seal.isEmpty, "the prelude's `Eq` is sealed")
      pi <- family.tpe match {
        case pi: VPi if pi.binders.map(_.mode) == modes => Right(pi)
        case _ => Left("the prelude's `Eq` does not bind `{u}(A)(x)(y)` in one group")
      }
      fresh = BinderOps.freshen(pi)
      (params, indices) = pi.binders.map(binder => fresh(binder.localRef)).splitAt(2)
      sortParams <- params match {
        case Vector(level: Level, a) => Right((level, a))
        case _                       => Left("the prelude's `Eq` does not bind `{u: Level}`")
      }
      (level, a) = sortParams
      _ <- require(
        ValueEquivalence.defEq(a.tpe, Sorts.sort(level, Kind.unr)),
        "the prelude's `Eq` does not range over `A: Type { level = u }`"
      )
      _ <- require(
        indices.forall(index => ValueEquivalence.defEq(index.tpe, a)),
        "the prelude's `Eq` is not over `(x: A)(y: A)`"
      )
      _ <- require(
        ValueEquivalence.defEq(pi.codomain(fresh), Sorts.Prop),
        "the prelude's `Eq` is not a `Prop`"
      )
      refl <- global(reflName) match {
        case Some(refl: ConstructorHead)
            if refl.numErasedFamilyArgs == 2 && refl.fieldBinders.map(_.mode) == Vector(BinderMode.Explicit) =>
          Right(refl)
        case _ => Left("the prelude's `Eq.refl` is not a constructor of one explicit field")
      }
      (fields, resultTy) = BinderOps.freshCtorFields(refl, params, Vector.empty)
      reflexive = Interpreter.evalApply(family, params ++ Vector(fields.head, fields.head))
      _ <- require(
        ValueEquivalence.defEq(fields.head.tpe, a) && ValueEquivalence.defEq(resultTy, reflexive),
        "the prelude's `Eq.refl` is not `(x: A) : Eq(A, x, x)`"
      )
    } yield new ValidatedEquality(family)
  }

  /**
   * `Eq(T, scrut, C(p̄, fields))`, `T` the scrutinee's type and `p̄` its parameters, which a constructor value erases:
   * the proposition a case of `ctor` binds its equation at. `MatchChecker` requires `T` unrestricted, so its sort is
   * one that `Eq` 's parameter ranges over.
   */
  private[raccoonlang] def proposition(
      equality: ValidatedEquality,
      scrut: Value,
      ctor: ConstructorHead,
      fields: Vector[Value]
  ): Value = {
    val tpe = scrut.tpe
    val sort = tpe.tpe match {
      case sort: VSort => sort
      case other       => wtf(s"The scrutinee type $tpe is classified by $other, which is not a sort")
    }
    val constructed = Packed.construct(ctor, fields, tpe)
    Interpreter.evalApply(equality.family, Vector(sort.level, tpe, scrut, constructed))
  }
}
