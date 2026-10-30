package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/**
 * The equation a match names (docs/kernel.md, "Match equations"): in the case of constructor `C` with fields `x̄`,
 * `match h : e` binds `h : Eq(T, e, C(x̄))`, `T` the scrutinee's type in that case. Its `Eq` is the global `Eq`, used
 * only when it is exactly the equality family, so that the hypothesis a case is checked under is one that reflexivity
 * proves whenever the case runs, whatever family a program or a custom prelude calls `Eq`.
 */
object MatchEquation {
  val FamilyName = "Eq"
  val ReflName = "Eq.refl"

  /** The global `Eq`, validated as the equality family: only `validate` makes one. */
  final class Equality private[MatchEquation] (val family: VConst, val refl: ConstructorHead)

  /**
   * The global `Eq` if it is exactly the prelude's equality family, `Eq (A: Sort($u)) indices (x: A)(y: A) : Prop`,
   * whose one constructor is `Eq.refl (x: $A in Sort($u)) : Eq(A, x, x)`, and otherwise why a named equation is
   * unavailable. The family ranges over every copyable type, and its only inhabitants are reflexive.
   */
  def validate(env: Env): Either[String, Equality] = {
    def global(name: String): Option[Value] =
      try Some(env(name))
      catch { case _: NotFound => None }
    def require(holds: Boolean, reason: => String): Either[String, Unit] = Either.cond(holds, (), reason)
    val shape = "`Eq (A: Sort($u)) indices (x: A)(y: A) : Prop`"
    for {
      found <- global(FamilyName).toRight("no `Eq` is declared")
      declared <- found match {
        case family @ VConst(FamilyName, Inductive(meta), _)
            if meta.familyArity == 3 && meta.paramCount == 1 && meta.constructorNames == Vector(ReflName) =>
          Right(family -> meta)
        case _ => Left(s"`Eq` is not $shape with the one constructor `Eq.refl`")
      }
      (family, meta) = declared
      pi <- family.tpe match {
        case pi: VPi if pi.binders.length == 3 => Right(pi)
        case _                                 => Left(s"`Eq` is not $shape")
      }
      fresh = BinderOps.freshen(pi)
      args = pi.binders.map(binder => fresh(binder.localRef))
      _ <- require(
        args(0).tpe match {
          case VUniv(kind, level) => kind.isCopy && level.c == 0 && level.atoms.values.toVector == Vector(0)
          case _                  => false
        },
        s"`Eq` does not range over every copyable type, as $shape does"
      )
      _ <- require(
        args.drop(1).forall(index => ValueEquivalence.defEq(index.tpe, args(0))) && pi.codomain(fresh) == PropTpe,
        s"`Eq` is not $shape"
      )
      refl <- global(ReflName) match {
        case Some(refl: ConstructorHead) => Right(refl)
        case _                           => Left("`Eq.refl` is not a constructor")
      }
      opened = MatchChecker.freshCtor(refl, InductiveFamilyInstance(family, meta, args))
      _ <- require(
        opened.fieldArgs.length == 1 && {
          val x = opened.fieldArgs.head
          ValueEquivalence.defEq(x.tpe, args(0)) &&
          ValueEquivalence.defEq(opened.resultTy, Interpreter.evalApply(family, Vector(args(0), x, x)))
        },
        "`Eq.refl` is not `(x: $A in Sort($u)) : Eq(A, x, x)`"
      )
    } yield new Equality(family, refl)
  }

  /**
   * `Eq(T, scrut, constructed)`, `T` the type of `scrut`, a copyable data value: the proposition a case binds its
   * equation at. `constructed` is the case's constructor applied to its fields, at its own result type, so the
   * application checks that it is an equation of one type: in an indexed family it is not when the case's refinement
   * left the constructor's indices apart from the scrutinee's, and then this is `None`.
   */
  def proposition(equality: Equality, scrut: Value, constructed: Value): Option[Value] = {
    val args = Vector(scrut.tpe, scrut, constructed)
    equality.family.tpe match {
      case pi: VPi =>
        BinderOps
          .tryCheckAndInstantiate(pi.binders, pi.env, args)
          .map(_ => Interpreter.evalApply(equality.family, args))
      case other => throw WTF(s"The validated `Eq` has type $other")
    }
  }

  /**
   * The canonical proof of a case's equation where the case is taken, `Eq.refl(scrut)` for its scrutinee's value, a
   * constructor applied to the case's fields or, at a structure eta type, a value its projections view as one. The
   * checker validated `Eq` where it checked the match; evaluation reads the same globals.
   */
  def proof(env: Env, scrut: Value): Value = Interpreter.evalApply(env(ReflName), Vector(scrut))
}
