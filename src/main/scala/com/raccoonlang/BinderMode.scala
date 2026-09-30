package com.raccoonlang

/**
 * How an application gives a binder its argument (docs/language.md#functions-and-binder-groups): written among its
 * explicit arguments, `(x: A)`; reconstructed from the types of later explicit arguments, `{x: A}`; or, for an evidence
 * binder `[h: P]`, discharged by evaluating its proposition where the application stands unless written in the
 * application's bracket group (PROOF_BY_EVALUATION §1). The mode is part of a function type's identity.
 */
sealed trait BinderMode

object BinderMode {
  case object Explicit extends BinderMode
  case object Implicit extends BinderMode
  case object Evidence extends BinderMode
}
