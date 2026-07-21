package com.raccoonlang.translator

import com.raccoonlang.{CoreAst, Env}
import com.raccoonlang.telescope.BinderOps

private[translator] object ImportedBinderOps {

  /** The export supplies every argument, so every requested implicit may be demoted when it cannot be reconstructed. */
  def checkBinders(binders: Vector[CoreAst.Binder], baseEnv: Env): BinderOps.CheckedBinders = {
    val demotable = binders.indices.filter(idx => binders(idx).isImplicit).toSet
    BinderOps.checkBindersDemoting(binders, baseEnv, demotable)
  }
}
