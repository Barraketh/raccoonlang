package com.raccoonlang

import com.raccoonlang.CoreAst.{ConstructorDecl, InductiveHeader}
import com.raccoonlang.Value._

/** Runtime publication for inductives.  Static formation and positivity are later milestones. */
object InductiveChecks {
  def evalInductive(decl: CoreAst.Decl.InductiveDecl, env: Env): Env = {
    evalInductiveBlock(Vector(decl), env)
  }

  /** Publish every family first, so constructor types can refer across a mutual block. */
  def evalInductiveBlock(decls: Vector[CoreAst.Decl.InductiveDecl], env: Env): Env = {
    val families = decls.map { decl =>
      val header = decl.header
      val meta = InductiveMeta(
        decl.ctors.map(c => ConstructorMeta(c.shortName, c.canonicalName)),
        header.binders.length
      )
      header.name -> VConst(header.name, Inductive(meta), familyType(header, env))
    }
    val withFamilies = families.foldLeft(env) { case (current, (name, value)) =>
      current.putGlobal(name, value)
    }
    decls.foldLeft(withFamilies) { case (current, decl) =>
      decl.ctors.foldLeft(current) { (ctorEnv, ctor) =>
        val header = decl.header
        val ctorType = constructorType(header, ctor, withFamilies)
        ctorEnv.putGlobal(
          ctor.canonicalName,
          ConstructorHead(
            ctor.canonicalName,
            header.params.length,
            header.params.length + ctor.binders.length,
            ctorType
          )
        )
      }
    }
  }

  private def familyType(header: InductiveHeader, env: Env): Value = {
    if (header.binders.isEmpty) Interpreter.evalTerm(header.resultTy, env)
    else Interpreter.evalPi(CoreAst.Term.Pi(header.binders, header.resultTy, header.span), env)
  }

  private def constructorType(header: InductiveHeader, ctor: ConstructorDecl, env: Env): Value = {
    val all = header.params ++ ctor.binders
    val bodyEnv = env
    if (all.isEmpty) Interpreter.evalTerm(ctor.resultTy, bodyEnv)
    else Interpreter.evalPi(CoreAst.Term.Pi(all, ctor.resultTy, ctor.span), bodyEnv)
  }
}
