package com.raccoonlang

import com.raccoonlang.CoreAst.{ConstructorDecl, InductiveHeader}
import com.raccoonlang.Value._

/** Runtime publication for inductives.  Static formation and positivity are later milestones. */
object InductiveChecks {

  /** Check a mutual block against all provisional family heads, then publish it atomically. */
  def checkInductiveBlock(decls: Vector[CoreAst.Decl.InductiveDecl], env: Env): Env = {
    if (decls.isEmpty) throw WTF("Inductive block must not be empty")
    val names = decls.map(_.header.name)
    if (names.distinct.length != names.length) throw AlreadyDefined(names.find(n => names.count(_ == n) > 1).get)
    names.foreach(name => if (env.globals.contains(name)) throw AlreadyDefined(name))
    val provisionalNames = decls.foldLeft(env) { case (current, decl) =>
      val meta = InductiveMeta(
        decl.ctors.map(c => ConstructorMeta(c.shortName, c.canonicalName)),
        decl.header.binders.length
      )
      current.putGlobal(decl.header.name, VConst(decl.header.name, Inductive(meta), Value.TypeValue))
    }
    val provisional = decls.foldLeft(provisionalNames) { case (current, decl) =>
      val meta = current(decl.header.name) match {
        case VConst(_, Inductive(value), _) => value
        case _                              => throw WTF("Invalid provisional inductive head")
      }
      current.copy(
        globals = current.globals.updated(
          decl.header.name,
          GlobalBinding.Strict(VConst(decl.header.name, Inductive(meta), familyType(decl.header, provisionalNames)))
        )
      )
    }
    val constructorNames = decls.flatMap(_.ctors.map(_.canonicalName))
    if (constructorNames.exists(names.contains)) throw AlreadyDefined(constructorNames.find(names.contains).get)
    if (constructorNames.distinct.length != constructorNames.length)
      throw AlreadyDefined(constructorNames.find(n => constructorNames.count(_ == n) > 1).get)
    constructorNames.foreach(name => if (env.globals.contains(name)) throw AlreadyDefined(name))
    val firstParams = decls.head.header.params
    val (canonicalEnv, _) = checkBinders(firstParams, provisional)
    val canonicalValues = firstParams.map(binder => canonicalEnv(binder.localRef))
    decls.tail.foreach { decl =>
      val params = decl.header.params
      if (params.length != firstParams.length) throw WTF("Mutual inductive families must have the same parameter count")
      var current = provisional
      params.zip(firstParams).zipWithIndex.foreach { case ((actual, expected), index) =>
        if (actual.isImplicit != expected.isImplicit)
          throw WTF("Mutual inductive parameters must have matching modes")
        val checkedTy = TypeChecker.checkTerm(actual.ty, current)
        Value.sortOf(checkedTy.value)
        val expectedTy = Interpreter.evalTerm(expected.ty, canonicalEnv)
        TypeChecker.checkFits(checkedTy.value, expectedTy)
        current = current.putLocal(actual.localRef, canonicalValues(index))
      }
    }
    decls.foreach { decl =>
      val (headerEnv, _) = checkBinders(decl.header.binders, provisional)
      Value.sortOf(TypeChecker.checkTerm(decl.header.resultTy, headerEnv).value)
      val (parameterEnv, _) = checkBinders(decl.header.params, provisional)
      decl.ctors.foreach { ctor =>
        // Constructor fields see family parameters and their own fields, but not family
        // indices: indices are determined by the constructor result.
        val (ctorEnv, _) = checkBinders(ctor.binders, parameterEnv)
        val checkedResult = TypeChecker.checkTerm(ctor.resultTy, ctorEnv)
        Value.sortOf(checkedResult.value)
        val (head, args) = resultSpine(checkedResult.value).getOrElse(
          throw WTF(s"Constructor ${ctor.canonicalName} must return ${decl.header.name}")
        )
        if (head.name != decl.header.name || args.length != decl.header.binders.length)
          throw WTF(
            s"Constructor ${ctor.canonicalName} must return ${decl.header.name} with ${decl.header.binders.length} arguments"
          )
        decl.header.params.zipWithIndex.foreach { case (parameter, index) =>
          if (!ValueEquivalence.defEq(args(index), parameterEnv(parameter.localRef)))
            throw WTF(s"Constructor ${ctor.canonicalName} must return the declared family parameters")
        }
      }
    }
    evalInductiveBlock(decls, env)
  }

  def checkInductive(decl: CoreAst.Decl.InductiveDecl, env: Env): Env = {
    checkInductiveBlock(Vector(decl), env)
  }

  private def checkBinders(binders: Vector[CoreAst.Binder], env: Env): (Env, Vector[CoreAst.Binder]) =
    binders.foldLeft((env, Vector.empty[CoreAst.Binder])) { case ((current, out), binder) =>
      val checked = TypeChecker.checkTerm(binder.ty, current)
      Value.sortOf(checked.value)
      val next = current.putLocal(binder.localRef, Interpreter.rigidBinderValue(binder.localRef, checked.value))
      (next, out :+ binder.copy(ty = checked.residual))
    }

  private def resultSpine(value: Value): Option[(VConst, Vector[Value])] = value match {
    case head: VConst                                                => Some(head -> Vector.empty)
    case VApp(head: VConst, args, _, blockedOn) if blockedOn.isEmpty => Some(head -> args)
    case _                                                           => None
  }

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
