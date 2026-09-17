package com.raccoonlang

import com.raccoonlang.CoreAst.{Decl, Program, Term => CTerm}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/** First bidirectional checker: unification is the conversion and refinement mechanism. */
object TypeChecker {
  private final case class CheckedPi(vpi: VPi, bodyEnv: Env, outTy: Value, residual: CTerm.Pi)
  final case class CheckedTerm(value: Value, residual: CTerm)
  private[raccoonlang] final case class Expected(value: Value, syntax: Option[CTerm])

  def checkFits(actual: Value, expected: Value): Unit =
    ValueEquivalence.tryUnify(actual, expected, EqStore.empty) match {
      case Right(_) =>
      case Left(_)  => throw TypeMismatch(expected, actual)
    }

  def checkType(value: Value, expectedType: Value): Unit = checkFits(value.tpe, expectedType)
  private def sortOf(value: Value): VSort = Value.sortOf(value)

  def checkTerm(term: CTerm, env: Env): CheckedTerm = term match {
    case CTerm.GlobalRef(name, _) => CheckedTerm(env(name), term)
    case CTerm.LocalRef(ref, _)   => CheckedTerm(env(ref), term)
    case CTerm.NatLit(_, span)    => throw WTF(s"Natural literals are not available in C05 at $span")
    case CTerm.StrLit(_, span)    => throw WTF(s"String literals are not available in C05 at $span")
    case CTerm.Select(_, _, span) => throw WTF(s"Projections are not available in C05 at $span")
    case pi: CTerm.Pi => {
      val checked = checkPi(pi, env)
      CheckedTerm(checked.vpi, checked.residual)
    }
    case CTerm.Lam(pi, body, span, name, recursion, peers) =>
      checkLam(pi, body, env, span, name, recursion, peers)
    case CTerm.App(fn, args, span) => checkApp(fn, args, env, span)
    case CTerm.Body(lets, result, span) =>
      checkBody(CTerm.Body(lets, result, span), env, None)
    case CTerm.Match(_, _, _, span) => throw WTF(s"Match checking is not available until C06 at $span")
  }

  def checkTerm(term: CTerm, expected: Value, env: Env): CheckedTerm = {
    check(term, Some(Expected(expected, None)), env)
  }

  private def checkPi(pi: CTerm.Pi, env: Env): CheckedPi = {
    val (scope, binders) = pi.binders.foldLeft((env, Vector.empty[CoreAst.Binder])) { case ((current, out), binder) =>
      val checkedTy = checkTerm(binder.ty, current)
      sortOf(checkedTy.value)
      val bound = current.putLocal(binder.localRef, Interpreter.rigidBinderValue(binder.localRef, checkedTy.value))
      (bound, out :+ binder.copy(ty = checkedTy.residual))
    }
    val checkedOut = checkTerm(pi.out, scope)
    sortOf(checkedOut.value)
    val residual = pi.copy(binders = binders, out = checkedOut.residual)
    CheckedPi(Interpreter.evalPi(residual, env), scope, checkedOut.value, residual)
  }

  private def check(term: CTerm, expected: Option[Expected], env: Env): CheckedTerm = {
    term match {
      case body: CTerm.Body => return checkBody(body, env, expected)
      case _                =>
    }
    val checked = checkTerm(term, env)
    expected.foreach(exp => checkFits(checked.value.tpe, exp.value))
    checked
  }

  private def checkBody(body: CTerm.Body, env: Env, expected: Option[Expected]): CheckedTerm = {
    val (bodyEnv, checkedLets) = body.lets.foldLeft((env, Vector.empty[CoreAst.Let])) { case ((current, out), let) =>
      val checkedTy = let.ty.map(ty => checkTerm(ty, current))
      checkedTy.foreach(ty => sortOf(ty.value))
      val checkedValue = check(let.value, checkedTy.map(ty => Expected(ty.value, let.ty)), current)
      checkedTy.foreach(ty => checkFits(checkedValue.value.tpe, ty.value))
      (
        current.putLocal(let.localRef, checkedValue.value),
        out :+ let.copy(ty = checkedTy.map(_.residual), value = checkedValue.residual)
      )
    }
    val checkedResult = check(body.res, expected, bodyEnv)
    CheckedTerm(checkedResult.value, CTerm.Body(checkedLets, checkedResult.residual, body.span))
  }

  private def checkLam(
      pi: CTerm.Pi,
      body: CTerm,
      env: Env,
      span: Span,
      name: Option[String],
      recursion: Option[CoreAst.Recursion],
      peers: Vector[(CoreAst.LocalRef, String)]
  ): CheckedTerm = {
    val checkedPi = checkPi(pi, env)
    val vpi = checkedPi.vpi
    val bodyEnv0 = bindPi(vpi, vpi.env)
    val bodyEnv = recursion.foldLeft(bodyEnv0) { case (current, rec) =>
      current.putLocal(rec.selfRef, VConst(name.getOrElse(rec.selfRef.name), Symbol, vpi))
    }
    val bodyEnvWithPeers = peers.foldLeft(bodyEnv) { case (current, (ref, peerName)) =>
      if (current.locals.contains(ref)) current
      else
        current.globals.get(peerName).map(binding => current.putLocal(ref, binding.value(current))).getOrElse(current)
    }
    val checkedBody =
      check(body, Some(Expected(vpi.codomain(bodyEnvWithPeers), Some(checkedPi.residual.out))), bodyEnvWithPeers)
    val residualPi = checkedPi.residual
    val residualLam = CTerm.Lam(residualPi, checkedBody.residual, span, name, recursion, peers)
    val closure = env.closeForEval(CapturedRefs.getCapturedRefs(residualLam, env))
    CheckedTerm(
      VLam(
        Interpreter.evalPiClosed(residualPi, closure),
        name
          .map(Value.ValueId.Const)
          .getOrElse(Value.ValueId.LocalId(residualLam.nodeId, closure.locals.values.toVector)),
        Value.LamBody.Core(residualLam, closure)
      ),
      residualLam
    )
  }

  private def bindPi(pi: VPi, env: Env): Env =
    pi.binders.foldLeft(env) { case (current, binder) =>
      current.putLocal(
        binder.localRef,
        Interpreter.rigidBinderValue(binder.localRef, Interpreter.evalTerm(binder.ty, current))
      )
    }

  private def checkApp(fn: CTerm, args: Vector[CTerm], env: Env, span: Span): CheckedTerm = {
    val checkedFn = checkTerm(fn, env)
    checkedFn.value.tpe match {
      case pi: VPi =>
        if (args.length != pi.binders.length) throw ArityMismatch(pi.binders.length, args.length)
        val (_, checkedArgs, values) =
          args.zip(pi.binders).foldLeft((pi.env, Vector.empty[CTerm], Vector.empty[Value])) {
            case ((scope, out, vals), (arg, binder)) =>
              val binderType = Interpreter.evalTerm(binder.ty, scope)
              val checked = checkTerm(arg, binderType, env)
              (scope.putLocal(binder.localRef, checked.value), out :+ checked.residual, vals :+ checked.value)
          }
        BinderOps.checkAndInstantiate(pi.binders, pi.env, values)
        CheckedTerm(Interpreter.evalApply(checkedFn.value, values), CTerm.App(checkedFn.residual, checkedArgs, span))
      case other => throw CannotApplyNonFunction(other)
    }
  }

  def checkDecl(decl: Decl, env: Env): Env = decl match {
    case Decl.ConstDecl(isOpaque, name, ty, CoreAst.ConstBody.TermBody(body), _) =>
      val checkedTy = checkTerm(ty, env)
      sortOf(checkedTy.value)
      val checkedBody = check(body, Some(Expected(checkedTy.value, Some(checkedTy.residual))), env)
      if (isOpaque) env.putOpaque(name, checkedTy.value) else env.putGlobal(name, checkedBody.value)
    case Decl.ConstDecl(_, _, _, CoreAst.ConstBody.Builtin(span), _) =>
      throw WTF(s"Builtin bodies are unavailable at $span")
    case Decl.AxiomDecl(name, ty, _) =>
      val checked = checkTerm(ty, env); sortOf(checked.value); env.putOpaque(name, checked.value)
    case d: Decl.InductiveDecl => InductiveChecks.checkInductive(d, env)
    case Decl.InductiveBlock(families, span) =>
      InductiveChecks.checkInductiveBlock(families, env)
    case Decl.RecursiveDefBlock(defs, span) =>
      checkRecursiveDefBlock(Decl.RecursiveDefBlock(defs, span), env)
  }

  private def checkRecursiveDefBlock(block: Decl.RecursiveDefBlock, env: Env): Env = {
    val defs = block.definitions
    if (defs.isEmpty) throw WTF("Recursive group must not be empty")
    if (defs.map(_.name).distinct.length != defs.length) throw AlreadyDefined("duplicate recursive name")
    defs.foreach(definition => if (env.globals.contains(definition.name)) throw AlreadyDefined(definition.name))
    if (defs.map(_.peerRef).distinct.length != defs.length) throw WTF("Recursive peer refs must be distinct")
    val collisions = defs.map(_.peerRef).filter(env.locals.contains)
    if (collisions.nonEmpty) throw WTF(s"Recursive peer ref collides with local ${collisions.head.name}")
    val typed = defs.map { definition =>
      val checked = checkTerm(definition.ty, env)
      sortOf(checked.value)
      definition -> (checked.value, checked.residual.asInstanceOf[CTerm.Pi])
    }
    val peerEnv = typed.foldLeft(env) { case (current, (definition, (ty, _))) =>
      current.putLocal(definition.peerRef, VConst(definition.name, Symbol, ty))
    }
    val residual = typed.map { case (definition, (ty, checkedTy)) =>
      val pi = ty.asInstanceOf[VPi]
      val scoped = bindPi(pi, peerEnv)
      val body = check(definition.body, Some(Expected(pi.codomain(scoped), Some(checkedTy.out))), scoped)
      definition.copy(ty = checkedTy, body = body.residual)
    }
    Interpreter.evalDecl(Decl.RecursiveDefBlock(residual, block.span), env)
  }

  def checkProgram(program: Program, initial: Env = Interpreter.builtins): (Env, Option[CheckedTerm]) = {
    val env = program.decls.foldLeft(initial) { case (current, decl) => checkDecl(decl, current) }
    (env, program.body.map(checkTerm(_, env)))
  }
}
