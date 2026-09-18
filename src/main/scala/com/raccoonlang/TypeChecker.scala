package com.raccoonlang

import com.raccoonlang.CoreAst.{Decl, Program, Term => CTerm}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/** Bidirectional checker: unification is the conversion and refinement mechanism. */
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
  def assertType(value: Value): VSort = getUniverse(value)
  def getUniverse(value: Value): VSort = value.tpe match {
    case sort: VSort => sort
    case _           => throw NotAType(value.tpe)
  }
  private def sortOf(value: Value): VSort = assertType(value)

  def checkTerm(term: CTerm, env: Env): CheckedTerm = term match {
    case CTerm.GlobalRef(name, _) => CheckedTerm(env(name), term)
    case CTerm.LocalRef(ref, _)   => CheckedTerm(env(ref), term)
    case CTerm.NatLit(_, span)    => throw WTF(s"Natural literals are unavailable at $span")
    case CTerm.StrLit(_, span)    => throw WTF(s"String literals are unavailable at $span")
    case CTerm.Select(base, field, span) =>
      val checkedBase = checkTerm(base, env)
      CheckedTerm(select(checkedBase.value, field, env, span), CTerm.Select(checkedBase.residual, field, span))
    case pi: CTerm.Pi => {
      val checked = checkPi(pi, env)
      CheckedTerm(checked.vpi, checked.residual)
    }
    case CTerm.Lam(pi, body, span, name, recursion, peers) =>
      checkLam(pi, body, env, span, name, recursion, peers)
    case CTerm.App(fn, args, span) => checkApp(fn, args, env, span)
    case CTerm.Body(lets, result, span) =>
      checkBody(CTerm.Body(lets, result, span), env, None)
    case matchTerm: CTerm.Match => MatchChecker.checkMatch(matchTerm, env, None)
  }

  /** Resolve a selector through the structure's ordinary generated definition. */
  private def select(base: Value, field: String, env: Env, span: Span): Value = {
    val normalized = base match {
      case head: ConstructorHead if head.totalArity == 0 => VCtor(head, Vector.empty, head.tpe)
      case value                                         => value
    }
    normalized.tpe match {
      case InductiveFamilyValue(instance) =>
        // C09 has no value-to-core quoting, so a residual Select is retained here; resolve it
        // through the ordinary generated Family.field definition with explicit family arguments.
        val fn = env(s"${instance.head.name}.$field")
        Interpreter.evalApply(fn, instance.args :+ normalized)
      case _ => throw NotFound(field, Some(span))
    }
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
    val checkedPi = Interpreter.evalPi(residual, env)
    checkedPi.tpe
    CheckedPi(checkedPi, scope, checkedOut.value, residual)
  }

  private[raccoonlang] def check(term: CTerm, expected: Option[Expected], env: Env): CheckedTerm = {
    term match {
      case body: CTerm.Body       => return checkBody(body, env, expected)
      case matchTerm: CTerm.Match => return MatchChecker.checkMatch(matchTerm, env, expected)
      case _                      =>
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
      TerminationChecker.assertNonRawRecursive(checkedValue.value, let.span)
      (
        current.putLocal(let.localRef, checkedValue.value),
        out :+ let.copy(ty = checkedTy.map(_.residual), value = checkedValue.residual)
      )
    }
    val checkedResult = check(body.res, expected, bodyEnv)
    TerminationChecker.assertNonRawRecursive(checkedResult.value, body.res.span)
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
    val bodyEnvWithSelf = recursion match {
      case Some(rec) =>
        val recursive = TerminationChecker.rawRecursiveSelf(
          name.getOrElse(rec.selfRef.name),
          vpi,
          rec.decreases,
          bodyEnv0
        )
        bodyEnv0.putLocal(rec.selfRef, recursive)
      case None => bodyEnv0
    }
    val bodyEnvWithPeers = peers.foldLeft(bodyEnvWithSelf) { case (current, (ref, peerName)) =>
      if (current.locals.contains(ref)) current
      else
        current.globals.get(peerName).map(binding => current.putLocal(ref, binding.value(current))).getOrElse(current)
    }
    val checkedBody =
      check(body, Some(Expected(vpi.codomain(bodyEnvWithPeers), Some(checkedPi.residual.out))), bodyEnvWithPeers)
    TerminationChecker.assertNonRawRecursive(checkedBody.value, body.span)
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
              TerminationChecker.assertNonRawRecursive(checked.value, arg.span)
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
      InductiveChecks.checkInductiveBlock(Decl.InductiveBlock(families, span), env)
    case Decl.RecursiveDefBlock(defs, span) =>
      checkRecursiveDefBlock(Decl.RecursiveDefBlock(defs, span), env)
  }

  private def checkRecursiveDefBlock(block: Decl.RecursiveDefBlock, env: Env): Env = {
    val defs = block.definitions
    if (defs.isEmpty) throw InvalidRecursiveGroup("recursive group must not be empty", Some(block.span))
    if (defs.map(_.name).distinct.length != defs.length)
      throw InvalidRecursiveGroup("recursive names must be distinct", Some(block.span))
    defs.foreach(definition => if (env.globals.contains(definition.name)) throw AlreadyDefined(definition.name))
    if (defs.map(_.peerRef).distinct.length != defs.length)
      throw InvalidRecursiveGroup("recursive peer refs must be distinct", Some(block.span))
    val collisions = defs.map(_.peerRef).filter(env.locals.contains)
    if (collisions.nonEmpty)
      throw InvalidRecursiveGroup(s"recursive peer ref collides with local ${collisions.head.name}", Some(block.span))
    val typed = defs.map { definition =>
      val checked = checkTerm(definition.ty, env)
      sortOf(checked.value)
      definition -> (checked.value, checked.residual.asInstanceOf[CTerm.Pi])
    }
    val peerEnv = typed.foldLeft(env) { case (current, (definition, (ty, _))) =>
      current.putLocal(definition.peerRef, VConst(definition.name, Symbol, ty))
    }
    val checkedMetrics = typed.map { case (definition, (ty, _)) =>
      definition -> TerminationChecker.checkLexicographic(
        ty.asInstanceOf[VPi],
        definition.decreases,
        bindPi(ty.asInstanceOf[VPi], peerEnv)
      )
    }.toMap
    val residual = typed.map { case (definition, (ty, checkedTy)) =>
      val pi = ty.asInstanceOf[VPi]
      val callerEnv = bindPi(pi, env)
      val checkedPeerEnv = typed.foldLeft(callerEnv) { case (current, (callee, (calleeTy, _))) =>
        val calleePi = calleeTy.asInstanceOf[VPi]
        val raw = TerminationChecker.rawRecursivePeer(
          callee.name,
          calleePi,
          checkedMetrics(callee),
          checkedMetrics(definition),
          callerEnv
        )
        current.putLocal(callee.peerRef, raw)
      }
      val scoped = checkedPeerEnv
      val body = check(definition.body, Some(Expected(pi.codomain(scoped), Some(checkedTy.out))), scoped)
      TerminationChecker.assertNonRawRecursive(body.value, definition.body.span)
      definition.copy(ty = checkedTy, body = body.residual)
    }
    Interpreter.evalDecl(Decl.RecursiveDefBlock(residual, block.span), env)
  }

  def checkProgram(program: Program, initial: Env = Interpreter.builtins): (Env, Option[CheckedTerm]) = {
    val env = program.decls.foldLeft(initial) { case (current, decl) => checkDecl(decl, current) }
    (env, program.body.map(checkTerm(_, env)))
  }
}
