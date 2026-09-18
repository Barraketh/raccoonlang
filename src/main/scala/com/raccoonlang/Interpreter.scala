package com.raccoonlang

import com.raccoonlang.CoreAst.{Decl, Program, Term}
import com.raccoonlang.Value._

/** The runtime evaluator; static validation is performed by TypeChecker. */
object Interpreter {
  val builtins: Env = Env.empty.putGlobal("Type", TypeValue).putGlobal("Level", LevelTpe)

  def evalPi(pi: Term.Pi, env: Env): VPi = {
    val closed = env.closeForEval(CapturedRefs.getCapturedRefs(pi, env))
    evalPiClosed(pi, closed)
  }

  def rigidBinderValue(ref: CoreAst.LocalRef, tpe: Value): Value =
    FreshVar.freshVar(ref.name, tpe)

  /** Continue reduction when an EqStore solved a value's blocker. */
  def resolveInEqStore(value: Value, store: EqStore): Value = {
    val forced = store.force(value)
    forced match {
      case VApp(head, args, tpe, blocked) if blocked.intersects(store.solvedIds) =>
        val resolvedHead = ValueOps.materialize(resolveInEqStore(head, store), store)
        val resolvedArgs = args.map(ValueOps.materialize(_, store))
        resolvedHead match {
          case lambda: VLam                => resolveInEqStore(evalApply(lambda, resolvedArgs), store)
          case next @ Blocker(nextBlocked) => VApp(next, resolvedArgs, ValueOps.materialize(tpe, store), nextBlocked)
          case other                       => resolveInEqStore(evalApply(other, resolvedArgs), store)
        }
      case thunk: NeutralThunk if thunk.blockedOn.intersects(store.solvedIds) =>
        resolveInEqStore(evalTerm(thunk.term, ValueOps.materializeEnv(thunk.env, store)), store)
      case _ => forced
    }
  }

  def evalPiClosed(pi: Term.Pi, env: Env): VPi = {
    val classifier = VSort(0)
    val captures = env.locals.values.toVector
    VPi(
      env,
      pi.binders,
      bodyEnv => evalTerm(pi.out, bodyEnv),
      env.dependencies,
      Value.ValueId.LocalId(pi.nodeId, captures),
      () => classifier
    )
  }

  def evalTerm(term: Term, env: Env): Value = term match {
    case Term.GlobalRef(name, _) =>
      env(name) match {
        case head: ConstructorHead if head.totalArity == 0 => VCtor(head, Vector.empty, head.tpe)
        case value                                         => value
      }
    case Term.LocalRef(ref, _)   => env(ref)
    case Term.NatLit(_, span)    => throw WTF(s"Natural literals are unavailable at $span")
    case Term.StrLit(_, span)    => throw WTF(s"String literals are unavailable at $span")
    case Term.Select(_, _, span) => throw WTF(s"Projections are unavailable at $span")
    case pi: Term.Pi             => evalPi(pi, env)
    case lam: Term.Lam           => evalLam(lam, env)
    case Term.App(fn, args, _) =>
      val values = args.map(arg => evalTerm(arg, env))
      evalApply(evalTerm(fn, env), values)
    case Term.Body(lets, result, _) =>
      evalBody(lets, result, env)
    case matchTerm: Term.Match => evalMatch(matchTerm, env)
  }

  private def evalMatch(matchTerm: Term.Match, env: Env): Value = {
    val scrut = evalTerm(matchTerm.scrut, env)
    val cases = matchTerm.cases
    val selected = Value.ConstructorForm.unapply(scrut)
    selected match {
      case Some((name, fields)) =>
        cases.find(c => c.ctorName == name || c.ctorName == name.split('.').last) match {
          case None => throw WTF(s"No match case for $name at ${matchTerm.span}")
          case Some(branch) =>
            if (branch.argRefs.length != fields.length) throw ArityMismatch(fields.length, branch.argRefs.length)
            evalBranch(branch, fields, env)
        }
      case None =>
        val outType = matchOutType(matchTerm, scrut, env)
        val closed = env.closeForEval(CapturedRefs.getCapturedRefs(matchTerm, env))
        val blockedOn = Blocker.unapply(scrut).getOrElse(DepSet.empty)
        NeutralThunk(
          matchTerm,
          closed,
          ValueId.LocalId(matchTerm.nodeId, closed.locals.values.toVector),
          outType,
          blockedOn
        )
    }
  }

  private[raccoonlang] def matchOutType(matchTerm: Term.Match, scrut: Value, env: Env): Value =
    matchTerm.motive.map(evalTerm(_, env)).getOrElse(scrut.tpe)

  private[raccoonlang] def evalBranch(branch: CoreAst.Case, fields: Vector[Value], env: Env): Value = {
    if (branch.argRefs.length != fields.length) throw ArityMismatch(fields.length, branch.argRefs.length)
    val branchEnv = branch.argRefs.zip(fields).foldLeft(env) {
      case (current, (Some(ref), value)) => current.putLocal(ref, value)
      case (current, (None, _))          => current
    }
    evalTerm(branch.body, branchEnv)
  }

  private def evalBody(lets: Vector[CoreAst.Let], result: Term, env: Env): Value = {
    val bodyEnv = lets.foldLeft(env) { case (current, let) =>
      current.putLocal(let.localRef, evalTerm(let.value, current))
    }
    evalTerm(result, bodyEnv)
  }

  def evalApply(fn: Value, args: Vector[Value]): Value = {
    fn match {
      case lam: VLam => runLam(lam, args)
      case head: ConstructorHead =>
        if (args.length != head.totalArity) throw ArityMismatch(head.totalArity, args.length)
        val result = resultType(head.tpe, args)
        VCtor(head, Value.constructorStoredArgs(head, args), result)
      case value =>
        value.tpe match {
          case pi: VPi =>
            if (args.length != pi.binders.length) throw ArityMismatch(pi.binders.length, args.length)
            val blocked = Blocker.unapply(value).getOrElse(DepSet.empty)
            VApp(value, args, resultType(pi, args), blocked)
          case _ => throw CannotApplyNonFunction(value)
        }
    }
  }

  private def resultType(tpe: Value, args: Vector[Value]): Value = tpe match {
    case pi: VPi => resultType(pi, args)
    case _       => throw CannotApplyNonFunction(tpe)
  }

  def resultType(pi: VPi, args: Vector[Value]): Value = {
    if (args.length != pi.binders.length) throw ArityMismatch(pi.binders.length, args.length)
    val applied = pi.binders.zip(args).foldLeft(pi.env) { case (current, (binder, value)) =>
      current.putLocal(binder.localRef, value)
    }
    pi.codomain(applied)
  }

  private def evalLam(lam: Term.Lam, env: Env): VLam = {
    val closure = env.closeForEval(CapturedRefs.getCapturedRefs(lam, env))
    val id =
      lam.name.map(Value.ValueId.Const).getOrElse(Value.ValueId.LocalId(lam.nodeId, closure.locals.values.toVector))
    VLam(evalPiClosed(lam.ty, closure), id, Value.LamBody.Core(lam, closure))
  }

  def runLam(lam: VLam, args: Vector[Value]): Value = lam.body match {
    case Value.LamBody.Core(term, closure) =>
      if (args.length != lam.tpe.binders.length) throw ArityMismatch(lam.tpe.binders.length, args.length)
      val applied = lam.tpe.binders.zip(args).foldLeft(closure) { case (current, (binder, value)) =>
        current.putLocal(binder.localRef, value)
      }
      val withPeers = term.recursivePeers.foldLeft(term.recursion match {
        case Some(recursion) => applied.putLocal(recursion.selfRef, lam)
        case None            => applied
      }) { case (current, (ref, name)) =>
        if (current.locals.contains(ref)) current
        else if (term.recursion.exists(_.selfRef == ref)) current.putLocal(ref, lam)
        else current.putLocal(ref, closure(name))
      }
      evalTerm(term.body, withPeers)
  }

  def evalDecl(decl: Decl, env: Env): Env = decl match {
    case Decl.ConstDecl(isOpaque, name, ty, body, _) =>
      val valueType = evalTerm(ty, env)
      if (isOpaque) env.putOpaque(name, valueType)
      else
        body match {
          case CoreAst.ConstBody.TermBody(term) => env.putGlobal(name, evalTerm(term, env))
          case CoreAst.ConstBody.Builtin(span) =>
            throw WTF(s"Builtin bodies are unavailable at $span")
        }
    case Decl.AxiomDecl(name, ty, _)            => env.putOpaque(name, evalTerm(ty, env))
    case d: Decl.InductiveDecl                  => InductiveChecks.evalInductive(d, env)
    case Decl.InductiveBlock(families, _)       => InductiveChecks.evalInductiveBlock(families, env)
    case Decl.RecursiveDefBlock(definitions, _) => evalRecursive(definitions, env)
  }

  private def evalRecursive(definitions: Vector[CoreAst.RecursiveDef], env: Env): Env = {
    val names = definitions.map(_.name)
    env.putRecursiveGroup(
      names,
      groupEnv => {
        val peers = definitions.map(definition => definition.peerRef -> definition.name)
        definitions.map { definition =>
          val recursion = CoreAst.Recursion(definition.peerRef, definition.decreases)
          val lambda = Term.Lam(
            definition.ty,
            definition.body,
            definition.span,
            Some(definition.name),
            Some(recursion),
            peers
          )
          evalLam(lambda, groupEnv) match {
            case value: VLam => value
            case other       => throw WTF(s"Recursive definition ${definition.name} produced $other")
          }
        }
      }
    )
  }

  def run(program: Program, initial: Env = builtins): Option[Value] = {
    val env = program.decls.foldLeft(initial) { case (current, decl) => evalDecl(decl, current) }
    program.body.map(evalTerm(_, env))
  }
}
