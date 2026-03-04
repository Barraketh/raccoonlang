package com.raccoonlang

import com.raccoonlang.CoreAst.Term.Match
import com.raccoonlang.CoreAst._
import com.raccoonlang.Util.NEL

import scala.collection.immutable.BitSet

object Interpreter {
  sealed trait ConstType
  case object ConstructorHead extends ConstType
  case class Inductive(constructorNames: Vector[String]) extends ConstType
  case object Symbol extends ConstType

  sealed trait Value {
    def tpe: Value
    def synDeps: BitSet

    override def toString: String = PrettyPrinter.print(this)
  }

  sealed trait Head extends Value
  sealed trait Sort extends Value

  type VarId = Int

  // Identifier for lambdas to shortcut equality when possible.
  sealed trait LamId
  object LamId {
    final case class Const(name: String) extends LamId {
      override def toString: String = name
    }
    final case class LocalId(nodeId: Int, params: Vector[Value]) extends LamId
  }

  case class VType(level: Int) extends Sort {
    override def tpe: Value = VType(level + 1)
    override val synDeps: BitSet = BitSet.empty
  }

  case object VProp extends Sort {
    override def tpe: Value = VType(0)
    override val synDeps: BitSet = BitSet.empty
  }

  // Env must be mutable in order to allow recursion - lambdas and envs must be able to point to each other
  case class VPi(var env: Env, binders: NEL[Binder], out: TypeTerm, synDeps: BitSet, tpe: Sort) extends Value {
    override def toString: String = "VPi"
  }

  case class VConst(name: String, constType: ConstType, tpe: Value) extends Head {
    override val synDeps: BitSet = tpe.synDeps
  }

  case class VApp(head: Head, args: NEL[Value], tpe: Value) extends Head {
    override lazy val synDeps: BitSet = {
      val res = collection.mutable.BitSet()
      res |= head.synDeps
      args.foreach(v => res |= v.synDeps)
      res |= tpe.synDeps
      res.toImmutable
    }
  }

  case class Var(name: String, id: VarId, tpe: Value) extends Head {
    override val synDeps: BitSet = tpe.synDeps + id
  }

  case class VLam(body: Term, tpe: VPi, id: LamId) extends Value {
    override lazy val synDeps: BitSet = {
      id match {
        case LamId.Const(_) => tpe.synDeps
        case LamId.LocalId(_, params) =>
          if (params.isEmpty) tpe.synDeps
          else {
            val res = collection.mutable.BitSet()
            res |= tpe.synDeps
            params.foreach(v => res |= v.synDeps)
            res.toImmutable
          }
      }
    }
  }

  case class StuckMatch(id: LamId.LocalId, term: Term.Match, scrut: Value, env: Env, tpe: Value) extends Value {
    override def synDeps: BitSet = {
      val res = collection.mutable.BitSet()
      res |= tpe.synDeps
      res |= scrut.synDeps
      id.params.foreach(v => res |= v.synDeps)
      res.toImmutable
    }
  }

  // Environment: tracks lexical scope
  final case class Env(globals: Map[String, Value], locals: Map[String, Value], parent: Option[Env]) {
    def find(name: String): Option[Value] =
      locals.get(name).orElse(globals.get(name)).orElse(parent.flatMap(_.find(name)))

    def findLocal(name: String): Option[Value] =
      locals.get(name).orElse(parent.flatMap(_.findLocal(name)))

    def putGlobal(name: String, value: Value): Env = {
      if (globals.contains(name))
        throw AlreadyDefined(name)
      else if (name == "_") this
      else Env(globals + (name -> value), locals, parent)
    }

    def putLocal(name: String, value: Value): Env = {
      if (locals.contains(name) || globals.contains(name))
        throw AlreadyDefined(name)
      else if (name == "_") this
      else Env(globals, locals + (name -> value), parent)
    }

    def newScope: Env = Env(Map.empty, Map.empty, Some(this))
  }

  object Env {
    val empty: Env = Env(globals = Map(), locals = Map(), parent = None)
  }

  // Tracks equalities between variables
  final case class EqStore(links: Map[VarId, Value]) {
    @annotation.tailrec
    def force(v: Interpreter.Value): Interpreter.Value = v match {
      case Interpreter.Var(_, id, _) =>
        links.get(id) match {
          case Some(v) => force(v)
          case None    => v
        }
      case other => other
    }

    def addLink(id: VarId, v: Interpreter.Value): EqStore = {
      if (links.contains(id)) throw VarAlreadyLinked(id)
      copy(links = links + (id -> v))
    }
  }

  object EqStore {
    val empty: EqStore = EqStore(Map())
  }

  def whnf(v: Value)(implicit eqStore: EqStore): Value = {
    val v0 = eqStore.force(v)
    v0 match {
      case VApp(h, args, tpe) =>
        val h0 = whnf(h)
        h0 match {
          case lam: VLam =>
            val envWithArgs = getEnvWithArgs(lam.tpe, args)
            val res = evalTerm(lam.body, envWithArgs)
            whnf(res)
          case h0: Head =>
            // Head is not reducible
            if (h0 eq h) v0 else VApp(h0, args, tpe)
        }
      case vm: StuckMatch =>
        val scrut0 = whnf(vm.scrut)
        val stillStuck = if (vm.scrut eq scrut0) vm else vm.copy(scrut = scrut0)
        val head = scrut0 match {
          case VApp(h, _, _) => h
          case c: VConst     => c
          case _             => return stillStuck
        }

        head match {
          case VConst(_, `ConstructorHead`, _) => whnf(evalMatchBody(vm.term, scrut0, vm.env))
          case _                               => stillStuck
        }

      case _ => v0
    }
  }

  private def getEnvWithArgs(fnTpe: VPi, args: NEL[Value]): Env = {
    if (fnTpe.binders.length != args.length) throw ArityMismatch(fnTpe.binders.length, args.length)

    fnTpe.binders.map(_.name).zip(args).foldLeft(fnTpe.env.newScope) { case (curEnv, (name, value)) =>
      curEnv.putLocal(name, value)
    }
  }

  def evalPi(pi: Term.Pi, env: Env)(implicit eqStore: EqStore): VPi = {
    val (bodyEnv, argTypes) = pi.binders.foldLeft((env.newScope, Vector.empty[Value])) {
      case ((curEnv, curArgTypes), b) =>
        val tyV = evalTerm(b.ty, curEnv)
        (curEnv.putLocal(b.name, tyV), curArgTypes :+ tyV)
    }

    val outType = evalTerm(pi.out, bodyEnv)
    val tpe = whnf(outType.tpe) match {
      case VProp => VProp
      case VType(lvl) =>
        val paramLevels = argTypes.map { tyV =>
          whnf(tyV.tpe) match {
            case VType(pLvl) => pLvl
            case VProp       => -1
            case _           => throw NotAType(tyV)
          }
        }
        val resLevel = (paramLevels :+ lvl).max
        VType(resLevel)
      case _ => throw NotAType(outType)
    }

    VPi(env, pi.binders, pi.out, FreeNames.getDeps(pi, env, Set.empty), tpe)
  }

  // Evaluate a type-position expression without enforcing it is a type yet
  private def evalTT(tt: TypeTerm, env: Env)(implicit meta: EqStore): Value = tt match {
    case Term.Ident(name, sp)    => env.find(name).getOrElse { throw TypeError.withSpan(NotFound(name), sp) }
    case Term.TApp(fn, args, _)  => evalApplyTerm(fn, args, env)
    case pi: Term.Pi             => evalPi(pi, env)
    case Term.SortType(level, _) => VType(level)
    case Term.SortProp(_)        => VProp
  }

  private def evalApply(fn: Value, vArgs: NEL[Value])(implicit eqStore: EqStore): Value = {
    val fn0 = whnf(fn)
    val tpe0 = whnf(fn0.tpe)

    tpe0 match {
      case pi: VPi =>
        if (pi.binders.length != vArgs.length) throw ArityMismatch(pi.binders.length, vArgs.length)
        val envWithArgs: Env = getEnvWithArgs(pi, vArgs)
        fn0 match {
          case VLam(body, _, _) => evalTerm(body, envWithArgs)
          case h: Head          => VApp(h, vArgs, evalTT(pi.out, envWithArgs))
          case _                => throw CannotApplyNonFunction(fn)
        }
      case _ => throw CannotApplyNonFunction(fn.tpe)
    }
  }

  private def evalApplyTerm(fn: Term, args: NEL[Term], env: Env)(implicit eqStore: EqStore): Value = {
    val vf = evalTerm(fn, env)
    val vArgs = args.map(a => evalTerm(a, env))
    evalApply(vf, vArgs)
  }

  def evalLam(l: Term.Lam, vpi: VPi, env: Env): VLam = {
    val id = l.name match {
      case Some(funcName) => LamId.Const(funcName)
      case None =>
        val captureNames =
          FreeNames.getFreeNames(l, Set.empty).toVector.filter(n => env.findLocal(n).isDefined).sorted
        val captureVals = captureNames.map(n => env.findLocal(n).get)
        LamId.LocalId(l.span.start, captureVals)

    }
    VLam(l.body, vpi, id)
  }

  private def evalLam(l: Term.Lam, env: Env)(implicit eqStore: EqStore): VLam = {
    val vpi = evalPi(l.ty, env)
    evalLam(l, vpi, env)
  }

  def evalTerm(term: Term, env: Env)(implicit eqStore: EqStore): Value = {
    try {
      term match {
        case tt: TypeTerm          => evalTT(tt, env)
        case Term.App(fn, args, _) => evalApplyTerm(fn, args, env)
        case l: Term.Lam           => evalLam(l, env)
        case m: Term.Match         => evalMatch(m, env)
        case b: Term.Body          => evalBody(b, env)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }
  }

  private def evalMatch(m: Match, env: Env)(implicit eqStore: EqStore): Value = {
    val scrut = whnf(evalTerm(m.scrut, env))
    evalMatchBody(m, scrut, env)
  }

  private def evalMatchBody(m: Match, scrut: Value, env: Env)(implicit eqStore: EqStore): Value = {
    val withScrut = env.newScope.putLocal(m.scrutName, scrut)

    lazy val stuckMatch = {
      // Get all the free locals referenced in the body of the match - we will use them as the key, just like VLam
      // We can treat scrutName as bound, since we are including it in StuckMatch and will unify it separately
      val freeNames = m.cases
        .foldLeft(Set.empty[String]) { case (curNames, c) =>
          val nextNames = FreeNames.getFreeNames(c.body, bound = (c.argNames :+ m.scrutName).toSet)
          curNames.union(nextNames)
        }
        .toVector
        .filter(n => withScrut.findLocal(n).isDefined)
        .sorted
      val captures = freeNames.map(n => withScrut.findLocal(n).get)
      val id = LamId.LocalId(m.span.start, captures)

      val outType = evalTerm(m.motive, withScrut)

      StuckMatch(id, m, scrut, withScrut, outType)
    }

    val (head, args) = scrut match {
      case VApp(head, args, _) => (head, args.toList)
      case c: VConst           => (c, Nil)
      case _                   => return stuckMatch
    }

    head match {
      case VConst(ctorName, `ConstructorHead`, _) =>
        val branch =
          m.cases.find(c => c.ctorName == ctorName).getOrElse(throw UnknownConstructor(ctorName, "", Some(m.span)))
        if (args.length != branch.argNames.length)
          throw ArityMismatch(branch.argNames.length, args.length, Some(branch.span))
        val newEnv = args.zip(branch.argNames).foldLeft(withScrut.newScope) { case (curEnv, (argV, argName)) =>
          curEnv.putLocal(argName, argV)
        }
        evalTerm(branch.body, newEnv)
      case _ => stuckMatch
    }
  }

  def evalBody(body: Term.Body, env: Env)(implicit eqStore: EqStore): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = evalTerm(l.value, curEnv)
      curEnv.putLocal(l.name, res)
    }
    evalTerm(body.res, newEnv)
  }

  private def evalDecl(decl: Decl, env: Env): Env = {
    implicit val eqStore = EqStore.empty
    decl match {
      case Decl.ConstDecl(isInline, name, ty, body, _) =>
        val tyV = TypeChecker.getType(ty, env)
        val declConst = VConst(name, Symbol, tyV)

        // Allow recursive references by pre-binding a symbolic self during body checking
        val bodyOpt = body.map(b => TypeChecker.typecheck(b, env.putGlobal(name, declConst)))
        val value: Value = (bodyOpt, isInline) match {
          case (Some(v), true) => v
          case _               => declConst
        }
        val nextEnv = env.putGlobal(name, value)

        value match {
          case VLam(_, tpe, _) => tpe.env = nextEnv
          case _               =>
        }

        nextEnv

      case Decl.InductiveDecl(name, ty, ctors, _) =>
        val inductiveType = TypeChecker.getType(ty, env)
        val inductiveHead = VConst(name, Inductive(ctors.map(c => c.name)), inductiveType)
        val env2 = env.putGlobal(name, inductiveHead)
        ctors.foldLeft(env2) { case (curEnv, c) =>
          val ctorV = TypeChecker.getType(c.ty, env2)

          val ctorResTpe = ctorV match {
            case v: VConst => v
            case pi: VPi =>
              val (_, nextEnv) = FreshVar.assignFreshVars(pi, EqStore.empty)
              evalTerm(pi.out, nextEnv)
          }

          val ctorResTpeHead = ctorResTpe match {
            case VApp(head, _, _) => head
            case other            => other
          }

          Unify.unify(ctorResTpeHead, inductiveHead, EqStore.empty, Set.empty)
          curEnv.putGlobal(c.name, VConst(c.name, ConstructorHead, ctorV))
        }
    }

  }

  def run(p: Program): Value = {
    val baseEnv = Env.empty
    val env = p.decls.foldLeft(baseEnv) { case (env, decl) => evalDecl(decl, env) }
    TypeChecker.typecheck(p.body, env)(EqStore.empty)
  }
}
