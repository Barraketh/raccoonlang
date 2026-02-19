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

  type MetaId = Int

  // Identifier for lambdas to shortcut equality when possible.
  sealed trait LamId
  object LamId {
    final case class Const(name: String) extends LamId {
      override def toString: String = name
    }
    final case class LocalId(nodeId: Int, params: Vector[Value]) extends LamId
  }

  case object VUniverse extends Value {
    override def tpe: Value = VUniverse

    override val synDeps: BitSet = BitSet.empty
  }

  // Env must be mutable in order to allow recursion - lambdas and envs must be able to point to each other
  case class VPi(var env: Env, binders: NEL[Binder], out: TypeTerm, synDeps: BitSet) extends Value {
    override def tpe: Value = VUniverse

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

  case class Meta(name: String, id: MetaId, tpe: Value) extends Head {
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

  // Tracks solutions to metas
  final case class MetaStore(links: Map[MetaId, Value]) {
    def isLinked(id: MetaId): Boolean = links.contains(id)

    @annotation.tailrec
    def force(v: Interpreter.Value): Interpreter.Value = v match {
      case Interpreter.Meta(_, id, _) =>
        links.get(id) match {
          case Some(v) => force(v)
          case None    => v
        }
      case other => other
    }

    def addLink(id: MetaId, v: Interpreter.Value): MetaStore = {
      if (links.contains(id)) throw VarAlreadyLinked(id)
      copy(links = links + (id -> v))
    }
  }

  object MetaStore {
    val empty: MetaStore = MetaStore(Map())
  }

  def whnf(v: Value, meta: MetaStore): Value = {
    val v0 = meta.force(v)
    v0 match {
      case VApp(h, args, tpe) =>
        val h0 = whnf(h, meta)
        h0 match {
          case lam: VLam =>
            implicit val envWithArgs = getEnvWithArgs(lam.tpe, args)
            val res = evalTerm(lam.body, meta)
            whnf(res, meta)
          case h0: Head =>
            // Head is not reducible
            if (h0 eq h) v0 else VApp(h0, args, tpe)
        }
      case vm: StuckMatch =>
        val scrut0 = whnf(vm.scrut, meta)
        val stillStuck = if (vm.scrut eq scrut0) vm else vm.copy(scrut = scrut0)
        val head = scrut0 match {
          case VApp(h, _, _) => h
          case c: VConst     => c
          case _             => return stillStuck
        }

        head match {
          case VConst(_, `ConstructorHead`, _) => whnf(evalMatchBody(vm.term, scrut0, meta, vm.env), meta)
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

  def evalPi(pi: Term.Pi)(implicit env: Env): VPi =
    VPi(env, pi.binders, pi.out, FreeNames.getDeps(pi, env, Set.empty))

  // Evaluate a type-position expression without enforcing it is a type yet
  private def evalTT(tt: TypeTerm, meta: MetaStore)(implicit env: Env): Value = tt match {
    case Term.Ident(name, sp)   => env.find(name).getOrElse { throw TypeError.withSpan(NotFound(name), sp) }
    case Term.TApp(fn, args, _) => evalApplyTerm(fn, args, meta)
    case pi: Term.Pi            => evalPi(pi)
  }

  private def evalApply(fn: Value, vArgs: NEL[Value], meta: MetaStore): Value = {
    val fn0 = whnf(fn, meta)
    val tpe0 = whnf(fn0.tpe, meta)

    tpe0 match {
      case pi: VPi =>
        implicit val envWithArgs: Env = getEnvWithArgs(pi, vArgs)
        fn0 match {
          case VLam(body, _, _) => evalTerm(body, meta)
          case h: Head          => VApp(h, vArgs, evalTT(pi.out, meta))
          case _                => throw CannotApplyNonFunction(fn)
        }
      case _ => throw CannotApplyNonFunction(fn.tpe)
    }
  }

  private def evalApplyTerm(fn: Term, args: NEL[Term], meta: MetaStore)(implicit env: Env): Value = {
    val vf = evalTerm(fn, meta)
    val vArgs = args.map(a => evalTerm(a, meta))
    evalApply(vf, vArgs, meta)
  }

  def evalLam(l: Term.Lam, vpi: VPi)(implicit env: Env): VLam = {
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

  private def evalLam(l: Term.Lam)(implicit env: Env): VLam = {
    val vpi = evalPi(l.ty)
    evalLam(l, vpi)
  }

  def evalTerm(term: Term, meta: MetaStore)(implicit env: Env): Value = {
    try {
      term match {
        case tt: TypeTerm          => evalTT(tt, meta)
        case Term.App(fn, args, _) => evalApplyTerm(fn, args, meta)
        case l: Term.Lam           => evalLam(l)
        case m: Term.Match         => evalMatch(m, meta, env)
        case b: Term.Body          => evalBody(b, meta, env)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }
  }

  private def evalMatch(m: Match, meta: MetaStore, env: Env): Value = {
    val scrut = whnf(evalTerm(m.scrut, meta)(env), meta)
    evalMatchBody(m, scrut, meta, env)
  }

  private def evalMatchBody(m: Match, scrut: Value, meta: MetaStore, env: Env): Value = {
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

      val outType = evalTerm(m.motive, meta)(withScrut)

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
        evalTerm(branch.body, meta)(newEnv)
      case _ => stuckMatch
    }
  }

  def evalBody(body: Term.Body, meta: MetaStore, env: Env): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = evalTerm(l.value, meta)(curEnv)
      curEnv.putLocal(l.name, res)
    }
    evalTerm(body.res, meta)(newEnv)
  }

  private def evalDecl(decl: Decl, env: Env): Env = {
    decl match {
      case Decl.ConstDecl(isInline, name, ty, body, _) =>
        val (tyV, m) = TypeChecker.getType(ty, MetaStore.empty)(env)
        val declConst = VConst(name, Symbol, tyV)

        // Allow recursive references by pre-binding a symbolic self during body checking
        val bodyOpt = body.map(b => TypeChecker.typecheck(b, m)(env.putGlobal(name, declConst))._1)
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
        val (inductiveType, _) = TypeChecker.getType(ty, MetaStore.empty)(env)
        val inductiveHead = VConst(name, Inductive(ctors.map(c => c.name)), inductiveType)
        val env2 = env.putGlobal(name, inductiveHead)
        ctors.foldLeft(env2) { case (curEnv, c) =>
          val (ctorV, _) = TypeChecker.getType(c.ty, MetaStore.empty)(env2)

          val ctorResTpe = ctorV match {
            case v: VConst => v
            case pi: VPi =>
              val (_, nextEnv) = FreshVar.assignFreshVars(pi, MetaStore.empty)
              evalTerm(pi.out, MetaStore.empty)(nextEnv)
          }

          val ctorResTpeHead = ctorResTpe match {
            case VApp(head, _, _) => head
            case other            => other
          }

          Unify.unify(ctorResTpeHead, inductiveHead, MetaStore.empty)
          curEnv.putGlobal(c.name, VConst(c.name, ConstructorHead, ctorV))
        }
    }

  }

  def run(p: Program): Value = {
    val baseEnv = Env.empty.putGlobal("Type", VUniverse)
    val env = p.decls.foldLeft(baseEnv) { case (env, decl) => evalDecl(decl, env) }
    TypeChecker.typecheck(p.body, MetaStore.empty)(env)._1
  }
}
