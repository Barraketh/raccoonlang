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

  case class VLam(body: Term, tpe: VPi, id: Option[LamId]) extends Value {
    override lazy val synDeps: BitSet =
      tpe.synDeps.union(FreeNames.getDeps(body, tpe.env, tpe.binders.map(_.name).toList.toSet))
  }

  // Environment: tracks lexical scope
  final case class Env(map: Map[String, Value], parent: Option[Env]) {
    def find(name: String): Option[Value] = map.get(name).orElse(parent.flatMap(_.find(name)))

    def put(name: String, value: Value): Env = {
      if (map.contains(name)) throw AlreadyDefined(name)
      else if (name == "_") this
      else Env(map + (name -> value), parent)
    }
    def newScope: Env = Env(Map.empty, Some(this))
  }

  object Env {
    val empty: Env = Env(map = Map(), parent = None)
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
      case _ => v0
    }
  }

  private def getEnvWithArgs(fnTpe: VPi, args: NEL[Value]): Env = {
    if (fnTpe.binders.length != args.length) throw ArityMismatch(fnTpe.binders.length, args.length)

    fnTpe.binders.map(_.name).zip(args).foldLeft(fnTpe.env.newScope) { case (curEnv, (name, value)) =>
      curEnv.put(name, value)
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
        fn match {
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

  def evalTerm(term: Term, meta: MetaStore)(implicit env: Env): Value = {
    try {
      term match {
        case tt: TypeTerm          => evalTT(tt, meta)
        case Term.App(fn, args, _) => evalApplyTerm(fn, args, meta)
        case Term.Lam(ty, body, _) =>
          val vpi = evalPi(ty)
          VLam(body, vpi, None)
        case m: Term.Match => evalMatch(m, meta)
        case b: Term.Body  => evalBody(b, meta)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }
  }

  private def evalMatch(m: Match, meta: MetaStore)(implicit env: Env): Value = {
    val scrut = evalTerm(m.scrut, meta)
    val withScrut = env.put(m.scrutName, scrut)

    def stuckMatch: Value = ???

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
        val newEnv = args.zip(branch.argNames).foldLeft(withScrut) { case (curEnv, (argV, argName)) =>
          curEnv.put(argName, argV)
        }
        evalTerm(branch.body, meta)(newEnv)
      case _ => stuckMatch
    }
  }

  def evalBody(body: Term.Body, meta: MetaStore)(implicit env: Env): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = evalTerm(l.value, meta)(curEnv)
      curEnv.put(l.name, res)
    }
    evalTerm(body.res, meta)(newEnv)
  }

  private def evalDecl(decl: Decl, env: Env): Env = {
    decl match {
      case Decl.ConstDecl(isInline, name, ty, body, _) =>
        val (tyV, m) = TypeChecker.getType(ty, MetaStore.empty)(env)
        val declConst = VConst(name, Symbol, tyV)

        // Allow recursive references by pre-binding a symbolic self during body checking
        val bodyOpt = body.map(b => TypeChecker.typecheck(b, m)(env.put(name, declConst))._1)
        val value: Value = (bodyOpt, isInline) match {
          case (Some(lam: VLam), true) => VLam(lam.body, lam.tpe, Some(LamId.Const(name)))
          case (Some(v), true)         => v
          case _                       => declConst
        }
        val nextEnv = env.put(name, value)

        value match {
          case VLam(_, tpe, _) => tpe.env = nextEnv
          case _               =>
        }

        nextEnv

      case Decl.InductiveDecl(name, ty, ctors, _) =>
        val (inductiveType, _) = TypeChecker.getType(ty, MetaStore.empty)(env)
        val env2 = env.put(name, VConst(name, Inductive(ctors.map(c => c.name)), inductiveType))
        ctors.foldLeft(env2) { case (curEnv, c) =>
          val (ctorTy, _) = TypeChecker.getType(c.ty, MetaStore.empty)(env2)
          Unify.unify(ctorTy.tpe, inductiveType, MetaStore.empty)
          curEnv.put(c.name, VConst(c.name, ConstructorHead, ctorTy))
        }
    }

  }

  def run(p: Program): Value = {
    val baseEnv = Env.empty.put("Type", VUniverse)
    val env = p.decls.foldLeft(baseEnv) { case (env, decl) => evalDecl(decl, env) }
    TypeChecker.typecheck(p.body, MetaStore.empty)(env)._1
  }
}
