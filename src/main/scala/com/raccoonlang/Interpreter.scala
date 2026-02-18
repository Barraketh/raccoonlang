package com.raccoonlang

import com.raccoonlang.CoreAst.Term.Match
import com.raccoonlang.CoreAst._
import com.raccoonlang.Util.NEL

import scala.annotation.tailrec

case class TypeErr(message: String) extends RuntimeException(message)
case class TypeErrWithSpan(message: String, span: Span) extends RuntimeException(message)

object Interpreter {
  sealed trait ConstType
  case object ConstructorHead extends ConstType
  case class Inductive(constructorNames: Vector[String]) extends ConstType
  case object Symbol extends ConstType

  sealed trait Value {
    def tpe: Value

    override def toString: String = PrettyPrinter.print(this)
  }

  case object VUniverse extends Value {
    override def tpe: Value = VUniverse
  }

  case object VAny extends Value {
    override def tpe: Value = VUniverse
  }

  /** A function type. env must be mutable in order to allow recursion - lambdas and envs must be able to point to each
    * other
    */
  case class VPi(var env: Env, binders: NEL[Binder], out: TypeTerm) extends Value {
    override def tpe: Value = VUniverse

    override def toString: String = "VPi"
  }

  case class VConst(name: String, constType: ConstType, tpe: Value) extends Value
  case class VLam(body: Term, tpe: VPi) extends Value

  case class VApp(head: Value, args: NEL[Value], tpe: Value) extends Value

  case class Var(name: String, id: Long, tpe: Value) extends Value

  case class StuckMatch(tpe: Value) extends Value

  // Environment: names map to typed values
  // Also contains a second level of indirection to handle unification - Vars can point at other Vars or
  // other values. You can only link the tops of var link chains (to make sure we can't get cycles)
  final case class Env(map: Map[String, Value], parent: Option[Env], varLinks: Map[Long, Value]) {
    def find(name: String): Option[Value] = map.get(name).orElse(parent.flatMap(_.find(name))) match {
      case Some(Var(_, id, _)) if varLinks.contains(id) => Some(getVarTop(id))
      case other                                        => other
    }

    def put(name: String, value: Value): Env = {
      if (map.contains(name))
        throw new RuntimeException(s"$name already defined")
      else if (name == "_") this
      else Env(map + (name -> value), parent, varLinks)
    }

    def addVarLink(id: Long, v: Value): Env = {
      if (varLinks.contains(id)) error(s"FreshVar $id already linked")
      v match {
        case Var(_, vid, _) if varLinks.contains(vid) => error("Cannot link to bottom of chain")
        case _                                        => Env(map, parent, varLinks + (id -> v))
      }
    }

    @tailrec
    def getVarTop(id: Long): Value = varLinks(id) match {
      case Var(_, nextId, _) if varLinks.contains(nextId) => getVarTop(nextId)
        case other => other
      }

    def newScope: Env = Env(Map.empty, Some(this), varLinks)
  }

  object Env {
    val empty: Env = Env(map = Map(), parent = None, varLinks = Map())
  }

  def error(message: String): Nothing = throw TypeErr(message)

  // Evaluate a type-position expression without enforcing it is a type yet
  private def evalTT(tt: TypeTerm, env: Env): Value = tt match {
    case Term.Ident(name, _) => env.find(name).getOrElse { error(s"$name not found") }
    case Term.TApp(fn, args, _) =>
      val vf = evalTT(fn, env)
      evalApply(vf, args, env)
    case pi: Term.Pi => VPi(env, pi.binders, pi.out)
  }

  private def evalApply(fn: Value, args: NEL[Term], argsEnv: Env): Value = {
    val vArgs = args.map(a => evalTerm(a, argsEnv))
    fn.tpe match {
      case VPi(env, binders, outTy) =>
        val envWithArgs = binders.map(_.name).zip(vArgs).foldLeft(env.newScope) { case (curEnv, (name, value)) =>
          curEnv.put(name, value)
        }
        fn match {
          case VLam(body, _) =>
            val res = evalTerm(body, envWithArgs)
            res match {
              case StuckMatch(tpe) => VApp(fn, vArgs, tpe)
              case other           => other
            }
          case _ => VApp(fn, vArgs, evalTT(outTy, envWithArgs))
        }
      case _ => error(s"Cannot apply non-fn type ${fn.tpe}")
    }
  }

  def evalTerm(term: Term, env: Env): Value = {
    try {
      term match {
        case tt: TypeTerm => evalTT(tt, env)
        case Term.App(fn, args, _) =>
          val vf = evalTerm(fn, env)
          evalApply(vf, args, env)
        case Term.Lam(ty, body, _) =>
          val vpi = VPi(env, ty.binders, ty.out)
          VLam(body, vpi)
        case m: Term.Match => evalMatch(m, env)
        case b: Term.Body  => evalBody(b, env)
      }
    } catch {
      case e: TypeErr => throw TypeErrWithSpan(e.message, term.span)
    }
  }

  private def evalMatch(m: Match, env: Env): Value = {
    val scrut = evalTerm(m.scrut, env)
    val withScrut = env.put(m.scrutName, scrut)

    lazy val stuckMatch = StuckMatch(evalTT(m.motive, withScrut))

    val (head, args) = scrut match {
      case VApp(head, args, _) => (head, args.toList)
      case c: VConst           => (c, Nil)
      case _                   => return stuckMatch
    }

    head match {
      case VConst(ctorName, `ConstructorHead`, _) =>
        val branch = m.cases.find(c => c.ctorName == ctorName).getOrElse(error(s"Match failed - $ctorName not found"))
        if (args.length != branch.argNames.length) error("Wrong number of args")
        val newEnv = args.zip(branch.argNames).foldLeft(withScrut) { case (curEnv, (argV, argName)) =>
          curEnv.put(argName, argV)
        }
        evalTerm(branch.body, newEnv)
      case _ => stuckMatch
    }
  }

  def evalBody(body: Term.Body, env: Env): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = evalTerm(l.value, curEnv)
      curEnv.put(l.name, res)
    }
    evalTerm(body.res, newEnv)
  }

  private def evalDecl(decl: Decl, env: Env): Env = {
    decl match {
      case Decl.ConstDecl(isInline, name, ty, body, _) =>
        val tyV = TypeChecker.getType(ty, env)
        val declConst = VConst(name, Symbol, tyV)

        // Allow recursive references by pre-binding a symbolic self during body checking
        val bodyOpt = body.map(b => TypeChecker.typecheck(b, env.put(name, declConst)))
        val value = (bodyOpt, isInline) match {
          case (Some(v), true) => v
          case _               => declConst
        }
        val nextEnv = env.put(name, value)

        value match {
          case VLam(_, tpe) => tpe.env = nextEnv
          case _            =>
        }

        nextEnv

      case Decl.InductiveDecl(name, ty, ctors, _) =>
        val tyV = TypeChecker.getType(ty, env)
        val env2 = env.put(name, VConst(name, Inductive(ctors.map(c => c.name)), tyV))
        ctors.foldLeft(env2) { case (curEnv, c) =>
          val ctorTy = TypeChecker.getType(c.ty, curEnv)
          curEnv.put(c.name, VConst(c.name, ConstructorHead, ctorTy))
        }
    }

  }

  def run(p: Program): Value = {
    val baseEnv = Env.empty.put("Type", VUniverse).put("Any", VAny)
    val env = p.decls.foldLeft(baseEnv) { case (env, decl) => evalDecl(decl, env) }
    TypeChecker.typecheck(p.body, env)
  }
}
