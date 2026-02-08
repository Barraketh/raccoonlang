package com.raccoonlang

import com.raccoonlang.CoreAst.Term._
import com.raccoonlang.CoreAst._
import com.raccoonlang.Util.NEL

import scala.annotation.tailrec

object Interpreter {
  sealed trait ConstType
  case object ConstructorHead extends ConstType
  case class Inductive(constructorNames: Vector[String]) extends ConstType
  case object Symbol extends ConstType

  // Runtime values (normal forms) used for both terms and types, all typed
  sealed trait Value { def tpe: VType }
  sealed trait VType extends Value

  // Universe of types: the value denoting "Type" (Type : Type for now)
  case object VUniverse extends VType { override def tpe: VType = this }

  /** A function type. env must be mutable in order to allow recursion - lambdas and envs must be able to point to each
    * other
    */
  case class VPi(var env: Env, binders: NEL[Binder], out: TypeTerm) extends VType {
    override def tpe: VType = VUniverse

    override def toString: String = "VPi"
  }

  // Term-level constants and constructors (also used for type-level identifiers)
  case class VConst(name: String, constType: ConstType, tpe: VType) extends VType
  // Application (term or type level)
  case class VApp(head: Value, args: NEL[Value], tpe: VType) extends VType
  // Lambda value (term-level function)
  case class VLam(body: Body, tpe: VPi) extends Value
  // Neutral match (when scrutinee is not a constructor)
  case class VMatch(m: Match, env: Env, tpe: VType) extends Value

  case class Var(name: String, id: Long, tpe: VType) extends VType

  case class TypeErr(message: String) extends RuntimeException(message)

  // Environment: names map to typed values
  // Also contains a second level of indirection to handle unification - Vars can point at other Vars or
  // other values. You can only link the tops of var link chains (to make sure we can't get cycles)
  final case class Env(map: Map[String, Value], parent: Option[Env], varLinks: Map[Long, Value]) {
    def find(name: String): Option[Value] = map.get(name).orElse(parent.flatMap(_.find(name))) match {
      case Some(Var(_, id, _)) if varLinks.contains(id) => Some(getVarTop(id))
      case other                                             => other
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
        case _                                             => Env(map, parent, varLinks + (id -> v))
      }
    }

    @tailrec
    def getVarTop(id: Long): Value = varLinks(id) match {
      case Var(_, nextId, _) if varLinks.contains(nextId) => getVarTop(nextId)
      case other                                               => other
    }

    def newScope: Env = Env(Map.empty, Some(this), varLinks)
  }

  object Env {
    val empty: Env = Env(map = Map(), parent = None, varLinks = Map())
  }

  private def error(message: String): Nothing = throw TypeErr(message)

  // Evaluate a type-position expression without enforcing it is a type yet
  private def evalTT(tt: TypeTerm, env: Env): Value = tt match {
    case Term.Ident("Type") => VUniverse
    case Term.Ident(name)   => env.find(name).getOrElse { error(s"$name not found") }
    case Term.TApp(fn, args) =>
      val vf = evalTT(fn, env)
      evalApply(vf, args, env)
    case pi: Term.Pi => VPi(env, pi.binders, pi.out)

  }

  // Evaluate a type term to a type value (NbE domain)
  private def evalType(ty: TypeTerm, env: Env): VType = {
    val res = evalTT(ty, env)
    res match {
      case v: VType =>
        check(v, VUniverse, env)
        v
      case _ => error(s"$ty is not a type")
    }
  }

  private def evalApply(fn: Value, args: NEL[Term], argsEnv: Env): Value = {
    fn.tpe match {
      case VPi(funcEnv, binders, out) =>
        if (args.length > binders.length) error("Too many args to fn")
        val (argBinders, rest) = binders.splitAt(args.length)
        val (nextFuncEnv, argValues) = args.zip(argBinders).foldLeft[(Env, Vector[Value])](funcEnv -> Vector.empty) {
          case ((curFuncEnv, curValues), (nextArg, nextBinder)) =>
            val argV = evalTerm(nextArg, argsEnv)
            val argTy = evalType(nextBinder.ty, curFuncEnv)
            check(argV, argTy, curFuncEnv)
            curFuncEnv.put(nextBinder.name, argV) -> (curValues :+ argV)
        }

        val resTy = rest match {
          case Some(remainingBinders) => VPi(nextFuncEnv, remainingBinders, out)
          case None                   => evalType(out, nextFuncEnv)
        }

        (fn, resTy) match {
          case (lam: VLam, pi: VPi) => VLam(lam.body, pi)
          case (lam: VLam, _) =>
            val newEnv = argValues.zip(binders.toList).foldLeft(lam.tpe.env.newScope) { case (curEnv, (argV, binder)) =>
              curEnv.put(binder.name, argV)
            }
            evalBody(lam.body, newEnv)
          case (VApp(h, args, _), _) => VApp(h, args :++ argValues, resTy)
          case (other, _)            => VApp(other, NEL.mk(argValues), resTy)
        }

      case notFn => error(s"Application to non-function type: $notFn")
    }
  }

  // Fresh symbol name helper
  private var gensymId: Long = 0L
  private def freshVar(name: String, tpe: VType) = {
    gensymId += 1
    Var(name, gensymId, tpe)
  }


  private def occurs(id: Long, v: Value, env: Env): Boolean = v match {
    case Var(_, vid, _) if vid == id => true
    case Var(_, vid, _) if env.varLinks.contains(vid) => occurs(id, env.getVarTop(vid), env)
    case VPi(piEnv, binders, out) =>
      // Check binder types first
      val inBinders = binders.toList.exists { b =>
        val tv = evalType(b.ty, piEnv)
        occurs(id, tv, env)
      }
      if (inBinders) true
      else {
        // Check codomain under fresh assignments for binders
        val (_, extEnv) = assignFreshVars(VPi(piEnv, binders, out))
        val outV = evalType(out, extEnv)
        occurs(id, outV, env)
      }
    case VApp(h, args, _) => occurs(id, h, env) || args.toList.exists(a => occurs(id, a, env))
    case _ => false
  }

  private def unify(v1: Value, v2: Value, env: Env): Env = {
    (v1, v2) match {
      case (VUniverse, VUniverse)                                         => env
      case (VConst(n1, c1, _), VConst(n2, c2, _)) if n1 == n2 && c1 == c2 => env
      case (p1 @ VPi(env1, bs1, out1), p2 @ VPi(env2, bs2, out2)) if bs1.length == bs2.length =>
        // Extensional unification for Pi types: unify binder types and codomain under shared fresh vars
        val (envAfterBinders, extEnv1, extEnv2) = bs1.toList.zip(bs2.toList).foldLeft((env, env1.newScope, env2.newScope)) {
          case ((curEnv, curEnv1, curEnv2), (b1, b2)) =>
            val t1 = evalType(b1.ty, curEnv1)
            val t2 = evalType(b2.ty, curEnv2)
            val nextEnv = unify(t1, t2, curEnv)
            val x = freshVar(b1.name, t1)
            (nextEnv, curEnv1.put(b1.name, x), curEnv2.put(b2.name, x))
        }
        val outT1 = evalType(out1, extEnv1)
        val outT2 = evalType(out2, extEnv2)
        unify(outT1, outT2, envAfterBinders)
      case (VApp(h1, args1, _), VApp(h2, args2, _)) if args1.length == args2.length =>
        val startCtx = unify(h1, h2, env)
        args1.zip(args2).foldLeft(startCtx) { case (newCtx, (arg1, arg2)) => unify(arg1, arg2, newCtx) }

      // Unify FreshVars through ctx. Basic idea: FreshVars can point at things through context
      // unify creates a ctx of pointers. We only create pointers from the top of the chain

      case (Var(_, id1, _), Var(_, id2, _)) if id1 == id2 => env

      // If we have FreshVars, resolve the tops of the chain
      case (Var(_, id, _), _) if env.varLinks.contains(id) => unify(env.getVarTop(id), v2, env)
      case (_, Var(_, id, _)) if env.varLinks.contains(id) => unify(v1, env.getVarTop(id), env)

      // Link two distinct, unlinked Vars: smaller id points to larger id
      case (v1 @ Var(_, id1, ty1), v2 @ Var(_, id2, ty2)) =>
        val (smallId, largeVar, smallTy, largeTy) =
          if (id1 < id2) (id1, v2: Value, ty1, ty2) else (id2, v1: Value, ty2, ty1)
        val env1 = unify(smallTy, largeTy, env)
        env1.addVarLink(smallId, largeVar)

      // Link unlinked Var (left) to a non-Var value
      case (v @ Var(_, id, ty), other) =>
        if (occurs(id, other, env)) error(s"Occurs check failed: $id in $other")
        val env1 = unify(ty, other.tpe, env)
        env1.addVarLink(id, other)

      // Symmetric: link unlinked Var (right) to non-Var value
      case (other, v @ Var(_, id, ty)) =>
        if (occurs(id, other, env)) error(s"Occurs check failed: $id in $other")
        val env1 = unify(ty, other.tpe, env)
        env1.addVarLink(id, other)

      case _ => error(s"Failed to unify $v1 and $v2")
    }
  }

  // Check that a value has a given type (by conversion)
  private def check(value: Value, tyVal: VType, env: Env): Unit = { unify(value.tpe, tyVal, env); () }

  private def evalMatch(m: Match, env: Env): Value = {
    val scrut = evalTerm(m.scrut, env)
    val (head, args) = scrut match {
      case VApp(head, args, _) => (head, args.toList)
      case c: VConst           => (c, Nil)
      case _                   => return VMatch(m, env, evalType(m.motive, env))
    }
    head match {
      case VConst(ctorName, `ConstructorHead`, _) =>
        val branch = m.cases.find(c => c.ctorName == ctorName).getOrElse(error(s"Match failed - $ctorName not found"))
        if (args.length != branch.argNames.length) error("Wrong number of args")
        val withScrut = env.put(m.scrutName, scrut)
        val newEnv = args.zip(branch.argNames).foldLeft(withScrut) { case (curEnv, (argV, argName)) =>
          curEnv.put(argName, argV)
        }
        val branchRes = evalTerm(branch.body, newEnv)
        val expectTy = evalType(m.motive, withScrut)
        check(branchRes, expectTy, withScrut)
        branchRes
      case _ =>
        // Scrutinee not a constructor: keep match neutral, but type-check all branches
        val withScrut = env.put(m.scrutName, scrut)

        // For each branch, synthesize a scrutinee of that constructor with fresh symbolic args
        m.cases.foreach { br =>
          val ctorVal = env.find(br.ctorName).getOrElse(error(s"Constructor ${br.ctorName} not found"))
          ctorVal match {
            case VConst(_, ConstructorHead, ctorTy) =>
              val (freshArgs, ctorEnv) = ctorTy match {
                case pi: VPi =>
                  if (br.argNames.length != pi.binders.length) error("Wrong number of args")
                  assignFreshVars(pi)
                case _ =>
                  if (br.argNames.nonEmpty) error("Wrong number of args")
                  (Vector.empty[Value], env)
              }

              val ctorResTy: VType = ctorTy match {
                case VPi(_, _, out) => evalType(out, ctorEnv)
                case otherTy: VType => otherTy
              }

              // Refine env by unifying scrutinee type with constructor result type
              val refinedEnv = unify(scrut.tpe, ctorResTy, env)

              val branchBase = refinedEnv.put(m.scrutName, scrut)
              val branchEnv = br.argNames.zip(freshArgs).foldLeft(branchBase) {
                case (curEnv, (argName, argVal)) => curEnv.put(argName, argVal)
              }

              val branchRes = evalTerm(br.body, branchEnv)
              val expectTy = evalType(m.motive, branchBase)
              check(branchRes, expectTy, branchBase)

            case other => error(s"${br.ctorName} is not a constructor: $other")
          }
        }

        VMatch(m, withScrut, evalType(m.motive, withScrut))
    }
  }

  private def assignFreshVars(vpi: VPi): (Vector[Value], Env) = vpi.binders.foldLeft(Vector.empty[Value] -> vpi.env) {
    case ((curValues, curEnv), binder) =>
      val tyV = evalType(binder.ty, curEnv)
      val fresh = freshVar(binder.name, tyV)
      (curValues :+ fresh, curEnv.put(binder.name, fresh))
  }

  private def evalTerm(term: Term, env: Env): Value = term match {
    case Term.Ident(name) => env.find(name).getOrElse { error(s"$name not found") }
    case Term.App(fn, args) =>
      val vf = evalTerm(fn, env)
      evalApply(vf, args, env)
    case Term.Lam(ty, body) =>
      val vpi = VPi(env, ty.binders, ty.out)
      val (_, nextEnv) = assignFreshVars(vpi)

      val bodyV = evalBody(body, nextEnv)
      val resType = evalType(vpi.out, nextEnv)

      check(bodyV, resType, nextEnv)
      VLam(body, vpi)
    case m: Term.Match => evalMatch(m, env)
    case tt: TypeTerm  => evalTT(tt, env)
  }

  private def evalBody(body: Body, env: Env): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = evalTerm(l.value, curEnv)
      l.ty.foreach { tyTerm =>
        val tyV = evalType(tyTerm, curEnv)
        check(res, tyV, curEnv)
      }
      curEnv.put(l.name, res)
    }
    evalTerm(body.res, newEnv)
  }

  private def evalDecl(decl: Decl, env: Env): Env = {
    decl match {
      case Decl.ConstDecl(isInline, name, ty, body) =>
        val tyV = evalType(ty, env)
        // Allow recursive references by pre-binding a symbolic self during body checking
        val envWithSelf = env.put(name, VConst(name, Symbol, tyV))
        val checkedBodyOpt = body.map(b => evalTerm(b, envWithSelf))
        val value = (checkedBodyOpt, isInline) match {
          case (Some(v), true) => v
          case _               => VConst(name, Symbol, tyV)
        }
        val nextEnv = env.put(name, value)

        value match {
          case VLam(_, tpe) => tpe.env = nextEnv
          case _            =>
        }

        nextEnv

      case Decl.InductiveDecl(name, ty, ctors) =>
        val tyV = evalType(ty, env)
        val env2 = env.put(name, VConst(name, Inductive(ctors.map(c => c.name)), tyV))
        ctors.foldLeft(env2) { case (curEnv, c) =>
          val ctorTy = evalType(c.ty, curEnv)
          curEnv.put(c.name, VConst(c.name, ConstructorHead, ctorTy))
        }
    }

  }

  def run(p: Program): Value = {
    val env = p.decls.foldLeft(Env.empty) { case (env, decl) => evalDecl(decl, env) }
    evalBody(p.body, env)
  }
}
