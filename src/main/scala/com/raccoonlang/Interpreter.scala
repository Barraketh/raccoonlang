package com.raccoonlang

import com.raccoonlang.CoreAst.Term._
import com.raccoonlang.CoreAst._
import com.raccoonlang.Util.NEL

object Interpreter {
  sealed trait ConstType
  case object ConstructorHead extends ConstType
  case class Inductive(constructorNames: Vector[String]) extends ConstType
  case object Symbol extends ConstType
  case object Var extends ConstType

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

  case class TypeErr(message: String) extends RuntimeException(message)

  // Environment: names map to typed values
  final case class Env(map: Map[String, Value], parent: Option[Env]) {
    def find(name: String): Option[Value] = map.get(name).orElse(parent.flatMap(_.find(name)))

    def put(name: String, value: Value): Env = {
      if (map.contains(name))
        throw new RuntimeException(s"$name already defined")
      else if (name == "_") this
      else Env(map + (name -> value), parent)
    }

    def newScope: Env = Env(Map.empty, Some(this))
  }

  object Env {
    val empty: Env = Env(map = Map(), parent = None)
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
        check(v, VUniverse)
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
            check(argV, argTy)
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

  // NbE-based definitional equality for values (types and terms)
  private def conv(v1: Value, v2: Value): Boolean = (v1, v2) match {
    case (VUniverse, VUniverse)                 => true
    case (VConst(n1, c1, _), VConst(n2, c2, _)) => n1 == n2 && c1 == c2
    case (VApp(h1, as1, _), VApp(h2, as2, _)) =>
      conv(h1, h2) && as1.length == as2.length && as1.zip(as2).forall { case (x, y) => conv(x, y) }
    case (VPi(env1, binders1, out1), VPi(env2, binders2, out2)) =>
      (binders1.length == binders2.length) && {
        val (env1res, env2res, argsMatch) = binders1.zip(binders2).foldWhile[(Env, Env, Boolean)]((env1, env2, true)) {
          case ((env1, env2, _), (b1, b2)) =>
            val b1V = evalType(b1.ty, env1)
            val b2V = evalType(b2.ty, env2)
            if (!conv(b1V, b2V)) ((env1, env2, false), true)
            else {
              val fresh = VConst(freshName(), Var, b1V)
              ((env1.put(b1.name, fresh), env2.put(b2.name, fresh), true), false)
            }
        }
        argsMatch && conv(evalType(out1, env1res), evalType(out2, env2res))
      }
    case (x, y) => x == y
  }

  // Fresh symbol name helper
  private var gensymId: Long = 0L
  private def freshName(): String = {
    gensymId += 1
    s"$$x_$gensymId"
  }

  // Check that a value has a given type (by conversion)
  private def check(value: Value, tyVal: Value): Unit = {
    val got = value.tpe
    if (!conv(got, tyVal))
      error(s"Type mismatch: expected $tyVal, found $got for $value")
  }

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
        check(branchRes, expectTy)
        branchRes
      case _ =>
        // Scrutinee not a constructor: keep match neutral, but type-check all branches
        val withScrut = env.put(m.scrutName, scrut)

        // For each branch, synthesize a scrutinee of that constructor with fresh symbolic args
        m.cases.foreach { br =>
          val ctorVal = env.find(br.ctorName).getOrElse(error(s"Constructor ${br.ctorName} not found"))
          ctorVal match {
            case VConst(_, ConstructorHead, ctorTy) =>
              val branchEnv = ctorTy match {
                case pi: VPi =>
                  if (br.argNames.length != pi.binders.length) error("Wrong number of args")
                  val (freshVars, _) = assignFreshVars(pi)
                  br.argNames.zip(freshVars).foldLeft(env) { case (curEnv, (argName, argVal)) =>
                    curEnv.put(argName, argVal)
                  }
                case _ => env
              }

              val branchRes = evalTerm(br.body, branchEnv)
              val expectTy = evalType(m.motive, env)
              check(branchRes, expectTy)

            case other => error(s"${br.ctorName} is not a constructor: $other")
          }
        }

        VMatch(m, withScrut, evalType(m.motive, withScrut))
    }
  }

  private def assignFreshVars(vpi: VPi): (Vector[Value], Env) = vpi.binders.foldLeft(Vector.empty[Value] -> vpi.env) {
    case ((curValues, curEnv), binder) =>
      val tyV = evalType(binder.ty, curEnv)
      val fresh = VConst(freshName(), Var, tyV)
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

      check(bodyV, resType)
      VLam(body, vpi)
    case m: Term.Match => evalMatch(m, env)
    case tt: TypeTerm  => evalTT(tt, env)
  }

  private def evalBody(body: Body, env: Env): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = evalTerm(l.value, curEnv)
      l.ty.foreach { tyTerm =>
        val tyV = evalType(tyTerm, curEnv)
        check(res, tyV)
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
