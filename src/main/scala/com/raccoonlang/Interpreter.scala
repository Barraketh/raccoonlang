package com.raccoonlang

import com.raccoonlang.CoreAst.Term._
import com.raccoonlang.CoreAst._

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

  // Dependent function type: Pi (x : binderTy) -> body(x)
  case class VPi(binderName: String, binderTy: Value, body: Value => Value) extends VType {
    override def tpe: VType = VUniverse
  }

  // Term-level constants and constructors (also used for type-level identifiers)
  case class VConst(name: String, constType: ConstType, tpe: VType) extends VType
  // Application (term or type level)
  case class VApp(head: Value, args: Vector[Value], tpe: VType) extends VType
  // Lambda value (term-level function)
  case class VLam(name: Option[String], argName: String, body: Body, env: Env, tpe: VType) extends Value
  // Neutral match (when scrutinee is not a constructor)
  case class VMatch(m: Match, env: Env, tpe: VType) extends Value

  // Environment: names map to typed values
  final case class Env(map: Map[String, Value], parent: Option[Env]) {
    def find(name: String): Option[Value] = map.get(name).orElse(parent.flatMap(_.find(name)))

    def put(name: String, value: Value): Env = {
      if (map.contains(name))
        throw new RuntimeException(s"$name already defined")
      else if (name == "_") this
      else Env(map + (name -> value), parent)
    }

    def maybePut(name: Option[String], value: Value): Env = name.map(n => put(n, value)).getOrElse(this)

    def newScope: Env = Env(Map.empty, Some(this))
  }

  object Env {
    val empty: Env = Env(map = Map(), parent = None)
  }

  private def error(message: String) = throw new RuntimeException(message)

  // Evaluate a type term to a type value (NbE domain)
  private def evalType(ty: TypeTerm, env: Env): Value = ty match {
    case Term.Ident("Type")        => VUniverse
    case Term.Ident(name)           => env.find(name).getOrElse { throw new RuntimeException(s"$name not found") }
    case Term.TypeVar(name)         => env.find(name).getOrElse { throw new RuntimeException(s"$name not found") }
    case Term.TApp(fn, arg)         =>
      val vf = evalType(fn, env)
      val va = evalType(arg, env)
      applyValue(vf, va, env)
    case Term.Pi(binder, body)      =>
      val bTy = evalType(binder.ty, env)
      VPi(binder.name, bTy, (x: Value) => evalType(body, env.newScope.put(binder.name, x)))
  }

  // Apply a value (for both term and type level), preserving types
  private def applyValue(fn: Value, arg: Value, callEnv: Env): Value = fn match {
    case lam: VLam =>
      val newEnv = lam.env.newScope.maybePut(lam.name, lam).put(lam.argName, arg)
      evalBody(lam.body, newEnv)
    case other =>
      other.tpe match {
        case VPi(bName, bTy, bBody) =>
          val resTy = bBody(arg).asInstanceOf[VType]
          other match {
            case VApp(h, args, _) => VApp(h, args.appended(arg), resTy)
            case _                 => VApp(other, Vector(arg), resTy)
          }
        case notFn => error(s"Application to non-function type: $notFn")
      }
  }

  // NbE-based definitional equality for values (types and terms)
  private def conv(v1: Value, v2: Value): Boolean = (v1, v2) match {
    case (VUniverse, VUniverse) => true
    case (VConst(n1, c1, _), VConst(n2, c2, _)) => n1 == n2 && c1 == c2
    case (VApp(h1, as1, _), VApp(h2, as2, _))   => conv(h1, h2) && as1.length == as2.length && as1.zip(as2).forall { case (x, y) => conv(x, y) }
    case (VPi(n1, a1, b1), VPi(n2, a2, b2)) =>
      conv(a1, a2) && {
        val fresh = VConst(freshName(n1), Symbol, a1.asInstanceOf[VType])
        val t1 = b1(fresh)
        val t2 = b2(fresh)
        conv(t1, t2)
      }
    case (x, y) => x == y
  }

  // Fresh symbol name helper
  private var gensymId: Long = 0L
  private def freshName(prefix: String): String = {
    gensymId += 1
    val p = if (prefix == "_" || prefix.isEmpty) "x" else prefix
    s"$$${p}_$gensymId"
  }

  // Synthesize the type of a value (trivial with typed values)
  private def synth(value: Value, env: Env): Value = value.tpe

  // Check that a value has a given type (by conversion)
  private def check(value: Value, tyVal: Value, env: Env): Unit = {
    val got = value.tpe
    if (!conv(got, tyVal)) error(s"Type mismatch: expected $tyVal, found $got for $value")
  }

  private def evalMatch(m: Match, env: Env): Value = {
    val scrut = evalTerm(m.scrut, env)
    val (head, args) = scrut match {
      case VApp(head, args, _) => (head, args)
      case c: VConst            => (c, Vector.empty)
      case _                    => return VMatch(m, env, evalType(m.motive, env).asInstanceOf[VType])
    }
    head match {
      case VConst(ctorName, `ConstructorHead`, _) =>
        val branch = m.cases.find(c => c.ctorName == ctorName).getOrElse(error(s"Match failed - $ctorName not found"))
        if (args.length != branch.argNames.length) error("Wrong number of args")
        val withScrut = env.put(m.scrutName, scrut)
        val newEnv = args.zip(branch.argNames).foldLeft(withScrut) {
          case (curEnv, (argV, argName)) => curEnv.put(argName, argV)
        }
        evalTerm(branch.body, newEnv)
      case _ =>
        // Keep match neutral for typing purposes (motive gives its type)
        val withScrut = env.put(m.scrutName, scrut)
        VMatch(m, withScrut, evalType(m.motive, withScrut).asInstanceOf[VType])
    }
  }

  private def evalTerm(term: Term, env: Env): Value = term match {
    case Term.Ident(name) => env.find(name).getOrElse { throw new RuntimeException(s"$name not found") }
    case Term.App(fn, arg) =>
      val vf = evalTerm(fn, env)
      val varg = evalTerm(arg, env)
      applyValue(vf, varg, env)
    case Term.Lam(binder, body) =>
      val domTy = evalType(binder.ty, env)
      // lazy self to allow recursion in body typing
      lazy val lam: VLam = VLam(None, binder.name, body, env, lamType)
      lazy val lamType: VType = VPi(
        binder.name,
        domTy,
        (x: Value) => {
          val env2 = env.newScope.maybePut(lam.name, lam).put(binder.name, x)
          val bodyV = evalBody(body, env2)
          bodyV.tpe
        }
      )
      lam
    case m: Term.Match          => evalMatch(m, env)

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
        val tyV = evalType(ty, env).asInstanceOf[VType]
        val value =
          if (isInline)
            body
              .map(b => {
                val res = evalBody(b, env)
                check(res, tyV, env)
                res match {
                  case v: VLam => v.copy(name = Some(name))
                  case other   => other
                }
              })
              .getOrElse(VConst(name, Symbol, tyV))
          else VConst(name, Symbol, tyV)

        env.put(name, value)

      case Decl.InductiveDecl(name, ty, ctors) =>
        val tyV = evalType(ty, env).asInstanceOf[VType]
        val env2 = env.put(name, VConst(name, Inductive(ctors.map(c => c.name)), tyV))
        ctors.foldLeft(env2) { case (curEnv, c) =>
          val ctorTy = evalType(c.ty, curEnv).asInstanceOf[VType]
          curEnv.put(c.name, VConst(c.name, ConstructorHead, ctorTy))
        }
    }

  }

  def run(p: Program): Value = {
    val env = p.decls.foldLeft(Env.empty) { case (env, decl) => evalDecl(decl, env) }
    evalBody(p.body, env)
  }
}
