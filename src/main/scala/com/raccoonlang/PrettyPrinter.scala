package com.raccoonlang

import com.raccoonlang.CoreAst.Term.Ident
import com.raccoonlang.Value.LevelTpe

object PrettyPrinter {

  private def printTypePattern(tp: CoreAst.TypePattern): String = {
    import com.raccoonlang.CoreAst.Term

    def pt(t: CoreAst.TypePattern): String = t match {
      case Term.Ident(name, _)          => name
      case Term.TSelect(base, field, _) => s"${ptAtom(base)}[$field]"
      case Term.TApp(fn, args, _) =>
        val headStr = ptAtom(fn)
        val argsStr = args.toList.map(ptAtom).mkString(", ")
        s"$headStr($argsStr)"
      case Term.PatternApp(fn, args, _) =>
        val headStr = ptAtom(fn)
        val argsStr = args.toList.map(ptAtom).mkString(", ")
        s"$headStr($argsStr)"
      case Term.Pi(binders, out, _) =>
        val bindersStr = binders.toList
          .map { b =>
            if (b.name == "_") pt(b.ty) else s"(${b.name}: ${pt(b.ty)})"
          }
          .mkString(" -> ")
        s"$bindersStr -> ${pt(out)}"
      case Term.Capture(name, _) => s"$$$name"
    }

    def ptAtom(t: CoreAst.TypePattern): String = t match {
      case Term.Ident(_, _)         => pt(t)
      case Term.TSelect(_, _, _)    => pt(t)
      case Term.TApp(_, _, _)       => pt(t)
      case Term.PatternApp(_, _, _) => pt(t)
      case Term.Pi(_, _, _)         => s"(${pt(t)})"
      case Term.Capture(_, _)       => pt(t)
    }

    pt(tp)
  }

  private def printTypeTerm(tt: CoreAst.TypeTerm): String = printTypePattern(tt)

  private def isAtomic(v: Value): Boolean = v match {
    case _: Value.VSort  => true
    case _: Value.VConst => true
    case _: Value.Var    => true
    case _               => false
  }

  private def printApp(head: Value, args: Seq[Value]): String = {
    val headStr = head match {
      case _: Value.VApp | _: Value.VConst | _: Value.Var | _: Value.VSort => print(head)
      case _                                                               => s"(${print(head)})"
    }
    val argsStr = args.toList.map(print).mkString(", ")
    s"$headStr($argsStr)"
  }

  def printBinder(b: CoreAst.Binder): String = s"(${b.name}: ${printTypePattern(b.ty)})"

  private def printBinders(binders: Util.NEL[CoreAst.Binder]): String =
    binders.toList.map(printBinder).mkString(" ")

  // ---- Core term pretty printing (for neutral match bodies/scrutinees) ----
  private def printLet(l: CoreAst.Let): String = {
    val tyStr = l.ty.map(t => s": ${printTypePattern(t)}").getOrElse("")
    s"let ${l.name}$tyStr := ${printTerm(l.value)}"
  }

  private def printBody(b: CoreAst.Term.Body): String = {
    if (b.lets.isEmpty) printTerm(b.res)
    else {
      val letsStr = b.lets.map(printLet).mkString("\n")
      s"{ $letsStr \n ${printTerm(b.res)} }"
    }
  }

  private def printTermAtom(t: CoreAst.Ast): String = t match {
    case CoreAst.Term.Ident(_, _)            => printTerm(t)
    case CoreAst.Term.App(_, _, _)           => printTerm(t)
    case CoreAst.Term.TApp(_, _, _)          => printTerm(t)
    case ts: CoreAst.Term.TSelect            => printTypeTerm(ts)
    case CoreAst.Term.Select(base, field, _) => s"${printTermAtom(base)}[$field]"
    case p: CoreAst.Term.PatternApp          => printTypePattern(p)
    case CoreAst.Term.Lam(_, _, _, _, _, _)  => s"(${printTerm(t)})"
    case CoreAst.Term.Match(_, _, _, _, _)   => s"(${printTerm(t)})"
    case CoreAst.Term.Body(_, _, _)          => s"(${printTerm(t)})"
    case CoreAst.Term.Pi(_, _, _)            => s"(${printTerm(t)})"
    case CoreAst.Term.Capture(name, _)       => s"$$$name"
  }

  def printTerm(t: CoreAst.Ast): String = t match {
    case tt: CoreAst.TypeTerm                => printTypeTerm(tt)
    case p: CoreAst.Term.PatternApp          => printTypePattern(p)
    case CoreAst.Term.Select(base, field, _) => s"${printTermAtom(base)}[$field]"
    case CoreAst.Term.App(fn, args, _) =>
      val head = printTermAtom(fn)
      val as = args.toList.map(printTermAtom).mkString(", ")
      s"$head($as)"
    case CoreAst.Term.Lam(ty, _, body, _, _, _) =>
      s"fun ${printBinders(ty.binders)}: ${printTypeTerm(ty.out)} => ${printTerm(body)}"
    case m @ CoreAst.Term.Match(_, _, _, _, _) => printMatch(m)
    case b: CoreAst.Term.Body                  => printBody(b)
    case CoreAst.Term.Capture(name, _)         => s"$$$name"
  }

  private def printCase(c: CoreAst.Case): String = {
    val args = if (c.argNames.isEmpty) "" else s" ${c.argNames.mkString(" ")}"
    s"| ${c.ctorName}$args => ${printTerm(c.body)}"
  }

  private def printMatch(m: CoreAst.Term.Match): String = {
    val scrutStr = printTermAtom(m.scrut)
    val motiveStr = printTypeTerm(m.motive)
    val casesStr = m.cases.map(printCase).mkString(" ")
    s"match $scrutStr as ${m.scrutName} returning $motiveStr with $casesStr"
  }

  def print(value: Value): String = value match {
    case Value.VSort(lvl)      => s"Type $lvl"
    case Value.PropTpe         => "Prop"
    case Value.KernelObject    => "KernelObject"
    case Value.Level(atoms, c) => s"Level($atoms, $c)"
    case Value.VPi(_, binders, _, out, _, _, _) =>
      val outTerm = out match {
        case Some(value) => value
        case None        => Ident("Any", Span(0, 0))
      }
      printTypeTerm(CoreAst.Term.Pi(binders, outTerm, Span(0, 0)))
    case Value.VConst(name, _, _)                => name
    case v: Value.AppliedValue                   => printApp(v.head, v.args)
    case Value.ConstructorHead(name, _, _, _, _) => name
    case Value.VCtor(head, fields, _) =>
      val headStr = print(head)
      if (fields.isEmpty) headStr
      else s"$headStr(${fields.map(print).mkString(", ")})"
    case v: Value.VLam          => s"func#${v.id}"
    case Value.Var(name, id, _) => s"$name#$id"
    case s: Value.VBlockedThunk => s"match#${s.id}"
    case Value.NormalizerType   => "Normalizer"
    case n: Value.Normalizer    => s"Normalizer ${n.name}"
    case LevelTpe               => s"Level"
  }

}
