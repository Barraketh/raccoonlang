package com.raccoonlang

object PrettyPrinter {

  private def printTypeTerm(tt: CoreAst.TypeTerm): String = {
    import com.raccoonlang.CoreAst.Term

    def pt(t: CoreAst.TypeTerm): String = t match {
      case Term.Ident(name, _) => name
      case Term.TApp(fn, args, _) =>
        val headStr = ptAtom(fn)
        val argsStr = args.toList.map(ptAtom).mkString(" ")
        s"$headStr $argsStr"
      case Term.Pi(binders, out, _) =>
        val bindersStr = binders.toList
          .map { b =>
            if (b.name == "_") pt(b.ty) else s"(${b.name}: ${pt(b.ty)})"
          }
          .mkString(" -> ")
        s"$bindersStr -> ${pt(out)}"
    }

    def ptAtom(t: CoreAst.TypeTerm): String = t match {
      case Term.Ident(_, _)   => pt(t)
      case Term.TApp(_, _, _) => pt(t)
      case Term.Pi(_, _, _)   => s"(${pt(t)})"
    }

    pt(tt)
  }

  private def isAtomic(v: Interpreter.Value): Boolean = v match {
    case Interpreter.VUniverse => true
    case _: Interpreter.VConst => true
    case _: Interpreter.Meta   => true
    case _                     => false
  }

  private def printApp(head: Interpreter.Value, args: Util.NEL[Interpreter.Value]): String = {
    val headStr = head match {
      case _: Interpreter.VApp | _: Interpreter.VConst | _: Interpreter.Meta | Interpreter.VUniverse => print(head)
      case _ => s"(${print(head)})"
    }
    val argsStr = args.toList.map { a => if (isAtomic(a)) print(a) else s"(${print(a)})" }.mkString(" ")
    s"$headStr $argsStr"
  }

  private def printBinder(b: CoreAst.Binder): String = s"(${b.name}: ${printTypeTerm(b.ty)})"

  private def printBinders(binders: Util.NEL[CoreAst.Binder]): String =
    binders.toList.map(printBinder).mkString(" ")

  // ---- Core term pretty printing (for neutral match bodies/scrutinees) ----
  private def printLet(l: CoreAst.Let): String = {
    val tyStr = l.ty.map(t => s": ${printTypeTerm(t)}").getOrElse("")
    s"let ${l.name}$tyStr := ${printTerm(l.value)}"
  }

  private def printBody(b: CoreAst.Term.Body): String = {
    if (b.lets.isEmpty) printTerm(b.res)
    else {
      val letsStr = b.lets.map(printLet).mkString("\n")
      s"{ $letsStr \n ${printTerm(b.res)} }"
    }
  }

  private def printTermAtom(t: CoreAst.Term): String = t match {
    case CoreAst.Term.Ident(_, _)          => printTerm(t)
    case CoreAst.Term.App(_, _, _)         => printTerm(t)
    case CoreAst.Term.TApp(_, _, _)        => printTerm(t)
    case CoreAst.Term.Lam(_, _, _, _)      => s"(${printTerm(t)})"
    case CoreAst.Term.Match(_, _, _, _, _) => s"(${printTerm(t)})"
  }

  def printTerm(t: CoreAst.Term): String = t match {
    case tt: CoreAst.TypeTerm => printTypeTerm(tt)
    case CoreAst.Term.App(fn, args, _) =>
      val head = printTermAtom(fn)
      val as = args.toList.map(printTermAtom).mkString(" ")
      s"$head $as"
    case CoreAst.Term.Lam(ty, body, _, _) =>
      s"fun ${printBinders(ty.binders)}: ${printTypeTerm(ty.out)} => ${printTerm(body)}"
    case m @ CoreAst.Term.Match(_, _, _, _, _) => printMatch(m)
    case b: CoreAst.Term.Body                  => printBody(b)
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

  def print(value: Interpreter.Value): String = value match {
    case Interpreter.VUniverse               => "Type"
    case Interpreter.VPi(_, binders, out, _) => printTypeTerm(CoreAst.Term.Pi(binders, out, Span(0, 0)))
    case Interpreter.VConst(name, _, _)      => name
    case Interpreter.VApp(head, args, _)     => printApp(head, args)
    case Interpreter.VLam(_, _, id)          => s"func#$id"
    case Interpreter.Meta(name, id, _)       => s"$name#$id"
    case s: Interpreter.StuckMatch           => s"match#${s.id}"
  }

}
