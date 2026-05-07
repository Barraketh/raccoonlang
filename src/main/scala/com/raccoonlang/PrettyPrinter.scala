package com.raccoonlang

import com.raccoonlang.Value.LevelTpe

object PrettyPrinter {
  private def printRef(ref: CoreAst.Term.Ref[_]): String = ref match {
    case CoreAst.Term.GlobalRef(name, _) => name
    case CoreAst.Term.LocalRef(ref, _)   => ref.name
  }

  private def printTypeTerm(tt: CoreAst.TypeTerm[_]): String = {
    import com.raccoonlang.CoreAst.Term

    def pt(t: CoreAst.TypeTerm[_]): String = t match {
      case ref: Term.Ref[_]             => printRef(ref)
      case Term.TSelect(base, field, _) => s"${ptAtom(base)}[$field]"
      case Term.Select(base, field, _)  => s"${printTermAtom(base)}[$field]"
      case Term.TApp(fn, args, _) =>
        val headStr = ptAtom(fn)
        val argsStr = args.toList.map(ptAtom).mkString(", ")
        s"$headStr($argsStr)"
      case Term.App(fn, args, _) =>
        val headStr = printTermAtom(fn)
        val argsStr = args.map(printTermAtom).mkString(", ")
        s"$headStr($argsStr)"
      case Term.Pi(binders, out, _) =>
        val bindersStr = binders.toList
          .map { b =>
            if (b.name == "_") printTypePattern(b.ty) else s"(${b.name}: ${printTypePattern(b.ty)})"
          }
          .mkString(" -> ")
        s"$bindersStr -> ${pt(out)}"
    }

    def ptAtom(t: CoreAst.TypeTerm[_]): String = t match {
      case _: Term.Ref[_]           => pt(t)
      case Term.TSelect(_, _, _)    => pt(t)
      case Term.Select(_, _, _)     => pt(t)
      case Term.TApp(_, _, _)       => pt(t)
      case Term.App(_, _, _)        => pt(t)
      case Term.Pi(_, _, _)         => s"(${pt(t)})"
    }

    pt(tt)
  }

  private def printTypePattern(tp: CoreAst.TypePattern[_]): String = {
    def pt(t: CoreAst.TypePattern[_]): String = t match {
      case CoreAst.TypePattern.Type(term) => printTypeTerm(term)
      case CoreAst.TypePattern.App(fn, args, _) =>
        val headStr = printRef(fn)
        val argsStr = args.toList.map(ptAtom).mkString(", ")
        s"$headStr($argsStr)"
      case CoreAst.TypePattern.Capture(ref, _) => s"$$${ref.name}"
    }

    def ptAtom(t: CoreAst.TypePattern[_]): String = t match {
      case CoreAst.TypePattern.Type(term: CoreAst.Term.Pi[_]) => s"(${printTypeTerm(term)})"
      case _                                                  => pt(t)
    }

    pt(tp)
  }

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

  def printBinder(b: CoreAst.Binder[_]): String = {
    val body = s"${b.name}: ${printTypePattern(b.ty)}"
    if (b.isDerived) s"[$body]" else if (b.isInstance) s"(instance $body)" else s"($body)"
  }

  private def printBinders[P <: CoreAst.Phase](binders: Util.NEL[CoreAst.Binder[P]]): String =
    binders.toList.map(printBinder).mkString(" ")

  // ---- Core term pretty printing (for neutral match bodies/scrutinees) ----
  private def printLet(l: CoreAst.Let[_]): String = {
    val tyStr = l.ty.map(t => s": ${printTypeTerm(t)}").getOrElse("")
    val inst = if (l.isInstance) "instance " else ""
    s"let $inst${l.name}$tyStr := ${printTerm(l.value)}"
  }

  private def printBody(b: CoreAst.Term.Body[_]): String = {
    if (b.lets.isEmpty) printTerm(b.res)
    else {
      val letsStr = b.lets.map(printLet).mkString("\n")
      s"{ $letsStr \n ${printTerm(b.res)} }"
    }
  }

  private def printTermAtom(t: CoreAst.Term[_]): String = t match {
    case _: CoreAst.Term.Ref[_]              => printTerm(t)
    case CoreAst.Term.App(_, _, _)           => printTerm(t)
    case CoreAst.Term.TApp(_, _, _)          => printTerm(t)
    case ts: CoreAst.Term.TSelect[_]         => printTypeTerm(ts)
    case CoreAst.Term.Select(base, field, _) => s"${printTermAtom(base)}[$field]"
    case CoreAst.Term.Lam(_, _, _, _, _, _)  => s"(${printTerm(t)})"
    case CoreAst.Term.Match(_, _, _, _)      => s"(${printTerm(t)})"
    case CoreAst.Term.Body(_, _, _)          => s"(${printTerm(t)})"
    case CoreAst.Term.Pi(_, _, _)            => s"(${printTerm(t)})"
  }

  def printTerm(t: CoreAst.Term[_]): String = t match {
    case CoreAst.Term.Lam(ty, _, body, _, _, _) =>
      s"fun ${printBinders(ty.binders)}: ${printTypeTerm(ty.out)} => ${printTerm(body)}"
    case m @ CoreAst.Term.Match(_, _, _, _) => printMatch(m)
    case b: CoreAst.Term.Body[_]            => printBody(b)
    case tt: CoreAst.TypeTerm[_]            => printTypeTerm(tt)
  }

  private def printCase(c: CoreAst.Case[_]): String = {
    val argNames = c.argRefs.map(_.map(_.name).getOrElse("_"))
    val args = if (argNames.isEmpty) "" else s" ${argNames.mkString(" ")}"
    s"| ${c.ctorName}$args => ${printTerm(c.body)}"
  }

  private def printMatch(m: CoreAst.Term.Match[_]): String = {
    val scrutStr = printTermAtom(m.scrut)
    val motiveStr = m.motive.map(motive => s" returning ${printTypeTerm(motive)}").getOrElse("")
    val casesStr = m.cases.map(printCase).mkString(" ")
    s"match $scrutStr$motiveStr with $casesStr"
  }

  def print(value: Value): String = value match {
    case Value.VSort(lvl)                        => s"Type $lvl"
    case Value.PropTpe                           => "Prop"
    case Value.KernelObject                      => "KernelObject"
    case Value.Level(atoms, c)                   => s"Level($atoms, $c)"
    case pi: Value.VPi                           => "VPi"
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
