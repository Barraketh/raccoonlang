package com.raccoonlang

import com.raccoonlang.Value.LevelTpe

object PrettyPrinter {
  private def printRef(ref: CoreAst.Term.Ref): String = ref match {
    case CoreAst.Term.GlobalRef(name, _) => name
    case CoreAst.Term.LocalRef(ref, _)   => ref.name
  }

  private def printTypePattern(tp: CoreAst.TypePattern): String = {
    import com.raccoonlang.CoreAst.Term

    def pt(t: CoreAst.TypePattern): String = t match {
      case ref: Term.Ref                => printRef(ref)
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
      case Term.Capture(name, _, _) => s"$$$name"
    }

    def ptAtom(t: CoreAst.TypePattern): String = t match {
      case _: Term.Ref              => pt(t)
      case Term.TSelect(_, _, _)    => pt(t)
      case Term.TApp(_, _, _)       => pt(t)
      case Term.PatternApp(_, _, _) => pt(t)
      case Term.Pi(_, _, _)         => s"(${pt(t)})"
      case Term.Capture(_, _, _)    => pt(t)
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

  def printBinder(b: CoreAst.Binder): String = {
    val body = s"${b.name}: ${printTypePattern(b.ty)}"
    if (b.isDerived) s"[$body]" else if (b.isInstance) s"(instance $body)" else s"($body)"
  }

  private def printBinders(binders: Util.NEL[CoreAst.Binder]): String =
    binders.toList.map(printBinder).mkString(" ")

  // ---- Core term pretty printing (for neutral match bodies/scrutinees) ----
  private def printLet(l: CoreAst.Let): String = {
    val tyStr = l.ty.map(t => s": ${printTypePattern(t)}").getOrElse("")
    val inst = if (l.isInstance) "instance " else ""
    s"let $inst${l.name}$tyStr := ${printTerm(l.value)}"
  }

  private def printBody(b: CoreAst.Term.Body): String = {
    if (b.lets.isEmpty) printTerm(b.res)
    else {
      val letsStr = b.lets.map(printLet).mkString("\n")
      s"{ $letsStr \n ${printTerm(b.res)} }"
    }
  }

  private def printTermAtom(t: CoreAst.Ast): String = t match {
    case _: CoreAst.Term.Ref                 => printTerm(t)
    case CoreAst.Term.App(_, _, _)           => printTerm(t)
    case CoreAst.Term.TApp(_, _, _)          => printTerm(t)
    case ts: CoreAst.Term.TSelect            => printTypeTerm(ts)
    case CoreAst.Term.Select(base, field, _) => s"${printTermAtom(base)}[$field]"
    case p: CoreAst.Term.PatternApp          => printTypePattern(p)
    case CoreAst.Term.Lam(_, _, _, _, _, _)  => s"(${printTerm(t)})"
    case CoreAst.Term.Match(_, _, _, _)      => s"(${printTerm(t)})"
    case CoreAst.Term.Body(_, _, _)          => s"(${printTerm(t)})"
    case CoreAst.Term.Pi(_, _, _)            => s"(${printTerm(t)})"
    case CoreAst.Term.Capture(name, _, _)    => s"$$$name"
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
    case m @ CoreAst.Term.Match(_, _, _, _) => printMatch(m)
    case b: CoreAst.Term.Body               => printBody(b)
    case CoreAst.Term.Capture(name, _, _)  => s"$$$name"
  }

  private def printCase(c: CoreAst.Case): String = {
    val args = if (c.argNames.isEmpty) "" else s" ${c.argNames.mkString(" ")}"
    s"| ${c.ctorName}$args => ${printTerm(c.body)}"
  }

  private def printMatch(m: CoreAst.Term.Match): String = {
    val scrutStr = printTermAtom(m.scrut)
    val motiveStr = m.motive.map(motive => s" returning ${printTypeTerm(motive)}").getOrElse("")
    val casesStr = m.cases.map(printCase).mkString(" ")
    s"match $scrutStr$motiveStr with $casesStr"
  }

  private def printElabRef(ref: ElabAst.Term.Ref): String = ref match {
    case ElabAst.Term.GlobalRef(name, _) => name
    case ElabAst.Term.LocalRef(ref, _)   => ref.name
  }

  private def printElabTypePattern(tp: ElabAst.TypePattern): String = {
    def pt(t: ElabAst.TypePattern): String = t match {
      case ref: ElabAst.Term.Ref => printElabRef(ref)
      case ElabAst.Term.Select(base, field, _) => s"${printElabTermAtom(base)}[$field]"
      case ElabAst.Term.App(fn, args, _) =>
        val head = printElabTermAtom(fn)
        val as = args.map(printElabTermAtom).mkString(", ")
        s"$head($as)"
      case ElabAst.Term.PatternApp(fn, args, _) =>
        val head = printElabRef(fn)
        val as = args.toList.map(ptAtom).mkString(", ")
        s"$head($as)"
      case ElabAst.Term.Pi(binders, out, _) =>
        s"${printElabBinders(binders)} -> ${printElabTypeTerm(out)}"
      case ElabAst.Term.Capture(name, _, _) => s"$$$name"
    }

    def ptAtom(t: ElabAst.TypePattern): String = t match {
      case _: ElabAst.Term.Ref              => pt(t)
      case ElabAst.Term.Select(_, _, _)     => pt(t)
      case ElabAst.Term.App(_, _, _)        => pt(t)
      case ElabAst.Term.PatternApp(_, _, _) => pt(t)
      case ElabAst.Term.Pi(_, _, _)         => s"(${pt(t)})"
      case ElabAst.Term.Capture(_, _, _)    => pt(t)
    }

    pt(tp)
  }

  private def printElabTypeTerm(tt: ElabAst.TypeTerm): String = printElabTypePattern(tt)

  private def printElabBinder(b: ElabAst.Binder): String = {
    val body = s"${b.name}: ${printElabTypePattern(b.ty)}"
    if (b.isDerived) s"[$body]" else if (b.isInstance) s"(instance $body)" else s"($body)"
  }

  private def printElabBinders(binders: Util.NEL[ElabAst.Binder]): String =
    binders.toList.map(printElabBinder).mkString(" ")

  private def printElabTermAtom(t: ElabAst.Ast): String = t match {
    case _: ElabAst.Term.Ref                 => printElabTerm(t)
    case ElabAst.Term.App(_, _, _)           => printElabTerm(t)
    case ElabAst.Term.Select(base, field, _) => s"${printElabTermAtom(base)}[$field]"
    case p: ElabAst.Term.PatternApp          => printElabTypePattern(p)
    case ElabAst.Term.Lam(_, _, _, _, _, _)  => s"(${printElabTerm(t)})"
    case ElabAst.Term.Match(_, _, _, _)      => s"(${printElabTerm(t)})"
    case ElabAst.Term.Body(_, _, _)          => s"(${printElabTerm(t)})"
    case ElabAst.Term.Pi(_, _, _)            => s"(${printElabTerm(t)})"
    case ElabAst.Term.Capture(name, _, _)    => s"$$$name"
  }

  private def printElabLet(l: ElabAst.Let): String = {
    val tyStr = l.ty.map(t => s": ${printElabTypeTerm(t)}").getOrElse("")
    val inst = if (l.isInstance) "instance " else ""
    s"let $inst${l.name}$tyStr := ${printElabTerm(l.value)}"
  }

  private def printElabBody(b: ElabAst.Term.Body): String = {
    if (b.lets.isEmpty) printElabTerm(b.res)
    else {
      val letsStr = b.lets.map(printElabLet).mkString("\n")
      s"{ $letsStr \n ${printElabTerm(b.res)} }"
    }
  }

  private def printElabCase(c: ElabAst.Case): String = {
    val args = if (c.argNames.isEmpty) "" else s" ${c.argNames.mkString(" ")}"
    s"| ${c.ctorName}$args => ${printElabTerm(c.body)}"
  }

  private def printElabMatch(m: ElabAst.Term.Match): String = {
    val scrutStr = printElabTermAtom(m.scrut)
    val motiveStr = m.motive.map(motive => s" returning ${printElabTypeTerm(motive)}").getOrElse("")
    val casesStr = m.cases.map(printElabCase).mkString(" ")
    s"match $scrutStr$motiveStr with $casesStr"
  }

  def printElabTerm(t: ElabAst.Ast): String = t match {
    case ref: ElabAst.Term.Ref => printElabRef(ref)
    case ElabAst.Term.Select(base, field, _) => s"${printElabTermAtom(base)}[$field]"
    case ElabAst.Term.App(fn, args, _) =>
      val head = printElabTermAtom(fn)
      val as = args.map(printElabTermAtom).mkString(", ")
      s"$head($as)"
    case p: ElabAst.Term.PatternApp => printElabTypePattern(p)
    case ElabAst.Term.Pi(binders, out, _) =>
      s"${printElabBinders(binders)} -> ${printElabTypeTerm(out)}"
    case ElabAst.Term.Capture(name, _, _) => s"$$$name"
    case ElabAst.Term.Lam(ty, _, body, _, _, _) =>
      s"fun ${printElabBinders(ty.binders)}: ${printElabTypeTerm(ty.out)} => ${printElabTerm(body)}"
    case m @ ElabAst.Term.Match(_, _, _, _) => printElabMatch(m)
    case b: ElabAst.Term.Body               => printElabBody(b)
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
