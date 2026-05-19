package com.raccoonlang

import com.raccoonlang.Value.LevelTpe

object PrettyPrinter {
  private def printRef(ref: CoreAst.Term.Ref): String = ref match {
    case CoreAst.Term.GlobalRef(name, _) => name
    case CoreAst.Term.LocalRef(ref, _)   => ref.name
  }

  private def printTypeTerm(tt: CoreAst.TypeTerm): String = {
    import com.raccoonlang.CoreAst.Term

    def pt(t: CoreAst.TypeTerm): String = t match {
      case ref: Term.Ref                => printRef(ref)
      case Term.TSelect(base, field, _) => s"${ptAtom(base)}[$field]"
      case Term.TApp(fn, args, _) =>
        val headStr = ptAtom(fn)
        val argsStr = args.map(ptAtom).mkString(", ")
        s"$headStr($argsStr)"
      case Term.Pi(binders, out, _) =>
        val bindersStr = binders
          .map(printPiBinder)
          .mkString(" -> ")
        s"$bindersStr -> ${pt(out)}"
    }

    def ptAtom(t: CoreAst.TypeTerm): String = t match {
      case _: Term.Ref           => pt(t)
      case Term.TSelect(_, _, _) => pt(t)
      case Term.TApp(_, _, _)    => pt(t)
      case Term.Pi(_, _, _)      => s"(${pt(t)})"
    }

    def printPiBinder(b: CoreAst.Binder): String =
      b.ty match {
        case CoreAst.BinderType.TypePattern(CoreAst.TypePattern.Type(term), _) if b.name == "_" && !b.isInstance =>
          ptAtom(term)
        case _ => printBinder(b)
      }

    pt(tt)
  }

  private def printTypePattern(tp: CoreAst.TypePattern): String = {
    def pt(t: CoreAst.TypePattern): String = t match {
      case CoreAst.TypePattern.Type(term) => printTypeTerm(term)
      case CoreAst.TypePattern.App(fn, args, _) =>
        val headStr = printRef(fn)
        val argsStr = args.map(ptAtom).mkString(", ")
        s"$headStr($argsStr)"
      case CoreAst.TypePattern.Capture(ref, _) => s"$$${ref.name}"
    }

    def ptAtom(t: CoreAst.TypePattern): String = t match {
      case CoreAst.TypePattern.Type(term: CoreAst.Term.Pi) => s"(${printTypeTerm(term)})"
      case _                                               => pt(t)
    }

    pt(tp)
  }

  private def printBinderType(bt: CoreAst.BinderType): String =
    bt match {
      case CoreAst.BinderType.TypePattern(tp, _) => printTypePattern(tp)
      case CoreAst.BinderType.ConstrainedCapture(ref, constraint, _) =>
        s"$$${ref.name} in ${printTypePattern(constraint)}"
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

  def printBinder(b: CoreAst.Binder): String = {
    val body = s"${b.name}: ${printBinderType(b.ty)}"
    if (b.isInstance) s"[$body]" else s"($body)"
  }

  private def printBinders(binders: Vector[CoreAst.Binder]): String =
    binders.map(printBinder).mkString(" ")

  // ---- Core term pretty printing (for neutral match bodies/scrutinees) ----
  private def printLet(l: CoreAst.Let): String = {
    val tyStr = l.ty.map(t => s": ${printTypeTerm(t)}").getOrElse("")
    val inst = if (l.isInstance) "instance " else ""
    s"let $inst${l.name}$tyStr := ${printCoreTerm(l.value)}"
  }

  private def printBody(b: CoreAst.Term.Body): String = {
    if (b.lets.isEmpty) printCoreTerm(b.res)
    else {
      val letsStr = b.lets.map(printLet).mkString("\n")
      s"{ $letsStr \n ${printCoreTerm(b.res)} }"
    }
  }

  private def printTermAtom(t: CoreAst.Term): String = t match {
    case _: CoreAst.Term.Ref                 => printCoreTerm(t)
    case CoreAst.Term.App(_, _, _)           => printCoreTerm(t)
    case CoreAst.Term.Derive(_, _)           => printCoreTerm(t)
    case CoreAst.Term.TApp(_, _, _)          => printCoreTerm(t)
    case ts: CoreAst.Term.TSelect            => printTypeTerm(ts)
    case CoreAst.Term.Select(base, field, _) => s"${printTermAtom(base)}[$field]"
    case CoreAst.Term.Lam(_, _, _, _, _, _)  => s"(${printCoreTerm(t)})"
    case CoreAst.Term.Match(_, _, _, _)      => s"(${printCoreTerm(t)})"
    case CoreAst.Term.Body(_, _, _)          => s"(${printCoreTerm(t)})"
    case CoreAst.Term.Pi(_, _, _)            => s"(${printCoreTerm(t)})"
  }

  private def printCoreTerm(t: CoreAst.Term): String = t match {
    case CoreAst.Term.Lam(ty, _, body, _, _, _) =>
      s"fun ${printBinders(ty.binders)}: ${printTypeTerm(ty.out)} => ${printCoreTerm(body)}"
    case m @ CoreAst.Term.Match(_, _, _, _)  => printMatch(m)
    case b: CoreAst.Term.Body                => printBody(b)
    case CoreAst.Term.Select(base, field, _) => s"${printTermAtom(base)}[$field]"
    case CoreAst.Term.Derive(goal, _)        => s"derive[${printTypeTerm(goal)}]"
    case CoreAst.Term.App(fn, args, _) =>
      val headStr = printTermAtom(fn)
      val argsStr = args.map(printTermAtom).mkString(", ")
      s"$headStr($argsStr)"
    case tt: CoreAst.TypeTerm => printTypeTerm(tt)
  }

  def printTerm(t: CoreAst.Ast): String = t match {
    case term: CoreAst.Term             => printCoreTerm(term)
    case pattern: CoreAst.TypePattern   => printTypePattern(pattern)
    case binderType: CoreAst.BinderType => printBinderType(binderType)
  }

  private def printCase(c: CoreAst.Case): String = {
    val argNames = c.argRefs.map(_.map(_.name).getOrElse("_"))
    val args = if (argNames.isEmpty) "" else s" ${argNames.mkString(" ")}"
    val ctor = if (c.isFullyQualified) c.ctorName else s".${c.ctorName}"
    s"| $ctor$args => ${printCoreTerm(c.body)}"
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

  private def printElabTypeTerm(tt: ElabAst.TypeTerm): String = {
    import com.raccoonlang.ElabAst.Term

    def pt(t: ElabAst.TypeTerm): String = t match {
      case ref: Term.Ref                  => printElabRef(ref)
      case Term.Select(base, field, _, _) => s"${printElabTermAtom(base)}[$field]"
      case Term.App(fn, args, _) =>
        val headStr = printElabTermAtom(fn)
        val argsStr = args.map(printElabTermAtom).mkString(", ")
        s"$headStr($argsStr)"
      case Term.Pi(binders, out, _, _) =>
        val bindersStr = binders
          .map(printElabPiBinder)
          .mkString(" -> ")
        s"$bindersStr -> ${pt(out)}"
    }

    def ptAtom(t: ElabAst.TypeTerm): String = t match {
      case _: Term.Ref             => pt(t)
      case Term.Select(_, _, _, _) => pt(t)
      case Term.App(_, _, _)       => pt(t)
      case Term.Pi(_, _, _, _)     => s"(${pt(t)})"
    }

    def printElabPiBinder(b: ElabAst.Binder): String =
      b.ty match {
        case ElabAst.BinderType.TypePattern(ElabAst.TypePattern.Type(term), _) if b.name == "_" && !b.isInstance =>
          ptAtom(term)
        case _ => printElabBinder(b)
      }

    pt(tt)
  }

  private def printElabTypePattern(tp: ElabAst.TypePattern): String = {
    def pt(t: ElabAst.TypePattern): String = t match {
      case ElabAst.TypePattern.Type(term) => printElabTypeTerm(term)
      case ElabAst.TypePattern.App(fn, args, _) =>
        val headStr = printElabRef(fn)
        val argsStr = args.map(ptAtom).mkString(", ")
        s"$headStr($argsStr)"
      case ElabAst.TypePattern.Capture(ref, _) => s"$$${ref.name}"
    }

    def ptAtom(t: ElabAst.TypePattern): String = t match {
      case ElabAst.TypePattern.Type(term: ElabAst.Term.Pi) => s"(${printElabTypeTerm(term)})"
      case _                                               => pt(t)
    }

    pt(tp)
  }

  private def printElabBinderType(bt: ElabAst.BinderType): String =
    bt match {
      case ElabAst.BinderType.TypePattern(tp, _) => printElabTypePattern(tp)
      case ElabAst.BinderType.ConstrainedCapture(ref, constraint, _) =>
        s"$$${ref.name} in ${printElabTypePattern(constraint)}"
    }

  def printElabBinder(b: ElabAst.Binder): String = {
    val body = s"${b.name}: ${printElabBinderType(b.ty)}"
    if (b.isInstance) s"(instance $body)" else s"($body)"
  }

  private def printElabBinders(binders: Vector[ElabAst.Binder]): String =
    binders.map(printElabBinder).mkString(" ")

  private def printElabLet(l: ElabAst.Let): String = {
    val tyStr = l.ty.map(t => s": ${printElabTypeTerm(t)}").getOrElse("")
    val inst = if (l.isInstance) "instance " else ""
    s"let $inst${l.name}$tyStr := ${printElabTerm0(l.value)}"
  }

  private def printElabBody(b: ElabAst.Term.Body): String = {
    if (b.lets.isEmpty) printElabTerm0(b.res)
    else {
      val letsStr = b.lets.map(printElabLet).mkString("\n")
      s"{ $letsStr \n ${printElabTerm0(b.res)} }"
    }
  }

  private def printElabTermAtom(t: ElabAst.Term): String = t match {
    case _: ElabAst.Term.Ref                    => printElabTerm0(t)
    case ElabAst.Term.App(_, _, _)              => printElabTerm0(t)
    case ElabAst.Term.Select(base, field, _, _) => s"${printElabTermAtom(base)}[$field]"
    case ElabAst.Term.Lam(_, _, _, _, _, _)     => s"(${printElabTerm0(t)})"
    case ElabAst.Term.Match(_, _, _, _)         => s"(${printElabTerm0(t)})"
    case ElabAst.Term.Body(_, _, _)             => s"(${printElabTerm0(t)})"
    case ElabAst.Term.Pi(_, _, _, _)            => s"(${printElabTerm0(t)})"
  }

  private def printElabTerm0(t: ElabAst.Term): String = t match {
    case ElabAst.Term.Lam(ty, _, body, _, _, _) =>
      s"fun ${printElabBinders(ty.binders)}: ${printElabTypeTerm(ty.out)} => ${printElabTerm0(body)}"
    case m @ ElabAst.Term.Match(_, _, _, _) => printElabMatch(m)
    case b: ElabAst.Term.Body               => printElabBody(b)
    case tt: ElabAst.TypeTerm               => printElabTypeTerm(tt)
  }

  def printElabTerm(t: ElabAst.Ast): String = t match {
    case term: ElabAst.Term             => printElabTerm0(term)
    case pattern: ElabAst.TypePattern   => printElabTypePattern(pattern)
    case binderType: ElabAst.BinderType => printElabBinderType(binderType)
  }

  private def printElabCase(c: ElabAst.Case): String = {
    val argNames = c.argRefs.map(_.map(_.name).getOrElse("_"))
    val args = if (argNames.isEmpty) "" else s" ${argNames.mkString(" ")}"
    s"| ${c.ctorName}$args => ${printElabTerm0(c.body)}"
  }

  private def printElabMatch(m: ElabAst.Term.Match): String = {
    val scrutStr = printElabTermAtom(m.scrut)
    val motiveStr = m.motive.map(motive => s" returning ${printElabTypeTerm(motive)}").getOrElse("")
    val casesStr = m.cases.map(printElabCase).mkString(" ")
    s"match $scrutStr$motiveStr with $casesStr"
  }

  def print(value: Value): String = value match {
    case Value.PropTpe                              => "Prop"
    case Value.VSort(lvl) if lvl == Value.Level.one => "Type"
    case Value.VSort(lvl)                           => s"Sort($lvl)"
    case Value.KernelObject                         => "KernelObject"
    case level: Value.Level                         => s"Level(${level.atoms}, ${level.c})"
    case pi: Value.VPi                              => "VPi"
    case Value.VConst(name, _, _)                   => name
    case v: Value.AppliedValue                      => printApp(v.head, v.args)
    case Value.ConstructorHead(name, _, _, _, _)    => name
    case ctor @ Value.VCtor(head, _, _) =>
      val headStr = print(head)
      val fields = ctor.fields
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
