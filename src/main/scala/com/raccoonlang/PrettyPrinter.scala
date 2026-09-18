package com.raccoonlang

import com.raccoonlang.Value.LevelTpe

object PrettyPrinter {
  private def printString(scalars: Vector[Int]): String = UnicodeScalarString.renderQuoted(scalars)

  private def printRef(ref: CoreAst.Term.Ref): String = ref match {
    case CoreAst.Term.GlobalRef(name, _) => name
    case CoreAst.Term.LocalRef(ref, _)   => ref.name
  }

  private def printDecreaseSpec(spec: CoreAst.DecreaseSpec): String =
    spec match {
      case CoreAst.DecreaseSpec.Lexicographic(args, _) =>
        s"decreases lexicographic(${args.map(_.name).mkString(", ")})"
      case CoreAst.DecreaseSpec.Measure(term, _) =>
        s"decreases measure(${printCoreTerm(term)})"
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
    val body = s"${b.name}: ${printCoreTerm(b.ty)}"
    if (b.isImplicit) s"{$body}" else s"($body)"
  }

  private def printPiBinder(b: CoreAst.Binder): String =
    if (b.name == "_" && !b.isImplicit) printTermAtom(b.ty)
    else printBinder(b)

  private def printBinders(binders: Vector[CoreAst.Binder]): String =
    binders.map(printBinder).mkString(" ")

  // ---- Core term pretty printing (for neutral match bodies/scrutinees) ----
  private def printLet(l: CoreAst.Let): String = {
    val tyStr = l.ty.map(t => s": ${printCoreTerm(t)}").getOrElse("")
    s"let ${l.name}$tyStr := ${printCoreTerm(l.value)}"
  }

  private def printBody(b: CoreAst.Term.Body): String = {
    if (b.lets.isEmpty) printCoreTerm(b.res)
    else {
      val letsStr = b.lets.map(printLet).mkString("\n")
      s"{ $letsStr \n ${printCoreTerm(b.res)} }"
    }
  }

  /**
   * A term in a position where an operator would bind tighter than the term prints: atoms and already-delimited forms
   * render as themselves, and the forms that print as loose infix-ish syntax get parenthesized.
   */
  private def printTermAtom(t: CoreAst.Term): String = t match {
    case _: CoreAst.Term.NatLit | _: CoreAst.Term.StrLit | _: CoreAst.Term.Ref | _: CoreAst.Term.App |
        _: CoreAst.Term.Select =>
      printCoreTerm(t)
    case _: CoreAst.Term.Lam | _: CoreAst.Term.Match | _: CoreAst.Term.Body | _: CoreAst.Term.Pi =>
      s"(${printCoreTerm(t)})"
  }

  private def printCoreTerm(t: CoreAst.Term): String = t match {
    case CoreAst.Term.NatLit(value, _)   => value.toString
    case CoreAst.Term.StrLit(scalars, _) => printString(scalars)
    case ref: CoreAst.Term.Ref           => printRef(ref)
    case CoreAst.Term.Lam(ty, body, _, _, recursion, _) =>
      val decreaseStr = recursion.map(r => s" ${printDecreaseSpec(r.decreases)}").getOrElse("")
      s"fun ${printBinders(ty.binders)}: ${printCoreTerm(ty.out)}$decreaseStr => ${printCoreTerm(body)}"
    case m @ CoreAst.Term.Match(_, _, _, _)  => printMatch(m)
    case b: CoreAst.Term.Body                => printBody(b)
    case CoreAst.Term.Select(base, field, _) => s"${printTermAtom(base)}[$field]"
    case CoreAst.Term.App(fn, args, _) =>
      val headStr = printTermAtom(fn)
      val argsStr = args.map(printTermAtom).mkString(", ")
      s"$headStr($argsStr)"
    case CoreAst.Term.Pi(binders, out, _, _) =>
      val bindersStr = binders.map(printPiBinder).mkString(" -> ")
      s"$bindersStr -> ${printCoreTerm(out)}"
  }

  def printTerm(t: CoreAst.Ast): String = t match {
    case term: CoreAst.Term             => printCoreTerm(term)
    case decrease: CoreAst.DecreaseSpec => printDecreaseSpec(decrease)
  }

  private def printCase(c: CoreAst.Case): String = {
    val argNames = c.argRefs.map(_.map(_.name).getOrElse("_"))
    val args = if (argNames.isEmpty) "" else s" ${argNames.mkString(" ")}"
    val ctor = if (c.isFullyQualified) c.ctorName else s".${c.ctorName}"
    s"| $ctor$args => ${printCoreTerm(c.body)}"
  }

  private def printMatch(m: CoreAst.Term.Match): String = {
    val scrutStr = printTermAtom(m.scrut)
    val motiveStr = m.motive.map(motive => s" returning ${printCoreTerm(motive)}").getOrElse("")
    val casesStr = m.cases.map(printCase).mkString(" ")
    s"match $scrutStr$motiveStr with $casesStr"
  }

  def print(value: Value): String = value match {
    case Value.PropTpe                              => "Prop"
    case Value.VSort(lvl) if lvl == Value.Level.one => "Type"
    case Value.VSort(lvl)                           => s"Sort($lvl)"
    case level: Value.Level                         => s"Level(${level.terms}, ${level.c})"
    case _: Value.VPi                               => "VPi"
    case Value.VConst(name, _, _)                   => name
    case Value.ConstructorHead(name, _, _, _, _)    => name
    case Value.VCtor(head, Vector(field: Value.VPacked), _)
        if head.name == "String.mk" && field.codec.isInstanceOf[Value.CharListCodec] =>
      printString(field.charScalars.getOrElse(throw WTF("Invalid packed String field")))
    case Value.VCtor(head, storedArgs, _) =>
      val headStr = print(head)
      if (storedArgs.isEmpty) headStr
      else s"$headStr(${storedArgs.map(print).mkString(", ")})"
    case v: Value.VApp         => printApp(v.head, v.args)
    case v: Value.VLam         => s"func#${v.id}"
    case v: Value.Var          => s"${v.name}#${v.id}"
    case s: Value.NeutralThunk => s"match#${s.id}"
    case p: Value.VProof       => s"‹proof of ${print(p.tpe)}›"
    case p: Value.VPacked =>
      p.natValue
        .map(_.toString)
        .orElse(p.charScalars.map(scalars => s"proj[String,0](${printString(scalars)})"))
        .getOrElse(throw WTF("Unknown packed payload"))
    case LevelTpe => s"Level"
  }

}
