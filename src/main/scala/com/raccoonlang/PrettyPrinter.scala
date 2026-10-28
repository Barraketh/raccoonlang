package com.raccoonlang

import com.raccoonlang.Value.LevelTpe

object PrettyPrinter {
  private def printNatForm(poly: Value.VNatPoly): String = {
    val constant = poly.form.constant
    val terms = poly.form.terms
    // Ground values print as literals. Operands that are forms with terms print in parentheses, as in
    // `2 * a * (b + 1)^2 * x^(c + d) + b + 3`, and numeral bases in decimal, as in `2^n`.
    if (terms.isEmpty) constant.toString
    else {
      def operandText(operand: Value): String =
        operand match {
          case poly: Value.VNatPoly if poly.form.terms.nonEmpty => s"(${printNatForm(poly)})"
          case other                                            => print(other)
        }
      def factorText(factor: NatNormalForm.Factor): String =
        factor match {
          case power: NatNormalForm.NumeralPower =>
            val base = operandText(power.base)
            if (power.exponent == 1) base else s"$base^${power.exponent}"
          case power: NatNormalForm.SymbolicPower => s"${operandText(power.base)}^${operandText(power.exponent)}"
        }
      val nonconstant = terms.map { term =>
        val product = term.monomial.factors.map(factorText).mkString(" * ")
        if (term.coefficient == 1) product else s"${term.coefficient} * $product"
      }
      (if (constant == 0) nonconstant else nonconstant :+ constant.toString).mkString(" + ")
    }
  }

  private def printRef(ref: CoreAst.Term.Ref): String = ref match {
    case CoreAst.Term.GlobalRef(name, _) => name
    case CoreAst.Term.LocalRef(ref, _)   => ref.name
  }

  private def printTypeTerm(tt: CoreAst.TypeTerm): String = {
    import com.raccoonlang.CoreAst.Term

    def pt(t: CoreAst.TypeTerm): String = t match {
      case ref: Term.Ref          => printRef(ref)
      case Term.NatLit(number, _) => number.toString
      case Term.StrLit(text, _)   => UnicodeScalarString.renderQuoted(text)
      case select: Term.Select    => printCoreTerm(select)
      case Term.Derive(goal, _)   => s"derive[${pt(goal)}]"
      case app: Term.App          => printCoreTerm(app)
      case Term.Pi(binders, out, _, _) =>
        val bindersStr = binders
          .map(printPiBinder)
          .mkString(" -> ")
        s"$bindersStr -> ${pt(out)}"
    }

    def ptAtom(t: CoreAst.TypeTerm): String = t match {
      case _: Term.Ref         => pt(t)
      case Term.NatLit(_, _)   => pt(t)
      case Term.StrLit(_, _)   => pt(t)
      case _: Term.Select      => pt(t)
      case Term.Derive(_, _)   => pt(t)
      case _: Term.App         => pt(t)
      case Term.Pi(_, _, _, _) => s"(${pt(t)})"
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

  private def printDecreaseSpec(spec: CoreAst.DecreaseSpec): String =
    spec match {
      case CoreAst.DecreaseSpec.Lexicographic(args, _) =>
        s"decreases lexicographic(${args.map(_.name).mkString(", ")})"
      case CoreAst.DecreaseSpec.Measure(term, _) =>
        s"decreases measure(${printCoreTerm(term)})"
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
      // A global function, such as a native stuck on its arguments, prints as its name.
      case Value.VLam(_, Value.ValueId.Const(name), _) => name
      case _                                           => s"(${print(head)})"
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
    case _: CoreAst.Term.Ref                     => printCoreTerm(t)
    case CoreAst.Term.NatLit(_, _)               => printCoreTerm(t)
    case CoreAst.Term.StrLit(_, _)               => printCoreTerm(t)
    case CoreAst.Term.App(_, _, _)               => printCoreTerm(t)
    case CoreAst.Term.Derive(_, _)               => printCoreTerm(t)
    case CoreAst.Term.Select(_, _, _)            => printCoreTerm(t)
    case CoreAst.Term.Lam(_, _, _, _, _, _, _)   => s"(${printCoreTerm(t)})"
    case CoreAst.Term.Match(_, _, _, _, _)       => s"(${printCoreTerm(t)})"
    case CoreAst.Term.MatchOne(_, _, _, _, _, _) => s"(${printCoreTerm(t)})"
    case CoreAst.Term.Body(_, _, _)              => s"(${printCoreTerm(t)})"
    case CoreAst.Term.Pi(_, _, _, _)             => s"(${printCoreTerm(t)})"
  }

  private def printCoreTerm(t: CoreAst.Term): String = t match {
    case CoreAst.Term.Lam(ty, _, body, _, _, recursion, _) =>
      val decreaseStr = recursion.map(r => s" ${printDecreaseSpec(r.decreases)}").getOrElse("")
      s"fun ${printBinders(ty.binders)}: ${printTypeTerm(ty.out)}$decreaseStr => ${printCoreTerm(body)}"
    case m @ CoreAst.Term.Match(_, _, _, _, _)       => printMatch(m)
    case m @ CoreAst.Term.MatchOne(_, _, _, _, _, _) => printMatchOne(m)
    case b: CoreAst.Term.Body                        => printBody(b)
    case CoreAst.Term.Select(base, field, _)         => s"${printTermAtom(base)}[$field]"
    case CoreAst.Term.Derive(goal, _)                => s"derive[${printTypeTerm(goal)}]"
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
    val motiveStr = m.motive.map(motive => s" returning ${printTypeTerm(motive)}").getOrElse("")
    val casesStr = m.cases.map(printCase).mkString(" ")
    s"match $scrutStr$motiveStr with $casesStr"
  }

  private def printMatchOne(m: CoreAst.Term.MatchOne): String = {
    val fields = m.fieldRefs.map(_.name).mkString(", ")
    val motiveStr = m.motive.map(motive => s" returning ${printTypeTerm(motive)}").getOrElse("")
    s"matchOne ${printTermAtom(m.scrut)}$motiveStr with ($fields) => ${printCoreTerm(m.body)}"
  }

  private def printElabRef(ref: ElabAst.Term.Ref): String = ref match {
    case ElabAst.Term.GlobalRef(name, _) => name
    case ElabAst.Term.LocalRef(ref, _)   => ref.name
  }

  private def printElabTypeTerm(tt: ElabAst.TypeTerm): String = {
    import com.raccoonlang.ElabAst.Term

    def pt(t: ElabAst.TypeTerm): String = t match {
      case ref: Term.Ref => printElabRef(ref)
      case Term.App(fn, args, _) =>
        val headStr = printElabTermAtom(fn)
        val argsStr = args.map(printElabTermAtom).mkString(", ")
        s"$headStr($argsStr)"
      case Term.NatLit(number, _) => number.toString
      case Term.StrLit(text, _)   => UnicodeScalarString.renderQuoted(text)
      case word: Term.Word        => printElabWord(word)
      case Term.Pi(binders, out, _, _, _) =>
        val bindersStr = binders
          .map(printElabPiBinder)
          .mkString(" -> ")
        s"$bindersStr -> ${pt(out)}"
    }

    def ptAtom(t: ElabAst.TypeTerm): String = t match {
      case _: Term.Ref            => pt(t)
      case Term.App(_, _, _)      => pt(t)
      case Term.NatLit(_, _)      => pt(t)
      case Term.StrLit(_, _)      => pt(t)
      case _: Term.Word           => pt(t)
      case Term.Pi(_, _, _, _, _) => s"(${pt(t)})"
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
    case _: ElabAst.Term.Ref                => printElabTerm0(t)
    case ElabAst.Term.App(_, _, _)          => printElabTerm0(t)
    case ElabAst.Term.NatLit(_, _)          => printElabTerm0(t)
    case ElabAst.Term.StrLit(_, _)          => printElabTerm0(t)
    case ElabAst.Term.Word(_, _, _)         => printElabTerm0(t)
    case ElabAst.Term.Lam(_, _, _, _, _, _) => s"(${printElabTerm0(t)})"
    case ElabAst.Term.Match(_, _, _, _, _)  => s"(${printElabTerm0(t)})"
    case ElabAst.Term.Body(_, _, _)         => s"(${printElabTerm0(t)})"
    case ElabAst.Term.Pi(_, _, _, _, _)     => s"(${printElabTerm0(t)})"
  }

  private def printElabTerm0(t: ElabAst.Term): String = t match {
    case ElabAst.Term.Lam(ty, body, _, _, _, _) =>
      s"fun ${printElabBinders(ty.binders)}: ${printElabTypeTerm(ty.out)} => ${printElabTerm0(body)}"
    case m @ ElabAst.Term.Match(_, _, _, _, _) => printElabMatch(m)
    case b: ElabAst.Term.Body                  => printElabBody(b)
    case tt: ElabAst.TypeTerm                  => printElabTypeTerm(tt)
  }

  /**
   * A word as the nested applications it stands for, built in a loop: each layer as its cons application around the
   * rest, and each splice before the end as `List.append` of it and the rest.
   */
  private def printElabWord(word: ElabAst.Term.Word): String = {
    val result = new StringBuilder
    val closings = scala.collection.mutable.ArrayBuffer.empty[String]
    word.pieces.init.foreach {
      case ElabAst.Term.WordPiece.Layer(before, after) =>
        result ++= word.consHead.name ++= "("
        before.foreach(arg => result ++= printElabTermAtom(arg) ++= ", ")
        closings += after.map(arg => ", " + printElabTermAtom(arg)).mkString + ")"
      case ElabAst.Term.WordPiece.Splice(list) =>
        result ++= "List.append(" ++= printElabTermAtom(list) ++= ", "
        closings += ")"
    }
    result ++= printElabTermAtom(word.pieces.last.asInstanceOf[ElabAst.Term.WordPiece.Splice].list)
    closings.reverseIterator.foreach(result ++= _)
    result.toString
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

  /**
   * A word, in one loop over its tokens. A kernel `List` word prints as its elements in brackets, followed by `++` and
   * its end unless that is `nil`, such as `[a, b] ++ xs`. A word of a user list-shaped type prints as nested
   * constructor applications, as for any constructor, ending in its terminator.
   */
  private def printWord(word: Value.VWord): String = {
    val elements = scala.collection.mutable.ArrayBuffer.empty[String]
    val opens = new StringBuilder
    val closings = scala.collection.mutable.ArrayBuffer.empty[String]
    var end: Value = null
    packed.Words.foreach(word)(
      layer = token => {
        if (token.head.name == Kernel.ListConsName) elements += print(token.payload(0))
        else {
          val recursive = token.recursiveIndex
          val before = (0 until recursive).map(index => print(token.payload(index)) + ", ")
          val after = (recursive until token.payloadWidth).map(index => ", " + print(token.payload(index)))
          opens ++= token.head.name + "(" + before.mkString
          closings += after.mkString + ")"
        }
        true
      },
      end = token => {
        end = token.value
        true
      }
    )
    // Only a user type's layers have closings, and only a kernel `List` 's have elements.
    if (closings.nonEmpty) opens.toString + print(end) + closings.reverseIterator.mkString
    else if (Kernel.isListNil(end)) elements.mkString("[", ", ", "]")
    else elements.mkString("[", ", ", "]") + " ++ " + print(end)
  }

  /**
   * A value as source-like text. A `String.mk` whose list ends in `nil` and holds only closed scalar characters prints
   * as a literal; any other string prints as its constructor applied to its list.
   */
  def print(value: Value): String = value match {
    case packed.Strings.Literal(text)                => UnicodeScalarString.renderQuoted(text)
    case nil if Kernel.isListNil(nil)                => "[]"
    case word: Value.VWord                           => printWord(word)
    case Value.PropTpe                               => "Prop"
    case Value.VSort(lvl) if lvl == Value.Level.zero => "Type"
    case Value.VSort(lvl)                            => s"Sort($lvl)"
    case Value.KernelObject                          => "KernelObject"
    case level: Value.Level                          => s"Level(${level.atoms}, ${level.c})"
    case pi: Value.VPi                               => "VPi"
    case Value.VConst(name, _, _)                    => name
    case Value.ConstructorHead(name, _, _, _, _)     => name
    case Value.VCtor(head, fields, _) =>
      val headStr = print(head)
      if (head.name == Kernel.ZeroName) "0" // as every other ground Nat prints as a literal
      else if (fields.isEmpty) headStr
      else s"$headStr(${fields.map(print).mkString(", ")})"
    case poly: Value.VNatPoly   => printNatForm(poly)
    case v: Value.VApp          => printApp(v.head, v.args)
    case v: Value.VLam          => s"func#${v.id}"
    case Value.Var(name, id, _) => s"$name#$id"
    case s: Value.NeutralThunk  => s"match#${s.id}"
    case LevelTpe               => s"Level"
  }

}
