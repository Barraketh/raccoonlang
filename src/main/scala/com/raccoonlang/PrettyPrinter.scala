package com.raccoonlang

import com.raccoonlang.Value.LevelTpe

import scala.util.control.NonFatal

object PrettyPrinter {
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
      case lam: Term.Lam          => printCoreTerm(lam)
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
      case _: Term.Lam         => s"(${pt(t)})"
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
      case CoreAst.TypePattern.Capture(ref, _, constraint) =>
        s"$$${ref.name}" + constraint.fold("")(c => s" in ${pt(c)}")
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
    spec.components match {
      case Vector(measure: CoreAst.MetricComponent.Measure) => s"decreases ${printMetricComponent(measure)}"
      case components => s"decreases lexicographic(${components.map(printMetricComponent).mkString(", ")})"
    }

  def printMetricComponent(component: CoreAst.MetricComponent): String =
    component match {
      case CoreAst.MetricComponent.Param(ref, _)    => ref.name
      case CoreAst.MetricComponent.Measure(term, _) => s"measure(${printCoreTerm(term)})"
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

  private def printCoreTermAtom(t: CoreAst.Term): String = t match {
    case _: CoreAst.Term.Ref                     => printCoreTerm(t)
    case CoreAst.Term.NatLit(_, _)               => printCoreTerm(t)
    case CoreAst.Term.StrLit(_, _)               => printCoreTerm(t)
    case CoreAst.Term.App(_, _, _)               => printCoreTerm(t)
    case CoreAst.Term.Derive(_, _)               => printCoreTerm(t)
    case CoreAst.Term.Select(_, _, _)            => printCoreTerm(t)
    case CoreAst.Term.Lam(_, _, _, _, _, _, _)   => s"(${printCoreTerm(t)})"
    case _: CoreAst.Term.Match                   => s"(${printCoreTerm(t)})"
    case CoreAst.Term.MatchOne(_, _, _, _, _, _) => s"(${printCoreTerm(t)})"
    case CoreAst.Term.Body(_, _, _)              => s"(${printCoreTerm(t)})"
    case CoreAst.Term.Pi(_, _, _, _)             => s"(${printCoreTerm(t)})"
    case CoreAst.Term.Rewrite(_, _, _, _)        => s"(${printCoreTerm(t)})"
  }

  private def printCoreTerm(t: CoreAst.Term): String = t match {
    case CoreAst.Term.Lam(ty, _, body, _, _, recursion, _) =>
      val decreaseStr = recursion.map(r => s" ${printDecreaseSpec(r.decreases)}").getOrElse("")
      s"fun ${printBinders(ty.binders)}: ${printTypeTerm(ty.out)}$decreaseStr => ${printCoreTerm(body)}"
    case m: CoreAst.Term.Match                       => printMatch(m)
    case m @ CoreAst.Term.MatchOne(_, _, _, _, _, _) => printMatchOne(m)
    case b: CoreAst.Term.Body                        => printBody(b)
    case CoreAst.Term.Rewrite(equation, reverse, body, _) =>
      s"rewrite ${if (reverse) "<- " else ""}${printCoreTerm(equation)} in ${printCoreTerm(body)}"
    case CoreAst.Term.Select(base, field, _)         => s"${printCoreTermAtom(base)}.$field"
    case CoreAst.Term.Derive(goal, _)                => s"derive[${printTypeTerm(goal)}]"
    case CoreAst.Term.App(fn, args, _) =>
      val headStr = printCoreTermAtom(fn)
      val argsStr = args.map(printTermAtom).mkString(", ")
      s"$headStr($argsStr)"
    case tt: CoreAst.TypeTerm => printTypeTerm(tt)
  }

  /** A core term as `printTerm` prints it, parenthesized where an argument or a head is expected. */
  def printTermAtom(t: CoreAst.Term): String = printCoreTermAtom(t)

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
    val scrutStr = printCoreTermAtom(m.scrut)
    val motiveStr = m.motive.map(motive => s" returning ${printTypeTerm(motive)}").getOrElse("")
    val casesStr = (m.cases.map(printCase) ++ m.wildcard.map(w => s"| _ => ${printCoreTerm(w.body)}")).mkString(" ")
    val equationStr = (m.cases.flatMap(_.equation) ++ m.wildcard.flatMap(_.equation)).headOption
      .fold("")(ref => s"${ref.name} : ")
    s"match $equationStr$scrutStr$motiveStr with $casesStr"
  }

  private def printMatchOne(m: CoreAst.Term.MatchOne): String = {
    val fields = m.fieldRefs.map(_.name).mkString(", ")
    val motiveStr = m.motive.map(motive => s" returning ${printTypeTerm(motive)}").getOrElse("")
    s"matchOne ${printCoreTermAtom(m.scrut)}$motiveStr with ($fields) => ${printCoreTerm(m.body)}"
  }

  /**
   * Checked syntax as source, printed to `out`. A local that `bound` binds prints there, such as a closure's captured
   * value, `bound` returning true; any other local prints by its binder's name.
   */
  private final class ElabPrinter(out: Out, bound: CoreAst.LocalRef => Boolean) {
    private def printElabRef(ref: ElabAst.Term.Ref): Unit = ref match {
      case ElabAst.Term.GlobalRef(name, _) => out += name
      case ElabAst.Term.LocalRef(ref, _)   => if (!bound(ref)) out += ref.name
    }


    def printElabTypeTerm(tt: ElabAst.TypeTerm): Unit = {
      import com.raccoonlang.ElabAst.Term

      def pt(t: ElabAst.TypeTerm): Unit = t match {
        case ref: Term.Ref => printElabRef(ref)
        case Term.App(fn, args, _) =>
          printElabTermAtom(fn)
          out.parenthesized(out.separated(args, ", ")(printElabTermAtom))
        // As written explicitly, which takes a base of any form, and reads back as the same projection.
        case Term.Proj(base, family, field, _, _) =>
          out += s"$family.$field"
          out.parenthesized(printElabTermAtom(base))
        case Term.NatLit(number, _) => out += number.toString
        case Term.StrLit(text, _)   => out += UnicodeScalarString.renderQuoted(text)
        case word: Term.Word        => printElabWord(word)
        case lam: Term.Lam          => printElabTerm0(lam)
        case Term.Pi(binders, codomain, _, _, _) =>
          out.separated(binders, " -> ")(printElabPiBinder)
          out += " -> "
          pt(codomain)
      }

      def ptAtom(t: ElabAst.TypeTerm): Unit = t match {
        case _: Term.Ref            => pt(t)
        case Term.App(_, _, _)      => pt(t)
        case _: Term.Proj           => pt(t)
        case Term.NatLit(_, _)      => pt(t)
        case Term.StrLit(_, _)      => pt(t)
        case _: Term.Word           => pt(t)
        case Term.Pi(_, _, _, _, _) => out.parenthesized(pt(t))
        case _: Term.Lam            => out.parenthesized(pt(t))
      }

      def printElabPiBinder(b: ElabAst.Binder): Unit =
        b.ty match {
          case ElabAst.BinderType.TypePattern(ElabAst.TypePattern.Type(term), _) if b.name == "_" && !b.isInstance =>
            ptAtom(term)
          case _ => printElabBinder(b)
        }

      pt(tt)
    }

    private def printElabTypePattern(tp: ElabAst.TypePattern): Unit = {
      def pt(t: ElabAst.TypePattern): Unit = t match {
        case ElabAst.TypePattern.Type(term) => printElabTypeTerm(term)
        case ElabAst.TypePattern.App(fn, args, _) =>
          printElabRef(fn)
          out.parenthesized(out.separated(args, ", ")(ptAtom))
        case ElabAst.TypePattern.Capture(ref, _, constraint) =>
          out += s"$$${ref.name}"
          constraint.foreach { c =>
            out += " in "
            pt(c)
          }
      }

      def ptAtom(t: ElabAst.TypePattern): Unit = t match {
        case ElabAst.TypePattern.Type(term: ElabAst.Term.Pi) => out.parenthesized(printElabTypeTerm(term))
        case _                                               => pt(t)
      }

      pt(tp)
    }

    def printElabBinderType(bt: ElabAst.BinderType): Unit =
      bt match {
        case ElabAst.BinderType.TypePattern(tp, _) => printElabTypePattern(tp)
        case ElabAst.BinderType.ConstrainedCapture(ref, constraint, _) =>
          out += s"$$${ref.name} in "
          printElabTypePattern(constraint)
      }

    /** A binder as source writes it: `(x: T)`, or `[x: T]` for an instance binder. */
    def printElabBinder(b: ElabAst.Binder): Unit = {
      out += (if (b.isInstance) "[" else "(") + b.name + ": "
      printElabBinderType(b.ty)
      out += (if (b.isInstance) "]" else ")")
    }

    def printElabBinders(binders: Vector[ElabAst.Binder]): Unit = binders.foreach(printElabBinder)

    private def printElabLet(l: ElabAst.Let): Unit = {
      out += "let " + (if (l.isInstance) "instance " else "") + l.name
      l.ty.foreach { t =>
        out += ": "
        printElabTypeTerm(t)
      }
      out += " := "
      printElabTerm0(l.value)
    }

    private def printElabBody(b: ElabAst.Term.Body): Unit =
      if (b.lets.isEmpty) printElabTerm0(b.res)
      else {
        out += "{ "
        out.separated(b.lets, "\n")(printElabLet)
        out += " \n "
        printElabTerm0(b.res)
        out += " }"
      }

    def printElabTermAtom(t: ElabAst.Term): Unit = t match {
      case _: ElabAst.Term.Ref                  => printElabTerm0(t)
      case ElabAst.Term.App(_, _, _)            => printElabTerm0(t)
      case _: ElabAst.Term.Proj                 => printElabTerm0(t)
      case ElabAst.Term.NatLit(_, _)            => printElabTerm0(t)
      case ElabAst.Term.StrLit(_, _)            => printElabTerm0(t)
      case ElabAst.Term.Word(_, _, _)           => printElabTerm0(t)
      case _: ElabAst.Term.Lam                  => out.parenthesized(printElabTerm0(t))
      case ElabAst.Term.Match(_, _, _, _, _, _) => out.parenthesized(printElabTerm0(t))
      case ElabAst.Term.Body(_, _, _)           => out.parenthesized(printElabTerm0(t))
      case ElabAst.Term.Pi(_, _, _, _, _)       => out.parenthesized(printElabTerm0(t))
    }

    def printElabTerm0(t: ElabAst.Term): Unit = t match {
      case ElabAst.Term.Lam(ty, body, _, _, _, _, _) =>
        out += "fun "
        printElabBinders(ty.binders)
        out += ": "
        printElabTypeTerm(ty.out)
        out += " => "
        printElabTerm0(body)
      case m @ ElabAst.Term.Match(_, _, _, _, _, _) => printElabMatch(m)
      case b: ElabAst.Term.Body                     => printElabBody(b)
      case tt: ElabAst.TypeTerm                     => printElabTypeTerm(tt)
    }

    /**
     * A word as the nested applications it stands for, in a loop: each layer as its cons application around the rest,
     * and each splice before the end as `List.append` of it and the rest. A layer's arguments after the rest close it,
     * after the end, so they are kept until then.
     */
    private def printElabWord(word: ElabAst.Term.Word): Unit = {
      val closings = scala.collection.mutable.ArrayBuffer.empty[Vector[ElabAst.Term]]
      word.pieces.init.foreach {
        case ElabAst.Term.WordPiece.Layer(before, after) =>
          out += word.consHead.name + "("
          before.foreach { arg =>
            printElabTermAtom(arg)
            out += ", "
          }
          closings += after
        case ElabAst.Term.WordPiece.Splice(list) =>
          out += "List.append("
          printElabTermAtom(list)
          out += ", "
          closings += Vector.empty
      }
      printElabTermAtom(word.pieces.last.asInstanceOf[ElabAst.Term.WordPiece.Splice].list)
      closings.reverseIterator.foreach { after =>
        after.foreach { arg =>
          out += ", "
          printElabTermAtom(arg)
        }
        out += ")"
      }
    }

    def printElabTerm(t: ElabAst.Ast): Unit = t match {
      case term: ElabAst.Term             => printElabTerm0(term)
      case pattern: ElabAst.TypePattern   => printElabTypePattern(pattern)
      case binderType: ElabAst.BinderType => printElabBinderType(binderType)
    }

    private def printElabCase(c: ElabAst.Case): Unit = {
      val argNames = c.argRefs.map(_.map(_.name).getOrElse("_"))
      out += s"| ${c.ctorName}" + (if (argNames.isEmpty) "" else s" ${argNames.mkString(" ")}") + " => "
      printElabTerm0(c.body)
    }

    def printElabMatch(m: ElabAst.Term.Match): Unit = printElabMatchOn(m, printElabTermAtom(m.scrut))

    /** `m` with `scrut` printing its scrutinee: a stuck match's is its scrutinee's value (`Value.MatchId`). */
    def printElabMatchOn(m: ElabAst.Term.Match, scrut: => Unit): Unit = {
      out += "match " + m.cases.flatMap(_.equation).headOption.fold("")(ref => s"${ref.name} : ")
      scrut
      m.motive.foreach { motive =>
        out += " returning "
        printElabTypeTerm(motive)
      }
      out += " with "
      out.separated(m.cases, " ")(printElabCase)
    }
  }

  def printElabBinder(b: ElabAst.Binder): String = whole(out => new ElabPrinter(out, _ => false).printElabBinder(b))

  def printElabTerm(t: ElabAst.Ast): String = whole(out => new ElabPrinter(out, _ => false).printElabTerm(t))

  /**
   * A proof call's run failed while the program's result was printed (`printResult`): `cause`, which must reach the
   * caller rather than the shorter forms `print` falls back to. A control throwable, so no `NonFatal` handler on the
   * way catches it.
   */
  private final class ForcingFailed(val cause: Throwable) extends scala.util.control.ControlThrowable

  /**
   * Printing past an `Out`'s limit. A control throwable, so no `NonFatal` handler on the way catches it: the
   * `ValuePrinter.upTo` that set the limit does, or the call that made the `Out`.
   */
  private object Overflow extends scala.util.control.ControlThrowable

  /**
   * The text a printer prints, held to `limit` characters: an append that would pass the limit keeps at most one
   * character past it and throws `Overflow`, so printing a value costs at most the room left, however large the value
   * (docs/language.md, "Type mismatches"). Only `ValuePrinter.upTo` changes the limit; a part it keeps may end past the
   * limit around it, and then the next append throws.
   */
  private final class Out(var limit: Int) {
    val text = new java.lang.StringBuilder

    def length: Int = text.length

    def +=(piece: String): Unit = {
      val room = limit - text.length
      if (piece.length <= room) text.append(piece)
      else {
        if (room >= 0) text.append(piece, 0, room + 1)
        throw Overflow
      }
    }

    /** Each of `items`, printed by `item`, with `separator` between them. */
    def separated[A](items: Iterable[A], separator: String)(item: A => Unit): Unit = {
      var first = true
      items.foreach { a =>
        if (!first) this += separator
        first = false
        item(a)
      }
    }

    /** What `print` prints, in parentheses. */
    def parenthesized(print: => Unit): Unit = {
      this += "("
      print
      this += ")"
    }
  }

  /**
   * Values as source-like text, printed to `out`. A variable that `names` names prints by that name, as a binder of the
   * function type or lambda being printed does; any other prints with its id, `x#12`, so that distinct variables of one
   * name differ.
   *
   * A suspended proof prints as its forced value (docs/kernel.md, "Proof calls"), so printing runs the suspensions that
   * nothing ran before. With `result`, the value is a program's result: a run that fails is the program's failure, and
   * is thrown as `ForcingFailed`, or as itself for a stack overflow. Otherwise the value is part of a diagnostic, which
   * runs outside every evaluation boundary: a suspension whose run fails, even by exhausting the stack, prints as its
   * computation (`printSuspended`).
   */
  private final class ValuePrinter(names: Map[Value.VarId, String], result: Boolean, out: Out) {

    /** The suspensions of a diagnostic whose run failed, which are not run again: a failed run memoizes nothing. */
    private val failed = new java.util.IdentityHashMap[Value.VSuspendedProof, java.lang.Boolean]()

    /** The value `proof` prints as: its forced value, or, in a diagnostic whose run of it fails, `None`. */
    private def forced(proof: Value.VSuspendedProof): Option[Value] =
      if (result)
        try Some(Interpreter.force(proof))
        catch { case NonFatal(failure) => throw new ForcingFailed(failure) }
      else if (failed.containsKey(proof)) None
      else
        try Some(Interpreter.force(proof))
        catch {
          case NonFatal(_) | _: StackOverflowError =>
            failed.put(proof, java.lang.Boolean.TRUE)
            None
        }

    /**
     * What `print` prints, kept when it is at most `max` characters: their count; or, when it prints more, `None`, with
     * nothing kept. Printing stops one character past `max`, so it costs at most that, however large the value. A part
     * kept may end past the limit around it, which the next append checks.
     */
    private def upTo(max: Int)(print: => Unit): Option[Int] = {
      val mark = out.length
      val outer = out.limit
      out.limit = math.min(mark.toLong + max, Int.MaxValue.toLong).toInt
      try {
        print
        Some(out.length - mark)
      } catch {
        case Overflow =>
          out.text.setLength(mark)
          None
      } finally out.limit = outer
    }

    /** What `print` prints, within the limit, taken back out: an application's head, for `shape`. */
    private def captured(print: => Unit): String = {
      val mark = out.length
      print
      val text = out.text.substring(mark)
      out.text.setLength(mark)
      text
    }

    /**
     * A suspended proof as its computation: a call or an application as one, a record's projection as `base.field`, any
     * other match as its syntax.
     */
    private def printSuspended(proof: Value.VSuspendedProof): Unit =
      proof match {
        case call: Value.VProofCall => printApp(call.fn, call.args)
        case app: Value.VProofApply => printApp(app.fn, app.args)
        case m: Value.VProofMatch =>
          projection(m.term, m.scrut) match {
            case Some((base, field)) => printField(base, field)
            case None                => printMatchOn(m.term, m.env, m.scrut)
          }
      }

    private def printNatForm(poly: Value.VNatPoly): Unit = {
      val constant = poly.form.constant
      val terms = poly.form.terms
      // Ground values print as literals. Operands that are forms with terms print in parentheses, as in
      // `2 * a * (b + 1)^2 * x^(c + d) + b + 3`, and numeral bases in decimal, as in `2^n`.
      if (terms.isEmpty) out += constant.toString
      else {
        def operand(operand: Value): Unit =
          operand match {
            case poly: Value.VNatPoly if poly.form.terms.nonEmpty => out.parenthesized(printNatForm(poly))
            case other                                            => print(other)
          }
        def factor(factor: NatNormalForm.Factor): Unit =
          factor match {
            case power: NatNormalForm.NumeralPower =>
              operand(power.base)
              if (power.exponent != 1) out += s"^${power.exponent}"
            case power: NatNormalForm.SymbolicPower =>
              operand(power.base)
              out += "^"
              operand(power.exponent)
          }
        out.separated(terms, " + ") { term =>
          if (term.coefficient != 1) out += s"${term.coefficient} * "
          out.separated(term.monomial.factors, " * ")(factor)
        }
        if (constant != 0) out += s" + $constant"
      }
    }

    /** A value that prints as loose syntax, so it is parenthesized where an atom is expected. */
    private def isLoose(value: Value): Boolean =
      value match {
        // A failed run prints as its computation, which is loose syntax for a match that is no projection only.
        case proof: Value.VSuspendedProof =>
          forced(proof).fold(proof match {
            case m: Value.VProofMatch => projection(m.term, m.scrut).isEmpty
            case _                   => false
          })(isLoose)
        case _: Value.VPi                               => true
        case Value.VLam(_, _: Value.ValueId.LocalId, _) => true
        case thunk: Value.NeutralThunk                  => projection(thunk.term, thunk.id.scrut).isEmpty
        case _                                          => false
      }

    def printAtom(value: Value): Unit = if (isLoose(value)) out.parenthesized(print(value)) else print(value)

    private def printApp(head: Value, args: Seq[Value]): Unit = {
      appHead(head)
      out.parenthesized(out.separated(args, ", ")(print))
    }

    private def appHead(head: Value): Unit =
      head match {
        // A global function, such as a native stuck on its arguments, prints as its name.
        case Value.VLam(_, Value.ValueId.Const(name), _) => out += name
        case _                                           => printAtom(head)
      }

    /**
     * A word, in one loop over its tokens. A kernel `List` word prints as its elements in brackets, followed by `++`
     * and its end unless that is `nil`, such as `[a, b] ++ xs`. A word of a user list-shaped type prints as nested
     * constructor applications, as for any constructor, ending in its terminator: each layer's fields after its
     * recursive one close it, after the terminator, so they are kept until then.
     */
    private def printWord(word: Value.VWord): Unit = {
      var listed = false
      val closings = scala.collection.mutable.ArrayBuffer.empty[IndexedSeq[Value]]
      var end: Value = null
      packed.Words.foreach(word)(
        layer = token => {
          if (token.head.name == Kernel.ListConsName) {
            out += (if (listed) ", " else "[")
            listed = true
            print(token.payload(0))
          } else {
            val recursive = token.recursiveIndex
            out += token.head.name + "("
            (0 until recursive).foreach { index =>
              print(token.payload(index))
              out += ", "
            }
            closings += (recursive until token.payloadWidth).map(token.payload)
          }
          true
        },
        end = token => {
          end = token.value
          true
        }
      )
      // Only a user type's layers have closings, and only a kernel `List` 's have elements.
      if (closings.nonEmpty) {
        print(end)
        closings.reverseIterator.foreach { after =>
          after.foreach { field =>
            out += ", "
            print(field)
          }
          out += ")"
        }
      } else {
        out += (if (listed) "]" else "[]")
        if (!Kernel.isListNil(end)) {
          out += " ++ "
          print(end)
        }
      }
    }

    /**
     * A level as source syntax, `Level.succ` and `Level.max` over `Level.zero`, `Level.one` and its variables, not its
     * normalized `max(atom+k, …, c)` form.
     */
    def printLevel(level: Value.Level): String = {
      def succs(base: String, offset: Int): String =
        if (offset == 0) base else s"Level.succ(${succs(base, offset - 1)})"
      val atoms =
        level.atoms.toVector.sortBy(_._1).map { case (id, offset) => succs(names.getOrElse(id, s"u#$id"), offset) }
      val constant = if (level.c == 0) "Level.zero" else succs("Level.one", level.c - 1)
      val parts = if (level.c > 0 || atoms.isEmpty) atoms :+ constant else atoms
      parts.reduceRight((part, rest) => s"Level.max($part, $rest)")
    }

    /** `Kind.copy`, `Kind.lin`, or the join of its variables, in id order. */
    def printKind(kind: Value.Kind): String =
      if (kind.lin) "Kind.lin"
      else if (kind.vars.isEmpty) "Kind.copy"
      else kind.vars.toVector.sorted.map(id => names.getOrElse(id, s"k#$id")).reduceLeft((a, b) => s"Kind.join($a, $b)")

    /** The variable ids of `values`, which an opened telescope binds, with the names their binders give them. */
    private def boundNames(opened: Iterable[(String, Value)]): Map[Value.VarId, String] =
      opened.collect { case (name, Value.Var(_, id, _)) if name != "_" => id -> name }.toMap

    /** Syntax printed under `env`: a local it binds prints as its value, in place. */
    private def underEnv(env: Env): ElabPrinter =
      new ElabPrinter(
        out,
        ref =>
          ref.id < env.locals.length && env.locals(ref.id).valueOption.exists { value =>
            printAtom(value)
            true
          }
      )

    /**
     * A function type, `(x: A) -> (y: B) -> C`, its binders opened on fresh variables named by them. Binder types print
     * as written, captures included, with the type's captured locals as their values; a codomain that is itself a
     * function type is parenthesized, so the binders of one type are told from the next.
     */
    private def printPi(pi: Value.VPi): Unit =
      piText(pi, (inner, codomain) => inner.print(codomain))

    /** `printPi`, with the codomain, opened on the binders' fresh variables, as `codomain` prints it with `inner`. */
    private def piText(pi: Value.VPi, codomain: (ValuePrinter, Value) => Unit): Unit = {
      val fresh = telescope.BinderOps.freshen(pi)
      val opened = pi.binders.flatMap(b => b.captures.map(_.localRef) :+ b.localRef).map(ref => ref.name -> fresh(ref))
      // Opened on fresh variables, the type's parts are no part of a result's value: they print as a diagnostic's do.
      val inner = new ValuePrinter(names ++ boundNames(opened), result = false, out)
      val syntax = underEnv(pi.env)
      pi.binders.foreach { binder =>
        binder.ty match {
          case ElabAst.BinderType.TypePattern(ElabAst.TypePattern.Type(_), _)
              if binder.name == "_" && !binder.isInstance =>
            inner.printAtom(fresh(binder.localRef).tpe)
          case _ => syntax.printElabBinder(toBinder(binder))
        }
        out += " -> "
      }
      pi.codomain(fresh) match {
        case nested: Value.VPi => out.parenthesized(codomain(inner, nested))
        case other             => codomain(inner, other)
      }
    }

    /** How `print` shows `value` (`Mismatch.Shape`): the parts it prints, each printed by `print`. */
    def shape(value: Value): Mismatch.Shape =
      value match {
        case proof: Value.VSuspendedProof => forced(proof).fold[Mismatch.Shape](Mismatch.Shape.Whole)(shape)
        case packed.Strings.Literal(_)    => Mismatch.Shape.Whole
        case nil if Kernel.isListNil(nil) => Mismatch.Shape.ListOf(Vector.empty, nil, Vector.empty)
        case word: Value.VWord =>
          val elements = Vector.newBuilder[Value]
          val rests = Vector.newBuilder[Value]
          var end: Value = null
          val kernelList = packed.Words.foreach(word)(
            layer = token =>
              token.head.name == Kernel.ListConsName && {
                elements += token.payload(0)
                rests += token.rest
                true
              },
            end = token => { end = token.value; true }
          )
          if (kernelList) Mismatch.Shape.ListOf(elements.result(), end, rests.result()) else Mismatch.Shape.Whole
        case Value.VCtor(head, fields, _) if head.name != Kernel.ZeroName && fields.nonEmpty =>
          Mismatch.Shape.App(head.name, fields)
        // The head as text, within the limit: past it, printing the shape overflows.
        case v: Value.VApp => Mismatch.Shape.App(captured(appHead(v.head)), v.args)
        case pi: Value.VPi => Mismatch.Shape.Fun(pi)
        case lam @ Value.VLam(_, _: Value.ValueId.LocalId, _: Value.LamBody.Core) => Mismatch.Shape.Lam(lam)
        case thunk: Value.NeutralThunk =>
          projection(thunk.term, thunk.id.scrut)
            .map { case (base, field) => Mismatch.Shape.Field(base, field) }
            .getOrElse(Mismatch.Shape.Whole)
        case _ => Mismatch.Shape.Whole
      }

    /**
     * `value` printed along `path`, as `print` prints it, except that each part off the path that prints longer than
     * `bounds.part` characters prints as `…` and its length (`briefly`), a list shows at most three elements before the
     * one on the path, and none after it, with `…` and how many it leaves out, and the part the path ends at prints in
     * `outline` when it is longer than `bounds.whole` characters.
     */
    def focused(value: Value, path: List[Mismatch.Step], bounds: Mismatch.Bounds): Unit =
      (path, shape(value)) match {
        case (Mismatch.Step.Arg(i) :: rest, Mismatch.Shape.App(head, args)) if i < args.length =>
          out += head
          out.parenthesized(out.separated(args.indices, ", ") { j =>
            if (j == i) focused(args(j), rest, bounds) else briefly(args(j), bounds)
          })
        case (Mismatch.Step.Elem(i) :: rest, Mismatch.Shape.ListOf(elements, end, _)) if i < elements.length =>
          out += "["
          lastThree(elements.take(i), bounds)
          if (i > 0) out += ", "
          focused(elements(i), rest, bounds)
          if (i + 1 < elements.length) out += ", " + bounds.omitted(elements.length - i - 1)
          out += "]"
          if (!Kernel.isListNil(end)) {
            out += " ++ "
            briefly(end, bounds)
          }
        case (Mismatch.Step.End :: rest, Mismatch.Shape.ListOf(elements, end, _)) =>
          out += "["
          lastThree(elements, bounds)
          out += "] ++ "
          focused(end, rest, bounds)
        // A list's shared elements, then what follows them, as an append of the two.
        case (Mismatch.Step.Rest(count) :: rest, list: Mismatch.Shape.ListOf) if count <= list.elements.length =>
          out += "["
          lastThree(list.elements.take(count), bounds)
          out += "] ++ "
          focused(list.after(count), rest, bounds)
        case (Mismatch.Step.Codomain :: rest, Mismatch.Shape.Fun(pi)) =>
          piText(pi, (inner, codomain) => inner.focused(codomain, rest, bounds))
        case (Mismatch.Step.Body :: rest, Mismatch.Shape.Lam(lam)) =>
          lamText(lam, (inner, body) => inner.focused(body, rest, bounds))
        case (Mismatch.Step.Base :: rest, Mismatch.Shape.Field(base, field)) =>
          if (isLoose(base)) out.parenthesized(focused(base, rest, bounds)) else focused(base, rest, bounds)
          out += "." + field
        case (Nil, _) => if (upTo(bounds.whole)(print(value)).isEmpty) outline(value, bounds)
        case _        => print(value)
      }

    /** The last three of `elements`, `briefly`, after `…` and how many it leaves out when there are more. */
    private def lastThree(elements: Vector[Value], bounds: Mismatch.Bounds): Unit = {
      val left = math.max(0, elements.length - 3)
      if (left > 0) out += bounds.omitted(left) + ", "
      out.separated(elements.drop(left), ", ")(briefly(_, bounds))
    }

    /**
     * `value` printed; or, when that is longer than `bounds.part` characters, `…` and its length, counted up to
     * `bounds.measure`, so an elided part costs at most that.
     */
    private def briefly(value: Value, bounds: Mismatch.Bounds): Unit = {
      val mark = out.length
      upTo(bounds.measure)(print(value)) match {
        case Some(length) if length <= bounds.part => ()
        case length =>
          out.text.setLength(mark)
          out += bounds.elided(length)
      }
    }

    /**
     * `value` as `print` shows it, except that each of its parts that prints longer than `bounds.part` characters
     * prints as `…` and its length (`briefly`): an application's arguments, a list's elements, after its first three,
     * and its end, and a projection's base in outline.
     */
    def outline(value: Value, bounds: Mismatch.Bounds): Unit =
      shape(value) match {
        case Mismatch.Shape.App(head, args) =>
          out += head
          out.parenthesized(out.separated(args, ", ")(briefly(_, bounds)))
        case Mismatch.Shape.ListOf(elements, end, _) =>
          out += "["
          out.separated(elements.take(3), ", ")(briefly(_, bounds))
          if (elements.length > 3) out += ", " + bounds.omitted(elements.length - 3)
          out += "]"
          if (!Kernel.isListNil(end)) {
            out += " ++ "
            briefly(end, bounds)
          }
        case Mismatch.Shape.Field(base, field) =>
          if (isLoose(base)) out.parenthesized(outline(base, bounds)) else outline(base, bounds)
          out += "." + field
        case _ => print(value)
      }

    /** A global function by its name; a local lambda as its binders and its body opened on them. */
    private def printLam(lam: Value.VLam): Unit =
      lam.id match {
        case Value.ValueId.Const(name) => out += name
        case _: Value.ValueId.LocalId  => lamText(lam, (inner, body) => inner.print(body))
      }

    /** A local lambda as `printLam` prints it, with its body, run on its binders' fresh variables, as `body` prints it. */
    private def lamText(lam: Value.VLam, body: (ValuePrinter, Value) => Unit): Unit = {
      val fresh = telescope.BinderOps.freshen(lam.tpe)
      val opened =
        lam.tpe.binders.flatMap(b => b.captures.map(_.localRef) :+ b.localRef).map(ref => ref.name -> fresh(ref))
      // Opened on fresh variables, the body is no part of a result's value: it prints as a diagnostic's does.
      val inner = new ValuePrinter(names ++ boundNames(opened), result = false, out)
      val run = Interpreter.runLam(lam, lam.tpe.binders.map(b => fresh(b.localRef)))
      out += "fun "
      underEnv(lam.tpe.env).printElabBinders(lam.tpe.binders.map(toBinder))
      out += " => "
      body(inner, run)
    }

    private def toBinder(b: Value.VBinder): ElabAst.Binder =
      ElabAst.Binder(b.localRef, b.ty, Span(0, 0), b.isInstance)

    /**
     * The match `term` on `base` as a named record field's canonical projection (`StructEta.Projection.of`): its base
     * and field, which print as `base.field`. An anonymous field's prints as the stuck match it is.
     */
    private def projection(term: ElabAst.Term.Match, base: Value): Option[(Value, String)] =
      StructEta.Projection.of(term, base).collect {
        case (base, _, info, idx) if info.fieldNames(idx) != "_" => (base, info.fieldNames(idx))
      }

    private def printField(base: Value, field: String): Unit = {
      printAtom(base)
      out += "." + field
    }

    /**
     * The match `term` on `scrut`, its scrutinee's value, as its syntax under `env`, with `scrut` as its scrutinee:
     * `env` need not hold the scrutinee term's locals (`Value.NeutralThunk`).
     */
    private def printMatchOn(term: ElabAst.Term.Match, env: Env, scrut: Value): Unit =
      underEnv(env).printElabMatchOn(term, printAtom(scrut))

    /** A stuck match: a record's projection as `base.field`, any other as its syntax on its scrutinee's value. */
    private def printThunk(thunk: Value.NeutralThunk): Unit =
      projection(thunk.term, thunk.id.scrut) match {
        case Some((base, field)) => printField(base, field)
        case None                => printMatchOn(thunk.term, thunk.env, thunk.id.scrut)
      }

    def print(value: Value): Unit = value match {
      // Printed as its forced value, which eager evaluation printed (docs/kernel.md, "Proof calls"), or as itself.
      case proof: Value.VSuspendedProof =>
        forced(proof) match {
          case Some(forcedValue) => print(forcedValue)
          case None              => printSuspended(proof)
        }
      case packed.Strings.Literal(text)                => out += UnicodeScalarString.renderQuoted(text)
      case nil if Kernel.isListNil(nil)                => out += "[]"
      case word: Value.VWord                           => printWord(word)
      case Value.PropTpe                               => out += "Prop"
      case Value.VSort(lvl) if lvl == Value.Level.zero => out += "Type"
      case Value.VSort(lvl)                            => out += s"Sort(${printLevel(lvl)})"
      case Value.VLin(lvl)                             => out += s"Lin(${printLevel(lvl)})"
      case Value.VUniv(kind, lvl)                      => out += s"Univ(${printKind(kind)}, ${printLevel(lvl)})"
      case Value.KernelObject                          => out += "KernelObject"
      case level: Value.Level                          => out += printLevel(level)
      case kind: Value.Kind                            => out += printKind(kind)
      case pi: Value.VPi                               => printPi(pi)
      case Value.VConst(name, _, _)                    => out += name
      case Value.ConstructorHead(name, _, _, _, _)     => out += name
      case Value.VCtor(head, fields, _) =>
        if (head.name == Kernel.ZeroName) out += "0" // as every other ground Nat prints as a literal
        else {
          print(head)
          if (fields.nonEmpty) out.parenthesized(out.separated(fields, ", ")(print))
        }
      case poly: Value.VNatPoly   => printNatForm(poly)
      case v: Value.VApp          => printApp(v.head, v.args)
      case v: Value.VLam          => printLam(v)
      case Value.Var(name, id, _) => out += names.getOrElse(id, s"$name#$id")
      case s: Value.NeutralThunk  => printThunk(s)
      case LevelTpe               => out += "Level"
      case Value.KindTpe          => out += "Kind"
    }
  }

  /**
   * A value as source-like text. A `String.mk` whose list ends in `nil` and holds only closed scalar characters prints
   * as a literal; any other string prints as its constructor applied to its list. A function type prints as one, a
   * record's projection as `base.field`, and a stuck match as its syntax. Printing never fails: a value whose binders
   * or body cannot be opened prints in a shorter form, and a suspended proof whose run fails prints as its computation.
   * The text is whole, however long: a diagnostic prints a value within bounds (`printWithin`, `printClipped`).
   */
  def print(value: Value): String = printWith(value, result = false)

  /**
   * How `print` shows `value`, for `Mismatch`: an application only when its head prints within `head` characters, and
   * whole otherwise.
   */
  def shapeOf(value: Value, head: Int): Mismatch.Shape =
    try diagnostic(new Out(head)).shape(value)
    catch { case Overflow => Mismatch.Shape.Whole }

  /** `value` as `print` shows it, when that is at most `max` characters; printing it costs at most that. */
  def printWithin(value: Value, max: Int): Option[String] =
    within(max, Some(unprintable(value)))(diagnostic(_).print(value))

  /** `value` as `print` shows it, parenthesized where an atom is expected, when that is at most `max` characters. */
  def printAtomWithin(value: Value, max: Int): Option[String] =
    within(max, Some(s"(${unprintable(value)})"))(diagnostic(_).printAtom(value))

  /** `value` as `print` shows it, clipped (`clipped`). */
  def printClipped(value: Value, bounds: Mismatch.Bounds): String =
    clipped(bounds, unprintable(value))(diagnostic(_).print(value))

  /** `value` as `print` shows it along `path` to a part, other parts abbreviated (`Mismatch`), clipped. */
  def printFocused(value: Value, path: List[Mismatch.Step], bounds: Mismatch.Bounds): String =
    clipped(bounds, printClipped(value, bounds))(diagnostic(_).focused(value, path, bounds))

  /** `value` as `print` shows it with its long parts abbreviated (`Mismatch`), clipped. */
  def printOutline(value: Value, bounds: Mismatch.Bounds): String =
    clipped(bounds, printClipped(value, bounds))(diagnostic(_).outline(value, bounds))

  /** Checked syntax as `printElabTerm` prints it, clipped (`clipped`): syntax quoted from a value may be as large. */
  def printElabClipped(t: ElabAst.Ast, bounds: Mismatch.Bounds): String =
    clipped(bounds, "<syntax>")(new ElabPrinter(_, _ => false).printElabTerm(t))

  /** A diagnostic's printer: a value is part of a diagnostic, not a program's result (`ValuePrinter`). */
  private def diagnostic(out: Out): ValuePrinter = new ValuePrinter(Map.empty, result = false, out)

  /** What `print` prints, whole, however long. */
  private def whole(print: Out => Unit): String = {
    val out = new Out(Int.MaxValue)
    print(out)
    out.text.toString
  }

  /**
   * What `print` prints, when at most `max` characters, or `failed`, when within `max`, if printing fails; it costs at
   * most `max` characters.
   */
  private def within(max: Int, failed: => Option[String])(print: Out => Unit): Option[String] = {
    val out = new Out(max)
    try {
      print(out)
      Option.when(out.length <= max)(out.text.toString)
    } catch {
      case Overflow                              => None
      case NonFatal(_) | _: StackOverflowError => failed.filter(_.length <= max)
    }
  }

  /**
   * What `print` prints, up to `bounds.cap` characters; past that, its first `bounds.cap` characters and `…` with how
   * many it leaves out, counted up to `bounds.measure`. So it costs at most `bounds.cap` and `bounds.measure`
   * characters, however large what it prints. `failed` when printing fails.
   */
  private def clipped(bounds: Mismatch.Bounds, failed: => String)(print: Out => Unit): String = {
    val out = new Out(math.min(bounds.cap.toLong + bounds.measure, Int.MaxValue.toLong).toInt)
    val counted =
      try {
        print(out)
        Some(out.length <= out.limit)
      } catch {
        case Overflow                              => Some(false)
        case NonFatal(_) | _: StackOverflowError => None
      }
    counted match {
      case None                                   => failed
      case Some(true) if out.length <= bounds.cap => out.text.toString
      case Some(complete) =>
        out.text.substring(0, bounds.cap) + bounds.elided(Option.when(complete)(out.length - bounds.cap))
    }
  }

  /** A binder's type as written, a local that `bound` names printing as the text it gives, and any other by name. */
  def printBinderType(ty: ElabAst.BinderType, bound: CoreAst.LocalRef => Option[String]): String =
    whole { out =>
      new ElabPrinter(out, ref => bound(ref).exists { text => out += text; true }).printElabBinderType(ty)
    }

  /**
   * A program's result as `print` shows it, except that a proof call whose run fails is the program's failure: its
   * error is thrown, as is a stack overflow, which `Interpreter.show` reports at the body.
   */
  def printResult(value: Value): String =
    try printWith(value, result = true)
    catch { case failed: ForcingFailed => throw failed.cause }

  private def printWith(value: Value, result: Boolean): String =
    try whole(new ValuePrinter(Map.empty, result, _).print(value))
    catch { case NonFatal(_) => unprintable(value) }

  /** What a value prints as when printing it fails. */
  private def unprintable(value: Value): String =
    value match {
      case _: Value.VPi          => "<function type>"
      case lam: Value.VLam       => s"<function ${lam.id}>"
      case _: Value.NeutralThunk => "<stuck match>"
      case other                 => other.getClass.getSimpleName
    }
}
