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

  private def printTermAtom(t: CoreAst.Term): String = t match {
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
  }

  private def printCoreTerm(t: CoreAst.Term): String = t match {
    case CoreAst.Term.Lam(ty, _, body, _, _, recursion, _) =>
      val decreaseStr = recursion.map(r => s" ${printDecreaseSpec(r.decreases)}").getOrElse("")
      s"fun ${printBinders(ty.binders)}: ${printTypeTerm(ty.out)}$decreaseStr => ${printCoreTerm(body)}"
    case m: CoreAst.Term.Match                       => printMatch(m)
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
    val casesStr = (m.cases.map(printCase) ++ m.wildcard.map(w => s"| _ => ${printCoreTerm(w.body)}")).mkString(" ")
    val equationStr = (m.cases.flatMap(_.equation) ++ m.wildcard.flatMap(_.equation)).headOption
      .fold("")(ref => s"${ref.name} : ")
    s"match $equationStr$scrutStr$motiveStr with $casesStr"
  }

  private def printMatchOne(m: CoreAst.Term.MatchOne): String = {
    val fields = m.fieldRefs.map(_.name).mkString(", ")
    val motiveStr = m.motive.map(motive => s" returning ${printTypeTerm(motive)}").getOrElse("")
    s"matchOne ${printTermAtom(m.scrut)}$motiveStr with ($fields) => ${printCoreTerm(m.body)}"
  }

  /**
   * Checked syntax as source. A local that `bound` binds prints as the text it gives, such as a closure's captured
   * value, and any other local by its binder's name.
   */
  private final class ElabPrinter(bound: CoreAst.LocalRef => Option[String]) {
    private def printElabRef(ref: ElabAst.Term.Ref): String = ref match {
      case ElabAst.Term.GlobalRef(name, _) => name
      case ElabAst.Term.LocalRef(ref, _)   => bound(ref).getOrElse(ref.name)
    }

    def printElabTypeTerm(tt: ElabAst.TypeTerm): String = {
      import com.raccoonlang.ElabAst.Term

      def pt(t: ElabAst.TypeTerm): String = t match {
        case ref: Term.Ref => printElabRef(ref)
        case Term.App(fn, args, _) =>
          val headStr = printElabTermAtom(fn)
          val argsStr = args.map(printElabTermAtom).mkString(", ")
          s"$headStr($argsStr)"
        // As written explicitly, which takes a base of any form, and reads back as the same projection.
        case Term.Proj(base, family, field, _, _) => s"$family.$field(${printElabTermAtom(base)})"
        case Term.NatLit(number, _)               => number.toString
        case Term.StrLit(text, _)                 => UnicodeScalarString.renderQuoted(text)
        case word: Term.Word                      => printElabWord(word)
        case lam: Term.Lam                        => printElabTerm0(lam)
        case Term.Pi(binders, out, _, _, _) =>
          val bindersStr = binders
            .map(printElabPiBinder)
            .mkString(" -> ")
          s"$bindersStr -> ${pt(out)}"
      }

      def ptAtom(t: ElabAst.TypeTerm): String = t match {
        case _: Term.Ref            => pt(t)
        case Term.App(_, _, _)      => pt(t)
        case _: Term.Proj           => pt(t)
        case Term.NatLit(_, _)      => pt(t)
        case Term.StrLit(_, _)      => pt(t)
        case _: Term.Word           => pt(t)
        case Term.Pi(_, _, _, _, _) => s"(${pt(t)})"
        case _: Term.Lam            => s"(${pt(t)})"
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
        case ElabAst.TypePattern.Capture(ref, _, constraint) =>
          s"$$${ref.name}" + constraint.fold("")(c => s" in ${pt(c)}")
      }

      def ptAtom(t: ElabAst.TypePattern): String = t match {
        case ElabAst.TypePattern.Type(term: ElabAst.Term.Pi) => s"(${printElabTypeTerm(term)})"
        case _                                               => pt(t)
      }

      pt(tp)
    }

    def printElabBinderType(bt: ElabAst.BinderType): String =
      bt match {
        case ElabAst.BinderType.TypePattern(tp, _) => printElabTypePattern(tp)
        case ElabAst.BinderType.ConstrainedCapture(ref, constraint, _) =>
          s"$$${ref.name} in ${printElabTypePattern(constraint)}"
      }

    /** A binder as source writes it: `(x: T)`, or `[x: T]` for an instance binder. */
    def printElabBinder(b: ElabAst.Binder): String = {
      val body = s"${b.name}: ${printElabBinderType(b.ty)}"
      if (b.isInstance) s"[$body]" else s"($body)"
    }

    def printElabBinders(binders: Vector[ElabAst.Binder]): String =
      binders.map(printElabBinder).mkString

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

    def printElabTermAtom(t: ElabAst.Term): String = t match {
      case _: ElabAst.Term.Ref                  => printElabTerm0(t)
      case ElabAst.Term.App(_, _, _)            => printElabTerm0(t)
      case _: ElabAst.Term.Proj                 => printElabTerm0(t)
      case ElabAst.Term.NatLit(_, _)            => printElabTerm0(t)
      case ElabAst.Term.StrLit(_, _)            => printElabTerm0(t)
      case ElabAst.Term.Word(_, _, _)           => printElabTerm0(t)
      case _: ElabAst.Term.Lam                  => s"(${printElabTerm0(t)})"
      case ElabAst.Term.Match(_, _, _, _, _, _) => s"(${printElabTerm0(t)})"
      case ElabAst.Term.Body(_, _, _)           => s"(${printElabTerm0(t)})"
      case ElabAst.Term.Pi(_, _, _, _, _)       => s"(${printElabTerm0(t)})"
    }

    def printElabTerm0(t: ElabAst.Term): String = t match {
      case ElabAst.Term.Lam(ty, body, _, _, _, _, _) =>
        s"fun ${printElabBinders(ty.binders)}: ${printElabTypeTerm(ty.out)} => ${printElabTerm0(body)}"
      case m @ ElabAst.Term.Match(_, _, _, _, _, _) => printElabMatch(m)
      case b: ElabAst.Term.Body                     => printElabBody(b)
      case tt: ElabAst.TypeTerm                     => printElabTypeTerm(tt)
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

    def printElabMatch(m: ElabAst.Term.Match): String = {
      val scrutStr = printElabTermAtom(m.scrut)
      val motiveStr = m.motive.map(motive => s" returning ${printElabTypeTerm(motive)}").getOrElse("")
      val casesStr = m.cases.map(printElabCase).mkString(" ")
      val equationStr = m.cases.flatMap(_.equation).headOption.fold("")(ref => s"${ref.name} : ")
      s"match $equationStr$scrutStr$motiveStr with $casesStr"
    }
  }

  private val unboundSyntax = new ElabPrinter(_ => None)

  def printElabBinder(b: ElabAst.Binder): String = unboundSyntax.printElabBinder(b)

  def printElabTerm(t: ElabAst.Ast): String = unboundSyntax.printElabTerm(t)

  /**
   * A proof call's run failed while the program's result was printed (`printResult`): `cause`, which must reach the
   * caller rather than the shorter forms `print` falls back to. A control throwable, so no `NonFatal` handler on the
   * way catches it.
   */
  private final class ForcingFailed(val cause: Throwable) extends scala.util.control.ControlThrowable

  /**
   * Values as source-like text. A variable that `names` names prints by that name, as a binder of the function type or
   * lambda being printed does; any other prints with its id, `x#12`, so that distinct variables of one name differ.
   *
   * A suspended proof prints as its forced value (docs/kernel.md, "Proof calls"), so printing runs the suspensions that
   * nothing ran before. With `result`, the value is a program's result: a run that fails is the program's failure, and
   * is thrown as `ForcingFailed`, or as itself for a stack overflow. Otherwise the value is part of a diagnostic, which
   * runs outside every evaluation boundary: a suspension whose run fails, even by exhausting the stack, prints as its
   * computation (`printSuspended`).
   */
  private final class ValuePrinter(names: Map[Value.VarId, String], result: Boolean) {

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
     * A suspended proof as its computation: a call or an application as one, a record's projection as `base.field`, any
     * other match as its syntax.
     */
    private def printSuspended(proof: Value.VSuspendedProof): String =
      proof match {
        case call: Value.VProofCall => printApp(call.fn, call.args)
        case app: Value.VProofApply => printApp(app.fn, app.args)
        case m: Value.VProofMatch   => projection(m.term, m.env).getOrElse(underEnv(m.env).printElabMatch(m.term))
      }

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

    /** A value that prints as loose syntax, so it is parenthesized where an atom is expected. */
    private def isLoose(value: Value): Boolean =
      value match {
        // A failed run prints as its computation, which is loose syntax for a match that is no projection only.
        case proof: Value.VSuspendedProof =>
          forced(proof).fold(proof match {
            case m: Value.VProofMatch => projection(m.term, m.env).isEmpty
            case _                    => false
          })(isLoose)
        case _: Value.VPi                               => true
        case Value.VLam(_, _: Value.ValueId.LocalId, _) => true
        case thunk: Value.NeutralThunk                  => projection(thunk).isEmpty
        case _                                          => false
      }

    def printAtom(value: Value): String = if (isLoose(value)) s"(${print(value)})" else print(value)

    private def printApp(head: Value, args: Seq[Value]): String = {
      val headStr = head match {
        // A global function, such as a native stuck on its arguments, prints as its name.
        case Value.VLam(_, Value.ValueId.Const(name), _) => name
        case _                                           => printAtom(head)
      }
      val argsStr = args.toList.map(print).mkString(", ")
      s"$headStr($argsStr)"
    }

    /**
     * A word, in one loop over its tokens. A kernel `List` word prints as its elements in brackets, followed by `++`
     * and its end unless that is `nil`, such as `[a, b] ++ xs`. A word of a user list-shaped type prints as nested
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

    /** `syntax` printed under `env`: a local it binds prints as its value. */
    private def underEnv(env: Env): ElabPrinter =
      new ElabPrinter(ref =>
        if (ref.id < env.locals.length) env.locals(ref.id).valueOption.map(printAtom)
        else None
      )

    /**
     * A function type, `(x: A) -> (y: B) -> C`, its binders opened on fresh variables named by them. Binder types print
     * as written, captures included, with the type's captured locals as their values; a codomain that is itself a
     * function type is parenthesized, so the binders of one type are told from the next.
     */
    private def printPi(pi: Value.VPi): String = {
      val fresh = telescope.BinderOps.freshen(pi)
      val opened = pi.binders.flatMap(b => b.captures.map(_.localRef) :+ b.localRef).map(ref => ref.name -> fresh(ref))
      // Opened on fresh variables, the type's parts are no part of a result's value: they print as a diagnostic's do.
      val inner = new ValuePrinter(names ++ boundNames(opened), result = false)
      val syntax = underEnv(pi.env)
      val binders = pi.binders.map { binder =>
        binder.ty match {
          case ElabAst.BinderType.TypePattern(ElabAst.TypePattern.Type(_), _)
              if binder.name == "_" && !binder.isInstance =>
            inner.printAtom(fresh(binder.localRef).tpe)
          case ty =>
            val text = s"${binder.name}: ${syntax.printElabBinderType(ty)}"
            if (binder.isInstance) s"[$text]" else s"($text)"
        }
      }
      val out = pi.codomain(fresh)
      val outText = out match {
        case _: Value.VPi => s"(${inner.print(out)})"
        case _            => inner.print(out)
      }
      (binders :+ outText).mkString(" -> ")
    }

    /** A global function by its name; a local lambda as its binders and its body opened on them. */
    private def printLam(lam: Value.VLam): String =
      lam.id match {
        case Value.ValueId.Const(name) => name
        case _: Value.ValueId.LocalId =>
          val fresh = telescope.BinderOps.freshen(lam.tpe)
          val opened =
            lam.tpe.binders.flatMap(b => b.captures.map(_.localRef) :+ b.localRef).map(ref => ref.name -> fresh(ref))
          // Opened on fresh variables, the body is no part of a result's value: it prints as a diagnostic's does.
          val inner = new ValuePrinter(names ++ boundNames(opened), result = false)
          val body = Interpreter.runLam(lam, lam.tpe.binders.map(b => fresh(b.localRef)))
          s"fun ${underEnv(lam.tpe.env).printElabBinders(lam.tpe.binders.map(toBinder))} => ${inner.print(body)}"
      }

    private def toBinder(b: Value.VBinder): ElabAst.Binder =
      ElabAst.Binder(b.localRef, b.ty, Span(0, 0), b.isInstance)

    /**
     * A named record field's canonical projection (`StructEta.Projection`), as `base.field`. An anonymous field's
     * prints as the stuck match it is.
     */
    def projection(thunk: Value.NeutralThunk): Option[String] = projection(thunk.term, thunk.env)

    /** The match `term` in `env` as `base.field`, when it is a named field's projector (`StructEta.Projection.of`). */
    private def projection(term: ElabAst.Term.Match, env: Env): Option[String] =
      StructEta.Projection.of(term, env).collect {
        case (base, _, info, idx) if info.fieldNames(idx) != "_" => s"${printAtom(base)}.${info.fieldNames(idx)}"
      }

    /** A stuck match: a record's projection as `base.field`, any other as its syntax under its environment. */
    private def printThunk(thunk: Value.NeutralThunk): String =
      projection(thunk).getOrElse(underEnv(thunk.env).printElabMatch(thunk.term))

    def print(value: Value): String = value match {
      // Printed as its forced value, which eager evaluation printed (docs/kernel.md, "Proof calls"), or as itself.
      case proof: Value.VSuspendedProof                => forced(proof).fold(printSuspended(proof))(print)
      case packed.Strings.Literal(text)                => UnicodeScalarString.renderQuoted(text)
      case nil if Kernel.isListNil(nil)                => "[]"
      case word: Value.VWord                           => printWord(word)
      case Value.PropTpe                               => "Prop"
      case Value.VSort(lvl) if lvl == Value.Level.zero => "Type"
      case Value.VSort(lvl)                            => s"Sort(${printLevel(lvl)})"
      case Value.VLin(lvl)                             => s"Lin(${printLevel(lvl)})"
      case Value.VUniv(kind, lvl)                      => s"Univ(${printKind(kind)}, ${printLevel(lvl)})"
      case Value.KernelObject                          => "KernelObject"
      case level: Value.Level                          => printLevel(level)
      case kind: Value.Kind                            => printKind(kind)
      case pi: Value.VPi                               => printPi(pi)
      case Value.VConst(name, _, _)                    => name
      case Value.ConstructorHead(name, _, _, _, _)     => name
      case Value.VCtor(head, fields, _) =>
        val headStr = print(head)
        if (head.name == Kernel.ZeroName) "0" // as every other ground Nat prints as a literal
        else if (fields.isEmpty) headStr
        else s"$headStr(${fields.map(print).mkString(", ")})"
      case poly: Value.VNatPoly   => printNatForm(poly)
      case v: Value.VApp          => printApp(v.head, v.args)
      case v: Value.VLam          => printLam(v)
      case Value.Var(name, id, _) => names.getOrElse(id, s"$name#$id")
      case s: Value.NeutralThunk  => printThunk(s)
      case LevelTpe               => s"Level"
      case Value.KindTpe          => "Kind"
    }
  }

  /**
   * A value as source-like text. A `String.mk` whose list ends in `nil` and holds only closed scalar characters prints
   * as a literal; any other string prints as its constructor applied to its list. A function type prints as one, a
   * record's projection as `base.field`, and a stuck match as its syntax. Printing never fails: a value whose binders
   * or body cannot be opened prints in a shorter form, and a suspended proof whose run fails prints as its computation.
   * This is how a diagnostic shows a value.
   */
  def print(value: Value): String = printWith(value, result = false)

  /**
   * A program's result as `print` shows it, except that a proof call whose run fails is the program's failure: its
   * error is thrown, as is a stack overflow, which `Interpreter.show` reports at the body.
   */
  def printResult(value: Value): String =
    try printWith(value, result = true)
    catch { case failed: ForcingFailed => throw failed.cause }

  private def printWith(value: Value, result: Boolean): String =
    try new ValuePrinter(Map.empty, result).print(value)
    catch {
      case NonFatal(_) =>
        value match {
          case _: Value.VPi          => "<function type>"
          case lam: Value.VLam       => s"<function ${lam.id}>"
          case _: Value.NeutralThunk => "<stuck match>"
          case other                 => other.getClass.getSimpleName
        }
    }
}
