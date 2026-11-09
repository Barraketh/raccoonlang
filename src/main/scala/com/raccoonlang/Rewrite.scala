package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.ValueQuote.{QuoteContext, QuoteEntry, quoteContext, quoteType}
import com.raccoonlang.{CoreAst => CA, ElabAst => EA}

/**
 * Goal-directed rewriting (docs/language.md, "Rewriting"): for one step of `rewrite h in e`, the call a user would
 * write, `Eq.substProp(Eq.symm(h), fun (x: A): Prop => T[x], e)`, built from the type of `h` and the type `T` expected
 * of the rewrite. Nothing here is trusted. The checker checks the call it returns as any other term
 * (`TypeChecker.checkRewrite`), so a motive this builds wrongly can only fail to check, and the kernel and its values
 * never see a rewrite.
 *
 * The motive abstracts the occurrences of one side of the equation in the goal as it evaluates: the goal's value is
 * quoted (`ValueQuote`) with that side's value read as the motive's bound variable wherever quotation meets a value of
 * its key. Keys are structural (`ValueKey`), so an occurrence is a subterm of the goal's evaluated form that evaluation
 * built the same way as the side, such as a scrutinee that a `Bool.cond` is stuck on, even where the goal as written
 * only names a definition that computes it.
 */
private[raccoonlang] object Rewrite {
  val SubstName = "Eq.substProp"
  val SymmName = "Eq.symm"

  /** The prelude family whose proofs a rewrite takes, as `Eq(A, x, y)`. */
  private val EqName = "Eq"

  /** The name the motive's bound variable prints with; no source name can be written with it, so none is shadowed. */
  private val BoundName = "_rewritten"

  /**
   * `call` is `Eq.substProp(p, motive, e)`, whose result is the motive at the side the rewrite abstracts, which is the
   * goal; `other` is the other side, the motive's argument in the type `e` is checked against.
   */
  final case class Plan(call: CA.Term.App, other: Value)

  /**
   * The call for `rw` in `env`, whose equation `rw.equation` checked to a proof of `equationType`, against `goal`, the
   * type expected of `rw` in `env`. Without `reverse` the step abstracts the equation's left side and checks `e` at its
   * right, through `Eq.symm`, as `rw [h]` does in Lean; with it, the right side, at the left. A goal with no occurrence of
   * the side is refused, since the rewrite would be the identity, and a direction mistake is the likely cause.
   */
  def plan(rw: CA.Term.Rewrite, equationType: Value, goal: Value, env: Env): Plan = {
    val span = rw.span
    def fail(reason: String): Nothing = throw RewriteFailed(reason, Some(span))

    val (carrier, left, right) = equationType match {
      case InductiveFamilyValue(eq) if eq.head.name == EqName && eq.args.length == 3 =>
        (eq.args(0), eq.args(1), eq.args(2))
      case other =>
        fail(s"its equation ${Mismatch.clip(PrettyPrinter.printTerm(rw.equation))} proves ${Mismatch.abbreviated(other)}, which is no Eq(A, x, y)")
    }
    if (goal.tpe != PropTpe)
      fail(s"the expected type ${Mismatch.abbreviated(goal)} is no proposition; a rewrite proves propositions, by $SubstName")
    val (from, other) = if (rw.reverse) (right, left) else (left, right)

    val base = quoteContext(env)
    // The motive's parameter takes the next slot of `env`, where the checker checks the motive.
    val bound = CA.LocalRef(base.localEnvLength, BoundName)
    // Quotation names a value a local holds by that local, before reading its form. So a goal written as a `let`'s name,
    // or holding one, is quoted as the name, which hides its occurrences of the side. Where the goal so quoted has none,
    // it is quoted again through the forms of the locals that hold computed values, as a goal written out would be;
    // the larger motive costs checking time only.
    val abstracted = {
      val named = abstractIn(goal, from, bound, base, span)
      if (CapturedIndexes.mentions(named, bound.id)) named
      else {
        val computed = env.locals.zipWithIndex.collect {
          case (binding, idx) if binding.valueOption.exists(v => !v.isInstanceOf[Var]) => idx
        }.toSet
        val open = base.copy(quote = base.quote.filter { case (_, entry) =>
          entry.term match {
            case EA.Term.LocalRef(ref, _) => !computed.contains(ref.id)
            case _                        => true
          }
        })
        abstractIn(goal, from, bound, open, span)
      }
    }
    if (!CapturedIndexes.mentions(abstracted, bound.id)) {
      if (ValueEquivalence.defEq(left, right))
        fail(s"the sides of ${Mismatch.abbreviated(equationType)} convert, so the step would change nothing; drop it")
      val sides = if (rw.reverse) ("right", "left") else ("left", "right")
      val otherOccurs = CapturedIndexes.mentions(abstractIn(goal, other, bound, base, span), bound.id)
      val hint =
        if (otherOccurs)
          s"; its ${sides._2} side ${Mismatch.abbreviated(other)} does, so the step may need ${if (rw.reverse) "no" else "a"} `<-`"
        else ""
      fail(
        s"the expected type ${Mismatch.abbreviated(goal)} has no occurrence of ${Mismatch.abbreviated(from)}, the ${sides._1} side of ${Mismatch.abbreviated(equationType)}$hint"
      )
    }

    val carrierType =
      try new Core(base.localEnvLength, Map.empty).typeTerm(quoteType(carrier, base, span))
      catch { case e: CannotQuoteValue => fail(s"the equation's type ${Mismatch.abbreviated(carrier)} cannot be written: ${e.msg}") }
    val parameter = CA.Binder(bound, CA.BinderType.TypePattern(CA.TypePattern.Type(carrierType), span), span)
    val motive = CA.Term.Lam(
      CA.Term.Pi(Vector(parameter), CA.Term.GlobalRef("Prop", span), span, NodeId.fresh()),
      Vector.empty,
      new Core(bound.id + 1, Map(bound.id -> bound)).term(abstracted),
      span,
      None,
      None,
      NodeId.fresh()
    )
    val proof =
      if (rw.reverse) rw.equation
      else CA.Term.App(CA.Term.GlobalRef(SymmName, span), Vector(rw.equation), span)
    Plan(CA.Term.App(CA.Term.GlobalRef(SubstName, span), Vector(proof, motive, rw.body), span), other)
  }

  /** `goal` quoted in `base`, with every value of the key of `side` read as `bound`, the next local of `base`. */
  private def abstractIn(goal: Value, side: Value, bound: CA.LocalRef, base: QuoteContext, span: Span): EA.Term = {
    val entry = QuoteEntry(EA.Term.LocalRef(bound, span), LocalResidualPolicy.Residualizable)
    val context = QuoteContext(base.quote + (side.key -> entry), base.localEnvLength + 1)
    try quoteType(goal, context, span)
    catch {
      case e: CannotQuoteValue =>
        throw RewriteFailed(s"the expected type ${Mismatch.abbreviated(goal)} cannot be written as a motive: ${e.msg}", Some(span))
    }
  }

  /**
   * Checked syntax written back as source syntax, for the checker to check again: each checked form as the source form
   * it checks from, its bound locals renumbered to the slots the checker gives them. A projection is
   * `Fam.field(base)`, and a word its cons applications and appends, from the back. A case names its constructor by
   * its canonical name, and a match whose cases bind their equation names one. A recursive lambda has no metric here
   * to be checked with, so it is refused; quotation names a recursive global, as the definitions a goal unfolds to
   * are, by its name.
   *
   * Renumbering gives the checker's density invariant (`Env.putLocal`) by construction, whatever slots quotation chose.
   * Quotation numbers the locals it binds densely in the checker's order (`ValueQuote.ClosedEnvInliner`), so this is
   * the identity on its output; it only keeps a rewrite independent of that. Each local is bound where its binder is,
   * in the checker's order: a body's lets in turn, a binder's captures in its pattern's order, a constraint's before
   * its capture, then the binder, and a case's named fields, then its equation. A local bound outside the quoted
   * syntax keeps its slot.
   */
  private final class Core(start: Int, initial: Map[Int, CA.LocalRef]) {
    import Core.Scope

    def term(t: EA.Term): CA.Term = term(t, Scope(start, initial))

    def typeTerm(t: EA.TypeTerm): CA.TypeTerm = typeTerm(t, Scope(start, initial))

    private def term(t: EA.Term, scope: Scope): CA.Term =
      t match {
        case tt: EA.TypeTerm => typeTerm(tt, scope)
        case EA.Term.Body(lets, res, span) =>
          var inner = scope
          val coreLets = lets.map { l =>
            val value = term(l.value, inner)
            val ty = l.ty.map(typeTerm(_, inner))
            val (slot, next) = inner.bind(l.localRef)
            inner = next
            CA.Let(slot, ty, value, l.span, l.isInstance)
          }
          CA.Term.Body(coreLets, term(res, inner), span)
        case EA.Term.Match(scrut, motive, cases, span, _, _) =>
          CA.Term.Match(
            term(scrut, scope),
            motive.map(typeTerm(_, scope)),
            cases.map { c =>
              var inner = scope
              val fields = c.argRefs.map(_.map { ref =>
                val (slot, next) = inner.bind(ref)
                inner = next
                slot
              })
              val equation = c.equation.map { ref =>
                val (slot, next) = inner.bind(ref)
                inner = next
                slot
              }
              CA.Case(c.ctorName, true, fields, term(c.body, inner), c.span, equation)
            },
            None,
            cases.headOption.flatMap(_.equation).map(_ => span),
            span,
            NodeId.fresh()
          )
      }

    private def typeTerm(t: EA.TypeTerm, scope: Scope): CA.TypeTerm =
      t match {
        case EA.Term.GlobalRef(name, span)  => CA.Term.GlobalRef(name, span)
        case EA.Term.LocalRef(ref, span)    => CA.Term.LocalRef(scope(ref), span)
        case EA.Term.App(fn, args, span)    => CA.Term.App(term(fn, scope), args.map(term(_, scope)), span)
        case EA.Term.NatLit(number, span)   => CA.Term.NatLit(number, span)
        case EA.Term.StrLit(text, span)     => CA.Term.StrLit(text, span)
        case pi: EA.Term.Pi                 => this.pi(pi, scope)._1
        case EA.Term.Proj(base, family, field, _, span) =>
          if (field == "_")
            throw RewriteFailed(s"the expected type projects an anonymous field of $family", Some(span))
          CA.Term.App(CA.Term.Select(CA.Term.GlobalRef(family, span), field, span), Vector(term(base, scope)), span)
        case EA.Term.Word(consHead, pieces, span) =>
          val head = CA.Term.GlobalRef(consHead.name, span)
          val end = pieces.last match {
            case EA.Term.WordPiece.Splice(list) => term(list, scope)
            case EA.Term.WordPiece.Layer(_, _)  => throw WTF("A word ends in a splice", Some(span))
          }
          pieces.init.foldRight(end) {
            case (EA.Term.WordPiece.Layer(before, after), rest) =>
              CA.Term.App(head, (before.map(term(_, scope)) :+ rest) ++ after.map(term(_, scope)), span)
            case (EA.Term.WordPiece.Splice(list), rest) =>
              CA.Term.App(CA.Term.GlobalRef("List.append", span), Vector(term(list, scope), rest), span)
          } match {
            case tt: CA.TypeTerm => tt
            case other           => throw WTF(s"A word's end $other is no type term", Some(span))
          }
        case lam: EA.Term.Lam =>
          if (lam.recursiveSelf.nonEmpty || lam.recursivePeers.nonEmpty)
            throw RewriteFailed("the expected type holds a local recursive function", Some(lam.span))
          val (ty, inner) = pi(lam.ty, scope)
          CA.Term.Lam(ty, Vector.empty, term(lam.body, inner), lam.span, lam.name, None, NodeId.fresh())
      }

    /** The function type, and the scope of its codomain, where its binders are bound. */
    private def pi(written: EA.Term.Pi, scope: Scope): (CA.Term.Pi, Scope) = {
      var inner = scope
      val binders = written.binders.map { b =>
        val (ty, typed) = binderType(b.ty, inner)
        val (slot, next) = typed.bind(b.localRef)
        inner = next
        CA.Binder(slot, ty, b.span, b.isInstance)
      }
      (CA.Term.Pi(binders, typeTerm(written.out, inner), written.span, NodeId.fresh()), inner)
    }

    private def binderType(t: EA.BinderType, scope: Scope): (CA.BinderType, Scope) =
      t match {
        case EA.BinderType.TypePattern(tp, span) =>
          val (pattern, inner) = topLevel(tp, scope)
          (CA.BinderType.TypePattern(pattern, span), inner)
        case EA.BinderType.ConstrainedCapture(ref, constraint, span) =>
          val (pattern, constrained) = topLevel(constraint, scope)
          val (slot, inner) = constrained.bind(ref)
          (CA.BinderType.ConstrainedCapture(slot, pattern, span), inner)
      }

    private def topLevel(tp: EA.TopLevelTP, scope: Scope): (CA.TopLevelTP, Scope) =
      tp match {
        case EA.TypePattern.Type(tt) => (CA.TypePattern.Type(typeTerm(tt, scope)), scope)
        case EA.TypePattern.App(fn, args, span) =>
          val head = fn match {
            case EA.Term.GlobalRef(name, sp) => CA.Term.GlobalRef(name, sp)
            case EA.Term.LocalRef(ref, sp)   => CA.Term.LocalRef(scope(ref), sp)
          }
          var inner = scope
          val patterns = args.map { arg =>
            val (p, next) = pattern(arg, inner)
            inner = next
            p
          }
          (CA.TypePattern.App(head, patterns, span), inner)
      }

    private def pattern(tp: EA.TypePattern, scope: Scope): (CA.TypePattern, Scope) =
      tp match {
        case top: EA.TopLevelTP => topLevel(top, scope)
        case EA.TypePattern.Capture(ref, span, constraint) =>
          val (checked, constrained) = constraint match {
            case Some(c) =>
              val (p, next) = topLevel(c, scope)
              (Some(p), next)
            case None => (None, scope)
          }
          val (slot, inner) = constrained.bind(ref)
          (CA.TypePattern.Capture(slot, span, checked), inner)
      }
  }

  private object Core {

    /** The next slot, and the slot each local the syntax bound so far is renumbered to. */
    final case class Scope(depth: Int, renamed: Map[Int, CA.LocalRef]) {
      def bind(ref: CA.LocalRef): (CA.LocalRef, Scope) = {
        val slot = CA.LocalRef(depth, ref.name)
        (slot, Scope(depth + 1, renamed + (ref.id -> slot)))
      }
      def apply(ref: CA.LocalRef): CA.LocalRef = renamed.getOrElse(ref.id, ref)
    }
  }
}
