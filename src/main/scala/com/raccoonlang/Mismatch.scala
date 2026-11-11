package com.raccoonlang

import com.raccoonlang.Value.{VLam, VPi}
import com.raccoonlang.telescope.BinderOps

import scala.annotation.tailrec
import scala.util.control.NonFatal

/**
 * The text of a `TypeMismatch` (docs/language.md, "Type mismatches"): the expected type as written where the checker
 * has it, the actual type, the first pair of subterms where the two differ, and the expected type as it evaluates.
 * Values print within `bounds`, which bound each one's text and the work of printing it, however large the value. A
 * diagnostic only: nothing here decides what checks, and any failure while describing falls back to the types clipped.
 */
object Mismatch {

  /**
   * How a diagnostic abbreviates a value. It prints whole up to `whole` characters; a longer one prints along the path
   * to a difference, or in outline, with each other part longer than `part` characters as `…` and its length, counted
   * up to `measure`, and at most `cap` characters, followed by `…` and how many more it has, counted alike. One budget,
   * `cap`, sets the others: printing a value costs at most `cap` and `measure` characters for the value and for each
   * part left out, of which at most about `cap` fit.
   */
  final case class Bounds(cap: Int) {
    require(cap > 0, "A diagnostic prints at least one character of a value")
    val whole: Int = cap * 2 / 5
    val part: Int = cap * 3 / 25
    val measure: Int = math.max(10000, cap * 16)

    /** The marker for text left out: `…` and its length, or more than `measure` characters when `None`. */
    def elided(length: Option[Int]): String = length.fold(s"…(over $measure chars)")(n => s"…($n chars)")

    /** The marker for `count` list elements left out. */
    def omitted(count: Int): String = s"…($count ${if (count == 1) "element" else "elements"})"
  }

  /**
   * The bounds of every diagnostic: a value prints in at most 600 characters, or as many as the JVM system property
   * `raccoon.messageCap` gives, as in `java -Draccoon.messageCap=2000`.
   */
  val bounds: Bounds =
    Bounds(sys.props.get("raccoon.messageCap").flatMap(_.toIntOption).filter(_ > 0).getOrElse(600))

  /** The most steps a difference is looked for through. */
  private val MaxDepth = 1000

  /** A differing pair this short, below the root, is reported with its parent, which says what the values are of. */
  private val Short = 12

  /** A value as short as `Short` without its variables' numbering prints within this many characters with it. */
  private val ShortNumbered = 240

  /** A step from a value, as `print` shows it, to one of its parts. */
  sealed trait Step
  object Step {

    /** An application's argument, as printed: a constructor's stored fields, a call's arguments. */
    final case class Arg(index: Int) extends Step

    /** A kernel list's element. */
    final case class Elem(index: Int) extends Step

    /** A kernel list's end after its elements, `xs` in `[a, b] ++ xs`. */
    case object End extends Step

    /** A kernel list after its first `count` elements, which another list of more or fewer elements shares. */
    final case class Rest(count: Int) extends Step

    /** A function type's codomain, opened on its binders. */
    case object Codomain extends Step

    /** A local lambda's body, run on its binders. */
    case object Body extends Step

    /** A record projection's base, `r` in `r.field`. */
    case object Base extends Step

    /** A stuck match's scrutinee's value (`Value.MatchId`), which its syntax shows as its scrutinee. */
    case object Scrutinee extends Step

    /** A stuck match's captured value (`Value.MatchId`), which its syntax shows where it names that local. */
    final case class Capture(index: Int) extends Step
  }

  /** How `print` shows a value: an application, a kernel list, a function type, or whole. */
  sealed trait Shape
  object Shape {
    final case class App(head: String, args: Vector[Value]) extends Shape
    /** `rests(i)` is the list from element `i` on. */
    final case class ListOf(elements: Vector[Value], end: Value, rests: Vector[Value]) extends Shape {
      require(rests.length == elements.length, "A list has a rest from each element")

      /** The list after its first `count` elements, at most all of them. */
      def after(count: Int): Value = if (count < elements.length) rests(count) else end
    }
    final case class Fun(pi: VPi) extends Shape
    final case class Lam(lam: VLam) extends Shape
    final case class Field(base: Value, field: String) extends Shape
    case object Whole extends Shape
  }

  /**
   * The message for `expected` and `actual`, `written` being the expected type as the source writes it, when the
   * checker has that: the type annotated, or a parameter's type with the call's arguments for its earlier parameters.
   */
  def message(expected: Value, actual: Value, written: Option[String]): String =
    try describe(expected, actual, written)
    catch {
      case NonFatal(_) | _: StackOverflowError =>
        s"Type mismatch: expected type: ${clipped(expected)}, actual: ${clipped(actual)}"
    }

  private def describe(expected: Value, actual: Value, written: Option[String]): String = {
    val (path, e, a) = reported(firstDifference(expected, actual))
    val expectedText = show(expected, path)
    val shown = written.fold(expectedText)(clip)
    val difference =
      if (path.isEmpty) "" else s"; first difference: expected ${abbreviated(e)}, actual ${abbreviated(a)}"
    val evaluated = written.filter(w => w != plain(expectedText)).fold("")(_ => s"; the expected type evaluates to $expectedText")
    s"Type mismatch: expected type: $shown, actual: ${show(actual, path)}$difference$evaluated"
  }

  /** `value` whole when short, and otherwise along `path` (`PrettyPrinter.printFocused`), clipped, on one line. */
  private def show(value: Value, path: List[Step]): String =
    PrettyPrinter.printWithin(value, bounds.whole).getOrElse(oneLine(PrettyPrinter.printFocused(value, path, bounds)))

  /** `value` whole, clipped, on one line. */
  private def clipped(value: Value): String = oneLine(PrettyPrinter.printClipped(value, bounds))

  /**
   * `value` for a diagnostic: whole when short, and otherwise in outline (`PrettyPrinter.printOutline`), clipped, on
   * one line. Printing it costs at most what `bounds` allow, however large the value.
   */
  def abbreviated(value: Value): String =
    PrettyPrinter.printWithin(value, bounds.whole).getOrElse(oneLine(PrettyPrinter.printOutline(value, bounds)))

  /** `text` on one line, and at most `bounds.cap` characters, followed by `…` and how many more it has. */
  def clip(text: String): String = {
    val line = oneLine(text)
    if (line.length <= bounds.cap) line else line.take(bounds.cap) + bounds.elided(Some(line.length - bounds.cap))
  }

  /** Checked syntax on one line, clipped as values are: syntax quoted from a value may be as large as the value. */
  def clip(syntax: ElabAst.Ast): String = oneLine(PrettyPrinter.printElabClipped(syntax, bounds))

  private def oneLine(text: String): String = text.replace('\n', ' ')

  /** A diagnostic without variable numbering, as a variable prints in a value, `x#12`, but by name in syntax. */
  private def plain(text: String): String = text.replaceAll("#[0-9]+", "")

  /**
   * The pair a difference reports, from the pairs along the path to the first difference, outermost first: the last,
   * unless it is a pair of short values, such as two numerals, that are arguments of an application or bases of a
   * projection below the root, when that application or projection, which says what they are, is.
   */
  private def reported(pairs: List[(List[Step], Value, Value)]): (List[Step], Value, Value) =
    pairs.reverse match {
      case (last @ (lastPath, e, a)) :: (parent @ (parentPath, _, _)) :: _
          if parentPath.nonEmpty && lastPath.lastOption.exists(step => step.isInstanceOf[Step.Arg] || step == Step.Base) =>
        if (short(e) && short(a)) parent else last
      case last :: _ => last
      case Nil       => throw new IllegalStateException("a difference has a pair")
    }

  /** Whether `value` prints in at most `Short` characters, without its variables' numbering. */
  private def short(value: Value): Boolean =
    PrettyPrinter.printWithin(value, ShortNumbered).exists(text => plain(text).length <= Short)

  /**
   * The path from `expected` and `actual` down to their first pair of subterms that do not convert, and that pair:
   * through applications of one head to as many arguments, the first argument pair that does not convert; through
   * kernel lists, the first element pair, or, when the elements they share agree, their ends if they have as many and
   * otherwise what follows the elements they share; through function types of as many
   * binders, their codomains on one set of fresh variables, and through local lambdas their bodies alike; through
   * projections of one field, their bases. It stops where the two have different shapes, or where no part differs
   * though the whole does. Returns every pair on the way, each with its path, the roots first.
   */
  def firstDifference(expected: Value, actual: Value): List[(List[Step], Value, Value)] = {
    def differ(x: Value, y: Value): Boolean = !ValueEquivalence.defEq(x, y)
    def shape(value: Value): Shape = PrettyPrinter.shapeOf(value, bounds.whole)

    // Each step goes into a part, so the path is finite; the bound only keeps a diagnostic's cost bounded too.
    @tailrec
    def loop(e: Value, a: Value, path: List[Step], pairs: List[(List[Step], Value, Value)]): List[(List[Step], Value, Value)] = {
      val here = (path.reverse, e, a) :: pairs
      val next: Option[(Step, Value, Value)] = if (pairs.length >= MaxDepth) None else (shape(e), shape(a)) match {
        case (Shape.App(eh, eArgs), Shape.App(ah, aArgs)) if eh == ah && eArgs.length == aArgs.length =>
          eArgs.indices.find(i => differ(eArgs(i), aArgs(i))).map(i => (Step.Arg(i), eArgs(i), aArgs(i)))
        case (eList: Shape.ListOf, aList: Shape.ListOf) =>
          val (eElems, aElems) = (eList.elements, aList.elements)
          val common = math.min(eElems.length, aElems.length)
          // After the shared elements one list is at its end, so a later step meets fewer elements, and the loop ends.
          (0 until common)
            .find(i => differ(eElems(i), aElems(i)))
            .map(i => (Step.Elem(i), eElems(i), aElems(i)))
            .orElse {
              if (eElems.length == aElems.length)
                Option.when(differ(eList.end, aList.end))((Step.End, eList.end, aList.end))
              else Option.when(common > 0)((Step.Rest(common), eList.after(common), aList.after(common)))
            }
        case (Shape.Fun(ePi), Shape.Fun(aPi)) if ePi.binders.length == aPi.binders.length =>
          // The actual type's binders bound to the expected's fresh variables; where their types' shapes differ so
          // that a capture does not open, the difference is the function types.
          try {
            val fresh = BinderOps.freshen(ePi)
            val args = ePi.binders.map(b => fresh(b.localRef))
            val eOut = ePi.codomain(fresh)
            val aOut = aPi.codomain(BinderOps.instantiateFull(aPi.binders, aPi.env, args))
            Option.when(differ(eOut, aOut))((Step.Codomain, eOut, aOut))
          } catch { case _: TypeError => None }
        case (Shape.Lam(eLam), Shape.Lam(aLam)) if eLam.tpe.binders.length == aLam.tpe.binders.length =>
          try {
            val fresh = BinderOps.freshen(eLam.tpe)
            val args = eLam.tpe.binders.map(b => fresh(b.localRef))
            val eBody = Interpreter.runLam(eLam, args)
            val aBody = Interpreter.runLam(aLam, args)
            Option.when(differ(eBody, aBody))((Step.Body, eBody, aBody))
          } catch { case _: TypeError => None }
        case (Shape.Field(eBase, eField), Shape.Field(aBase, aField)) if eField == aField =>
          Option.when(differ(eBase, aBase))((Step.Base, eBase, aBase))
        // Stuck matches of one code differ in their scrutinees or in what they captured.
        case (Shape.Whole, Shape.Whole) =>
          (e, a) match {
            case (eThunk: Value.NeutralThunk, aThunk: Value.NeutralThunk)
                if (eThunk.id.code eq aThunk.id.code) && eThunk.id.captures.length == aThunk.id.captures.length =>
              val (eScrut, aScrut) = (eThunk.id.scrut, aThunk.id.scrut)
              val (eCaptures, aCaptures) = (eThunk.id.captures, aThunk.id.captures)
              if (differ(eScrut, aScrut)) Some((Step.Scrutinee, eScrut, aScrut))
              else
                eCaptures.indices
                  .find(i => differ(eCaptures(i), aCaptures(i)))
                  .map(i => (Step.Capture(i), eCaptures(i), aCaptures(i)))
            case _ => None
          }
        case _ => None
      }
      next match {
        case Some((step, e2, a2)) => loop(e2, a2, step :: path, here)
        case None                 => here.reverse
      }
    }
    loop(expected, actual, Nil, Nil)
  }
}
