package com.raccoonlang

import com.raccoonlang.Parser._

import scala.annotation.unchecked.uncheckedVariance
import scala.collection.mutable.ArrayBuffer

sealed trait ParseResult[+T] {
  def map[B](f: T => B): ParseResult[B]
}
case class Success[T](value: T, startIdx: Int, endIdx: Int) extends ParseResult[T] {
  override def map[B](f: T => B): ParseResult[B] = Success(f(value), startIdx, endIdx)
}
case class Failure(startIdx: Int, curIdx: Int, message: String) extends ParseResult[Nothing] {
  override def map[B](f: Nothing => B): ParseResult[B] = this
}

case class ParseError(startIdx: Int, curIdx: Int, message: String) extends RuntimeException()

trait Parser[+A] {
  def parse(input: String, startIdx: Int): ParseResult[A]

  def ~[B](p2: => Parser[B])(implicit C: Sequence.Combine[A, B] @uncheckedVariance): Parser[C.Out] =
    Sequence.seqParser[A, B](this, p2, fatal = false, C)

  def ~/[B](p2: => Parser[B])(implicit C: Sequence.Combine[A, B] @uncheckedVariance): Parser[C.Out] =
    FatalRight(Sequence.seqParser[A, B](this, p2, fatal = true, C))

  def rep(min: Int)(implicit acc: Rep.Accumulator[A] @uncheckedVariance): Parser[acc.Out] =
    Rep.repParser(this, min, acc)

  def |[Out >: A, B <: Out](p2: => Parser[B]): Parser[Out] = new OrParser[Out, A, B](this, p2)

  def ?(implicit opt: Opt.OptValue[A] @uncheckedVariance): Parser[opt.Out] = Opt.optParser(this, opt)

  def named(name: String): Parser[A] = NamedParser(this, name)

  def log(name: String): Parser[A] = LogParser(this, name)

  def fail(startIdx: Int, curIdx: Int): Failure = Failure(startIdx, curIdx, message = s"$this")

  def map[B](f: A => B): Parser[B] = new Parser.Map[A, B](this, f)

  def filter(f: A => Boolean): Parser[A] = new FilterParser[A](this, f)

  //Useful combinators
  def rep(min: Int, sep: Parser[NoValueT]): Parser[Vector[A]] = {
    val p = (this ~ (sep ~ this).rep(min - 1)).map { case (a, buff) => buff.prepended(a) }

    if (min > 0) p
    else p.?.map(_.getOrElse(Vector.empty))
  }
}

object Parser {
  case object NoValue
  private type NoValueT = NoValue.type

  private type Match = ParseResult[NoValueT]
  private type MatchParser = Parser[NoValueT]

  def P(s: String) = Exact(s)
  def P(c: Char) = CharPred(_ == c)
  def P(pred: Char => Boolean) = CharPred(pred)

  implicit class MatchParserOps(p: MatchParser) {
    def ! : Parser[String] = Parser.Capture(p)
  }

  private def success(startIdx: Int, curIdx: Int): Success[NoValueT] = Success(Parser.NoValue, startIdx, curIdx)

  case class Exact(s: String) extends MatchParser {
    override def parse(input: String, startIdx: Int): Match = {
      val endIdx = startIdx + s.length
      if (startIdx <= input.length && input.startsWith(s, startIdx)) success(startIdx, endIdx)
      else fail(startIdx, startIdx)
    }
  }

  case class CharPred(pred: Char => Boolean) extends MatchParser {
    override def parse(input: String, startIdx: Int): ParseResult[NoValueT] = {
      if (startIdx < input.length && pred(input.charAt(startIdx))) success(startIdx, startIdx + 1)
      else fail(startIdx, startIdx)
    }
  }

  case class CharsWhile(pred: Char => Boolean) extends MatchParser {
    override def parse(input: String, startIdx: Int): Match = {
      var curIdx = startIdx
      while (curIdx < input.length && pred(input.charAt(curIdx)))
        curIdx += 1

      success(startIdx, curIdx)
    }
  }

  object End extends MatchParser {
    override def parse(input: String, startIdx: Int): ParseResult[NoValueT] = {
      if (startIdx == input.length) success(startIdx, startIdx)
      else fail(startIdx, startIdx)
    }
  }

  private case class NamedParser[T](p: Parser[T], name: String) extends Parser[T] {
    override def parse(input: String, startIdx: Int): ParseResult[T] = p.parse(input, startIdx)

    override def toString: String = name
  }

  private case class LogParser[T](p: Parser[T], name: String) extends Parser[T] {
    override def parse(input: String, startIdx: Int): ParseResult[T] = {
      val res = p.parse(input, startIdx)
      res match {
        case Success(value, startIdx, endIdx) =>
          println(s"$name - $startIdx: ${input.substring(startIdx, endIdx)}")
        case _: Failure =>
      }
      res
    }

    override def toString: String = s"($p).log($name)"
  }

  class FilterParser[T](p: Parser[T], f: T => Boolean) extends Parser[T] {
    override def parse(input: String, startIdx: Int): ParseResult[T] = p.parse(input, startIdx) match {
      case s @ Success(value, _, _) if f(value) => s
      case other                                => fail(startIdx, startIdx)
    }
  }

  // Wraps a parser to propagate fatal behavior to all subsequent ~ / ~/
  private case class FatalRight[T](p: Parser[T]) extends Parser[T] {
    override def parse(input: String, startIdx: Int): ParseResult[T] = p.parse(input, startIdx)

    override def ~[B](p2: => Parser[B])(implicit C: Sequence.Combine[T, B] @uncheckedVariance): Parser[C.Out] =
      FatalRight(Sequence.seqParser[T, B](this, p2, fatal = true, C))

    override def ~/[B](p2: => Parser[B])(implicit C: Sequence.Combine[T, B] @uncheckedVariance): Parser[C.Out] =
      FatalRight(Sequence.seqParser[T, B](this, p2, fatal = true, C))

    override def toString: String = s"FatalRight($p)"
  }

  private object Sequence {
    // Type-level combination for sequencing
    trait Combine[A, B] {
      type Out

      def combine(a: A, b: B): Out
    }

    private object Combine extends TupleCombine {
      type Aux[A, B, O] = Combine[A, B] { type Out = O }
      private type NV = NoValueT

      implicit val bothNoValue: Aux[NV, NV, NV] =
        new Combine[NV, NV] {
          type Out = NV
          def combine(a: NV, b: NV): Out = NoValue
        }

      implicit def leftNoValue[B]: Aux[NV, B, B] =
        new Combine[NV, B] {
          type Out = B
          def combine(a: NV, b: B): Out = b
        }

      implicit def rightNoValue[A]: Aux[A, NV, A] =
        new Combine[A, NV] {
          type Out = A
          def combine(a: A, b: NV): Out = a
        }
    }

    /** Tuple flattener. Kinda ugly, but what can you do */
    private trait TupleCombine extends DefaultCombine {
      type CA[A, B, O] = Combine.Aux[A, B, O]

      implicit def t2[A, B, C]: CA[(A, B), C, (A, B, C)] = new Combine[(A, B), C] {
        override type Out = (A, B, C)
        override def combine(a: (A, B), b: C): Out = (a._1, a._2, b)
      }
      implicit def t3[A, B, C, D]: CA[(A, B, C), D, (A, B, C, D)] = new Combine[(A, B, C), D] {
        override type Out = (A, B, C, D)
        override def combine(a: (A, B, C), b: D): Out = (a._1, a._2, a._3, b)
      }
      implicit def t4[A, B, C, D, E]: CA[(A, B, C, D), E, (A, B, C, D, E)] = new Combine[(A, B, C, D), E] {
        override type Out = (A, B, C, D, E)
        override def combine(a: (A, B, C, D), b: E): Out = (a._1, a._2, a._3, a._4, b)
      }
      implicit def t5[A, B, C, D, E, F]: CA[(A, B, C, D, E), F, (A, B, C, D, E, F)] = new Combine[(A, B, C, D, E), F] {
        override type Out = (A, B, C, D, E, F)
        override def combine(a: (A, B, C, D, E), b: F): Out = (a._1, a._2, a._3, a._4, a._5, b)
      }
      implicit def t6[A, B, C, D, E, F, G]: CA[(A, B, C, D, E, F), G, (A, B, C, D, E, F, G)] =
        new Combine[(A, B, C, D, E, F), G] {
          override type Out = (A, B, C, D, E, F, G)
          override def combine(a: (A, B, C, D, E, F), b: G): Out = (a._1, a._2, a._3, a._4, a._5, a._6, b)
        }
    }

    private trait DefaultCombine {
      implicit def bothValues[A, B]: Combine.Aux[A, B, (A, B)] =
        new Combine[A, B] {
          type Out = (A, B)
          def combine(a: A, b: B): Out = (a, b)
        }
    }

    def seqParser[A, B](p1: Parser[A], p2: => Parser[B], fatal: Boolean, C: Combine[A, B]): Parser[C.Out] =
      new Parser[C.Out] {
        override def parse(input: String, startIdx: Int): ParseResult[C.Out] = {
          p1.parse(input, startIdx) match {
            case Success(a, sIdx, midIdx) =>
              p2.parse(input, midIdx) match {
                case Success(b, _, endIdx) => Success(C.combine(a, b), sIdx, endIdx)
                case f: Failure =>
                  if (fatal)
                    throw ParseError(startIdx, midIdx, s"Failed to parse ${p2}")
                  else f
              }
            case f: Failure => f
          }
        }

        override def toString: String = s"$p1 ~ $p2"
      }
  }

  private case class Capture(p: MatchParser) extends Parser[String] {
    override def parse(input: String, startIdx: Int): ParseResult[String] = {
      p.parse(input, startIdx) match {
        case Success(_, startIdx, endIdx) => Success(input.substring(startIdx, endIdx), startIdx, endIdx)
        case f: Failure                   => f
      }
    }
  }

  private class Map[A, B](v: Parser[A], f: A => B) extends Parser[B] {
    override def parse(input: String, startIdx: Int): ParseResult[B] = {
      v.parse(input, startIdx).map(f)
    }

    override def toString: String = s"$v.map()"
  }

  object Rep {
    trait Accumulator[A] {
      type Out
      def put(a: A): Unit
      def length: Int
      def res: Out
    }

    private object Accumulator extends LowPriImplicits {
      type Aux[A, O] = Accumulator[A] { type Out = O }

      implicit val nvAccumulator: Aux[NoValueT, NoValueT] = new Accumulator[NoValueT] {
        private var _count: Int = 0

        override type Out = NoValueT
        override def put(a: NoValueT): Unit = _count = _count + 1
        override def length: Int = _count
        override def res: NoValueT = NoValue
      }
    }

    private trait LowPriImplicits {
      implicit def valueAccumulator[A]: Accumulator.Aux[A, Vector[A]] = new Accumulator[A] {
        private val _buf = ArrayBuffer.empty[A]

        override type Out = Vector[A]
        override def put(a: A): Unit = _buf += a
        override def length: Int = _buf.length
        override def res: Out = _buf.toVector
      }
    }

    def repParser[A](p: Parser[A], min: Int, acc: Accumulator[A]): Parser[acc.Out] = new Parser[acc.Out] {
      override def parse(input: String, startIdx: Int): ParseResult[acc.Out] = {
        var done = false
        var curIdx = startIdx

        while (!done) {
          p.parse(input, curIdx) match {
            case Success(a, _, endIdx) =>
              acc.put(a)
              curIdx = endIdx
            case _: Failure =>
              done = true
          }
        }

        if (acc.length >= min) Success(acc.res, startIdx, curIdx)
        else Failure(startIdx, curIdx, s"$this: Not enough instances parsed")
      }

      override def toString: String = s"${p}.rep(${min})"
    }

  }

  private class OrParser[Out, A <: Out, B <: Out](p1: Parser[A], p2: => Parser[B]) extends Parser[Out] {
    override def parse(input: String, startIdx: Int): ParseResult[Out] = {
      p1.parse(input, startIdx) match {
        case Success(value, startIdx, endIdx) => Success[Out](value, startIdx, endIdx)
        case _: Failure =>
          p2.parse(input, startIdx) match {
            case Success(value, startIdx, endIdx) => Success[Out](value, startIdx, endIdx)
            case f: Failure                       => f
          }
      }
    }
  }

  object Opt {
    trait OptValue[A] {
      type Out
      def success(a: A): Out
      def failure: Out
    }

    private object OptValue extends LowPriImplicits {
      type Aux[A, O] = OptValue[A] { type Out = O }

      implicit val nvOptValue: Aux[NoValueT, NoValueT] = new OptValue[NoValueT] {
        override type Out = NoValueT
        override def success(a: NoValueT): Out = NoValue
        override def failure: Out = NoValue
      }
    }
    private trait LowPriImplicits {
      implicit def valueOptValue[A]: OptValue.Aux[A, Option[A]] = new OptValue[A] {
        override type Out = Option[A]
        override def success(a: A): Out = Some(a)
        override def failure: Out = None
      }
    }

    def optParser[A](p1: Parser[A], O: OptValue[A]): Parser[O.Out] = new Parser[O.Out] {
      override def parse(input: String, startIdx: Int): ParseResult[O.Out] = {
        p1.parse(input, startIdx) match {
          case Success(value, startIdx, endIdx) => Success(O.success(value), startIdx, endIdx)
          case _: Failure                       => Success(O.failure, startIdx, startIdx)
        }
      }
    }
  }

}
