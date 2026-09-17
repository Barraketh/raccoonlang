package com.raccoonlang

import com.raccoonlang.Parser._

class ParserCoreTests extends munit.FunSuite {
  private def success[A](result: ParseResult[A]): Success[A] = result match {
    case value: Success[A] => value
    case failure           => fail(s"Expected parser success, got $failure")
  }

  test("primitive exact and character parsers consume their input") {
    assertEquals(P("abc").parse("abcdef", 0), Success(Parser.NoValue, 0, 3))
    assertEquals(P('a').parse("abcdef", 0), Success(Parser.NoValue, 0, 1))
    assert(P('z').parse("abcdef", 0).isInstanceOf[Failure])
    assertEquals(CharsWhile(_.isLetter).parse("abc123", 0), Success(Parser.NoValue, 0, 3))
    assertEquals(End.parse("", 0), Success(Parser.NoValue, 0, 0))
    assert(End.parse("x", 0).isInstanceOf[Failure])
  }

  test("capture and sequencing preserve values and positions") {
    val parser = (P("name=") ~ P(c => c.isLetter).!.rep(1)).map { letters => letters.mkString }
    assertEquals(parser.parse("name=Raccoon", 0), Success("Raccoon", 0, 12))

    val captured = (P("let ") ~ P(c => c.isLetter).!.rep(1).map(_.mkString)).parse("let x", 0)
    assertEquals(captured, Success("x", 0, 5))
  }

  test("ordered choice retries the second parser after ordinary failure") {
    val parser = P("ab") | P("a")
    assertEquals(parser.parse("ac", 0), Success(Parser.NoValue, 0, 1))
    assert(parser.parse("z", 0).isInstanceOf[Failure])
  }

  test("fatal sequencing cuts, while Attempt recovers the cut") {
    val committed = P('a') ~/ P('b')
    intercept[ParseError](committed.parse("ac", 0))

    val recoverable = Attempt(committed) | P('a')
    assertEquals(recoverable.parse("ac", 0), Success(Parser.NoValue, 0, 1))
  }

  test("repetition supports minimum counts and separated values") {
    val repeated = success(P('a').!.rep(0).parse("aaab", 0))
    assertEquals(repeated.value.size, 3)
    assertEquals(repeated.endIdx, 3)

    val digits = CharsWhile(_.isDigit).!.rep(1, P(','))
    assertEquals(digits.parse("12,34,5", 0), Success(Vector("12", "34", "5"), 0, 7))

    P('a').!.rep(2).parse("a", 0) match {
      case Failure(startIdx, curIdx, _) =>
        assertEquals(startIdx, 0)
        assertEquals(curIdx, 1)
      case result => fail(s"Expected repetition failure, got $result")
    }
  }

  test("spans retain source identity and source offsets") {
    val source = SourceId(42)
    val parsed = success(P("abc").!.spanned(source).parse("abcdef", 0))
    assertEquals(parsed.value.value, "abc")
    assertEquals(parsed.value.span, Span(0, 3, Some(source)))
    assertEquals(parsed.value.span.nodeId, AstNodeId(Some(source), 0))
    assertEquals(parsed.value.span.nodeId.stableName, "42:0")
  }
}
