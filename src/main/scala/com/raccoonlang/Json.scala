package com.raccoonlang

/**
 * The JSON the CLI's batch output and its server's protocol use: strings written quoted, and values read into Scala
 * ones: an object as a `Map[String, Any]`, an array as a `Vector[Any]`, a string, a `Double`, a `Boolean`, or `null`.
 */
object Json {

  /** `text` as a JSON string. */
  def quote(text: String): String = {
    val out = new StringBuilder(text.length + 2)
    out += '"'
    text.foreach {
      case '"'          => out ++= "\\\""
      case '\\'         => out ++= "\\\\"
      case '\n'         => out ++= "\\n"
      case '\r'         => out ++= "\\r"
      case '\t'         => out ++= "\\t"
      case c if c < ' ' => out ++= f"\\u${c.toInt}%04x"
      case c            => out += c
    }
    out += '"'
    out.result()
  }

  /** An object of `fields`, each value already JSON. */
  def obj(fields: (String, String)*): String =
    fields.map { case (name, value) => s"${quote(name)}:$value" }.mkString("{", ",", "}")

  /** The value `text` holds, or `IllegalArgumentException` when it holds no one JSON value. */
  def parse(text: String): Any = {
    val reader = new Reader(text)
    val value = reader.value()
    reader.end()
    value
  }

  private final class Reader(text: String) {
    private var at = 0

    private def fail(expected: String): Nothing =
      throw new IllegalArgumentException(s"Invalid JSON at offset $at: expected $expected")

    private def skipSpace(): Unit = while (at < text.length && " \t\r\n".indexOf(text(at)) >= 0) at += 1

    private def peek: Char = { skipSpace(); if (at < text.length) text(at) else fail("a value") }

    private def expect(c: Char): Unit = if (peek == c) at += 1 else fail(s"'$c'")

    private def literal(word: String, value: Any): Any =
      if (text.startsWith(word, at)) { at += word.length; value }
      else fail(word)

    def end(): Unit = { skipSpace(); if (at != text.length) fail("the end") }

    def value(): Any =
      peek match {
        case '{' =>
          at += 1
          if (peek == '}') { at += 1; Map.empty[String, Any] }
          else {
            val fields = Map.newBuilder[String, Any]
            var more = true
            while (more) {
              val name = string()
              expect(':')
              fields += name -> value()
              if (peek == ',') at += 1 else { expect('}'); more = false }
            }
            fields.result()
          }
        case '[' =>
          at += 1
          if (peek == ']') { at += 1; Vector.empty[Any] }
          else {
            val items = Vector.newBuilder[Any]
            var more = true
            while (more) {
              items += value()
              if (peek == ',') at += 1 else { expect(']'); more = false }
            }
            items.result()
          }
        case '"' => string()
        case 't' => literal("true", true)
        case 'f' => literal("false", false)
        case 'n' => literal("null", null)
        case _ =>
          val start = at
          while (at < text.length && "+-.eE0123456789".indexOf(text(at)) >= 0) at += 1
          text.substring(start, at).toDoubleOption.getOrElse { at = start; fail("a value") }
      }

    private def string(): String = {
      expect('"')
      val out = new StringBuilder
      while (at < text.length && text(at) != '"') {
        if (text(at) == '\\') {
          if (at + 1 >= text.length) fail("an escape")
          text(at + 1) match {
            case 'u' if at + 6 <= text.length =>
              out += Integer.parseInt(text.substring(at + 2, at + 6), 16).toChar
              at += 6
            case c =>
              out += (c match {
                case 'n'                     => '\n'
                case 'r'                     => '\r'
                case 't'                     => '\t'
                case 'b'                     => '\b'
                case 'f'                     => '\f'
                case '"' | '\\' | '/'        => c
                case _                       => fail("an escape")
              })
              at += 2
          }
        } else {
          out += text(at)
          at += 1
        }
      }
      expect('"')
      out.result()
    }
  }
}
