package com.raccoonlang

/**
 * Source syntax of string literals: a double-quoted sequence of Unicode scalar values with JSON-style escapes. Decoding
 * and rendering are inverse on text made of scalars, so a printed literal reads back as the same text.
 */
private[raccoonlang] object UnicodeScalarString {

  /**
   * The decoded `text`, which holds only scalars (no unpaired surrogate), and the index just after the closing quote.
   */
  final case class Decoded(text: String, endIdx: Int)

  /** A malformed literal; `offset` indexes the input at the offending character or escape. */
  final case class Invalid(offset: Int, message: String) extends RuntimeException(message)

  val MaxScalar: Int = 0x10ffff

  def isScalar(value: Int): Boolean =
    value >= 0 && value <= MaxScalar && (value < 0xd800 || value > 0xdfff)

  /**
   * Decode the literal starting at `startIdx`, which must be its opening quote. Escapes are `\"`, `\\`, `\/`, `\b`,
   * `\f`, `\n`, `\r`, `\t` and `\uXXXX`; a high-surrogate `\u` escape must be followed by a low-surrogate one, and the
   * pair denotes one scalar. Raw surrogates must be paired, and control characters below U+0020 must be escaped.
   */
  def decodeQuoted(input: String, startIdx: Int): Decoded = {
    require(startIdx < input.length && input.charAt(startIdx) == '"', "decodeQuoted requires an opening quote")
    val text = new java.lang.StringBuilder
    var idx = startIdx + 1

    def invalid(offset: Int, message: String): Nothing = throw Invalid(offset, message)
    def hex4(at: Int): Int = {
      if (at + 4 > input.length) invalid(at, "incomplete Unicode escape")
      var value = 0
      var cur = at
      while (cur < at + 4) {
        val digit = Character.digit(input.charAt(cur), 16)
        if (digit < 0) invalid(cur, "invalid hexadecimal digit in Unicode escape")
        value = (value << 4) | digit
        cur += 1
      }
      value
    }

    while (idx < input.length) {
      val ch = input.charAt(idx)
      if (ch == '"') return Decoded(text.toString, idx + 1)
      if (ch == '\\') {
        if (idx + 1 >= input.length) invalid(idx, "unterminated string escape")
        input.charAt(idx + 1) match {
          case '"'  => text.append('"'); idx += 2
          case '\\' => text.append('\\'); idx += 2
          case '/'  => text.append('/'); idx += 2
          case 'b'  => text.append('\b'); idx += 2
          case 'f'  => text.append('\f'); idx += 2
          case 'n'  => text.append('\n'); idx += 2
          case 'r'  => text.append('\r'); idx += 2
          case 't'  => text.append('\t'); idx += 2
          case 'u' =>
            val first = hex4(idx + 2)
            if (Character.isHighSurrogate(first.toChar)) {
              val secondEscape = idx + 6
              if (
                secondEscape + 6 > input.length || input.charAt(secondEscape) != '\\' ||
                input.charAt(secondEscape + 1) != 'u'
              ) invalid(idx, "high surrogate escape is not followed by a low surrogate escape")
              val second = hex4(secondEscape + 2)
              if (!Character.isLowSurrogate(second.toChar))
                invalid(secondEscape, "high surrogate escape is not followed by a low surrogate")
              text.append(first.toChar).append(second.toChar)
              idx = secondEscape + 6
            } else if (Character.isLowSurrogate(first.toChar)) {
              invalid(idx, "unpaired low surrogate escape")
            } else {
              text.append(first.toChar)
              idx += 6
            }
          case _ => invalid(idx + 1, "invalid string escape")
        }
      } else if (Character.isHighSurrogate(ch)) {
        if (idx + 1 >= input.length || !Character.isLowSurrogate(input.charAt(idx + 1)))
          invalid(idx, "unpaired high surrogate in string literal")
        text.append(ch).append(input.charAt(idx + 1))
        idx += 2
      } else if (Character.isLowSurrogate(ch)) {
        invalid(idx, "unpaired low surrogate in string literal")
      } else if (ch < 0x20) {
        invalid(idx, "unescaped control character in string literal")
      } else {
        text.append(ch)
        idx += 1
      }
    }
    invalid(idx, "unterminated string literal")
  }

  /**
   * The literal that decodes to `text`, which must hold only scalars, as every literal's text and every text read from
   * a value (`packed.Strings`) does.
   */
  def renderQuoted(text: String): String = {
    val out = new java.lang.StringBuilder("\"")
    text.codePoints().forEach { scalar =>
      scalar match {
        case '"'                       => out.append("\\\"")
        case '\\'                      => out.append("\\\\")
        case '\b'                      => out.append("\\b")
        case '\f'                      => out.append("\\f")
        case '\n'                      => out.append("\\n")
        case '\r'                      => out.append("\\r")
        case '\t'                      => out.append("\\t")
        case control if control < 0x20 => out.append(f"\\u$control%04x")
        case _                         => out.appendCodePoint(scalar)
      }
    }
    out.append('"').toString
  }
}
