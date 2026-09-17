package com.raccoonlang

/** Parsing and rendering for source strings represented as validated Unicode scalar values. */
private[raccoonlang] object UnicodeScalarString {
  final case class Decoded(scalars: Vector[Int], endIdx: Int)
  final case class Invalid(offset: Int, message: String) extends RuntimeException(message)

  def isScalar(value: Int): Boolean =
    value >= 0 && value <= 0x10ffff && (value < 0xd800 || value > 0xdfff)

  def decodeQuoted(input: String, startIdx: Int): Decoded = {
    require(startIdx < input.length && input.charAt(startIdx) == '"', "decodeQuoted requires an opening quote")
    val scalars = Vector.newBuilder[Int]
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
      if (ch == '"') return Decoded(scalars.result(), idx + 1)
      if (ch == '\\') {
        if (idx + 1 >= input.length) invalid(idx, "unterminated string escape")
        input.charAt(idx + 1) match {
          case '"'  => scalars += '"'; idx += 2
          case '\\' => scalars += '\\'; idx += 2
          case '/'  => scalars += '/'; idx += 2
          case 'b'  => scalars += '\b'; idx += 2
          case 'f'  => scalars += '\f'; idx += 2
          case 'n'  => scalars += '\n'; idx += 2
          case 'r'  => scalars += '\r'; idx += 2
          case 't'  => scalars += '\t'; idx += 2
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
              scalars += Character.toCodePoint(first.toChar, second.toChar)
              idx = secondEscape + 6
            } else if (Character.isLowSurrogate(first.toChar)) {
              invalid(idx, "unpaired low surrogate escape")
            } else {
              scalars += first
              idx += 6
            }
          case _ => invalid(idx + 1, "invalid string escape")
        }
      } else if (Character.isHighSurrogate(ch)) {
        if (idx + 1 >= input.length || !Character.isLowSurrogate(input.charAt(idx + 1)))
          invalid(idx, "unpaired high surrogate in string literal")
        scalars += Character.toCodePoint(ch, input.charAt(idx + 1))
        idx += 2
      } else if (Character.isLowSurrogate(ch)) {
        invalid(idx, "unpaired low surrogate in string literal")
      } else if (ch < 0x20) {
        invalid(idx, "unescaped control character in string literal")
      } else {
        scalars += ch.toInt
        idx += 1
      }
    }
    invalid(idx, "unterminated string literal")
  }

  def renderQuoted(scalars: Vector[Int]): String = {
    val out = new StringBuilder("\"")
    scalars.foreach { scalar =>
      require(isScalar(scalar), s"Cannot render non-Unicode scalar $scalar")
      scalar match {
        case '"'                       => out.append("\\\"")
        case '\\'                      => out.append("\\\\")
        case '\b'                      => out.append("\\b")
        case '\f'                      => out.append("\\f")
        case '\n'                      => out.append("\\n")
        case '\r'                      => out.append("\\r")
        case '\t'                      => out.append("\\t")
        case control if control < 0x20 => out.append(f"\\u$control%04x")
        case _                         => out.append(new String(Character.toChars(scalar)))
      }
    }
    out.append('"').result()
  }
}
