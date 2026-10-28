package com.raccoonlang.packed

import com.raccoonlang.{Kernel, NatNormalForm, UnicodeScalarString, Value}
import com.raccoonlang.Value._

import java.util.concurrent.atomic.AtomicReferenceArray

/**
 * Kernel `Char` and `String` values (docs/packed_lists.md, "Kernel strings"): literal construction, interning of closed
 * characters, and reading a value back as text. `Char.mk` is unconstrained, so a character is text only when its code
 * is a closed Unicode scalar value.
 */
private[raccoonlang] object Strings {
  import UnicodeScalarString.{MaxScalar, isScalar}

  /**
   * Interned characters: every `Char.mk` of a closed code at most `MaxScalar`, surrogates included, is one value per
   * code, so literals and decoded strings share their characters. The table has two levels: pages of 4096 codes, each
   * allocated when its first character is built, so a run that uses only ASCII holds one page. Larger codes are never
   * scalars and are not interned, which bounds the table at 272 pages.
   */
  private val PageBits = 12
  private val PageSize = 1 << PageBits
  private val pages = new AtomicReferenceArray[AtomicReferenceArray[Value]]((MaxScalar >>> PageBits) + 1)

  /** The code of a `Char.mk` field when it is a closed numeral at most `MaxScalar`, otherwise -1. */
  private def internableCode(field: Value): Int =
    field match {
      case poly: VNatPoly if poly.form.terms.isEmpty && poly.form.constant <= MaxScalar => poly.form.constant.toInt
      case VCtor(_, _, _) => 0 // Nat's only stored constructor is zero
      case _              => -1
    }

  // The interned character of `code`, made by `make` when it has none yet; a lost race returns the winner's value.
  private def interned(code: Int, make: => Value): Value = {
    val pageIndex = code >>> PageBits
    var page = pages.get(pageIndex)
    if (page == null) {
      pages.compareAndSet(pageIndex, null, new AtomicReferenceArray[Value](PageSize))
      page = pages.get(pageIndex)
    }
    val slot = code & (PageSize - 1)
    val known = page.get(slot)
    if (known != null) known
    else {
      val made = make
      if (page.compareAndSet(slot, null, made)) made else page.get(slot)
    }
  }

  /**
   * `Char.mk(field)` of type `tpe`, for ConstructorValue: interned when `field` is a closed code at most `MaxScalar`.
   * `head` is the kernel's `Char.mk` and `tpe` the kernel's `Char`, the only values of their names.
   */
  def char(head: ConstructorHead, field: Value, tpe: Value): Value = {
    val code = internableCode(field)
    if (code < 0) VCtor(head, Vector(field), tpe) else interned(code, VCtor(head, Vector(field), tpe))
  }

  private def charOf(scalar: Int): Value =
    interned(scalar, VCtor(Kernel.charMk, Vector(NatNormalForm.literal(BigInt(scalar))), Kernel.charType))

  /**
   * The value of a literal whose decoded text is `text`: `String.mk` of `nil`, or of one segment of interned characters
   * that fills its own chunk (`Words.filled`).
   */
  def literal(text: String): Value = {
    val scalars = text.codePoints().toArray
    val data =
      if (scalars.isEmpty) Kernel.charListNil
      else {
        val layers = new Array[Value](scalars.length)
        var index = 0
        while (index < scalars.length) {
          layers(index) = charOf(scalars(index))
          index += 1
        }
        Words.filled(Kernel.listCons, Kernel.charListType, layers, Kernel.charListNil)
      }
    VCtor(Kernel.stringMk, Vector(data), Kernel.stringType)
  }

  /** The scalar of a closed character whose code is a Unicode scalar value, otherwise -1. */
  def scalar(value: Value): Int =
    value match {
      case VCtor(head, fields, _) if head.name == Kernel.CharMkName =>
        val code = internableCode(fields.head)
        if (isScalar(code)) code else -1
      case _ => -1
    }

  /** The text of a `List(Char)` that ends in `nil` and whose every element is a closed scalar character. */
  private def text(list: Value): Option[String] =
    list match {
      case word: VWord if Kernel.isListNil(word.repr.terminator) =>
        val out = new java.lang.StringBuilder
        Words.segments(word).foreach { rest =>
          val segment = rest.repr
          var slot = segment.start
          while (slot < segment.end) {
            val code = scalar(segment.chunk.payload(slot, 0))
            if (code < 0) return None
            out.appendCodePoint(code)
            slot += 1
          }
        }
        Some(out.toString)
      case nil if Kernel.isListNil(nil) => Some("")
      case _                            => None
    }

  /** A `String.mk` whose list ends in `nil` and holds only closed scalar characters, as its text. */
  object Literal {
    def unapply(value: Value): Option[String] =
      value match {
        case VCtor(head, fields, _) if head.name == Kernel.StringMkName => text(fields.head)
        case _                                                          => None
      }
  }
}
