package com.raccoonlang

import com.raccoonlang.Value.{VCtor, VPacked}

/**
 * Printing a `String` (PROOF_BY_EVALUATION §2.2): one whose characters are all known prints as a literal, whether it
 * was written or computed, however long it is.
 */
class StringPrintingTests extends munit.FunSuite with TestSupport {
  private def stringPrelude(charOfNat: String): Prelude.Config =
    Prelude.fromSource(
      "strings",
      TestSupport.bundledPreludeSource + TestSupport.stringLayoutSource(charOfNat),
      Set(Prelude.ImportPath)
    )

  override protected lazy val suitePrelude: Prelude.Config = stringPrelude("Char.mk(value)")

  private def strings: Option[Value.ValidatedStringLayout] = suitePrelude.checkedEnv.nativeLiterals.stringLayout

  /** A `String` expression computed from the text's scalars, one `Char.ofNat` each, with no literal in it. */
  private def computed(text: String): String = {
    val chars =
      text.codePoints().toArray.foldRight("List.nil(Char)")((scalar, rest) => s"List.cons(Char.ofNat($scalar), $rest)")
    s"String.mk($chars)"
  }

  /** The time `body` takes, in milliseconds, with its result. */
  private def timed[A](body: => A): (A, Long) = {
    val start = System.nanoTime()
    val result = body
    (result, (System.nanoTime() - start) / 1000000)
  }

  test("a computed String prints as the literal a written one does, and the literal reads back as it") {
    val cases = Vector(
      s"{ ${computed("hi")} }" -> "\"hi\"",
      s"{ ${computed("")} }" -> "\"\"",
      "{ String.append(\"ab\", \"cd\") }" -> "\"abcd\"",
      "{ String.append(\"\", \"cd\") }" -> "\"cd\"",
      s"{ String.append(${computed("ab")}, \"cd\") }" -> "\"abcd\"",
      s"{ String.append(\"ab\", ${computed("cd")}) }" -> "\"abcd\""
    )
    cases.foreach { case (source, printed) =>
      val value = runProgram(source)
      assertEquals(PrettyPrinter.print(value, strings), printed)
      assert(ValueEquivalence.defEq(runProgram(s"{ $printed }"), value), source)
    }
  }

  test("a computed String escapes exactly as a written literal prints") {
    val text = "q\"b\\n\nt\tr\rb\bf\f\u0001\u001f/\u007fλ😀"
    val printed = "\"q\\\"b\\\\n\\nt\\tr\\rb\\bf\\f\\u0001\\u001f/\u007fλ😀\""
    val value = runProgram(s"{ ${computed(text)} }")
    assertEquals(PrettyPrinter.print(value, strings), printed)
    assertEquals(PrettyPrinter.print(runProgram(s"{ $printed }")), printed)
    assert(ValueEquivalence.defEq(runProgram(s"{ $printed }"), value))
    assertEquals(PrettyPrinter.rawString(value, strings), Some(text))
  }

  test("a String with a character not known prints as its constructors") {
    // A neutral character, a character that is not `Char.ofNat` of any scalar, and a surrogate, which is no scalar.
    val cases = Vector(
      "{ String.mk(List.cons(Char.ofNat(97), List.cons(someChar, List.nil(Char)))) }" ->
        "String.mk(List.cons(Char.mk(97), List.cons(someChar, List.nil)))",
      "{ String.append(\"a\", String.mk(List.cons(someChar, List.nil(Char)))) }" ->
        "String.mk(List.cons(Char.mk(97), List.cons(someChar, List.nil)))",
      "{ String.mk(List.cons(Char.ofNat(55296), List.nil(Char))) }" ->
        "String.mk(List.cons(Char.mk(55296), List.nil))",
      "{ String.mk(List.cons(Char.ofNat(1114112), List.nil(Char))) }" ->
        "String.mk(List.cons(Char.mk(1114112), List.nil))"
    )
    cases.foreach { case (source, printed) =>
      val value = runProgram(source)
      assertEquals(PrettyPrinter.print(value, strings), printed)
      assertEquals(PrettyPrinter.rawString(value, strings), None)
    }
    val open = expectTypeError[TypeMismatch](
      "def bad (s: String): Eq(String, String.append(\"x\", s), \"y\") := Eq.refl(\"y\")\n"
    )
    assertEquals(
      PrettyPrinter.print(open.expected, strings),
      "Eq(String, String.mk(List.cons(Char.mk(120), String.data(s))), \"y\")"
    )
  }

  test("without the String layout, only a packed String prints as a literal, as before") {
    val cases = Vector(
      "{ \"hi\" }" -> "\"hi\"",
      s"{ ${computed("hi")} }" -> "String.mk(List.cons(Char.mk(104), List.cons(Char.mk(105), List.nil)))",
      s"{ ${computed("")} }" -> "String.mk(List.nil)",
      "{ String.append(\"ab\", \"cd\") }" ->
        "String.mk(List.cons(Char.mk(97), List.cons(Char.mk(98), proj[String,0](\"cd\"))))"
    )
    cases.foreach { case (source, printed) =>
      val value = runProgram(source)
      assertEquals(PrettyPrinter.print(value), printed)
      assertEquals(PrettyPrinter.print(value, None), printed)
    }
    assertEquals(PrettyPrinter.rawString(runProgram("{ \"hi\" }"), None), Some("hi"))
    assertEquals(PrettyPrinter.rawString(runProgram(s"{ ${computed("hi")} }"), None), None)
  }

  test("a character is known only as `Char.ofNat` makes it") {
    // Here `Char.ofNat(s)` is `Char.mk(s + 1)`, so `Char.mk(98)` is the character of scalar 97, and reading it as 98
    // would print a literal that reads back as another String.
    val shifted = stringPrelude("Char.mk(Nat.succ(value))")
    val layout = shifted.checkedEnv.nativeLiterals.stringLayout
    val value = runProgram(s"{ ${computed("ab")} }", shifted)
    assertEquals(
      PrettyPrinter.print(value, layout),
      "String.mk(List.cons(Char.mk(98), List.cons(Char.mk(99), List.nil)))"
    )
    assertEquals(PrettyPrinter.rawString(value, layout), None)
    assertEquals(PrettyPrinter.print(runProgram("{ \"ab\" }", shifted), layout), "\"ab\"")
  }

  test("only a String prints raw") {
    assertEquals(PrettyPrinter.rawString(runProgram(s"{ ${computed("a\"\n")} }"), strings), Some("a\"\n"))
    assertEquals(PrettyPrinter.rawString(runProgram("{ \"\" }"), strings), Some(""))
    assertEquals(PrettyPrinter.rawString(runProgram("{ 5 }"), strings), None)
    assertEquals(PrettyPrinter.rawString(runProgram("{ Char.ofNat(97) }"), strings), None)
    assertEquals(PrettyPrinter.rawString(runProgram("{ List.cons(Char.ofNat(97), List.nil(Char)) }"), strings), None)
    assertEquals(
      PrettyPrinter.print(runProgram("{ List.cons(\"a\", List.nil(String)) }"), strings),
      "List.cons(\"a\", List.nil)"
    )
  }

  test("a computed String of a million characters prints in linear time and no host stack") {
    val sample = runProgram(s"{ ${computed("a")} }")
    val (stringMk, cons, nil, charMk, charTpe, natTpe, listTpe, stringTpe) = sample match {
      case VCtor(
            stringMk,
            Vector(VCtor(cons, Vector(char @ VCtor(charMk, Vector(code: VPacked), _), nil), listTpe)),
            stringTpe
          ) =>
        (stringMk, cons, nil, charMk, char.tpe, code.tpe, listTpe, stringTpe)
      case other => fail(s"Expected a one-character computed String, got $other")
    }
    def textOf(length: Int): Vector[Char] = Vector.tabulate(length)(idx => "ab\"\\\nλ".charAt(idx % 6))
    def stringOf(text: Vector[Char]): Value = {
      val chars = text.reverseIterator.foldLeft(nil) { (rest, char) =>
        VCtor(cons, Vector(VCtor(charMk, Vector(VPacked.nat(BigInt(char.toInt), natTpe)), charTpe), rest), listTpe)
      }
      VCtor(stringMk, Vector(chars), stringTpe)
    }
    // The first print of a short one compiles the printer, so what is timed is printing itself.
    onDefaultStack(PrettyPrinter.print(stringOf(textOf(10000)), strings))
    onDefaultStack(PrettyPrinter.rawString(stringOf(textOf(10000)), strings))
    val length = 1000000
    val text = textOf(length)
    val string = stringOf(text)
    val (printed, printMillis) = onDefaultStack(timed(PrettyPrinter.print(string, strings)))
    assertEquals(printed, UnicodeScalarString.renderQuoted(text.map(_.toInt)))
    assert(printMillis < 1000, s"printing took $printMillis ms")
    val (raw, rawMillis) = onDefaultStack(timed(PrettyPrinter.rawString(string, strings)))
    assertEquals(raw, Some(text.mkString))
    assert(rawMillis < 1000, s"reading raw took $rawMillis ms")
    // Without the layout, it prints as its constructors, as deep as it is long.
    val (tree, treeMillis) = onDefaultStack(timed(PrettyPrinter.print(string)))
    assert(tree.startsWith("String.mk(List.cons(Char.mk(97), List.cons(Char.mk(98), List.cons(Char.mk(34), "))
    assert(tree.endsWith(")" * (length + 1)))
    assert(treeMillis < 5000, s"printing constructors took $treeMillis ms")
  }
}
