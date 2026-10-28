package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.Value._
import com.raccoonlang.packed.{Storage, Strings, Words}

class KernelStringTests extends munit.FunSuite {
  private def parse(src: String): SurfaceAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) => value
      case err: Failure         => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def elabAndRun(src: String, prelude: Prelude.Config = Prelude.default): Env = {
    val core = Elaborator.elab(parse(src), prelude)
    try
      core.decls.foldLeft(Interpreter.initialEnv(prelude)) { case (env, decl) =>
        Interpreter.evalDecl(decl, env)
      }
    catch { case t: TypeError => fail(ErrorReporter.pretty(t, Source(src))) }
  }

  private def runProgram(src: String): Value = {
    val core = Elaborator.elab(parse(src), Prelude.default)
    try Interpreter.run(core, Prelude.default).getOrElse(fail("Program has no body"))
    catch { case t: TypeError => fail(ErrorReporter.pretty(t, Source(src))) }
  }

  private def typeError[T <: TypeError](src: String)(implicit ct: reflect.ClassTag[T]): T =
    intercept[T] {
      val core = Elaborator.elab(parse(src), Prelude.default)
      Interpreter.run(core, Prelude.default)
    }

  private def code(n: Int): Value = NatNormalForm.literal(BigInt(n))

  private def char(n: Int): Value = ConstructorValue(Kernel.charMk, Vector(code(n)), Kernel.charType)

  private def consChar(element: Value, tail: Value): Value =
    ConstructorValue(Kernel.listCons, Vector(element, tail), Kernel.charListType)

  /** The characters of `text` as a list built cons by cons. */
  private def consList(text: String): Value =
    text.codePoints().toArray.foldRight(Kernel.charListNil)((scalar, tail) => consChar(char(scalar), tail))

  private def string(data: Value): Value = ConstructorValue(Kernel.stringMk, Vector(data), Kernel.stringType)

  private def literal(text: String): Value = Strings.literal(text)

  private def dataOf(value: Value): Value =
    value match {
      case VCtor(head, Vector(data), _) if head eq Kernel.stringMk => data
      case other                                                   => fail(s"Expected String.mk, got $other")
    }

  private def append(l: Value, r: Value): Value = Words.append(l, r)

  private def assertSameString(left: Value, right: Value): Unit = {
    assert(ValueEquivalence.defEq(left, right), s"$left and $right do not convert")
    assert(ValueEquivalence.defEq(right, left))
    assertEquals(left.key, right.key)
    assertEquals(left.toString, right.toString)
  }

  private def quoteClosed(value: Value): ElabAst.Term =
    ValueQuote.quoteTerm(value, ValueQuote.QuoteContext(Map.empty, 0), Span(0, 0))

  private lazy val env: Env = Interpreter.initialEnv(Prelude.default)

  // ------------ Literal syntax ------------

  test("literals decode JSON-style escapes and Unicode scalar values") {
    val cases = Vector(
      "\"\"" -> "",
      "\"hi\"" -> "hi",
      "\"q\\\"b\\\\s\\/n\\b\\f\\n\\r\\t\"" -> "q\"b\\s/n\b\f\n\r\t",
      "\"\\u00e9\\u0001\\uFFFF\"" -> "\u00e9\u0001\uffff",
      "\"\\ud83d\\ude00\"" -> "\ud83d\ude00",
      "\"λ😀\u007f\"" -> "λ😀\u007f"
    )
    cases.foreach { case (source, text) =>
      runProgram(s"{ $source }") match {
        case Strings.Literal(decoded) => assertEquals(decoded, text, source)
        case other                    => fail(s"$source evaluated to $other")
      }
    }
  }

  test("malformed literals are parse errors at the offending character or escape") {
    val cases = Vector(
      "{ \"a\\x\" }" -> (5, "invalid string escape"),
      "{ \"a\\u12G4\" }" -> (8, "invalid hexadecimal digit in Unicode escape"),
      "{ \"a\\u12\" }" -> (8, "invalid hexadecimal digit in Unicode escape"),
      "{ \"\\ud800\" }" -> (3, "high surrogate escape is not followed by a low surrogate escape"),
      "{ \"\\ud800\\u0041\" }" -> (9, "high surrogate escape is not followed by a low surrogate"),
      "{ \"\\udc00\" }" -> (3, "unpaired low surrogate escape"),
      "{ \"a\ud800b\" }" -> (4, "unpaired high surrogate in string literal"),
      "{ \"a\udc00\" }" -> (4, "unpaired low surrogate in string literal"),
      "{ \"a\nb\" }" -> (4, "unescaped control character in string literal"),
      "{ \"a\tb\" }" -> (4, "unescaped control character in string literal"),
      "{ \"ab" -> (5, "unterminated string literal"),
      "{ \"ab\\" -> (5, "unterminated string escape")
    )
    cases.foreach { case (source, (offset, message)) =>
      LanguageParser.parseProgram(source) match {
        case Failure(_, curIdx, actual) =>
          assertEquals(actual, message, source)
          assertEquals(curIdx, offset, source)
        case success => fail(s"$source parsed as $success")
      }
    }
  }

  test("a literal has type String whatever is expected, in terms and in types") {
    val loaded = elabAndRun(
      "inductive Tag (s: String) : Type\n | mk {s: String} : Tag(s)\n\n" +
        "def tagged : Tag(\"a\") := Tag.mk(\"a\")\n" +
        "def s : String := \"x\"\n"
    )
    assert(ValueEquivalence.defEq(loaded("s").tpe, Kernel.stringType))
    assertEquals(loaded("tagged").tpe.toString, "Tag(\"a\")")
    typeError[TypeMismatch]("def n : Nat := \"x\"\n")
    typeError[TypeMismatch]("def l : List(Char) := \"x\"\n")
  }

  test("Char and String are kernel declarations: present without a prelude and not redeclarable") {
    intercept[AlreadyDefined] {
      Elaborator.elab(parse("struct String : Type\n | mk (n: Nat) : String\n"), Prelude.none)
    }
    intercept[AlreadyDefined] {
      Elaborator.elab(parse("inductive Char : Type\n | a : Char\n"), Prelude.none)
    }
    val loaded = elabAndRun("def d : List(Char) := String.data(\"ab\")\n", Prelude.none)
    assertEquals(loaded("d").key, dataOf(literal("ab")).key)
  }

  // ------------ Values ------------

  test("a literal is String.mk of one segment that fills its chunk") {
    dataOf(literal("héllo😀")) match {
      case data: VWord =>
        assertEquals(Storage.segments(data).length, 1)
        val segment = Storage.segment(data)
        assertEquals((segment.start, segment.end, Storage.layers(data)), (0, 6, 6L))
        assertEquals((segment.front, segment.back, segment.capacity), (0, 6, 6))
        assert(Kernel.isListNil(segment.next))
      case other => fail(s"Expected a word, got $other")
    }
    assert(Kernel.isListNil(dataOf(literal(""))))
  }

  test("a literal converts with the same string built by cons and by append, with equal keys") {
    val previous = Words.verifyKeys
    Words.verifyKeys = true
    try {
      val texts = Vector("", "a", "ab", "héllo, wörld", "😀λ\n\"", "x" * 40)
      texts.foreach { text =>
        val lit = literal(text)
        assertSameString(lit, string(consList(text)))
        val scalars = text.codePoints().toArray
        (0 to scalars.length).foreach { split =>
          val left = new String(scalars, 0, split)
          val right = new String(scalars, split, scalars.length - split)
          assertSameString(lit, string(append(dataOf(literal(left)), dataOf(literal(right)))))
          assertSameString(lit, string(append(consList(left), dataOf(literal(right)))))
          assertSameString(lit, string(append(dataOf(literal(left)), consList(right))))
        }
      }
      assert(!ValueEquivalence.defEq(literal("ab"), literal("ba")))
      assertNotEquals(literal("ab").key, literal("ba").key)
      assert(!ValueEquivalence.defEq(literal("ab"), literal("abc")))
    } finally Words.verifyKeys = previous
  }

  test("String.append of literals converts with the concatenated literal, and String.length computes") {
    val appended = runProgram("{ String.append(\"ab\", String.append(\"\", \"cd😀\")) }")
    assertSameString(appended, runProgram("{ \"abcd😀\" }"))
    assertEquals(appended.toString, "\"abcd😀\"")
    val length = runProgram("{ String.length(\"héllo😀\") }")
    assertEquals(length.key, code(6).key)
    assert(ValueEquivalence.defEq(length, code(6)))
    assertEquals(runProgram("{ String.length(String.append(\"ab\", \"\")) }").key, code(2).key)
  }

  test("closed characters are interned, so literals and constructed strings share them") {
    def chars(value: Value): Vector[Value] = {
      val result = Vector.newBuilder[Value]
      Words.foreach(dataOf(value).asInstanceOf[VWord])(
        layer = token => {
          result += token.payload(0)
          true
        },
        end = _ => true
      )
      result.result()
    }
    val ab = chars(literal("ab"))
    val ba = chars(runProgram("{ \"ba\" }"))
    assert(ab(0) eq ba(1))
    assert(ab(1) eq ba(0))
    assert(char('a'.toInt) eq ab(0))
    assert(char(0x1f600) eq chars(literal("😀"))(0))
    // A character built by source, from a closed numeral, is the same object too.
    assert(runProgram("{ Char.mk(Nat.zero) }") eq chars(literal("\u0000"))(0))
    assert(runProgram("{ Char.mk(Nat.succ(Nat.zero)) }") eq char(1))
    // Codes beyond the last scalar are not interned; surrogate codes are.
    assert(char(0xd800) eq char(0xd800))
    assert(!(char(0x110000) eq char(0x110000)))
    assert(ValueEquivalence.defEq(char(0x110000), char(0x110000)))
  }

  // ------------ Conversion in programs ------------

  test("Eq.refl is accepted between equal strings built differently and rejected between different ones") {
    elabAndRun(
      "def p1 : Eq(String, String.append(\"ab\", \"cd\"), \"abcd\") := Eq.refl(\"abcd\")\n" +
        "def p2 : Eq(String, String.mk(List.cons(Char.mk(Nat.zero), String.data(\"a\"))), \"\\u0000a\") := " +
        "Eq.refl(\"\\u0000a\")\n" +
        "def p3 : Eq(String, String.mk(List.append(String.data(\"a\"), List.nil(Char))), \"a\") := Eq.refl(\"a\")\n" +
        "def p4 (s: String): Eq(String, String.append(String.append(\"a\", s), \"c\"), " +
        "String.append(\"a\", String.append(s, \"c\"))) := Eq.refl(String.append(\"a\", String.append(s, \"c\")))\n" +
        "def p5 : Eq(Nat, String.length(\"abc\"), Nat.succ(Nat.succ(Nat.succ(Nat.zero)))) := " +
        "Eq.refl(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))\n"
    )
    typeError[TypeMismatch]("def bad : Eq(String, \"ab\", \"ba\") := Eq.refl(\"ab\")\n")
    typeError[TypeMismatch]("def bad : Eq(String, \"ab\", \"abc\") := Eq.refl(\"ab\")\n")
    typeError[TypeMismatch]("def bad : Eq(String, String.append(\"a\", \"b\"), \"a\") := Eq.refl(\"a\")\n")
  }

  // ------------ Printing ------------

  test("strings of closed scalar characters print as literals that read back as the same value") {
    val texts = Vector("", "hi", "q\"b\\n\nt\tr\rb\bf\f\u0001\u001f/\u007fλ😀")
    texts.foreach { text =>
      val built = string(consList(text))
      val printed = PrettyPrinter.print(built)
      assertEquals(printed, UnicodeScalarString.renderQuoted(text))
      assertSameString(runProgram(s"{ $printed }"), built)
      assertEquals(PrettyPrinter.print(runProgram(s"{ $printed }")), printed)
    }
    assertEquals(
      PrettyPrinter.print(literal("q\"\\\n\u0001")),
      "\"q\\\"\\\\\\n\\u0001\""
    )
  }

  test("a string with a character that is not a closed scalar prints structurally") {
    val surrogate = string(consChar(char('a'.toInt), consChar(char(0xd800), Kernel.charListNil)))
    assertEquals(PrettyPrinter.print(surrogate), "String.mk([Char.mk(97), Char.mk(55296)])")
    val tooLarge = string(append(dataOf(literal("b")), consChar(char(0x110000), Kernel.charListNil)))
    assertEquals(PrettyPrinter.print(tooLarge), "String.mk([Char.mk(98), Char.mk(1114112)])")
    // An open string: its list ends in a stuck value, here a selector application.
    val err = typeError[TypeMismatch](
      "def bad (s: String): Eq(String, String.append(\"x\", s), \"y\") := Eq.refl(\"y\")\n"
    )
    assert(err.getMessage.contains("String.mk([Char.mk(120)] ++ match#"), err.getMessage)
    assert(err.getMessage.contains("\"y\""), err.getMessage)
    // A bare List(Char) is a list, not a string.
    assertEquals(PrettyPrinter.print(dataOf(literal("ab"))), "[Char.mk(97), Char.mk(98)]")
  }

  // ------------ Quotation ------------

  test("closed character runs quote as string literals, and evaluating the quotation rebuilds the value") {
    def roundTrip(value: Value, expected: String): Unit = {
      val quoted = quoteClosed(value)
      assertEquals(quoted.toString, expected)
      val rebuilt = Interpreter.evalTerm(quoted, env)
      assertSameString(rebuilt, value)
    }
    roundTrip(literal("ab😀"), "\"ab😀\"")
    roundTrip(string(consList("hi\n")), "\"hi\\n\"")
    roundTrip(literal(""), "\"\"")
    roundTrip(dataOf(literal("ab")), "String.data(\"ab\")")
    roundTrip(consList("x"), "String.data(\"x\")")
    val mixed = append(
      dataOf(literal("ab")),
      consChar(char(0xd800), append(consChar(char(0x110000), Kernel.charListNil), dataOf(literal("c"))))
    )
    roundTrip(
      mixed,
      "List.append(String.data(\"ab\"), List.cons(Char.mk(55296), List.cons(Char.mk(1114112), String.data(\"c\"))))"
    )
    roundTrip(
      string(mixed),
      "String.mk(List.append(String.data(\"ab\"), List.cons(Char.mk(55296), List.cons(Char.mk(1114112), " +
        "String.data(\"c\")))))"
    )
    roundTrip(
      string(consChar(char(0xd800), Kernel.charListNil)),
      "String.mk(List.cons(Char.mk(55296), List.nil(Char)))"
    )
  }

  test("a run before a stuck end quotes as an append onto it") {
    val loaded = elabAndRun("axiom xs : List(Char)\n")
    val xs = loaded("xs")
    val value = append(dataOf(literal("ab")), xs)
    val quoted = quoteClosed(value)
    assertEquals(quoted.toString, "List.append(String.data(\"ab\"), xs)")
    assertSameString(Interpreter.evalTerm(quoted, loaded), value)
  }
}
