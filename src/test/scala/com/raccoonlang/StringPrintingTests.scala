package com.raccoonlang

import com.raccoonlang.Value.{VCtor, VPacked}
import com.raccoonlang.telescope.Projection

import java.nio.file.{Files, Paths}

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

  test("native String.append preserves its source constructor and packed-suffix boundaries") {
    val cases = Vector(
      "{ String.append(\"a\", String.append(\"b\", \"c\")) }" ->
        "String.mk(List.cons(Char.mk(97), List.cons(Char.mk(98), proj[String,0](\"c\"))))",
      "{ String.append(String.append(\"a\", \"b\"), \"c\") }" ->
        "String.mk(List.cons(Char.mk(97), List.cons(Char.mk(98), proj[String,0](\"c\"))))",
      "{ String.append(\"x\", String.mk(List.cons(Char.ofNat(66), (\"😀\").data))) }" ->
        "String.mk(List.cons(Char.mk(120), List.cons(Char.mk(66), proj[String,0](\"😀\"))))",
      "{ String.append(String.mk(List.cons(Char.ofNat(65), (\"😀\").data)), \"z\") }" ->
        "String.mk(List.cons(Char.mk(65), List.cons(Char.mk(128512), proj[String,0](\"z\"))))",
      "{ String.append(\"\", \"cd\") }" -> "\"cd\"",
      "{ String.append(\"a\", \"\") }" ->
        "String.mk(List.cons(Char.mk(97), proj[String,0](\"\")))",
      "{ String.append(\"a\", String.mk(List.nil(Char))) }" ->
        "String.mk(List.cons(Char.mk(97), List.nil))"
    )
    cases.foreach { case (source, printed) =>
      val enabled = runProgram(source)
      val disabled = Packed.withOpsDisabled(runProgram(source))
      assert(ValueEquivalence.defEq(enabled, disabled), source)
      assertEquals(PrettyPrinter.print(enabled, None), printed, source)
      assertEquals(PrettyPrinter.print(enabled, None), PrettyPrinter.print(disabled, None), source)
    }
  }

  test("decoded tails of an appended packed list print like source evaluation without a layout") {
    val env = suitePrelude.checkedEnv
    val stringMk = env("String.mk").asInstanceOf[Value.ConstructorHead]
    val source = "{ String.append(\"ab\", \"cd\") }"
    var enabledData = runProgram(source) match {
      case Value.VCtor(head, Vector(data), _) if head eq stringMk => data
      case other                                                  => fail(s"Expected String.mk, got $other")
    }
    var disabledData = Packed.withOpsDisabled(runProgram(source)) match {
      case Value.VCtor(head, Vector(data), _) if head eq stringMk => data
      case other                                                  => fail(s"Expected String.mk, got $other")
    }

    def tail(data: Value): Value =
      data match {
        case packed: Value.VPacked                                             => Value.VPacked.charListTail(packed)
        case Value.VCtor(head, Vector(_, rest), _) if head.name == "List.cons" => rest
        case other => fail(s"Expected nonempty List Char, got $other")
      }

    (0 to 4).foreach { depth =>
      val enabled = Interpreter.evalApply(stringMk, Vector(enabledData))
      val disabled = Interpreter.evalApply(stringMk, Vector(disabledData))
      assertEquals(PrettyPrinter.print(enabled, None), PrettyPrinter.print(disabled, None), s"tail depth $depth")
      if (depth < 4) {
        enabledData = tail(enabledData)
        disabledData = tail(disabledData)
      }
    }
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

  /**
   * The rejection of `program` as the text report and as the JSON report, each printing values with the String layout
   * that checking hands back with its diagnostics.
   */
  private def reports(program: String): (String, String) = {
    val sources = Vector(ModuleLoader.LoadedSource(SourceId.fresh(), Paths.get("main.rac"), program))
    try {
      typecheckDecls(program)
      fail("expected the program to be rejected")
    } catch {
      case Execution.CheckFailure(diagnostics, reported) =>
        assertEquals(reported, strings)
        (ErrorReporter.pretty(diagnostics, sources, reported), DiagnosticJson.render(diagnostics, sources, reported))
    }
  }

  /** `text` as a JSON string's contents. */
  private def escaped(text: String): String = text.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n")

  test("a diagnostic prints a computed String as a literal, in the text report and in JSON alike") {
    val list = s"List.cons(${computed("ab")}, List.nil(String))"
    val (mismatchText, mismatchJson) =
      reports(s"def bad : Eq(List(String), $list, List.nil(String)) := Eq.refl(List.nil(String))\n")
    val mismatchDetail =
      "\n  expected: Eq(List(String), List.cons(\"ab\", List.nil), List.nil)" +
        "\n  actual:   Eq(List(String), List.nil, List.nil)" +
        "\n  differ at: List.cons(\"ab\", List.nil)  vs  List.nil   (not reducible: stuck)"
    assert(mismatchText.contains("error: type mismatch\n"), mismatchText)
    assert(mismatchText.contains(s"$mismatchDetail\n"), mismatchText)
    assert(mismatchJson.contains(s"\"message\": \"${escaped("type mismatch" + mismatchDetail)}\""), mismatchJson)

    val (evidenceText, evidenceJson) =
      reports(s"def needs (s: String)[ok: Eq(String, s, \"ok\")]: Nat := 0\n{ needs(${computed("no")}) }\n")
    val evidenceMessage =
      "Evidence ok of needs is not discharged: its proposition is Eq(String, \"no\", \"ok\"), which no constructor " +
        "proves with the fields its type determines; supply a proof as needs(…)[proof]"
    assert(evidenceText.contains(s"error: $evidenceMessage\n"), evidenceText)
    assert(evidenceJson.contains(s"\"message\": \"${escaped(evidenceMessage)}\""), evidenceJson)

    // A part a declared kind must contain is named with its type.
    val (partsText, _) = reports(
      "inductive Tok (s: String) : Type { kind = lin }\n | mk : Tok(s)\n" +
        "def eat {s: String}(t: Tok(s)): Nat := match t returning Nat with\n | Tok.mk => 0\n" +
        s"def delay (t: Tok(${computed("a")})): { kind = lin } Unit -> Nat :=\n" +
        "  fun { kind = unr } (u: Unit): Nat => eat(t)\n" +
        s"inductive Holder : Type\n | mk (held: Tok(${computed("b")})) : Holder\n"
    )
    assert(partsText.contains("of capture t : Tok(\"a\")\n"), partsText)
    assert(partsText.contains("of field Holder.mk.held : Tok(\"b\")\n"), partsText)
  }

  test("a diagnostic prints a String with a character not known as its constructors") {
    val (text, json) = reports(
      "def needs (s: String)[ok: Eq(String, s, \"ok\")]: Nat := 0\n" +
        "{ needs(String.mk(List.cons(Char.ofNat(111), List.cons(someChar, List.nil(Char))))) }\n"
    )
    val proposition = "Eq(String, String.mk(List.cons(Char.mk(111), List.cons(someChar, List.nil))), \"ok\")"
    assert(text.contains(s"its proposition is $proposition, "), text)
    assert(json.contains(s"its proposition is ${escaped(proposition)}, "), json)
  }

  test("every value a diagnostic holds prints with the layout, so a String among them prints as a literal") {
    val ab = runProgram(s"{ ${computed("ab")} }")
    // A function type whose binder's type names a local bound to the String.
    val pi = runProgram(s"{\n  let s := ${computed("ab")}\n  fun (x: Eq(String, s, s)): Nat => 0\n}\n").tpe match {
      case pi: Value.VPi => pi
      case other         => fail(s"Expected a function type, got $other")
    }
    val span = Span(0, 0)
    val failures = Vector(
      Projection.Failure.NotALevel(ab),
      Projection.Failure.NotAnApplication("Box", ab),
      Projection.Failure.NotAConstructor("Box.mk", ab),
      Projection.Failure.NotASort(ab),
      Projection.Failure.NotAFunctionType(ab),
      Projection.Failure.DependentDomain(0, pi),
      Projection.Failure.DependentCodomain(pi),
      Projection.Failure.DependentResult(pi)
    )
    val parts = Vector(ContainedPart.Capture("t", ab), ContainedPart.Field("Box.mk.a", ab))
    val errors = Vector(
      CannotApplyNonFunction(ab),
      NotAType(ab),
      NonInductiveMatch(ab),
      NotDestructurable(ab),
      TypeMismatch(ab, ab, Some(ValueEquivalence.UnifyFailure(ab, ab, apart = true))),
      InvalidConstructorResult("Box.mk", "Box", ab),
      NotAProposition("h", ab),
      EvidenceNotDischarged("h", "f", Vector.empty, ab, EvidenceNotDischarged.NoConstructor),
      NonUniformInductiveParam("Box", "Box.mk", "A", ab),
      InductiveUniverseTooSmall("Box", "field a", ab, Value.Level.one, Value.Level.one),
      InductiveTypeNotASort(ab),
      LinearInType(CoreAst.Term.GlobalRef("t", span), ab),
      LinearGlobal(None, ab),
      NonStrictlyPositive("Box", "Box.mk", "a", ab),
      PropEliminationRestricted("Box", ab),
      NonInductiveDecreaseMetric(ab, isProof = true),
      NonInductiveDecreaseMetric(ab, isProof = false)
    ) ++ failures.map(ImplicitReconstructionFailed("A", "f", _)) ++
      parts.map(KindExceeded("Box", Value.Kind.unr, _, Value.Kind.lin))
    errors.foreach { error =>
      val message = ErrorRendering.render(error, strings)
      assert(message.contains("\"ab\"") && !message.contains("String.mk"), message)
    }

    // Every class of Errors.scala and of Projection.scala with a field of type `Value` or `VPi`, or an `Option` of
    // one, is among those above. The three that hold a value only through a part or a failure are too.
    def holdingValues(file: String, parents: String): Set[String] =
      raw"final case class (\w+)\(([^)]*)\)\s*extends ($parents)\b".r
        .findAllMatchIn(Files.readString(Paths.get("src/main/scala/com/raccoonlang", file)))
        .filter(m => raw":\s*(Option\[)?(Value|VPi)\b(?!\.)".r.findFirstIn(m.group(2)).nonEmpty)
        .map(_.group(1))
        .toSet
    assertEquals(
      holdingValues("Errors.scala", "TypeError|ContainedPart") ++
        holdingValues("telescope/Projection.scala", "Failure"),
      (errors ++ parts ++ failures).map(_.productPrefix).toSet --
        Set("ImplicitReconstructionFailed", "KindExceeded")
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
    // The bounds catch a printer that is not linear, without flaking under load: the recursive, quadratic printer took
    // 45 s for 100k characters, so over an hour for this. PROOF_BY_EVALUATION §2.6's under-a-second target is measured
    // by hand.
    val (printed, printMillis) = onDefaultStack(timed(PrettyPrinter.print(string, strings)))
    assertEquals(printed, UnicodeScalarString.renderQuoted(text.map(_.toInt)))
    assert(printMillis < 10000, s"printing took $printMillis ms")
    val (raw, rawMillis) = onDefaultStack(timed(PrettyPrinter.rawString(string, strings)))
    assertEquals(raw, Some(text.mkString))
    assert(rawMillis < 10000, s"reading raw took $rawMillis ms")
    // Without the layout, it prints as its constructors, as deep as it is long.
    val (tree, treeMillis) = onDefaultStack(timed(PrettyPrinter.print(string)))
    assert(tree.startsWith("String.mk(List.cons(Char.mk(97), List.cons(Char.mk(98), List.cons(Char.mk(34), "))
    assert(tree.endsWith(")" * (length + 1)))
    assert(treeMillis < 30000, s"printing constructors took $treeMillis ms")
  }
}
