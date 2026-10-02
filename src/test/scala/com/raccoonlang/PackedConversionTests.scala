package com.raccoonlang

/**
 * Conversion against packed literals: its cost is linear in what the two sides share, and it tells literals that differ
 * apart from a comparison that is merely stuck.
 */
class PackedConversionTests extends munit.FunSuite with TestSupport {
  private def stringPrelude(charOfNat: String): Prelude.Config =
    Prelude.fromSource(
      "strings",
      TestSupport.bundledPreludeSource + TestSupport.stringLayoutSource(charOfNat),
      Set(Prelude.ImportPath)
    )

  override protected lazy val suitePrelude: Prelude.Config = stringPrelude("Char.mk(value)")

  private val lengths = Vector(24, 100, 1000)

  private def stringAppend(env: Env): Value.VLam =
    env("String.append") match {
      case lam: Value.VLam => lam
      case other           => fail(s"Expected String.append lambda, got $other")
    }

  private def printsAsString(value: Value, env: Env): String =
    PrettyPrinter.print(value, env.nativeLiterals.stringLayout)

  /** Evaluating `String.append` recurses once per character of its first argument, as checking the result does. */
  private def onLargeStack[A](body: => A): A = Execution.onStack(64L << 20)(body)

  /** A type mismatch, with the time checking `source` took to report it. */
  private def timedMismatch(source: String): (TypeMismatch, Long) =
    onLargeStack(timed(expectTypeError[TypeMismatch](source)))

  /** The two sides of the equation where a mismatch was found, expected first, and whether they are apart. */
  private def differAt(mismatch: TypeMismatch): (String, String, Boolean) = {
    val failure = mismatch.detail.getOrElse(fail("The mismatch has no detail"))
    (PrettyPrinter.print(failure.v2), PrettyPrinter.print(failure.v1), failure.apart)
  }

  // A computed list against a literal decodes the literal one layer per shared character, and the failure at the end
  // passes through each data layer. The outer Eq proposition is only a congruence frame, so the diagnostic is stuck.
  test("a failing conversion of a computed String against a literal is prompt however much text they share") {
    lengths.foreach { length =>
      val text = "a" * length
      val (literal, literalMillis) = timedMismatch(
        s"""def wrong : Eq(String, String.append("$text", "0"), "${text}1") := Eq.refl("${text}1")"""
      )
      assert(literalMillis < 10000, s"$length shared characters took $literalMillis ms")
      assertEquals(differAt(literal), ("proj[String,0](\"0\")", "proj[String,0](\"1\")", false))

      val (neutral, neutralMillis) = timedMismatch(
        s"""def wrong (s: String) : Eq(String, String.append("$text", s), "${text}1") := Eq.refl("${text}1")"""
      )
      assert(neutralMillis < 10000, s"$length shared characters before a variable took $neutralMillis ms")
      assertEquals(differAt(neutral), ("String.data(s)", "proj[String,0](\"1\")", false))
    }
  }

  test("a failing conversion of a successor chain against a Nat literal is prompt however long the chain") {
    // Up to the unfolding limit, `Nat.add(n, k)` is `k` successors of `n`. Its key decides the equation, and the
    // key-coherence assertion, on in every test, checks that verdict by the rules, which decode the literal one layer
    // per successor.
    Vector(24, 100, 256).foreach { k =>
      val (mismatch, millis) =
        timedMismatch(s"def wrong (n: Nat) : Eq(Nat, Nat.add(n, $k), ${k + 1}) := Eq.refl(${k + 1})")
      assert(millis < 10000, s"$k successors took $millis ms")
      assert(!mismatch.detail.exists(_.apart))
    }
  }

  test("a succeeding conversion of the same shapes still succeeds") {
    lengths.foreach { length =>
      val text = "a" * length
      val (_, millis) = onLargeStack(
        timed(
          typecheckDecls(
            s"""
               |def right : Eq(String, String.append("$text", "1"), "${text}1") := Eq.refl("${text}1")
               |
               |def refined (s: String)(h: Eq(String, s, "1")): Eq(String, String.append("$text", s), "${text}1") := {
               |  match h returning Eq(String, String.append("$text", s), "${text}1") with
               |  | Eq.refl t => Eq.refl("${text}1")
               |}
               |""".stripMargin
          )
        )
      )
      assert(millis < 10000, s"$length shared characters took $millis ms")
    }
  }

  test("the validated String.append path packs Unicode and mixed literal constructor lists") {
    val env = suitePrelude.checkedEnv
    val append = stringAppend(env)
    assert(append.body.isInstanceOf[Value.LamBody.Native])

    val left = Packed.evalStrLit(Vector('a'.toInt, 0x1f600), env)
    val right = Packed.evalStrLit(Vector(0xe9), env)
    val joined = Interpreter.evalApply(append, Vector(left, right))
    val sourceResult = Packed.withOpsDisabled(Interpreter.evalApply(append, Vector(left, right)))
    assertEquals(printsAsString(joined, env), "\"a😀é\"")
    assert(ValueEquivalence.defEq(joined, sourceResult))

    val mixed = runProgram(
      """{ String.append(String.mk(List.cons(Char.ofNat(65), ("😀").data)), "z") }""",
      suitePrelude
    )
    assertEquals(printsAsString(mixed, env), "\"A😀z\"")
    assert(mixed match {
      case Value.VCtor(head, Vector(chars: Value.VPacked), _) =>
        (head eq env("String.mk").asInstanceOf[Value.ConstructorHead]) &&
        (chars.codec eq env.nativeLiterals.stringLayout.get.charListCodec)
      case _ => false
    })
  }

  test("packed append operands preserve Unicode, nested and mixed source representations") {
    val env = suitePrelude.checkedEnv
    val append = stringAppend(env)
    val a = Packed.evalStrLit(Vector('a'.toInt, 0x1f600), env)
    val b = Packed.evalStrLit(Vector(0xe9), env)
    val c = Packed.evalStrLit(Vector('z'.toInt), env)
    val nestedRight = Interpreter.evalApply(append, Vector(b, c))
    val nestedRightDisabled = Packed.withOpsDisabled(Interpreter.evalApply(append, Vector(b, c)))
    val mixedLeft = runProgram(
      "{ String.mk(List.cons(Char.ofNat(65), (\"😀\").data)) }",
      suitePrelude
    )

    Vector(
      (a, b, a, b),
      (a, nestedRight, a, nestedRightDisabled),
      (mixedLeft, c, mixedLeft, c)
    ).foreach { case (left, right, sourceLeft, sourceRight) =>
      val enabled = Interpreter.evalApply(append, Vector(left, right))
      val disabled = Packed.withOpsDisabled(Interpreter.evalApply(append, Vector(sourceLeft, sourceRight)))
      assert(ValueEquivalence.defEq(enabled, disabled))
      assertEquals(PrettyPrinter.print(enabled, None), PrettyPrinter.print(disabled, None))
    }
  }

  test("native packed append defers only its exact application key until demand") {
    val env = suitePrelude.checkedEnv
    val layout = env.nativeLiterals.stringLayout.get.asInstanceOf[Value.SourceStringLayout]
    val append = stringAppend(env)
    val a = Packed.evalStrLit(Vector('a'.toInt), env)
    val b = Packed.evalStrLit(Vector(0x1f600), env)
    val c = Packed.evalStrLit(Vector('c'.toInt), env)

    val first = Interpreter.evalApply(append, Vector(a, b)).asInstanceOf[Value.VApp]
    val second = Interpreter.evalApply(append, Vector(first, c)).asInstanceOf[Value.VApp]
    assertEquals(Value.VApp.deferredStringAppendKeyMaterialized(first), Some(false))
    assertEquals(Value.VApp.deferredStringAppendKeyMaterialized(second), Some(false))
    assertEquals(printsAsString(second, env), "\"a😀c\"")
    assertEquals(Value.VApp.deferredStringAppendKeyMaterialized(first), Some(false))
    assertEquals(Value.VApp.deferredStringAppendKeyMaterialized(second), Some(false))

    val packedField = second match {
      case Value.VCtor(head, Vector(chars: Value.VPacked), tpe) =>
        assert(head eq layout.stringMk)
        assert(ValueEquivalence.defEq(tpe, layout.stringTpe))
        assert(chars.codec eq layout.charListCodec)
        chars
      case other => fail(s"Expected validated packed String.mk result, got $other")
    }
    val eagerEquivalent = Interpreter.evalApply(layout.stringMk, Vector(packedField))
    assertEquals(Value.VApp.deferredStringAppendKeyMaterialized(second), Some(false))
    assertEquals(second.key, eagerEquivalent.key)
    assertEquals(second.hashCode(), eagerEquivalent.hashCode())
    assertEquals(Value.VApp.deferredStringAppendKeyMaterialized(second), Some(true))
    assert(ValueEquivalence.defEq(second, eagerEquivalent))
    assertEquals(second.key, eagerEquivalent.key)

    val disabled = Packed.withOpsDisabled {
      val sourceFirst = Interpreter.evalApply(append, Vector(a, b))
      Interpreter.evalApply(append, Vector(sourceFirst, c))
    }
    assert(ValueEquivalence.defEq(second, disabled))
    assertEquals(printsAsString(disabled, env), printsAsString(second, env))
  }

  test("validated String.append scalars cover Unicode boundaries while checked packing rejects invalid scalars") {
    val env = suitePrelude.checkedEnv
    val append = stringAppend(env)
    val codec = env.nativeLiterals.stringLayout.get.charListCodec
    val scalars = Vector(0, 0x7f, 0x7ff, 0xd7ff, 0xe000, 0x10ffff)
    val left = Packed.evalStrLit(scalars.take(3), env)
    val right = Packed.evalStrLit(scalars.drop(3), env)
    val joined = Interpreter.evalApply(append, Vector(left, right))
    assertEquals(
      joined match {
        case Value.VCtor(_, Vector(chars: Value.VPacked), _) => chars.charScalars
        case _                                               => None
      },
      Some(scalars)
    )
    assert(
      ValueEquivalence.defEq(joined, Packed.withOpsDisabled(Interpreter.evalApply(append, Vector(left, right))))
    )

    Vector(0xd800, 0xdfff, 0x110000).foreach { invalid =>
      intercept[IllegalArgumentException] {
        Value.VPacked.charList(codec, Vector(invalid))
      }
      val source = s"{ String.append(String.mk(List.cons(Char.ofNat($invalid), List.nil(Char))), \"x\") }"
      val enabled = runProgram(source)
      val disabled = Packed.withOpsDisabled(runProgram(source))
      assert(ValueEquivalence.defEq(enabled, disabled), s"U+${invalid.toHexString}")
      assert(
        enabled match {
          case Value.VCtor(stringMk, Vector(Value.VCtor(cons, Vector(_, _), _)), _) =>
            stringMk.name == "String.mk" && cons.name == "List.cons"
          case _ => false
        },
        s"U+${invalid.toHexString} unexpectedly used the packed fast path"
      )
    }
  }

  test("String.append falls back for neutral suffixes and arbitrary Char values") {
    val env = suitePrelude.checkedEnv
    val append = stringAppend(env)
    val left = Packed.evalStrLit(Vector('x'.toInt), env)
    val neutral = FreshVar.freshVar("suffix", env("String"))
    val actual = Interpreter.evalApply(append, Vector(left, neutral))
    val sourceResult = Packed.withOpsDisabled(Interpreter.evalApply(append, Vector(left, neutral)))
    assert(ValueEquivalence.defEq(actual, sourceResult))

    val arbitrary =
      "{ String.append(String.mk(List.cons(someChar, List.nil(Char))), \"x\") }"
    val packedEnabled = runProgram(arbitrary, suitePrelude)
    val packedDisabled = Packed.withOpsDisabled(runProgram(arbitrary, suitePrelude))
    assert(ValueEquivalence.defEq(packedEnabled, packedDisabled))
  }

  test("unrecognized trusted append declarations retain their source equations") {
    val wrongStringAppend = TestSupport
      .stringLayoutSource("Char.mk(value)")
      .replace(
        "String.mk(List.append(a.data, b.data))",
        "a"
      )
    val wrongStringPrelude = Prelude.fromSource(
      "string-append-source-fallback",
      TestSupport.bundledPreludeSource + wrongStringAppend,
      Set(Prelude.ImportPath)
    )
    assert(stringAppend(wrongStringPrelude.checkedEnv).body.isInstanceOf[Value.LamBody.Core])
    assertEquals(
      printsAsString(runProgram("{ String.append(\"a\", \"b\") }", wrongStringPrelude), wrongStringPrelude.checkedEnv),
      "\"a\""
    )

    val alteredListSource = TestSupport.bundledPreludeSource.replace(
      "List.cons(head, List.append(tail, ys))",
      "ys"
    )
    val wrongListPrelude = Prelude.fromSource(
      "list-append-source-fallback",
      alteredListSource + TestSupport.stringLayoutSource("Char.mk(value)"),
      Set(Prelude.ImportPath)
    )
    assert(stringAppend(wrongListPrelude.checkedEnv).body.isInstanceOf[Value.LamBody.Core])
    assertEquals(
      printsAsString(runProgram("{ String.append(\"a\", \"b\") }", wrongListPrelude), wrongListPrelude.checkedEnv),
      "\"b\""
    )

    // String's representation is still a valid one-field String layout, but its hand-written selector ignores that
    // field. The native append must retain this source equation instead of concatenating the stored fields.
    val alteredSelectorSource = TestSupport
      .stringLayoutSource("Char.mk(value)")
      .replace("mk (data: List(Char))", "mk (chars: List(Char))")
      .replace(
        "namespace String {\n  def append",
        "namespace String {\n  def data (self: String): List(Char) := List.nil(Char)\n  def append"
      )
    val alteredSelectorPrelude = Prelude.fromSource(
      "string-data-source-fallback",
      TestSupport.bundledPreludeSource + alteredSelectorSource,
      Set(Prelude.ImportPath)
    )
    assert(stringAppend(alteredSelectorPrelude.checkedEnv).body.isInstanceOf[Value.LamBody.Core])
    assertEquals(
      printsAsString(
        runProgram("{ String.append(\"a\", \"b\") }", alteredSelectorPrelude),
        alteredSelectorPrelude.checkedEnv
      ),
      "\"\""
    )
  }

  test("distinct String literals are apart, and a literal against an unknown suffix is not") {
    typecheckDecls(
      """
        |def differ (h: Eq(String, "ab", "ac")): False := {
        |  match h returning False with
        |}
        |
        |def prefix (h: Eq(String, "ab", "abc")): False := {
        |  match h returning False with
        |}
        |""".stripMargin
    )
    expectTypeError[MissingCase](
      """
        |def unknown (s: String)(h: Eq(String, String.append("a", s), "ab")): False := {
        |  match h returning False with
        |}
        |""".stripMargin
    )
  }

  test("unequal packed character lists compare as their decodings do") {
    // `Char.ofNat` is trusted to be injective and is here not: every scalar decodes to the same character, so two
    // literals are equal exactly when a literal and its decoding are.
    val constant = stringPrelude("Char.mk(Nat.zero)")
    val a = runProgram("{ \"a\" }", constant)
    val b = runProgram("{ \"b\" }", constant)
    val decodedB = runProgram("{ String.mk(List.cons(Char.ofNat(98), List.nil(Char))) }", constant)
    assert(ValueEquivalence.defEq(a, decodedB))
    assert(ValueEquivalence.defEq(decodedB, b))
    assert(ValueEquivalence.defEq(a, b))
    assert(!ValueEquivalence.defEq(runProgram("{ \"a\" }"), runProgram("{ \"b\" }")))
  }

  test("a character that compares stuck leaves two literals apart only where one ends first") {
    // Here `Char.ofNat` wraps each scalar in an axiom, so no two decoded characters compare apart.
    val scrambled = Prelude.fromSource(
      "scrambled-chars",
      TestSupport.bundledPreludeSource + "\naxiom scramble : (n: Nat) -> Nat\n" +
        TestSupport.stringLayoutSource("Char.mk(scramble(value))"),
      Set(Prelude.ImportPath)
    )
    typecheckDecls(
      """
        |def shorter (h: Eq(String, "ab", "c")): False := {
        |  match h returning False with
        |}
        |""".stripMargin,
      scrambled
    )
    expectTypeError[MissingCase](
      """
        |def unknown (h: Eq(String, "ab", "ac")): False := {
        |  match h returning False with
        |}
        |""".stripMargin,
      scrambled
    )
    val mismatch =
      expectTypeError[TypeMismatch]("def wrong : Eq(String, \"xab\", \"xac\") := Eq.refl(\"xab\")", scrambled)
    assertEquals(differAt(mismatch), ("proj[String,0](\"c\")", "proj[String,0](\"b\")", false))
  }

  test("a clash of constructors or of literals is apart even where keys decide the equation") {
    // `g(n)`'s type is closed and `Tag.mk` has no fields, so the index equation is solved with nothing refinable,
    // where a key mismatch is conclusive. The `Char` index, a structure, leads the rules down to the clashing one.
    def program(index: String, value: String, clash: String, cases: String): String =
      s"""
         |inductive Tag indices (i: $index)(c: Char) : Type
         | | mk : Tag($value, Char.mk(0))
         |
         |def f (g: (n: Nat) -> Tag($clash, Char.mk(0)))(n: Nat): Nat := {
         |  match g(n) returning Nat with
         |$cases
         |}
         |""".stripMargin
    Vector(("Nat", "0", "1"), ("Bool", "Bool.true", "Bool.false")).foreach { case (index, value, clash) =>
      typecheckDecls(program(index, value, clash, ""))
      expectTypeError[UnreachableCase](program(index, value, clash, "  | Tag.mk => 0"))
    }
  }
}
