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
