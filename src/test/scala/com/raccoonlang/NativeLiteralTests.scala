package com.raccoonlang

import java.nio.charset.StandardCharsets
import scala.collection.immutable.BitSet

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.Value.{NatCodec, VPacked}

class NativeLiteralTests extends munit.FunSuite {
  private val fullK3Addendum =
    """
      |namespace Nat {
      |  def div (a: Nat)(b: Nat): Nat := a
      |  def mod (a: Nat)(b: Nat): Nat := a
      |  def gcd (a: Nat)(b: Nat): Nat := a
      |  def land (a: Nat)(b: Nat): Nat := a
      |  def lor (a: Nat)(b: Nat): Nat := a
      |  def xor (a: Nat)(b: Nat): Nat := a
      |  def shiftLeft (a: Nat)(b: Nat): Nat := a
      |  def shiftRight (a: Nat)(b: Nat): Nat := a
      |}
      |
      |struct Char : Type
      | | mk (value: Nat) : Char
      |
      |namespace Char {
      |  def ofNat (value: Nat): Char := Char.mk(value)
      |}
      |
      |struct String : Type
      | | mk (data: List(Char)) : String
      |""".stripMargin

  private lazy val bundledPreludeSource = {
    val stream = Option(getClass.getResourceAsStream("/Init/Prelude.rac")).getOrElse(fail("Missing bundled Prelude"))
    try new String(stream.readAllBytes(), StandardCharsets.UTF_8)
    finally stream.close()
  }

  private def syntheticFullK3(sourceName: String, addendum: String): Prelude.Config =
    Prelude.fromTrustedSource(
      sourceName,
      bundledPreludeSource + "\n" + addendum,
      Set(Prelude.ImportPath),
      BootstrapAuthority.syntheticFullK3
    )

  private lazy val fullK3Prelude = syntheticFullK3("synthetic-full-k3", fullK3Addendum)

  private def parse(src: String, prelude: Prelude.Config): CoreAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) => Elaborator.elab(value, prelude)
      case err: Failure         => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def runProgram(src: String): Value = runProgram(src, Prelude.default)

  private def runProgram(src: String, prelude: Prelude.Config): Value =
    try Interpreter.run(parse(src, prelude), prelude).getOrElse(fail("Program has no body"))
    catch {
      case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
    }

  private def typecheckDecls(src: String): Unit =
    try Interpreter.run(parse(src, Prelude.default), Prelude.default)
    catch {
      case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
    }

  private def payload(value: Value): BigInt =
    value match {
      case p: VPacked if p.codec == NatCodec => p.natValue.getOrElse(fail("Invalid packed Nat"))
      case other                             => fail(s"Expected packed Nat, got $other")
    }

  private def ctorName(value: Value): String =
    value match {
      case Value.VCtor(head, _, _) => head.name
      case other                   => fail(s"Expected constructor value, got $other")
    }

  private def stringField(value: Value): VPacked =
    value match {
      case Value.VCtor(head, Vector(field: VPacked), _) if head.name == "String.mk" => field
      case other => fail(s"Expected packed String value, got $other")
    }

  private def replaceGlobal(env: Env, name: String, value: Value): Env =
    env.copy(globals = env.globals.updated(name, GlobalBinding.Strict(value, None)))

  private def expectTypeError[E <: TypeError](src: String, prelude: Prelude.Config)(implicit
      tag: reflect.ClassTag[E]
  ): E =
    intercept[E](Interpreter.run(parse(src, prelude), prelude))

  test("literal syntax, constructor folding, and printing use packed Nats") {
    assertEquals(payload(runProgram("{ 5 }")), BigInt(5))
    assertEquals(PrettyPrinter.print(runProgram("{ 5 }")), "5")
    assertEquals(payload(runProgram("{ Nat.zero }")), BigInt(0))
    assertEquals(payload(runProgram("{ Nat.succ(41) }")), BigInt(42))
    typecheckDecls("def five : Nat := 5")
  }

  test("Nat literal checking and evaluation use the same validated layout capability") {
    val original = Prelude.default.checkedEnv
    val expectedNat = original("Nat")
    val impostor = Value.VConst("Nat", Value.Symbol, Value.TypeTpe)
    val tampered = replaceGlobal(original, "Nat", impostor)
    val checked = TypeChecker.checkTerm(CoreAst.Term.NatLit(BigInt(7), Span(0, 1)), tampered)
    val evaluated = Interpreter.evalTerm(checked.residual, tampered)

    assert(checked.value.tpe eq expectedNat)
    assert(evaluated.tpe eq expectedNat)
    assert(!(evaluated.tpe eq impostor))
  }

  test("literal and constructor forms are definitionally equal") {
    typecheckDecls(
      """
        |def p : Eq(Nat, 5, Nat.succ(4)) := Eq.refl(5)
        |def q : Eq(Nat, Nat.succ(Nat.succ(Nat.zero)), 2) := Eq.refl(2)
        |""".stripMargin
    )
  }

  test("matching and constructor folding stay constant-time for large literals") {
    assertEquals(payload(runProgram("{ Nat.pred(1000000) }")), BigInt(999999))
  }

  test("accelerated Nat operations follow the Prelude conventions") {
    assertEquals(payload(runProgram("{ Nat.add(2, 3) }")), BigInt(5))
    assertEquals(payload(runProgram("{ Nat.sub(3, 5) }")), BigInt(0))
    assertEquals(payload(runProgram("{ Nat.mul(7, 8) }")), BigInt(56))
    assertEquals(payload(runProgram("{ Nat.pow(2, 10) }")), BigInt(1024))
    assertEquals(payload(runProgram("{ Nat.pow(7, 0) }")), BigInt(1))
    assertEquals(ctorName(runProgram("{ Nat.beq(5, 5) }")), "Bool.true")
    assertEquals(ctorName(runProgram("{ Nat.ble(2, 3) }")), "Bool.true")
    assertEquals(ctorName(runProgram("{ Nat.blt(3, 3) }")), "Bool.false")
  }

  test("pow enforces the native exponent limit without structural fallback") {
    val limit = Packed.MaxPowExponent
    assertEquals(payload(runProgram(s"{ Nat.pow(1, $limit) }")), BigInt(1))

    val error = expectTypeError[NativeOperationLimitExceeded](
      s"{ Nat.pow(1, ${limit + 1}) }",
      Prelude.default
    )
    assertEquals(error.operation, "Nat.pow")
    assertEquals(error.argument, limit + 1)
    assertEquals(error.limit, limit)
  }

  test("native operations agree with their structural definitions") {
    val arithmeticRanges = Vector("add" -> 12, "sub" -> 12, "mul" -> 6, "pow" -> 3)
    arithmeticRanges.foreach { case (op, limit) =>
      for {
        a <- 0 to limit
        b <- 0 to limit
      } {
        val src = s"{ Nat.$op($a, $b) }"
        val accelerated = runProgram(src)
        val structural = Packed.withOpsDisabled(runProgram(src))
        assert(ValueEquivalence.defEq(accelerated, structural), s"Nat.$op disagreed at ($a, $b)")
      }
    }

    Vector("beq", "ble", "blt").foreach { op =>
      for {
        a <- 0 to 12
        b <- 0 to 12
      } {
        val src = s"{ Nat.$op($a, $b) }"
        val accelerated = runProgram(src)
        val structural = Packed.withOpsDisabled(runProgram(src))
        assert(ValueEquivalence.defEq(accelerated, structural), s"Nat.$op disagreed at ($a, $b)")
      }
    }
  }

  test("large native-operation results use exact BigInt arithmetic") {
    val two64 = BigInt(2).pow(64)
    val two128 = BigInt(2).pow(128)
    assertEquals(payload(runProgram(s"{ Nat.mul($two64, $two64) }")), two128)
    assertEquals(payload(runProgram(s"{ Nat.add($two128, $two128) }")), two128 * 2)
    assertEquals(ctorName(runProgram(s"{ Nat.blt($two64, $two128) }")), "Bool.true")

    val random = new java.util.Random(0x4b33L)
    val pairs = Vector.fill(10) {
      val a = BigInt(new java.math.BigInteger(128, random))
      val b = BigInt(new java.math.BigInteger(128, random))
      (a, b)
    }
    pairs.foreach { case (a, b) =>
      assertEquals(payload(runProgram(s"{ Nat.add($a, $b) }")), a + b)
      assertEquals(payload(runProgram(s"{ Nat.sub($a, $b) }")), (a - b).max(0))
      assertEquals(payload(runProgram(s"{ Nat.mul($a, $b) }")), a * b)
      assertEquals(ctorName(runProgram(s"{ Nat.beq($a, $b) }")), if (a == b) "Bool.true" else "Bool.false")
      assertEquals(ctorName(runProgram(s"{ Nat.ble($a, $b) }")), if (a <= b) "Bool.true" else "Bool.false")
      assertEquals(ctorName(runProgram(s"{ Nat.blt($a, $b) }")), if (a < b) "Bool.true" else "Bool.false")

      val smallBase = a & ((BigInt(1) << 32) - 1)
      val smallExponent = (b & 7).toInt
      assertEquals(payload(runProgram(s"{ Nat.pow($smallBase, $smallExponent) }")), smallBase.pow(smallExponent))
    }
  }

  test("packed literals refine constructor equations and prove apartness") {
    typecheckDecls(
      """
        |def refine (n: Nat)(h: Eq(Nat, Nat.succ(n), 5)): Eq(Nat, n, 4) := {
        |  match h returning Eq(Nat, n, 4) with
        |  | Eq.refl z => Eq.refl(n)
        |}
        |
        |def distinct (h: Eq(Nat, 3, 5)): False := {
        |  match h returning False with
        |}
        |""".stripMargin
    )
  }

  test("forced implicits project constructor fields from packed literals") {
    val src =
      """
        |def predecessor {n: Nat}(h: Eq(Nat, Nat.succ(n), 5)): Nat := n
        |{ predecessor(Eq.refl(5)) }
        |""".stripMargin
    assertEquals(payload(runProgram(src)), BigInt(4))
  }

  test("the positional projection evaluator decodes packed constructor fields") {
    val env = Prelude.default.checkedEnv
    val nat = env("Nat")
    val instance = TypeChecker.inductiveFamilyOf(nat).getOrElse(fail("Nat is not an inductive family"))
    val succ = env("Nat.succ") match {
      case head: Value.ConstructorHead => head
      case other                       => fail(s"Expected Nat.succ constructor, got $other")
    }
    val info = new Value.ProjectionInfo(Vector(BitSet.empty), etaEligible = false, () => Some(succ))
    val one = VPacked.nat(1, nat)

    assertEquals(payload(InductiveProjection.check(one, instance, info, 0, Span(0, 0))), BigInt(0))
  }

  test("packed versus an opaque neutral is stuck, never apart") {
    expectTypeError[MissingCase](
      """
        |opaque def k : Nat := 5
        |def notApart (h: Eq(Nat, k, 5)): False := {
        |  match h returning False with
        |}
        |""".stripMargin,
      Prelude.default
    )
  }

  test("ground literal matches enforce their one reachable constructor") {
    assertEquals(
      payload(
        runProgram(
          """
            |{
            |  match 3 returning Nat with
            |  | Nat.succ p => p
            |}
            |""".stripMargin
        )
      ),
      BigInt(2)
    )

    expectTypeError[UnreachableCase](
      """
        |{
        |  match 3 returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ p => p
        |}
        |""".stripMargin,
      Prelude.default
    )
  }

  test("structural recursion can decrease directly on packed payloads") {
    val src =
      """
        |def fib (n: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ p => {
        |    match p returning Nat with
        |    | Nat.zero => 1
        |    | Nat.succ q => Nat.add(fib(p), fib(q))
        |  }
        |}
        |
        |{ fib(20) }
        |""".stripMargin
    assertEquals(payload(runProgram(src)), BigInt(6765))
  }

  test("packed literals survive quote and residual evaluation") {
    val src =
      """
        |def addFive : (n: Nat) -> Nat := fun (n: Nat): Nat => Nat.add(n, 5)
        |{ addFive(2) }
        |""".stripMargin
    assertEquals(payload(runProgram(src)), BigInt(7))

    val original = runProgram("{ 1000000 }")
    val quoted = ValueQuote.quoteTerm(original, ValueQuote.quoteContext(Prelude.default.checkedEnv), Span(0, 0))
    val roundTripped = Interpreter.evalTerm(quoted, Prelude.default.checkedEnv)
    assertEquals(roundTripped.key, original.key)
  }

  test("native Nat names are reserved outside a trusted bootstrap") {
    val natDecl =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |""".stripMargin

    assertEquals(expectTypeError[ReservedKernelName](natDecl, Prelude.none).name, "Nat")
    assertEquals(expectTypeError[ReservedKernelName](natDecl, Prelude.test).name, "Nat")

    val custom = Prelude.fromSource("custom-prelude", natDecl)
    assertEquals(intercept[ReservedKernelName](custom.checkedEnv).name, "Nat")

    Packed.nativeNatOpSpecs.foreach { spec =>
      val shortName = spec.name.stripPrefix("Nat.")
      val reservedOp =
        s"""
           |namespace Nat {
           |  def $shortName (A: Type): Type := A
           |}
           |""".stripMargin
      assertEquals(expectTypeError[ReservedKernelName](reservedOp, Prelude.none).name, spec.name)
    }

    assertEquals(payload(runProgram("{ Nat.add(2, 3) }")), BigInt(5))
  }

  test("the authoritative native table covers the full K3 profile and labels only blt as an extension") {
    assertEquals(Packed.nativeNatOpSpecs.map(_.name).distinct.length, 15)
    assertEquals(
      Packed.nativeNatOpSpecs.filter(_.origin == Packed.RaccoonExtension).map(_.name),
      Vector("Nat.blt")
    )
    assertEquals(
      Packed.nativeNatOpSpecs.filter(_.requiredBy(Packed.BundledSourcePrelude)).map(_.name),
      Vector("Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.beq", "Nat.ble", "Nat.blt")
    )
    assertEquals(
      Packed.nativeNatOpSpecs.filter(_.returnsBool).map(_.name),
      Vector("Nat.beq", "Nat.ble", "Nat.blt")
    )
    fullK3Prelude.checkedEnv
  }

  test("full-profile Nat operations follow K3 equations") {
    val cases = Vector(
      "Nat.div(17, 5)" -> BigInt(3),
      "Nat.div(17, 0)" -> BigInt(0),
      "Nat.mod(17, 5)" -> BigInt(2),
      "Nat.mod(17, 0)" -> BigInt(17),
      "Nat.gcd(0, 18)" -> BigInt(18),
      "Nat.gcd(48, 18)" -> BigInt(6),
      "Nat.land(10, 12)" -> BigInt(8),
      "Nat.lor(10, 12)" -> BigInt(14),
      "Nat.xor(10, 12)" -> BigInt(6),
      "Nat.shiftLeft(3, 5)" -> BigInt(96),
      "Nat.shiftRight(96, 5)" -> BigInt(3)
    )
    cases.foreach { case (term, expected) =>
      assertEquals(payload(runProgram(s"{ $term }", fullK3Prelude)), expected, term)
    }

    val random = new java.util.Random(0x4b334b33L)
    Vector
      .fill(20) {
        val a = BigInt(new java.math.BigInteger(192, random))
        val b = BigInt(new java.math.BigInteger(192, random))
        (a, b)
      }
      .foreach { case (a, b) =>
        assertEquals(payload(runProgram(s"{ Nat.div($a, $b) }", fullK3Prelude)), if (b == 0) BigInt(0) else a / b)
        assertEquals(payload(runProgram(s"{ Nat.mod($a, $b) }", fullK3Prelude)), if (b == 0) a else a % b)
        assertEquals(payload(runProgram(s"{ Nat.gcd($a, $b) }", fullK3Prelude)), a.gcd(b))
        assertEquals(payload(runProgram(s"{ Nat.land($a, $b) }", fullK3Prelude)), a & b)
        assertEquals(payload(runProgram(s"{ Nat.lor($a, $b) }", fullK3Prelude)), a | b)
        assertEquals(payload(runProgram(s"{ Nat.xor($a, $b) }", fullK3Prelude)), a ^ b)
      }
  }

  test("shift operations enforce the asymmetric resource policy") {
    val limit = Packed.MaxShiftLeft
    val admitted = payload(runProgram(s"{ Nat.shiftLeft(1, $limit) }", fullK3Prelude))
    assertEquals(admitted.bitLength, limit.toInt + 1)

    val error = expectTypeError[NativeOperationLimitExceeded](
      s"{ Nat.shiftLeft(1, ${limit + 1}) }",
      fullK3Prelude
    )
    assertEquals(error.operation, "Nat.shiftLeft")
    assertEquals(error.argument, limit + 1)
    assertEquals(error.limit, limit)
    assertEquals(payload(runProgram(s"{ Nat.shiftLeft(0, ${limit + 1}) }", fullK3Prelude)), BigInt(0))
    assertEquals(payload(runProgram(s"{ Nat.shiftRight(1, ${limit + 1}) }", fullK3Prelude)), BigInt(0))
  }

  test("String literals preserve scalar content, escaping, and compact quotation") {
    val sources = Vector(
      "\"\"" -> Vector.empty[Int],
      "\"raccoon\"" -> "raccoon".codePoints().toArray.toVector,
      "\"λ\"" -> Vector(0x03bb),
      "\"😀\"" -> Vector(0x1f600),
      "\"\\uD83D\\uDE00\\n\"" -> Vector(0x1f600, '\n'.toInt)
    )
    sources.foreach { case (source, expected) =>
      val value = runProgram(s"{ $source }", fullK3Prelude)
      val field = stringField(value)
      assertEquals(field.charScalars, Some(expected))
      val quoted = ValueQuote.quoteTerm(value, ValueQuote.quoteContext(fullK3Prelude.checkedEnv), Span(0, 0))
      val roundTripped = Interpreter.evalTerm(quoted, fullK3Prelude.checkedEnv)
      assertEquals(roundTripped.key, value.key)
      assertEquals(PrettyPrinter.print(roundTripped), PrettyPrinter.print(value))
    }
    assertEquals(PrettyPrinter.print(runProgram("{ \"a\\n\\t\\\"\\\\b\" }", fullK3Prelude)), "\"a\\n\\t\\\"\\\\b\"")
  }

  test("String matching peels one List and Char layer through checked constructors") {
    val codePoint = runProgram(
      """
        |{
        |  match "😀x" returning Nat with
        |  | String.mk chars => {
        |    match chars returning Nat with
        |    | List.cons head tail => {
        |      match head returning Nat with
        |      | Char.mk value => value
        |    }
        |  }
        |}
        |""".stripMargin,
      fullK3Prelude
    )
    assertEquals(payload(codePoint), BigInt(0x1f600))

    val empty = runProgram(
      """
        |{
        |  match "" returning Nat with
        |  | String.mk chars => {
        |    match chars returning Nat with
        |    | List.nil => 1
        |  }
        |}
        |""".stripMargin,
      fullK3Prelude
    )
    assertEquals(payload(empty), BigInt(1))
  }

  test("String peeling preserves distinct Char.ofNat scalars") {
    def decodedChar(source: String): Value = {
      val field = stringField(runProgram(s"{ $source }", fullK3Prelude))
      field.codec.decodeHead(field) match {
        case ("List.cons", Vector(char, _: VPacked)) => char
        case other                                   => fail(s"Expected a nonempty decoded CharList, got $other")
      }
    }

    def charScalar(char: Value): BigInt =
      char match {
        case Value.VCtor(head, Vector(value: VPacked), _) if head.name == "Char.mk" => payload(value)
        case other => fail(s"Expected Char.mk over a packed Nat, got $other")
      }

    val a = decodedChar("\"a\"")
    val b = decodedChar("\"b\"")
    assertEquals(charScalar(a), BigInt('a'.toInt))
    assertEquals(charScalar(b), BigInt('b'.toInt))
    assert(!ValueEquivalence.defEq(a, b))
    assertNotEquals(a.key, b.key)
  }

  test("decoded CharList tails share keys with independently introduced suffixes") {
    val whole = stringField(runProgram("{ \"abc\" }", fullK3Prelude))
    val (_, Vector(_, tail: VPacked)) = whole.codec.decodeHead(whole)
    val suffix = stringField(runProgram("{ \"bc\" }", fullK3Prelude))
    assertEquals(tail.key, suffix.key)

    val quoted = ValueQuote.quoteTerm(whole, ValueQuote.quoteContext(fullK3Prelude.checkedEnv), Span(0, 0))
    quoted match {
      case ElabAst.Term.Proj("String", 0, ElabAst.Term.StrLit(Vector(97, 98, 99), _), _) =>
      case other => fail(s"Unexpected standalone CharList quotation: $other")
    }
    assertEquals(Interpreter.evalTerm(quoted, fullK3Prelude.checkedEnv).key, whole.key)
  }

  test("long packed CharLists peel without rescanning their suffixes") {
    val layout = fullK3Prelude.checkedEnv.nativeLiterals.stringLayout.getOrElse(fail("Missing String layout"))
    val length = 20000
    var current = VPacked.charList(layout.charListCodec, Vector.fill(length)('x'.toInt))
    var remaining = length
    while (remaining > 0) {
      current.codec.decodeHead(current) match {
        case ("List.cons", Vector(_, tail: VPacked)) =>
          current = tail
          remaining -= 1
        case other => fail(s"Expected List.cons with $remaining scalars remaining, got $other")
      }
    }
    current.codec.decodeHead(current) match {
      case ("List.nil", Vector()) =>
      case other                  => fail(s"Expected List.nil after peeling the long CharList, got $other")
    }
  }

  test("String syntax rejects malformed Unicode and requires a validated layout") {
    val malformed = Vector(
      "{ \"\\uD800\" }" -> "surrogate",
      "{ \"\\uDC00\" }" -> "surrogate",
      "{ \"\\uD83D\\u0041\" }" -> "surrogate",
      "{ \"\\u12xz\" }" -> "hexadecimal",
      "{ \"\\q\" }" -> "escape",
      ("{ \"" + 0xd800.toChar + "\" }") -> "surrogate",
      "{ \"line\nbreak\" }" -> "control",
      "{ \"unterminated }" -> "unterminated"
    )
    malformed.foreach { case (source, expectedMessage) =>
      LanguageParser.parseProgram(source) match {
        case Failure(_, _, message) => assert(message.toLowerCase.contains(expectedMessage), message)
        case other                  => fail(s"Expected malformed Unicode failure, got $other")
      }
    }
    val unavailable = expectTypeError[StringLiteralUnavailable]("{ \"x\" }", Prelude.default)
    assert(unavailable.reason.contains("validated String layout"))
  }

  test("String layouts survive closure capture and environment materialization") {
    val value = runProgram(
      """
        |def literal : (n: Nat) -> String := fun (n: Nat): String => "closed"
        |{ literal(0) }
        |""".stripMargin,
      fullK3Prelude
    )
    assertEquals(PrettyPrinter.print(value), "\"closed\"")

    val layout = fullK3Prelude.checkedEnv.nativeLiterals.stringLayout.getOrElse(fail("Missing String layout"))
    val materialized = ValueOps.materializeEnv(fullK3Prelude.checkedEnv, EqStore.empty)
    assert(materialized.nativeLiterals.stringLayout.contains(layout))
  }

  test("full-profile admission rejects missing, malformed, opaque, and misidentified native declarations") {
    val allButDiv = fullK3Addendum.replace("  def div (a: Nat)(b: Nat): Nat := a\n", "")
    assertEquals(
      intercept[MissingNativeOperation](syntheticFullK3("missing-div", allButDiv).checkedEnv).name,
      "Nat.div"
    )

    val wrongTelescope = fullK3Addendum.replace(
      "  def div (a: Nat)(b: Nat): Nat := a",
      "  def div (a: Nat): Nat := a"
    )
    assertEquals(
      intercept[NativeOperationDeclarationMismatch](
        syntheticFullK3("wrong-div", wrongTelescope).checkedEnv
      ).name,
      "Nat.div"
    )

    val opaque = fullK3Addendum.replace(
      "  def div (a: Nat)(b: Nat): Nat := a",
      "  opaque def div (a: Nat)(b: Nat): Nat := a"
    )
    assertEquals(
      intercept[NativeOperationDeclarationMismatch](syntheticFullK3("opaque-div", opaque).checkedEnv).name,
      "Nat.div"
    )

    val wrongIdentity = fullK3Addendum.replace(
      "  def div (a: Nat)(b: Nat): Nat := a",
      "  def div : Nat -> Nat -> Nat := Nat.add"
    )
    assertEquals(
      intercept[NativeOperationDeclarationMismatch](
        syntheticFullK3("wrong-identity", wrongIdentity).checkedEnv
      ).name,
      "Nat.div"
    )

    val env = fullK3Prelude.checkedEnv
    val div = env("Nat.div") match {
      case lam: Value.VLam => lam
      case other           => fail(s"Expected Nat.div lambda, got $other")
    }
    val implicitDiv =
      div.copy(tpe = div.tpe.copy(binders = div.tpe.binders.updated(0, div.tpe.binders.head.copy(isImplicit = true))))
    val implicitError =
      intercept[NativeOperationDeclarationMismatch](Packed.validateNativeOpDeclaration("Nat.div", implicitDiv, env))
    assert(implicitError.reason.contains("explicit"), implicitError.reason)

    val beq = env("Nat.beq") match {
      case lam: Value.VLam => lam
      case other           => fail(s"Expected Nat.beq lambda, got $other")
    }
    val natResultBeq = beq.copy(tpe = beq.tpe.copy(codomain = _ => env("Nat")))
    val boolResultError =
      intercept[NativeOperationDeclarationMismatch](Packed.validateNativeOpDeclaration("Nat.beq", natResultBeq, env))
    assert(boolResultError.reason.contains("Bool"), boolResultError.reason)
  }

  test("String layout admission rejects every malformed representation component") {
    val wrongField = fullK3Addendum.replace(" | mk (data: List(Char)) : String", " | mk (data: Nat) : String")
    intercept[StringLiteralUnavailable](syntheticFullK3("wrong-string-field", wrongField).checkedEnv)

    val wrongArity = fullK3Addendum.replace(
      " | mk (data: List(Char)) : String",
      " | mk (data: List(Char))(extra: Nat) : String"
    )
    intercept[StringLiteralUnavailable](syntheticFullK3("wrong-string-arity", wrongArity).checkedEnv)

    val env = fullK3Prelude.checkedEnv
    val stringMk = env("String.mk") match {
      case head: Value.ConstructorHead => head
      case other                       => fail(s"Expected String.mk constructor, got $other")
    }
    val withoutNoConfusion = replaceGlobal(env, "String.mk", stringMk.copy(noConfusion = false))
    intercept[StringLiteralUnavailable](Packed.validateStringLayout(withoutNoConfusion))

    val string = env("String") match {
      case value @ Value.VConst(_, Value.Inductive(_), _) => value
      case other                                          => fail(s"Expected String inductive, got $other")
    }
    val stringMeta = string.constType match {
      case Value.Inductive(meta) => meta
      case _                     => fail("Expected String inductive metadata")
    }
    val wrongStringConstructor = string.copy(
      constType = Value.Inductive(
        stringMeta.copy(constructors = Vector(Value.ConstructorMeta("other", "String.other")))
      )
    )
    val wrongStringConstructorError = intercept[StringLiteralUnavailable](
      Packed.validateStringLayout(replaceGlobal(env, "String", wrongStringConstructor))
    )
    assert(wrongStringConstructorError.reason.contains("exactly"), wrongStringConstructorError.reason)
    val wrongStringMkTpe = stringMk.tpe match {
      case pi: Value.VPi => pi.copy(codomain = _ => env("Nat"))
      case other         => fail(s"Expected String.mk Pi type, got $other")
    }
    val wrongStringMk = stringMk.copy(tpe = wrongStringMkTpe)
    val originalProjection = stringMeta.projectionInfo.getOrElse(fail("Missing String projection metadata"))
    val wrongResultProjection = new Value.ProjectionInfo(
      originalProjection.fieldDependencies,
      originalProjection.etaEligible,
      () => Some(wrongStringMk)
    )
    val wrongResultString =
      string.copy(constType = Value.Inductive(stringMeta.copy(projectionInfo = Some(wrongResultProjection))))
    val wrongStringResultEnv =
      replaceGlobal(replaceGlobal(env, "String", wrongResultString), "String.mk", wrongStringMk)
    val wrongStringResultError =
      intercept[StringLiteralUnavailable](Packed.validateStringLayout(wrongStringResultEnv))
    assert(wrongStringResultError.reason.contains("result is not `String`"), wrongStringResultError.reason)

    val withoutProjection = string.constType match {
      case Value.Inductive(meta) => string.copy(constType = Value.Inductive(meta.copy(projectionInfo = None)))
      case _                     => fail("Expected String inductive metadata")
    }
    val projectionEnv = replaceGlobal(env, "String", withoutProjection)
    intercept[StringLiteralUnavailable](Packed.validateStringLayout(projectionEnv))

    val list = env("List") match {
      case value @ Value.VConst(_, Value.Inductive(_), _) => value
      case other                                          => fail(s"Expected List inductive, got $other")
    }
    val wrongListConstructors = list.constType match {
      case Value.Inductive(meta) =>
        list.copy(
          constType = Value.Inductive(
            meta.copy(constructors = meta.constructors.updated(0, Value.ConstructorMeta("empty", "List.empty")))
          )
        )
      case _ => fail("Expected List inductive metadata")
    }
    val wrongListConstructorsError = intercept[StringLiteralUnavailable](
      Packed.validateStringLayout(replaceGlobal(env, "List", wrongListConstructors))
    )
    assert(wrongListConstructorsError.reason.contains("exactly"), wrongListConstructorsError.reason)

    val listCons = env("List.cons") match {
      case head: Value.ConstructorHead => head
      case other                       => fail(s"Expected List.cons constructor, got $other")
    }
    val wrongListConsTpe = listCons.tpe match {
      case pi: Value.VPi => pi.copy(codomain = _ => env("Nat"))
      case other         => fail(s"Expected List.cons Pi type, got $other")
    }
    val wrongListConsResultError = intercept[StringLiteralUnavailable](
      Packed.validateStringLayout(replaceGlobal(env, "List.cons", listCons.copy(tpe = wrongListConsTpe)))
    )
    assert(wrongListConsResultError.reason.contains("does not instantiate"), wrongListConsResultError.reason)

    val charOfNat = env("Char.ofNat") match {
      case lam: Value.VLam => lam
      case other           => fail(s"Expected Char.ofNat lambda, got $other")
    }
    val wrongCharOfNat = charOfNat.copy(tpe = charOfNat.tpe.copy(codomain = _ => env("Nat")))
    val wrongCharOfNatError = intercept[StringLiteralUnavailable](
      Packed.validateStringLayout(replaceGlobal(env, "Char.ofNat", wrongCharOfNat))
    )
    assert(wrongCharOfNatError.reason.contains("Nat -> Char"), wrongCharOfNatError.reason)

    val capturedRef = CoreAst.LocalRef(Int.MaxValue, "captured")
    val captured = FreshVar.freshVar("captured", env("Nat"))
    val openBody = charOfNat.body match {
      case Value.LamBody.Core(term, closure) => Value.LamBody.Core(term, closure.putLocal(capturedRef, captured))
      case other                             => fail(s"Expected source Char.ofNat body, got $other")
    }
    val openEnv = replaceGlobal(env, "Char.ofNat", charOfNat.copy(body = openBody))
    intercept[StringLiteralUnavailable](Packed.validateStringLayout(openEnv))
  }

  test("trusted bootstrap finalization is atomic and reusable for streamed declarations") {
    val bootstrap = Interpreter.trustedBootstrap(BootstrapAuthority.syntheticFullK3)
    val validCandidate = fullK3Prelude.core.decls.foldLeft(bootstrap.initialEnv)(bootstrap.add)
    assert(validCandidate.nativeLiterals.stringLayout.isEmpty)
    val finished = bootstrap.finish(validCandidate)
    assert(finished.nativeLiterals.stringLayout.nonEmpty)
    assert(validCandidate.nativeLiterals.stringLayout.isEmpty)

    val stringStart = fullK3Addendum.indexOf("struct Char")
    assert(stringStart >= 0)
    val missingString = syntheticFullK3("missing-string-layout", fullK3Addendum.substring(0, stringStart))
    val failedCandidate = missingString.core.decls.foldLeft(bootstrap.initialEnv)(bootstrap.add)
    assert(failedCandidate.nativeLiterals.stringLayout.isEmpty)
    intercept[StringLiteralUnavailable](bootstrap.finish(failedCandidate))
    assert(bootstrap.initialEnv.nativeLiterals.stringLayout.isEmpty)
    assert(failedCandidate.nativeLiterals.stringLayout.isEmpty)
  }
}
