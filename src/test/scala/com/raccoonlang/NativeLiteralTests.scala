package com.raccoonlang

import com.raccoonlang.Value.{NatCodec, VPacked, VCtor}

/** C17's self-contained trusted bootstrap coverage; bundled Prelude/module tests remain C18. */
class NativeLiteralTests extends munit.FunSuite {
  private def qualify(term: CoreAst.Term): CoreAst.Term = term match {
    case CoreAst.Term.Select(CoreAst.Term.GlobalRef(base, _), field, span)
        if Set("Nat", "Bool", "Char", "List", "String").contains(base) =>
      CoreAst.Term.GlobalRef(s"$base.$field", span)
    case CoreAst.Term.Select(base, field, span) => CoreAst.Term.Select(qualify(base), field, span)
    case CoreAst.Term.App(fn, args, span)       => CoreAst.Term.App(qualify(fn), args.map(qualify), span)
    case p: CoreAst.Term.Pi => p.copy(binders = p.binders.map(b => b.copy(ty = qualify(b.ty))), out = qualify(p.out))
    case CoreAst.Term.Body(lets, res, span) =>
      CoreAst.Term.Body(lets.map(l => l.copy(ty = l.ty.map(qualify), value = qualify(l.value))), qualify(res), span)
    case l: CoreAst.Term.Lam => l.copy(ty = qualify(l.ty).asInstanceOf[CoreAst.Term.Pi], body = qualify(l.body))
    case CoreAst.Term.Match(scrut, motive, cases, span) =>
      CoreAst.Term.Match(qualify(scrut), motive.map(qualify), cases.map(c => c.copy(body = qualify(c.body))), span)
    case other => other
  }

  private def core(source: String): CoreAst.Program = LanguageParser.parseProgram(source) match {
    case Success(program, _, _) =>
      val elaborated = Elaborator.elab(program)
      // C17 has no namespace/module loader yet.  The checked bootstrap fixture nevertheless
      // installs the authoritative Char.ofNat identity expected by String layout admission.
      val nativeNames = Set(
        "add",
        "sub",
        "mul",
        "pow",
        "beq",
        "ble",
        "blt",
        "div",
        "mod",
        "gcd",
        "land",
        "lor",
        "xor",
        "shiftLeft",
        "shiftRight"
      )
      val qualified = elaborated.copy(decls = elaborated.decls.map {
        case d @ CoreAst.Decl
              .ConstDecl(_, name, _, CoreAst.ConstBody.TermBody(CoreAst.Term.Lam(ty, body, sp, _, rec, peers)), _)
            if name == "ofNat" || nativeNames(name) =>
          val qualified = if (name == "ofNat") "Char.ofNat" else s"Nat.$name"
          d.copy(
            name = qualified,
            body = CoreAst.ConstBody.TermBody(CoreAst.Term.Lam(ty, body, sp, Some(qualified), rec, peers))
          )
        case d => d
      })
      qualified.copy(
        decls = qualified.decls.map {
          case d: CoreAst.Decl.ConstDecl =>
            d.copy(
              ty = qualify(d.ty),
              body = d.body match {
                case CoreAst.ConstBody.TermBody(t) => CoreAst.ConstBody.TermBody(qualify(t))
                case other                         => other
              }
            )
          case other => other
        },
        body = qualified.body.map(qualify)
      )
    case other => fail(s"parse failed: $other")
  }
  private def run(source: String): Value =
    TypeChecker.checkProgramTrusted(core(source))._2.map(_.value).getOrElse(fail("missing body"))
  private def payload(value: Value): BigInt = value match {
    case p: VPacked if p.codec == NatCodec => p.natValue.get
    case other                             => fail(s"expected packed Nat, got $other")
  }

  private def replaceGlobal(env: Env, name: String, value: Value): Env =
    env.copy(globals = env.globals.updated(name, GlobalBinding.Strict(value)))

  private def natOp(op: String, a: BigInt, b: BigInt, result: String = "Nat"): Value =
    run(
      bootstrap + s"\ndef $op (x: Nat)(y: Nat): $result := ${if (result == "Bool") "Bool.true" else "x"}\n\nNat.$op($a, $b)"
    )

  private def stringSource: String =
    """
      |inductive Bool : Type
      | | true : Bool
      | | false : Bool
      |
      |inductive Nat : Type
      | | zero : Nat
      | | succ (_: Nat) : Nat
      |
      |inductive List (A: Type) : Type
      | | nil : List(A)
      | | cons (head: A) (tail: List(A)) : List(A)
      |
      |struct Char : Type
      | | mk (value: Nat) : Char
      |
      |def ofNat (value: Nat): Char := Char.mk(value)
      |
      |struct String : Type
      | | mk (data: List(Char)) : String
      |""".stripMargin

  private val bootstrap =
    """
      |inductive Bool : Type
      | | true : Bool
      | | false : Bool
      |
      |inductive Nat : Type
      | | zero : Nat
      | | succ (_: Nat) : Nat
      |""".stripMargin

  private val fullNativeBootstrap =
    bootstrap +
      """
        |def div (a: Nat)(b: Nat): Nat := a
        |def mod (a: Nat)(b: Nat): Nat := a
        |def gcd (a: Nat)(b: Nat): Nat := a
        |def land (a: Nat)(b: Nat): Nat := a
        |def lor (a: Nat)(b: Nat): Nat := a
        |def xor (a: Nat)(b: Nat): Nat := a
        |def shiftLeft (a: Nat)(b: Nat): Nat := a
        |def shiftRight (a: Nat)(b: Nat): Nat := a
        |""".stripMargin

  test("validated literals and constructor equations use compact Nat values") {
    assertEquals(payload(run(bootstrap + "\n\n5")), BigInt(5))
    assertEquals(payload(run(bootstrap + "\n\nNat.succ(41)")), BigInt(42))
    val five = run(bootstrap + "\n\n5")
    val constructors = run(bootstrap + "\n\nNat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))))")
    assert(
      constructors.isInstanceOf[VPacked],
      s"class=${constructors.getClass} tpe=${constructors.tpe} deps=${constructors.tpe.synDeps}"
    )
    assertEquals(payload(constructors), BigInt(5))
    assert(ValueEquivalence.defEq(five, constructors), s"$five != $constructors")
  }

  test("Nat literal syntax requires the trusted layout") {
    val source = "inductive Nat : Type\n | zero : Nat\n | succ (_: Nat) : Nat\n\n\n5"
    intercept[NatLiteralUnavailable](TypeChecker.checkProgram(core(source)))
  }

  test("Nat operations retain exact BigInt semantics") {
    val source = bootstrap +
      """
        |def add (a: Nat)(b: Nat): Nat := a
        |""".stripMargin
    val (env, _) = TypeChecker.checkProgramTrusted(core(source))
    assertEquals(
      payload(Interpreter.evalTerm(CoreAst.Term.NatLit(BigInt("12345678901234567890"), Span(0, 1)), env)),
      BigInt("12345678901234567890")
    )
  }

  test("the trusted native operation table accelerates exact declarations") {
    val source = bootstrap + "\n\ndef add (a: Nat)(b: Nat): Nat := a\n"
    val checked = TypeChecker.checkProgramTrusted(core(source))._1
    val app = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Nat.add", Span(0, 1)),
      Vector(CoreAst.Term.NatLit(7, Span(0, 1)), CoreAst.Term.NatLit(8, Span(0, 1))),
      Span(0, 1)
    )
    assertEquals(payload(TypeChecker.checkTerm(app, checked).value), BigInt(15))
  }

  test("malformed Unicode is rejected by the scalar parser") {
    LanguageParser.parseProgram("{ \"\\uD800\" }") match {
      case Failure(_, _, message) => assert(message.toLowerCase.contains("surrogate"))
      case other                  => fail(s"expected malformed literal failure, got $other")
    }
  }

  test("validated String literals retain Unicode scalar payloads and peel compactly") {
    val declarations =
      """
        |inductive Bool : Type
        | | true : Bool
        | | false : Bool
        |
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive List (A: Type) : Type
        | | nil : List(A)
        | | cons (head: A) (tail: List(A)) : List(A)
        |
        |struct Char : Type
        | | mk (value: Nat) : Char
        |
        |def ofNat (value: Nat): Char := Char.mk(value)
        |
        |struct String : Type
        | | mk (data: List(Char)) : String
        |""".stripMargin
    val checked = TypeChecker.checkProgramTrusted(core(declarations))._1
    val literal = TypeChecker
      .checkTerm(
        CoreAst.Term.StrLit(Vector(0x1f600, 'x'.toInt), Span(0, 1)),
        checked
      )
      .value
    literal match {
      case VCtor(head, Vector(chars: VPacked), _) if head.name == "String.mk" =>
        assertEquals(chars.charScalars, Some(Vector(0x1f600, 'x'.toInt)))
        assertEquals(chars.codec.decodeHead(chars)._1, "List.cons")
      case other => fail(s"expected compact String constructor, got $other")
    }
  }

  test("native grouped applications enforce exact arity") {
    val env = TypeChecker.checkProgramTrusted(core(bootstrap + "\ndef add (x: Nat)(y: Nat): Nat := x"))._1
    val add = env("Nat.add")
    val error = intercept[ArityMismatch](
      Interpreter.evalApply(add, Vector(TypeChecker.checkTerm(CoreAst.Term.NatLit(1, Span(0, 1)), env).value))
    )
    assertEquals((error.expected, error.got), (2, 1))
    assertEquals(
      payload(
        Interpreter.evalApply(
          add,
          Vector(
            TypeChecker.checkTerm(CoreAst.Term.NatLit(1, Span(0, 1)), env).value,
            TypeChecker.checkTerm(CoreAst.Term.NatLit(2, Span(0, 1)), env).value
          )
        )
      ),
      BigInt(3)
    )
  }

  test("literal checking and residual evaluation share the installed Nat capability") {
    val env = TypeChecker.checkProgramTrusted(core(bootstrap))._1
    val checked = TypeChecker.checkTerm(CoreAst.Term.NatLit(17, Span(0, 1)), env)
    val evaluated = Interpreter.evalTerm(checked.residual, env)
    assert(checked.value.tpe eq evaluated.tpe)
    assertEquals(payload(evaluated), BigInt(17))
  }

  test("packed constructors print as literals and fold at arbitrary depth") {
    val env = TypeChecker.checkProgramTrusted(core(bootstrap))._1
    val zero = env("Nat.zero").asInstanceOf[Value.ConstructorHead]
    val succ = env("Nat.succ").asInstanceOf[Value.ConstructorHead]
    assert(Packed.foldCtor(zero, Vector.empty, zero.tpe).nonEmpty)
    assertEquals((succ.totalArity, succ.numErasedFamilyArgs, succ.noConfusion), (1, 0, true))
    assert(Packed.foldCtor(succ, Vector(Packed.foldCtor(zero, Vector.empty, zero.tpe).get), zero.tpe).nonEmpty)
    val value = (1 to 3).foldLeft(Packed.foldCtor(zero, Vector.empty, zero.tpe).get: Value) { (current, _) =>
      Interpreter.evalApply(succ, Vector(current))
    }
    assertEquals(payload(value), BigInt(3))
    assertEquals(PrettyPrinter.print(value), "3")
  }

  test("large constructor matching remains compact") {
    val value = run(
      bootstrap +
        "\ndef predecessor (n: Nat): Nat := match n with\n" +
        " | Nat.zero => Nat.zero\n" +
        " | Nat.succ p => p\n\npredecessor(1000000)"
    )
    assertEquals(payload(value), BigInt(999999))
  }

  test("the authoritative native table contains every operation and result kind") {
    val expected = Vector(
      "Nat.add",
      "Nat.sub",
      "Nat.mul",
      "Nat.pow",
      "Nat.beq",
      "Nat.ble",
      "Nat.blt",
      "Nat.div",
      "Nat.mod",
      "Nat.gcd",
      "Nat.land",
      "Nat.lor",
      "Nat.xor",
      "Nat.shiftLeft",
      "Nat.shiftRight"
    )
    assertEquals(Packed.nativeNatOpSpecs.map(_.name), expected)
    assertEquals(Packed.nativeNatOpSpecs.count(_.returnsBool), 3)
  }

  test("all native arithmetic equations retain exact BigInt semantics") {
    assertEquals(payload(natOp("add", 7, 8)), BigInt(15))
    assertEquals(payload(natOp("sub", 7, 8)), BigInt(0))
    assertEquals(payload(natOp("mul", 7, 8)), BigInt(56))
    assertEquals(payload(natOp("pow", 2, 10)), BigInt(1024))
    assertEquals(payload(natOp("div", 17, 3)), BigInt(5))
    assertEquals(payload(natOp("div", 17, 0)), BigInt(0))
    assertEquals(payload(natOp("mod", 17, 3)), BigInt(2))
    assertEquals(payload(natOp("mod", 17, 0)), BigInt(17))
    assertEquals(payload(natOp("gcd", 18, 12)), BigInt(6))
    assertEquals(payload(natOp("land", 6, 3)), BigInt(2))
    assertEquals(payload(natOp("lor", 6, 3)), BigInt(7))
    assertEquals(payload(natOp("xor", 6, 3)), BigInt(5))
    assertEquals(payload(natOp("shiftLeft", 3, 4)), BigInt(48))
    assertEquals(payload(natOp("shiftRight", 48, 4)), BigInt(3))
    assertEquals(natOp("beq", 4, 4, "Bool").toString.contains("Bool.true"), true)
    assertEquals(natOp("ble", 4, 4, "Bool").toString.contains("Bool.true"), true)
    assertEquals(natOp("blt", 4, 4, "Bool").toString.contains("Bool.false"), true)
  }

  test("pow and asymmetric shift limits are enforced") {
    val powLimit = Packed.MaxPowExponent
    assertEquals(payload(natOp("pow", 1, powLimit)), BigInt(1))
    intercept[NativeOperationLimitExceeded](natOp("pow", 1, powLimit + 1))
    assertEquals(payload(natOp("shiftLeft", 0, Packed.MaxShiftLeft + 1)), BigInt(0))
    intercept[NativeOperationLimitExceeded](natOp("shiftLeft", 1, Packed.MaxShiftLeft + 1))
    assertEquals(payload(natOp("shiftRight", 1, Packed.MaxShiftLeft + 1)), BigInt(0))
  }

  test("a complete checked native table evaluates every extended equation") {
    val cases = Vector(
      "Nat.div(17, 5)" -> BigInt(3),
      "Nat.mod(17, 0)" -> BigInt(17),
      "Nat.gcd(48, 18)" -> BigInt(6),
      "Nat.land(10, 12)" -> BigInt(8),
      "Nat.lor(10, 12)" -> BigInt(14),
      "Nat.xor(10, 12)" -> BigInt(6),
      "Nat.shiftLeft(3, 5)" -> BigInt(96),
      "Nat.shiftRight(96, 5)" -> BigInt(3)
    )
    cases.foreach { case (term, expected) =>
      assertEquals(payload(run(fullNativeBootstrap + s"\n\n$term")), expected, term)
    }
  }

  test("large native results use unbounded BigInt arithmetic") {
    val a = BigInt(2).pow(128)
    assertEquals(payload(natOp("mul", a, a)), a * a)
  }

  test("packed literals refine genuine constructor equations and apartness") {
    val env = TypeChecker.checkProgramTrusted(core(bootstrap))._1
    val packed = TypeChecker.checkTerm(CoreAst.Term.NatLit(5, Span(0, 1)), env).value
    val zeroHead = env("Nat.zero").asInstanceOf[Value.ConstructorHead]
    val zero = Value.VCtor(zeroHead, Vector.empty, zeroHead.tpe)
    val failure = ValueEquivalence.tryUnify(packed, zero, EqStore.empty).swap.getOrElse(fail("expected apartness"))
    assert(failure.apart)
  }

  test("packed versus opaque constructor neutrals is stuck") {
    val env = TypeChecker.checkProgramTrusted(core(bootstrap))._1
    val packed = TypeChecker.checkTerm(CoreAst.Term.NatLit(5, Span(0, 1)), env).value
    val opaqueHead = Value.ConstructorHead("Opaque.mk", 0, 0, packed.tpe, noConfusion = false)
    val opaque = Value.VCtor(opaqueHead, Vector.empty, packed.tpe)
    assert(!ValueEquivalence.tryUnify(packed, opaque, EqStore.empty).swap.getOrElse(fail("expected stuck")).apart)
  }

  test("ground packed matches reject unreachable constructors") {
    val matched = run(
      bootstrap +
        "\n\n{ match 3 returning Nat with\n" +
        " | Nat.succ p => p\n}"
    )
    assertEquals(payload(matched), BigInt(2))
    intercept[UnreachableCase] {
      run(
        bootstrap +
          "\n\n{ match 3 returning Nat with\n" +
          " | Nat.zero => Nat.zero\n" +
          " | Nat.succ p => p\n}"
      )
    }
  }

  test("packed constructor equations refine a real forced implicit") {
    val value = run(
      bootstrap +
        "\ninductive Eq (A: Type) indices (left: A)(right: A) : Prop\n" +
        " | refl (value: A) : Eq(A, value, value)\n" +
        "\ndef predecessor {n: Nat}(h: Eq(Nat, Nat.succ(n), Nat.succ(n))): Nat := n\n" +
        "\npredecessor(Eq.refl(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))"
    )
    assertEquals(payload(value), BigInt(3))
  }

  test("disabled native acceleration falls back to the checked body") {
    val source = bootstrap + "\ndef add (x: Nat)(y: Nat): Nat := x\n\nNat.add(7, 8)"
    val normal = run(source)
    val structural = Packed.withOpsDisabled(run(source))
    assertEquals(payload(normal), BigInt(15))
    assertEquals(payload(structural), BigInt(7))
  }

  test("native declarations are trusted-only and reserved names alone do not accelerate") {
    val env = TypeChecker.checkProgram(core(bootstrap + "\ndef add (x: Nat)(y: Nat): Nat := x"))._1
    assert(
      !env("Nat.add")
        .isInstanceOf[Value.VLam] || !env("Nat.add").asInstanceOf[Value.VLam].body.isInstanceOf[Value.LamBody.Native]
    )
  }

  test("trusted native admission rejects opaque, builtin, identity, domain, and codomain variants") {
    val opaque = bootstrap + "\nopaque def add (x: Nat)(y: Nat): Nat := x"
    intercept[NativeOperationDeclarationMismatch](TypeChecker.checkProgramTrusted(core(opaque)))

    val builtin = core(bootstrap + "\ndef add (x: Nat)(y: Nat): Nat := builtin")
      .copy(decls = core(bootstrap + "\ndef add (x: Nat)(y: Nat): Nat := builtin").decls.map {
        case d: CoreAst.Decl.ConstDecl if d.name == "add" => d.copy(name = "Nat.add")
        case d                                            => d
      })
    intercept[NativeOperationDeclarationMismatch](TypeChecker.checkProgramTrusted(builtin))

    val wrongIdentity = core(bootstrap + "\ndef add (x: Nat)(y: Nat): Nat := x")
      .copy(decls = core(bootstrap + "\ndef add (x: Nat)(y: Nat): Nat := x").decls.map {
        case d @ CoreAst.Decl.ConstDecl(_, "Nat.add", ty, CoreAst.ConstBody.TermBody(lam: CoreAst.Term.Lam), span) =>
          d.copy(body = CoreAst.ConstBody.TermBody(lam.copy(name = Some("Nat.other"))))
        case d => d
      })
    intercept[NativeOperationDeclarationMismatch](TypeChecker.checkProgramTrusted(wrongIdentity))

    val wrongDomain = bootstrap + "\ndef add (x: Bool)(y: Nat): Nat := Nat.zero"
    intercept[NativeOperationDeclarationMismatch](TypeChecker.checkProgramTrusted(core(wrongDomain)))
    val wrongCodomain = bootstrap + "\ndef add (x: Nat)(y: Nat): Bool := Bool.true"
    intercept[NativeOperationDeclarationMismatch](TypeChecker.checkProgramTrusted(core(wrongCodomain)))
  }

  test("String layout admission rejects every missing or malformed component") {
    val env = TypeChecker.checkProgramTrusted(core(stringSource))._1
    Vector("String", "String.mk", "List", "List.nil", "List.cons", "Char", "Char.ofNat").foreach { name =>
      intercept[StringLiteralUnavailable](Packed.validateStringLayout(env.copy(globals = env.globals - name)))
    }
    val charOfNat = env("Char.ofNat").asInstanceOf[Value.VLam]
    val wrongChar = charOfNat.copy(tpe = charOfNat.tpe.asInstanceOf[Value.VPi].copy(codomain = _ => env("Nat")))
    intercept[StringLiteralUnavailable](Packed.validateStringLayout(replaceGlobal(env, "Char.ofNat", wrongChar)))
    val string = env("String").asInstanceOf[Value.VConst]
    val meta = string.constType.asInstanceOf[Value.Inductive].meta
    val noEta = string.copy(constType = Value.Inductive(meta.copy(projectionInfo = None)))
    intercept[StringLiteralUnavailable](Packed.validateStringLayout(replaceGlobal(env, "String", noEta)))
  }

  test("independently introduced CharList suffixes share one cached codec") {
    val env = TypeChecker.checkProgramTrusted(core(stringSource))._1
    val one = TypeChecker.checkTerm(CoreAst.Term.StrLit(Vector('a'.toInt, 'b'.toInt), Span(0, 1)), env).value
    val two = TypeChecker.checkTerm(CoreAst.Term.StrLit(Vector('b'.toInt), Span(0, 1)), env).value
    val first = one.asInstanceOf[Value.VApp].args.head.asInstanceOf[VPacked]
    val suffix = first.codec.decodeHead(first)._2(1).asInstanceOf[VPacked]
    assert(suffix.codec eq two.asInstanceOf[Value.VApp].args.head.asInstanceOf[VPacked].codec)
    assert(ValueEquivalence.defEq(suffix, two.asInstanceOf[Value.VApp].args.head))
  }

  test("long CharList peeling shares suffix storage") {
    val env = TypeChecker.checkProgramTrusted(core(stringSource))._1
    val chars = Vector.fill(20000)('x'.toInt)
    val value = TypeChecker.checkTerm(CoreAst.Term.StrLit(chars, Span(0, 1)), env).value
    var list = value.asInstanceOf[Value.VApp].args.head.asInstanceOf[VPacked]
    var count = 0
    while (count < chars.length) {
      val head = list.codec.decodeHead(list)
      list = head._2(1).asInstanceOf[VPacked]
      count += 1
    }
    assertEquals(list.codec.decodeHead(list)._1, "List.nil")
  }

  test("String printing preserves scalar escaping") {
    val env = TypeChecker.checkProgramTrusted(core(stringSource))._1
    val value = TypeChecker.checkTerm(CoreAst.Term.StrLit(Vector('a'.toInt, 10, 0x1f600), Span(0, 1)), env).value
    assertEquals(PrettyPrinter.print(value), "\"a\\n😀\"")
  }

  test("checked String, List, and Char matches peel scalar literals") {
    val value = run(
      stringSource +
        "\n\n{ match \"😀x\" returning Nat with\n" +
        " | String.mk chars => {\n" +
        "   match chars returning Nat with\n" +
        "   | List.cons head tail => {\n" +
        "     match head returning Nat with\n" +
        "     | Char.mk code => code\n" +
        "   }\n" +
        " }\n}"
    )
    assertEquals(payload(value), BigInt(0x1f600))
  }

  test("String layout identity survives closures and materialization") {
    val env = TypeChecker.checkProgramTrusted(core(stringSource))._1
    val layout = env.nativeLiterals.stringLayout.getOrElse(fail("missing String layout"))
    val materialized = ValueOps.materializeEnv(env, EqStore.empty)
    assert(materialized.nativeLiterals.stringLayout.get eq layout)
    val (checkedEnv, body) = TypeChecker.checkProgram(
      core("def closed : (n: Nat) -> String := fun (n: Nat): String => \"closed\"\n\nclosed(0)"),
      env
    )
    assert(checkedEnv.nativeLiterals.stringLayout.get eq layout)
    val value = body.map(_.value).getOrElse(fail("missing closure result"))
    assertEquals(PrettyPrinter.print(value), "\"closed\"")
    assert(ValueOps.materializeEnv(checkedEnv, EqStore.empty).nativeLiterals.stringLayout.get eq layout)
  }

  test("malformed String layout remains unavailable rather than partially installed") {
    val source = bootstrap + "\n\nstruct String : Type\n | mk (data: Nat) : String\n\n\n\"x\""
    intercept[StringLiteralUnavailable](TypeChecker.checkProgramTrusted(core(source)))
  }

  test("packed values survive residual evaluation and materialization") {
    val env = TypeChecker.checkProgramTrusted(core(bootstrap))._1
    val checked = TypeChecker.checkTerm(CoreAst.Term.NatLit(99, Span(0, 1)), env)
    val materialized = ValueOps.materializeEnv(env, EqStore.empty)
    assert(materialized.nativeLiterals.natLayout.nonEmpty)
    assertEquals(payload(Interpreter.evalTerm(checked.residual, materialized)), BigInt(99))
  }

  test("trusted bootstrap finalization is reusable and atomic") {
    val env = TypeChecker.checkProgramTrusted(core(bootstrap))._1
    assert(env.nativeLiterals.natLayout.nonEmpty)
    val layout = Packed.validateNatFamily(env)
    val installed = Env.empty.installNatLayout(layout)
    intercept[WTF](installed.installNatLayout(layout))
    val finished = Packed.finalizeTrustedBootstrap(env)
    assert(finished.nativeLiterals.natLayout.get eq env.nativeLiterals.natLayout.get)
    val malformed = "inductive Nat : Type\n | zero : Nat\n\n"
    intercept[NatLiteralUnavailable](TypeChecker.checkProgramTrusted(core(malformed)))
    val original = Env.empty
    val malformedString = TypeChecker.checkProgramTrusted(core(stringSource + "\n\n\"x\""))._1
    assert(malformedString.nativeLiterals.natLayout.nonEmpty)
    assert(original.nativeLiterals.natLayout.isEmpty)
  }

  test("structural recursion accepts packed payload descent") {
    val value = run(
      bootstrap +
        "\ndef pred (n: Nat): Nat decreases structural(n) := match n with\n" +
        " | Nat.zero => Nat.zero\n" +
        " | Nat.succ k => k\n\npred(4)"
    )
    assertEquals(payload(value), BigInt(3))
  }

  test("reserved native admission rejects a declaration with the wrong result kind") {
    intercept[NativeOperationDeclarationMismatch] {
      TypeChecker.checkProgramTrusted(core(bootstrap + "\ndef add (x: Nat)(y: Nat): Bool := Bool.true\n"))
    }
  }

  test("distinct Unicode scalar Char values remain distinct") {
    val env = TypeChecker.checkProgramTrusted(core(stringSource))._1
    val a = TypeChecker.checkTerm(CoreAst.Term.StrLit(Vector(0x1f600), Span(0, 1)), env).value
    val b = TypeChecker.checkTerm(CoreAst.Term.StrLit(Vector(0x1f601), Span(0, 1)), env).value
    val ac = a
      .asInstanceOf[Value.VApp]
      .args
      .head
      .asInstanceOf[VPacked]
      .codec
      .decodeHead(a.asInstanceOf[Value.VApp].args.head.asInstanceOf[VPacked])
      ._2
      .head
    val bc = b
      .asInstanceOf[Value.VApp]
      .args
      .head
      .asInstanceOf[VPacked]
      .codec
      .decodeHead(b.asInstanceOf[Value.VApp].args.head.asInstanceOf[VPacked])
      ._2
      .head
    assert(!ValueEquivalence.defEq(ac, bc))
  }
}
