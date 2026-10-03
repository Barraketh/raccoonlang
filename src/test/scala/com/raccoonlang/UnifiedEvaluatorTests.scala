package com.raccoonlang

import com.raccoonlang.CoreAst.{Term => CTerm}

class UnifiedEvaluatorTests extends munit.FunSuite with TestSupport {
  private val span = Span(0, 0)

  private def identity: Value.VLam =
    runProgram("def identity (x: Nat): Nat := x\n{ identity }").asInstanceOf[Value.VLam]

  test("evaluating a lambda expression and applying the same syntax use distinct plan roles") {
    val fn = identity
    val core = fn.body.asInstanceOf[Value.LamBody.Core]
    val arg = Value.VPacked.nat(BigInt(7), fn.tpe.env("Nat"))
    val expression = Interpreter.evalTerm(core.term, core.env).asInstanceOf[Value.VLam]
    assertEquals(Interpreter.evalApply(expression, Vector(arg)).key, arg.key)
    assertEquals(Interpreter.evalApply(fn, Vector(arg)).key, arg.key)
    assertEquals(Interpreter.evalApply(Interpreter.evalTerm(core.term, core.env), Vector(arg)).key, arg.key)

    val second = identity
    val secondCore = second.body.asInstanceOf[Value.LamBody.Core]
    val secondArg = Value.VPacked.nat(BigInt(9), second.tpe.env("Nat"))
    assertEquals(Interpreter.evalApply(second, Vector(secondArg)).key, secondArg.key)
    assertEquals(
      Interpreter.evalApply(Interpreter.evalTerm(secondCore.term, secondCore.env), Vector(secondArg)).key,
      secondArg.key
    )
  }

  test("raw application evaluates explicit arguments and ignores supplied evidence syntax") {
    val fn = identity
    val ref = CoreAst.LocalRef(900001, "callee")
    val env = fn.tpe.env.putLocal(ref, fn)
    val app = CTerm.App(
      CTerm.LocalRef(ref, span),
      Vector(CTerm.NatLit(BigInt(3), span)),
      Vector(CTerm.GlobalRef("unboundEvidence", span)),
      span
    )
    val expected = Value.VPacked.nat(BigInt(3), fn.tpe.env("Nat"))
    assertEquals(Interpreter.evalTerm(app, env).key, expected.key)
  }

  test("actual lambda binder refs govern raw application and duplicate binding is rejected") {
    val fn = identity
    val original = fn.tpe.binders.head.localRef
    val different = CoreAst.LocalRef(original.id + 900000, "different")
    val pi = fn.tpe.copy(binders = fn.tpe.binders.map(_.copy(localRef = different)))
    val mismatched = fn.copy(tpe = pi)
    val arg = Value.VPacked.nat(BigInt(4), fn.tpe.env("Nat"))
    interceptError[NotFound](Interpreter.evalApply(mismatched, Vector(arg)))

    val core = fn.body.asInstanceOf[Value.LamBody.Core]
    val occupied = fn.copy(body = core.copy(env = core.env.putLocal(original, arg)))
    val error = intercept[InternalError](Interpreter.evalApply(occupied, Vector(arg)))
    assert(error.getMessage.contains("already bound"))
    assertEquals(Interpreter.evalApply(fn, Vector(arg)).key, arg.key)
  }

  test("a raw match with duplicate constructor cases selects its first case") {
    val fn = identity
    val first = CoreAst.Case("Bool.true", isFullyQualified = true, Vector.empty, CTerm.NatLit(BigInt(1), span), span)
    val second = first.copy(body = CTerm.NatLit(BigInt(2), span))
    val term = CTerm.Match(
      CTerm.GlobalRef("Bool.true", span),
      CTerm.GlobalRef("Nat", span),
      Vector(first, second),
      None,
      None,
      span,
      NodeId.fresh()
    )
    val expected = Value.VPacked.nat(BigInt(1), fn.tpe.env("Nat"))
    assertEquals(Interpreter.evalTerm(term, fn.tpe.env).key, expected.key)
  }

  test("match branch slots preserve a closure captured in the scrutinee") {
    val result = runProgram(
      """def run : Nat := match {
        |  let captured := 41
        |  (fun (ignored: Nat): Nat => captured, 0)
        |} returning Nat with
        | | Pair.mk f marker => {
        |   let first := Nat.add(marker, 10)
        |   let second := Nat.add(first, 10)
        |   f(second)
        | }
        |{ run }
        |""".stripMargin
    )
    val expected = Value.VPacked.nat(BigInt(41), identity.tpe.env("Nat"))
    assertEquals(result.key, expected.key)
  }

  test("a dependent Pi keeps a scrutinee-local binder type after branch slots overwrite it") {
    val result = runProgram(
      """def run : Type := match {
        |  let captured := 41
        |  ((x: Eq(Nat, captured, captured)) -> Nat, 0)
        |} returning Type with
        | | Pair.mk ty marker => {
        |   let first := Nat.add(marker, 10)
        |   let second := Nat.add(first, 10)
        |   ty
        | }
        |{ run }
        |""".stripMargin
    ).asInstanceOf[Value.VPi]
    val domain = Interpreter.evalTerm(result.binders.head.ty, result.env)
    assertEquals(PrettyPrinter.print(domain), "Eq(Nat, 41, 41)")
  }

  test("nested asymmetric match regions keep the live sibling argument and high-water") {
    val result = runProgram(
      """def run (flag: Bool)(inner: Bool)(n: Nat): Nat := Nat.add(
        |  (match flag returning Nat with
        |   | Bool.true => {
        |     let first := Nat.add(n, 1)
        |     let second := Nat.add(first, 2)
        |     match inner returning Nat with
        |     | Bool.true => Nat.add(second, 3)
        |     | Bool.false => Nat.add(second, 4)
        |   }
        |   | Bool.false => Nat.add(n, 5)
        |  ),
        |  Nat.add(n, 10)
        |)
        |{ run(Bool.true, Bool.true, 7) }
        |""".stripMargin
    )
    val expected = Value.VPacked.nat(BigInt(30), identity.tpe.env("Nat"))
    assertEquals(result.key, expected.key)
  }

  test("Sort validates the level before evaluating its kind") {
    val fn = identity
    val term = CTerm.Sort(
      CTerm.NatLit(BigInt(1), span),
      CTerm.GlobalRef("missingKind", span),
      CTerm.GlobalRef("missingLifetime", span),
      span
    )
    val error = intercept[InternalError](Interpreter.evalTerm(term, fn.tpe.env))
    assert(error.getMessage.contains("non-level"))
  }

  test("Sort validates the kind before its lifetime in both atomic and framed evaluation") {
    val env = identity.tpe.env
    val zero = CTerm.FormOp(CoreAst.Form.LevelZero, Vector.empty, span)
    val atomic = CTerm.Sort(zero, zero, zero, span)
    val atomicError = intercept[InternalError](Interpreter.evalTerm(atomic, env))
    assert(atomicError.getMessage.contains("non-kind"))

    val framed = CTerm.Sort(zero, CTerm.NatLit(BigInt(1), span), CTerm.GlobalRef("missingLifetime", span), span)
    val framedError = intercept[InternalError](Interpreter.evalTerm(framed, env))
    assert(framedError.getMessage.contains("non-kind"))
  }

  test("raw application evaluates its function before explicit arguments, left to right") {
    val fn = identity
    val ref = CoreAst.LocalRef(900002, "callee")
    val env = fn.tpe.env.putLocal(ref, fn)
    val missingFn = CTerm.App(
      CTerm.GlobalRef("missingFunction", span),
      Vector(CTerm.GlobalRef("missingArgument", span)),
      Vector.empty,
      span
    )
    assertEquals(interceptError[NotFound](Interpreter.evalTerm(missingFn, env)), NotFound("missingFunction"))

    val missingArgs = CTerm.App(
      CTerm.LocalRef(ref, span),
      Vector(CTerm.GlobalRef("firstArgument", span), CTerm.GlobalRef("secondArgument", span)),
      Vector.empty,
      span
    )
    assertEquals(interceptError[NotFound](Interpreter.evalTerm(missingArgs, env)), NotFound("firstArgument"))
  }

  test("wrong arity is reported before inspecting a malformed raw Core body") {
    val fn = identity
    val core = fn.body.asInstanceOf[Value.LamBody.Core]
    val malformed = fn.copy(body = core.copy(term = core.term.copy(body = null)))
    val ref = CoreAst.LocalRef(900004, "malformed")
    val env = fn.tpe.env.putLocal(ref, malformed)
    val call = CTerm.App(CTerm.LocalRef(ref, span), Vector.empty, Vector.empty, span)
    assertEquals(
      interceptError[ArityMismatch](Interpreter.evalTerm(call, env)),
      ArityMismatch(1, 0, ArityMismatch.Arguments)
    )
  }

  test("boxed raw Core restores lexical environments through nested let, scope, match and tail call") {
    val fn = runProgram(
      """def identity (x: Nat): Nat := x
        |def run (x: Nat): Nat := {
        |  let y := Nat.add(x, 1)
        |  scope s => {
        |    match Nat.beq(x, 3) returning Nat with
        |    | Bool.true => {
        |      let z := Nat.add(y, 2)
        |      identity(z)
        |    }
        |    | Bool.false => x
        |  }
        |}
        |{ run }
        |""".stripMargin
    ).asInstanceOf[Value.VLam]
    val core = fn.body.asInstanceOf[Value.LamBody.Core]
    val rawTy = core.term.ty.copy(knownPropValued = None)
    val boxed = fn.copy(body = core.copy(term = core.term.copy(ty = rawTy)))
    val three = Value.VPacked.nat(BigInt(3), fn.tpe.env("Nat"))
    val six = Value.VPacked.nat(BigInt(6), fn.tpe.env("Nat"))
    assertEquals(Interpreter.evalApply(boxed, Vector(three)).key, six.key)
    assertEquals(Interpreter.evalApply(boxed, Vector(three)).key, six.key)
  }

  test("boxed sibling scopes release a reused local before the next argument") {
    val fn = identity
    val core = fn.body.asInstanceOf[Value.LamBody.Core]
    val shared = CoreAst.LocalRef(900003, "shared")
    val first = CTerm.Scope(shared, CTerm.NatLit(BigInt(1), span), span, NodeId.fresh())
    val second = CTerm.Scope(shared, CTerm.NatLit(BigInt(2), span), span, NodeId.fresh())
    val body = CTerm.App(CTerm.GlobalRef("Nat.add", span), Vector(first, second), Vector.empty, span)
    val fast = fn.copy(body = core.copy(term = core.term.copy(body = body)))
    val boxed =
      fn.copy(body = core.copy(term = core.term.copy(ty = core.term.ty.copy(knownPropValued = None), body = body)))
    val zero = Value.VPacked.nat(BigInt(0), fn.tpe.env("Nat"))
    val three = Value.VPacked.nat(BigInt(3), fn.tpe.env("Nat"))
    assertEquals(Interpreter.evalApply(fast, Vector(zero)).key, three.key)
    assertEquals(Interpreter.evalApply(boxed, Vector(zero)).key, three.key)
  }

  test("a local let rejects a noncanonical proof returned by a raw native callback") {
    val fn = runProgram(
      """def callback (n: Nat): Nat := n
        |def run (n: Nat): Nat := {
        |  let x := callback(n)
        |  0
        |}
        |{ run }
        |""".stripMargin
    ).asInstanceOf[Value.VLam]
    val core = fn.body.asInstanceOf[Value.LamBody.Core]
    val callback = core.env("callback").asInstanceOf[Value.VLam]
    val zero = Value.VPacked.nat(BigInt(0), fn.tpe.env("Nat"))
    val proposition = core.env("True")
    val noncanonical = Value.VProof(proposition)
    assert(!(Value.canonicalizeProof(noncanonical) eq noncanonical))
    val native = callback.copy(body = Value.LamBody.Native((_, _) => noncanonical, core.env, isRawRecursive = false))
    val modifiedEnv = core.env.copy(globals = core.env.globals.updated("callback", GlobalBinding.Strict(native)))
    val modified = fn.copy(body = core.copy(env = modifiedEnv))
    val error = intercept[InternalError](Interpreter.evalApply(modified, Vector(zero)))
    assert(error.getMessage.contains("Non-canonical proof bound into env"))
    assertEquals(Interpreter.evalApply(fn, Vector(zero)).key, zero.key)
  }

  test("nested reentry beyond the retained session pool clears after failure") {
    val fn = runProgram(
      """def callback (n: Nat): Nat := n
        |def run (n: Nat): Nat := callback(n)
        |{ run }
        |""".stripMargin
    ).asInstanceOf[Value.VLam]
    val core = fn.body.asInstanceOf[Value.LamBody.Core]
    val callback = core.env("callback").asInstanceOf[Value.VLam]
    var modified: Value.VLam = null
    var levels = 12
    var failAtBottom = true
    val native = callback.copy(body =
      Value.LamBody.Native(
        (args, _) => {
          if (levels > 0) {
            levels -= 1
            Interpreter.evalApply(modified, args)
          } else if (failAtBottom) {
            failAtBottom = false
            throw new IllegalStateException("planned nested failure")
          } else args.head
        },
        core.env,
        isRawRecursive = false
      )
    )
    val modifiedEnv = core.env.copy(globals = core.env.globals.updated("callback", GlobalBinding.Strict(native)))
    modified = fn.copy(body = core.copy(env = modifiedEnv))
    val seven = Value.VPacked.nat(BigInt(7), fn.tpe.env("Nat"))
    assertEquals(
      intercept[IllegalStateException](Interpreter.evalApply(modified, Vector(seven))).getMessage,
      "planned nested failure"
    )
    levels = 12
    assertEquals(Interpreter.evalApply(modified, Vector(seven)).key, seven.key)
    assertEquals(Interpreter.evalApply(fn, Vector(seven)).key, seven.key)
  }
}
