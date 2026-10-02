package com.raccoonlang

class PreparedEvalTests extends munit.FunSuite with TestSupport {
  private val peano =
    """
      |inductive Peano : Type
      | | zero : Peano
      | | succ (_: Peano) : Peano
      |""".stripMargin

  private def zero(fn: Value.VLam): Value =
    fn.tpe.env(fn.tpe.env.globals.keys.find(_.endsWith("Peano.zero")).getOrElse(fail("No Peano.zero"))) match {
      case head: Value.ConstructorHead => Packed.construct(head, Vector.empty, head.tpe)
      case other                       => fail(s"Expected Peano.zero constructor, got $other")
    }

  private def succ(fn: Value.VLam, value: Value): Value =
    Interpreter.evalApply(
      fn.tpe.env(fn.tpe.env.globals.keys.find(_.endsWith("Peano.succ")).getOrElse(fail("No Peano.succ"))),
      Vector(value)
    )

  test("prepared nested closures retain their captures across frame reuse") {
    val source = peano +
      """
        |def capture (x: Peano): Peano -> Peano := {
        |  let captured := Peano.succ(x)
        |  fun (ignored: Peano): Peano => captured
        |}
        |{ capture }
        |""".stripMargin
    val fn = runProgram(source).asInstanceOf[Value.VLam]
    val prepared = PreparedEval.prepare(fn).getOrElse(fail("Checked closure was not eligible"))
    val z = zero(fn)
    val one = succ(fn, z)
    val first = prepared.run(Vector(z))
    val second = prepared.run(Vector(one))
    val firstAgain = prepared.run(Vector(z))
    val genericFirst = Interpreter.evalApply(fn, Vector(z))
    val genericSecond = Interpreter.evalApply(fn, Vector(one))
    assert(ValueEquivalence.defEq(first, genericFirst))
    assert(ValueEquivalence.defEq(second, genericSecond))
    assertEquals(first.key, genericFirst.key)
    assertEquals(second.key, genericSecond.key)
    assertEquals(first.synDeps, genericFirst.synDeps)
    assertEquals(second.synDeps, genericSecond.synDeps)
    assert(ValueEquivalence.defEq(firstAgain, first))
    assert(ValueEquivalence.defEq(Interpreter.evalApply(first, Vector(z)), one))
    assert(ValueEquivalence.defEq(Interpreter.evalApply(second, Vector(z)), succ(fn, one)))
  }

  test("prepared recursive matches and non-tail arguments agree with the evaluator") {
    val source = peano +
      """
        |def add (a: Peano)(b: Peano): Peano decreases structural(b) := {
        |  match b returning Peano with
        |  | Peano.zero => a
        |  | Peano.succ rest => add(Peano.succ(a), rest)
        |}
        |def twice (x: Peano): Peano := {
        |  let y := Peano.succ(x)
        |  add(y, y)
        |}
        |{ twice }
        |""".stripMargin
    val fn = runProgram(source).asInstanceOf[Value.VLam]
    val prepared = PreparedEval.prepare(fn).getOrElse(fail("Checked closure was not eligible"))
    val z = zero(fn)
    val one = succ(fn, z)
    Vector(z, one, succ(fn, one)).foreach { arg =>
      val expected = Interpreter.evalApply(fn, Vector(arg))
      assert(ValueEquivalence.defEq(prepared.run(Vector(arg)), expected))
      assert(ValueEquivalence.defEq(prepared.run(Vector(arg)), expected))
    }
  }

  test("prepared evidence remains deferred and error recovery clears the session") {
    val source =
      """
        |def need [h: True]: Nat := 1
        |def caller (n: Nat): Nat := need()
        |{ caller }
        |""".stripMargin
    val fn = runProgram(source).asInstanceOf[Value.VLam]
    val prepared = PreparedEval.prepare(fn).getOrElse(fail("Checked closure was not eligible"))
    val nat = fn.tpe.env("Nat")
    val three = Value.VPacked.nat(BigInt(3), nat)
    interceptError[ArityMismatch](prepared.run(Vector.empty))
    val forced = forcings {
      val generic = Interpreter.evalApply(fn, Vector(three))
      val fast = prepared.run(Vector(three))
      assert(ValueEquivalence.defEq(fast, generic))
      assertEquals(fast.key, generic.key)
      assert(ValueEquivalence.defEq(prepared.run(Vector(three)), generic))
    }
    assertEquals(forced, 0L)
  }

  test("prepared match stuck on a neutral has the same identity and dependencies") {
    val source = peano +
      """
        |def choose (x: Peano): Peano := {
        |  match x returning Peano with
        |  | Peano.zero => Peano.zero
        |  | Peano.succ p => p
        |}
        |{ choose }
        |""".stripMargin
    val fn = runProgram(source).asInstanceOf[Value.VLam]
    val prepared = PreparedEval.prepare(fn).getOrElse(fail("Checked closure was not eligible"))
    val (_, neutral) = FreshVar.freshValue("unknown", zero(fn).tpe)
    val generic = Interpreter.evalApply(fn, Vector(neutral))
    val fast = prepared.run(Vector(neutral))
    assertEquals(fast.key, generic.key)
    assertEquals(fast.synDeps, generic.synDeps)
    assert(ValueEquivalence.defEq(fast, generic))
  }

  test("prepared mutual recursive peers match the generic evaluator") {
    val source =
      """
        |mutual {
        |  def even (n: Nat): Bool decreases structural(n) := {
        |    match n returning Bool with
        |    | Nat.zero => Bool.true
        |    | Nat.succ k => odd(k)
        |  }
        |  def odd (n: Nat): Bool decreases structural(n) := {
        |    match n returning Bool with
        |    | Nat.zero => Bool.false
        |    | Nat.succ k => even(k)
        |  }
        |}
        |{ even }
        |""".stripMargin
    val fn = runProgram(source).asInstanceOf[Value.VLam]
    val prepared = PreparedEval.prepare(fn).getOrElse(fail("Checked closure was not eligible"))
    val nat = fn.tpe.env("Nat")
    Vector(0, 1, 2, 9).foreach { n =>
      val arg = Value.VPacked.nat(BigInt(n), nat)
      val generic = Interpreter.evalApply(fn, Vector(arg))
      val fast = prepared.run(Vector(arg))
      assertEquals(fast.key, generic.key)
      assert(ValueEquivalence.defEq(fast, generic))
    }
  }

  test("prepared dependent Pi captures and scope fallback keep immutable environments") {
    val fn = runProgram(
      """
        |def makeType (n: Nat): Type := {
        |  let copied := n
        |  (x: Eq(Nat, copied, copied)) -> Nat
        |}
        |{ makeType }
        |""".stripMargin
    ).asInstanceOf[Value.VLam]
    val prepared = PreparedEval.prepare(fn).getOrElse(fail("Checked closure was not eligible"))
    val nat = fn.tpe.env("Nat")
    val one = Value.VPacked.nat(BigInt(1), nat)
    val two = Value.VPacked.nat(BigInt(2), nat)
    val first = prepared.run(Vector(one))
    val second = prepared.run(Vector(two))
    assertEquals(first.key, Interpreter.evalApply(fn, Vector(one)).key)
    assertEquals(second.key, Interpreter.evalApply(fn, Vector(two)).key)
    assertEquals(first.key, prepared.run(Vector(one)).key)

    val scoped = runProgram("def scoped (n: Nat): Nat := scope l => n\n{ scoped }")
      .asInstanceOf[Value.VLam]
    val scopedPlan = PreparedEval.prepare(scoped).getOrElse(fail("Checked scoped closure was not eligible"))
    val arg = Value.VPacked.nat(BigInt(7), scoped.tpe.env("Nat"))
    assertEquals(scopedPlan.run(Vector(arg)).key, Interpreter.evalApply(scoped, Vector(arg)).key)
  }

  test("an equation match and a native call fall back without replaying their arguments") {
    val fn = runProgram(
      """
        |def choose (n: Nat): Nat := {
        |  let increased := Nat.add(n, 1)
        |  match h : Nat.isZero(n) returning Nat with
        |  | Bool.true => 0
        |  | Bool.false => increased
        |}
        |{ choose }
        |""".stripMargin
    ).asInstanceOf[Value.VLam]
    val prepared = PreparedEval.prepare(fn).getOrElse(fail("Checked closure was not eligible"))
    val nat = fn.tpe.env("Nat")
    Vector(0, 1, 17).foreach { n =>
      val arg = Value.VPacked.nat(BigInt(n), nat)
      val generic = Interpreter.evalApply(fn, Vector(arg))
      val fast = prepared.run(Vector(arg))
      assertEquals(fast.key, generic.key)
    }
    val arg = Value.VPacked.nat(BigInt(4), nat)
    val sourceOnly = Packed.withOpsDisabled(prepared.run(Vector(arg)))
    val sourceGeneric = Packed.withOpsDisabled(Interpreter.evalApply(fn, Vector(arg)))
    assertEquals(sourceOnly.key, sourceGeneric.key)
  }

  test("separate checked module contexts keep their prepared plans local") {
    val module = peano +
      """
        |def wrap (x: Peano): Peano := Peano.succ(x)
        |""".stripMargin
    val first = outside(module, "{ wrap }")
      .getOrElse(fail("First module has no body"))
      .asInstanceOf[Value.VLam]
    val second = outside(module, "{ wrap }")
      .getOrElse(fail("Second module has no body"))
      .asInstanceOf[Value.VLam]
    val one = PreparedEval.prepare(first).getOrElse(fail("First checked closure was not eligible"))
    val two = PreparedEval.prepare(second).getOrElse(fail("Second checked closure was not eligible"))
    val firstResult = one.run(Vector(zero(first)))
    val secondResult = two.run(Vector(zero(second)))
    assertEquals(firstResult.key, Interpreter.evalApply(first, Vector(zero(first))).key)
    assertEquals(secondResult.key, Interpreter.evalApply(second, Vector(zero(second))).key)
    assert(!(firstResult.tpe eq secondResult.tpe))
  }

  test("tail calls replace frames when callee layouts grow and shrink") {
    val source =
      """
        |def narrow (x: Nat): Nat := x
        |def wide (x: Nat)(y: Nat): Nat := narrow(Nat.add(x, y))
        |def run (n: Nat): Nat := wide(n, 3)
        |{ run }
        |""".stripMargin
    val fn = runProgram(source).asInstanceOf[Value.VLam]
    val prepared = PreparedEval.prepare(fn).getOrElse(fail("Checked closure was not eligible"))
    val nat = fn.tpe.env("Nat")
    Vector(0, 1, 10).foreach { n =>
      val arg = Value.VPacked.nat(BigInt(n), nat)
      assertEquals(prepared.run(Vector(arg)).key, Interpreter.evalApply(fn, Vector(arg)).key)
    }
  }

  test("a same-thread callback can reenter Prepared without overwriting the outer frame") {
    val fn = runProgram(
      """
        |def callback (n: Nat): Nat := n
        |def run (n: Nat): Nat := Nat.add(callback(n), n)
        |{ run }
        |""".stripMargin
    ).asInstanceOf[Value.VLam]
    val originalCore = fn.body.asInstanceOf[Value.LamBody.Core]
    val callback = originalCore.env("callback").asInstanceOf[Value.VLam]
    var prepared: PreparedEval.Prepared = null
    var calls = 0
    val callbackBody = Value.LamBody.Native(
      (args, _) => {
        calls += 1
        if (calls == 1) {
          val nested = prepared.run(args)
          assertEquals(nested.key, Interpreter.evalApply(fn, args).key)
        }
        args.head
      },
      callback.body.asInstanceOf[Value.LamBody.Core].env,
      isRawRecursive = false
    )
    val native = callback.copy(body = callbackBody)
    val modifiedEnv = originalCore.env.copy(
      globals = originalCore.env.globals.updated("callback", GlobalBinding.Strict(native))
    )
    val modified = fn.copy(body = originalCore.copy(env = modifiedEnv))
    prepared = PreparedEval.prepare(modified).getOrElse(fail("Checked closure was not eligible"))
    val two = Value.VPacked.nat(BigInt(2), fn.tpe.env("Nat"))
    assertEquals(prepared.run(Vector(two)).key, Interpreter.evalApply(fn, Vector(two)).key)
    assertEquals(calls, 2)
    assertEquals(prepared.run(Vector(two)).key, Interpreter.evalApply(fn, Vector(two)).key)
  }
}
