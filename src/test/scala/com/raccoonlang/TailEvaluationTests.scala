package com.raccoonlang

import com.raccoonlang.Value.{NatCodec, VPacked}

/**
 * Tail positions run in a loop (docs/kernel.md#evaluation-depth): a block's result, a match's chosen branch, a scope's
 * body and a core lambda's body at an application take no host stack. Non-tail Core calls now use explicit frames too.
 */
class TailEvaluationTests extends munit.FunSuite with TestSupport {

  /**
   * `body` on a thread with a 2MB stack, the default stack of the JVM that measured the old limits (PROOF_BY_EVALUATION
   * §2.1), whatever thread and stack the runner uses. The suite's prelude is built first, on the runner's thread, so
   * that only the program meets the chosen stack.
   */
  private def onSmallStack[A](body: => A): A = {
    suitePrelude.checkedEnv
    Execution.onStack(2L << 20)(body)
  }

  private def payload(value: Value): BigInt =
    value match {
      case p: VPacked if p.codec == NatCodec => p.natValue.getOrElse(fail("Invalid packed Nat"))
      case other                             => fail(s"Expected packed Nat, got $other")
    }

  private def sumBelow(n: Long): BigInt = BigInt(n) * (n - 1) / 2

  /** `build(n, nil)` is `[0, 1, …, n - 1]`, built with an accumulator; `sum` and `allBelow` consume one likewise. */
  private val accumulators =
    """
      |def build (n: Nat)(acc: List(Nat)): List(Nat) decreases structural(n) := {
      |  match n returning List(Nat) with
      |  | Nat.zero => acc
      |  | Nat.succ p => build(p, List.cons(p, acc))
      |}
      |
      |def sum (xs: List(Nat))(acc: Nat): Nat decreases structural(xs) := {
      |  match xs returning Nat with
      |  | List.nil => acc
      |  | List.cons h t => sum(t, Nat.add(acc, h))
      |}
      |
      |def allBelow (xs: List(Nat))(n: Nat): Bool decreases structural(xs) := {
      |  match xs returning Bool with
      |  | List.nil => Bool.true
      |  | List.cons h t => {
      |    match Nat.blt(h, n) returning Bool with
      |    | Bool.true => allBelow(t, n)
      |    | Bool.false => Bool.false
      |  }
      |}
      |""".stripMargin

  /** Far beyond the ~920 elements that overflowed a 2MB stack before, and quick enough for the suite. */
  private val size = 250000

  test("accumulator recursion over a 250,000-element list runs in a 2MB stack") {
    val result = onSmallStack(runProgram(accumulators + s"{ sum(build($size, List.nil(Nat)), 0) }"))
    assertEquals(payload(result), sumBelow(size))
  }

  test("a check-time equation evaluates an accumulator procedure over 250,000 elements") {
    def equation(bound: Int): String =
      accumulators + s"def ok : Eq(Bool, allBelow(build($size, List.nil(Nat)), $bound), Bool.true) := Eq.refl(Bool.true)\n"
    onSmallStack(typecheckDecls(equation(size)))
    // Only the list's last element is not below the smaller bound, so the procedure ran to the end.
    onSmallStack(expectTypeError[TypeMismatch](equation(size - 1)))
  }

  test("non-tail recursion also runs through explicit frames on a small host stack") {
    val nonTail =
      """
        |def build (n: Nat)(acc: List(Nat)): List(Nat) decreases structural(n) := {
        |  match n returning List(Nat) with
        |  | Nat.zero => acc
        |  | Nat.succ p => build(p, List.cons(p, acc))
        |}
        |
        |def sum (xs: List(Nat)): Nat decreases structural(xs) := {
        |  match xs returning Nat with
        |  | List.nil => 0
        |  | List.cons h t => Nat.add(h, sum(t))
        |}
        |""".stripMargin
    assertEquals(payload(onSmallStack(runProgram(nonTail + "{ sum(build(500, List.nil(Nat))) }"))), sumBelow(500))
    assertEquals(payload(onSmallStack(runProgram(nonTail + "{ sum(build(5000, List.nil(Nat))) }"))), sumBelow(5000))
  }

  test("a let body, a nested block and a call into another definition are tail positions") {
    val program =
      """
        |def viaLet (n: Nat)(acc: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => acc
        |  | Nat.succ p => {
        |    let next := Nat.add(acc, 2)
        |    viaLet(p, next)
        |  }
        |}
        |
        |def viaBlock (n: Nat)(acc: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => acc
        |  | Nat.succ p => { viaBlock(p, Nat.add(acc, 3)) }
        |}
        |
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
        |""".stripMargin
    assertEquals(payload(onSmallStack(runProgram(program + "{ viaLet(100000, 0) }"))), BigInt(200000))
    assertEquals(payload(onSmallStack(runProgram(program + "{ viaBlock(100000, 0) }"))), BigInt(300000))
    assertEquals(ctorName(onSmallStack(runProgram(program + "{ even(100001) }"))), "Bool.false")
  }

  test("the branch a structure-eta view chooses on a neutral is a tail position") {
    // Checking `deep` evaluates `viaEta` with `x` a variable: each step's inner match fires on `x`'s eta view.
    val program =
      """
        |struct Box : Type
        | | mk (a: Nat)(b: Nat) : Box
        |
        |def viaEta (n: Nat)(acc: Nat)(x: Box): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => acc
        |  | Nat.succ p => {
        |    match x returning Nat with
        |    | Box.mk a b => viaEta(p, Nat.add(acc, 1), x)
        |  }
        |}
        |
        |def deep (x: Box): Eq(Nat, viaEta(20000, 0, x), 20000) := Eq.refl(20000)
        |""".stripMargin
    onSmallStack(typecheckDecls(program))
  }

  test("a tail call binds its evidence deferred, as any call does, and forces none") {
    // `spin(k)` makes 2^k calls; a proposition that called it on every one of the 100,000 steps would dominate the run.
    val program =
      """
        |inductive IsTrue indices (b: Bool) : Prop
        | | yes : IsTrue(Bool.true)
        |
        |def spin (n: Nat): Bool decreases structural(n) := match n returning Bool with
        | | Nat.zero => Bool.true
        | | Nat.succ k => Bool.and(spin(k), spin(k))
        |
        |def count (n: Nat)(acc: Nat)[h: IsTrue(spin(10))]: Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => acc
        |  | Nat.succ k => count(k, Nat.add(acc, 1))
        |}
        |
        |{ count(100000, 0) }
        |""".stripMargin
    val before = Value.DeferredEvidence.forcings.get()
    assertEquals(payload(onSmallStack(runProgram(program))), BigInt(100000))
    assertEquals(Value.DeferredEvidence.forcings.get() - before, 0L)
  }

  test("a tail call runs the callee's body in the callee's closure, and a closure it builds is the same closure") {
    val source =
      """
        |def adder (n: Nat): Nat -> Nat := fun (x: Nat): Nat => Nat.add(x, n)
        |
        |def pick (b: Bool)(n: Nat): Nat -> Nat := {
        |  let m := Nat.mul(n, 10)
        |  match b returning Nat -> Nat with
        |  | Bool.true => adder(m)
        |  | Bool.false => adder(n)
        |}
        |
        |def use (f: Nat -> Nat)(y: Nat): Nat := {
        |  let z := Nat.mul(y, 10)
        |  f(z)
        |}
        |""".stripMargin
    assertEquals(payload(runProgram(source + "{ pick(Bool.true, 2)(5) }")), BigInt(25))
    assertEquals(payload(runProgram(source + "{ pick(Bool.false, 2)(5) }")), BigInt(7))
    // `f`'s body reads `n`, which only `adder`'s closure binds, not `use`'s body where `f` is applied.
    assertEquals(payload(runProgram(source + "{ use(adder(3), 2) }")), BigInt(23))
    val env = parse(source).decls.foldLeft(Prelude.default.checkedEnv) { case (current, decl) =>
      Interpreter.evalDecl(decl, current)
    }
    val built = Interpreter.evalApply(env("pick"), Vector(runProgram("{ Bool.true }"), runProgram("{ 2 }")))
    val direct = Interpreter.evalApply(env("adder"), Vector(runProgram("{ 20 }")))
    // One lambda node, closed over the same captures.
    (built, direct) match {
      case (
            Value.VLam(_, Value.ValueId.LocalId(builtNode, builtCaptures), _),
            Value.VLam(_, Value.ValueId.LocalId(directNode, directCaptures), _)
          ) =>
        assertEquals(builtNode, directNode)
        assertEquals(builtCaptures.map(payload), directCaptures.map(payload))
      case other => fail(s"Expected two local closures, got $other")
    }
  }

  test("a match on a neutral reached through tail positions is the same stuck match, and resumes when solved") {
    val program = parse(
      """
        |def count (n: Nat)(acc: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => acc
        |  | Nat.succ k => count(k, Nat.succ(acc))
        |}
        |
        |def probe (b: Bool)(n: Nat): Nat := {
        |  let m := Nat.succ(n)
        |  { match b returning Nat with
        |    | Bool.true => count(100000, m)
        |    | Bool.false => n
        |  }
        |}
        |
        |def outer (b: Bool)(n: Nat): Nat := probe(b, n)
        |""".stripMargin
    )
    val env = program.decls.foldLeft(Prelude.default.checkedEnv) { case (current, decl) =>
      Interpreter.evalDecl(decl, current)
    }
    val bool = env("Bool")
    val three = runProgram("{ 3 }")
    val b = FreshVar.freshVar("b", bool)
    val thunk = Interpreter.evalApply(env("outer"), Vector(b, three)) match {
      case thunk: Value.NeutralThunk => thunk
      case other                     => fail(s"Expected a stuck match, got $other")
    }
    assertEquals(thunk.term.cases.map(_.ctorName), Vector("Bool.true", "Bool.false"))
    // The match closes over what it mentions, as bound where it stands: the parameters and the let.
    assertEquals(thunk.env.locals.keys.map(_.name).toSet, Set("b", "n", "m"))
    assertEquals(
      thunk.env.locals.collectFirst { case (ref, value) if ref.name == "m" => payload(value) },
      Some(BigInt(4))
    )
    assert(thunk.tpe eq env("Nat"))
    assertEquals(thunk.blockedOn, DepSet(b.id))
    assert(ValueEquivalence.defEq(thunk, Interpreter.evalApply(env("probe"), Vector(b, three))))

    // Resumed, the chosen branch runs its tail loop in a small stack too.
    def solved(solution: Value): Value =
      onSmallStack(Interpreter.resolveInEqStore(thunk, EqStore.empty.allow(DepSet(b.id)).addLink(b.id, solution)))
    assertEquals(payload(solved(runProgram("{ Bool.true }"))), BigInt(100004))
    assertEquals(payload(solved(runProgram("{ Bool.false }"))), BigInt(3))

    val rigid = Value.VConst("k", Value.Symbol, bool)
    Interpreter.evalApply(env("outer"), Vector(rigid, three)) match {
      case stuck: Value.NeutralThunk => assert(stuck.blockedOn.isEmpty)
      case other                     => fail(s"Expected a rigid stuck match, got $other")
    }
  }

  test("a proof-valued lambda applied in tail position gives the canonical proof") {
    val result = runProgram(
      """
        |def lemma (n: Nat): Eq(Nat, n, n) := Eq.refl(n)
        |
        |def via (A: Type)(B: Prop)(f: A -> B)(x: A): B := f(x)
        |
        |{ via(Nat, Eq(Nat, 3, 3), fun (n: Nat): Eq(Nat, 3, 3) => lemma(3), 0) }
        |""".stripMargin
    )
    assertEquals(ctorName(result), "Eq.refl")
  }

  test("a native operation in tail position computes or keeps a compact Nat prefix") {
    val program = parse(
      """
        |def small (n: Nat): Nat := Nat.add(n, 2)
        |
        |def large (n: Nat): Nat := Nat.add(n, 1000)
        |""".stripMargin
    )
    val env = program.decls.foldLeft(Prelude.default.checkedEnv) { case (current, decl) =>
      Interpreter.evalDecl(decl, current)
    }
    assertEquals(payload(Interpreter.evalApply(env("small"), Vector(runProgram("{ 5 }")))), BigInt(7))
    val k = Value.VConst("k", Value.Symbol, env("Nat"))
    val unfolded = Interpreter.evalApply(env("small"), Vector(k))
    assert(
      ValueEquivalence.defEq(
        unfolded,
        Interpreter.evalApply(env("Nat.succ"), Vector(Interpreter.evalApply(env("Nat.succ"), Vector(k))))
      )
    )
    val big = runProgram("{ 1000 }")
    Interpreter.evalApply(env("large"), Vector(k)) match {
      case prefix: Value.VNatPrefix =>
        assert(prefix.base eq k)
        assertEquals(prefix.offset, payload(big))
        assert(ValueEquivalence.defEq(prefix.tpe, env("Nat")))
      case other => fail(s"Expected a compact Nat prefix, got $other")
    }
  }
}
