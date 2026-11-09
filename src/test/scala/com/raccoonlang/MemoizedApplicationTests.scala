package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.ProgramFixtures.Programs
import com.raccoonlang.Value._

/**
 * Memoized application (docs/kernel.md, "Memoized application"): applying a closure records what it returned under the
 * arguments' key, and an application with the same key returns that value instead of running the body again. These
 * programs compute what they computed without the memo, wrong claims about those values are still refused, and the
 * memo keeps apart what it must: different arguments, suspended proofs, values across a linked variable or carrying
 * another context's variables, and a run inside a demanded proof.
 */
class MemoizedApplicationTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs._

  private def accepts(src: String)(implicit loc: munit.Location): Unit =
    try { runChecked(src); () }
    catch { case t: TypeError => fail("REJECTED (should accept): " + ErrorReporter.pretty(t, Source(src))) }

  private def rejects(src: String)(implicit loc: munit.Location): Unit =
    try {
      runChecked(src)
      fail("ACCEPTED (should be rejected)")
    } catch { case _: TypeError => () }

  /**
   * `chain(n)` is n closures, each reading its predecessor three times at its argument: without the memo, applying it
   * runs the first closure 3^n times; with it, each closure runs once per argument.
   */
  private val chain =
    """
      |def step (X: Nat -> Nat): Nat -> Nat := fun (r: Nat): Nat => Nat.add(X(r), Nat.add(X(r), X(r)))
      |
      |def chain (n: Nat): Nat -> Nat decreases structural(n) := {
      |  match n returning Nat -> Nat with
      |  | Nat.zero => fun (r: Nat): Nat => r
      |  | Nat.succ m => step(chain(m))
      |}
      |""".stripMargin

  test("a closure that reads its predecessor three times computes the same values") {
    assertEquals(result(chain + "chain(8)(2)"), "13122")
    accepts(chain + "def small : Eq(Nat, chain(8)(2), 13122) := Eq.refl(13122)\n")
    // 3^40 runs of the first closure without the memo; 41 with it.
    accepts(chain + "def deep : Eq(Nat, chain(40)(1), 12157665459056928801) := Eq.refl(12157665459056928801)\n")
  }

  test("a neutral argument keys as its variable, and the chain's symbolic value is the same") {
    accepts(chain + "def sym (b: Nat): Eq(Nat, chain(40)(b), Nat.mul(12157665459056928801, b)) := Eq.refl(Nat.mul(12157665459056928801, b))\n")
    accepts(
      chain +
        """
          |def at (b: Nat): Nat -> Nat := fun (t: Nat): Nat => Nat.add(chain(30)(b), t)
          |def two (b: Nat): Eq(Nat, Nat.add(at(b)(1), at(b)(1)), Nat.add(Nat.mul(411782264189298, b), 2)) :=
          |  Eq.refl(Nat.add(Nat.mul(411782264189298, b), 2))
          |""".stripMargin
    )
  }

  test("control: wrong values for memoized applications are still refused") {
    rejects(chain + "def deep : Eq(Nat, chain(40)(1), 12157665459056928800) := Eq.refl(12157665459056928800)\n")
    rejects(chain + "def sym (b: Nat): Eq(Nat, chain(40)(b), Nat.mul(12157665459056928801, Nat.succ(b))) := Eq.refl(Nat.mul(12157665459056928801, b))\n")
    // The second application hits nothing the first recorded: its argument's key differs.
    rejects(
      """
        |def f : Nat -> Nat := fun (x: Nat): Nat => Nat.mul(x, 3)
        |def same : Eq(Nat, f(1), f(2)) := Eq.refl(f(1))
        |""".stripMargin
    )
  }

  test("an application with the same key returns the recorded value; one with another key runs") {
    val env = declsEnv(
      """
        |def f : Nat -> Prod(Nat, Nat) := fun (x: Nat): Prod(Nat, Nat) => Prod.mk(Nat, Nat, x, Nat.mul(x, 3))
        |def a : Prod(Nat, Nat) := f(4)
        |def b : Prod(Nat, Nat) := f(Nat.add(2, 2))
        |def c : Prod(Nat, Nat) := f(5)
        |""".stripMargin
    )
    val f = env("f").asInstanceOf[VLam]
    assert(f.id.isInstanceOf[ValueId.LocalId], f.id)
    assertEquals(f.applied.size, 2)
    assert(env("a") eq env("b"), "the second application ran again")
    assertEquals(PrettyPrinter.print(env("c")), "Prod.mk(5, 15)")
  }

  test("a named definition is not memoized, and a closure built by each call starts without a memo") {
    val env = declsEnv(
      """
        |def g (x: Nat): Nat := Nat.add(x, 1)
        |def mk (k: Nat): Nat -> Nat := fun (x: Nat): Nat => Nat.add(x, k)
        |def a : Nat := Nat.add(g(1), g(1))
        |def h : Nat -> Nat := mk(2)
        |def b : Nat := Nat.add(h(1), mk(2)(1))
        |""".stripMargin
    )
    assertEquals(env("g").asInstanceOf[VLam].applied, null)
    assertEquals(env("h").asInstanceOf[VLam].applied.size, 1)
    assertEquals(PrettyPrinter.print(env("b")), "6")
  }

  test("an argument holding a suspended proof is not keyed, forced or not, and keying forces nothing") {
    val env = declsEnv(
      """
        |def lem (n: Nat) : Eq(Nat, n, n) := Eq.refl(n)
        |def p : Eq(Nat, 3, 3) := lem(3)
        |def use : (x: Nat) -> (h: Eq(Nat, 3, 3)) -> Nat := fun (x: Nat)(h: Eq(Nat, 3, 3)): Nat => Nat.succ(x)
        |def a : Nat := use(1, p)
        |def b : Nat := use(1, p)
        |""".stripMargin
    )
    val p = env("p").asInstanceOf[VSuspendedProof]
    val use = env("use").asInstanceOf[VLam]
    assert(p.forced eq null, "keying the application forced the proof")
    assertEquals(use.applied, null)
    assertEquals(PrettyPrinter.print(env("b")), "2")
    // A forced suspension shares its forced value's key, but the checker reads the two differently.
    Interpreter.force(p)
    assertEquals(PrettyPrinter.print(Interpreter.evalApply(use, Vector(env("a"), p))), "3")
    assertEquals(use.applied, null)
  }

  test("a value is not reused across a variable some store has linked") {
    val env = declsEnv("def f : Nat -> Prod(Nat, Nat) := fun (x: Nat): Prod(Nat, Nat) => Prod.mk(Nat, Nat, x, x)\n")
    val f = env("f")
    val x = FreshVar.freshVar("x", Kernel.natType)
    val first = Interpreter.evalApply(f, Vector(x))
    assert(Interpreter.evalApply(f, Vector(x)) eq first, "the second application ran again")
    // Linked in some branch's store: a store that solves it may substitute its solution, also into types that
    // mention it, where keys do not look, so neither the recorded value nor a new one is reused.
    EqStore.empty.allow(DepSet.single(x.id)).addLink(x.id, Kernel.zeroValue)
    val again = Interpreter.evalApply(f, Vector(x))
    assert(again ne first)
    assert(Interpreter.evalApply(f, Vector(x)) ne again)
    assertEquals(again.key, first.key)
  }

  test("a recorded value whose dependencies the arguments lack is not returned") {
    val env = declsEnv(
      """
        |def mk (p: Prod(Nat, Nat)) : Unit -> Nat := fun (u: Unit): Nat => p.fst
        |def wrap : (Unit -> Nat) -> Prod(Unit -> Nat, Nat) := fun (c: Unit -> Nat): Prod(Unit -> Nat, Nat) =>
        |  Prod.mk(Unit -> Nat, Nat, c, 0)
        |""".stripMargin
    )
    val y = FreshVar.freshVar("y", Kernel.natType)
    val z = FreshVar.freshVar("z", Kernel.natType)
    def closure(v: Value): Value =
      Interpreter.evalApply(env("mk"), Vector(Interpreter.evalApply(env("Prod.mk"), Vector(Kernel.natType, Kernel.natType, Kernel.zeroValue, v))))
    val (c1, c2) = (closure(y), closure(z))
    // One code reading one field of records that differ in another: equal keys, different dependencies.
    assertEquals(c1.key, c2.key)
    assert(c1.synDeps.contains(y.id) && c2.synDeps.contains(z.id))
    val wrap = env("wrap")
    assert(Interpreter.evalApply(wrap, Vector(c1)).synDeps.contains(y.id))
    val second = Interpreter.evalApply(wrap, Vector(c2))
    assert(second.synDeps.contains(z.id) && !second.synDeps.contains(y.id), second.synDeps)
  }

  test("applications inside and outside a demanded proof are keyed apart") {
    val args = Vector[Value](Kernel.zeroValue)
    assertNotEquals(ValueKey.applicationKey(args, forcing = true), ValueKey.applicationKey(args, forcing = false))
    assertEquals(ValueKey.applicationKey(args, forcing = false), ValueKey.applicationKey(args, forcing = false))
  }

  test("a closure records at most MemoCap applications, and those it recorded still answer") {
    val env = declsEnv("def f : Nat -> Prod(Nat, Nat) := fun (x: Nat): Prod(Nat, Nat) => Prod.mk(Nat, Nat, x, x)\n")
    val f = env("f")
    def at(n: Int): Value = Interpreter.evalApply(f, Vector(NatNormalForm.literal(BigInt(n))))
    val first = at(0)
    (1 until Interpreter.MemoCap + 10).foreach(at)
    assertEquals(f.asInstanceOf[VLam].applied.size, Interpreter.MemoCap)
    assert(at(0) eq first, "a recorded application ran again")
    assertEquals(PrettyPrinter.print(at(Interpreter.MemoCap + 5)), s"Prod.mk(${Interpreter.MemoCap + 5}, ${Interpreter.MemoCap + 5})")
  }

  test("every hit gives what running the body again gives") {
    var hits = 0
    Interpreter.hitCheck = (lam, args, known, fresh) => {
      hits += 1
      assertEquals(known.key, fresh.key, s"$lam on $args")
      assertEquals(known.tpe.key, fresh.tpe.key, s"$lam on $args")
      assert((known.synDeps -- fresh.synDeps).isEmpty, s"$lam on $args: ${known.synDeps} against ${fresh.synDeps}")
    }
    try {
      accepts(chain + "def small : Eq(Nat, chain(8)(2), 13122) := Eq.refl(13122)\n")
      accepts(chain + "def sym (b: Nat): Eq(Nat, chain(6)(b), Nat.mul(729, b)) := Eq.refl(Nat.mul(729, b))\n")
      accepts(
        """
          |def pick (n: Nat) : Nat -> Nat := {
          |  match n returning Nat -> Nat with
          |  | Nat.zero => fun (x: Nat): Nat => x
          |  | Nat.succ k => fun (x: Nat): Nat => Nat.add(x, k)
          |}
          |def twice (n: Nat)(x: Nat) : Nat := Nat.add(pick(n)(x), pick(n)(x))
          |def same (n: Nat)(x: Nat) : Eq(Nat, twice(n, x), Nat.add(pick(n)(x), pick(n)(x))) := Eq.refl(twice(n, x))
          |def at3 : Eq(Nat, twice(3, 4), 12) := Eq.refl(12)
          |""".stripMargin
      )
    } finally Interpreter.hitCheck = null
    assert(hits > 0)
  }

  test("keying a 100,000-deep chain of closures takes no host stack") {
    val src =
      """
        |def build (n: Nat)(acc: Nat -> Nat): Nat -> Nat decreases structural(n) := {
        |  match n returning Nat -> Nat with
        |  | Nat.zero => acc
        |  | Nat.succ k => build(k, fun (r: Nat): Nat => acc(r))
        |}
        |
        |def ignore : (Nat -> Nat) -> Nat := fun (g: Nat -> Nat): Nat => 7
        |
        |ignore(build(100000, fun (r: Nat): Nat => r))
        |""".stripMargin
    // The chain is built in a loop and never applied, so only its key and the memo's checks would read it deeply.
    assertEquals(Execution.onStack(1L << 20)(result(src)), "7")
  }

  test("a memoized closure in tail position takes no host stack") {
    val src =
      """
        |def count (n: Nat)(acc: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => acc
        |  | Nat.succ k => {
        |    let next := fun (a: Nat): Nat => count(k, a)
        |    next(Nat.add(acc, 1))
        |  }
        |}
        |
        |count(100000, 0)
        |""".stripMargin
    assertEquals(Execution.onStack(1L << 20)(result(src)), "100000")
  }
}
