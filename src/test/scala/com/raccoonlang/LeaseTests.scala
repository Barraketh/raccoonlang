package com.raccoonlang

import com.raccoonlang.Value.VPi
import com.raccoonlang.telescope.{BinderOps, Projection}
import com.raccoonlang.{CoreAst => CA}

import java.nio.file.Paths

/**
 * Leases and tokens end to end (spec §4.4, §4.2, §8): the sealed `Lease` and `Tok` module of `TestSupport.leaseModule`,
 * its `withLease`, and clients in another file. One definition serves callbacks and results of both kinds; a token is
 * consumed inside its scope; and a residual re-evaluated gives what checking computed.
 */
class LeaseTests extends munit.FunSuite with TestSupport {
  import TestSupport.leaseModule

  /** The three callers of spec §4.4, each over locals `t: Tok(m)` or `g: Lease(m)` bound by its header. */
  private val callers = Vector(
    "def first : Nat := withLease(fun (l: Lifetime)(h: Lease(l)): Nat => 0)\n",
    "def second {m: Lifetime}(t: Tok(m)): Tok(m) := withLease(fun (l: Lifetime)(h: Lease(l)): Tok(m) => t)\n",
    "def third {m: Lifetime}(g: Lease(m)): Nat := withLease(fun (l: Lifetime)(h: Lease(l)): Nat => useLease(g))\n"
  )

  /**
   * A client's last definition, a call of `withLease`, checked in the environment of the module and the client's
   * earlier declarations, under its header's binders: that environment, the call's source and its checked form.
   */
  private def checkCall(client: String): (Env, CA.Term.App, TypeChecker.CheckedTerm) = {
    val core = Elaborator.elab(outsideProgram(leaseModule, client), suitePrelude)
    val env = core.decls.dropRight(1).foldLeft(suitePrelude.checkedEnv)((env, decl) => Interpreter.evalDecl(decl, env))
    val (bodyEnv, body) = core.decls.last match {
      case CA.Decl.ConstDecl(_, _, _, CA.ConstBody.TermBody(lam: CA.Term.Lam), _, _) =>
        (BinderOps.checkBinders(lam.ty.binders, env, familyParams = 0, lam.ty.span).env, lam.body)
      case CA.Decl.ConstDecl(_, _, _, CA.ConstBody.TermBody(body), _, _) => (env, body)
      case other                                                         => fail(s"Expected a definition, got $other")
    }
    body match {
      case call: CA.Term.App => (bodyEnv, call, TypeChecker.checkTerm(call, bodyEnv))
      case other             => fail(s"Expected a call, got $other")
    }
  }

  /** A checked call's residual argument, its callback. */
  private def callbackResidual(checked: TypeChecker.CheckedTerm): CA.Term =
    checked.residual match {
      case CA.Term.App(_, Vector(callback), _) => callback
      case other                               => fail(s"Expected a call residual, got $other")
    }

  /** `withLease`'s implicits, read off its callback's value the way checking and evaluation both read them. */
  private def solutions(env: Env, callback: Value): Map[String, String] =
    env("withLease").tpe match {
      case pi: VPi =>
        pi.binders.collect {
          case binder if binder.isImplicit =>
            binder.name -> Projection.project(binder.projection.get, Vector(callback)).fold(fail(_), _.toString)
        }.toMap
      case other => fail(s"Expected a function type, got $other")
    }

  test("withLease serves the three callers of spec §4.4, forcing k and S through A's sort and kf, Sf by the closure") {
    val expected = Vector(
      Map("k" -> "Kind.unr", "S" -> "Lifetime.empty", "A" -> "Nat", "kf" -> "Kind.unr", "Sf" -> "Lifetime.empty"),
      Map("k" -> "Kind.lin", "S" -> "m", "A" -> "Tok(m)", "kf" -> "Kind.lin", "Sf" -> "m"),
      Map("k" -> "Kind.unr", "S" -> "Lifetime.empty", "A" -> "Nat", "kf" -> "Kind.unr", "Sf" -> "m")
    )
    callers.zip(expected).foreach { case (caller, solved) =>
      val (env, _, checked) = checkCall(caller)
      assertEquals(solutions(env, Interpreter.evalTerm(callbackResidual(checked), env)), solved, caller)
    }
  }

  test("the callers run, with a token issued for a lease and burned inside its scope") {
    val client = callers.mkString("\n") +
      "\n{ withLease(fun (m: Lifetime)(g: Lease(m)): Nat => Nat.add(first, Nat.add(burn(second(issue(g))), third(g)))) }\n"
    assertEquals(outside(leaseModule, client).map(PrettyPrinter.print), Some("3"))
  }

  test("re-evaluating a caller's residual gives the checked value, its callback's derived closure included") {
    assert(ValueEquivalence.keyAssertionsEnabled)
    callers.foreach { caller =>
      val (env, call, checked) = checkCall(caller)
      val reevaluated = Interpreter.evalTerm(checked.residual, env)
      assertEquals(reevaluated.key, checked.value.key, caller)
      assert(ValueEquivalence.defEq(reevaluated, checked.value), caller)
      // Evaluating the callback's residual derives its closure from the captures it carries, and gives the type
      // checking the source gave.
      val callbackType = Interpreter.evalTerm(callbackResidual(checked), env).tpe
      val checkedType = TypeChecker.checkTerm(call.args.head, env).value.tpe
      assertEquals(callbackType.key, checkedType.key, caller)
      assert(ValueEquivalence.defEq(callbackType, checkedType), caller)
    }
  }

  test("a token can neither leave its scope nor be dropped, so it is consumed inside it") {
    // In the module, where a token is made directly.
    inside(leaseModule, "def spent : Nat := scope l => burn(Tok.mk(l))\n")
    assertEquals(
      expectOnly[LifetimeEscapes](inside(leaseModule, "def spent : Nat := burn(scope l => Tok.mk(l))\n")).lifetime,
      "l"
    )
    assertEquals(
      expectOnly[LinearUnused](inside(leaseModule, "def spent : Nat := scope l => {\n  let t := Tok.mk(l)\n  0\n}\n")),
      LinearUnused("t")
    )
    // In a client, where a token comes from a lease its callback holds.
    def client(body: String): String = s"def spent : Nat := withLease(fun (l: Lifetime)(h: Lease(l)): Nat => $body)\n"
    outside(leaseModule, client("burn(issue(h))"))
    assertEquals(
      expectOnly[LinearUnused](outside(leaseModule, client("{\n  let t := issue(h)\n  0\n}"))),
      LinearUnused("t")
    )
  }

  test("neither a lease nor a token can be returned from withLease's callback, since A is bound outside it") {
    def client(result: String, body: String): String =
      s"def leaked : Nat := withLease(fun (l: Lifetime)(h: Lease(l)): $result => $body)\n"
    outside(leaseModule, client("Nat", "useLease(h)"))
    // A is read off the callback's result, which depends on the callback's own lifetime binder.
    for ((result, body) <- Vector("Lease(l)" -> "h", "Tok(l)" -> "issue(h)")) {
      val failed = expectOnly[ImplicitReconstructionFailed](outside(leaseModule, client(result, body)))
      assertEquals(failed.fn, "withLease")
    }
  }

  test("a closure that names the callback's lifetime but captures nothing scoped may leave it") {
    def client(body: String): String =
      "def leave : Unit -> Nat :=\n" +
        s"  withLease(fun (l: Lifetime)(h: Lease(l)): Unit -> Nat => fun (u: Unit): Nat => $body)\n\n{ leave(Unit.unit) }\n"
    val named = client("List.length(List.nil(Lease(l)))")
    assertEquals(outside(leaseModule, named).map(PrettyPrinter.print), Some("0"))
    // Capturing the lease puts `l` in the closure's scope, and a lambda's type is exact wherever it stands.
    val mismatch = expectOnly[TypeMismatch](outside(leaseModule, client("useLease(h)")))
    assertEquals(mismatch.actual.toString, "{ scope = l } (u: Unit) -> Nat")
  }

  test("a callback at a kind variable serves both kinds and is applied once") {
    // Applying the callback twice would copy a linear one; fixing its kind at `Kind.unr` refuses a linear one.
    def module(kindBinder: String, kind: String, body: String): String =
      leaseModule +
        s"\ndef withTwo $kindBinder{Sf: Lifetime}(f: { ${kind}scope = Sf } (l: Lifetime) -> Lease(l) -> Nat): Nat :=\n" +
        s"  scope l => $body\n"
    val (once, twice) = ("f(l, Lease.mk(l))", "Nat.add(f(l, Lease.mk(l)), f(l, Lease.mk(l)))")
    val client =
      """
        |def both {m: Lifetime}(t: Tok(m)): Nat :=
        |  Nat.add(withTwo(fun (l: Lifetime)(h: Lease(l)): Nat => 5), withTwo(fun (l: Lifetime)(h: Lease(l)): Nat => burn(t)))
        |
        |{ withLease(fun (m: Lifetime)(g: Lease(m)): Nat => both(issue(g))) }
        |""".stripMargin
    assertEquals(outside(module("{kf: Kind}", "kind = kf, ", once), client).map(PrettyPrinter.print), Some("6"))
    assertEquals(
      expectOnly[LinearReused](typecheckDecls(module("{kf: Kind}", "kind = kf, ", twice))),
      LinearReused("f")
    )
    typecheckDecls(module("", "", twice))
    expectOnly[TypeMismatch](outside(module("", "", twice), client))
  }

  test("a proposition about a lease is scoped by its lifetime, its proofs are unrestricted, and none holds a token") {
    // A proof is unrestricted however its proposition is scoped: here one is never used.
    outside(leaseModule, "def fact {m: Lifetime}(g: Lease(m))(p: Eq(Nat, useLease(g), 2)): Nat := useLease(g)\n")
    val inType = expectOnly[LinearInType](
      outside(leaseModule, "def fact {m: Lifetime}(t: Tok(m))(p: Eq(Nat, burn(t), 1)): Nat := burn(t)\n")
    )
    assertEquals(inType.term.toString, "t")
    // The prelude's Eq is at `Kind.unr`, so an equation between tokens is not even a proposition.
    expectOnly[TypeMismatch](outside(leaseModule, "def fact {m: Lifetime}(t: Tok(m))(p: Eq(Tok(m), t, t)): Nat := 0\n"))
    // A proposition naming the atom is confined to its scope like any type.
    def proposition(about: String): String =
      s"def P : Prop := scope l => Eq(List($about), List.nil($about), List.nil($about))\n"
    outside(leaseModule, proposition("Lease(Lifetime.empty)"))
    expectOnly[LifetimeEscapes](outside(leaseModule, proposition("Lease(l)")))
  }

  test("the leases example runs") {
    val entry = Paths.get("examples", "leases", "main.rac").toAbsolutePath
    val loaded = ModuleLoader.load(entry, ModuleLoader.LoadConfig.forEntry(entry, suitePrelude))
    val result = Interpreter.run(TypeChecker.check(Elaborator.elaborate(loaded.program, suitePrelude)))
    assertEquals(result.map(PrettyPrinter.print), Some("11"))
  }
}
