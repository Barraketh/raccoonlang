package com.raccoonlang

import com.raccoonlang.CoreAst.{Case, Decl, DecreaseSpec, RecursiveDef, Term}

class RecursiveDefBlockTests extends munit.FunSuite {
  private val span = Span(0, 1)
  private def global(name: String): Term.GlobalRef = Term.GlobalRef(name, span)
  private def local(ref: CoreAst.LocalRef): Term.LocalRef = Term.LocalRef(ref, span)
  private def app(fn: Term, args: Term*): Term.App = Term.App(fn, args.toVector, span)
  private def binder(ref: CoreAst.LocalRef, ty: Term): CoreAst.Binder = CoreAst.Binder(ref, ty, span)
  private def pi(refs: CoreAst.LocalRef*): Term.Pi =
    Term.Pi(refs.toVector.map(ref => binder(ref, global("Nat"))), global("Nat"), span)

  private val natDecl = Decl.InductiveDecl(
    CoreAst.InductiveHeader("Nat", Vector.empty, Vector.empty, global("Type"), span),
    Vector(
      CoreAst.ConstructorDecl("Nat.zero", "zero", Vector.empty, global("Nat"), span),
      CoreAst.ConstructorDecl(
        "Nat.succ",
        "succ",
        Vector(binder(CoreAst.LocalRef(2, "tail"), global("Nat"))),
        global("Nat"),
        span
      )
    ),
    span
  )

  private def natEnv: Env = TypeChecker.checkProgram(CoreAst.Program(Vector(natDecl), None))._1

  private def mutual(nonDecreasing: Boolean = false): Decl.RecursiveDefBlock = {
    val f = CoreAst.LocalRef(10, "walkA")
    val g = CoreAst.LocalRef(11, "walkB")
    val a = CoreAst.LocalRef(12, "a")
    val b = CoreAst.LocalRef(13, "b")
    val aField = CoreAst.LocalRef(14, "aTail")
    val bField = CoreAst.LocalRef(15, "bTail")
    val fCallArg = if (nonDecreasing) local(a) else local(aField)
    val fBody = Term.Match(
      local(a),
      Some(global("Nat")),
      Vector(
        Case("Nat.zero", true, Vector.empty, global("Nat.zero"), span),
        Case("Nat.succ", true, Vector(Some(aField)), app(local(g), fCallArg), span)
      ),
      span
    )
    val gBody = Term.Match(
      local(b),
      Some(global("Nat")),
      Vector(
        Case("Nat.zero", true, Vector.empty, global("Nat.zero"), span),
        Case("Nat.succ", true, Vector(Some(bField)), app(local(f), local(bField)), span)
      ),
      span
    )
    val decA = DecreaseSpec.Lexicographic(Vector(a), span)
    val decB = DecreaseSpec.Lexicographic(Vector(b), span)
    Decl.RecursiveDefBlock(
      Vector(
        RecursiveDef("walkA", f, pi(a), fBody, decA, span),
        RecursiveDef("walkB", g, pi(b), gBody, decB, span)
      ),
      span
    )
  }

  test("mutual recursive calls check and execute") {
    val env = TypeChecker.checkProgram(CoreAst.Program(Vector(mutual()), None), natEnv)._1
    val zero = Interpreter.evalTerm(global("Nat.zero"), env)
    val one = Interpreter.evalApply(env("Nat.succ"), Vector(zero))
    TypeChecker.checkTerm(app(global("walkA"), app(global("Nat.succ"), global("Nat.zero"))), env)
    val result = Interpreter.evalApply(env("walkA"), Vector(one))
    result match {
      case Value.VCtor(head, _, _)                                      => assertEquals(head.name, "Nat.zero")
      case packed: Value.VPacked if packed.natValue.contains(BigInt(0)) =>
      case other                                                        => fail(s"expected Nat.zero, got $other")
    }
  }

  test("nondecreasing cross-peer calls are rejected") {
    intercept[NonDecreasingRecursiveCall] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(mutual(nonDecreasing = true)), None), natEnv)
    }
  }

  test("incompatible metric vectors are rejected before publication") {
    val block = mutual()
    val first = block.definitions.head
    val extra = CoreAst.LocalRef(99, "extra")
    val malformed = block.copy(
      definitions = block.definitions.updated(
        0,
        first.copy(
          ty = pi(first.ty.binders.head.localRef, extra),
          decreases = DecreaseSpec.Lexicographic(Vector(first.ty.binders.head.localRef, extra), span)
        )
      )
    )
    intercept[InvalidDecreaseSpec] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(malformed), None), natEnv)
    }
  }

  test("a later member failure leaves the group unpublished") {
    val block = mutual().copy(
      definitions = mutual().definitions.updated(
        1,
        mutual().definitions(1).copy(body = local(CoreAst.LocalRef(999, "missing")))
      )
    )
    val base = natEnv
    intercept[NotFound] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(block), None), base)
    }
    assert(!base.globals.contains("walkA"))
    assert(!base.globals.contains("walkB"))
  }

  test("equal-prefix later-component peer calls are accepted") {
    val f = CoreAst.LocalRef(30, "lexA")
    val g = CoreAst.LocalRef(31, "lexB")
    val ap = CoreAst.LocalRef(32, "ap")
    val bp = CoreAst.LocalRef(33, "bp")
    val at = CoreAst.LocalRef(34, "at")
    val bt = CoreAst.LocalRef(35, "bt")
    val fBody = Term.Match(
      local(at),
      Some(global("Nat")),
      Vector(
        Case("Nat.zero", true, Vector.empty, global("Nat.zero"), span),
        Case("Nat.succ", true, Vector(Some(bt)), app(local(g), local(ap), local(bt)), span)
      ),
      span
    )
    val gBody = Term.LocalRef(bt, span)
    val decF = DecreaseSpec.Lexicographic(Vector(ap, at), span)
    val decG = DecreaseSpec.Lexicographic(Vector(bp, bt), span)
    val block = Decl.RecursiveDefBlock(
      Vector(
        RecursiveDef("lexA", f, pi(ap, at), fBody, decF, span),
        RecursiveDef("lexB", g, pi(bp, bt), gBody, decG, span)
      ),
      span
    )
    TypeChecker.checkProgram(CoreAst.Program(Vector(block), None), natEnv)
  }

  test("group shape and measure specifications are rejected") {
    val base = natEnv
    intercept[InvalidRecursiveGroup] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(Decl.RecursiveDefBlock(Vector.empty, span)), None), base)
    }
    val duplicate = mutual().copy(
      definitions = mutual().definitions.updated(1, mutual().definitions(1).copy(name = "walkA"))
    )
    intercept[InvalidRecursiveGroup] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(duplicate), None), base)
    }
    val measured = mutual().copy(
      definitions = mutual().definitions.updated(
        0,
        mutual().definitions.head.copy(decreases = DecreaseSpec.Measure(local(CoreAst.LocalRef(12, "a")), span))
      )
    )
    intercept[InvalidDecreaseSpec] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(measured), None), base)
    }
  }

  test("raw peer values cannot be stored in group results") {
    val block = mutual()
    val first = block.definitions.head
    val stored = first.copy(
      body = Term.Body(
        Vector(CoreAst.Let(CoreAst.LocalRef(80, "stored"), None, local(block.definitions(1).peerRef), span)),
        global("Nat.zero"),
        span
      )
    )
    intercept[InvalidRecursiveOccurrence] {
      TypeChecker.checkProgram(
        CoreAst.Program(Vector(block.copy(definitions = block.definitions.updated(0, stored))), None),
        natEnv
      )
    }
  }
}
