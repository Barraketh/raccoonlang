package com.raccoonlang

import com.raccoonlang.CoreAst.{Decl, DecreaseSpec, RecursiveDef, Term}

class RecursiveDefBlockTests extends munit.FunSuite with DiagnosticAssertions {
  private val span = Span(0, 0)

  private def global(name: String): Term.GlobalRef = Term.GlobalRef(name, span)
  private def local(ref: CoreAst.LocalRef): Term.LocalRef = Term.LocalRef(ref, span)
  private def app(fn: Term, args: Term*): Term.App = Term.App(fn, args.toVector, span)
  private def binder(ref: CoreAst.LocalRef, tpe: Term): CoreAst.Binder = CoreAst.Binder(ref, tpe, span)
  private def pi(ref: CoreAst.LocalRef, input: Term, output: Term): Term.Pi =
    Term.Pi(Vector(binder(ref, input)), output, span)
  private def pi2(first: CoreAst.LocalRef, firstType: Term, second: CoreAst.LocalRef, secondType: Term): Term.Pi =
    Term.Pi(Vector(binder(first, firstType), binder(second, secondType)), global("GroupResult"), span)

  private def installSource(source: String, initial: Env): Env =
    LanguageParser.parseProgram(source) match {
      case Success(program, _, _) =>
        Elaborator.elab(program, Prelude.test).decls.foldLeft(initial) { case (env, declaration) =>
          Interpreter.evalDecl(declaration, env)
        }
      case failure: Failure => fail(s"failed to parse nested-container fixture: $failure")
    }

  private def installMutualFamilies(): Env = {
    val aToB = CoreAst.LocalRef(1, "b")
    val bToA = CoreAst.LocalRef(2, "a")
    val familyA = Decl.InductiveDecl(
      CoreAst.InductiveHeader("GroupA", Vector.empty, Vector.empty, global("Type"), span),
      Vector(
        CoreAst.ConstructorDecl("GroupA.leaf", "leaf", Vector.empty, global("GroupA"), span),
        CoreAst.ConstructorDecl(
          "GroupA.toB",
          "toB",
          Vector(binder(aToB, global("GroupB"))),
          global("GroupA"),
          span
        )
      ),
      span
    )
    val familyB = Decl.InductiveDecl(
      CoreAst.InductiveHeader("GroupB", Vector.empty, Vector.empty, global("Type"), span),
      Vector(
        CoreAst.ConstructorDecl("GroupB.leaf", "leaf", Vector.empty, global("GroupB"), span),
        CoreAst.ConstructorDecl(
          "GroupB.toA",
          "toA",
          Vector(binder(bToA, global("GroupA"))),
          global("GroupB"),
          span
        )
      ),
      span
    )
    val result = Decl.InductiveDecl(
      CoreAst.InductiveHeader("GroupResult", Vector.empty, Vector.empty, global("Type"), span),
      Vector(CoreAst.ConstructorDecl("GroupResult.zero", "zero", Vector.empty, global("GroupResult"), span)),
      span
    )
    val withResult = Interpreter.evalDecl(result, Prelude.test.checkedEnv)
    Interpreter.evalDecl(
      Decl.InductiveBlock(Vector(familyA, familyB), span),
      withResult
    )
  }

  private def mutualFunctions(nonDecreasing: Boolean = false): Decl.RecursiveDefBlock = {
    val fPeer = CoreAst.LocalRef(10, "walkA")
    val gPeer = CoreAst.LocalRef(11, "walkB")
    val a = CoreAst.LocalRef(12, "a")
    val b = CoreAst.LocalRef(13, "b")
    val aField = CoreAst.LocalRef(14, "b")
    val bField = CoreAst.LocalRef(15, "a")
    val fBody = Term.Match(
      local(a),
      Some(global("GroupResult")),
      Vector(
        CoreAst.Case("GroupA.leaf", true, Vector.empty, global("GroupResult.zero"), span),
        CoreAst.Case(
          "GroupA.toB",
          true,
          Vector(Some(aField)),
          app(local(gPeer), if (nonDecreasing) global("GroupB.leaf") else local(aField)),
          span
        )
      ),
      span
    )
    val gBody = Term.Match(
      local(b),
      Some(global("GroupResult")),
      Vector(
        CoreAst.Case("GroupB.leaf", true, Vector.empty, global("GroupResult.zero"), span),
        CoreAst.Case(
          "GroupB.toA",
          true,
          Vector(Some(bField)),
          app(local(fPeer), local(bField)),
          span
        )
      ),
      span
    )
    Decl.RecursiveDefBlock(
      Vector(
        RecursiveDef(
          "walkA",
          fPeer,
          pi(a, global("GroupA"), global("GroupResult")),
          fBody,
          DecreaseSpec.Lexicographic(Vector(a), span),
          span
        ),
        RecursiveDef(
          "walkB",
          gPeer,
          pi(b, global("GroupB"), global("GroupResult")),
          gBody,
          DecreaseSpec.Lexicographic(Vector(b), span),
          span
        )
      ),
      span
    )
  }

  test("recursive groups check and run cross-component structural calls") {
    val env = Interpreter.evalDecl(mutualFunctions(), installMutualFamilies())
    val input = app(global("GroupA.toB"), global("GroupB.leaf"))
    val result = TypeChecker.checkTerm(app(global("walkA"), input), env).value
    result match {
      case Value.VCtor(head, _, _) => assertEquals(head.name, "GroupResult.zero")
      case other                   => fail(s"expected GroupResult.zero, got $other")
    }
    assert(env.globals("walkA").isInstanceOf[GlobalBinding.Lazy])
    assert(env.globals("walkB").isInstanceOf[GlobalBinding.Lazy])
  }

  test("cross-component calls must descend from the caller metric") {
    val base = installMutualFamilies()
    interceptError[NonDecreasingRecursiveCall] {
      Interpreter.evalDecl(mutualFunctions(nonDecreasing = true), base)
    }
    val recovered = Interpreter.evalDecl(mutualFunctions(), base)
    assert(recovered.globals("walkA").isInstanceOf[GlobalBinding.Lazy])
    assert(recovered.globals("walkB").isInstanceOf[GlobalBinding.Lazy])
  }

  test("recursive peers cannot bypass decrease checking through global spelling") {
    val block = mutualFunctions()
    val first = block.definitions.head
    val bypass = first.body match {
      case value: Term.Match =>
        val branch = value.cases(1)
        val field = branch.argRefs.headOption.flatten.getOrElse(fail("walkA recursive branch has no field"))
        value.copy(cases = value.cases.updated(1, branch.copy(body = app(global("walkB"), local(field)))))
      case other => fail(s"expected match body, got $other")
    }
    val malformed = block.copy(definitions = block.definitions.updated(0, first.copy(body = bypass)))

    interceptError[NotFound](Interpreter.evalDecl(malformed, installMutualFamilies()))
  }

  test("recursive groups reject a raw peer stored inside a result") {
    val base = installMutualFamilies()
    val functionField = CoreAst.LocalRef(120, "function")
    val argument = CoreAst.LocalRef(121, "argument")
    val holder = Decl.InductiveDecl(
      CoreAst.InductiveHeader("GroupHolder", Vector.empty, Vector.empty, global("Type"), span),
      Vector(
        CoreAst.ConstructorDecl(
          "GroupHolder.mk",
          "mk",
          Vector(binder(functionField, pi(argument, global("GroupA"), global("GroupResult")))),
          global("GroupHolder"),
          span
        )
      ),
      span
    )
    val holderEnv = Interpreter.evalDecl(holder, base)
    val firstPeer = CoreAst.LocalRef(122, "leakA")
    val secondPeer = CoreAst.LocalRef(123, "leakB")
    val firstArg = CoreAst.LocalRef(124, "a")
    val secondArg = CoreAst.LocalRef(125, "a")
    val leaking = Decl.RecursiveDefBlock(
      Vector(
        RecursiveDef(
          "leakA",
          firstPeer,
          pi(firstArg, global("GroupA"), global("GroupHolder")),
          app(global("GroupHolder.mk"), local(secondPeer)),
          DecreaseSpec.Lexicographic(Vector(firstArg), span),
          span
        ),
        RecursiveDef(
          "leakB",
          secondPeer,
          pi(secondArg, global("GroupA"), global("GroupHolder")),
          app(global("GroupHolder.mk"), local(firstPeer)),
          DecreaseSpec.Lexicographic(Vector(secondArg), span),
          span
        )
      ),
      span
    )

    interceptError[InvalidRecursiveOccurrence](Interpreter.evalDecl(leaking, holderEnv))
  }

  test("recursive groups reject incompatible metric vectors before checking bodies") {
    val block = mutualFunctions()
    val first = block.definitions.head
    val metric = first.ty.binders.head.localRef
    val extra = CoreAst.LocalRef(99, "extra")
    val extendedType = first.ty.copy(binders = first.ty.binders :+ binder(extra, global("GroupA")))
    val malformed = block.copy(
      definitions = block.definitions.updated(
        0,
        first.copy(ty = extendedType, decreases = DecreaseSpec.Lexicographic(Vector(metric, extra), span))
      )
    )
    interceptError[InvalidDecreaseSpec](Interpreter.evalDecl(malformed, installMutualFamilies()))
  }

  test("a later member failure leaves the whole recursive group unpublished and retryable") {
    val base = installMutualFamilies()
    val block = mutualFunctions()
    val second = block.definitions(1)
    val malformedBody = second.body match {
      case value: Term.Match =>
        val branch = value.cases(1)
        val nonDecreasingCall = app(local(block.definitions.head.peerRef), global("GroupA.leaf"))
        value.copy(cases = value.cases.updated(1, branch.copy(body = nonDecreasingCall)))
      case other => fail(s"expected match body, got $other")
    }
    val malformed = block.copy(definitions = block.definitions.updated(1, second.copy(body = malformedBody)))

    interceptError[NonDecreasingRecursiveCall](Interpreter.evalDecl(malformed, base))
    val recovered = Interpreter.evalDecl(block, base)
    assert(recovered.globals("walkA").isInstanceOf[GlobalBinding.Lazy])
    assert(recovered.globals("walkB").isInstanceOf[GlobalBinding.Lazy])
  }

  test("cross-peer lexicographic calls accept an equal prefix and later strict decrease") {
    val fPeer = CoreAst.LocalRef(40, "lexA")
    val gPeer = CoreAst.LocalRef(41, "lexB")
    val fPrefix = CoreAst.LocalRef(42, "prefix")
    val gPrefix = CoreAst.LocalRef(43, "prefix")
    val a = CoreAst.LocalRef(44, "a")
    val b = CoreAst.LocalRef(45, "b")
    val bField = CoreAst.LocalRef(46, "b")
    val aField = CoreAst.LocalRef(47, "a")
    val fBody = Term.Match(
      local(a),
      Some(global("GroupResult")),
      Vector(
        CoreAst.Case("GroupA.leaf", true, Vector.empty, global("GroupResult.zero"), span),
        CoreAst.Case(
          "GroupA.toB",
          true,
          Vector(Some(bField)),
          app(local(gPeer), local(fPrefix), local(bField)),
          span
        )
      ),
      span
    )
    val gBody = Term.Match(
      local(b),
      Some(global("GroupResult")),
      Vector(
        CoreAst.Case("GroupB.leaf", true, Vector.empty, global("GroupResult.zero"), span),
        CoreAst.Case(
          "GroupB.toA",
          true,
          Vector(Some(aField)),
          app(local(fPeer), local(gPrefix), local(aField)),
          span
        )
      ),
      span
    )
    val block = Decl.RecursiveDefBlock(
      Vector(
        RecursiveDef(
          "lexA",
          fPeer,
          pi2(fPrefix, global("GroupA"), a, global("GroupA")),
          fBody,
          DecreaseSpec.Lexicographic(Vector(fPrefix, a), span),
          span
        ),
        RecursiveDef(
          "lexB",
          gPeer,
          pi2(gPrefix, global("GroupA"), b, global("GroupB")),
          gBody,
          DecreaseSpec.Lexicographic(Vector(gPrefix, b), span),
          span
        )
      ),
      span
    )

    val env = Interpreter.evalDecl(block, installMutualFamilies())
    assert(env.globals.contains("lexA"))
    assert(env.globals.contains("lexB"))
  }

  test("recursive group shape and lexical scope are validated before publication") {
    val base = installMutualFamilies()
    interceptError[InvalidRecursiveGroup](Interpreter.evalDecl(Decl.RecursiveDefBlock(Vector.empty, span), base))

    val block = mutualFunctions()
    val duplicateName = block.copy(
      definitions = block.definitions.updated(1, block.definitions(1).copy(name = block.definitions.head.name))
    )
    interceptError[InvalidRecursiveGroup](Interpreter.evalDecl(duplicateName, base))

    val duplicateRef = block.copy(
      definitions = block.definitions.updated(1, block.definitions(1).copy(peerRef = block.definitions.head.peerRef))
    )
    interceptError[InvalidRecursiveGroup](Interpreter.evalDecl(duplicateRef, base))

    val recovered = Interpreter.evalDecl(block, base)
    assert(recovered.globals("walkA").isInstanceOf[GlobalBinding.Lazy])
    assert(recovered.globals("walkB").isInstanceOf[GlobalBinding.Lazy])
  }

  test("recursive groups reject measure specifications") {
    val block = mutualFunctions()
    val first = block.definitions.head
    val malformed = block.copy(
      definitions = block.definitions.updated(
        0,
        first.copy(decreases = DecreaseSpec.Measure(local(first.ty.binders.head.localRef), span))
      )
    )
    interceptError[InvalidDecreaseSpec](Interpreter.evalDecl(malformed, installMutualFamilies()))
  }

  test("recursive groups descend through a specialized nested container") {
    val base = installSource(
      """
        |inductive K6List (A: Type) : Type
        | | nil : K6List(A)
        | | cons (tail: K6List(A))(head: A) : K6List(A)
        |
        |inductive K6Tree : Type
        | | leaf : K6Tree
        | | node (children: K6List(K6Tree)) : K6Tree
        |""".stripMargin,
      installMutualFamilies()
    )
    val treePeer = CoreAst.LocalRef(30, "walkTree")
    val listPeer = CoreAst.LocalRef(31, "walkList")
    val tree = CoreAst.LocalRef(32, "tree")
    val list = CoreAst.LocalRef(33, "list")
    val children = CoreAst.LocalRef(34, "children")
    val tail = CoreAst.LocalRef(35, "tail")
    val head = CoreAst.LocalRef(36, "head")
    val listTree = app(global("K6List"), global("K6Tree"))
    val treeBody = Term.Match(
      local(tree),
      Some(global("GroupResult")),
      Vector(
        CoreAst.Case("K6Tree.leaf", true, Vector.empty, global("GroupResult.zero"), span),
        CoreAst.Case(
          "K6Tree.node",
          true,
          Vector(Some(children)),
          app(local(listPeer), local(children)),
          span
        )
      ),
      span
    )
    val listBody = Term.Match(
      local(list),
      Some(global("GroupResult")),
      Vector(
        CoreAst.Case("K6List.nil", true, Vector.empty, global("GroupResult.zero"), span),
        CoreAst.Case(
          "K6List.cons",
          true,
          Vector(Some(tail), Some(head)),
          app(local(treePeer), local(head)),
          span
        )
      ),
      span
    )
    val block = Decl.RecursiveDefBlock(
      Vector(
        RecursiveDef(
          "walkTree",
          treePeer,
          pi(tree, global("K6Tree"), global("GroupResult")),
          treeBody,
          DecreaseSpec.Lexicographic(Vector(tree), span),
          span
        ),
        RecursiveDef(
          "walkList",
          listPeer,
          pi(list, listTree, global("GroupResult")),
          listBody,
          DecreaseSpec.Lexicographic(Vector(list), span),
          span
        )
      ),
      span
    )

    val env = Interpreter.evalDecl(block, base)
    assert(env.globals.contains("walkTree"))
    assert(env.globals.contains("walkList"))
  }

  test("re-evaluated singleton recursion rebinds the copied lambda rather than a same-named global") {
    val env = installSource(
      """
        |inductive QuoteNat : Type
        | | zero : QuoteNat
        | | succ (n: QuoteNat) : QuoteNat
        |
        |def quotedPred (n: QuoteNat): QuoteNat decreases structural(n) := {
        |  match n with
        |  | QuoteNat.zero => QuoteNat.zero
        |  | QuoteNat.succ k => quotedPred(k)
        |}
        |
        |def poison (n: QuoteNat): QuoteNat := QuoteNat.succ(QuoteNat.zero)
        |""".stripMargin,
      Prelude.test.checkedEnv
    )
    val residual = env("quotedPred") match {
      case Value.VLam(_, _, Value.LamBody.Core(term, _)) => term
      case other                                         => fail(s"expected checked recursive lambda, got $other")
    }
    val poisoned = env.copy(globals = env.globals.updated("quotedPred", env.globals("poison")))
    val copied = Interpreter.evalTerm(residual, poisoned)
    val zero = poisoned("QuoteNat.zero")
    val one = Interpreter.evalApply(poisoned("QuoteNat.succ"), Vector(zero))
    val two = Interpreter.evalApply(poisoned("QuoteNat.succ"), Vector(one))

    Interpreter.evalApply(copied, Vector(two)) match {
      case Value.VCtor(head, _, _) => assertEquals(head.name, "QuoteNat.zero")
      case other                   => fail(s"expected QuoteNat.zero, got $other")
    }
  }
}
