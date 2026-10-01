package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.Projection

class ProjectionTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

  test("Pi-codomain projection peels one binder from a grouped telescope, keeping what its code captures") {
    val span = Span(0, 0)
    val env = Env.empty
    val typeSort = CoreTestTerms.sortAt(CoreAst.Form.LevelOne, span)
    val x = CoreAst.Binder(CoreAst.LocalRef(0, "x"), typeSort, span, CoreAst.BinderSite.Function, BinderMode.Explicit)
    val y = CoreAst.Binder(CoreAst.LocalRef(1, "y"), typeSort, span, CoreAst.BinderSite.Function, BinderMode.Explicit)
    val mentioned = FreshVar.freshValue("m", LifetimeTpe)._2.asInstanceOf[Value.Lifetime]
    val grouped = VPi(
      env,
      Vector(x, y),
      _ => Sorts.Type,
      Value.Kind.unr,
      Value.Lifetime.empty,
      mentioned,
      mentioned.synDeps,
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      () => Sorts.sort(Level.succ(Level.one), Value.Kind.unr, mentioned)
    )
    val root = VConst("f", Symbol, grouped)
    val tail = Projection
      .project(Projection.Spec(0, Vector(Projection.Step.Tpe, Projection.Step.PiCodomain)), Vector(root))
      .fold(failure => fail(failure.toString), identity)

    assertEquals(tail.asInstanceOf[VPi].binders.map(_.localRef), Vector(y.localRef))
    // The remaining group is the same function type's, so its sort counts the same captures.
    assert(Sorts.sortOf(tail).exists(_.scope == mentioned), tail.tpe)
    assert(
      Projection
        .project(Projection.Spec(0, Vector(Projection.Step.PiCodomain)), Vector(tail))
        .exists(ValueEquivalence.defEq(_, Sorts.Type))
    )
  }

  test("Pi-result projection crosses dependent grouped binders") {
    val span = Span(0, 0)
    val env = Env.empty
    val typeSort = CoreTestTerms.sortAt(CoreAst.Form.LevelOne, span)
    val x = CoreAst.Binder(CoreAst.LocalRef(0, "x"), typeSort, span, CoreAst.BinderSite.Function, BinderMode.Explicit)
    val y = CoreAst.Binder(
      CoreAst.LocalRef(1, "y"),
      CoreAst.Term.LocalRef(x.localRef, span),
      span,
      CoreAst.BinderSite.Function,
      BinderMode.Explicit
    )
    val grouped = VPi(
      env,
      Vector(x, y),
      _ => Sorts.Type,
      Value.Kind.unr,
      Value.Lifetime.empty,
      Value.Lifetime.empty,
      DepSet.empty,
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      () => Sorts.sort(Level.succ(Level.one), Value.Kind.unr, Value.Lifetime.empty)
    )

    assert(
      Projection
        .project(Projection.Spec(0, Vector(Projection.Step.PiResult)), Vector(grouped))
        .exists(ValueEquivalence.defEq(_, Sorts.Type))
    )
    assert(
      Projection.project(Projection.Spec(0, Vector(Projection.Step.PiCodomain)), Vector(grouped)).isLeft
    )
  }

  private def evalDecls(src: String): Env = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        core.decls.foldLeft(Prelude.test.checkedEnv) { case (cur, decl) =>
          Interpreter.evalDecl(decl, cur)
        }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  // Simple shapes for results, using the ordinary pattern view of constructor arguments.
  sealed trait Shape
  case class SConst(name: String) extends Shape
  case class SApp(head: Shape, args: List[Shape]) extends Shape

  private def toShape(v: Value): Shape = v match {
    case Value.ConstructorHead(n, _, _, _, _) => SConst(n)
    case Value.VCtor(h, storedArgs, _) =>
      val args = storedArgs
      if (args.isEmpty) SConst(h.name) else SApp(SConst(h.name), args.toList.map(toShape))
    case Value.VConst(n, _, _)     => SConst(n)
    case Value.VApp(h, args, _, _) => SApp(toShape(h), args.toList.map(toShape))
    case other                     => SConst(other.toString)
  }

  private val zeroS = SConst("Peano.zero")
  test("non-dependent projections: Couple.fst and Couple.snd") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |struct Couple (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Couple(A, B)
        |
        |def first {A1: Type}{B1: Type} (p: Couple(A1, B1)): A1 := p.fst
        |def second {A2: Type}{B2: Type} (p: Couple(A2, B2)): B2 := p.snd
        |
        |{
        |  let p : Couple(Peano, Peano) := Couple.mk(Peano.zero, Peano.succ(Peano.zero))
        |  first(p)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("struct syntax emits selectors whose bodies are matches on self") {
    val p =
      """
        |struct Couple (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Couple(A, B)
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        val found = core.decls.exists {
          case CoreAst.Decl.ConstDecl(
                false,
                "Couple.snd",
                _,
                CoreAst.ConstBody.TermBody(
                  CoreAst.Term.Lam(_, m: CoreAst.Term.Match, _, _, _, _, _)
                ),
                None,
                _
              ) =>
            m.cases.length == 1 && m.cases.head.ctorName.endsWith("mk") && m.cases.head.argRefs.length == 2
          case _ => false
        }
        assert(found, "expected Couple.snd to be a match on self returning its second field")
        Interpreter.run(core, Prelude.test)
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("generated positional projections resolve a namespaced family canonically") {
    typecheckDecls(
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |namespace Data {
        |  struct Box : Type
        |   | mk (value: Peano) : Box
        |
        |  def get (box: Box): Peano := box.value
        |}
        |""".stripMargin
    )
  }

  test("dependent projections on family arguments: WrapIdx.x") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Type
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |struct WrapIdx (A: Type) indices (n: Peano) : Type
        | | mk {n: Peano} (x: Vec(A, n)) : WrapIdx(A, n)
        |
        |def get (A: Type)(n: Peano)(w: WrapIdx(A, n)): Vec(A, w.n) := w.x
        |
        |{
        |  let v : Vec(Peano, Peano.zero) := Vec.nil(Peano)
        |  let w : WrapIdx(Peano, Peano.zero) := WrapIdx.mk(v)
        |  get(Peano, Peano.zero, w)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), SConst("Vec.nil"))
  }

  test("typecheck: dependent projection works in types with family arguments") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Type
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |struct WrapIdx (A: Type) indices (n: Peano) : Type
        | | mk {n: Peano} (x: Vec(A, n)) : WrapIdx(A, n)
        |
        |def useGet (A: Type)(n: Peano)(w: WrapIdx(A, n)): Vec(A, w.n) := w.x
        |""".stripMargin

    typecheckDecls(p)
  }

  test("typecheck: dependent projection works with implicit parameters") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Type
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |struct WrapIdx (A: Type) indices (n: Peano): Type
        | | mk {n: Peano} (x: Vec(A, n)) : WrapIdx(A, n)
        |
        |def useGet {A: Type}{n: Peano} (w: WrapIdx(A, n)): Vec(A, w.n) := w.x
        |""".stripMargin

    typecheckDecls(p)
  }

  test("typecheck: later field projection can depend on earlier field projection") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Type
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |struct DepPair (A: Type) : Type
        | | mk (n: Peano)(v: Vec(A, n)) : DepPair(A)
        |
        |def getV (p: DepPair(Peano)): Vec(Peano, p.n) := p.v
        |""".stripMargin

    typecheckDecls(p)
  }

  test("typecheck: later field projection can instantiate a family field with an earlier projection") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |struct Sigma (A: Type)(B: A -> Type) : Type
        | | mk (fst: A)(snd: B(fst)) : Sigma(A, B)
        |
        |def getSnd (A: Type)(B: A -> Type)(p: Sigma(A, B)): B(p.fst) := p.snd
        |""".stripMargin

    typecheckDecls(p)
  }

  test("typecheck: projection can quote a function-typed field") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |struct HasFn : Type
        | | mk (f: Peano -> Peano) : HasFn
        |
        |def getFn (h: HasFn): Peano -> Peano := h.f
        |""".stripMargin

    typecheckDecls(p)
  }

  test("typecheck: projection can quote a dependent function-typed field") {
    val p =
      """
        |struct HasDepFn (A: Type)(B: A -> Type) : Type
        | | mk (f: (x: A) -> B(x)) : HasDepFn(A, B)
        |
        |def getDepFn (A: Type)(B: A -> Type)(h: HasDepFn(A, B)): (x: A) -> B(x) := h.f
        |""".stripMargin

    typecheckDecls(p)
  }

  test("regression: a function-valued projection from a neutral base can be applied") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |struct FnBox : Type
        | | mk (f: (n: Peano) -> Peano) : FnBox
        |
        |opaque def box : FnBox := FnBox.mk(fun (n: Peano): Peano => n)
        |def use : Peano := box.f(Peano.zero)
        |
        |{ use }
        |""".stripMargin

    val result = runProgram(p)
    assert(Value.Blocker.unapply(result).isEmpty, s"Expected an unblocked stuck value, got $result")

    // Residuals are pure syntax, so the nested stuck projection has to survive re-evaluation of
    // the syntax the checker produced for it.
    val env = evalDecls(p)
    val core = LanguageParser.parseProgram(p) match {
      case Success(value, _, _) => Elaborator.elab(value, Prelude.test)
      case err: Failure         => fail(s"Failed to parse: $err")
    }
    val body = core.body.getOrElse(fail("Program has no body"))
    val residual = TypeChecker.checkTerm(body, env).residual
    assert(
      ValueEquivalence.defEq(Interpreter.evalTerm(residual, env), result),
      "re-evaluated residual must be defEq to the original stuck application"
    )
  }

  test("typecheck: projection checks a constructor value with an erased family argument in a field type") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |inductive Box (A: Type) : Type
        | | mk : Box(A)
        |
        |inductive Foo (b: Box(Peano)) : Type
        | | intro : Foo(b)
        |
        |struct S : Type
        | | mk (x: Foo(Box.mk(Peano))) : S
        |
        |def get (s: S): Foo(Box.mk(Peano)) := s.x
        |""".stripMargin

    typecheckDecls(p)
  }

  test("typecheck: projection can quote non-family implicit constructor argument from stored field") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |inductive Pack : Sort { level = succ(one) }
        | | mk {A: Type} (x: A) : Pack
        |
        |inductive Wrap (p: Pack) : Type
        | | intro : Wrap(p)
        |
        |struct S : Type
        | | mk (x: Wrap(Pack.mk(Peano.zero))) : S
        |
        |def get (s: S): Wrap(Pack.mk(Peano.zero)) := s.x
        |""".stripMargin

    typecheckDecls(p)
  }

  test("regression: projection from opaque struct-valued def stays neutral") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |struct Couple (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Couple(A, B)
        |
        |// Opaque on purpose
        |opaque def mkCouple (a: Peano)(b: Peano): Couple(Peano, Peano) := Couple.mk(a, b)
        |
        |def firstOpaque (a: Peano)(b: Peano): Peano := {
        |  let p := mkCouple(a, b)
        |  p.fst
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("regression: projection in type position from opaque struct constant stays neutral") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |struct CoupleU {u1: Level}{u2: Level}(A: Sort { level = u1 })(B: Sort { level = u2 }) : Sort { level = max(u1, u2) }
        | | mk (fst: A)(snd: B) : CoupleU(A, B)
        |
        |// Opaque on purpose
        |opaque def F : CoupleU(Type, Type) := CoupleU.mk(Peano, Peano)
        |
        |def idF (x: F.fst): F.fst := x
        |""".stripMargin

    typecheckDecls(p)
  }

  test("stuck projection in a constructor field type is transparent to positivity") {
    // Before struct expansion (StructEta) this was rejected conservatively: F.fst was a blocked
    // selector match, opaque to the positivity walker. An opaque struct global now publishes in
    // constructor form, so F.fst is a structured stuck projection the walker can traverse.
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |struct CoupleU {u1: Level}{u2: Level}(A: Sort { level = u1 })(B: Sort { level = u2 }) : Sort { level = max(u1, u2) }
        | | mk (fst: A)(snd: B) : CoupleU(A, B)
        |
        |// Opaque on purpose
        |opaque def F : CoupleU(Type, Type) := CoupleU.mk(Peano, Peano)
        |
        |struct UsesF : Type
        | | mk (x: F.fst) : UsesF
        |
        |def getX (u: UsesF): F.fst := u.x
        |""".stripMargin

    typecheckDecls(p)
  }

  test("regression: projection from stuck match returning a struct stays neutral") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |struct Couple (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Couple(A, B)
        |
        |// Opaque on purpose
        |opaque def step (n: Peano): Peano := n
        |
        |def choose (n: Peano): Couple(Peano, Peano) := {
        |  match step(n) returning Couple(Peano, Peano) with
        |  | Peano.zero => Couple.mk(Peano.zero, Peano.zero)
        |  | Peano.succ k => Couple.mk(Peano.succ(k), k)
        |}
        |
        |def fstChoose (n: Peano): Peano := {
        |  let p := choose(n)
        |  p.fst
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("typecheck: struct output determined by erased family witnesses supports explicit specialized projection") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |struct ChooseLeft (A: Type)(B: Type) indices (Out: Type) : Type
        | | mk (x: A) : ChooseLeft(A, B, A)
        |
        |def getExplicit (A: Type)(B: Type)(w: ChooseLeft(A, B, A)): A := w.x
        |""".stripMargin

    typecheckDecls(p)
  }

  test("negative: projection does not refine unrelated implicit struct output parameters") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |struct ChooseLeft (A: Type)(B: Type) indices (Out: Type) : Type
        | | mk (x: A) : ChooseLeft(A, B, A)
        |
        |def getCaptured {A: Type}{B: Type}{Out: Type} (w: ChooseLeft(A, B, Out)): Out := w.x
        |
        |{
        |  let w : ChooseLeft(Peano, Peano, Peano) := ChooseLeft.mk(Peano, Peano, Peano.zero)
        |  getCaptured(w)
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[TypeMismatch] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("typecheck: struct indices may depend on constructor fields") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Type
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |struct IndexedWrap (A: Type) indices (n: Peano) : Type
        | | mk (k: Peano)(x: Vec(A, k)) : IndexedWrap(A, k)
        |""".stripMargin

    typecheckDecls(p)
  }

  test("typecheck: selector field types respect nested Pi binder scope") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Type
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |struct IndexedFn (A: Type) indices (n: Peano) : Type
        | | mk (f: (m: Peano) -> Vec(A, m))(m: Peano) : IndexedFn(A, m)
        |
        |def project {n: Peano} (w: IndexedFn(Peano, n))(m: Peano): Vec(Peano, m) := w.f(m)
        |""".stripMargin

    typecheckDecls(p)
  }

  test("typecheck: a nested Pi binder may shadow an earlier field name") {
    typecheckDecls(
      """
        |struct Shadow (A: Type) : Type
        | | mk (x: A)(f: (x: A) -> A) : Shadow(A)
        |
        |def getF {A: Type} (s: Shadow(A)): (x: A) -> A := s.f
        |""".stripMargin
    )
  }

  test("negative: projection does not infer unrelated hidden binders from family arguments") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Type
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |struct Hidden : Type
        | | mk {m: Peano} (x: Vec(Peano, m)) : Hidden
        |
        |def bad (w: Hidden): Vec(Peano, Peano.zero) := w.x
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[TypeMismatch] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("typecheck: hidden constructor fields are projected and can determine visible field types") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Type
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |struct HiddenVec (A: Type) : Type
        | | mk {n: Peano} (v: Vec(A, n)) : HiddenVec(A)
        |
        |def sameLenLeft {n: Peano} (v1: Vec(Peano, n))(v2: Vec(Peano, n)): Peano := n
        |
        |def hiddenLen (h: HiddenVec(Peano)): Peano := h.n
        |
        |def lenTwice (h: HiddenVec(Peano)): Peano := sameLenLeft(h.v, h.v)
        |""".stripMargin

    typecheckDecls(p)
  }

  test("plain inductives do not receive generated named selectors") {
    val p =
      """
        |inductive And (P: Prop)(Q: Prop) : Prop
        | | intro (p: P)(q: Q) : And(P, Q)
        |
        |def bad (P: Prop)(Q: Prop)(h: And(P, Q)): P := h.fst
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[NotFound] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("multi-constructor inductives do not receive generated named selectors") {
    val p =
      """
        |inductive Or (A: Type)(B: Type) : Type
        | | inl (a: A) : Or(A, B)
        | | inr (b: B) : Or(A, B)
        |
        |def bad (A: Type)(B: Type)(h: Or(A, B)): A := h.fst
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[NotFound] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("negative: unknown field name on struct throws NotFound") {
    val p =
      """
        |struct Couple (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Couple(A, B)
        |
        |def bad (A: Type)(B: Type)(p: Couple(A, B)): A := p.foo
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        interceptError[NotFound] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("invalid: struct with multiple constructors is rejected") {
    val p =
      """
        |struct Bad (A: Type) : Type
        | | mk1 (a: A) : Bad(A)
        | | mk2 (a: A) : Bad(A)
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) => fail("Struct parsed successfully with multiple constructors")
      case _: Failure           =>
    }
  }

  test("Prop structs may project Prop-valued fields") {
    val p =
      """
        |struct And (P: Prop)(Q: Prop) : Prop
        | | intro (left: P)(right: Q) : And(P, Q)
        |
        |def andLeft (P: Prop)(Q: Prop)(h: And(P, Q)): P := h.left
        |def andRight (P: Prop)(Q: Prop)(h: And(P, Q)): Q := h.right
        |""".stripMargin

    typecheckDecls(p)
  }

  test("a generic struct projection remains valid when its instance specializes to Prop") {
    val p =
      """
        |inductive True : Prop
        | | intro : True
        |
        |struct PolyBox {u: Level}(A: Sort { level = u }) : Sort { level = u }
        | | mk (value: A) : PolyBox(A)
        |
        |def get {u: Level}{A: Sort { level = u }} (box: PolyBox(A)): A := box.value
        |
        |opaque def boxedTrue : PolyBox(True) := PolyBox.mk(True.intro)
        |def gotTrue : True := get(boxedTrue)
        |""".stripMargin

    typecheckDecls(p)
  }

  test("Prop projection permits an unused preceding data field") {
    // Prop-into-Prop is small elimination: the match needs no recovery at all.
    typecheckDecls(
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |inductive True : Prop
        | | intro : True
        |
        |inductive HasProof : Prop
        | | intro (data: Peano)(proof: True) : HasProof
        |
        |opaque def h : HasProof := HasProof.intro(Peano.zero, True.intro)
        |def theProof : True := {
        |  match h returning True with
        |  | HasProof.intro data proof => proof
        |}
        |""".stripMargin
    )
  }

  test("Prop projection into data is rejected when a preceding data field is not recoverable") {
    val err = expectAnyTypeError(
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |inductive DepProof : Prop
        | | intro (data: Peano)(proof: Eq(Peano, data, data)) : DepProof
        |
        |def theData (h: DepProof): Peano := {
        |  match h returning Peano with
        |  | DepProof.intro data proof => data
        |}
        |""".stripMargin
    )
    assert(err.isInstanceOf[PropEliminationRestricted], s"expected PropEliminationRestricted, got $err")
  }

  test("Prop recovery uses syntactic telescope dependencies") {
    val err = expectAnyTypeError(
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |inductive True : Prop
        | | intro : True
        |
        |def Ignore (_: Peano): Prop := True
        |
        |inductive DepProof : Prop
        | | intro (data: Peano)(proof: Ignore(data)) : DepProof
        |
        |def theData (h: DepProof): Peano := {
        |  match h returning Peano with
        |  | DepProof.intro data proof => data
        |}
        |""".stripMargin
    )
    assert(err.isInstanceOf[PropEliminationRestricted], s"expected PropEliminationRestricted, got $err")
  }

  test("Prop elimination recovers fields forced by an index") {
    val result = runProgram(
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |inductive True : Prop
        | | intro : True
        |
        |inductive IndexedProof indices (n: Peano) : Prop
        | | intro (data: Peano)(proof: True) : IndexedProof(data)
        |
        |opaque def h : IndexedProof(Peano.zero) := IndexedProof.intro(Peano.zero, True.intro)
        |def theData : Peano := {
        |  match h returning Peano with
        |  | IndexedProof.intro data proof => data
        |}
        |
        |{ theData }
        |""".stripMargin
    )
    assertEquals(PrettyPrinter.print(result), "Peano.zero")
  }

  test("a Prop struct may generate a selector for an index-forced data field") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |struct IndexedProp indices (n: Peano) : Prop
        | | intro (value: Peano) : IndexedProp(value)
        |
        |opaque def h : IndexedProp(Peano.zero) := IndexedProp.intro(Peano.zero)
        |def recovered : Peano := h.value
        |""".stripMargin

    typecheckDecls(p)
  }

  test("Prop field recovery does not assert the constructor result equation") {
    // Recovery reads the first index only: it must NOT assume `a = b` from the result equation.
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (pred: Peano) : Peano
        |
        |inductive Eq2 indices (left: Peano)(right: Peano) : Prop
        | | refl (value: Peano) : Eq2(value, value)
        |
        |opaque def a : Peano := Peano.zero
        |opaque def b : Peano := Peano.zero
        |def AB : Prop := Eq2(a, b)
        |""".stripMargin

    val env = evalDecls(p)
    val eqTpe = env("AB")
    // Field recovery reads the index that forces the field (`value := a`) and stops there; it never
    // asserts the constructor's own result equation, which here would claim `a = b`. So the fields
    // are recoverable, while reconstructing the whole `Eq2.refl a : Eq2(a, a)` layer is refused.
    assert(ProofReconstruction.canRecoverAll(eqTpe), "Eq2(a, b)'s single field is forced by its first index")
    assert(ProofReconstruction.reconstruct(eqTpe).isEmpty, "Eq2(a, b) must not reconstruct a refl")
  }

  test("Prop elimination into data is rejected for a result-only dependency") {
    val err = expectAnyTypeError(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (pred: Peano) : Peano
        |
        |inductive True : Prop
        | | intro : True
        |
        |inductive NestedProof indices (n: Peano) : Prop
        | | intro (data: Peano)(proof: True) : NestedProof(Peano.succ(data))
        |
        |def theData (h: NestedProof(Peano.succ(Peano.zero))): Peano := {
        |  match h returning Peano with
        |  | NestedProof.intro data proof => data
        |}
        |""".stripMargin
    )
    assert(err.isInstanceOf[PropEliminationRestricted], s"expected PropEliminationRestricted, got $err")
  }

  test("a selector is generated only for a one-constructor family, and unknown fields are rejected") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |inductive Box : Type
        | | mk (value: Peano) : Box
        |
        |inductive Choice : Type
        | | left (value: Peano) : Choice
        | | right (value: Peano) : Choice
        |
        |opaque def box : Box := Box.mk(Peano.zero)
        |opaque def choice : Choice := Choice.left(Peano.zero)
        |""".stripMargin

    val env = evalDecls(p)
    val span = Span(0, 0)
    // A plain inductive gets no generated selectors at all, so any field name is NotFound.
    interceptError[NotFound] {
      TypeChecker.checkTerm(CoreAst.Term.Select(CoreAst.Term.GlobalRef("box", span), "value", span), env)
    }
    interceptError[NotFound] {
      TypeChecker.checkTerm(CoreAst.Term.Select(CoreAst.Term.GlobalRef("choice", span), "value", span), env)
    }
  }

  test("a Prop struct with a named data field is rejected while its selector is checked") {
    val p =
      """
        |struct Nonempty (A: Type) : Prop
        | | intro (val: A) : Nonempty(A)
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        // The generated selector is a large elimination out of a Prop whose data field is not
        // recoverable from the proposition, which is exactly what the Prop-elimination gate refuses.
        interceptError[PropEliminationRestricted] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("struct with anonymous field is accepted without a named selector") {
    val p =
      """
        |struct Bad (A: Type) : Type
        | | mk (_: A) : Bad(A)
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        Interpreter.run(core, Prelude.test)
        assert(!core.decls.exists {
          case CoreAst.Decl.ConstDecl(_, "Bad._", _, _, _, _) => true
          case _                                              => false
        })
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

}
