package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class ProjectionTests extends munit.FunSuite {

  private def typecheckDecls(src: String): Unit = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        try {
          Interpreter.run(core, Prelude.test)
        } catch {
          case t: TypeError =>
            val source = Source(src)
            fail(ErrorReporter.pretty(t, source))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  private def runProgram(src: String): Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        try {
          Interpreter.run(core, Prelude.test).getOrElse(fail("Program has no body"))
        } catch {
          case t: TypeError =>
            val source = Source(src)
            fail(ErrorReporter.pretty(t, source))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
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
  private def succS(s: Shape) = SApp(SConst("Peano.succ"), List(s))

  test("non-dependent projections: Pair.fst and Pair.snd") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |struct Pair (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Pair(A, B)
        |
        |def first {A1: Type}{B1: Type} (p: Pair(A1, B1)): A1 := p.fst
        |def second {A2: Type}{B2: Type} (p: Pair(A2, B2)): B2 := p.snd
        |
        |{
        |  let p : Pair(Peano, Peano) := Pair.mk(Peano.zero, Peano.succ(Peano.zero))
        |  first(p)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("struct syntax emits eager aliases backed by positional projections") {
    val p =
      """
        |struct Pair (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Pair(A, B)
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        val found = core.decls.exists {
          case CoreAst.Decl.ConstDecl(
                false,
                "Pair.snd",
                _,
                CoreAst.ConstBody.TermBody(
                  CoreAst.Term.Lam(
                    _,
                    CoreAst.Term.Proj("Pair", 1, _: CoreAst.Term.LocalRef, _),
                    _,
                    _,
                    _
                  )
                ),
                _,
                false,
                Some(CoreAst.ProjectionAlias("Pair", 1))
              ) =>
            true
          case _ => false
        }
        assert(found, "expected Pair.snd to be an eager alias of positional projection Pair[1]")
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
        |axiom box : FnBox
        |def use : Peano := box.f(Peano.zero)
        |
        |{ use }
        |""".stripMargin

    val result = runProgram(p)
    result match {
      case Value.VApp(
            Value.VApp(
              Value.VConst(_, Value.StructField("FnBox", 0, _), _),
              Vector(Value.VConst("box", _, _)),
              _,
              None
            ),
            Vector(_),
            _,
            None
          ) =>
      case other => fail(s"Expected a nested application of the stuck projection, got $other")
    }

    ValueQuote.quoteTerm(result, ValueQuote.quoteContext(Env.empty), Span(0, 0)) match {
      case ElabAst.Term.App(
            ElabAst.Term.Proj("FnBox", 0, ElabAst.Term.GlobalRef("box", _), _),
            Vector(_),
            _
          ) =>
      case other => fail(s"Expected the nested application to quote through Proj, got $other")
    }
  }

  test("typecheck: projection can quote constructor value with erased family argument in field type") {
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
        |inductive Pack : Sort(Level.succ(Level.one))
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
        |struct Pair (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Pair(A, B)
        |
        |// Opaque on purpose
        |opaque def mkPair (a: Peano)(b: Peano): Pair(Peano, Peano) := Pair.mk(a, b)
        |
        |def firstOpaque (a: Peano)(b: Peano): Peano := {
        |  let p := mkPair(a, b)
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
        |struct PairU {u1: Level}{u2: Level}(A: Sort(u1))(B: Sort(u2)) : Sort(Level.max(u1, u2))
        | | mk (fst: A)(snd: B) : PairU(A, B)
        |
        |// Opaque on purpose
        |opaque def F : PairU(Type, Type) := PairU.mk(Peano, Peano)
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
        |struct PairU {u1: Level}{u2: Level}(A: Sort(u1))(B: Sort(u2)) : Sort(Level.max(u1, u2))
        | | mk (fst: A)(snd: B) : PairU(A, B)
        |
        |// Opaque on purpose
        |opaque def F : PairU(Type, Type) := PairU.mk(Peano, Peano)
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
        |struct Pair (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Pair(A, B)
        |
        |// Opaque on purpose
        |opaque def step (n: Peano): Peano := n
        |
        |def choose (n: Peano): Pair(Peano, Peano) := {
        |  match step(n) returning Pair(Peano, Peano) with
        |  | Peano.zero => Pair.mk(Peano.zero, Peano.zero)
        |  | Peano.succ k => Pair.mk(Peano.succ(k), k)
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
        intercept[TypeMismatch] { Interpreter.run(core, Prelude.test) }
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
        intercept[TypeMismatch] { Interpreter.run(core, Prelude.test) }
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
        intercept[NotFound] { Interpreter.run(core, Prelude.test) }
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
        intercept[NotFound] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("negative: unknown field name on struct throws NotFound") {
    val p =
      """
        |struct Pair (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Pair(A, B)
        |
        |def bad (A: Type)(B: Type)(p: Pair(A, B)): A := p.foo
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[NotFound] { Interpreter.run(core, Prelude.test) }
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
      case err: Failure         =>
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

  test("primitive Prop projection permits an unused preceding data field") {
    val p =
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
        |axiom h : HasProof
        |""".stripMargin

    val span = Span(0, 0)
    val checked = TypeChecker.checkTerm(
      CoreAst.Term.Proj("HasProof", 1, CoreAst.Term.GlobalRef("h", span), span),
      evalDecls(p)
    )
    assert(Value.isPropositionType(checked.value.tpe))
    assert(checked.residual.isInstanceOf[ElabAst.Term.Proj])
  }

  test("primitive Prop projection rejects a preceding data field used by the selected field type") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |inductive DepProof : Prop
        | | intro (data: Peano)(proof: Eq(Peano, data, data)) : DepProof
        |
        |axiom h : DepProof
        |""".stripMargin

    val span = Span(0, 0)
    intercept[InvalidProjection] {
      TypeChecker.checkTerm(
        CoreAst.Term.Proj("DepProof", 1, CoreAst.Term.GlobalRef("h", span), span),
        evalDecls(p)
      )
    }
  }

  test("primitive Prop projection uses syntactic telescope dependencies") {
    val p =
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
        |axiom h : DepProof
        |""".stripMargin

    val span = Span(0, 0)
    intercept[InvalidProjection] {
      TypeChecker.checkTerm(
        CoreAst.Term.Proj("DepProof", 1, CoreAst.Term.GlobalRef("h", span), span),
        evalDecls(p)
      )
    }
  }

  test("primitive Prop projection counts dependencies in the constructor result") {
    val p =
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
        |axiom h : IndexedProof(Peano.zero)
        |""".stripMargin

    val span = Span(0, 0)
    intercept[InvalidProjection] {
      TypeChecker.checkTerm(
        CoreAst.Term.Proj("IndexedProof", 1, CoreAst.Term.GlobalRef("h", span), span),
        evalDecls(p)
      )
    }
  }

  test("primitive projection validates the family shape and field index") {
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
        |axiom box : Box
        |axiom choice : Choice
        |""".stripMargin

    val env = evalDecls(p)
    val span = Span(0, 0)
    val box = CoreAst.Term.GlobalRef("box", span)
    val choice = CoreAst.Term.GlobalRef("choice", span)

    intercept[InvalidProjection] {
      TypeChecker.checkTerm(CoreAst.Term.Proj("Box", 1, box, span), env)
    }
    intercept[InvalidProjection] {
      TypeChecker.checkTerm(CoreAst.Term.Proj("Peano", 0, box, span), env)
    }
    intercept[InvalidProjection] {
      TypeChecker.checkTerm(CoreAst.Term.Proj("Choice", 0, choice, span), env)
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
        intercept[InvalidProjection] { Interpreter.run(core, Prelude.test) }
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
          case CoreAst.Decl.ConstDecl(_, "Bad._", _, _, _, _, _) => true
          case _                                                 => false
        })
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

}
