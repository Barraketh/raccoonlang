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
        |def get (A: Type)(n: Peano)(w: WrapIdx(A, n)): Vec(A, n) := w.x
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
        |def useGet (A: Type)(n: Peano)(w: WrapIdx(A, n)): Vec(A, n) := w.x
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
        |def useGet {A: Type}{n: Peano} (w: WrapIdx(A, n)): Vec(A, n) := w.x
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

  test("typecheck: selector family-field rewrites respect nested Pi binder scope") {
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

  test("negative: selecting from non-struct Prop family throws") {
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
        intercept[NotAStruct] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("negative: selecting from non-struct multi-ctor inductive throws") {
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
        intercept[NotAStruct] { Interpreter.run(core, Prelude.test) }
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

  test("negative: Prop struct projection into Type is restricted when the field is not forced") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |struct Nonempty (A: Type) : Prop
        | | intro (val: A) : Nonempty(A)
        |
        |def bad (h: Nonempty(Peano)): Peano := h.val
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[PropEliminationRestricted] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("invalid: struct with '_' anonymous field is rejected") {
    val p =
      """
        |struct Bad (A: Type) : Type
        | | mk (_: A) : Bad(A)
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[InvalidStruct] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

}
