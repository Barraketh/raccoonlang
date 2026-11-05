package com.raccoonlang

import com.raccoonlang.ProgramFixtures.Programs

/**
 * Stuck matches (docs/kernel.md, "Stuck matches"): a stuck match is identified by its checked code, up to names,
 * positions and the slots of its locals, and by the values of its free locals, so the same match written apart
 * converts, and two recursive functions convert as fixpoints, by their bodies with their recursive slots paired.
 */
class StuckMatchIdentityTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = true)
  import programs._

  private val isZ =
    """
      |def isZ (n: Nat): Bool := {
      |  match n returning Bool with
      |  | Nat.zero => Bool.true
      |  | Nat.succ m => Bool.false
      |}
      |def isZ2 (k: Nat): Bool := {
      |  match k returning Bool with
      |  | Nat.zero => Bool.true
      |  | Nat.succ j => Bool.false
      |}
      |""".stripMargin

  private val sel =
    """
      |def sel (n: Nat)(a: Nat)(b: Nat): Nat := {
      |  match n returning Nat with
      |  | Nat.zero => a
      |  | Nat.succ m => b
      |}
      |""".stripMargin

  private def accepted(src: String)(implicit loc: munit.Location): Unit = run(src)

  private def mismatched(src: String)(implicit loc: munit.Location): Unit = intercept[TypeMismatch](runChecked(src))

  test("the same match written in two definitions converts") {
    accepted(isZ + "def p (n: Nat): Eq(Bool, isZ(n), isZ2(n)) := Eq.refl(isZ(n))\n")
    accepted(isZ + "def p : Eq((n: Nat) -> Bool, isZ, isZ2) := Eq.refl(isZ)\n")
  }

  test("the same match written inline twice, or inline and in a definition, converts") {
    accepted(
      """
        |def p (n: Nat): Bool := {
        |  let a : Bool := {
        |    match n returning Bool with
        |    | Nat.zero => Bool.true
        |    | Nat.succ m => Bool.false
        |  }
        |  let b : Bool := {
        |    match n returning Bool with
        |    | Nat.zero => Bool.true
        |    | Nat.succ m => Bool.false
        |  }
        |  let e : Eq(Bool, a, b) := Eq.refl(a)
        |  a
        |}
        |""".stripMargin
    )
    accepted(
      isZ +
        """
          |def q (n: Nat): Bool := {
          |  let v : Bool := {
          |    match n returning Bool with
          |    | Nat.zero => Bool.true
          |    | Nat.succ m => Bool.false
          |  }
          |  let e : Eq(Bool, v, isZ(n)) := Eq.refl(v)
          |  v
          |}
          |""".stripMargin
    )
  }

  test("a definition converts with a lambda in a type that writes its match, and two such lambdas convert") {
    val lambda =
      """fun (k: Nat): Bool => match k returning Bool with
        |  | Nat.zero => Bool.true
        |  | Nat.succ m => Bool.false
        |""".stripMargin
    accepted(isZ + s"def p : Eq((k: Nat) -> Bool, isZ, $lambda) := Eq.refl(isZ)\n")
    accepted(isZ + s"def p (h: Eq((k: Nat) -> Bool, isZ, $lambda)): Eq((k: Nat) -> Bool, isZ, $lambda) := h\n")
  }

  test("a match on propositions and the prelude's own matches convert like any other") {
    accepted(
      """
        |def P (n: Nat): Prop := {
        |  match n returning Prop with
        |  | Nat.zero => True
        |  | Nat.succ m => False
        |}
        |def P2 (n: Nat): Prop := {
        |  match n returning Prop with
        |  | Nat.zero => True
        |  | Nat.succ m => False
        |}
        |def t (n: Nat)(h: P(n)): P2(n) := h
        |""".stripMargin
    )
    accepted(
      """
        |def myNot (b: Bool): Bool := {
        |  match b returning Bool with
        |  | Bool.true => Bool.false
        |  | Bool.false => Bool.true
        |}
        |def p (b: Bool): Eq(Bool, Bool.not(b), myNot(b)) := Eq.refl(myNot(b))
        |""".stripMargin
    )
  }

  test("captures convert by value, in the order the code first mentions them") {
    accepted(
      sel +
        """
          |def sel2 (n: Nat)(a: Nat)(b: Nat): Nat := {
          |  match n returning Nat with
          |  | Nat.zero => a
          |  | Nat.succ m => b
          |}
          |def p (n: Nat)(a: Nat)(b: Nat): Eq(Nat, sel(n, a, b), sel2(n, a, b)) := Eq.refl(sel(n, a, b))
          |def q (n: Nat)(a: Nat)(b: Nat): Eq(Nat, sel(n, Nat.add(a, 0), b), sel2(n, a, Nat.add(0, b))) :=
          |  Eq.refl(sel(n, a, b))
          |""".stripMargin
    )
    // The same code over parameters declared in the other order reads its captures in the code's order: `sel2(n, x, y)`
    // is `sel(n, y, x)`.
    val swapped =
      sel +
        """
          |def sel2 (n: Nat)(b: Nat)(a: Nat): Nat := {
          |  match n returning Nat with
          |  | Nat.zero => a
          |  | Nat.succ m => b
          |}
          |""".stripMargin
    accepted(
      swapped + "def p (n: Nat)(x: Nat)(y: Nat): Eq(Nat, sel(n, y, x), sel2(n, x, y)) := Eq.refl(sel(n, y, x))\n"
    )
    mismatched(
      swapped + "def p (n: Nat)(x: Nat)(y: Nat): Eq(Nat, sel(n, x, y), sel2(n, x, y)) := Eq.refl(sel(n, x, y))\n"
    )
  }

  test("stuck matches captured by stuck matches convert, before and after refinement resumes them") {
    val selB =
      """
        |def selB (n: Nat)(a: Bool)(b: Bool): Bool := {
        |  match n returning Bool with
        |  | Nat.zero => a
        |  | Nat.succ m => b
        |}
        |""".stripMargin
    accepted(
      isZ + selB +
        """
          |def p (n: Nat)(k: Nat): Eq(Bool, selB(n, isZ(k), Bool.true), selB(n, isZ2(k), Bool.true)) :=
          |  Eq.refl(selB(n, isZ(k), Bool.true))
          |def q (n: Nat)(k: Nat): Eq(Bool, selB(n, isZ(k), Bool.true), selB(n, isZ2(k), Bool.true)) := {
          |  match n returning Eq(Bool, selB(n, isZ(k), Bool.true), selB(n, isZ2(k), Bool.true)) with
          |  | Nat.zero => Eq.refl(isZ(k))
          |  | Nat.succ m => Eq.refl(Bool.true)
          |}
          |""".stripMargin
    )
    accepted(
      """
        |def h (n: Nat): Nat := n
        |def f (n: Nat): Nat := {
        |  match n returning Nat with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ m => h(m)
        |}
        |def g (n: Nat): Nat := {
        |  match n returning Nat with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ m => h(m)
        |}
        |def p (n: Nat): Eq(Nat, f(n), g(n)) := Eq.refl(f(n))
        |""".stripMargin
    )
  }

  test("matches that differ in their code, their scrutinee or their captures do not convert") {
    // Different branches.
    mismatched(
      """
        |def a (n: Nat): Bool := {
        |  match n returning Bool with
        |  | Nat.zero => Bool.true
        |  | Nat.succ m => Bool.false
        |}
        |def b (n: Nat): Bool := {
        |  match n returning Bool with
        |  | Nat.zero => Bool.false
        |  | Nat.succ m => Bool.true
        |}
        |def p (n: Nat): Eq(Bool, a(n), b(n)) := Eq.refl(a(n))
        |""".stripMargin
    )
    // A field where the other reads a capture.
    mismatched(
      """
        |def a (n: Nat)(k: Nat): Nat := {
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ m => m
        |}
        |def b (n: Nat)(k: Nat): Nat := {
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ m => k
        |}
        |def p (n: Nat)(k: Nat): Eq(Nat, a(n, k), b(n, k)) := Eq.refl(a(n, k))
        |""".stripMargin
    )
    // Different motives, though their values convert: the motive is code.
    mismatched(
      """
        |def a (n: Nat): Nat := {
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ m => m
        |}
        |def b (n: Nat): Nat := {
        |  match n returning (fun (k: Nat): Type => Nat)(n) with
        |  | Nat.zero => 0
        |  | Nat.succ m => m
        |}
        |def p (n: Nat): Eq(Nat, a(n), b(n)) := Eq.refl(a(n))
        |""".stripMargin
    )
    // Different scrutinees, and different captures.
    mismatched(isZ + "def p (n: Nat)(k: Nat): Eq(Bool, isZ(n), isZ2(k)) := Eq.refl(isZ(n))\n")
    mismatched(sel + "def p (n: Nat)(a: Nat)(b: Nat): Eq(Nat, sel(n, a, b), sel(n, b, a)) := Eq.refl(sel(n, a, b))\n")
  }

  // A completeness limit: a written case that binds a field it does not use binds a slot that a wildcard's anonymous
  // field does not, so the two are different code, while two wildcards are the same.
  test("a wildcard's case is the same code as a case binding its fields anonymously") {
    val wildcards =
      """
        |def isZw (n: Nat): Bool := {
        |  match n returning Bool with
        |  | Nat.zero => Bool.true
        |  | _ => Bool.false
        |}
        |def isZw2 (n: Nat): Bool := {
        |  match n returning Bool with
        |  | Nat.zero => Bool.true
        |  | Nat.succ _ => Bool.false
        |}
        |""".stripMargin
    accepted(wildcards + "def p (n: Nat): Eq(Bool, isZw(n), isZw2(n)) := Eq.refl(isZw(n))\n")
    mismatched(isZ + wildcards + "def p (n: Nat): Eq(Bool, isZ(n), isZw(n)) := Eq.refl(isZ(n))\n")
  }

  test("identical recursive definitions convert as fixpoints, and different ones do not, both terminating") {
    val fg =
      """
        |def f (n: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ m => f(m)
        |}
        |def g (n: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ m => g(m)
        |}
        |def d (n: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => Nat.succ(Nat.zero)
        |  | Nat.succ m => d(m)
        |}
        |""".stripMargin
    accepted(fg + "def p (n: Nat): Eq(Nat, f(n), g(n)) := Eq.refl(f(n))\n")
    accepted(fg + "def p : Eq((n: Nat) -> Nat, f, g) := Eq.refl(f)\n")
    mismatched(fg + "def p (n: Nat): Eq(Nat, f(n), d(n)) := Eq.refl(f(n))\n")
    // A function that is not recursive opens as before: a wrapper of `f` is `f`.
    accepted(fg + "def h (n: Nat): Nat := f(n)\ndef p : Eq((n: Nat) -> Nat, f, h) := Eq.refl(f)\n")
    // Recursive functions passed to each other: every pair compared is paired.
    accepted(
      """
        |def f (k: Nat -> Nat)(n: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => k(Nat.zero)
        |  | Nat.succ m => f(k, m)
        |}
        |def g (k: Nat -> Nat)(n: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => k(Nat.zero)
        |  | Nat.succ m => g(k, m)
        |}
        |def p (n: Nat): Eq(Nat, f(fun (x: Nat): Nat => f(fun (y: Nat): Nat => y, x), n),
        |  g(fun (x: Nat): Nat => g(fun (y: Nat): Nat => y, x), n)) :=
        |  Eq.refl(f(fun (x: Nat): Nat => f(fun (y: Nat): Nat => y, x), n))
        |""".stripMargin
    )
  }

  test("members of mutual blocks convert when the blocks' bodies do, member for member") {
    def block(suffix: String, oddZero: String) =
      s"""
         |mutual {
         |  def ev$suffix (n: Nat) : Bool decreases structural(n) := {
         |    match n returning Bool with
         |    | Nat.zero => Bool.true
         |    | Nat.succ m => od$suffix(m)
         |  }
         |  def od$suffix (n: Nat) : Bool decreases structural(n) := {
         |    match n returning Bool with
         |    | Nat.zero => $oddZero
         |    | Nat.succ m => ev$suffix(m)
         |  }
         |}
         |""".stripMargin
    val blocks = block("A", "Bool.false") + block("B", "Bool.false") + block("C", "Bool.true") +
      """
        |def selfE (n: Nat) : Bool decreases structural(n) := {
        |  match n returning Bool with
        |  | Nat.zero => Bool.true
        |  | Nat.succ m => selfE(m)
        |}
        |""".stripMargin
    accepted(blocks + "def p (n: Nat): Eq(Bool, evA(n), evB(n)) := Eq.refl(evA(n))\n")
    accepted(blocks + "def p (n: Nat): Eq(Bool, odA(n), odB(n)) := Eq.refl(odA(n))\n")
    accepted(blocks + "def p : Eq((n: Nat) -> Bool, evA, evB) := Eq.refl(evA)\n")
    // `evC` differs from `evA` only in its peer.
    mismatched(blocks + "def p (n: Nat): Eq(Bool, evA(n), evC(n)) := Eq.refl(evA(n))\n")
    // Another member, and a fixpoint of another shape.
    mismatched(blocks + "def p (n: Nat): Eq(Bool, evA(n), odB(n)) := Eq.refl(evA(n))\n")
    mismatched(blocks + "def p (n: Nat): Eq(Bool, evA(n), selfE(n)) := Eq.refl(evA(n))\n")
  }

  // Motive inference quotes the first branch's type and evaluates the quotation: the stuck matches it rebuilds are the
  // ones it quoted, whatever their captures hold.
  test("a match rebuilt by quotation converts with the one quoted") {
    def inferred(tpe: String) =
      s"""
         |def t (n: Nat)(k: Nat)(j: Nat)(h: $tpe): $tpe := {
         |  let r := match n with
         |    | Nat.zero => h
         |    | Nat.succ m => h
         |  r
         |}
         |""".stripMargin
    accepted(isZ + inferred("Eq(Bool, isZ(k), Bool.true)"))
    // A capture that is no local is quoted as a let, and two captures holding one local are told apart.
    accepted(isZ + inferred("Eq(Bool, isZ(Nat.mul(k, k)), Bool.true)"))
    accepted(sel + inferred("Eq(Nat, sel(j, k, k), k)"))
    accepted(
      isZ +
        """
          |inductive Box (b: Bool) : Type
          | | mk {b: Bool} : Box(b)
          |def t (n: Nat)(k: Nat)(x: Box(isZ(k))): Box(isZ(k)) := {
          |  let r := match n with
          |    | Nat.zero => x
          |    | Nat.succ m => x
          |  r
          |}
          |""".stripMargin
    )
  }

  test("what converted before still does") {
    accepted(isZ + "def p (n: Nat): Eq(Bool, isZ(n), isZ(n)) := Eq.refl(isZ(n))\n")
    accepted(
      isZ +
        """
          |def p (n: Nat): Eq(Bool, isZ(n), isZ(n)) := {
          |  let k : Nat := n
          |  let e : Eq(Bool, isZ(k), isZ(n)) := Eq.refl(isZ(n))
          |  e
          |}
          |def isZ3 (n: Nat): Bool := isZ(n)
          |def q (n: Nat): Eq(Bool, isZ3(n), isZ(n)) := Eq.refl(isZ(n))
          |def r : Eq(Bool, isZ(3), isZ2(3)) := Eq.refl(Bool.false)
          |def s (n: Nat): Eq(Bool, isZ(n), isZ2(n)) := {
          |  match n returning Eq(Bool, isZ(n), isZ2(n)) with
          |  | Nat.zero => Eq.refl(Bool.true)
          |  | Nat.succ m => Eq.refl(Bool.false)
          |}
          |def u (h: Eq((k: Nat) -> Bool, fun (k: Nat): Bool => isZ(k), isZ)): Eq((k: Nat) -> Bool, fun (j: Nat): Bool => isZ(j), isZ) := h
          |def v (n: Nat)(k: Nat)(h: Eq(Bool, isZ(k), Bool.true)): Eq(Bool, isZ(k), Bool.true) := {
          |  match n returning Eq(Bool, isZ(k), Bool.true) with
          |  | Nat.zero => h
          |  | Nat.succ m => h
          |}
          |""".stripMargin
    )
    accepted(
      """
        |def f (n: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ m => f(m)
        |}
        |def p (n: Nat): Eq(Nat, f(n), f(n)) := Eq.refl(f(n))
        |def a (n: Nat): Nat := Nat.add(n, 1)
        |def b (n: Nat): Nat := Nat.add(n, 1)
        |def q : Eq((n: Nat) -> Nat, a, b) := Eq.refl(a)
        |def r1 (n: Nat): Eq(Nat, n, n) := {
        |  match n returning Eq(Nat, n, n) with
        |  | Nat.zero => Eq.refl(Nat.zero)
        |  | Nat.succ m => Eq.refl(Nat.succ(m))
        |}
        |def r2 (n: Nat): Eq(Nat, n, n) := {
        |  match n returning Eq(Nat, n, n) with
        |  | Nat.zero => Eq.refl(Nat.zero)
        |  | Nat.succ m => Eq.refl(Nat.succ(m))
        |}
        |def Q (n: Nat)(h: Eq(Nat, n, n)): Prop := True
        |def t (n: Nat)(x: Q(n, r1(n))): Q(n, r2(n)) := x
        |""".stripMargin
    )
  }
}
