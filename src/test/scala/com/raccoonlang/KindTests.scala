package com.raccoonlang

import com.raccoonlang.ProgramFixtures._
import com.raccoonlang.Value._

/**
 * Kinds (docs/kernel.md, "Kinds"): `Kind.copy`, `Kind.lin`, kind variables and `Kind.join`; universes `Univ(k, l)`,
 * with `Sort` and `Lin` as names for the constant kinds; `$k` captures; apartness of constant kinds; L1 over the kind
 * lattice; tracking of values of variable kind; and kind-polymorphic families, such as the kernel `List` and the
 * prelude's `Prod`, at copyable and linear instances.
 */
class KindTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = true)
  import programs._

  private val base = lnats

  test("Kind.join normalizes: copy vanishes, lin absorbs, and variables join as a set") {
    run(
      base +
        """
          |def copyUnit (k: Kind) : Eq(Kind, Kind.join(Kind.copy, k), k) := Eq.refl(k)
          |def linAbsorbs (k: Kind) : Eq(Kind, Kind.join(k, Kind.lin), Kind.lin) := Eq.refl(Kind.lin)
          |def idempotent (k: Kind) : Eq(Kind, Kind.join(k, k), k) := Eq.refl(k)
          |def commutes (a: Kind)(b: Kind) : Eq(Kind, Kind.join(a, b), Kind.join(b, a)) := Eq.refl(Kind.join(a, b))
          |""".stripMargin
    )
    val a = FreshVar.freshVar("a", KindTpe)
    val b = FreshVar.freshVar("b", KindTpe)
    val ka = Kind.mk(a.id)
    assertEquals(Kind.join(Kind.copy, ka), ka)
    assertEquals(Kind.join(ka, Kind.lin), Kind.lin)
    assertEquals(Kind.join(ka, Kind.mk(b.id)), Kind.join(Kind.mk(b.id), ka))
    assert(Kind.leq(Kind.copy, ka) && Kind.leq(ka, Kind.lin) && !Kind.leq(Kind.lin, ka) && !Kind.leq(ka, Kind.copy))
  }

  test("Sort and Lin name Univ at the constant kinds, and a $k capture binds a universe's kind") {
    val env = declsEnv(base + "def kindOf (A: Univ($k, $u)) : Kind := k\n")
    assertEquals(Interpreter.evalApply(env("Univ"), Vector(Kind.copy, Level.zero)), TypeTpe)
    assertEquals(Interpreter.evalApply(env("Univ"), Vector(Kind.lin, Level.one)), VLin(Level.one))
    assertEquals(Interpreter.evalApply(env("kindOf"), Vector(Kernel.natType)), Kind.copy)
    assertEquals(Interpreter.evalApply(env("kindOf"), Vector(env("LNats"))), Kind.lin)
    run(
      base +
        """
          |def kindOf (A: Univ($k, $u)) : Kind := k
          |def copyNat : Eq(Kind, kindOf(Nat), Kind.copy) := Eq.refl(Kind.copy)
          |def linNats : Eq(Kind, kindOf(LNats), Kind.lin) := Eq.refl(Kind.lin)
          |def sortIsUniv : Eq(Sort(Level.one), Type, Univ(Kind.copy, Level.zero)) := Eq.refl(Type)
          |def linIsUniv : Eq(Sort(Level.one), Lin(Level.zero), Univ(Kind.lin, Level.zero)) := Eq.refl(Lin(Level.zero))
          |""".stripMargin
    )
  }

  test("a universe with a kind variable prints, quotes as Univ, and is inferred as a match motive") {
    val res = runProgram(
      base +
        """
          |def pick (A: Univ($k, $u))(b: Bool) : Univ(k, u) := {
          |  let chosen := match b with
          |  | Bool.true => A
          |  | Bool.false => A
          |  chosen
          |}
          |
          |{ pick(LNats, Bool.true) }
          |""".stripMargin
    )
    assertEquals(PrettyPrinter.print(res), "LNats")
    val k = FreshVar.freshVar("k", KindTpe)
    assert(PrettyPrinter.print(VUniv(Kind.mk(k.id), Level.zero)).startsWith("Univ(k#"))
  }

  test("universes of different constant kinds are apart; a kind variable is solved by refinement") {
    run(
      base + "def apart (h: Eq(Sort(Level.one), Type, Lin(Level.zero))) : False := {\n  match h returning False with\n}\n"
    )
    assertErrorAt[MissingCase](
      base + "def notApart (k: Kind)(h: Eq(Sort(Level.one), Univ(k, Level.zero), Type)) : False := {\n  match h returning False with\n}\n",
      "match h returning False with"
    )
    // Matching an equation of kinds refines the kind variable, and the universe that mentions it follows.
    run(
      base +
        """
          |def asType (k: Kind)(e: Eq(Kind, k, Kind.copy))(A: Univ(k, Level.zero)) : Type := {
          |  match e returning Type with
          |  | Eq.refl j => A
          |}
          |""".stripMargin
    )
  }

  test("L1 over the kind lattice: a field's kind is at most its family's") {
    run(
      base +
        """
          |inductive Wrap (A: Univ($k, $u)) : Univ(k, u)
          | | mk (x: $A in Univ($k, $u)) : Wrap(A)
          |
          |inductive Hold (A: Univ($k, $u)) : Lin(u)
          | | mk (x: $A in Univ($k, $u)) : Hold(A)
          |
          |inductive Both2 (A: Univ($k1, $u))(B: Univ($k2, $v)) : Univ(Kind.join(k2, k1), Level.max(u, v))
          | | mk (a: $A in Univ($k1, $u))(b: $B in Univ($k2, $v)) : Both2(A, B)
          |""".stripMargin
    )
    assertErrorAt[LinearFieldInUnrestrictedFamily](
      base + "inductive Bad (A: Univ($k, $u)) : Sort(u)\n | mk (x: $A in Univ($k, $u)) : Bad(A)\n",
      "(x: $A in Univ($k, $u))"
    )
    assertErrorAt[LinearFieldInUnrestrictedFamily](
      base +
        "inductive Bad (A: Univ($k1, $u))(B: Univ($k2, $v)) : Univ(k1, Level.max(u, v))\n" +
        " | mk (a: $A in Univ($k1, $u))(b: $B in Univ($k2, $v)) : Bad(A, B)\n",
      "(b: $B in Univ($k2, $v))"
    )
    assertErrorAt[LinearFieldInUnrestrictedFamily](
      base + "inductive BadP (A: Univ($k, $u)) : Prop\n | mk (x: $A in Univ($k, $u)) : BadP(A)\n",
      "(x: $A in Univ($k, $u))"
    )
  }

  test("a value of variable kind is tracked: kind-polymorphic code treats it as affine") {
    assertErrorAt[LinearReused](
      base + "def dup (x: $A in Univ($k, $u)) : Prod(A, A) := Prod.mk(A, A, x, x)\n",
      "x",
      "x)\n"
    )
    assertErrorAt[LinearReused](
      base +
        "def heads (xs: List($A)) : Prod(List(A), List(A)) := {\n  match xs with\n" +
        "  | List.nil => Prod.mk(List(A), List(A), List.nil(A), List.nil(A))\n" +
        "  | List.cons h t => Prod.mk(List(A), List(A), List.cons(h, t), List.cons(h, List.nil(A)))\n}\n",
      "h",
      "h, List.nil(A))"
    )
    // A caller instantiates the kind: copyable values pass freely, and linear ones are consumed.
    run(
      base +
        """
          |def keep (x: $A in Univ($k, $u)) : A := x
          |def twice (n: Nat) : Nat := Nat.add(keep(n), keep(n))
          |def once (xs: LNats) : Nat := count(keep(xs))
          |""".stripMargin
    )
    assertErrorAt[LinearReused](
      base + "def keep (x: $A in Univ($k, $u)) : A := x\ndef bad (xs: LNats) : Nat := Nat.add(count(keep(xs)), count(xs))\n",
      "xs",
      "xs))\n"
    )
  }

  test("a tracked local stays tracked where refinement makes its kind copy, and a fresh binding of it is copyable") {
    def refined(body: String): String =
      base +
        s"""
           |def asCopy (k: Kind)(e: Eq(Kind, k, Kind.copy))(A: Univ(k, Level.zero))(x: A) : Prod(A, A) := {
           |  match e returning Prod(A, A) with
           |  | Eq.refl j => $body
           |}
           |""".stripMargin
    assertErrorAt[LinearReused](refined("Prod.mk(A, A, x, x)"), "x", "x)\n}")
    // Binding it afresh is intended: the branch has proved A copyable, so y is untracked, and x is used once.
    run(refined("{\n    let y := x\n    Prod.mk(A, A, y, y)\n  }"))
  }

  // KERNEL_FOLLOWUPS 1.4: a constructor capture whose universe does not fit its parameter's used to be unlocated.
  test("a constructor capture that does not fit its parameter's universe is a located TypeMismatch") {
    assertErrorAt[TypeMismatch](
      base + "inductive Box (A: Sort($u)) : Sort(u)\n | mk (a: $A in Lin($u)) : Box(A)\n",
      "(A)",
      "Box(A)\n"
    )
    assertErrorAt[TypeMismatch](
      base + "def S (u: Level) : Sort(Level.succ(u)) := Sort(u)\ninductive Box (A: Lin($u)) : Lin(u)\n | mk (a: $A in S($u)) : Box(A)\n",
      "(A)",
      "Box(A)\n"
    )
    // Through a user alias for Lin, the capture reads a universe's level by position, which only Sort has.
    val alias =
      base + "def L (u: Level) : Sort(Level.succ(u)) := Lin(u)\ninductive Box (A: Univ($k, $u)) : Univ(k, u)\n" +
        " | mk (a: $A in L($u)) : Box(A)\n\ninductive LB : Lin(Level.zero)\n | mk (n: Nat) : LB\n\n"
    val error = assertErrorAt[FailedToOpenCapture](alias + "def f (b: LB) : Box(LB) := Box.mk(b)\n", "(b)")
    assertEquals(
      error.getMessage,
      "The type-pattern capture $u cannot be read off Lin(Level.zero), which has no argument 0"
    )
  }

  test("an instance binder or an Eq carrier of variable kind is refused") {
    assertErrorAt[LinearInstance](base + "def bad [x: $A in Univ($k, $u)] : Nat := 0\n", "[x: $A in Univ($k, $u)]")
    // Located at the pattern argument that does not fit its parameter.
    assertErrorAt[TypeMismatch](
      base + "def bad (A: Univ($k, $u))(x: A)(e: Eq(A, x, x)) : Nat := 0\n",
      "A",
      "A, x, x)"
    )
  }

  test("the kernel List, Prod, Option and Sum are copyable at copyable arguments and linear at linear ones") {
    run(
      base +
        """
          |def dupList (xs: List(Nat)) : Prod(List(Nat), List(Nat)) := Prod.mk(List(Nat), List(Nat), xs, xs)
          |def dupPair (p: Prod(Nat, Bool)) : Nat := {
          |  let (a, b) := p
          |  let (c, d) := p
          |  Nat.add(a, c)
          |}
          |def lengths (xs: List(LNats)) : Nat decreases structural(xs) := {
          |  match xs with
          |  | List.nil => 0
          |  | List.cons h t => Nat.add(count(h), lengths(t))
          |}
          |def fromOption (x: Option(LNats)) : Nat := {
          |  match x with
          |  | Option.none => 0
          |  | Option.some v => count(v)
          |}
          |def fromSum (x: Sum(LNats, Nat)) : Nat := {
          |  match x with
          |  | Sum.inl v => count(v)
          |  | Sum.inr n => n
          |}
          |def total : Nat := lengths(List.cons(LNats.cons(1, LNats.nil), List.cons(LNats.nil, List.nil(LNats))))
          |""".stripMargin
    )
    assertErrorAt[LinearReused](
      base + "def bad (xs: List(LNats)) : Prod(List(LNats), List(LNats)) := Prod.mk(List(LNats), List(LNats), xs, xs)\n",
      "xs",
      "xs)\n"
    )
    assertErrorAt[LinearReused](
      base + "def bad (p: Prod(LNats, Nat)) : Nat := {\n  let (a, b) := p\n  let (c, d) := p\n  b\n}\n",
      "p",
      "p\n  b"
    )
    // A selector consumes a linear pair and drops the other component.
    run(base + "def first (p: Prod(LNats, LNats)) : Nat := count(p.fst)\n")
    // The natives take kind-polymorphic lists and consume linear ones.
    run(
      base +
        "def joined (a: List(LNats))(b: List(LNats)) : Nat := List.length(List.append(a, b))\n" +
        "def size : Nat := joined(List.cons(LNats.nil, List.nil(LNats)), List.nil(LNats))\n"
    )
    assertEquals(
      result(
        base + "\nList.length(List.append(List.cons(LNats.nil, List.nil(LNats)), List.cons(LNats.nil, List.nil(LNats))))\n"
      ),
      "2"
    )
  }

  test("a constrained capture fixes an element type's kind: List($A in Sort($u)) takes copyable elements only") {
    val dupHeads =
      base +
        """
          |def dupHeads (xs: List($A in Sort($u))) : List(A) decreases structural(xs) := {
          |  match xs with
          |  | List.nil => List.nil(A)
          |  | List.cons h t => List.cons(h, List.cons(h, dupHeads(t)))
          |}
          |""".stripMargin
    assertEquals(result(dupHeads + "\nList.length(dupHeads(List.cons(1, List.cons(2, List.nil(Nat)))))\n"), "4")
    assertErrorAt[TypeMismatch](
      dupHeads + "def bad (xs: List(LNats)) : Nat := List.length(dupHeads(xs))\n",
      "(xs)",
      "dupHeads(xs)"
    )
    // A plain capture is kind-polymorphic, so the same body duplicates a value of variable kind.
    assertErrorAt[LinearReused](
      base +
        "def dupHeads (xs: List($A)) : List(A) decreases structural(xs) := {\n  match xs with\n  | List.nil => List.nil(A)\n" +
        "  | List.cons h t => List.cons(h, List.cons(h, dupHeads(t)))\n}\n",
      "h",
      "h, dupHeads(t))"
    )
  }

  test("a function type is copyable whatever the kinds of its domain and codomain (F1)") {
    val env =
      declsEnv(base + "def F (A: Univ($k, $u)) : Sort(u) := (x: A) -> A\ndef G : Type := (xs: LNats) -> LNats\n")
    assertEquals(env("G").tpe, TypeTpe)
    run(base + "def apply (A: Univ($k, $u))(f: (x: A) -> A)(g: (x: A) -> A)(x: A) : A := g(f(x))\n")
  }
}
