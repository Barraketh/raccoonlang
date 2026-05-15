package com.raccoonlang

class NamespaceTests extends munit.FunSuite {
  private def parseCore(src: String): CoreAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) => Elaborator.elab(value)
      case err: Failure         => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def runProgram(src: String): Value =
    Interpreter.run(parseCore(src)).getOrElse(fail("Program has no body"))

  private def typecheckProgram(src: String): Unit =
    Interpreter.run(parseCore(src))

  private def ctorName(v: Value): String = v match {
    case Value.VCtor(head, _, _) => head.name
    case other                   => fail(s"Expected constructor value, got $other")
  }

  test("inductive head can also be used as a namespace for functions") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive List (A: Type) : Type
        | | nil : List(A)
        | | cons (tail: List(A))(head: A) : List(A)
        |
        |namespace List {
        |  inline def singleton (A: Type)(x: A): List(A) := cons(A, nil(A), x)
        |}
        |
        |{
        |  List.singleton(Nat, Nat.zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "List.cons")
  }

  test("open namespace snapshots known globals and checks namespace existence") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |namespace Nat {
        |  inline def add (a: Nat)(b: Nat): Nat := a
        |}
        |
        |open Nat
        |
        |{
        |  add(succ(zero), zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Nat.succ")

    val late =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |open Nat
        |
        |namespace Nat {
        |  inline def add (a: Nat)(b: Nat): Nat := a
        |}
        |
        |{
        |  add(succ(zero), zero)
        |}
        |""".stripMargin

    intercept[NotFound] {
      runProgram(late)
    }

    val missing =
      """
        |def Nat : Type := Type
        |open Nat
        |""".stripMargin

    intercept[NotFound] {
      parseCore(missing)
    }
  }

  test("root-qualified open bypasses current namespace shadowing") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |namespace Shadow {
        |  namespace Nat {
        |    def decoy : _root_.Nat := _root_.Nat.zero
        |  }
        |
        |  open _root_.Nat
        |
        |  def one : _root_.Nat := succ(zero)
        |}
        |
        |{
        |  Shadow.one
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Nat.succ")

    val shadowed =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |namespace Shadow {
        |  namespace Nat {
        |    def decoy : _root_.Nat := _root_.Nat.zero
        |  }
        |
        |  open Nat
        |
        |  def bad : _root_.Nat := succ(zero)
        |}
        |""".stripMargin

    intercept[NotFound] {
      typecheckProgram(shadowed)
    }
  }

  test("empty namespace blocks do not create openable namespace objects") {
    val p =
      """
        |namespace Empty {
        |}
        |
        |open Empty
        |""".stripMargin

    intercept[NotFound] {
      parseCore(p)
    }
  }

  test("selected, renamed, and excluded open rules expose the requested aliases") {
    val selected =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |open Nat.{zero, succ}
        |
        |{
        |  succ(zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(selected)), "Nat.succ")

    val renamed =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |open Nat.{zero as natZero, succ as natSucc}
        |
        |{
        |  natSucc(natZero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(renamed)), "Nat.succ")

    val excludedAndRenamed =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |open Nat.{*, -succ, succ as nsucc}
        |
        |{
        |  nsucc(zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(excludedAndRenamed)), "Nat.succ")

    val excludedOriginal =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |open Nat.{*, -succ, succ as nsucc}
        |
        |def bad : Nat := succ(zero)
        |""".stripMargin

    intercept[NotFound] {
      typecheckProgram(excludedOriginal)
    }
  }

  test("open aliases can be used as qualified namespace prefixes") {
    val wildcard =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |namespace Data {
        |  inductive Tree (A: Type) : Type
        |   | leaf (value: A) : Tree(A)
        |}
        |
        |open Data
        |
        |{
        |  Tree.leaf(Nat, Nat.zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(wildcard)), "Data.Tree.leaf")

    val selected =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |namespace Data {
        |  inductive Tree (A: Type) : Type
        |   | leaf (value: A) : Tree(A)
        |}
        |
        |open Data.{Tree}
        |
        |{
        |  Tree.leaf(Nat, Nat.zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(selected)), "Data.Tree.leaf")

    val renamed =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |namespace Data {
        |  inductive Tree (A: Type) : Type
        |   | leaf (value: A) : Tree(A)
        |}
        |
        |open Data.{Tree as DTree}
        |
        |{
        |  DTree.leaf(Nat, Nat.zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(renamed)), "Data.Tree.leaf")

    val excluded =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |namespace Data {
        |  inductive Tree (A: Type) : Type
        |   | leaf (value: A) : Tree(A)
        |}
        |
        |open Data.{*, -Tree}
        |
        |def bad : Data.Tree(Nat) := Tree.leaf(Nat, Nat.zero)
        |""".stripMargin

    intercept[NotFound] {
      typecheckProgram(excluded)
    }

    val ambiguous =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |namespace A {
        |  inductive Tree (A: Type) : Type
        |   | leaf (value: A) : Tree(A)
        |}
        |
        |namespace B {
        |  inductive Tree (A: Type) : Type
        |   | leaf (value: A) : Tree(A)
        |}
        |
        |open A
        |open B
        |
        |def bad : A.Tree(Nat) := Tree.leaf(Nat, Nat.zero)
        |""".stripMargin

    intercept[AmbiguousName] {
      parseCore(ambiguous)
    }
  }

  test("open conflicts are reported when opened") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |namespace A {
        |  def foo : Nat := Nat.zero
        |}
        |
        |namespace B {
        |  def foo : Nat := Nat.zero
        |}
        |
        |open A
        |open B
        |""".stripMargin

    intercept[AmbiguousName] {
      parseCore(p)
    }
  }

  test("anonymous command block scopes opens but keeps declarations") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |{
        |  open Nat
        |  def one : Nat := succ(zero)
        |}
        |
        |def two : Nat := Nat.succ(one)
        |""".stripMargin

    typecheckProgram(p)

    val scoped =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |{
        |  open Nat
        |  def ok : Nat := zero
        |}
        |
        |def bad : Nat := zero
        |""".stripMargin

    intercept[NotFound] {
      typecheckProgram(scoped)
    }
  }

  test("local dotted names project, root-qualified names bypass local shadowing") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |struct NatOps : Type
        | | mk (zero: Nat) : NatOps
        |
        |def local (Nat: NatOps): _root_.Nat := Nat.zero
        |def root (Nat: NatOps): _root_.Nat := _root_.Nat.zero
        |""".stripMargin

    typecheckProgram(p)
  }

  test("match cases may use explicit short constructor names from scrutinee type") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (p: Nat) : Nat
        |
        |inline def pred (n: Nat): Nat := {
        |  match n with
        |  | .zero => Nat.zero
        |  | .succ p => p
        |}
        |
        |{
        |  pred(Nat.succ(Nat.zero))
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Nat.zero")
  }

  test("plain case heads must resolve as globals, not locals") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (p: Nat) : Nat
        |
        |inline def bad (zero: Nat)(n: Nat): Nat := {
        |  match n with
        |  | zero => Nat.zero
        |  | Nat.succ p => p
        |}
        |""".stripMargin

    intercept[LocalCaseHead] {
      typecheckProgram(p)
    }
  }

  test("constructors for inductives inside namespaces may be called fully, partially, and unqualified") {
    val fullyQualified =
      """
        |namespace Data {
        |  inductive Tree : Type
        |   | leaf : Tree
        |   | node (left: Tree)(right: Tree) : Tree
        |}
        |
        |{
        |  Data.Tree.node(Data.Tree.leaf, Data.Tree.leaf)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(fullyQualified)), "Data.Tree.node")

    val partiallyQualified =
      """
        |namespace Data {
        |  inductive Tree : Type
        |   | leaf : Tree
        |   | node (left: Tree)(right: Tree) : Tree
        |}
        |
        |open Data
        |
        |{
        |  Tree.node(Tree.leaf, Tree.leaf)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(partiallyQualified)), "Data.Tree.node")

    val unqualified =
      """
        |namespace Data {
        |  inductive Tree : Type
        |   | leaf : Tree
        |   | node (left: Tree)(right: Tree) : Tree
        |}
        |
        |open Data.Tree
        |
        |{
        |  node(leaf, leaf)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(unqualified)), "Data.Tree.node")
  }

  test("match cases for namespaced inductives may be fully qualified, partially qualified, and unqualified") {
    val fullyQualified =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |namespace Data {
        |  inductive Tree : Type
        |   | leaf : Tree
        |   | node (left: Tree)(right: Tree) : Tree
        |}
        |
        |inline def classify (t: Data.Tree): Nat := {
        |  match t returning Nat with
        |  | Data.Tree.leaf => Nat.zero
        |  | Data.Tree.node left right => Nat.succ(Nat.zero)
        |}
        |
        |{
        |  classify(Data.Tree.node(Data.Tree.leaf, Data.Tree.leaf))
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(fullyQualified)), "Nat.succ")

    val partiallyQualified =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |namespace Data {
        |  inductive Tree : Type
        |   | leaf : Tree
        |   | node (left: Tree)(right: Tree) : Tree
        |}
        |
        |open Data
        |
        |inline def classify (t: Tree): Nat := {
        |  match t returning Nat with
        |  | Tree.leaf => Nat.zero
        |  | Tree.node left right => Nat.succ(Nat.zero)
        |}
        |
        |{
        |  classify(Tree.node(Tree.leaf, Tree.leaf))
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(partiallyQualified)), "Nat.succ")

    val unqualified =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |namespace Data {
        |  inductive Tree : Type
        |   | leaf : Tree
        |   | node (left: Tree)(right: Tree) : Tree
        |}
        |
        |open Data.Tree
        |
        |inline def classify (t: Data.Tree): Nat := {
        |  match t returning Nat with
        |  | leaf => Nat.zero
        |  | node left right => Nat.succ(Nat.zero)
        |}
        |
        |{
        |  classify(node(leaf, leaf))
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(unqualified)), "Nat.succ")

    val renamedUnqualified =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |open Nat.{zero as z, succ as s}
        |
        |inline def pred (n: Nat): Nat := {
        |  match n returning Nat with
        |  | z => Nat.zero
        |  | s p => p
        |}
        |
        |{
        |  pred(s(z))
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(renamedUnqualified)), "Nat.zero")
  }

  test("raw elaboration rejects unresolved imports") {
    val p = "import Mathlib.Data.Nat.Basic\n"

    intercept[UnsupportedImport] {
      parseCore(p)
    }
  }

  test("old double-colon qualified syntax is rejected") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |{ Nat::zero }
        |""".stripMargin

    assert(LanguageParser.parseProgram(p).isInstanceOf[Failure])
  }
}
