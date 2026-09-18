package com.raccoonlang

class NamespaceTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

  private def typecheckProgram(src: String): Unit =
    Interpreter.run(parse(src), Prelude.test)

  test("inductive head can also be used as a namespace for functions") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive List (A: Type) : Type
        | | nil : List(A)
        | | cons (tail: List(A))(head: A) : List(A)
        |
        |namespace List {
        |  def singleton (A: Type)(x: A): List(A) := cons(nil(A), x)
        |}
        |
        |{
        |  List.singleton(Peano, Peano.zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "List.cons")
  }

  test("open namespace snapshots known globals and checks namespace existence") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |namespace Peano {
        |  def add (a: Peano)(b: Peano): Peano := a
        |}
        |
        |open Peano
        |
        |{
        |  add(succ(zero), zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Peano.succ")

    val late =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |open Peano
        |
        |namespace Peano {
        |  def add (a: Peano)(b: Peano): Peano := a
        |}
        |
        |{
        |  add(succ(zero), zero)
        |}
        |""".stripMargin

    expectTypeError[NotFound](late)

    val missing =
      """
        |def Peano : Type := Type
        |open Peano
        |""".stripMargin

    intercept[NotFound] {
      parse(missing)
    }
  }

  test("root-qualified open bypasses current namespace shadowing") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |namespace Shadow {
        |  namespace Peano {
        |    def decoy : _root_.Peano := _root_.Peano.zero
        |  }
        |
        |  open _root_.Peano
        |
        |  def one : _root_.Peano := succ(zero)
        |}
        |
        |{
        |  Shadow.one
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Peano.succ")

    val shadowed =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |namespace Shadow {
        |  namespace Peano {
        |    def decoy : _root_.Peano := _root_.Peano.zero
        |  }
        |
        |  open Peano
        |
        |  def bad : _root_.Peano := succ(zero)
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
      parse(p)
    }
  }

  test("selected, renamed, and excluded open rules expose the requested aliases") {
    val selected =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |open Peano.{zero, succ}
        |
        |{
        |  succ(zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(selected)), "Peano.succ")

    val renamed =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |open Peano.{zero as natZero, succ as natSucc}
        |
        |{
        |  natSucc(natZero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(renamed)), "Peano.succ")

    val excludedAndRenamed =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |open Peano.{*, -succ, succ as nsucc}
        |
        |{
        |  nsucc(zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(excludedAndRenamed)), "Peano.succ")

    val excludedOriginal =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |open Peano.{*, -succ, succ as nsucc}
        |
        |def bad : Peano := succ(zero)
        |""".stripMargin

    intercept[NotFound] {
      typecheckProgram(excludedOriginal)
    }
  }

  test("open aliases can be used as qualified namespace prefixes") {
    val wildcard =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |namespace Data {
        |  inductive Tree (A: Type) : Type
        |   | leaf (value: A) : Tree(A)
        |}
        |
        |open Data
        |
        |{
        |  Tree.leaf(Peano.zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(wildcard)), "Data.Tree.leaf")

    val selected =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |namespace Data {
        |  inductive Tree (A: Type) : Type
        |   | leaf (value: A) : Tree(A)
        |}
        |
        |open Data.{Tree}
        |
        |{
        |  Tree.leaf(Peano.zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(selected)), "Data.Tree.leaf")

    val renamed =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |namespace Data {
        |  inductive Tree (A: Type) : Type
        |   | leaf (value: A) : Tree(A)
        |}
        |
        |open Data.{Tree as DTree}
        |
        |{
        |  DTree.leaf(Peano.zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(renamed)), "Data.Tree.leaf")

    val excluded =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |namespace Data {
        |  inductive Tree (A: Type) : Type
        |   | leaf (value: A) : Tree(A)
        |}
        |
        |open Data.{*, -Tree}
        |
        |def bad : Data.Tree(Peano) := Tree.leaf(Peano.zero)
        |""".stripMargin

    intercept[NotFound] {
      typecheckProgram(excluded)
    }

    val ambiguous =
      """
        |inductive Peano : Type
        | | zero : Peano
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
        |def bad : A.Tree(Peano) := Tree.leaf(Peano.zero)
        |""".stripMargin

    intercept[AmbiguousName] {
      parse(ambiguous)
    }
  }

  test("open conflicts are reported when opened") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |namespace A {
        |  def foo : Peano := Peano.zero
        |}
        |
        |namespace B {
        |  def foo : Peano := Peano.zero
        |}
        |
        |open A
        |open B
        |""".stripMargin

    intercept[AmbiguousName] {
      parse(p)
    }
  }

  test("anonymous command block scopes opens but keeps declarations") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |{
        |  open Peano
        |  def one : Peano := succ(zero)
        |}
        |
        |def two : Peano := Peano.succ(one)
        |""".stripMargin

    typecheckProgram(p)

    val scoped =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |{
        |  open Peano
        |  def ok : Peano := zero
        |}
        |
        |def bad : Peano := zero
        |""".stripMargin

    intercept[NotFound] {
      typecheckProgram(scoped)
    }
  }

  test("local dotted names project, root-qualified names bypass local shadowing") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |struct NatOps : Type
        | | mk (zero: Peano) : NatOps
        |
        |def local (Peano: NatOps): _root_.Peano := Peano.zero
        |def root (Peano: NatOps): _root_.Peano := _root_.Peano.zero
        |""".stripMargin

    typecheckProgram(p)
  }

  test("match cases may use explicit short constructor names from scrutinee type") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (p: Peano) : Peano
        |
        |def pred (n: Peano): Peano := {
        |  match n with
        |  | .zero => Peano.zero
        |  | .succ p => p
        |}
        |
        |{
        |  pred(Peano.succ(Peano.zero))
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Peano.zero")
  }

  test("plain case heads must resolve as globals, not locals") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (p: Peano) : Peano
        |
        |def bad (zero: Peano)(n: Peano): Peano := {
        |  match n with
        |  | zero => Peano.zero
        |  | Peano.succ p => p
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
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |namespace Data {
        |  inductive Tree : Type
        |   | leaf : Tree
        |   | node (left: Tree)(right: Tree) : Tree
        |}
        |
        |def classify (t: Data.Tree): Peano := {
        |  match t returning Peano with
        |  | Data.Tree.leaf => Peano.zero
        |  | Data.Tree.node left right => Peano.succ(Peano.zero)
        |}
        |
        |{
        |  classify(Data.Tree.node(Data.Tree.leaf, Data.Tree.leaf))
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(fullyQualified)), "Peano.succ")

    val partiallyQualified =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |namespace Data {
        |  inductive Tree : Type
        |   | leaf : Tree
        |   | node (left: Tree)(right: Tree) : Tree
        |}
        |
        |open Data
        |
        |def classify (t: Tree): Peano := {
        |  match t returning Peano with
        |  | Tree.leaf => Peano.zero
        |  | Tree.node left right => Peano.succ(Peano.zero)
        |}
        |
        |{
        |  classify(Tree.node(Tree.leaf, Tree.leaf))
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(partiallyQualified)), "Peano.succ")

    val unqualified =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |namespace Data {
        |  inductive Tree : Type
        |   | leaf : Tree
        |   | node (left: Tree)(right: Tree) : Tree
        |}
        |
        |open Data.Tree
        |
        |def classify (t: Data.Tree): Peano := {
        |  match t returning Peano with
        |  | leaf => Peano.zero
        |  | node left right => Peano.succ(Peano.zero)
        |}
        |
        |{
        |  classify(node(leaf, leaf))
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(unqualified)), "Peano.succ")

    val renamedUnqualified =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |open Peano.{zero as z, succ as s}
        |
        |def pred (n: Peano): Peano := {
        |  match n returning Peano with
        |  | z => Peano.zero
        |  | s p => p
        |}
        |
        |{
        |  pred(s(z))
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(renamedUnqualified)), "Peano.zero")
  }

  test("raw elaboration rejects unresolved imports") {
    val p = "import Mathlib.Data.Peano.Basic\n"

    intercept[UnsupportedImport] {
      parse(p)
    }
  }

  test("old double-colon qualified syntax is rejected") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |{ Peano::zero }
        |""".stripMargin

    assert(LanguageParser.parseProgram(p).isInstanceOf[Failure])
  }
}
