package com.raccoonlang

class NamespaceTests extends munit.FunSuite {
  private def parseCore(src: String): CoreAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) => Elaborator.elab(value, Prelude.test)
      case err: Failure         => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def runProgram(src: String): Value =
    Interpreter.run(parseCore(src), Prelude.test).getOrElse(fail("Program has no body"))

  private def typecheckProgram(src: String): Unit =
    Interpreter.run(parseCore(src), Prelude.test)

  private def ctorName(v: Value): String = v match {
    case ConstructorValue(head, _) => head.name
    case other                     => fail(s"Expected constructor value, got $other")
  }

  test("inductive head can also be used as a namespace for functions") {
    val p =
      """
        |inductive Bag (A: Type) : Type
        | | nil {A: Type} : Bag(A)
        | | cons {A: Type} (tail: Bag(A))(head: A) : Bag(A)
        |
        |namespace Bag {
        |  def singleton (A: Type)(x: A): Bag(A) := cons(A, nil(A), x)
        |}
        |
        |{
        |  Bag.singleton(Nat, Nat.zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Bag.cons")
  }

  test("open namespace snapshots known globals and checks namespace existence") {
    val p =
      """
        |namespace Nat {
        |  def keepLeft (a: Nat)(b: Nat): Nat := a
        |}
        |
        |open Nat
        |
        |{
        |  keepLeft(succ(zero), zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(p)), "Nat.succ")

    val late =
      """
        |open Nat
        |
        |namespace Nat {
        |  def keepLeft (a: Nat)(b: Nat): Nat := a
        |}
        |
        |{
        |  keepLeft(succ(zero), zero)
        |}
        |""".stripMargin

    intercept[NotFound] {
      runProgram(late)
    }

    val missing =
      """
        |def Number : Type := Type
        |open Number
        |""".stripMargin

    intercept[NotFound] {
      parseCore(missing)
    }
  }

  test("root-qualified open bypasses current namespace shadowing") {
    val p =
      """
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
        |open Nat.{zero, succ}
        |
        |{
        |  succ(zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(selected)), "Nat.succ")

    val renamed =
      """
        |open Nat.{zero as natZero, succ as natSucc}
        |
        |{
        |  natSucc(natZero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(renamed)), "Nat.succ")

    val excludedAndRenamed =
      """
        |open Nat.{*, -succ, succ as nsucc}
        |
        |{
        |  nsucc(zero)
        |}
        |""".stripMargin

    assertEquals(ctorName(runProgram(excludedAndRenamed)), "Nat.succ")

    val excludedOriginal =
      """
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
        |namespace Data {
        |  inductive Tree (A: Type) : Type
        |   | leaf {A: Type} (value: A) : Tree(A)
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
        |namespace Data {
        |  inductive Tree (A: Type) : Type
        |   | leaf {A: Type} (value: A) : Tree(A)
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
        |namespace Data {
        |  inductive Tree (A: Type) : Type
        |   | leaf {A: Type} (value: A) : Tree(A)
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
        |namespace Data {
        |  inductive Tree (A: Type) : Type
        |   | leaf {A: Type} (value: A) : Tree(A)
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
        |namespace A {
        |  inductive Tree (A: Type) : Type
        |   | leaf {A: Type} (value: A) : Tree(A)
        |}
        |
        |namespace B {
        |  inductive Tree (A: Type) : Type
        |   | leaf {A: Type} (value: A) : Tree(A)
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
        |inductive NatOps : Type
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
        |def pred (n: Nat): Nat := {
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
        |def bad (zero: Nat)(n: Nat): Nat := {
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
        |namespace Data {
        |  inductive Tree : Type
        |   | leaf : Tree
        |   | node (left: Tree)(right: Tree) : Tree
        |}
        |
        |def classify (t: Data.Tree): Nat := {
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
        |namespace Data {
        |  inductive Tree : Type
        |   | leaf : Tree
        |   | node (left: Tree)(right: Tree) : Tree
        |}
        |
        |open Data
        |
        |def classify (t: Tree): Nat := {
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
        |namespace Data {
        |  inductive Tree : Type
        |   | leaf : Tree
        |   | node (left: Tree)(right: Tree) : Tree
        |}
        |
        |open Data.Tree
        |
        |def classify (t: Data.Tree): Nat := {
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
        |open Nat.{zero as z, succ as s}
        |
        |def pred (n: Nat): Nat := {
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

  /** The source text where `src` is `AlreadyDefined`, which must be located. */
  private def redeclaredAt(src: String): String = {
    val error = intercept[AlreadyDefined](typecheckProgram(src))
    val span = error.span.getOrElse(fail(s"${error.getMessage} has no span"))
    src.substring(span.start, span.end)
  }

  // KERNEL_FOLLOWUPS 1.4.
  test("AlreadyDefined is located at the redeclaration") {
    assertEquals(redeclaredAt("def twice : Nat := 0\ndef twice : Nat := 1\n"), "twice")
    assertEquals(redeclaredAt("namespace N {\n  axiom a : Nat\n}\nnamespace N {\n  axiom a : Nat\n}\n"), "a")
    assertEquals(redeclaredAt("inductive T : Type\n | a : T\n\ninductive T : Type\n | b : T\n"), "T")
    assertEquals(redeclaredAt("inductive T : Type\n | a : T\n | a : T\n"), "a")
    assertEquals(redeclaredAt("def f (x: Nat)(x: Nat) : Nat := x\n"), "(x: Nat)")
    assertEquals(
      redeclaredAt(
        "def f (n: Nat) : Nat := {\n  match n with\n  | Nat.succ k => k\n  | Nat.zero => 0\n}\n"
          .replace("succ k", "succ k k")
      ).trim,
      "| Nat.succ k k => k"
    )
    assertEquals(
      redeclaredAt("def bad (n: Nat): Nat decreases structural(n) := {\n  let bad := n\n  n\n}\n"),
      "let bad := n"
    )
  }

  // KERNEL_FOLLOWUPS 1.4: an explicitly opened name beats a member of the enclosing namespace; a wildcard does not.
  test("a selective open beats the enclosing namespace, and a wildcard open does not") {
    def program(open: String): String =
      s"""
         |namespace Lib {
         |  def pick : Nat := Nat.succ(Nat.zero)
         |}
         |
         |namespace Mine {
         |  def pick : Nat := Nat.zero
         |
         |  $open
         |
         |  def chosen : Nat := pick
         |}
         |
         |Mine.chosen
         |""".stripMargin

    assertEquals(ctorName(runProgram(program("open Lib.{pick}"))), "Nat.succ")
    assertEquals(ctorName(runProgram(program("open Lib"))), "Nat.zero")
    assertEquals(ctorName(runProgram(program("open Lib.{*}"))), "Nat.zero")
    // A renamed alias is selective too, and so is a name a wildcard and an explicit rule both open.
    assertEquals(
      ctorName(
        runProgram(
          program("open Lib.{pick as chosen0}").replace("def chosen : Nat := pick", "def chosen : Nat := chosen0")
        )
      ),
      "Nat.succ"
    )
    assertEquals(ctorName(runProgram(program("open Lib.{*, pick}"))), "Nat.succ")
    // Locals still win.
    assertEquals(
      ctorName(
        runProgram(
          program("open Lib.{pick}")
            .replace("def chosen : Nat := pick", "def chosen : Nat := {\n    let pick := Nat.zero\n    pick\n  }")
        )
      ),
      "Nat.zero"
    )
  }

  test("a selective open in an outer scope beats the namespace and a wildcard open in an inner one") {
    val p =
      """
        |namespace A {
        |  def x : Nat := Nat.succ(Nat.zero)
        |}
        |
        |namespace B {
        |  def x : Nat := Nat.zero
        |}
        |
        |open A.{x}
        |
        |namespace C {
        |  def x : Nat := Nat.zero
        |
        |  open B
        |
        |  def chosen : Nat := x
        |}
        |
        |C.chosen
        |""".stripMargin
    assertEquals(ctorName(runProgram(p)), "Nat.succ")
  }

  test("old double-colon qualified syntax is rejected") {
    val p =
      """
        |{ Nat::zero }
        |""".stripMargin

    assert(LanguageParser.parseProgram(p).isInstanceOf[Failure])
  }
}
