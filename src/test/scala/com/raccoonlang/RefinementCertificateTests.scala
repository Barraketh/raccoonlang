package com.raccoonlang

class RefinementCertificateTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

  private val peano =
    """
      |inductive P:Type
      | | z:P
      | | s(n:P):P
      |""".stripMargin

  test("the private equality bootstrap works without the source prelude") {
    val source = peano + "def pick:P := match P.z returning P with\n | P.z => P.z\n"
    typecheckDecls(source, Prelude.none)
    RefinementCertificates.Testing.withWrongQuotation {
      expectTypeError[MissingCase](
        peano + "def pick(A:Type):P := match P.z returning P with\n | P.z => P.z\n",
        Prelude.none
      )
    }
  }

  test("same-constructor injection handles dependent field coordinates") {
    typecheckDecls(
      peano +
        """
          |inductive Dep:Type { level = one }
          | | mk(A:Type)(x:A):Dep
          |def impossible(n:P)(h:Eq(Dep,Dep.mk(P,P.z),Dep.mk(P,P.s(n)))):P :=
          |  match h returning P with
          |""".stripMargin
    )
  }

  test("restricted N1 certifies injectivity of a checked data-family parameter") {
    val source =
      peano +
        """
          |inductive Tag(n:P):Type
          | | mk:Tag(n)
          |def impossible(h:Eq(Type,Tag(P.z),Tag(P.s(P.z)))):P :=
          |  match h returning P with
          |""".stripMargin

    RefinementCertificates.Testing.withProposals {
      typecheckDecls(source)
    }
    RefinementCertificates.Testing.withInvalidProof {
      RefinementCertificates.Testing.withProposals {
        expectTypeError[MissingCase](source)
      }
    }
  }

  test("Prop-family equations do not receive N1 injectivity") {
    val source =
      peano +
        """
          |inductive Pred(n:P):Prop
          | | mk:Pred(n)
          |def needCase(h:Eq(Prop,Pred(P.z),Pred(P.s(P.z)))):P :=
          |  match h returning P with
          |""".stripMargin

    RefinementCertificates.Testing.withProposals {
      expectTypeError[MissingCase](source)
    }
  }

  test("different data-family heads do not receive type-generativity certificates") {
    val source =
      peano +
        """
          |inductive LeftTag(n:P):Type
          | | left:LeftTag(n)
          |inductive RightTag(n:P):Type
          | | right:RightTag(n)
          |def needCase(h:Eq(Type,LeftTag(P.z),RightTag(P.z))):P :=
          |  match h returning P with
          |""".stripMargin

    RefinementCertificates.Testing.withProposals {
      expectTypeError[MissingCase](source)
    }
  }

  test("a usable data index can certify exclusion when another index cannot be quoted") {
    typecheckDecls(
      """
        |inductive Node:Type
        | | zero:Node
        | | one:Node
        |def constant(n:Node):Node -> Node := fun (x:Node):Node => n
        |inductive Typed indices (run:Node -> Node)(code:Node):Prop
        | | zero:Typed(constant(Node.zero),Node.zero)
        | | one:Typed(constant(Node.one),Node.one)
        |inductive Flag:Prop
        | | yes:Flag
        |def origin(run:Node -> Node)(proof:Typed(run,Node.one)):Flag :=
        |  match proof returning Flag with
        | | Typed.one => Flag.yes
        |""".stripMargin,
      Prelude.none
    )
  }

  test("unsupported function quotation keeps a proposed constructor reachable") {
    val source =
      """
        |inductive Node:Type
        | | zero:Node
        |inductive Flag:Prop
        | | yes:Flag
        |def constant(n:Node):Node -> Node := fun (x:Node):Node => n
        |inductive Typed indices (run:Node -> Node):Prop
        | | mk:Typed(constant(Node.zero))
        |def needCase(run:Node -> Node)(proof:Typed(run)):Flag :=
        |  match proof returning Flag with
        |""".stripMargin
    RefinementCertificates.Testing.withProposals {
      expectTypeError[MissingCase](source, Prelude.none)
    }
  }

  test("invalid pruning proposals cannot omit an inhabited case") {
    val source = peano + "def pick(n:P):P := match n returning P with\n | P.z => P.z\n"
    RefinementCertificates.Testing.withProposals {
      expectTypeError[MissingCase](source)
    }
  }

  test("a malformed certificate proof cannot omit an inhabited known-constructor case") {
    val source = peano + "def pick:P := match P.z returning P with\n | P.z => P.z\n"
    RefinementCertificates.Testing.withInvalidProof {
      expectTypeError[MissingCase](source)
    }
  }

  test("written unreachable cases are diagnosed only after certification") {
    val source = peano +
      "def pick:P := match P.z returning P with\n | P.z => P.z\n | P.s n => P.z\n"
    expectTypeError[UnreachableCase](source)
    RefinementCertificates.Testing.withInvalidProof {
      typecheckDecls(source)
    }
  }

  test("Prop empty-fiber large elimination shares certified reachability") {
    val source = peano +
      "inductive At indices (n:P):Prop\n | mk(hidden:P):At(P.z)\n" +
      "def absurd(n:P)(proof:At(P.s(n))):P := match proof returning P with\n"
    typecheckDecls(source)
    RefinementCertificates.Testing.withInvalidProof {
      expectTypeError[PropEliminationRestricted](source)
    }
  }
}
