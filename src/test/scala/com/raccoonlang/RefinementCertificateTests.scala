package com.raccoonlang

class RefinementCertificateTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test
  private val peano = "inductive P:Type\n | z:P\n | s(n:P):P\n"

  test("ordinary no-confusion certifies nested same-constructor fields") {
    typecheckDecls(peano + "def absurd(n:P)(h:Eq(P,P.s(P.z),P.s(P.s(n)))):P := match h returning P with\n")
  }
  test("dependent constructor injection shares the homogeneous field domain") {
    typecheckDecls(peano + """
                             |inductive D:Type { level = one }
                             | | mk(A:Type)(x:A):D
                             |def absurd(n:P)(h:Eq(D,D.mk(P,P.z),D.mk(P,P.s(n)))):P := match h returning P with
                             |""".stripMargin)
  }
  test("bootstrap needs neither a source Eq nor a source bottom") {
    typecheckDecls(peano + "def pick:P := match P.z returning P with\n | P.z => P.z\n", Prelude.none)
  }
  test("wrong pruning proposals cannot omit an inhabited case") {
    RefinementCertificates.Testing.withProposals {
      expectOnly[MissingCase](typecheckDecls(peano + "def f(n:P):P := match n returning P with\n | P.z => P.z\n"))
      typecheckDecls(peano + "def f(n:P):P := match n returning P with\n | P.z => P.z\n | P.s m => m\n")
    }
  }
  test("many compatible index hypotheses cannot amplify a wrong proposal") {
    val indices = (1 to 12).map(i => s"n$i")
    val telescope = indices.map(n => s"($n:P)").mkString
    val args = indices.mkString(",")
    val source = peano + s"inductive At indices $telescope:Prop\n | mk$telescope:At($args)\n" +
      s"def bad$telescope(h:At($args)):P := match h returning P with\n"
    RefinementCertificates.Testing.withProposals {
      expectOnly[MissingCase](typecheckDecls(source))
      val typeTelescope = indices.map(n => s"($n:Type)").mkString
      val familyArgs = indices.map(n => s"List($n)").mkString(",")
      val compound = s"inductive At indices $typeTelescope:Prop\n | mk$typeTelescope:At($familyArgs)\n" +
        s"def bad$typeTelescope(h:At($familyArgs)):False := match h returning False with\n"
      expectOnly[MissingCase](typecheckDecls(compound, Prelude.default))
    }
  }
  test("wrong proposals do not refute arbitrary application equations") {
    RefinementCertificates.Testing.withProposals {
      expectOnly[MissingCase](
        typecheckDecls(peano + "def bad(g:P -> P)(a:P)(b:P)(h:Eq(P,g(a),g(b))):P := match h returning P with\n")
      )
    }
  }
  test("ordinary rejection retains cases through known-constructor and wildcard coverage") {
    RefinementCertificates.Testing.withInvalidProof {
      expectOnly[MissingCase](typecheckDecls(peano + "def pick:P := match P.z returning P with\n | P.z => P.z\n"))
      typecheckDecls(peano + "def pick:P := match P.z returning P with\n | P.z => P.z\n | _ => P.z\n")
    }
  }
  test("ordinary rejection does not report a written case unreachable") {
    RefinementCertificates.Testing.withInvalidProof {
      typecheckDecls(peano + "def pick:P := match P.z returning P with\n | P.z => P.z\n | P.s n => P.z\n")
    }
  }
  test("the Prop empty-fiber large-elimination gate uses certified coverage") {
    val program = peano + "inductive At indices (n:P):Prop\n | mk(x:P):At(P.z)\n" +
      "def absurd(n:P)(h:At(P.s(n))):P := match h returning P with\n"
    typecheckDecls(program)
    RefinementCertificates.Testing.withInvalidProof {
      expectOnly[PropEliminationRestricted](typecheckDecls(program))
    }
  }
  test("known canonical proofs do not exclude alternative proof constructors") {
    val header = "inductive Choice:Prop\n | left:Choice\n | right:Choice\n"
    val definition = "def choose:Eq(Prop,Choice,Choice) := match Choice.left returning Eq(Prop,Choice,Choice) with\n"
    RefinementCertificates.Testing.withProposals {
      expectOnly[MissingCase](typecheckDecls(header + definition + " | Choice.left => Eq.refl(Choice)\n"))
      typecheckDecls(header + definition + " | Choice.left => Eq.refl(Choice)\n | Choice.right => Eq.refl(Choice)\n")
    }
  }
  test("linear families certify index contradictions but retain value-only alternatives") {
    val token = peano + "inductive Token:Type { kind = lin }\n | a:Token\n | b:Token\n"
    expectOnly[MissingCase](typecheckDecls(token + "def pick:P := match Token.a returning P with\n | Token.a => P.z\n"))
    typecheckDecls(token + "def pick:P := match Token.a returning P with\n | Token.a => P.z\n | Token.b => P.z\n")
    typecheckDecls(
      peano + "inductive Coin indices (n:P):Type { kind = lin }\n | mk:Coin(P.z)\n" +
        "def absurd(n:P)(c:Coin(P.s(n))):P := match c returning P with\n"
    )
  }
  test("nominal refutations preserve rigid forms after equality elimination") {
    typecheckDecls(
      """
        |inductive At indices (A:Type)(B:Type):Prop
        | | mk(C:Type):At(C,List(C))
        |def impossible(h:At(Bool,List(Nat))):False := match h returning False with
        |""".stripMargin,
      Prelude.default
    )
  }
  test("helper capture closure terminates with a dependent function capture type") {
    typecheckDecls(
      peano + """
                |inductive Eq {u:Level}(T:Type { level=u }) indices (x:T)(y:T):Prop
                | | refl(x:T):Eq(T,x,x)
                |inductive At indices (n:P):Type
                | | mk(n:P):At(n)
                |inductive A(f:(n:P)->At(n)):Type
                |inductive B(f:(n:P)->At(n)):Type
                |def impossible(f:(n:P)->At(n))(h:Eq(Type,A(f),B(f))):P := match h returning P with
                |""".stripMargin,
      Prelude.none
    )
  }
  test("constructor refutations quote structure-eta fields through checked source locals") {
    typecheckDecls(
      """
        |inductive Record:Type
        | | mk(a:Nat)(b:Bool):Record
        |def noSome(r:Record)(h:Eq(Option(Record),Option.some(r),Option.none(Record))):False :=
        | match h returning False with
        |""".stripMargin,
      Prelude.default
    )
  }
  test("a type-correct quotation of a different local cannot certify exclusion") {
    val source = """
                   |inductive Record:Type
                   | | mk(a:Nat)(b:Bool):Record
                   |def noSome(r:Record)(other:Record)(h:Eq(Option(Record),Option.some(r),Option.none(Record))):False :=
                   | match h returning False with
                   |""".stripMargin
    typecheckDecls(source, Prelude.default)
    RefinementCertificates.Testing.withWrongQuotation {
      expectOnly[MissingCase](typecheckDecls(source, Prelude.default))
    }
  }
  test("possibly linear scrutinees use only their unrestricted index hypotheses") {
    typecheckDecls(peano + """
                             |inductive Coin (k:Kind) indices (n:P):Type { kind = k }
                             | | mk:Coin(k,P.z)
                             |def absurd (k:Kind)(n:P)(c:Coin(k,P.s(n))):P := match c returning P with
                             |""".stripMargin)
  }
  test("failed speculative certificate checks preserve enclosing linear syntax") {
    val source = peano + """
                           |def bad:Prop := match (fun { kind = lin } (n:P):P => n)(P.z) returning Prop with
                           | | P.z => Eq(P,P.z,P.z)
                           | | P.s n => Eq(P,P.z,P.z)
                           |""".stripMargin
    expectOnly[LinearInType](typecheckDecls(source))
  }
}
