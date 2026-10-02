package com.raccoonlang

class SubsingletonTests extends munit.FunSuite with TestSupport {

  test("proposition instances of Subsingleton are rejected") {
    expectOnly[ImplicitReconstructionFailed](typecheckDecls("def bad : Subsingleton(True) := True.intro\n"))
  }

  test("proof irrelevance transports predicates without a Subsingleton witness") {
    typecheckDecls("def irrel (P: Prop)(Q: P -> Prop)(h1: P)(h2: P)(q: Q(h1)): Q(h2) := q\n")
  }

}
