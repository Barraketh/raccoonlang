package com.raccoonlang

/** Regression coverage for declaration-certified proof recovery and large elimination. */
class ProofCollapseTests extends munit.FunSuite {
  test("certified singleton proofs canonicalize to constructor form") {
    val result = TestSupport.eval(
      """
        |inductive Eq (A: Type) indices (left: A)(right: A) : Prop
        | | refl (value: A) : Eq(A, value, value)
        |
        |inductive Nat : Type
        | | zero : Nat
        |
        |{ Eq.refl(Nat.zero) }
        |""".stripMargin
    )
    result match {
      case Value.VCtor(head, _, tpe) =>
        assertEquals(head.name, "Eq.refl")
        assertEquals(Value.InductiveFamilyValue.unapply(tpe).map(_.head.name), Some("Eq"))
      case other => fail(s"Expected a canonical Eq.refl constructor, got $other")
    }
  }

  test("forced data fields permit large elimination from an exact proposition") {
    val result = TestSupport.eval(
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |inductive Box indices (n: Nat) : Prop
        | | mk (value: Nat) : Box(value)
        |
        |axiom h : Box(Nat.zero)
        |def inspect (p: Box(Nat.zero)): Nat := {
        |  match p returning Nat with
        |  | Box.mk value => value
        |}
        |{ inspect(h) }
        |""".stripMargin
    )
    assertEquals(PrettyPrinter.print(result), "Nat.zero()")
  }

  test("unforced data fields still reject large elimination") {
    intercept[PropEliminationRestricted] {
      TestSupport.check(
        """
          |inductive Nat : Type
          | | zero : Nat
          |
          |inductive Has : Prop
          | | intro (A: Type) : Has
          |
          |def bad (h: Has): Nat := {
          |  match h returning Nat with
          |  | Has.intro A => Nat.zero
          |}
          |""".stripMargin
      )
    }
  }

  test("injectively wrapped result arguments are not treated as direct recovery") {
    intercept[PropEliminationRestricted] {
      TestSupport.check(
        """
          |inductive Nat : Type
          | | zero : Nat
          | | succ (pred: Nat) : Nat
          |
          |inductive SuccBox indices (n: Nat) : Prop
          | | mk (value: Nat) : SuccBox(Nat.succ(value))
          |
          |def bad (h: SuccBox(Nat.succ(Nat.zero))): Nat := {
          |  match h returning Nat with
          |  | SuccBox.mk value => value
          |}
          |""".stripMargin
      )
    }
  }

  test("polymorphic fields become recoverable proofs at a Prop instance") {
    val result = TestSupport.eval(
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |inductive True : Prop
        | | intro : True
        |
        |inductive PolyBox {u: Level}(A: Sort(u)) : Sort(u)
        | | mk (value: A) : PolyBox(A)
        |
        |axiom boxedTrue : PolyBox(True)
        |def observe (P: Prop)(box: PolyBox(P)): Nat := {
        |  match box returning Nat with
        |  | PolyBox.mk _ => Nat.zero
        |}
        |{ observe(True, boxedTrue) }
        |""".stripMargin
    )
    assertEquals(PrettyPrinter.print(result), "Nat.zero()")
  }

  test("recursive proof fields reconstruct only one shallow layer") {
    val result = TestSupport.eval(
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |inductive Loop : Prop
        | | mk (next: Loop) : Loop
        |
        |axiom loop : Loop
        |def inspect (p: Loop): Nat := {
        |  match p returning Nat with
        |  | Loop.mk _ => Nat.zero
        |}
        |{ inspect(loop) }
        |""".stripMargin
    )
    assertEquals(PrettyPrinter.print(result), "Nat.zero()")
  }

  test("fixed positive-universe families carry no recovery metadata") {
    val (env, _) = TestSupport.check(
      """
        |inductive Box : Type
        | | mk : Box
        |""".stripMargin
    )
    env("Box") match {
      case Value.VConst(_, Value.Inductive(meta), _) => assertEquals(meta.proofRecovery, None)
      case other                                     => fail(s"Expected Box family, got $other")
    }
  }

  test("generic code remains data until an exact Prop instance") {
    val result = TestSupport.eval(
      """
        |inductive True : Prop
        | | intro : True
        |
        |def identity {u: Level}{A: Sort(u)} (x: A): A := x
        |def atProp (h: True): True := identity(h)
        |{ atProp(True.intro) }
        |""".stripMargin
    )
    result match {
      case Value.VCtor(head, _, _) => assertEquals(head.name, "True.intro")
      case other                   => fail(s"Expected exact Prop instantiation to canonicalize, got $other")
    }
  }

  test("VProof and certified constructors remain proof irrelevant") {
    val constructor = TestSupport.eval(
      """
        |inductive True : Prop
        | | intro : True
        |{ True.intro }
        |""".stripMargin
    )
    val proposition = constructor.tpe
    assert(ValueEquivalence.defEq(Value.VProof(proposition), constructor))
  }

  test("exact-result mismatch stays a runtime neutral after certified checking") {
    val result = TestSupport.eval(
      """
        |inductive Nat : Type
        | | zero : Nat
        | | one : Nat
        |
        |inductive Eq2 (A: Type) indices (left: A)(right: A) : Prop
        | | refl (value: A) : Eq2(A, value, value)
        |
        |axiom a : Nat
        |axiom b : Nat
        |axiom h : Eq2(Nat, a, b)
        |def inspect (p: Eq2(Nat, a, b)): Nat := {
        |  match p returning Nat with
        |  | Eq2.refl _ => Nat.zero
        |}
        |{ inspect(h) }
        |""".stripMargin
    )
    result match {
      case _: Value.NeutralThunk => ()
      case other                 => fail(s"Expected a stuck exact-result mismatch, got $other (${other.getClass})")
    }
  }

  test("multi-constructor proofs cannot choose a data branch") {
    intercept[PropEliminationRestricted] {
      TestSupport.check(
        """
          |inductive Nat : Type
          | | zero : Nat
          |
          |inductive EitherProof : Prop
          | | left : EitherProof
          | | right : EitherProof
          |
          |def bad (p: EitherProof): Nat := {
          |  match p returning Nat with
          |  | EitherProof.left => Nat.zero
          |  | EitherProof.right => Nat.zero
          |}
          |""".stripMargin
      )
    }
  }

  test("proof eta applications reconstruct an Eq result before data elimination") {
    val result = TestSupport.eval(
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |inductive Eq (A: Type) indices (left: A)(right: A) : Prop
        | | refl (value: A) : Eq(A, value, value)
        |
        |def reflFn (n: Nat): Eq(Nat, n, n) := Eq.refl(n)
        |def inspect (p: Eq(Nat, Nat.zero, Nat.zero)): Nat := {
        |  match p returning Nat with
        |  | Eq.refl _ => Nat.zero
        |}
        |{ inspect(reflFn(Nat.zero)) }
        |""".stripMargin
    )
    assertEquals(PrettyPrinter.print(result), "Nat.zero()")
  }

  test("returned proof functions reconstruct their instantiated Eq result") {
    val result = TestSupport.eval(
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |inductive Eq (A: Type) indices (left: A)(right: A) : Prop
        | | refl (value: A) : Eq(A, value, value)
        |
        |def makeRefl (_: Nat): (n: Nat) -> Eq(Nat, n, n) :=
        |  fun (n: Nat): Eq(Nat, n, n) => Eq.refl(n)
        |def inspect (p: Eq(Nat, Nat.zero, Nat.zero)): Nat := {
        |  match p returning Nat with
        |  | Eq.refl _ => Nat.zero
        |}
        |{ inspect(makeRefl(Nat.zero)(Nat.zero)) }
        |""".stripMargin
    )
    assertEquals(PrettyPrinter.print(result), "Nat.zero()")
  }

  test("axiom, transparent, opaque, let, and match proof boundaries canonicalize") {
    val result = TestSupport.eval(
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |inductive Eq (A: Type) indices (left: A)(right: A) : Prop
        | | refl (value: A) : Eq(A, value, value)
        |
        |axiom ax : Eq(Nat, Nat.zero, Nat.zero)
        |def transparent : Eq(Nat, Nat.zero, Nat.zero) := Eq.refl(Nat.zero)
        |opaque def hidden : Eq(Nat, Nat.zero, Nat.zero) := Eq.refl(Nat.zero)
        |def normalize (p: Eq(Nat, Nat.zero, Nat.zero)): Eq(Nat, Nat.zero, Nat.zero) := {
        |  match p returning Eq(Nat, Nat.zero, Nat.zero) with
        |  | Eq.refl n => Eq.refl(n)
        |}
        |def inspect (p: Eq(Nat, Nat.zero, Nat.zero)): Nat := {
        |  match p returning Nat with
        |  | Eq.refl _ => Nat.zero
        |}
        |{
        |  let a : Eq(Nat, Nat.zero, Nat.zero) := ax
        |  let b : Eq(Nat, Nat.zero, Nat.zero) := transparent
        |  let c : Eq(Nat, Nat.zero, Nat.zero) := hidden
        |  inspect(normalize(a))
        |}
        |""".stripMargin
    )
    assertEquals(PrettyPrinter.print(result), "Nat.zero()")
  }

  test("recursive proof constructors reconstruct two finite layers") {
    val result = TestSupport.eval(
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |inductive Loop : Prop
        | | mk (next: Loop) : Loop
        |
        |axiom loop : Loop
        |def inspect (p: Loop): Nat := {
        |  match p returning Nat with
        |  | Loop.mk next => {
        |      match next returning Nat with
        |      | Loop.mk _ => Nat.zero
        |    }
        |}
        |{ inspect(loop) }
        |""".stripMargin
    )
    assertEquals(PrettyPrinter.print(result), "Nat.zero()")
  }

  test("dependent Pi proof fields remain applicable after shallow recovery") {
    val result = TestSupport.eval(
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |inductive True : Prop
        | | intro : True
        |
        |inductive DependentProof : Prop
        | | mk (h: (n: Nat) -> True) : DependentProof
        |
        |axiom recovered : DependentProof
        |def observe (p: DependentProof): Nat := {
        |  match p returning Nat with
        |  | DependentProof.mk h => {
        |      match h(Nat.zero) returning Nat with
        |      | True.intro => Nat.zero
        |    }
        |}
        |{ observe(recovered) }
        |""".stripMargin
    )
    assertEquals(PrettyPrinter.print(result), "Nat.zero()")
  }

  test("one reachable constructor does not bypass certified large elimination") {
    intercept[PropEliminationRestricted] {
      TestSupport.check(
        """
          |inductive Nat : Type
          | | zero : Nat
          | | succ (pred: Nat) : Nat
          |
          |inductive Indexed indices (n: Nat) : Prop
          | | zero : Indexed(Nat.zero)
          | | succ (pred: Nat) : Indexed(Nat.succ(pred))
          |
          |def bad (h: Indexed(Nat.zero)): Nat := {
          |  match h returning Nat with
          |  | Indexed.zero => Nat.zero
          |}
          |""".stripMargin
      )
    }
  }

  test("judgment-blocked proof matches wake on either endpoint and re-stick on the remainder") {
    val (env, _) = TestSupport.check(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (pred: Peano) : Peano
        |
        |inductive Eq2 indices (left: Peano)(right: Peano) : Prop
        | | refl (value: Peano) : Eq2(value, value)
        |
        |def probe (a: Peano)(b: Peano)(h: Eq2(a, b)): Peano := {
        |  match h returning Peano with
        |  | Eq2.refl v => v
        |}
        |""".stripMargin
    )
    val peano = env("Peano")
    val a = FreshVar.freshVar("a", peano)
    val b = FreshVar.freshVar("b", peano)
    val proposition = Interpreter.evalApply(env("Eq2"), Vector(a, b))
    val h = Value.canonicalizeProof(Value.VProof(proposition))
    val thunk = Interpreter.evalApply(env("probe"), Vector(a, b, h)).asInstanceOf[Value.NeutralThunk]
    assertEquals(thunk.blockedOn, DepSet(a.id, b.id))

    val firedA = Interpreter.resolveInEqStore(thunk, EqStore.empty.allow(DepSet(a.id)).addLink(a.id, b))
    val firedB = Interpreter.resolveInEqStore(thunk, EqStore.empty.allow(DepSet(b.id)).addLink(b.id, a))
    assert(ValueEquivalence.defEq(firedA, b))
    assert(ValueEquivalence.defEq(firedB, a))

    val c = FreshVar.freshVar("c", peano)
    val restuck = Interpreter
      .resolveInEqStore(thunk, EqStore.empty.allow(DepSet(a.id)).addLink(a.id, c))
      .asInstanceOf[Value.NeutralThunk]
    assertEquals(restuck.blockedOn, DepSet(b.id, c.id))
    assert(!restuck.blockedOn.contains(a.id))
  }

  test("generic-universe match neutrals wake when their type collapses to Prop") {
    val (env, _) = TestSupport.check(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (pred: Peano) : Peano
        |
        |inductive PolyUnit (u: Level) indices (n: Peano) : Sort(u)
        | | mk : PolyUnit(u, Peano.zero)
        |
        |axiom makerType (u: Level): (n: Peano) -> PolyUnit(u, Peano.zero)
        |def probe (u: Level)(x: PolyUnit(u, Peano.zero)): Peano := {
        |  match x returning Peano with
        |  | PolyUnit.mk => Peano.zero
        |}
        |""".stripMargin
    )
    val u = FreshVar.freshVar("u", Value.LevelTpe)
    val zero = env("Peano.zero")
    val family = Interpreter.evalApply(env("PolyUnit"), Vector(u, zero))
    val x = Value.VConst("x", Value.Symbol, family)
    val thunk = Interpreter.evalApply(env("probe"), Vector(u, x)).asInstanceOf[Value.NeutralThunk]
    assertEquals(thunk.blockedOn, DepSet(u.id))
    val solved = EqStore.empty.allow(DepSet(u.id)).addLink(u.id, Value.Level.zero)
    assertEquals(PrettyPrinter.print(Interpreter.resolveInEqStore(thunk, solved)), "Peano.zero()")

    val maker = Interpreter.evalApply(env("makerType"), Vector(u))
    val blockedHead = FreshVar.freshVar("blockedHead", maker.tpe)
    val blocked = Value.VApp(blockedHead, Vector(zero), family, DepSet(blockedHead.id))
    val blockedThunk = Interpreter.evalApply(env("probe"), Vector(u, blocked)).asInstanceOf[Value.NeutralThunk]
    assertEquals(blockedThunk.blockedOn, DepSet(blockedHead.id, u.id))
    assertEquals(PrettyPrinter.print(Interpreter.resolveInEqStore(blockedThunk, solved)), "Peano.zero()")
  }
}
