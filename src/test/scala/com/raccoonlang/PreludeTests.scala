package com.raccoonlang

class PreludeTests extends munit.FunSuite with TestSupport {

  test("basic Prelude data constructors are available") {
    val res =
      runProgram(
        """
          |{
          |  Prod.snd(Prod.mk(Nat.zero, Bool.true))
          |}
          |""".stripMargin
      )

    assertEquals(ctorName(res), "Bool.true")
  }

  test("Prelude logical convenience APIs typecheck and reduce") {
    typecheckDecls(
      """
        |def andProof : And(True, True) := And.intro(True.intro, True.intro)
        |def leftProof : True := And.left(andProof)
        |def rightProof : True := And.right(andProof)
        |
        |def trueOr : Or(True, False) := Or.inl(False, True.intro)
        |def fromOr : True := Or.elim(trueOr, True, fun (h: True): True => h, fun (h: False): True => falseElim(h, True))
        |
        |def trueIff : Iff(True, True) := Iff.intro(fun (h: True): True => h, fun (h: True): True => h)
        |def iffForward : True := Iff.mp(trueIff)(True.intro)
        |def iffBackward : True := Iff.mpr(trueIff)(True.intro)
        |def eqForward : True := Eq.mp(Eq.refl(True), True.intro)
        |def eqBackward : True := Eq.mpr(Eq.refl(True), True.intro)
        |
        |def impossibleNat (h: False): Nat := absurd(h, notFalse, Nat)
        |""".stripMargin
    )

    val res =
      runProgram(
        """
          |{
          |  id(Prod.fst(Prod.mk(Nat.zero, Bool.false)))
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(res), "Nat.zero")
  }

  test("Prelude propositions and dependent carriers typecheck") {
    typecheckDecls(
      """
        |def isTrue (b: Bool): Prop := True
        |def boolFamily (n: Nat): Type := Bool
        |
        |def andProof : And(True, True) := And.intro(True.intro, True.intro)
        |def iffProof : Iff(True, True) := Iff.intro(fun (h: True): True => h, fun (h: True): True => h)
        |def existsBool : Exists(Bool, isTrue) := Exists.intro(isTrue, Bool.true, True.intro)
        |def nonemptyNat : Nonempty(Nat) := Nonempty.intro(Nat.zero)
        |def subtypeBool : Subtype(Bool, isTrue) := Subtype.mk(isTrue, Bool.true, True.intro)
        |def sigmaNat : Sigma(Nat, boolFamily) := Sigma.mk(boolFamily, Nat.zero, Bool.true)
        |""".stripMargin
    )
  }

  test("Prelude equality helpers typecheck and reduce") {
    val res =
      runProgram(
        """
          |def idNat (n: Nat): Nat := n
          |def succNat (n: Nat): Nat := Nat.succ(n)
          |def natFamily (n: Nat): Type := Nat
          |def funEq : Eq((x: Nat) -> Nat, idNat, idNat) := Eq.refl(idNat)
          |
          |def symmProof : Eq(Nat, Nat.zero, Nat.zero) := Eq.symm(Eq.refl(Nat.zero))
          |def transProof : Eq(Nat, Nat.zero, Nat.zero) := Eq.trans(Eq.refl(Nat.zero), Eq.refl(Nat.zero))
          |def substValue : Nat := Eq.subst(Eq.refl(Nat.zero), Level.one, natFamily, Nat.zero)
          |def congrArgProof : Eq(Nat, Nat.succ(Nat.zero), Nat.succ(Nat.zero)) := congrArg(Eq.refl(Nat.zero), Nat, succNat)
          |
          |{
          |  congrFun(Nat, Nat, idNat, idNat, funEq, Nat.zero)
          |}
          |""".stripMargin
      )

    // The helper's canonical proof eta-lambda reconstructs the certified Eq constructor.
    res match {
      case Value.VCtor(head, _, _) => assertEquals(head.name, "Eq.refl")
      case other                   => fail(s"Expected a canonical Eq.refl proof, got $other")
    }
  }

  test("Prelude Decidable and conditionals reduce") {
    val decided =
      runProgram(
        """
          |{
          |  decide(trueDecidable)
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(decided), "Bool.true")

    val selected =
      runProgram(
        """
          |{
          |  ite(falseDecidable, Nat, Nat.succ(Nat.zero), Nat.zero)
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(selected), "Nat.zero")

    val negated =
      runProgram(
        """
          |{
          |  Decidable.toBool(Decidable.not(falseDecidable))
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(negated), "Bool.true")

    val byCases =
      runProgram(
        """
          |{
          |  Decidable.casesOn(falseDecidable, Nat, fun (h: Not(False)): Nat => Nat.zero, fun (h: False): Nat => falseElim(h, Nat))
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(byCases), "Nat.zero")
  }

  test("Prelude Bool and Nat APIs reduce") {
    val boolRes =
      runProgram(
        """
          |{
          |  Bool.or(Bool.false, Bool.not(Bool.false))
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(boolRes), "Bool.true")

    val natRes =
      runProgram(
        """
          |{
          |  Nat.mul(Nat.succ(Nat.zero), Nat.succ(Nat.succ(Nat.zero)))
          |}
          |""".stripMargin
      )
    assertEquals(PrettyPrinter.print(natRes), "2")

    val subRes =
      runProgram(
        """
          |{
          |  Nat.sub(Nat.succ(Nat.succ(Nat.zero)), Nat.succ(Nat.zero))
          |}
          |""".stripMargin
      )
    assertEquals(PrettyPrinter.print(subRes), "1")

    val beqRes =
      runProgram(
        """
          |{
          |  Nat.beq(Nat.succ(Nat.zero), Nat.succ(Nat.zero))
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(beqRes), "Bool.true")

    val bleRes =
      runProgram(
        """
          |{
          |  Nat.ble(Nat.succ(Nat.succ(Nat.zero)), Nat.succ(Nat.zero))
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(bleRes), "Bool.false")
  }

  test("Prelude Option, Sum, List, and Inhabited APIs typecheck and reduce") {
    typecheckDecls(
      """
        |def leftSum : Sum(Nat, Bool) := Sum.inl(Bool, Nat.zero)
        |def rightSum : Sum(Nat, Bool) := Sum.inr(Nat, Bool.true)
        |""".stripMargin
    )

    val optionRes =
      runProgram(
        """
          |{
          |  Option.getD(Option.some(Nat.zero), Nat.succ(Nat.zero))
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(optionRes), "Nat.zero")

    val optionBindRes =
      runProgram(
        """
          |{
          |  let x := Option.bind(Option.some(Nat.zero), Nat, fun (n: Nat): Option(Nat) => Option.some(Nat.succ(n)))
          |  Option.getD(x, Nat.zero)
          |}
          |""".stripMargin
      )
    assertEquals(PrettyPrinter.print(optionBindRes), "1")

    val sumElimRes =
      runProgram(
        """
          |{
          |  Sum.elim(Sum.inr(Nat, Bool.true), Nat, fun (n: Nat): Nat => n, fun (b: Bool): Nat => Bool.cond(b, Nat, Nat.succ(Nat.zero), Nat.zero))
          |}
          |""".stripMargin
      )
    assertEquals(PrettyPrinter.print(sumElimRes), "1")

    val listRes =
      runProgram(
        """
          |{
          |  List.length(List.append(List.cons(Nat.zero, List.nil(Nat)), List.cons(Nat.zero, List.nil(Nat))))
          |}
          |""".stripMargin
      )
    assertEquals(PrettyPrinter.print(listRes), "2")

    val listApiRes =
      runProgram(
        """
          |def count (acc: Nat)(n: Nat): Nat := Nat.succ(acc)
          |def isZeroNat (n: Nat): Bool := Nat.isZero(n)
          |
          |{
          |  let xs := List.cons(Nat.zero, List.cons(Nat.succ(Nat.zero), List.nil(Nat)))
          |  let foldedRight := List.foldr(xs, Nat, Nat.zero, fun (head: Nat)(tail: Nat): Nat => Nat.succ(tail))
          |  let foldedLeft := List.foldl(xs, Nat, Nat.zero, count)
          |  let kept := List.filter(xs, isZeroNat)
          |  let ok := Bool.and(List.any(xs, isZeroNat), Bool.not(List.all(xs, isZeroNat)))
          |  Bool.cond(Bool.and(Nat.beq(foldedRight, foldedLeft), ok), Nat, List.length(List.reverse(kept)), Nat.zero)
          |}
          |""".stripMargin
      )
    assertEquals(PrettyPrinter.print(listApiRes), "1")

    val inhabitedRes =
      runProgram(
        """
          |{
          |  natInhabited.default
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(inhabitedRes), "Nat.zero")
  }

  test("Prelude typeclass seed APIs derive and reduce") {
    typecheckDecls(
      """
        |def zeroEqZero : Decidable(Eq(Nat, Nat.zero, Nat.zero)) := decEq(natDecidableEq, Nat.zero, Nat.zero)
        |def falseNeTrue : Decidable(Eq(Bool, Bool.false, Bool.true)) := decEq(boolDecidableEq, Bool.false, Bool.true)
        |
        |def noZeroSucc (h: Eq(Nat, Nat.zero, Nat.succ(Nat.zero))): False := Nat.zeroNeSucc(Nat.zero, h)
        |def succInjects (h: Eq(Nat, Nat.succ(Nat.zero), Nat.succ(Nat.zero))): Eq(Nat, Nat.zero, Nat.zero) := Nat.succInj(h)
        |
        |def oneLeOne : Nat.le(Nat.succ(Nat.zero), Nat.succ(Nat.zero)) := Eq.refl(Bool.true)
        |def zeroLtOne : Nat.lt(Nat.zero, Nat.succ(Nat.zero)) := Eq.refl(Bool.true)
        |""".stripMargin
    )

    val natBeq =
      runProgram(
        """
          |{
          |  beq(natBEq, Nat.succ(Nat.zero), Nat.succ(Nat.zero))
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(natBeq), "Bool.true")

    val optionBeq =
      runProgram(
        """
          |{
          |  beq(optionBEq(natBEq), Option.some(Nat.zero), Option.some(Nat.zero))
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(optionBeq), "Bool.true")

    val listBeq =
      runProgram(
        """
          |{
          |  let xs := List.cons(Nat.zero, List.cons(Nat.succ(Nat.zero), List.nil(Nat)))
          |  beq(listBEq(natBEq), xs, xs)
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(listBeq), "Bool.true")

    val prodBeq =
      runProgram(
        """
          |{
          |  let p := Prod.mk(Nat.zero, Bool.true)
          |  beq(prodBEq(natBEq, boolBEq), p, p)
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(prodBeq), "Bool.true")

    val natDecEq =
      runProgram(
        """
          |{
          |  Decidable.toBool(decEq(natDecidableEq, Nat.succ(Nat.zero), Nat.zero))
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(natDecEq), "Bool.false")

    val unitDecEq =
      runProgram(
        """
          |{
          |  Decidable.toBool(decEq(unitDecidableEq, Unit.unit, Unit.unit))
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(unitDecEq), "Bool.true")

    val beqFromDecidableEq =
      runProgram(
        """
          |{
          |  let natEq := natDecidableEq
          |  beq(DecidableEq.toBEq(natEq), Nat.zero, Nat.succ(Nat.zero))
          |}
          |""".stripMargin
      )
    assertEquals(ctorName(beqFromDecidableEq), "Bool.false")
  }
}
