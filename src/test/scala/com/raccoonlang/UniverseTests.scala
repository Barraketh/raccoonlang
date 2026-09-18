package com.raccoonlang

import com.raccoonlang.CoreAst.Term
import com.raccoonlang.Value.{Level, VSort}

class UniverseTests extends munit.FunSuite {
  test("predicative Type and Sort hierarchy") {
    assertEquals(Value.TypeValue, VSort(Level.one))
    assertEquals(Value.TypeValue.tpe, VSort(Level.succ(Level.one)))
    assertEquals(Value.LevelTpe.tpe, Value.TypeValue)
    assert(Value.TypeValue.tpe != Value.TypeValue)
  }

  test("Type is not self-typed in a language let") {
    intercept[TypeMismatch] {
      TestSupport.check("{ let x : Type := Type\n x }")
    }
  }

  test("Level is a type and higher-sort ascription is exact") {
    assertEquals(TestSupport.eval("Level"), Value.LevelTpe)
    assertEquals(Value.LevelTpe.tpe, Value.TypeValue)
    val (_, result) = TestSupport.check(
      "{ let s : Sort(Level.succ(Level.succ(Level.zero))) := Type\n s }"
    )
    assert(result.nonEmpty)
    assertEquals(result.get.value, Value.TypeValue)
  }

  test("level operations normalize") {
    assertEquals(
      Interpreter.evalTerm(
        Term
          .App(Term.GlobalRef("Level.succ", Span(0, 1)), Vector(Term.GlobalRef("Level.zero", Span(0, 1))), Span(0, 1)),
        Interpreter.builtins
      ),
      Level.one
    )
    assertEquals(Level.max(Vector(Level.zero, Level.one)), Level.one)
    assertEquals(Level.imax(Level.const(3), Level.zero), Level.zero)
    assertEquals(Level.imax(Level.const(3), Level.one), Level.const(3))
  }

  test("explicit level-polymorphic identity checks") {
    val (_, result) = TestSupport.check("def id (u: Level)(A: Sort(u))(x: A): A := x\n")
    assert(result.isEmpty)
  }

  test("universe levels are not cumulative") {
    intercept[TypeMismatch] {
      TestSupport.check("def bad : Sort(Level.one) := Type")
    }
  }

  test("universe conversion is rejected in both directions") {
    intercept[TypeMismatch] {
      TestSupport.check(
        "opaque def up2 (u: Level)(A: Sort(u)): Sort(Level.succ(Level.succ(u))) := A"
      )
    }
    intercept[TypeMismatch] {
      TestSupport.check("def down (u: Level)(A: Sort(Level.succ(u))): Sort(u) := A")
    }
  }

  test("level equations solve only forced offsets") {
    val meta = Value.Var("u", 9001, Value.LevelTpe)
    val store = EqStore.empty.allow(DepSet(9001))
    val solved = ValueEquivalence.tryUnify(VSort(Level.mk(meta.id)), VSort(Level.one), store)
    assert(solved.isRight)
    assertEquals(solved.toOption.get.force(meta), Level.one)
    assert(ValueEquivalence.tryUnify(VSort(Level.addOffset(Level.mk(meta.id), 1)), VSort(Level.zero), store).isLeft)
    val imax = Level.imax(Level.mk(meta.id), Level.one)
    assert(ValueEquivalence.tryUnify(VSort(imax), VSort(Level.const(2)), store).isLeft)
  }

  test("level offset equations solve their unique variable") {
    val meta = Value.Var("u", 9002, Value.LevelTpe)
    val store = EqStore.empty.allow(DepSet(9002))
    val solved = ValueEquivalence
      .tryUnify(Level.addOffset(Level.mk(meta.id), 1), Level.const(2), store)
      .toOption
      .get
    assertEquals(solved.force(meta), Level.one)
  }

  test("level materialization rewrites solved atoms") {
    val meta = Value.Var("u", 9010, Value.LevelTpe)
    val store = EqStore.empty.allow(DepSet(meta.id)).addLink(meta.id, Level.one)
    assertEquals(ValueOps.materialize(VSort(Level.mk(meta.id)), store), Value.TypeValue)
  }

  test("unresolved imax remains distinct from ordinary max") {
    val u = Value.Level.mk(9101)
    val v = Value.Level.mk(9102)
    val imax = Level.imax(u, v)
    val ordinary = Level.max(Vector(u, v))
    assert(Level.containsIMax(imax))
    assert(imax.synDeps.contains(9101))
    assert(imax.synDeps.contains(9102))
    assertNotEquals(imax, ordinary)
    assert(!ValueEquivalence.defEq(imax, ordinary))
  }

  test("imax materialization simplifies when rhs solves to zero or one") {
    val imax = Level.imax(Level.mk(9111), Level.mk(9112))
    assertEquals(
      ValueOps.materialize(imax, EqStore(Map(9112 -> Level.zero), DepSet.empty)),
      Level.zero
    )
    assertEquals(
      ValueOps.materialize(imax, EqStore(Map(9112 -> Level.one), DepSet.empty)),
      Level.max(Vector(Level.mk(9111), Level.one))
    )
  }

  test("Level.of and Level constants reject invalid inputs") {
    assertEquals(Level.of(Map(9120 -> 3), 2), Level.of(Map(9120 -> 3), 0))
    intercept[IllegalArgumentException] { Level.of(Map(9120 -> -1), 0) }
    intercept[IllegalArgumentException] { Level.const(-1) }
  }

  test("Level.imax normalizes all basic forms") {
    val u = Level.mk(9131)
    val v = Level.mk(9132)
    assertEquals(Level.imax(u, Level.zero), Level.zero)
    assertEquals(Level.imax(Level.zero, v), v)
    assertEquals(Level.imax(Level.one, v), v)
    assertEquals(Level.imax(u, u), u)
    assertEquals(Level.imax(u, Level.succ(v)), Level.max(Vector(u, Level.succ(v))))
    val nested = Level.imax(u, Level.imax(v, Level.mk(9133)))
    assert(Level.containsIMax(nested))
    assert(nested.synDeps.contains(9131) && nested.synDeps.contains(9132))
  }

  test("Level.leq is conservative for imax and ordinary levels") {
    val u = Level.mk(9141)
    val v = Level.mk(9142)
    val imax = Level.imax(u, v)
    assert(Level.leq(v, imax))
    assert(Level.leq(imax, Level.max(Vector(u, v))))
    assert(!Level.leq(u, imax))
    assert(Level.leq(Level.const(3), Level.of(Map(9141 -> 5), 0)))
    assert(!Level.leq(Level.of(Map(9141 -> 5), 0), Level.const(7)))
    assert(Level.leq(Level.of(Map(9141 -> 2), 0), Level.of(Map(9141 -> 5), 0)))
    assert(!Level.leq(Level.of(Map(9141 -> 5), 0), Level.of(Map(9141 -> 2), 0)))
  }

  test("imax and successful Level.leq bounds agree on small assignments") {
    val uId = 9151
    val vId = 9152
    val u = Level.mk(uId)
    val v = Level.mk(vId)
    def eval(level: Level, assignment: Map[Int, Int]): Int = {
      val terms = level.terms.map { case (atom, offset) =>
        val base = atom match {
          case Level.ParamAtom(id) => assignment(id)
          case Level.IMaxAtom(lhs, rhs) =>
            val r = eval(rhs, assignment)
            if (r == 0) 0 else math.max(eval(lhs, assignment), r)
        }
        base + offset
      }
      (terms.iterator ++ Iterator.single(level.c)).max
    }
    val operands = Vector(Level.zero, Level.one, u, v, Level.succ(u), Level.max(Vector(u, v)), Level.imax(u, v))
    for {
      lhs <- operands
      rhs <- operands
      uv <- 0 to 2
      vv <- 0 to 2
    } {
      val assignment = Map(uId -> uv, vId -> vv)
      val normalized = Level.imax(lhs, rhs)
      val rhsValue = eval(rhs, assignment)
      val expected = if (rhsValue == 0) 0 else math.max(eval(lhs, assignment), rhsValue)
      assertEquals(eval(normalized, assignment), expected)
      if (Level.leq(lhs, rhs)) assert(eval(lhs, assignment) <= rhsValue)
    }
  }

  test("Pi classifiers use the universe of their codomain") {
    val value = TestSupport.eval("(A: Type) -> A")
    assert(value.tpe.isInstanceOf[VSort])
    assertEquals(value.tpe, VSort(Level.const(2)))
  }

  test("Sort's declared result type matches its native result at zero and one") {
    val sort = Interpreter.builtins("Sort").asInstanceOf[Value.VLam]
    Vector(Level.zero, Level.one).foreach { level =>
      val native = Interpreter.evalApply(sort, Vector(level))
      val declared = Interpreter.resultType(sort.tpe, Vector(level))
      assertEquals(declared, native.tpe)
    }
  }

  test("native builtins enforce Pi-group arity") {
    intercept[ArityMismatch] {
      Interpreter.evalApply(Interpreter.builtins("Level.succ"), Vector.empty)
    }
  }

  test("explicit level-polymorphic identity returns a small inductive value") {
    val (_, result) = TestSupport.check(
      "inductive Bool : Type\n | true : Bool\n | false : Bool\n\n" +
        "def id (u: Level)(A: Sort(u))(x: A): A := x\n" +
        "id(Level.one, Bool, Bool.true)"
    )
    assertEquals(PrettyPrinter.print(result.get.value), "Bool.true")
  }

  test("explicit polymorphic Pi classifiers preserve right-nested imax") {
    val (_, result) = TestSupport.check(
      "def piType (u: Level)(v: Level)(A: Sort(u))(B: Sort(v)): Sort(Level.imax(u, v)) := (x: A) -> B\n" +
        "def piType2 (u: Level)(v: Level)(w: Level)(A: Sort(u))(B: Sort(v))(C: Sort(w)): " +
        "Sort(Level.imax(u, Level.imax(v, w))) := (x: A) -> (y: B) -> C\n" +
        "piType"
    )
    assert(result.nonEmpty)
  }

  test("direct level unification solves forced offsets and rejects imax guesses") {
    val meta = Value.Var("u", 9161, Value.LevelTpe)
    val store = EqStore.empty.allow(DepSet(9161))
    val solved = ValueEquivalence.tryUnify(Level.mk(meta.id), Level.one, store).toOption.get
    assertEquals(solved.force(meta), Level.one)
    assert(ValueEquivalence.tryUnify(Level.addOffset(Level.mk(meta.id), 1), Level.zero, store).isLeft)
    assert(
      ValueEquivalence
        .tryUnify(
          Level.imax(Level.mk(meta.id), Level.one),
          Level.const(2),
          store
        )
        .isLeft
    )
  }
}
