package com.raccoonlang

/**
 * Kinds, lifetimes and three-field sorts (spec §2): `Kind` and `Lifetime` are second-class sort parameters bound only
 * at the binder sites of the §2.2 table, their expressions are normalized at birth (§2.3), a sort's kind and scope are
 * exact (§2.5, §2.6), forced like its level (§2.7), and refined by linking a lone variable (§6.2). Each rule has an
 * admitted program and the smallest mutation that reaches its diagnostic.
 */
class KindLifetimeTests extends munit.FunSuite with TestSupport {

  /**
   * A family scoped by its lifetime; one scoped by two, whose instances at swapped arguments share a sort and so fit
   * one `Eq`; one per kind.
   */
  private val families =
    """
      |inductive V (l: Lifetime) : Type { scope = l }
      | | mk : V(l)
      |
      |inductive P (l: Lifetime)(m: Lifetime) : Type { scope = union(l, m) }
      | | mk : P(l, m)
      |
      |inductive K (k: Kind) : Type
      | | mk : K(k)
      |""".stripMargin

  private def withFamilies(decls: String): String = families + "\n" + decls

  test("a declaration's header and a family parameter may bind a kind or a lifetime") {
    typecheckDecls("def f {k: Kind}{S: Lifetime}(A: Type { kind = k, scope = S })(x: A): A := x\n")
    typecheckDecls(
      "def f (k: Kind)(S: Lifetime): Sort { level = succ(one), scope = S } := Type { kind = k, scope = S }\n"
    )
    typecheckDecls(
      "inductive Box {k: Kind}{S: Lifetime}(A: Type { kind = k, scope = S }) : Type { scope = S }\n | mk : Box(A)\n"
    )
  }

  test("a family index cannot bind a kind or a lifetime") {
    def program(index: String, sort: String, result: String): String =
      s"inductive Box $index : $sort\n | mk : Box($result)\n"

    typecheckDecls(program("(l: Lifetime)", "Type { scope = l }", "l"))
    expectOnly[NotAType](typecheckDecls(program("indices (l: Lifetime)", "Type", "Lifetime.empty")))
    expectOnly[NotAType](typecheckDecls(program("indices (k: Kind)", "Type", "Kind.unr")))
  }

  test("a constructor field cannot bind a kind or a lifetime") {
    def program(field: String): String = s"inductive Holder : Type\n | mk ($field) : Holder\n"

    typecheckDecls(program("n: Nat"))
    expectOnly[NotAType](typecheckDecls(program("l: Lifetime")))
    expectOnly[NotAType](typecheckDecls(program("k: Kind")))
  }

  test("a function type may bind a lifetime but not a kind") {
    def program(domain: String): String = s"def apply (f: ($domain) -> Nat): Nat := 0\n"

    typecheckDecls(program("l: Lifetime"))
    expectOnly[NotAType](typecheckDecls(program("k: Kind")))
  }

  test("a lambda may bind a lifetime but not a kind") {
    def program(binder: String, arg: String): String =
      withFamilies(
        s"def use : Nat := {\n  let f := fun ($binder)(h: K(Kind.unr)): Nat => 0\n  f($arg, K.mk(Kind.unr))\n}\n"
      )

    typecheckDecls(program("l: Lifetime", "Lifetime.empty"))
    expectOnly[NotAType](typecheckDecls(program("k: Kind", "Kind.unr")))
  }

  test("Kind and Lifetime are not types") {
    def program(body: String): String = s"def f (A: Type)(x: A): Nat := $body\n"

    typecheckDecls(program("List.length(List.cons(x, List.nil(A)))"))
    expectOnly[NotAType](typecheckDecls(program("List.length(List.nil(Lifetime))")))
    expectOnly[NotAType](typecheckDecls(program("{ let k : Kind := Kind.lin\n 0 }")))
    expectOnly[NotAType](typecheckDecls("def k : Kind := Kind.lin\n"))
    expectOnly[NotAType](typecheckDecls("def join (a: Kind)(b: Kind) : Kind := Kind.join(a, b)\n"))
    expectOnly[NotAType](typecheckDecls("{ Lifetime }\n"))
  }

  test("a kind or a lifetime stands only at a parameter position") {
    def program(body: String): String = withFamilies(s"def f (l: Lifetime)(h: V(l)): V(l) := $body\n")

    typecheckDecls(program("V.mk(Lifetime.union(l, l))"))
    expectOnly[NotAType](typecheckDecls(program("{ let m := l\n h }")))
    expectOnly[NotAType](typecheckDecls(program("{ let e := Lifetime.empty\n h }")))
    expectOnly[NotAType](
      typecheckDecls(withFamilies("def f (l: Lifetime): Nat := List.length(List.cons(l, List.nil(Nat)))\n"))
    )
  }

  test("a term of another type at a parameter position is a type mismatch") {
    def program(sort: String): String = s"def f (A: $sort)(x: A): A := x\n"

    typecheckDecls(program("Type { kind = unr, scope = empty }"))
    expectOnly[TypeMismatch](typecheckDecls(program("Type { scope = Nat.zero }")))
    expectOnly[TypeMismatch](typecheckDecls(program("Type { scope = Kind.lin }")))
    expectOnly[TypeMismatch](typecheckDecls(program("Type { kind = Lifetime.empty }")))
    expectOnly[TypeMismatch](typecheckDecls(program("Sort { level = Kind.unr }")))
    expectOnly[TypeMismatch](typecheckDecls(withFamilies("def w : Type := V(Kind.lin)\n")))
  }

  test("kind and lifetime forms are the language's, recognized only applied") {
    def program(scope: String): String = s"def f (a: Lifetime)(b: Lifetime)(A: Type { scope = $scope })(x: A): A := x\n"

    typecheckDecls(program("union(a, b)"))
    typecheckDecls(program("Lifetime.union(a, Lifetime.empty)"))
    assertEquals(
      expectOnly[ArityMismatch](typecheckDecls(program("union"))),
      ArityMismatch(2, 0, ArityMismatch.Arguments)
    )
    expectOnly[ArityMismatch](typecheckDecls(program("union(a)")))
  }

  // Normal forms are equal exactly when their sets are (spec §2.3), so each law holds by `Eq.refl`.
  test("union and join are normalized at birth") {
    val laws =
      """
        |def unionComm (a: Lifetime)(b: Lifetime):
        |    Eq(Type { scope = union(a, b) }, V(Lifetime.union(a, b)), V(Lifetime.union(b, a))) :=
        |  Eq.refl(V(Lifetime.union(a, b)))
        |def unionAssoc (a: Lifetime)(b: Lifetime)(c: Lifetime):
        |    Eq(Type { scope = union(a, union(b, c)) },
        |      V(Lifetime.union(a, Lifetime.union(b, c))), V(Lifetime.union(Lifetime.union(a, b), c))) :=
        |  Eq.refl(V(Lifetime.union(a, Lifetime.union(b, c))))
        |def unionIdem (a: Lifetime): Eq(Type { scope = a }, V(Lifetime.union(a, a)), V(a)) := Eq.refl(V(a))
        |def unionEmpty (a: Lifetime): Eq(Type { scope = a }, V(Lifetime.union(Lifetime.empty, a)), V(a)) :=
        |  Eq.refl(V(a))
        |def joinLin (k: Kind): Eq(Type, K(Kind.join(Kind.lin, k)), K(Kind.lin)) := Eq.refl(K(Kind.lin))
        |def joinUnr (k: Kind): Eq(Type, K(Kind.join(Kind.unr, k)), K(k)) := Eq.refl(K(k))
        |def joinComm (j: Kind)(k: Kind): Eq(Type, K(Kind.join(j, k)), K(Kind.join(k, j))) := Eq.refl(K(Kind.join(j, k)))
        |""".stripMargin

    typecheckDecls(withFamilies(laws))
    expectOnly[TypeMismatch](
      typecheckDecls(
        withFamilies(
          "def apart (a: Lifetime)(b: Lifetime): Eq(Type { scope = union(a, b) }, P(a, b), P(b, a)) := Eq.refl(P(a, b))\n"
        )
      )
    )
    expectOnly[TypeMismatch](
      typecheckDecls(withFamilies("def unrLin : Eq(Type, K(Kind.unr), K(Kind.lin)) := Eq.refl(K(Kind.unr))\n"))
    )
  }

  test("a sort's kind and scope are exact") {
    def program(result: String): String = withFamilies(s"def T (m: Lifetime) : $result := (h: V(m)) -> Nat\n")

    typecheckDecls(program("Type { scope = m }"))
    expectOnly[TypeMismatch](typecheckDecls(program("Type")))
    expectOnly[TypeMismatch](typecheckDecls(program("Type { kind = lin, scope = m }")))
  }

  test("a sort is at the scope of its own scope, and at Kind.unr") {
    def program(result: String): String =
      s"def s (k: Kind)(S: Lifetime) : $result := Type { kind = k, scope = S }\n"

    typecheckDecls(program("Sort { level = succ(one), scope = S }"))
    expectOnly[TypeMismatch](typecheckDecls(program("Sort { level = succ(one) }")))
    expectOnly[TypeMismatch](typecheckDecls(program("Sort { level = succ(one), kind = k, scope = S }")))
  }

  // spec §2.4: a function type's scope unites its domains' and codomain's, less the group's own lifetime variables.
  test("a function type's scope is less its own lifetime binders") {
    def program(ty: String): String = withFamilies(s"def T (m: Lifetime) : Type := $ty\n")

    typecheckDecls(program("(l: Lifetime) -> V(l) -> Nat"))
    typecheckDecls(program("(l: Lifetime)(h: V(l)) -> Nat"))
    expectOnly[TypeMismatch](typecheckDecls(program("(l: Lifetime) -> V(m) -> Nat")))
  }

  // A type variable's domain counts its sort's scope: a type carries up to the scope its sort states.
  test("a function type's scope counts its domains' and codomain's scopes") {
    def program(result: String, ty: String): String = withFamilies(s"def T (m: Lifetime) : $result := $ty\n")

    typecheckDecls(program("Sort { level = succ(one), scope = m }", "(A: Type { scope = m }) -> Nat"))
    typecheckDecls(program("Type { scope = m }", "(n: Nat) -> V(m)"))
    expectOnly[TypeMismatch](typecheckDecls(program("Sort { level = succ(one) }", "(A: Type { scope = m }) -> Nat")))
    expectOnly[TypeMismatch](typecheckDecls(program("Type", "(n: Nat) -> V(m)")))
  }

  // A kind or lifetime binder contributes no level, so a declaration binding only kinds and lifetimes is small, and
  // naming it unapplied is an ordinary reference; only a level binder makes a declaration's type large.
  test("kind and lifetime binders leave a declaration's type small") {
    def program(binder: String, sort: String): String =
      s"def keep {$binder}{A: $sort}(x: A): A := x\n\ndef use : Nat := {\n  let f := keep\n  0\n}\n"

    typecheckDecls(program("k: Kind", "Type { kind = k }"))
    typecheckDecls(program("S: Lifetime", "Type { scope = S }"))
    expectOnly[NotAType](typecheckDecls(program("u: Level", "Sort { level = u }")))
  }

  test("a kind or lifetime variable is forced only through a field that is exactly that variable") {
    typecheckDecls("def f {S: Lifetime}{A: Type { scope = S }}(x: A): A := x\n")
    typecheckDecls("def f {k: Kind}{A: Type { kind = k }}(x: A): A := x\n")
    typecheckDecls(withFamilies("def f {l: Lifetime}(h: V(l)): V(l) := h\n"))
    expectOnly[NonForcedImplicitParam](
      typecheckDecls("def f {S: Lifetime}(m: Lifetime)(A: Type { scope = union(S, m) })(x: A): A := x\n")
    )
    expectOnly[NonForcedImplicitParam](
      typecheckDecls("def f {k: Kind}(j: Kind)(A: Type { kind = join(k, j) })(x: A): A := x\n")
    )
  }

  test("forcing a lifetime solves it to the argument's scope") {
    val program =
      """
        |def keep {S: Lifetime}{A: Type { scope = S }}(x: A): A := x
        |def get (m: Lifetime)(h: V(m)): V(m) := keep(h)
        |{ get(Lifetime.empty, V.mk(Lifetime.empty)) }
        |""".stripMargin

    assertEquals(PrettyPrinter.print(runProgram(withFamilies(program))), "V.mk")
  }

  test("every other occurrence of a forced variable must equal its solution") {
    def program(second: String): String =
      withFamilies(
        s"""
           |def both {S: Lifetime}{A: Type { scope = S }}{B: Type { scope = S }}(x: A)(y: B): A := x
           |def use (l: Lifetime)(m: Lifetime)(a: V(l))(b: V(m)): V(l) := both(a, $second)
           |""".stripMargin
      )

    typecheckDecls(program("a"))
    expectOnly[TypeMismatch](typecheckDecls(program("b")))
  }

  test("a sort other than Kind.unr needs a level that is never zero") {
    def program(sort: String): String = s"def keep (u: Level)(k: Kind)(A: $sort)(x: A): A := x\n"

    typecheckDecls(program("Type { kind = k }"))
    typecheckDecls(program("Type { kind = lin }"))
    typecheckDecls(program("Sort { level = succ(u), kind = k }"))
    typecheckDecls(program("Sort { level = max(u, one), kind = k }"))
    val zero = expectOnly[LinearProp](typecheckDecls(program("Prop { kind = lin }")))
    assert(ErrorRendering.render(zero, None).contains("its level is zero"), ErrorRendering.render(zero, None))
    val variable = expectOnly[LinearProp](typecheckDecls(program("Sort { level = u, kind = k }")))
    assert(ErrorRendering.render(variable, None).contains("may be zero"), ErrorRendering.render(variable, None))
    expectOnly[LinearProp](typecheckDecls(program("Sort { level = u, kind = lin }")))
  }

  // spec §6.2: a variable alone on one side links, the later-bound to the earlier-bound when both are variables. A
  // lifetime equation arises only between instances that share a scope, so each one swaps P's arguments.
  test("refinement links a lone lifetime or kind variable") {
    val program =
      """
        |def cast (a: Lifetime)(b: Lifetime)(p: Eq(Type { scope = union(a, b) }, P(a, b), P(b, a)))(x: P(a, b))
        |    : P(b, a) :=
        |  match p returning P(b, a) with
        |  | .refl _ => x
        |
        |def toEmpty (a: Lifetime)(p: Eq(Type { scope = a }, P(a, Lifetime.empty), P(Lifetime.empty, a)))
        |    (x: P(a, Lifetime.empty)): P(Lifetime.empty, a) :=
        |  match p returning P(Lifetime.empty, a) with
        |  | .refl _ => x
        |
        |def toUnion (a: Lifetime)(b: Lifetime)(c: Lifetime)
        |    (p: Eq(Type { scope = union(c, union(a, b)) }, P(c, Lifetime.union(a, b)), P(Lifetime.union(a, b), c)))
        |    (x: P(c, Lifetime.union(a, b))): P(Lifetime.union(a, b), c) :=
        |  match p returning P(Lifetime.union(a, b), c) with
        |  | .refl _ => x
        |
        |def toLin (k: Kind)(p: Eq(Type, K(k), K(Kind.lin)))(x: K(k)): K(Kind.lin) :=
        |  match p returning K(Kind.lin) with
        |  | .refl _ => x
        |""".stripMargin

    typecheckDecls(withFamilies(program))
  }

  test("an equation between unions is stuck: no link, and its branch stays reachable") {
    def program(cases: String): String =
      withFamilies(
        s"""
           |def cast (a: Lifetime)(b: Lifetime)(c: Lifetime)(d: Lifetime)
           |    (p: Eq(Type { scope = union(union(a, b), union(c, d)) },
           |      P(Lifetime.union(a, b), Lifetime.union(c, d)), P(Lifetime.union(c, d), Lifetime.union(a, b))))
           |    (x: P(Lifetime.union(a, b), Lifetime.union(c, d))): P(Lifetime.union(a, b), Lifetime.union(c, d)) :=
           |  match p returning P(Lifetime.union(a, b), Lifetime.union(c, d)) with
           |  $cases
           |""".stripMargin
      )

    typecheckDecls(program("| .refl _ => x"))
    expectOnly[MissingCase](typecheckDecls(program("")))
    expectOnly[TypeMismatch](
      typecheckDecls(
        withFamilies(
          """
            |def cast (a: Lifetime)(b: Lifetime)(c: Lifetime)(d: Lifetime)
            |    (p: Eq(Type { scope = union(union(a, b), union(c, d)) },
            |      P(Lifetime.union(a, b), Lifetime.union(c, d)), P(Lifetime.union(c, d), Lifetime.union(a, b))))
            |    (x: P(Lifetime.union(a, b), Lifetime.union(c, d))): P(Lifetime.union(c, d), Lifetime.union(a, b)) :=
            |  match p returning P(Lifetime.union(c, d), Lifetime.union(a, b)) with
            |  | .refl _ => x
            |""".stripMargin
        )
      )
    )
  }

  // Siblings of a mutual block are each checked against their own sort, so one that holds another at a greater level or
  // kind is refused at that field. They share their parameters, and each names every lifetime parameter and no other
  // lifetime, so their scopes cannot differ: a sibling that omits one is refused at it.
  test("mutual siblings are bounded at each field and name their lifetime parameters") {
    def program(secondSort: String): String =
      s"""
         |mutual {
         |  inductive First (l: Lifetime) : Type { scope = l }
         |   | mk (second: Second(l)) : First(l)
         |
         |  inductive Second (l: Lifetime) : $secondSort
         |   | stop : Second(l)
         |}
         |""".stripMargin

    typecheckDecls(program("Type { scope = l }"))
    val level = expectOnly[InductiveUniverseTooSmall](typecheckDecls(program("Sort { level = succ(one), scope = l }")))
    assertEquals(level.where, "First.mk.second")
    val kind = expectOnly[KindExceeded](typecheckDecls(program("Type { kind = lin, scope = l }")))
    assert(PartialFunction.cond(kind.part) { case ContainedPart.Field("First.mk.second", _) => true }, kind.part)
    assertEquals(expectOnly[ScopeExceeded](typecheckDecls(program("Type"))).part, ContainedPart.LifetimeParameter("l"))
  }
}
