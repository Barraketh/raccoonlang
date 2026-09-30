package com.raccoonlang

/**
 * Spec §9's parse errors, each reached at every position its syntax can stand in: a definition's header, a lambda's
 * header, a function type's binder in a type and in a term position, and a constructor's field. An error inside a
 * binder is reported as itself, not swallowed into a generic failure of the enclosing type.
 *
 * A fragment marks where its error is reported with `@`, which the program does not contain.
 */
class ParseErrorTests extends munit.FunSuite {

  /** The positions a type stands in, each as the program that puts a type there. */
  private val typePositions: Vector[String => String] = Vector(
    t => s"def f (x: $t): Nat := 0\n", // a definition's parameter
    t => s"def f (n: Nat): $t := n\n", // a definition's result
    t => s"def f : Nat := (fun (x: $t): Nat => 0)(0)\n", // a lambda's parameter
    t => s"def f : Nat := (fun (n: Nat): $t => n)(0)\n", // a lambda's result
    t => s"def f (h: (x: $t) -> Nat): Nat := 0\n", // a function type's binder in a type position
    t => s"def f (h: {x: $t} -> Nat): Nat := 0\n", // its implicit binder
    t => s"def f : Type := (x: $t) -> Nat\n", // a function type's binder in a term position
    t => s"inductive W : Type\n | mk (x: $t) : W\n" // a constructor's field
  )

  /** The message and offset of the parse error `marked` reports where its `@` stands. */
  private def expectParseError(marked: String, message: String)(implicit loc: munit.Location): Unit = {
    val at = marked.indexOf('@')
    assert(at >= 0, s"no @ in $marked")
    val source = marked.patch(at, "", 1)
    LanguageParser.parseProgram(source) match {
      case Failure(_, curIdx, reported) =>
        assertEquals(reported, message, source)
        assertEquals(source.substring(curIdx), source.substring(at), source)
      case _: Success[_] => fail(s"expected a parse error in:\n$source")
    }
  }

  private def expectParses(source: String)(implicit loc: munit.Location): Unit =
    LanguageParser.parseProgram(source) match {
      case _: Success[_]                => ()
      case Failure(_, curIdx, reported) => fail(s"$reported at ${source.substring(curIdx)} in:\n$source")
    }

  private def everywhere(fragment: String, message: String)(implicit loc: munit.Location): Unit =
    typePositions.foreach(program => expectParseError(program(fragment), message))

  test("each position parses a well-formed sort and function type") {
    Vector("Type", "Sort { level = Level.one, kind = Kind.unr }", "{ kind = Kind.unr } Nat -> Nat").foreach { t =>
      typePositions.foreach(program => expectParses(program(t)))
    }
  }

  test("a sort's field list is nonempty and names each known field once") {
    everywhere("Sort @{}", "Empty field list")
    everywhere("Type @{}", "Empty field list")
    everywhere("Sort { level = Level.one, @size = 1 }", "Unknown field size")
    everywhere("Type { kind = Kind.unr, @kind = Kind.unr }", "Repeated field kind")
  }

  test("Sort requires its level, bare or applied, and Type and Prop fix theirs") {
    everywhere("@Sort", "Sort requires a level field")
    everywhere("@Sort(Level.one)", "Sort requires a level field")
    everywhere("@Sort { kind = Kind.unr }", "Sort requires a level field")
    everywhere("Type { @level = Level.one }", "Misplaced field level: Type fixes the level")
    everywhere("Prop { kind = Kind.unr, @level = Level.zero }", "Misplaced field level: Prop fixes the level")
  }

  test("a function type's closure is a field list without a level, before the group's first domain") {
    everywhere("@{} Nat -> Nat", "Empty field list")
    everywhere("{ @level = Level.one } Nat -> Nat", "Misplaced field level: a closure has no level")
    everywhere("{ @size = 1 } Nat -> Nat", "Unknown field size")
    everywhere("{ kind = Kind.unr, @kind = Kind.unr } Nat -> Nat", "Repeated field kind")
    val misplaced = "A closure prefixes a whole function type; parenthesize a nested one"
    everywhere("Nat -> @{ kind = Kind.unr } Nat -> Nat", misplaced)
    everywhere("(n: Nat) -> @{ kind = Kind.unr } (m: Nat) -> Nat", misplaced)
    everywhere("@{ kind = Kind.unr } Nat", "A closure prefixes a function type")
  }

  test("a lambda's closure is a field list without a level") {
    def lambda(closure: String): String = s"def f : Nat := (fun $closure (x: Nat): Nat => x)(0)\n"

    expectParses(lambda("{ kind = Kind.unr }"))
    expectParseError(lambda("@{}"), "Empty field list")
    expectParseError(lambda("{ @level = Level.one }"), "Misplaced field level: a closure has no level")
    expectParseError(lambda("{ @size = 1 }"), "Unknown field size")
    expectParseError(lambda("{ scope = Lifetime.empty, @scope = Lifetime.empty }"), "Repeated field scope")
  }

  // A match stands only where a term does: a type's grammar has none, so a header, a binder or a field cannot hold one.
  test("a match without returning is a parse error in a definition's body and a lambda's") {
    val cases = " with\n | .zero => 0\n | .succ k => k\n"
    val positions = Vector(
      s"def f (n: Nat): Nat := match n@$cases",
      s"def f : Nat -> Nat := fun (n: Nat): Nat => match n@$cases",
      s"def f (n: Nat): Nat := {\n  let m := match n@$cases  m\n}\n"
    )
    positions.foreach(expectParseError(_, "Failed to parse returning clause"))
  }

  // `returning` continues the match header, as an arrow continues a function type.
  test("a match's returning clause may start the next line") {
    expectParses("def f (n: Nat): Nat := match n\n  returning Nat with\n | .zero => 0\n | .succ k => k\n")
    expectParses(
      "def f (n: Nat): Nat := match n\n  // the motive\n  returning Nat with\n | .zero => 0\n | .succ k => k\n"
    )
  }

  // Blank and comment lines may separate cases and constructors (LineLayoutTests), but each still ends its line.
  test("a case or constructor on another's line is a parse error where it stands") {
    val cases = Vector(
      "def f (n: Nat): Nat := match n returning Nat with@ | .zero => 0\n",
      "def f (n: Nat): Nat := match n returning Nat with\n  | .zero => 0@ | .succ k => k\n",
      "def f (n: Nat): Nat := {\n  let m := match n returning Nat with@ | .zero => 0\n  m\n}\n",
      "def f (n: Nat): Nat := {\n  match n returning Nat with\n  | .zero => 0\n  | .succ k => k@ }\n"
    )
    cases.foreach(expectParseError(_, "Failed to parse end of line"))
    val constructors = Vector(
      "inductive Color : Type@ | red : Color\n",
      "inductive Color : Type\n  | red : Color@ | green : Color\n",
      "struct Point : Type@ | mk (x: Nat) : Point\n"
    )
    constructors.foreach(expectParseError(_, "Failed to parse end of line"))
  }

  test("a destructuring has two or more components, and only a block's let destructures") {
    expectParses("def f (p: Prod(Nat, Nat)): Nat := {\n  let (a, _) := p\n  a\n}\n")
    expectParses(
      "def f : Nat := {\n  let ( e ,\n    (a, b) ) : Prod(Nat, Prod(Nat, Nat)) := Prod.mk(1, Prod.mk(2, 3))\n  e\n}\n"
    )
    val single = "A destructuring has two or more components"
    expectParseError("def f (p: Nat): Nat := {\n  let (@x) := p\n  x\n}\n", single)
    expectParseError("def f (p: Nat): Nat := {\n  let (e, (@x)) := p\n  x\n}\n", single)
    expectParseError("def f (p: Nat): Nat := {\n  let (@) := p\n  p\n}\n", "Failed to parse pattern")
    // A binder, a lambda's and a match case's pattern take no destructuring.
    expectParseError("def @f ((a, b): Prod(Nat, Nat)): Nat := a\n", "Failed to parse Sym(:)")
    expectParseError(
      "def f : Prod(Nat, Nat) -> Nat := fun @((a, b): Prod(Nat, Nat)): Nat => a\n",
      "Failed to parse Sym(:)"
    )
    expectParseError(
      "def f (p: Prod(Nat, Nat)): Nat := match p returning Nat with\n | Prod.mk@ (a, b) => a\n",
      "Failed to parse Sym(=>)"
    )
  }

  test("a parse failure names what was expected, never a parser object") {
    expectParseError("def f : Nat := 0\n@)\n", "Failed to parse end of input")
    expectParseError("def f (n: Nat): Nat := Nat.add(n@\n", "Failed to parse LayoutSymTight())")
  }
}
