package com.raccoonlang

/**
 * Sealed families (spec §7.1, §7.2): a sealed family exports its head, parameters, indices and classifier, but its
 * constructors and selectors only to its module, the file that declares it. Each rule is checked with the same
 * declarations once inside the module, appended to it, and once outside it, in an entry file that imports it.
 */
class SealingTests extends munit.FunSuite with TestSupport {
  import TestSupport.leaseModule

  /**
   * A sealed struct with a module-made value, an unsealed family indexed by it, and a module definition that forces an
   * implicit through the sealed constructor's field.
   */
  private def boxModule(sealing: String): String =
    s"""
       |${sealing}struct Box : Type
       | | mk (n: Nat) : Box
       |
       |def box (n: Nat): Box := Box.mk(n)
       |
       |inductive P indices (b: Box) : Type
       | | mk (b: Box) : P(b)
       |
       |def get {n: Nat}(p: P(box(n))): Nat := n
       |""".stripMargin

  private val sealedBox = boxModule("sealed ")

  /** The use is admitted inside the module and `SealedConstructor` outside it. */
  private def sealedUse(module: String, client: String, expected: SealedConstructor)(implicit
      loc: munit.Location
  ): Unit = {
    inside(module, client)
    assertEquals(expectOnly[SealedConstructor](outside(module, client)), expected)
  }

  test("a term naming a sealed constructor is SealedConstructor outside its module, applied or not") {
    val constructor = SealedConstructor("Box", Some("Box.mk"))
    sealedUse(sealedBox, "def x : Box := Box.mk(3)\n", constructor)
    sealedUse(sealedBox, "def x : Nat -> Box := Box.mk\n", constructor)
    // The name still resolves, through an open as anywhere, so the use reaches the diagnostic.
    sealedUse(sealedBox, "open Box\ndef x : Box := mk(3)\n", constructor)
    // The mutation is the seal alone.
    outside(boxModule(""), "def x : Box := Box.mk(3)\n")
  }

  test("a match on a value of a sealed family is SealedConstructor outside its module, a .short case included") {
    val matching = SealedConstructor("Box", None)
    sealedUse(sealedBox, "def x (b: Box): Nat := match b returning Nat with\n | Box.mk n => n\n", matching)
    sealedUse(sealedBox, "def x (b: Box): Nat := match b returning Nat with\n | .mk n => n\n", matching)
    outside(boxModule(""), "def x (b: Box): Nat := match b returning Nat with\n | .mk n => n\n")
  }

  test("selecting a field of a sealed family is SealedConstructor outside its module") {
    val selector = SealedConstructor("Box", Some("Box.n"))
    sealedUse(sealedBox, "def x (b: Box): Nat := b.n\n", selector)
    sealedUse(sealedBox, "def x (b: Box): Nat := Box.n(b)\n", selector)
    outside(boxModule(""), "def x (b: Box): Nat := b.n\n")
  }

  test("a module is a source, and a site in no source lies outside every module") {
    val seal = Some(Sealing.Seal("Box", SourceId.fresh()))
    assert(Sealing.accessible(seal, Span(0, 0, Some(seal.get.module))))
    assert(!Sealing.accessible(seal, Span(0, 0, Some(SourceId.fresh()))))
    assert(!Sealing.accessible(seal, Span(0, 0, None)))
    assert(Sealing.accessible(None, Span(0, 0, None)))
  }

  test("a family and its selectors are sealed to one module, the source the family was read from") {
    val program = parse(sealedBox)
    val seals = program.decls.map {
      case family: CoreAst.Decl.InductiveDecl => family.header.name -> family.seal
      case definition: CoreAst.Decl.ConstDecl => definition.name -> definition.sealedBy
      case other                              => fail(s"unexpected declaration $other")
    }
    val boxSeal = Some(Sealing.Seal("Box", program.decls.head.span.source.get))
    // The unsealed family and the module's own definitions carry none.
    assertEquals(seals, Vector("Box" -> boxSeal, "Box.n" -> boxSeal, "box" -> None, "P" -> None, "get" -> None))
  }

  test("outside its module a sealed family's head, its instances and the module's definitions stay usable") {
    val client =
      """
        |def pick (b: Box): Box := b
        |def same : Eq(Box, box(1), box(1)) := Eq.refl(box(1))
        |// The implicit is reconstructed as a sealed constructor application, which names it without writing it.
        |def idBox {b: Box}(p: P(b)): Box := b
        |def made : Box := idBox(P.mk(box(1)))
        |// The module's own implicit reads the sealed field wherever it is applied.
        |{ get(P.mk(box(4))) }
        |""".stripMargin
    assertEquals(outside(sealedBox, client).map(PrettyPrinter.print), Some("4"))
  }

  test("forcing an implicit through a sealed constructor's field compiles only inside its module") {
    val forcing = "def get2 {n: Nat}(p: P(box(n))): Nat := n\n"
    assertEquals(inside(sealedBox, forcing + "{ get2(P.mk(box(5))) }\n").map(PrettyPrinter.print), Some("5"))
    assertEquals(expectOnly[NonForcedImplicitParam](outside(sealedBox, forcing)), NonForcedImplicitParam("n"))
    outside(boxModule(""), forcing)
  }

  test("sealing restricts what a program writes, not what the checker knows about the family") {
    // Apartness of the sealed constructor's fields prunes the only branch, and the family's kind makes a Tok linear.
    outside(sealedBox, "def apart (h: Eq(Box, box(1), box(2))): Nat := match h returning Nat with\n")
    assertEquals(
      expectOnly[LinearUnused](outside(leaseModule, "def drop {l: Lifetime}(t: Tok(l)): Nat := 0\n")),
      LinearUnused("t")
    )
  }

  test("a sealed family has structure eta like any other, in its module and outside it") {
    // Every Box comes from Box.mk, since only the trusted prelude declares axioms (spec §7.1, §7.3), so a match on a
    // caller's Box reduces through eta, in the module and wherever its definitions are applied.
    val two = "def two (b: Box): Nat := match b returning Nat with\n | .mk n => 2\n\n"
    val opened = "def opened (b: Box): Eq(Nat, two(b), 2) := Eq.refl(2)\n"
    val eta = "def eta (b: Box): Eq(Box, b, Box.mk(b.n)) := Eq.refl(b)\n"
    typecheckDecls(sealedBox + two + opened + eta)
    outside(sealedBox + two, opened)
    // Outside the module eta still holds, but stating it names the sealed constructor.
    expectOnly[SealedConstructor](outside(sealedBox, eta))
  }

  test("sealed Lease and Tok are made only by their module, whose helpers any module may call") {
    val callers =
      """
        |def unscoped : Nat := withLease(fun (l: Lifetime)(h: Lease(l)): Nat => 0)
        |def burned : Nat := withLease(fun (l: Lifetime)(h: Lease(l)): Nat => burn(issue(h)))
        |{ Nat.add(unscoped, burned) }
        |""".stripMargin
    assertEquals(outside(leaseModule, callers).map(PrettyPrinter.print), Some("1"))
    val mint = "def mint {l: Lifetime}(h: Lease(l)): Nat := burn(Tok.mk(l))\n"
    sealedUse(leaseModule, mint, SealedConstructor("Tok", Some("Tok.mk")))
    val consume = "def eat {l: Lifetime}(t: Tok(l)): Nat := match t returning Nat with\n | .mk => 0\n"
    sealedUse(leaseModule, consume, SealedConstructor("Tok", None))
  }
}
