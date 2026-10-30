package com.raccoonlang

import com.raccoonlang.Value._

/**
 * Declarations present in every environment, beneath any prelude. The kernel owns `Sort`, `Lin`, Bool, Nat, List, Char
 * and String, and the resource-protocol declarations: `List.Perm`, the `Protocol` families, the opaque `Supply`, `Inst`
 * and `Tok`, and the primitives (`ProtocolSource`). NatNormalForm implements Nat arithmetic, truncated subtraction,
 * comparisons, and division and remainder natively; Nat successors are always compact. `packed.Words` implements List
 * append and length natively; `packed.Strings` builds string literals and interns closed characters. Preludes and
 * programs cannot redeclare these names, so every value of type Nat, Bool, List, Char or String belongs to these
 * families, and code may recognise their constructors by name.
 */
private[raccoonlang] object Kernel {
  val NatName = "Nat"
  val ZeroName = "Nat.zero"
  val SuccName = "Nat.succ"
  val ListNilName = "List.nil"
  val ListConsName = "List.cons"
  val CharMkName = "Char.mk"
  val StringMkName = "String.mk"
  val StringDataName = "String.data"

  private val Source =
    """def Sort (l: Level): Type := builtin
      |
      |def Lin (l: Level): Type := builtin
      |
      |def Univ (k: Kind)(l: Level): Type := builtin
      |
      |namespace Kind {
      |  def join (a: Kind)(b: Kind): Kind := builtin
      |}
      |
      |inductive Bool : Type
      | | false : Bool
      | | true : Bool
      |
      |inductive Nat : Type
      | | zero : Nat
      | | succ (_: Nat) : Nat
      |
      |namespace Nat {
      |  def add (a: Nat)(b: Nat): Nat := builtin
      |  def mul (a: Nat)(b: Nat): Nat := builtin
      |  def pow (a: Nat)(b: Nat): Nat := builtin
      |  def sub (a: Nat)(b: Nat): Nat := builtin
      |  def pred (n: Nat): Nat := builtin
      |  def isZero (n: Nat): Bool := builtin
      |  def beq (a: Nat)(b: Nat): Bool := builtin
      |  def ble (a: Nat)(b: Nat): Bool := builtin
      |  def div (a: Nat)(b: Nat): Nat := builtin
      |  def mod (a: Nat)(b: Nat): Nat := builtin
      |}
      |
      |inductive List (A: Univ($k, $u)) : Univ(k, u)
      | | nil {A: Univ($k, $u)} : List(A)
      | | cons (head: $A in Univ($k, $u))(tail: List(A)) : List(A)
      |
      |namespace List {
      |  def append (xs: List($A))(ys: List(A)): List(A) := builtin
      |  def length (xs: List($A)): Nat := builtin
      |}
      |
      |inductive Char : Type
      | | mk (val: Nat) : Char
      |
      |inductive String : Type
      | | mk (data: List(Char)) : String
      |""".stripMargin

  /**
   * Resource protocols: permutations, protocol records, reachability and validity, and the types of instances and their
   * tokens. The primitives' types name these, so they live beneath every prelude and cannot be redeclared. They are
   * evaluated over the core declarations, whose natives their types call.
   *
   * `Supply`, `Inst` and `Tok` are opaque builtins (`Builtins.Opaque`): symbols without constructors, so no term builds
   * or matches a supply or a token. `Toks`, `Observed` and `Fresh` are linear inductives; `Observed` and `Fresh` are
   * records, with selectors and structure eta (`StructEta`).
   *
   * Every family and opaque builtin here takes a protocol as a `Proto`: structure eta makes a variable `P` convert with
   * `Proto.mk(P.Atom, P.Step)`, positivity accepts a field type that projects a parameter, and the size check charges a
   * `Proto` by its fields, an atom type and a relation into `Prop`, which cost nothing. So the linear families are in
   * `Lin(Level.zero)`, like `Tok` and `Supply`.
   */
  private val ProtocolSource =
    """namespace List {
      |  inductive Perm (A: Sort($u)) indices (xs: List(A))(ys: List(A)) : Prop
      |   | nil {A: Sort($u)} : Perm(A, List.nil(A), List.nil(A))
      |   | cons {A: Sort($u)} (x: A)(xs: List(A))(ys: List(A))(p: Perm(A, xs, ys))
      |       : Perm(A, List.cons(x, xs), List.cons(x, ys))
      |   | swap {A: Sort($u)} (x: A)(y: A)(xs: List(A))
      |       : Perm(A, List.cons(y, List.cons(x, xs)), List.cons(x, List.cons(y, xs)))
      |   | trans {A: Sort($u)} (xs: List(A))(ys: List(A))(zs: List(A))(p: Perm(A, xs, ys))(q: Perm(A, ys, zs))
      |       : Perm(A, xs, zs)
      |}
      |
      |namespace Protocol {
      |  inductive Proto : Sort(Level.one)
      |   | mk (Atom: Type)(Step: (consumed: List(Atom)) -> (produced: List(Atom)) -> Prop) : Proto
      |
      |  inductive Reach (P: Proto)(init: List(P.Atom)) indices (C: List(P.Atom)) : Prop
      |   | initial {P: Proto}{init: List(P.Atom)} : Reach(P, init, init)
      |   | step {P: Proto}{init: List(P.Atom)} (A: List(P.Atom))(B: List(P.Atom))(frame: List(P.Atom))(h: (P.Step(A, B)))
      |       (prev: Reach(P, init, List.append(A, frame))) : Reach(P, init, List.append(B, frame))
      |   | perm {P: Proto}{init: List(P.Atom)} (C: List(P.Atom))(D: List(P.Atom))(prev: Reach(P, init, C))
      |       (p: List.Perm(P.Atom, C, D)) : Reach(P, init, D)
      |
      |  inductive Valid (P: Proto)(init: List(P.Atom)) indices (C: List(P.Atom)) : Prop
      |   | mk {P: Proto}{init: List(P.Atom)} (C: List(P.Atom))(rest: List(P.Atom))
      |       (r: Reach(P, init, List.append(C, rest))) : Valid(P, init, C)
      |
      |  def Supply : Lin(Level.zero) := builtin
      |
      |  def Inst (P: Proto)(init: List(P.Atom)): Type := builtin
      |
      |  def Tok (P: Proto)(init: List(P.Atom))(s: Inst(P, init))(a: P.Atom): Lin(Level.zero) := builtin
      |
      |  inductive Toks (P: Proto)(init: List(P.Atom))(s: Inst(P, init)) indices (C: List(P.Atom)) : Lin(Level.zero)
      |   | nil {P: Proto}{init: List(P.Atom)}{s: Inst(P, init)} : Toks(P, init, s, List.nil(P.Atom))
      |   | cons {P: Proto}{init: List(P.Atom)}{s: Inst(P, init)} (a: P.Atom)(t: Tok(P, init, s, a))(C: List(P.Atom))
      |       (rest: Toks(P, init, s, C)) : Toks(P, init, s, List.cons(a, C))
      |
      |  inductive Observed (P: Proto)(init: List(P.Atom))(s: Inst(P, init))(C: List(P.Atom)) : Lin(Level.zero)
      |   | mk {P: Proto}{init: List(P.Atom)}{s: Inst(P, init)}{C: List(P.Atom)} (toks: Toks(P, init, s, C))
      |       (valid: Valid(P, init, C)) : Observed(P, init, s, C)
      |
      |  inductive Fresh (P: Proto)(init: List(P.Atom)) : Lin(Level.zero)
      |   | mk {P: Proto}{init: List(P.Atom)} (next: Supply)(s: Inst(P, init))(toks: Toks(P, init, s, init)) : Fresh(P, init)
      |
      |  def new (P: Proto)(init: List(P.Atom))(sup: Supply): Fresh(P, init) := builtin
      |
      |  def step (P: Proto)(init: List(P.Atom))(s: Inst(P, init))(A: List(P.Atom))(B: List(P.Atom))(h: (P.Step(A, B)))
      |      (toks: Toks(P, init, s, A)) : Toks(P, init, s, B) := builtin
      |
      |  def observe (P: Proto)(init: List(P.Atom))(s: Inst(P, init))(C: List(P.Atom))(toks: Toks(P, init, s, C))
      |      : Observed(P, init, s, C) := builtin
      |}
      |""".stripMargin

  private def parse(source: String, part: String): SurfaceAst.Program =
    LanguageParser.parseProgram(source) match {
      case Success(program, _, _)      => program
      case Failure(_, curIdx, message) => throw WTF(s"Failed to parse kernel $part declarations at $curIdx: $message")
    }

  // Strict, so the elaborator can read them while the kernel environments are being initialized without taking this
  // object's lock.
  val surface: SurfaceAst.Program = parse(Source, "core")
  val protocolSurface: SurfaceAst.Program = parse(ProtocolSource, "protocol")

  /**
   * The core declarations, evaluated once. The core natives and the core accessors below read this stage, so evaluating
   * a later kernel declaration that calls a native never re-enters an environment under construction.
   */
  lazy val coreEnv: Env =
    Elaborator.kernelDecls.foldLeft(Interpreter.primitiveEnv) { case (env, decl) =>
      Interpreter.evalDecl(decl, env)
    }

  /** Every kernel declaration, evaluated once, so all environments share the same kernel values. */
  lazy val env: Env =
    Elaborator.kernelProtocolDecls.foldLeft(coreEnv) { case (env, decl) =>
      Interpreter.evalDecl(decl, env)
    }

  private def constructor(stage: Env, name: String): ConstructorHead = stage(name).asInstanceOf[ConstructorHead]
  private def native(name: String): VLam = coreEnv(name).asInstanceOf[VLam]

  lazy val natType: Value = coreEnv("Nat")
  lazy val zero: ConstructorHead = constructor(coreEnv, ZeroName)
  lazy val succ: ConstructorHead = constructor(coreEnv, SuccName)
  lazy val zeroValue: Value = VCtor(zero, Vector.empty, natType)

  lazy val charType: Value = coreEnv("Char")
  lazy val charMk: ConstructorHead = constructor(coreEnv, CharMkName)
  lazy val stringType: Value = coreEnv("String")
  lazy val stringMk: ConstructorHead = constructor(coreEnv, StringMkName)
  lazy val listCons: ConstructorHead = constructor(coreEnv, ListConsName)
  lazy val charListType: Value = Interpreter.evalApply(coreEnv("List"), Vector(charType))
  lazy val charListNil: Value = Interpreter.evalApply(coreEnv(ListNilName), Vector(charType))

  /** Whether `value` is the kernel `List` 's `nil`, of any element type. */
  def isListNil(value: Value): Boolean =
    value match {
      case VCtor(head, _, _) => head.name == ListNilName
      case _                 => false
    }

  lazy val boolType: Value = coreEnv("Bool")
  lazy val falseValue: Value = VCtor(constructor(coreEnv, "Bool.false"), Vector.empty, boolType)
  lazy val trueValue: Value = VCtor(constructor(coreEnv, "Bool.true"), Vector.empty, boolType)

  // Native functions, applied to retain a stuck result as an application that resumes once a dependency is solved.
  lazy val sub: VLam = native("Nat.sub")
  lazy val isZero: VLam = native("Nat.isZero")
  lazy val beq: VLam = native("Nat.beq")
  lazy val ble: VLam = native("Nat.ble")
  lazy val div: VLam = native("Nat.div")
  lazy val mod: VLam = native("Nat.mod")
  lazy val append: VLam = native("List.append")
  lazy val length: VLam = native("List.length")

  // The protocol families and constructors whose values the primitives' natives build (`ProtocolPrimitives`). They
  // read the full kernel environment; no kernel declaration applies a primitive, so evaluating `env` never runs a
  // native that reads them.
  lazy val supplyType: Value = env("Protocol.Supply")
  lazy val instFamily: Value = env("Protocol.Inst")
  lazy val tokFamily: Value = env("Protocol.Tok")
  lazy val validFamily: Value = env("Protocol.Valid")
  lazy val toksFamily: Value = env("Protocol.Toks")
  lazy val toksNil: ConstructorHead = constructor(env, "Protocol.Toks.nil")
  lazy val toksCons: ConstructorHead = constructor(env, "Protocol.Toks.cons")
  lazy val observedFamily: Value = env("Protocol.Observed")
  lazy val observedMk: ConstructorHead = constructor(env, "Protocol.Observed.mk")
  lazy val freshFamily: Value = env("Protocol.Fresh")
  lazy val freshMk: ConstructorHead = constructor(env, "Protocol.Fresh.mk")
}
