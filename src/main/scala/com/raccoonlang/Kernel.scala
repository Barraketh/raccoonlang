package com.raccoonlang

import com.raccoonlang.Value._

/**
 * Declarations present in every environment, beneath any prelude. The kernel owns `Sort`, Bool, Nat, List, Char and
 * String. NatNormalForm implements Nat arithmetic, truncated subtraction, and comparisons natively; Nat successors are
 * always compact. `packed.Words` implements List append and length natively; `packed.Strings` builds string literals
 * and interns closed characters. Preludes and programs cannot redeclare these names, so every value of type Nat, Bool,
 * List, Char or String belongs to these families, and code may recognise their constructors by name.
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
      |}
      |
      |inductive List (A: Sort($u)) : Sort(u)
      | | nil {A: Sort($u)} : List(A)
      | | cons (head: $A in Sort($u))(tail: List(A)) : List(A)
      |
      |namespace List {
      |  def append (xs: List($A))(ys: List(A)): List(A) := builtin
      |  def length (xs: List($A)): Nat := builtin
      |}
      |
      |struct Char : Type
      | | mk (val: Nat) : Char
      |
      |struct String : Type
      | | mk (data: List(Char)) : String
      |""".stripMargin

  // Strict, so the elaborator can read it while Kernel.env is being initialized without taking this object's lock.
  val surface: SurfaceAst.Program =
    LanguageParser.parseProgram(Source) match {
      case Success(program, _, _)      => program
      case Failure(_, curIdx, message) => throw WTF(s"Failed to parse kernel declarations at $curIdx: $message")
    }

  /** Evaluated once, so all environments share the same kernel values. */
  lazy val env: Env =
    Elaborator.kernelDecls.foldLeft(Interpreter.primitiveEnv) { case (env, decl) =>
      Interpreter.evalDecl(decl, env)
    }

  private def constructor(name: String): ConstructorHead = env(name).asInstanceOf[ConstructorHead]
  private def native(name: String): VLam = env(name).asInstanceOf[VLam]

  lazy val natType: Value = env("Nat")
  lazy val zero: ConstructorHead = constructor(ZeroName)
  lazy val succ: ConstructorHead = constructor(SuccName)
  lazy val zeroValue: Value = VCtor(zero, Vector.empty, natType)

  lazy val charType: Value = env("Char")
  lazy val charMk: ConstructorHead = constructor(CharMkName)
  lazy val stringType: Value = env("String")
  lazy val stringMk: ConstructorHead = constructor(StringMkName)
  lazy val listCons: ConstructorHead = constructor(ListConsName)
  lazy val charListType: Value = Interpreter.evalApply(env("List"), Vector(charType))
  lazy val charListNil: Value = Interpreter.evalApply(env(ListNilName), Vector(charType))

  /** Whether `value` is the kernel `List` 's `nil`, of any element type. */
  def isListNil(value: Value): Boolean =
    value match {
      case VCtor(head, _, _) => head.name == ListNilName
      case _                 => false
    }

  lazy val boolType: Value = env("Bool")
  lazy val falseValue: Value = VCtor(constructor("Bool.false"), Vector.empty, boolType)
  lazy val trueValue: Value = VCtor(constructor("Bool.true"), Vector.empty, boolType)

  // Native functions, applied to retain a stuck result as an application that resumes once a dependency is solved.
  lazy val sub: VLam = native("Nat.sub")
  lazy val isZero: VLam = native("Nat.isZero")
  lazy val beq: VLam = native("Nat.beq")
  lazy val ble: VLam = native("Nat.ble")
  lazy val append: VLam = native("List.append")
  lazy val length: VLam = native("List.length")
}
