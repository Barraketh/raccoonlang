package com.raccoonlang

import com.raccoonlang.Value._

/**
 * Declarations present in every environment, beneath any prelude. The kernel owns Bool and Nat, and NatNormalForm
 * implements Nat arithmetic, truncated subtraction, and comparisons natively; Nat successors are always compact.
 * Preludes and programs cannot redeclare these names, so every value of type Nat or Bool belongs to these families.
 */
private[raccoonlang] object Kernel {
  val SuccName = "Nat.succ"

  private val Source =
    """inductive Bool : Type
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
  lazy val zero: ConstructorHead = constructor("Nat.zero")
  lazy val succ: ConstructorHead = constructor(SuccName)
  lazy val zeroValue: Value = VCtor(zero, Vector.empty, natType)

  lazy val boolType: Value = env("Bool")
  lazy val falseValue: Value = VCtor(constructor("Bool.false"), Vector.empty, boolType)
  lazy val trueValue: Value = VCtor(constructor("Bool.true"), Vector.empty, boolType)

  // Native functions, applied to retain a stuck result as an application that resumes once a dependency is solved.
  lazy val sub: VLam = native("Nat.sub")
  lazy val isZero: VLam = native("Nat.isZero")
  lazy val beq: VLam = native("Nat.beq")
  lazy val ble: VLam = native("Nat.ble")
}
