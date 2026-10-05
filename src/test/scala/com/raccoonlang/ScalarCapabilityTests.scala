package com.raccoonlang

import com.raccoonlang.Value._
import java.nio.file.Paths

class ScalarCapabilityTests extends munit.FunSuite {
  private val env = Prelude.fromPath(Paths.get("src/test/resources/NativeScalarPrelude.rac")).checkedEnv

  test("only the exact validated native Nat lambda receives a scalar capability") {
    val expected = Vector(
      "Nat.add" -> Packed.ScalarNatKind.Add,
      "Nat.sub" -> Packed.ScalarNatKind.Sub,
      "Nat.mul" -> Packed.ScalarNatKind.Mul,
      "Nat.div" -> Packed.ScalarNatKind.Div,
      "Nat.mod" -> Packed.ScalarNatKind.Mod,
      "Nat.beq" -> Packed.ScalarNatKind.Beq,
      "Nat.ble" -> Packed.ScalarNatKind.Ble,
      "Nat.blt" -> Packed.ScalarNatKind.Blt
    )
    expected.foreach { case (name, kind) =>
      val lam = env(name).asInstanceOf[VLam]
      assertEquals(Packed.scalarNatCapability(lam, env).map(_.kind), Some(kind))
      assertEquals(Packed.scalarNatCapability(lam.copy(), env), None)
      assertEquals(Packed.scalarNatCapability(lam, env.copy(nativeLiterals = NativeLiteralState.empty)), None)
      assertEquals(Packed.withOpsDisabled(Packed.scalarNatCapability(lam, env)), None)
    }

    val other = env("Nat.pow").asInstanceOf[VLam]
    assertEquals(Packed.scalarNatCapability(other, env), None)

    val separateContext = Prelude.fromPath(Paths.get("src/test/resources/NativeScalarPrelude.rac")).checkedEnv
    val add = env("Nat.add").asInstanceOf[VLam]
    assertEquals(Packed.scalarNatCapability(add, separateContext), None)
    val lookalike = add.copy(
      body = LamBody.Native(
        (args, _) => args.head,
        Env.empty,
        isRawRecursive = false,
        scalarCapability = None,
        equation = None
      )
    )
    assertEquals(Packed.scalarNatCapability(lookalike, env), None)
  }
}
