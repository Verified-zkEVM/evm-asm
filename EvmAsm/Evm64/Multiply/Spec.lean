/-
  EvmAsm.Evm64.Multiply.Spec

  Stack-level 256-bit EVM MUL spec using evmWordIs.
  Wraps the limb-level evm_mul_spec with EvmWord abstraction.
-/

import EvmAsm.Evm64.Multiply.LimbSpec
import EvmAsm.Evm64.EvmWordMul
import EvmAsm.Evm64.Stack

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

/-- Stack-level 256-bit EVM MUL: operates on two EvmWords via evmWordIs.
    63 instructions total. Pops 2 stack words (A at sp, B at sp+32),
    writes (A * B) mod 2^256 to sp+32..sp+56, advances sp by 32. -/
theorem evm_mul_stack_spec (sp base : Addr)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (hvalid : ValidMemRange sp 8) :
    let a0 := a.getLimb 0; let a1 := a.getLimb 1
    let a2 := a.getLimb 2; let a3 := a.getLimb 3
    let b0 := b.getLimb 0; let b1 := b.getLimb 1
    let b2 := b.getLimb 2; let b3 := b.getLimb 3
    -- Col0 intermediates
    let c0_r0 := a0 * b0
    let c0_hi_a0b0 := rv64_mulhu a0 b0
    let c0_lo_a1b0 := a1 * b0
    let c0_hi_a1b0 := rv64_mulhu a1 b0
    let c0_r1 := c0_hi_a0b0 + c0_lo_a1b0
    let c0_c1 := if BitVec.ult c0_r1 c0_lo_a1b0 then (1 : Word) else 0
    let c0_lo_a2b0 := a2 * b0
    let c0_hi_a2b0 := rv64_mulhu a2 b0
    let c0_r2 := c0_hi_a1b0 + c0_c1 + c0_lo_a2b0
    let c0_c2 := if BitVec.ult c0_r2 c0_lo_a2b0 then (1 : Word) else 0
    let c0_r3p := c0_hi_a2b0 + c0_c2 + a3 * b0
    -- Col1 intermediates
    let c1_lo := a0 * b1
    let c1_hi := rv64_mulhu a0 b1
    let c1_r1 := c0_r1 + c1_lo
    let c1_c1 := if BitVec.ult c1_r1 c1_lo then (1 : Word) else 0
    let c1_rc := c1_hi + c1_c1
    let c1_r2a := c0_r2 + c1_rc
    let c1_cr1 := if BitVec.ult c1_r2a c1_rc then (1 : Word) else 0
    let c1_lo2 := a1 * b1
    let c1_hi2 := rv64_mulhu a1 b1
    let c1_r2 := c1_r2a + c1_lo2
    let c1_cr2 := if BitVec.ult c1_r2 c1_lo2 then (1 : Word) else 0
    let c1_rc2 := c1_hi2 + c1_cr2
    let c1_r3p := c1_cr1 + c1_rc2 + a2 * b1 + c0_r3p
    -- Col2 intermediates
    let c2_lo := a0 * b2
    let c2_hi := rv64_mulhu a0 b2
    let c2_r2 := c1_r2 + c2_lo
    let c2_c := if BitVec.ult c2_r2 c2_lo then (1 : Word) else 0
    let c2_rc := c2_hi + c2_c + a1 * b2
    let c2_r3 := c1_r3p + c2_rc
    -- Col3
    let r3_final := c2_r3 + a0 * b3
    let code := evm_mul_code base
    cpsTriple base (base + 252) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ b3) ** (.x6 ↦ᵣ a0 * b3) ** (.x7 ↦ᵣ a1 * b2) **
       (.x10 ↦ᵣ r3_final) ** (.x11 ↦ᵣ c2_r2) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a * b)) := by
  sorry

end EvmAsm.Rv64
