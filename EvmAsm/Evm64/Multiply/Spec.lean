/-
  EvmAsm.Evm64.Multiply.Spec

  Full 256-bit EVM MUL spec composed from per-limb specs.
  63 instructions total (4 column blocks + ADDI).
-/

import EvmAsm.Evm64.Multiply.LimbSpec
import EvmAsm.Evm64.EvmWordArith

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Stack-level MUL spec
-- ============================================================================

/-- Stack-level 256-bit EVM MUL: operates on two EvmWords via evmWordIs.

    Note: MUL clobbers sp+16 and sp+24 (used as scratch for r3 accumulator),
    so the postcondition cannot claim evmWordIs sp a. Instead, sp+0 and sp+8
    are preserved, and sp+16/sp+24 contain intermediate values. -/
theorem evm_mul_stack_spec (sp base : Addr)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (hvalid : ValidMemRange sp 8) :
    let a0 := a.getLimb 0; let b0 := b.getLimb 0
    let a1 := a.getLimb 1; let b1 := b.getLimb 1
    let a2 := a.getLimb 2; let b2 := b.getLimb 2
    let a3 := a.getLimb 3; let b3 := b.getLimb 3
    -- Col0 intermediates
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
    let c1_hi := rv64_mulhu a0 b1
    let c1_r1 := c0_r1 + a0 * b1
    let c1_c1 := if BitVec.ult c1_r1 (a0 * b1) then (1 : Word) else 0
    let c1_rc := c1_hi + c1_c1
    let c1_r2a := c0_r2 + c1_rc
    let c1_cr1 := if BitVec.ult c1_r2a c1_rc then (1 : Word) else 0
    let c1_lo2 := a1 * b1
    let c1_hi2 := rv64_mulhu a1 b1
    let c1_r2 := c1_r2a + c1_lo2
    let c1_cr2 := if BitVec.ult c1_r2 c1_lo2 then (1 : Word) else 0
    let c1_rc2 := c1_hi2 + c1_cr2
    let c1_r3p := c1_cr1 + c1_rc2 + a2 * b1 + c0_r3p
    let code := evm_mul_code base
    cpsTriple base (base + 252) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ b3) ** (.x6 ↦ᵣ a0 * b3) ** (.x7 ↦ᵣ a1 * b2) **
       (.x10 ↦ᵣ (a * b).getLimb 3) ** (.x11 ↦ᵣ (a * b).getLimb 2) **
       -- sp+0, sp+8 preserved; sp+16, sp+24 clobbered
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ c1_r3p) ** ((sp + 24) ↦ₘ c0_r3p) **
       evmWordIs (sp + 32) (a * b)) := by
  intro a0 b0 a1 b1 a2 b2 a3 b3
  intro c0_hi_a0b0 c0_lo_a1b0 c0_hi_a1b0
  intro c0_r1 c0_c1 c0_lo_a2b0 c0_hi_a2b0
  intro c0_r2 c0_c2 c0_r3p
  intro c1_hi c1_r1 c1_c1
  intro c1_rc c1_r2a c1_cr1
  intro c1_lo2 c1_hi2 c1_r2 c1_cr2 c1_rc2 c1_r3p
  -- Get the schoolbook correctness lemma
  have ⟨h0, h1, h2, h3⟩ := EvmWord.mul_schoolbook_correct a b
  -- Get the limb-level MUL spec
  have h_main := evm_mul_spec sp base
    (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3)
    (b.getLimb 0) (b.getLimb 1) (b.getLimb 2) (b.getLimb 3)
    v5 v6 v7 v10 v11 hvalid
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      simp only [evmWordIs] at hp
      have : (sp : Addr) + 32 + 8 = sp + 40 := by bv_omega
      have : (sp : Addr) + 32 + 16 = sp + 48 := by bv_omega
      have : (sp : Addr) + 32 + 24 = sp + 56 := by bv_omega
      rw [‹sp + 32 + 8 = sp + 40›, ‹sp + 32 + 16 = sp + 48›, ‹sp + 32 + 24 = sp + 56›] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs]
      have : (sp : Addr) + 32 + 8 = sp + 40 := by bv_omega
      have : (sp : Addr) + 32 + 16 = sp + 48 := by bv_omega
      have : (sp : Addr) + 32 + 24 = sp + 56 := by bv_omega
      rw [‹sp + 32 + 8 = sp + 40›, ‹sp + 32 + 16 = sp + 48›, ‹sp + 32 + 24 = sp + 56›]
      rw [h0, h1, h2, h3]
      xperm_hyp hq)
    h_main

end EvmAsm.Rv64
