/-
  EvmAsm.Evm64.Add.Spec

  Full 256-bit EVM ADD spec composed from per-limb specs.
  30 instructions total (5 + 3×8 + 1 ADDI).
-/

-- `Add.LimbSpec → Add.Program → Stack → SpAddr`.
import EvmAsm.Evm64.Add.LimbSpec
import EvmAsm.Evm64.EvmWordArith.Arithmetic
import EvmAsm.Rv64.Tactics.XSimp

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CodeReq for the 256-bit EVM ADD operation.
    30 instructions = 120 bytes. 4 per-limb ADD blocks + ADDI sp adjustment. -/
abbrev evm_add_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_add

/-- Full 256-bit EVM ADD: composes 4 per-limb ADD specs + ADDI sp adjustment.
    30 instructions total. Pops 2 stack words (A at sp, B at sp+32),
    writes A + B to sp+32..sp+56, advances sp by 32.
    Carry propagates through limbs via x5. -/
theorem evm_add_spec (sp : Word) (base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (v7 v6 v5 v11 : Word) :
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    let carry3 := carry3a ||| carry3b
    let code := evm_add_code base
    cpsTriple base (base + 120) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) ** (.x5 ↦ᵣ carry3) ** (.x11 ↦ᵣ carry3a) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ sum0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) ** ((sp + 56) ↦ₘ result3)) := by
  intro sum0 carry0 psum1 carry1a result1 carry1b carry1 psum2 carry2a result2 carry2b carry2 psum3 carry3a result3 carry3b carry3
  have L0 := add_limb0_spec 0 32 sp a0 b0 v7 v6 v5 base
  have L1 := add_limb_carry_spec 8 40 sp a1 b1 sum0 b0 carry0 v11 (base + 20)
  have L2 := add_limb_carry_spec 16 48 sp a2 b2 result1 carry1b carry1 carry1a (base + 52)
  have L3 := add_limb_carry_spec 24 56 sp a3 b3 result2 carry2b carry2 carry2a (base + 84)
  have Laddi := addi_spec_gen_same .x12 sp 32 (base + 116) (by nofun)
  runBlock L0 L1 L2 L3 Laddi

-- ============================================================================
-- Stack-level ADD spec
-- ============================================================================

/-- Stack-level 256-bit EVM ADD: operates on two EvmWords via evmWordIs. -/
theorem evm_add_stack_spec (sp base : Word)
    (a b : EvmWord) (v7 v6 v5 v11 : Word) :
    let a0 := a.getLimbN 0; let b0 := b.getLimbN 0
    let a1 := a.getLimbN 1; let b1 := b.getLimbN 1
    let a2 := a.getLimbN 2; let b2 := b.getLimbN 2
    let a3 := a.getLimbN 3; let b3 := b.getLimbN 3
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    let carry3 := carry3a ||| carry3b
    let code := evm_add_code base
    cpsTriple base (base + 120) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) **
       (.x5 ↦ᵣ carry3) ** (.x11 ↦ᵣ carry3a) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a + b)) := by
  intro a0 b0 a1 b1 a2 b2 a3 b3 sum0 carry0 psum1 carry1a result1 carry1b carry1 psum2 carry2a result2 carry2b carry2 psum3 carry3a result3 carry3b carry3
  have h_main := evm_add_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v7 v6 v5 v11
  -- Get the carry chain correctness
  have ⟨h0, h1, h2, h3⟩ := EvmWord.add_carry_chain_correct a b
  exact cpsTriple_weaken
    (fun h hp => by
      simp only [evmWordIs] at hp
      rw [spAddr32_8, spAddr32_16, spAddr32_24] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs]
      rw [spAddr32_8, spAddr32_16, spAddr32_24]
      simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
                 EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3] at h0 h1 h2 h3
      rw [h0, h1, h2, h3]
      xperm_hyp hq)
    h_main

end EvmAsm.Evm64
