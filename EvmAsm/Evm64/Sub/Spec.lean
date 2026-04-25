/-
  EvmAsm.Evm64.Sub.Spec

  Full 256-bit EVM SUB spec composed from per-limb specs.
  30 instructions total (5 + 3×8 + 1 ADDI).
-/

-- `Sub.LimbSpec → Sub.Program → Stack → SpAddr`.
import EvmAsm.Evm64.Sub.LimbSpec
import EvmAsm.Evm64.EvmWordArith.Arithmetic
import EvmAsm.Rv64.Tactics.XSimp

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CodeReq for the 256-bit EVM SUB operation.
    30 instructions = 120 bytes. 4 per-limb SUB blocks + ADDI sp adjustment. -/
abbrev evm_sub_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_sub

/-- Full 256-bit EVM SUB: composes 4 per-limb SUB specs + ADDI sp adjustment.
    30 instructions total. Pops 2 stack words (A at sp, B at sp+32),
    writes A - B to sp+32..sp+56, advances sp by 32.
    Borrow propagates through limbs via x5. -/
theorem evm_sub_spec (sp : Word) (base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (v7 v6 v5 v11 : Word) :
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let diff0 := a0 - b0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let result1 := temp1 - borrow0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let result2 := temp2 - borrow1
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult a3 b3 then (1 : Word) else 0
    let temp3 := a3 - b3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let result3 := temp3 - borrow2
    let borrow3 := borrow3a ||| borrow3b
    let code := evm_sub_code base
    cpsTriple base (base + 120) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ borrow3b) ** (.x5 ↦ᵣ borrow3) ** (.x11 ↦ᵣ borrow3a) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ diff0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) ** ((sp + 56) ↦ₘ result3)) := by
  intro borrow0 diff0 borrow1a temp1 borrow1b result1 borrow1 borrow2a temp2 borrow2b result2 borrow2 borrow3a temp3 borrow3b result3 borrow3
  have L0 := sub_limb0_spec 0 32 sp a0 b0 v7 v6 v5 base
  have L1 := sub_limb_carry_spec 8 40 sp a1 b1 diff0 b0 borrow0 v11 (base + 20)
  have L2 := sub_limb_carry_spec 16 48 sp a2 b2 result1 borrow1b borrow1 borrow1a (base + 52)
  have L3 := sub_limb_carry_spec 24 56 sp a3 b3 result2 borrow2b borrow2 borrow2a (base + 84)
  have Laddi := addi_spec_gen_same .x12 sp 32 (base + 116) (by nofun)
  runBlock L0 L1 L2 L3 Laddi

-- ============================================================================
-- Stack-level SUB spec
-- ============================================================================

/-- Stack-level 256-bit EVM SUB: operates on two EvmWords via evmWordIs. -/
theorem evm_sub_stack_spec (sp base : Word)
    (a b : EvmWord) (v7 v6 v5 v11 : Word) :
    let a0 := a.getLimbN 0; let b0 := b.getLimbN 0
    let a1 := a.getLimbN 1; let b1 := b.getLimbN 1
    let a2 := a.getLimbN 2; let b2 := b.getLimbN 2
    let a3 := a.getLimbN 3; let b3 := b.getLimbN 3
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let _diff0 := a0 - b0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let _result1 := temp1 - borrow0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let _result2 := temp2 - borrow1
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult a3 b3 then (1 : Word) else 0
    let temp3 := a3 - b3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let result3 := temp3 - borrow2
    let borrow3 := borrow3a ||| borrow3b
    let code := evm_sub_code base
    cpsTriple base (base + 120) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ borrow3b) **
       (.x5 ↦ᵣ borrow3) ** (.x11 ↦ᵣ borrow3a) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a - b)) := by
  intro a0 b0 a1 b1 a2 b2 a3 b3 borrow0 diff0 borrow1a temp1 borrow1b result1 borrow1 borrow2a temp2 borrow2b result2 borrow2 borrow3a temp3 borrow3b result3 borrow3
  have h_main := evm_sub_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v7 v6 v5 v11
  -- Get the borrow chain correctness
  have ⟨h0, h1, h2, h3⟩ := EvmWord.sub_borrow_chain_correct a b
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
