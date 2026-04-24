/-
  EvmAsm.Evm64.Lt.Spec

  Full 256-bit EVM LT spec composed from per-limb specs.
  26 instructions total (3 + 3×6 + 5 store).
-/

import EvmAsm.Evm64.Lt.Program
import EvmAsm.Evm64.Compare.LimbSpec
import EvmAsm.Evm64.EvmWordArith.Comparison
import EvmAsm.Evm64.SpAddr

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CodeReq for the 256-bit EVM LT operation.
    26 instructions = 104 bytes. Borrow chain across 4 limbs + store. -/
abbrev evm_lt_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_lt

/-- Full 256-bit EVM LT: LT(a, b) = 1 iff a < b (unsigned).
    Borrow chain across 4 limbs, then store result.
    Pops 2 stack words (A at sp, B at sp+32),
    writes result to sp+32..sp+56, advances sp by 32.
    26 instructions = 104 bytes total. -/
theorem evm_lt_spec (sp : Word) (base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (v7 v6 v5 v11 : Word) :
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult a3 b3 then (1 : Word) else 0
    let temp3 := a3 - b3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let borrow3 := borrow3a ||| borrow3b
    let code := evm_lt_code base
    cpsTriple base (base + 104) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ temp3) ** (.x6 ↦ᵣ borrow3b) **
       (.x5 ↦ᵣ borrow3) ** (.x11 ↦ᵣ borrow3a) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ borrow3) ** ((sp + 40) ↦ₘ 0) ** ((sp + 48) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0)) := by
  intro borrow0 borrow1a temp1 borrow1b borrow1 borrow2a temp2 borrow2b borrow2 borrow3a temp3 borrow3b borrow3
  -- Per-limb borrow specs
  have L0 := lt_limb0_spec 0 32 sp a0 b0 v7 v6 v5 base
  have L1 := lt_limb_carry_spec 8 40 sp a1 b1 a0 b0 borrow0 v11 (base + 12)
  have L2 := lt_limb_carry_spec 16 48 sp a2 b2 temp1 borrow1b borrow1 borrow1a (base + 36)
  have L3 := lt_limb_carry_spec 24 56 sp a3 b3 temp2 borrow2b borrow2 borrow2a (base + 60)
  -- Store phase
  have A := addi_spec_gen_same .x12 sp 32 (base + 84) (by nofun)
  simp only [signExtend12_32] at A
  have S0 := sd_spec_gen .x12 .x5 (sp + 32) borrow3 b0 0 (base + 88)
  have S1 := sd_x0_spec_gen .x12 (sp + 32) b1 8 (base + 92)
  have S2 := sd_x0_spec_gen .x12 (sp + 32) b2 16 (base + 96)
  have S3 := sd_x0_spec_gen .x12 (sp + 32) b3 24 (base + 100)
  runBlock L0 L1 L2 L3 A S0 S1 S2 S3

-- ============================================================================
-- Stack-level LT spec
-- ============================================================================

/-- Stack-level 256-bit EVM LT: operates on two EvmWords via evmWordIs. -/
theorem evm_lt_stack_spec (sp base : Word)
    (a b : EvmWord) (v7 v6 v5 v11 : Word) :
    let a0 := a.getLimbN 0; let b0 := b.getLimbN 0
    let a1 := a.getLimbN 1; let b1 := b.getLimbN 1
    let a2 := a.getLimbN 2; let b2 := b.getLimbN 2
    let a3 := a.getLimbN 3; let b3 := b.getLimbN 3
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult a3 b3 then (1 : Word) else 0
    let temp3 := a3 - b3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let borrow3 := borrow3a ||| borrow3b
    let code := evm_lt_code base
    cpsTriple base (base + 104) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ temp3) ** (.x6 ↦ᵣ borrow3b) **
       (.x5 ↦ᵣ borrow3) ** (.x11 ↦ᵣ borrow3a) **
       evmWordIs sp a ** evmWordIs (sp + 32) (if BitVec.ult a b then 1 else 0)) := by
  intro a0 b0 a1 b1 a2 b2 a3 b3 borrow0 borrow1a temp1 borrow1b borrow1 borrow2a temp2 borrow2b borrow2 borrow3a temp3 borrow3b borrow3
  have h_main := evm_lt_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v7 v6 v5 v11
  exact cpsTriple_weaken
    (fun h hp => by
      simp only [evmWordIs] at hp
      rw [spAddr32_8, spAddr32_16, spAddr32_24] at hp
      xperm_hyp hp)
    (fun h hq => by
      unfold evmWordIs
      simp only [EvmWord.getLimbN_ite, EvmWord.getLimbN_zero,
                 EvmWord.getLimbN_one_zero, EvmWord.getLimbN_one_one,
                 EvmWord.getLimbN_one_two, EvmWord.getLimbN_one_three,
                 ite_self,
                 ← EvmWord.lt_borrow_chain_correct]
      simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
                 EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]
      rw [spAddr32_8, spAddr32_16, spAddr32_24]
      xperm_hyp hq)
    h_main

end EvmAsm.Evm64
