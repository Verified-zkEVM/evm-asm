/-
  EvmAsm.Evm64.Slt.Spec

  Full 256-bit EVM SLT (Signed Less Than) spec composed from per-limb specs.
  25 instructions total (3 MSB check + 2 signed path OR 15 borrow chain + 5 store).

  Algorithm: Compare MSB limbs (limb 3) with signed RV64 SLT instruction.
  If MSB limbs equal, use unsigned borrow chain on limbs 0-2.
-/

-- `Slt.Program → Stack → SpAddr`.
import EvmAsm.Evm64.Slt.Program
import EvmAsm.Evm64.Compare.LimbSpec
import EvmAsm.Evm64.EvmWordArith.Comparison
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.ControlFlow

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se13_12 se21_64)

/-- CodeReq for the 256-bit EVM SLT operation.
    25 instructions = 100 bytes. MSB signed compare + lower borrow chain + store. -/
abbrev evm_slt_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_slt

/-- Full 256-bit EVM SLT: SLT(a, b) = 1 iff a <s b (signed).
    If MSB limbs differ, uses RV64 SLT (signed comparison).
    If MSB limbs equal, uses unsigned borrow chain on lower 3 limbs.
    Pops 2 stack words (A at sp, B at sp+32),
    writes result to sp+32..sp+56, advances sp by 32.
    25 instructions = 100 bytes total. -/
theorem evm_slt_spec (sp : Word) (base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (v7 v6 v5 v11 : Word) :
    -- Lower 3 limbs borrow chain (used when MSB limbs equal)
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    -- Signed comparison of MSB limbs
    let sltMsb := if BitVec.slt a3 b3 then (1 : Word) else 0
    -- Result: signed LT
    let result := if a3 = b3 then borrow2 else sltMsb
    let code := evm_slt_code base
    cpsTriple base (base + 100) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) **
       (.x7 ↦ᵣ (if a3 = b3 then temp2 else a3)) **
       (.x6 ↦ᵣ (if a3 = b3 then borrow2b else b3)) **
       (.x5 ↦ᵣ result) **
       (.x11 ↦ᵣ (if a3 = b3 then borrow2a else v11)) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ result) ** ((sp + 40) ↦ₘ 0) ** ((sp + 48) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0)) := by
  intro borrow0 borrow1a temp1 borrow1b borrow1 borrow2a temp2 borrow2b borrow2 sltMsb
  -- Don't intro result; let simp inline it via if_pos/if_neg
  by_cases h : a3 = b3
  · -- Case: MSB limbs equal → BEQ taken, lower compare path
    subst h
    simp only [ite_true]
    -- MSB load phase
    have M := slt_msb_load_spec 24 56 sp a3 a3 v7 v6 base
    -- BEQ taken (a3 = a3)
    have B := beq_eq_spec .x7 .x6 (12 : BitVec 13) a3 (base + 8)
    simp only [se13_12] at B
    -- Lower limb borrow chain
    have L0 := lt_limb0_spec 0 32 sp a0 b0 a3 a3 v5 (base + 20)
    have L1 := lt_limb_carry_spec 8 40 sp a1 b1 a0 b0 borrow0 v11 (base + 32)
    have L2 := lt_limb_carry_spec 16 48 sp a2 b2 temp1 borrow1b borrow1 borrow1a (base + 56)
    -- Store phase
    have A := addi_spec_gen_same .x12 sp 32 (base + 80) (by nofun)
    simp only [signExtend12_32] at A
    have S0 := sd_spec_gen .x12 .x5 (sp + 32) borrow2 b0 0 (base + 84)
    have S1 := sd_x0_spec_gen .x12 (sp + 32) b1 8 (base + 88)
    have S2 := sd_x0_spec_gen .x12 (sp + 32) b2 16 (base + 92)
    have S3 := sd_x0_spec_gen .x12 (sp + 32) a3 24 (base + 96)
    runBlock M B L0 L1 L2 A S0 S1 S2 S3
  · -- Case: MSB limbs differ → BEQ not taken, SLT + JAL path
    simp only [if_neg h]
    -- MSB load phase
    have M := slt_msb_load_spec 24 56 sp a3 b3 v7 v6 base
    -- BEQ not taken (a3 ≠ b3)
    have B := beq_ne_spec .x7 .x6 (12 : BitVec 13) a3 b3 h (base + 8)
    -- SLT instruction
    have S := slt_spec_gen .x5 .x7 .x6 v5 a3 b3 (base + 12) (by nofun)
    -- JAL to store
    have J := jal_x0_spec_gen (64 : BitVec 21) (base + 16)
    simp only [se21_64] at J
    -- Store phase
    have A := addi_spec_gen_same .x12 sp 32 (base + 80) (by nofun)
    simp only [signExtend12_32] at A
    have S0 := sd_spec_gen .x12 .x5 (sp + 32) sltMsb b0 0 (base + 84)
    have S1 := sd_x0_spec_gen .x12 (sp + 32) b1 8 (base + 88)
    have S2 := sd_x0_spec_gen .x12 (sp + 32) b2 16 (base + 92)
    have S3 := sd_x0_spec_gen .x12 (sp + 32) b3 24 (base + 96)
    runBlock M B S J A S0 S1 S2 S3

-- ============================================================================
-- Stack-level SLT spec
-- ============================================================================

/-- Stack-level 256-bit EVM SLT: operates on two EvmWords via evmWordIs. -/
theorem evm_slt_stack_spec (sp base : Word)
    (a b : EvmWord) (v7 v6 v5 v11 : Word) :
    -- Lower 3 limbs borrow chain (used when MSB limbs equal)
    let borrow0 := if BitVec.ult (a.getLimbN 0) (b.getLimbN 0) then (1 : Word) else 0
    let borrow1a := if BitVec.ult (a.getLimbN 1) (b.getLimbN 1) then (1 : Word) else 0
    let temp1 := a.getLimbN 1 - b.getLimbN 1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult (a.getLimbN 2) (b.getLimbN 2) then (1 : Word) else 0
    let temp2 := a.getLimbN 2 - b.getLimbN 2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    -- Signed comparison of MSB limbs
    let sltMsb := if BitVec.slt (a.getLimbN 3) (b.getLimbN 3) then (1 : Word) else 0
    let result := if a.getLimbN 3 = b.getLimbN 3 then borrow2 else sltMsb
    let code := evm_slt_code base
    cpsTriple base (base + 100) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) **
       (.x7 ↦ᵣ (if a.getLimbN 3 = b.getLimbN 3 then temp2 else a.getLimbN 3)) **
       (.x6 ↦ᵣ (if a.getLimbN 3 = b.getLimbN 3 then borrow2b else b.getLimbN 3)) **
       (.x5 ↦ᵣ result) **
       (.x11 ↦ᵣ (if a.getLimbN 3 = b.getLimbN 3 then borrow2a else v11)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (if BitVec.slt a b then 1 else 0)) := by
  intro borrow0 borrow1a temp1 borrow1b borrow1 borrow2a temp2 borrow2b borrow2 sltMsb result
  have h_main := evm_slt_spec sp base
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
                 ← EvmWord.slt_result_correct]
      simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
                 EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]
      rw [spAddr32_8, spAddr32_16, spAddr32_24]
      xperm_hyp hq)
    h_main

end EvmAsm.Evm64
