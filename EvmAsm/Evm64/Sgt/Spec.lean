/-
  EvmAsm.Evm64.Sgt.Spec

  Full 256-bit EVM SGT (Signed Greater Than) spec composed from per-limb specs.
  SGT(a, b) = SLT(b, a): load b-limbs into x7, a-limbs into x6 (swapped).
  25 instructions total (3 MSB check + 2 signed path OR 15 borrow chain + 5 store).

  Algorithm: Compare MSB limbs (limb 3) with signed RV64 SLT on (b3, a3).
  If MSB limbs equal, use unsigned borrow chain on lower 3 limbs (b - a).
-/

-- `Sgt.Program → Stack → SpAddr`.
import EvmAsm.Evm64.Sgt.Program
import EvmAsm.Evm64.Compare.LimbSpec
import EvmAsm.Evm64.EvmWordArith.Comparison
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se13_12 se21_64)

/-- CodeReq for the 256-bit EVM SGT operation.
    25 instructions = 100 bytes. SGT(a, b) = SLT(b, a): swapped load order. -/
abbrev evm_sgt_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_sgt

/-- Full 256-bit EVM SGT: SGT(a, b) = 1 iff a >s b (signed).
    Computed as SLT(b, a): signed compare MSB limbs (b3 vs a3),
    if equal, unsigned borrow chain on lower 3 limbs (b - a).
    Pops 2 stack words (A at sp, B at sp+32),
    writes result to sp+32..sp+56, advances sp by 32.
    25 instructions = 100 bytes total. -/
theorem evm_sgt_spec_within (sp : Word) (base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (v7 v6 v5 v11 : Word) :
    -- Lower 3 limbs borrow chain: b - a direction (used when MSB limbs equal)
    let borrow0 := if BitVec.ult b0 a0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult b1 a1 then (1 : Word) else 0
    let temp1 := b1 - a1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult b2 a2 then (1 : Word) else 0
    let temp2 := b2 - a2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    -- Signed comparison of MSB limbs (swapped: b3 vs a3)
    let sgtMsb := if BitVec.slt b3 a3 then (1 : Word) else 0
    -- Result: signed GT
    let result := if b3 = a3 then borrow2 else sgtMsb
    let code := evm_sgt_code base
    cpsTripleWithin 25 base (base + 100) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) **
       (.x7 ↦ᵣ (if b3 = a3 then temp2 else b3)) **
       (.x6 ↦ᵣ (if b3 = a3 then borrow2b else a3)) **
       (.x5 ↦ᵣ result) **
       (.x11 ↦ᵣ (if b3 = a3 then borrow2a else v11)) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ result) ** ((sp + 40) ↦ₘ 0) ** ((sp + 48) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0)) := by
  intro borrow0 borrow1a temp1 borrow1b borrow1 borrow2a temp2 borrow2b borrow2 sgtMsb
  -- Don't intro result; let simp inline it via if_pos/if_neg
  by_cases h : b3 = a3
  · -- Case: MSB limbs equal → BEQ taken, lower compare path
    subst h
    simp only [ite_true]
    -- MSB load phase (swapped: 56 first, 24 second)
    have M := slt_msb_load_spec_within 56 24 sp b3 b3 v7 v6 base
    -- BEQ taken (b3 = b3)
    have B := beq_eq_spec_within .x7 .x6 (12 : BitVec 13) b3 (base + 8)
    simp only [se13_12] at B
    -- Lower limb borrow chain (swapped: b-limbs into x7, a-limbs into x6)
    have L0 := lt_limb0_spec_within 32 0 sp b0 a0 b3 b3 v5 (base + 20)
    have L1 := lt_limb_carry_spec_within 40 8 sp b1 a1 b0 a0 borrow0 v11 (base + 32)
    have L2 := lt_limb_carry_spec_within 48 16 sp b2 a2 temp1 borrow1b borrow1 borrow1a (base + 56)
    -- Store phase
    have A := addi_spec_gen_same_within .x12 sp 32 (base + 80) (by nofun)
    simp only [signExtend12_32] at A
    have S0 := sd_spec_gen_within .x12 .x5 (sp + 32) borrow2 b0 0 (base + 84)
    have S1 := sd_x0_spec_gen_within .x12 (sp + 32) b1 8 (base + 88)
    have S2 := sd_x0_spec_gen_within .x12 (sp + 32) b2 16 (base + 92)
    have S3 := sd_x0_spec_gen_within .x12 (sp + 32) b3 24 (base + 96)
    runBlock M B L0 L1 L2 A S0 S1 S2 S3
  · -- Case: MSB limbs differ → BEQ not taken, SLT + JAL path
    simp only [if_neg h]
    -- MSB load phase (swapped)
    have M := slt_msb_load_spec_within 56 24 sp b3 a3 v7 v6 base
    -- BEQ not taken (b3 ≠ a3)
    have B := beq_ne_spec_within .x7 .x6 (12 : BitVec 13) b3 a3 h (base + 8)
    -- SLT instruction (signed compare b3 vs a3)
    have S := slt_spec_gen_within .x5 .x7 .x6 v5 b3 a3 (base + 12) (by nofun)
    -- JAL to store
    have J := jal_x0_spec_gen_within (64 : BitVec 21) (base + 16)
    simp only [se21_64] at J
    -- Store phase
    have A := addi_spec_gen_same_within .x12 sp 32 (base + 80) (by nofun)
    simp only [signExtend12_32] at A
    have S0 := sd_spec_gen_within .x12 .x5 (sp + 32) sgtMsb b0 0 (base + 84)
    have S1 := sd_x0_spec_gen_within .x12 (sp + 32) b1 8 (base + 88)
    have S2 := sd_x0_spec_gen_within .x12 (sp + 32) b2 16 (base + 92)
    have S3 := sd_x0_spec_gen_within .x12 (sp + 32) b3 24 (base + 96)
    runBlock M B S J A S0 S1 S2 S3


-- ============================================================================
-- Stack-level SGT spec
-- ============================================================================

/-- Stack-level 256-bit EVM SGT: operates on two EvmWords via evmWordIs.
    SGT(a, b) = SLT(b, a), using signed comparison with swapped operands. -/
theorem evm_sgt_stack_spec_within (sp base : Word)
    (a b : EvmWord) (v7 v6 v5 v11 : Word) :
    -- Lower 3 limbs borrow chain: b - a direction (used when MSB limbs equal)
    let borrow0 := if BitVec.ult (b.getLimbN 0) (a.getLimbN 0) then (1 : Word) else 0
    let borrow1a := if BitVec.ult (b.getLimbN 1) (a.getLimbN 1) then (1 : Word) else 0
    let temp1 := b.getLimbN 1 - a.getLimbN 1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult (b.getLimbN 2) (a.getLimbN 2) then (1 : Word) else 0
    let temp2 := b.getLimbN 2 - a.getLimbN 2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    -- Signed comparison of MSB limbs (swapped: b3 vs a3)
    let sgtMsb := if BitVec.slt (b.getLimbN 3) (a.getLimbN 3) then (1 : Word) else 0
    let result := if b.getLimbN 3 = a.getLimbN 3 then borrow2 else sgtMsb
    let code := evm_sgt_code base
    cpsTripleWithin 25 base (base + 100) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) **
       (.x7 ↦ᵣ (if b.getLimbN 3 = a.getLimbN 3 then temp2 else b.getLimbN 3)) **
       (.x6 ↦ᵣ (if b.getLimbN 3 = a.getLimbN 3 then borrow2b else a.getLimbN 3)) **
       (.x5 ↦ᵣ result) **
       (.x11 ↦ᵣ (if b.getLimbN 3 = a.getLimbN 3 then borrow2a else v11)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (if BitVec.slt b a then 1 else 0)) := by
  intro borrow0 borrow1a temp1 borrow1b borrow1 borrow2a temp2 borrow2b borrow2 sgtMsb result
  have h_main := evm_sgt_spec_within sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v7 v6 v5 v11
  exact cpsTripleWithin_weaken
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
