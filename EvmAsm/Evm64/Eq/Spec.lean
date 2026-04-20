/-
  EvmAsm.Evm64.Eq.Spec

  Full 256-bit EVM EQ spec composed from per-limb specs.
  21 instructions total (3 + 3×4 + 6 store).
-/

import EvmAsm.Evm64.Eq.LimbSpec
import EvmAsm.Evm64.EvmWordArith
import EvmAsm.Evm64.SpAddr

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CodeReq for the 256-bit EVM EQ operation.
    21 instructions = 84 bytes. XOR-OR accumulation + SLTIU boolean + store. -/
abbrev evm_eq_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_eq

/-- Full 256-bit EVM EQ: EQ(a, b) = 1 iff a == b (unsigned).
    XOR each limb pair, OR-reduce, SLTIU to boolean.
    Pops 2 stack words (A at sp, B at sp+32),
    writes result to sp+32..sp+56, advances sp by 32.
    21 instructions = 84 bytes total. -/
theorem evm_eq_spec (sp : Word) (base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (v7 v6 v5 v11 : Word) :
    -- XOR-OR accumulation chain
    let acc0 := a0 ^^^ b0
    let acc1 := acc0 ||| (a1 ^^^ b1)
    let acc2 := acc1 ||| (a2 ^^^ b2)
    let acc3 := acc2 ||| (a3 ^^^ b3)
    let eqResult := if BitVec.ult acc3 (1 : Word) then (1 : Word) else 0
    let code := evm_eq_code base
    cpsTriple base (base + 84) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) **
       (.x7 ↦ᵣ eqResult) ** (.x6 ↦ᵣ (a3 ^^^ b3)) ** (.x5 ↦ᵣ b3) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ eqResult) ** ((sp + 40) ↦ₘ 0) ** ((sp + 48) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0)) := by
  intro acc0 acc1 acc2 acc3 eqResult
  -- Per-limb EQ specs
  have L0 := eq_limb0_spec 0 32 sp a0 b0 v7 v6 base
  have L1 := eq_or_limb_spec 8 40 sp a1 b1 b0 v5 (a0 ^^^ b0) (base + 12)
  have L2 := eq_or_limb_spec 16 48 sp a2 b2 (a1 ^^^ b1) b1
    ((a0 ^^^ b0) ||| (a1 ^^^ b1)) (base + 28)
  have L3 := eq_or_limb_spec 24 56 sp a3 b3 (a2 ^^^ b2) b2
    ((a0 ^^^ b0) ||| (a1 ^^^ b1) ||| (a2 ^^^ b2)) (base + 44)
  -- Store phase: SLTIU + ADDI + SD eqResult + 3×SD 0
  have T := sltiu_spec_gen_same .x7
    ((a0 ^^^ b0) ||| (a1 ^^^ b1) ||| (a2 ^^^ b2) ||| (a3 ^^^ b3)) 1 (base + 60) (by nofun)
  simp only [signExtend12_1] at T
  have A := addi_spec_gen_same .x12 sp 32 (base + 64) (by nofun)
  simp only [signExtend12_32] at A
  have S0 := sd_spec_gen .x12 .x7 (sp + 32)
    (if BitVec.ult ((a0 ^^^ b0) ||| (a1 ^^^ b1) ||| (a2 ^^^ b2) ||| (a3 ^^^ b3)) (1 : Word) then (1 : Word) else 0)
    b0 0 (base + 68)
  have S1 := sd_x0_spec_gen .x12 (sp + 32) b1 8 (base + 72)
  have S2 := sd_x0_spec_gen .x12 (sp + 32) b2 16 (base + 76)
  have S3 := sd_x0_spec_gen .x12 (sp + 32) b3 24 (base + 80)
  runBlock L0 L1 L2 L3 T A S0 S1 S2 S3

-- ============================================================================
-- Stack-level EQ spec
-- ============================================================================

/-- Stack-level 256-bit EVM EQ: operates on two EvmWords via evmWordIs. -/
theorem evm_eq_stack_spec (sp base : Word)
    (a b : EvmWord) (v7 v6 v5 v11 : Word) :
    -- XOR-OR accumulation chain
    let acc0 := a.getLimbN 0 ^^^ b.getLimbN 0
    let acc1 := acc0 ||| (a.getLimbN 1 ^^^ b.getLimbN 1)
    let acc2 := acc1 ||| (a.getLimbN 2 ^^^ b.getLimbN 2)
    let acc3 := acc2 ||| (a.getLimbN 3 ^^^ b.getLimbN 3)
    let eqResult := if BitVec.ult acc3 (1 : Word) then (1 : Word) else 0
    let code := evm_eq_code base
    cpsTriple base (base + 84) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) **
       (.x7 ↦ᵣ eqResult) ** (.x6 ↦ᵣ (a.getLimbN 3 ^^^ b.getLimbN 3)) **
       (.x5 ↦ᵣ b.getLimbN 3) ** (.x11 ↦ᵣ v11) **
       evmWordIs sp a ** evmWordIs (sp + 32) (if a = b then 1 else 0)) := by
  intro acc0 acc1 acc2 acc3 eqResult
  have h_main := evm_eq_spec sp base
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
                 ← EvmWord.eq_xor_or_reduce_correct]
      simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
                 EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]
      rw [spAddr32_8, spAddr32_16, spAddr32_24]
      xperm_hyp hq)
    h_main

end EvmAsm.Evm64
