/-
  EvmAsm.Evm64.IsZero.Spec

  Full 256-bit EVM ISZERO spec composed from per-limb specs.
  12 instructions total. Unary: pops 1, pushes 1, sp unchanged.
-/

import EvmAsm.Evm64.IsZero.LimbSpec
import EvmAsm.Evm64.EvmWordArith.IsZero

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CodeReq for the 256-bit EVM ISZERO operation.
    12 instructions = 48 bytes. OR-reduce 4 limbs + SLTIU boolean + store. -/
abbrev evm_iszero_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_iszero

/-- Full 256-bit EVM ISZERO: result = 1 iff all 4 limbs are 0.
    Unary: reads 256-bit word at sp, overwrites with boolean result.
    12 instructions = 48 bytes. -/
theorem evm_iszero_spec (sp : Word) (base : Word)
    (a0 a1 a2 a3 : Word)
    (v7 v6 : Word) :
    let orAll := a0 ||| a1 ||| a2 ||| a3
    let result := if BitVec.ult orAll (1 : Word) then (1 : Word) else 0
    let code := evm_iszero_code base
    cpsTriple base (base + 48) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ a3) **
       (sp ↦ₘ result) ** ((sp + 8) ↦ₘ 0) ** ((sp + 16) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0)) := by
  intro orAll result
  -- LD x7 x12 0 (load limb 0 into x7)
  have L0 := ld_spec_gen .x7 .x12 sp v7 a0 0 base (by nofun)
  -- OR limbs 1-3
  have O1 := iszero_or_limb_spec 8 sp a1 v6 a0 (base + 4)
  have O2 := iszero_or_limb_spec 16 sp a2 a1 (a0 ||| a1) (base + 12)
  have O3 := iszero_or_limb_spec 24 sp a3 a2 (a0 ||| a1 ||| a2) (base + 20)
  -- SLTIU
  have T := sltiu_spec_gen_same .x7 (a0 ||| a1 ||| a2 ||| a3) 1 (base + 28) (by nofun)
  simp only [signExtend12_1] at T
  -- Store phase
  have S0 := sd_spec_gen .x12 .x7 sp
    (if BitVec.ult (a0 ||| a1 ||| a2 ||| a3) (1 : Word) then (1 : Word) else 0)
    a0 0 (base + 32)
  have S1 := sd_x0_spec_gen .x12 sp a1 8 (base + 36)
  have S2 := sd_x0_spec_gen .x12 sp a2 16 (base + 40)
  have S3 := sd_x0_spec_gen .x12 sp a3 24 (base + 44)
  runBlock L0 O1 O2 O3 T S0 S1 S2 S3

-- ============================================================================
-- Stack-level ISZERO spec
-- ============================================================================

/-- Stack-level 256-bit EVM ISZERO: operates on an EvmWord via evmWordIs. -/
theorem evm_iszero_stack_spec (sp base : Word)
    (a : EvmWord) (v7 v6 : Word) :
    let orAll := a.getLimbN 0 ||| a.getLimbN 1 ||| a.getLimbN 2 ||| a.getLimbN 3
    let result := if BitVec.ult orAll 1 then (1 : Word) else 0
    let code := evm_iszero_code base
    cpsTriple base (base + 48) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a)
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ a.getLimbN 3) **
       evmWordIs sp (if a = 0 then 1 else 0)) := by
  intro orAll result
  have h_main := evm_iszero_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    v7 v6
  exact cpsTriple_weaken
    (fun h hp => by
      simp only [evmWordIs] at hp
      xperm_hyp hp)
    (fun h hq => by
      unfold evmWordIs
      simp only [EvmWord.getLimbN_ite, EvmWord.getLimbN_zero,
                 EvmWord.getLimbN_one_zero, EvmWord.getLimbN_one_one,
                 EvmWord.getLimbN_one_two, EvmWord.getLimbN_one_three,
                 ite_self,
                 ← EvmWord.iszero_or_reduce_correct]
      simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
                 EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]
      xperm_hyp hq)
    h_main

end EvmAsm.Evm64
