/-
  EvmAsm.Evm64.Exp.Compose.LoopCodeSpecs

  EXP loop-code specs split out of `Compose/Base.lean` to keep the base
  composition module under the Compose file-size guardrail.
-/

module

public import EvmAsm.Evm64.Exp.Compose.Base
public import EvmAsm.Evm64.Exp.AddrNorm

@[expose] public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64 (cpsBranchWithin cpsBranchWithin_extend_code cpsTripleWithin
  cpsTripleWithin_extend_code signExtend12 signExtend13 signExtend21)

theorem exp_loop_back_loop_spec_within (c : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base target : Word)
    (htarget : ((base + 24) + 4 : Word) + signExtend13 backOff = target) :
    cpsBranchWithin 2 (base + 24)
      (expLoopCode base mulOff skipOff backOff)
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      target
        ((.x9 ↦ᵣ expIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜expIterCountNew c ≠ 0⌝)
      (base + 32)
        ((.x9 ↦ᵣ expIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜expIterCountNew c = 0⌝) := by
  have h := EvmAsm.Evm64.exp_loop_back_spec_within c backOff (base + 24) target htarget
  rw [EvmAsm.Evm64.Exp.AddrNorm.expLoopBackNextPc] at h
  simpa [expIterCountNew] using
    (cpsBranchWithin_extend_code (h := h) (hmono := expLoopCode_loop_back_sub))

theorem exp_bit_test_loop_spec_within
    (e c v10 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 3 base (base + 12) (expLoopCode base mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e >>> (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (e &&& signExtend12 (1 : BitVec 12)))) := by
  have h := EvmAsm.Evm64.exp_bit_test_block_spec_within e c v10 base
  exact cpsTripleWithin_extend_code (h := h) (hmono := expLoopCode_bit_test_sub)

theorem exp_square_loop_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (vOld : Word) (base mulTarget : Word)
    (hmul : ((base + 12) + signExtend21 mulOff : Word) = mulTarget) :
    cpsTripleWithin 1 (base + 12) mulTarget
      (expLoopCode base mulOff skipOff backOff)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 16)) := by
  have h := EvmAsm.Evm64.exp_square_block_spec_within mulOff vOld (base + 12)
  rw [hmul] at h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expLoopSquareReturnPc] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := expLoopCode_square_sub)

theorem exp_cond_mul_loop_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (v10 vOld : Word) (base skipTarget mulTarget : Word)
    (hskip : ((base + 16) + signExtend13 skipOff : Word) = skipTarget)
    (hmul : (((base + 16) + 4) + signExtend21 mulOff : Word) = mulTarget) :
    cpsBranchWithin 2 (base + 16) (expLoopCode base mulOff skipOff backOff)
      ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vOld))
      skipTarget
        ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vOld) **
          ⌜v10 = 0⌝)
      mulTarget
        ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (base + 24)) **
          ⌜v10 ≠ 0⌝) := by
  have h := EvmAsm.Evm64.exp_cond_mul_block_spec_within
    mulOff skipOff v10 vOld (base + 16)
  rw [hskip, hmul] at h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expLoopCondMulReturnPc] at h
  exact cpsBranchWithin_extend_code (h := h) (hmono := expLoopCode_cond_mul_sub)

end EvmAsm.Evm64.Exp.Compose
