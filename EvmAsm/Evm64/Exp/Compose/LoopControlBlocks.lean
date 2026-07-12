/-
  EvmAsm.Evm64.Exp.Compose.LoopControlBlocks

  Lift simple EXP loop-control blocks into the full-loop EXP+MUL code bundle.
-/

import EvmAsm.Evm64.Exp.SquaringWithMulShared

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Bit-test block lifted to the full-loop EXP+MUL code bundle. -/
theorem exp_bit_test_evm_exp_with_mul_spec_within
    (e c v10 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin 3 (base + 28) (base + 40)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e >>> (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (e &&& signExtend12 (1 : BitVec 12)))) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_bit_test_evm_exp_spec_within e c v10 mulOff skipOff backOff base)

/-- Loop-back block lifted to the full-loop EXP+MUL code bundle. -/
theorem exp_loop_back_evm_exp_with_mul_spec_within (c : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget target : Word)
    (htarget : ((base + 252) + 4 : Word) + signExtend13 backOff = target) :
    cpsBranchWithin 2 (base + 252)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      target
        ((.x9 ↦ᵣ expIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜expIterCountNew c ≠ 0⌝)
      (base + 260)
        ((.x9 ↦ᵣ expIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜expIterCountNew c = 0⌝) :=
  cpsBranchWithin_extend_evmExpWithMulCode
    (exp_loop_back_evm_exp_spec_within c mulOff skipOff backOff base target htarget)

/-- Squaring-call JAL lifted to the full-loop EXP+MUL code bundle. -/
theorem exp_squaring_square_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (vOld : Word) (base mulTarget : Word)
    (hmul : ((base + 104) + signExtend21 mulOff : Word) = mulTarget) :
    cpsTripleWithin 1 (base + 104) mulTarget
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 108)) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_squaring_square_evm_exp_spec_within
      mulOff skipOff backOff vOld base mulTarget hmul)

/-- Conditional-multiply JAL lifted to the full-loop EXP+MUL code bundle. -/
theorem exp_cond_mul_square_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (vOld : Word) (base mulTarget : Word)
    (hmul : ((base + 212) + signExtend21 mulOff : Word) = mulTarget) :
    cpsTripleWithin 1 (base + 212) mulTarget
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 216)) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_cond_mul_square_evm_exp_spec_within
      mulOff skipOff backOff vOld base mulTarget hmul)

end EvmAsm.Evm64.Exp.Compose
