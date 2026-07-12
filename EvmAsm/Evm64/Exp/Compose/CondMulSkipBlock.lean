/-
  EvmAsm.Evm64.Exp.Compose.CondMulSkipBlock

  Lift the conditional-multiply skip branch into the full-loop EXP+MUL code
  bundle.
-/

import EvmAsm.Evm64.Exp.SquaringWithMulShared

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Conditional-multiply BEQ skip-gate lifted to the full-loop EXP+MUL code
    bundle. -/
theorem exp_cond_mul_beq_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (v10 : Word) (base mulTarget target : Word)
    (htarget : (base + 144 : Word) + signExtend13 skipOff = target) :
    cpsBranchWithin 1 (base + 144)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 = 0⌝)
      (base + 148) ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ 0⌝) :=
  cpsBranchWithin_extend_evmExpWithMulCode
    (exp_cond_mul_beq_evm_exp_spec_within
      mulOff skipOff backOff v10 base target htarget)

end EvmAsm.Evm64.Exp.Compose
