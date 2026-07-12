/-
  EvmAsm.Evm64.Exp.Compose.CondMulMarshalBlocks

  Lift conditional-multiply marshal/unmarshal blocks into the full-loop
  EXP+MUL code bundle.
-/

import EvmAsm.Evm64.Exp.SquaringWithMulShared

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Conditional-multiply factor-1 marshal lifted to the full-loop EXP+MUL
    code bundle. -/
theorem exp_cond_mul_marshal_factor1_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (base mulTarget : Word) :
    cpsTripleWithin 8 (base + 148) (base + 180)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3)) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_cond_mul_marshal_factor1_evm_exp_spec_within
      mulOff skipOff backOff sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base)

/-- Conditional-multiply factor-2 marshal (from EVM-stack base slot) lifted
    to the full-loop EXP+MUL code bundle. -/
theorem exp_cond_mul_marshal_a_to_factor2_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (evmSp tOld a0 a1 a2 a3 d0 d1 d2 d3 : Word)
    (base mulTarget : Word) :
    cpsTripleWithin 8 (base + 180) (base + 212)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ a3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3)) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_cond_mul_marshal_a_to_factor2_evm_exp_spec_within
      mulOff skipOff backOff evmSp tOld a0 a1 a2 a3 d0 d1 d2 d3 base)

/-- Conditional-multiply un-marshal-and-restore lifted to the full-loop
    EXP+MUL code bundle. -/
theorem exp_cond_mul_un_marshal_and_restore_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (base mulTarget : Word) :
    cpsTripleWithin 9 (base + 216) (base + 252)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (-32 : BitVec 12))) **
       (.x5 ↦ᵣ d3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3)) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_cond_mul_un_marshal_and_restore_evm_exp_spec_within
      mulOff skipOff backOff sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base)

end EvmAsm.Evm64.Exp.Compose
