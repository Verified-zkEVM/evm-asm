/- Shared declaration home for the EXP conditional-multiply call path and block. -/

import EvmAsm.Evm64.Exp.SquaringWithMulShared
import EvmAsm.Evm64.Exp.CondMulPairThenMulCall
import EvmAsm.Evm64.Exp.AddrNorm

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Cond-mul-side marshal-pair + JAL + `mul_callable` round-trip lifted from
    the disjoint-union code `exp_cond_mul_call_block_code.union mul_callable_code`
    into the combined `evmExpWithMulCode` bundle. Sibling of
    `exp_squaring_marshal_pair_then_mul_call_evm_exp_with_mul_spec_within`.
    Instantiates `EvmAsm.Evm64.exp_cond_mul_marshal_pair_then_mul_call_spec_within`
    at offset `base + 148` (the cond-mul-call sub-block entry inside the
    iteration body, after the leading BEQ skip-gate at `base + 144`). -/
theorem exp_cond_mul_marshal_pair_then_mul_call_evm_exp_with_mul_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) (base : Word)
    (hmt : mulTarget = ((base + 148) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    cpsTripleWithin (17 + 64) (base + 148) (((base + 148) + 68) &&& ~~~1)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       evmMulStackPost evmSp (expResultWord r0 r1 r2 r3)
                              (expResultWord a0 a1 a2 a3) **
       (.x1 ↦ᵣ ((base + 148) + 68))) := by
  have hCondSub : ∀ a i,
      exp_cond_mul_call_block_code (base + 148) mulOff a = some i →
      evmExpCode base mulOff skipOff backOff a = some i := by
    intro a i h
    rw [EvmAsm.Evm64.Exp.AddrNorm.expFullLoopCondMulCallAddr] at h
    exact evmExpCode_iter_cond_mul_sub a i
      (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code_call_sub
        (base + 144) mulOff skipOff a i h)
  have hd_inner : CodeReq.Disjoint
      (exp_cond_mul_call_block_code (base + 148) mulOff)
      (mul_callable_code mulTarget) := by
    intro a
    rcases hd a with hExp | hMul
    · left
      cases hsub : exp_cond_mul_call_block_code (base + 148) mulOff a with
      | none => rfl
      | some i =>
        have hev := hCondSub a i hsub
        exact absurd (hev.symm.trans hExp) (by simp)
    · right
      exact hMul
  have hbase := EvmAsm.Evm64.exp_cond_mul_marshal_pair_then_mul_call_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget mulOff (base + 148) hmt hd_inner
  exact cpsTripleWithin_extend_code
    (hmono := CodeReq.union_sub
      (fun a i h => evmExpWithMulCode_exp_sub a i (hCondSub a i h))
      (fun a i h => evmExpWithMulCode_mul_sub hd a i h)) hbase


open EvmAsm.Rv64

/-- Cond-mul-side full call-block (`marshal_pair + JAL + mul_callable +
    un_marshal_and_restore`, 90 instrs) lifted from the disjoint-union
    code into the full-loop `evmExpWithMulCode` bundle. Instantiates
    `EvmAsm.Evm64.exp_cond_mul_call_block_spec_within` at offset
    `base + 148` (the cond-mul call sub-block entry after the leading
    BEQ skip-gate at `base + 144`). -/
theorem exp_cond_mul_call_block_evm_exp_with_mul_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 148) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let rw := expCondMulRwFromLimbs r0 r1 r2 r3 a0 a1 a2 a3
    cpsTripleWithin (17 + 64 + 9) (base + 148) ((base + 148) + 104)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ rw.getLimbN 3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 148) + 68))) := by
  intro rw
  have hbase' : (base + 148 : Word) &&& 1 = 0 :=
    EvmAsm.Evm64.Exp.AddrNorm.expBaseAdd148Aligned base hbase
  have hCondSub : ∀ a i,
      exp_cond_mul_call_block_code (base + 148) mulOff a = some i →
      evmExpCode base mulOff skipOff backOff a = some i := by
    intro a i h
    rw [EvmAsm.Evm64.Exp.AddrNorm.expFullLoopCondMulCallAddr] at h
    exact evmExpCode_iter_cond_mul_sub a i
      (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code_call_sub
        (base + 144) mulOff skipOff a i h)
  have hd_inner : CodeReq.Disjoint
      (exp_cond_mul_call_block_code (base + 148) mulOff)
      (mul_callable_code mulTarget) := by
    intro a
    rcases hd a with hExp | hMul
    · left
      cases hsub : exp_cond_mul_call_block_code (base + 148) mulOff a with
      | none => rfl
      | some i =>
        have hev := hCondSub a i hsub
        exact absurd (hev.symm.trans hExp) (by simp)
    · right
      exact hMul
  have hbase_spec := EvmAsm.Evm64.exp_cond_mul_call_block_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget mulOff (base + 148) hbase' hmt hd_inner
  exact cpsTripleWithin_extend_code
    (hmono := CodeReq.union_sub
      (fun a i h => evmExpWithMulCode_exp_sub a i (hCondSub a i h))
      (fun a i h => evmExpWithMulCode_mul_sub hd a i h)) hbase_spec

end EvmAsm.Evm64.Exp.Compose
