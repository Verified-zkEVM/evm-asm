/- Shared declaration home for the EXP squaring code bundle and marshal blocks. -/

import EvmAsm.Evm64.Exp.TopPipelineShared
import EvmAsm.Evm64.Exp.SquaringPairThenMulCall
import EvmAsm.Evm64.Exp.CondMulPairThenMulCall
import EvmAsm.Evm64.Multiply.Callable
import EvmAsm.Evm64.Exp.AddrNorm

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Code required by the top-level EXP program plus the external
    `mul_callable` body reached by both JALs in one loop iteration. -/
abbrev evmExpWithMulCode (base mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : CodeReq :=
  (evmExpCode base mulOff skipOff backOff).union (mul_callable_code mulTarget)

theorem evmExpWithMulCode_exp_sub {base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (evmExpCode base mulOff skipOff backOff) a = some i →
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) a = some i := by
  unfold evmExpWithMulCode
  exact CodeReq.union_mono_left

theorem evmExpWithMulCode_mul_sub {base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (evmExpCode base mulOff skipOff backOff) (mul_callable_code mulTarget)) :
    ∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) a = some i := by
  unfold evmExpWithMulCode
  exact CodeReq.mono_union_right hd (fun _ _ h => h)

abbrev expCondMulRwFromLimbs
    (r0 r1 r2 r3 a0 a1 a2 a3 : Word) : EvmWord :=
  expCondMulCallProductW r0 r1 r2 r3 a0 a1 a2 a3

abbrev expSquareRw (r0 r1 r2 r3 : Word) : EvmWord :=
  expSquaringCallSquareW r0 r1 r2 r3

/-- Lift a top-level EXP-body spec into the combined EXP+MUL code bundle. -/
theorem cpsTripleWithin_extend_evmExpWithMulCode {nSteps : Nat}
    {entry exit_ base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_
      (evmExpCode base mulOff skipOff backOff) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) P Q :=
  cpsTripleWithin_extend_code (hmono := evmExpWithMulCode_exp_sub) h

/-- Lift a top-level EXP-body branch spec into the combined EXP+MUL code
    bundle. The full loop uses this for the conditional multiply skip gate and
    the iteration back-edge. -/
theorem cpsBranchWithin_extend_evmExpWithMulCode {nSteps : Nat}
    {entry base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word}
    {Q_f : Assertion}
    (h : cpsBranchWithin nSteps entry
      (evmExpCode base mulOff skipOff backOff) P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f :=
  cpsBranchWithin_extend_code (hmono := evmExpWithMulCode_exp_sub) h

/-- Lift a top-level EXP-body N-branch spec into the combined EXP+MUL code
    bundle. -/
theorem cpsNBranchWithin_extend_evmExpWithMulCode {nSteps : Nat}
    {entry base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P : Assertion} {exits : List (Word × Assertion)}
    (h : cpsNBranchWithin nSteps entry
      (evmExpCode base mulOff skipOff backOff) P exits) :
    cpsNBranchWithin nSteps entry
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) P exits :=
  cpsNBranchWithin_extend_code (hmono := evmExpWithMulCode_exp_sub) h

/-- Lift a multiply-callable spec into the combined EXP+MUL code bundle. -/
theorem cpsTripleWithin_extend_mulCallable_evmExpWithMulCode {nSteps : Nat}
    {entry exit_ base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q : Assertion}
    (hd : CodeReq.Disjoint
      (evmExpCode base mulOff skipOff backOff) (mul_callable_code mulTarget))
    (h : cpsTripleWithin nSteps entry exit_ (mul_callable_code mulTarget) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) P Q :=
  cpsTripleWithin_extend_code
    (hmono := evmExpWithMulCode_mul_sub (base := base) (mulTarget := mulTarget)
      (mulOff := mulOff) (skipOff := skipOff) (backOff := backOff) hd)
    h

theorem evmExpWithMulCode_block_subs {base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (evmExpCode base mulOff skipOff backOff) (mul_callable_code mulTarget)) :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (expIterBodyFullCode (base + 28) mulOff skipOff backOff) a = some i →
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 260)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 264) EvmAsm.Evm64.exp_epilogue) a = some i →
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) a = some i) := by
  rcases evmExpCode_block_subs (base := base) (mulOff := mulOff)
      (skipOff := skipOff) (backOff := backOff) with
    ⟨h_prologue, h_pointer_advance, h_iter, h_pointer_restore, h_epilogue⟩
  exact
    ⟨fun a i h => evmExpWithMulCode_exp_sub a i (h_prologue a i h),
     fun a i h => evmExpWithMulCode_exp_sub a i (h_pointer_advance a i h),
     fun a i h => evmExpWithMulCode_exp_sub a i (h_iter a i h),
     fun a i h => evmExpWithMulCode_exp_sub a i (h_pointer_restore a i h),
     fun a i h => evmExpWithMulCode_exp_sub a i (h_epilogue a i h),
     evmExpWithMulCode_mul_sub hd⟩


open EvmAsm.Rv64

/-- Squaring-side marshal-pair + JAL + `mul_callable` round-trip lifted from
    the disjoint-union code `exp_squaring_call_block_code.union mul_callable_code`
    into the combined `evmExpWithMulCode` bundle. Iteration body composition
    needs the round-trip spec stated over the full-loop code, not the local
    union. Reuses `EvmAsm.Evm64.exp_squaring_marshal_pair_then_mul_call_spec_within`
    instantiated at offset `base + 40` (the squaring-call sub-block entry inside
    the iteration body). -/
theorem exp_squaring_marshal_pair_then_mul_call_evm_exp_with_mul_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) (base : Word)
    (hmt : mulTarget = ((base + 40) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    cpsTripleWithin (17 + 64) (base + 40) (((base + 40) + 68) &&& ~~~1)
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
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmMulStackPost evmSp (expResultWord r0 r1 r2 r3)
                              (expResultWord r0 r1 r2 r3) **
       (.x1 ↦ᵣ ((base + 40) + 68))) := by
  have hd_inner : CodeReq.Disjoint
      (exp_squaring_call_block_code (base + 40) mulOff)
      (mul_callable_code mulTarget) := by
    intro a
    rcases hd a with hExp | hMul
    · left
      cases hsub : exp_squaring_call_block_code (base + 40) mulOff a with
      | none => rfl
      | some i =>
        have hev := evmExpCode_iter_squaring_sub
          (base := base) (mulOff := mulOff)
          (skipOff := skipOff) (backOff := backOff) a i hsub
        exact absurd (hev.symm.trans hExp) (by simp)
    · right
      exact hMul
  have hbase := EvmAsm.Evm64.exp_squaring_marshal_pair_then_mul_call_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget mulOff (base + 40) hmt hd_inner
  exact cpsTripleWithin_extend_code
    (hmono := CodeReq.union_sub
      (fun a i h => evmExpWithMulCode_exp_sub a i
        (evmExpCode_iter_squaring_sub
          (base := base) (mulOff := mulOff)
          (skipOff := skipOff) (backOff := backOff) a i h))
      (fun a i h => evmExpWithMulCode_mul_sub hd a i h)) hbase


open EvmAsm.Rv64

/-- Squaring-side full call-block (`marshal_pair + JAL + mul_callable +
    un_marshal_and_restore`, 90 instrs) lifted from the disjoint-union
    code into the full-loop `evmExpWithMulCode` bundle. Instantiates
    `EvmAsm.Evm64.exp_squaring_call_block_spec_within` at offset `base + 40`
    (the squaring-call sub-block entry inside the iteration body). -/
theorem exp_squaring_call_block_evm_exp_with_mul_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 40) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let rw := expSquareRw r0 r1 r2 r3
    cpsTripleWithin (17 + 64 + 9) (base + 40) ((base + 40) + 104)
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
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ rw.getLimbN 3) **
       evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 40) + 68))) := by
  intro rw
  have hbase' : (base + 40 : Word) &&& 1 = 0 :=
    EvmAsm.Evm64.Exp.AddrNorm.expBaseAdd40Aligned base hbase
  have hd_inner : CodeReq.Disjoint
      (exp_squaring_call_block_code (base + 40) mulOff)
      (mul_callable_code mulTarget) := by
    intro a
    rcases hd a with hExp | hMul
    · left
      cases hsub : exp_squaring_call_block_code (base + 40) mulOff a with
      | none => rfl
      | some i =>
        have hev := evmExpCode_iter_squaring_sub
          (base := base) (mulOff := mulOff)
          (skipOff := skipOff) (backOff := backOff) a i hsub
        exact absurd (hev.symm.trans hExp) (by simp)
    · right
      exact hMul
  have hbase_spec := EvmAsm.Evm64.exp_squaring_call_block_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget mulOff (base + 40) hbase' hmt hd_inner
  exact cpsTripleWithin_extend_code
    (hmono := CodeReq.union_sub
      (fun a i h => evmExpWithMulCode_exp_sub a i
        (evmExpCode_iter_squaring_sub
          (base := base) (mulOff := mulOff)
          (skipOff := skipOff) (backOff := backOff) a i h))
      (fun a i h => evmExpWithMulCode_mul_sub hd a i h)) hbase_spec


open EvmAsm.Rv64

/-- Squaring-call factor-1 marshal lifted to the full-loop EXP+MUL code bundle. -/
theorem exp_squaring_marshal_factor1_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (base mulTarget : Word) :
    cpsTripleWithin 8 (base + 40) (base + 72)
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
    (exp_squaring_marshal_factor1_evm_exp_spec_within
      mulOff skipOff backOff sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base)

/-- Squaring-call factor-2 marshal lifted to the full-loop EXP+MUL code bundle. -/
theorem exp_squaring_marshal_result_to_factor2_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (base mulTarget : Word) :
    cpsTripleWithin 8 (base + 72) (base + 104)
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3)) :=
  cpsTripleWithin_extend_evmExpWithMulCode
    (exp_squaring_marshal_result_to_factor2_evm_exp_spec_within
      mulOff skipOff backOff sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base)

/-- Squaring-call un-marshal-and-restore lifted to the full-loop EXP+MUL code
    bundle. -/
theorem exp_squaring_un_marshal_and_restore_evm_exp_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (base mulTarget : Word) :
    cpsTripleWithin 9 (base + 108) (base + 144)
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
    (exp_squaring_un_marshal_and_restore_evm_exp_spec_within
      mulOff skipOff backOff sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base)

end EvmAsm.Evm64.Exp.Compose
