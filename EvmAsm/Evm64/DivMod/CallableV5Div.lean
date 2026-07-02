/-
  EvmAsm.Evm64.DivMod.CallableV5Div

  v5 LP64-callable DIV adapter: code-subsumption lemmas from the v5 DIV body
  surface (`divCode_noNop_v5`) into the callable code `evm_div_callable_code_v5`,
  the `cc_ret` return-instruction subsumption, and the callable wrappers that
  append the return to an x1(-and-x9)-preserving v5 body proof.

  Mechanical mirror of `EvmAsm.Evm64.DivMod.CallableV4Div`, swapping the appended
  `divK_div128_v4` subroutine block to `divK_div128_v5` (blocks b0–b12 are
  byte-identical; only b13 differs).  This is the *return adapter* only: it takes
  an x1/x9-preserving v5 no-NOP stack proof already shaped for the callable post
  and threads it through the `cc_ret`.  Supplying that x1-preserving v5 body proof
  (a rebuild of the callable-post lane infrastructure over v5) is the remaining
  work for a fully unconditional `evm_div_callable_v5` correctness spec.
-/

import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Evm64.DivMod.Compose.V5NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

private theorem callable_b0_div_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i →
      (evm_div_callable_code_v5 b) a = some i := by
  unfold evm_div_callable_code_v5; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left
private theorem callable_b1_div_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i →
      (evm_div_callable_code_v5 b) a = some i := by
  unfold evm_div_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b2_div_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i →
      (evm_div_callable_code_v5 b) a = some i := by
  unfold evm_div_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b3_div_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i →
      (evm_div_callable_code_v5 b) a = some i := by
  unfold evm_div_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b4_div_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i →
      (evm_div_callable_code_v5 b) a = some i := by
  unfold evm_div_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b5_div_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i →
      (evm_div_callable_code_v5 b) a = some i := by
  unfold evm_div_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b6_div_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i →
      (evm_div_callable_code_v5 b) a = some i := by
  unfold evm_div_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b7_div_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
      (evm_div_callable_code_v5 b) a = some i := by
  unfold evm_div_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b8_div_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (evm_div_callable_code_v5 b) a = some i := by
  unfold evm_div_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b9_div_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i →
      (evm_div_callable_code_v5 b) a = some i := by
  unfold evm_div_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b10_div_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + epilogueOff) (divK_div_epilogue 24)) a = some i →
      (evm_div_callable_code_v5 b) a = some i := by
  unfold evm_div_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b11_div_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i →
      (evm_div_callable_code_v5 b) a = some i := by
  unfold evm_div_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b12_div_v5 {b : Word} :
    ∀ a i, (cc_ret_code (b + nopOff)) a = some i →
      (evm_div_callable_code_v5 b) a = some i := by
  unfold evm_div_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  exact CodeReq.union_mono_left
private theorem callable_b13_div_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128_v5) a = some i →
      (evm_div_callable_code_v5 b) a = some i := by
  unfold evm_div_callable_code_v5; simp only [CodeReq.unionAll_cons, cc_ret_code]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock
  -- final skip: over the `cc_ret` block while targeting `divK_div128_v5`; needs
  -- BOTH `cc_ret_len` (only in `skipBlockCC`) and `divK_div128_v5_len` (only in
  -- `skipBlock`), so inline the disjoint-range tactic with the full simp set.
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [divK_div128_v5_len, cc_ret_len] at hk1 hk2
      bv_omega))
  exact CodeReq.union_mono_left

/-- The callable `cc_ret` return instruction sits at `base + nopOff` inside
    `evm_div_callable_code_v5`. -/
theorem evm_div_callable_code_v5_ret_sub {base : Word} :
    ∀ a i, (CodeReq.singleton (base + nopOff) (.JALR .x0 .x1 0)) a = some i →
      (evm_div_callable_code_v5 base) a = some i := by
  intro a i h
  apply callable_b12_div_v5
  unfold cc_ret_code cc_ret
  simpa [CodeReq.ofProg] using h

/-- `divCode_noNop_v5 ⊆ evm_div_callable_code_v5`: the callable v5 DIV code is
    the exact v5 no-NOP DIV body followed by the callable return. -/
theorem divCode_noNop_v5_sub_div_callable_code_v5 {base : Word} :
    ∀ a i, (divCode_noNop_v5 base) a = some i →
           (evm_div_callable_code_v5 base) a = some i := by
  unfold divCode_noNop_v5; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono callable_b0_div_v5
    (CodeReq.union_split_mono callable_b1_div_v5
    (CodeReq.union_split_mono callable_b2_div_v5
    (CodeReq.union_split_mono callable_b3_div_v5
    (CodeReq.union_split_mono callable_b4_div_v5
    (CodeReq.union_split_mono callable_b5_div_v5
    (CodeReq.union_split_mono callable_b6_div_v5
    (CodeReq.union_split_mono callable_b7_div_v5
    (CodeReq.union_split_mono callable_b8_div_v5
    (CodeReq.union_split_mono callable_b9_div_v5
    (CodeReq.union_split_mono callable_b10_div_v5
    (CodeReq.union_split_mono callable_b11_div_v5
    (CodeReq.union_split_mono callable_b13_div_v5
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))

/-- v5 callable DIV wrapper: append the `cc_ret` return to an x1/x9-preserving
    v5 no-NOP body proof (callable post `divStackDispatchPostCallable ** x1`,
    plus exact `x9`).  Mechanical mirror of the v4
    `evm_div_callable_v4_spec_from_noNop_preserving_x1_x9`. -/
theorem evm_div_callable_v5_spec_from_noNop_preserving_x1_x9
    (sp base x9Val raVal : Word) (a b : EvmWord)
    (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        ((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
          (.x9 ↦ᵣ x9Val))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      ((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) := by
  have hStackCall :=
    cpsTripleWithin_extend_code
      (hmono := divCode_noNop_v5_sub_div_callable_code_v5) hStack
  have hStackForRet :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (evm_div_callable_code_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        ((divStackDispatchPostCallable sp a b ** (.x9 ↦ᵣ x9Val)) **
          (.x1 ↦ᵣ raVal)) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp) hStackCall
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v5_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (divStackDispatchPostCallable sp a b ** (.x9 ↦ᵣ x9Val))
      (by
        rw [divStackDispatchPostCallable_unfold, divScratchOwnCallNoX1_unfold,
          divScratchOwn_unfold]
        pcFree)
      hRet
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_same_cr hStackForRet hRetFramed)

/-- Named-post variant of the v5 callable DIV wrapper, landing the public
    `divStackDispatchPostCallableExactFrame`. -/
theorem evm_div_callable_v5_spec_from_noNop_exact_frame
    (sp base x9Val raVal : Word) (a b : EvmWord)
    (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPostCallableExactFrame sp a b raVal x9Val)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divStackDispatchPostCallableExactFrame sp a b raVal x9Val) := by
  rw [divStackDispatchPostCallableExactFrame_unfold] at hStack ⊢
  exact evm_div_callable_v5_spec_from_noNop_preserving_x1_x9
    sp base x9Val raVal a b v2 v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 hStack

end EvmAsm.Evm64
