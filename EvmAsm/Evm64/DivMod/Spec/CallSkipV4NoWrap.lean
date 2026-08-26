/-
  EvmAsm.Evm64.DivMod.Spec.CallSkipV4NoWrap

  Predicate-packaged surfaces for the v4 n=4 call+skip no-wrap branch.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.CallSkipV4

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- EvmWord-level certificate for the v4 call+skip no-wrap branch plus the
    supplied 128/64 upper bound used by the exact-quotient adapter. -/
def n4CallSkipNoWrapLeV4 (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  (divKTrialCallV4Q1dd u4 u3 b3').toNat *
      (divKTrialCallV4DLo b3').toNat ≤
    ((divKTrialCallV4Rhatdd u4 u3 b3').toNat % 2^32) * 2^32 +
      (divKTrialCallV4Un1 u3).toNat ∧
  (div128Quot_v4 u4 u3 b3').toNat ≤
    (u4.toNat * 2^64 + u3.toNat) / b3'.toNat

/-- EvmWord-level certificate for the v4 call+skip no-wrap branch.

    Unlike `n4CallSkipNoWrapLeV4`, this is the runtime branch evidence alone.
    The v4 lower-bound path can consume it directly; the older `Le` predicate
    is only needed by exact-quotient/upper-bound surfaces. -/
def n4CallSkipNoWrapV4 (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  (divKTrialCallV4Q1dd u4 u3 b3').toNat *
      (divKTrialCallV4DLo b3').toNat ≤
    ((divKTrialCallV4Rhatdd u4 u3 b3').toNat % 2^32) * 2^32 +
      (divKTrialCallV4Un1 u3).toNat

/-- Final Phase-1b runtime certificate for the v4 call+skip path: either the
    high half of `rhatdd` is zero, or the low-half no-wrap branch is selected.
    This is the branch split needed by the lower-bound semantic proof. -/
def n4CallSkipRuntimeBranchV4 (a b : EvmWord) : Prop :=
  n4CallSkipRhatddHiZeroV4 a b ∨ n4CallSkipNoWrapV4 a b

/-- Final Phase-1b certificate for the v4 call+skip path: either the high
    half of `rhatdd` is zero, or the low-half no-wrap plus upper-bound facts
    needed by the exact-quotient adapter are available. -/
def n4CallSkipBranchV4 (a b : EvmWord) : Prop :=
  n4CallSkipRhatddHiZeroV4 a b ∨ n4CallSkipNoWrapLeV4 a b

theorem n4CallSkipNoWrapV4_def {a b : EvmWord} :
    n4CallSkipNoWrapV4 a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     (divKTrialCallV4Q1dd u4 u3 b3').toNat *
         (divKTrialCallV4DLo b3').toNat ≤
       ((divKTrialCallV4Rhatdd u4 u3 b3').toNat % 2^32) * 2^32 +
         (divKTrialCallV4Un1 u3).toNat) :=
  rfl

theorem n4CallSkipRuntimeBranchV4_def {a b : EvmWord} :
    n4CallSkipRuntimeBranchV4 a b =
      (n4CallSkipRhatddHiZeroV4 a b ∨ n4CallSkipNoWrapV4 a b) :=
  rfl

theorem n4CallSkipNoWrapLeV4_def {a b : EvmWord} :
    n4CallSkipNoWrapLeV4 a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     (divKTrialCallV4Q1dd u4 u3 b3').toNat *
         (divKTrialCallV4DLo b3').toNat ≤
       ((divKTrialCallV4Rhatdd u4 u3 b3').toNat % 2^32) * 2^32 +
         (divKTrialCallV4Un1 u3).toNat ∧
     (div128Quot_v4 u4 u3 b3').toNat ≤
       (u4.toNat * 2^64 + u3.toNat) / b3'.toNat) :=
  rfl

theorem n4CallSkipBranchV4_def {a b : EvmWord} :
    n4CallSkipBranchV4 a b =
      (n4CallSkipRhatddHiZeroV4 a b ∨ n4CallSkipNoWrapLeV4 a b) :=
  rfl

theorem n4CallSkipNoWrapV4_of_no_wrap_le {a b : EvmWord}
    (h_no_wrap_le : n4CallSkipNoWrapLeV4 a b) :
    n4CallSkipNoWrapV4 a b := by
  rw [n4CallSkipNoWrapLeV4_def] at h_no_wrap_le
  rw [n4CallSkipNoWrapV4_def]
  exact h_no_wrap_le.1

theorem n4CallSkipRuntimeBranchV4_of_branch_pred {a b : EvmWord}
    (hbranch : n4CallSkipBranchV4 a b) :
    n4CallSkipRuntimeBranchV4 a b := by
  rw [n4CallSkipBranchV4_def] at hbranch
  rw [n4CallSkipRuntimeBranchV4_def]
  cases hbranch with
  | inl hrhat => exact Or.inl hrhat
  | inr h_no_wrap_le =>
      exact Or.inr (n4CallSkipNoWrapV4_of_no_wrap_le h_no_wrap_le)

/-- Predicate-packaged v4 call-skip semantic lower bound in the runtime
    no-wrap branch, without a separate 128/64 upper-bound premise. -/
theorem n4CallSkipSemanticHoldsV4_of_no_wrap_pred (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_no_wrap : n4CallSkipNoWrapV4 a b) :
    n4CallSkipSemanticHoldsV4 a b := by
  rw [n4CallSkipNoWrapV4_def] at h_no_wrap
  exact n4CallSkipSemanticHoldsV4_of_runtime_no_wrap a b
    hb3nz hshift_nz h_no_wrap

/-- Predicate-packaged v4 call-skip semantic lower bound for the runtime
    Phase-1b branch split. -/
theorem n4CallSkipSemanticHoldsV4_of_runtime_branch_pred (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbranch : n4CallSkipRuntimeBranchV4 a b) :
    n4CallSkipSemanticHoldsV4 a b := by
  rw [n4CallSkipRuntimeBranchV4_def] at hbranch
  cases hbranch with
  | inl hrhat =>
      exact n4CallSkipSemanticHoldsV4_of_rhatdd_hi_zero_pred a b
        hb3nz hshift_nz hrhat
  | inr h_no_wrap =>
      exact n4CallSkipSemanticHoldsV4_of_no_wrap_pred a b
        hb3nz hshift_nz h_no_wrap


/-- Val256 lower-bound surface for the runtime no-wrap branch, phrased
    directly over the canonical `getLimbN` normalized 128/64 quotient. -/
theorem div128Quot_v4_call_skip_ge_val256_div_of_no_wrap_pred_getLimbN
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_no_wrap : n4CallSkipNoWrapV4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3prime := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
      (div128Quot_v4 u4 u3 b3prime).toNat := by
  intro shift antiShift b3prime u4 u3
  have hsem := n4CallSkipSemanticHoldsV4_of_no_wrap_pred a b
    hb3nz hshift_nz h_no_wrap
  rw [n4CallSkipSemanticHoldsV4_def] at hsem
  exact hsem

/-- Val256 lower-bound surface for the final runtime Phase-1b branch split.
    This is the explicit normalized-quotient form of
    `n4CallSkipSemanticHoldsV4_of_runtime_branch_pred`. -/
theorem div128Quot_v4_call_skip_ge_val256_div_of_runtime_branch_pred_getLimbN
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbranch : n4CallSkipRuntimeBranchV4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3prime := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
      (div128Quot_v4 u4 u3 b3prime).toNat := by
  intro shift antiShift b3prime u4 u3
  have hsem := n4CallSkipSemanticHoldsV4_of_runtime_branch_pred a b
    hb3nz hshift_nz hbranch
  rw [n4CallSkipSemanticHoldsV4_def] at hsem
  exact hsem

/-- Predicate-packaged v4 call-skip semantic lower bound in the no-wrap branch. -/
theorem n4CallSkipSemanticHoldsV4_of_no_wrap_le_pred (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_no_wrap_le : n4CallSkipNoWrapLeV4 a b) :
    n4CallSkipSemanticHoldsV4 a b := by
  rw [n4CallSkipNoWrapLeV4_def] at h_no_wrap_le
  exact n4CallSkipSemanticHoldsV4_of_runtime_no_wrap_of_le a b
    hb3nz hshift_nz h_no_wrap_le.1 h_no_wrap_le.2

/-- Predicate-packaged v4 call-skip semantic lower bound for the final
    Phase-1b branch split. -/
theorem n4CallSkipSemanticHoldsV4_of_branch_pred (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbranch : n4CallSkipBranchV4 a b) :
    n4CallSkipSemanticHoldsV4 a b := by
  rw [n4CallSkipBranchV4_def] at hbranch
  cases hbranch with
  | inl hrhat =>
      exact n4CallSkipSemanticHoldsV4_of_rhatdd_hi_zero_pred a b
        hb3nz hshift_nz hrhat
  | inr h_no_wrap_le =>
      exact n4CallSkipSemanticHoldsV4_of_no_wrap_le_pred a b
        hb3nz hshift_nz h_no_wrap_le

/-- Predicate-packaged v4 getLimbN bridge in the runtime no-wrap branch,
    without a separate 128/64 upper-bound premise. -/
theorem n4_call_skip_div_mod_getLimbN_v4_of_no_wrap_pred_hb3nz
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (h_no_wrap : n4CallSkipNoWrapV4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let qHat := div128Quot_v4 u4 u3 b3'
    (EvmWord.div a b).getLimbN 0 = qHat ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  exact n4_call_skip_div_mod_getLimbN_v4 a b
    (evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz)
    hshift_nz hborrow
    (n4CallSkipSemanticHoldsV4_of_no_wrap_pred a b
      hb3nz hshift_nz h_no_wrap)

/-- Predicate-packaged v4 getLimbN bridge for the runtime Phase-1b branch split. -/
theorem n4_call_skip_div_mod_getLimbN_v4_of_runtime_branch_pred_hb3nz
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hbranch : n4CallSkipRuntimeBranchV4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let qHat := div128Quot_v4 u4 u3 b3'
    (EvmWord.div a b).getLimbN 0 = qHat ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  rw [n4CallSkipRuntimeBranchV4_def] at hbranch
  cases hbranch with
  | inl hrhat =>
      exact n4_call_skip_div_mod_getLimbN_v4_of_rhatdd_hi_zero_pred_hb3nz a b
        hb3nz hshift_nz hborrow hrhat
  | inr h_no_wrap =>
      exact n4_call_skip_div_mod_getLimbN_v4_of_no_wrap_pred_hb3nz a b
        hb3nz hshift_nz hborrow h_no_wrap


/-- Predicate-packaged bundled v4 call+skip stack wrapper in the runtime
    no-wrap branch, without a separate 128/64 upper-bound premise. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_no_wrap_pred_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (h_no_wrap : n4CallSkipNoWrapV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  rw [n4CallSkipNoWrapV4_def] at h_no_wrap
  have hbnz : b ≠ 0 := evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz
  have hbltu : isCallTrialN4Evm a b :=
    isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz
  have h_pre := evm_div_n4_full_call_skip_stack_pre_spec_v4 sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4
    u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift :=
    (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3prime := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let u4prime := (a.getLimbN 3) >>> antiShift
  let u3prime := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let qHat := div128Quot_v4 u4prime u3prime b3prime
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    n4_call_skip_div_mod_getLimbN_v4_of_no_wrap_pred_hb3nz a b
      hb3nz hshift_nz hborrow (by
        rw [n4CallSkipNoWrapV4_def]
        exact h_no_wrap)
  refine cpsTripleWithin_weaken (fun _ hp => by
    rw [divN4StackPreCall_unfold] at hp
    xperm_hyp hp) ?_ h_pre
  intro h hq
  simp only [fullDivN4CallSkipPostV4_div128Quot_unfold, denormDivPost_unfold] at hq
  apply sepConj_mono_right memIs_implies_memOwn h
  apply sepConj_mono_left (div_n4_call_skip_stack_weaken sp a b) h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) =
      (((sp + 32) ↦ₘ qHat) **
       ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) **
       ((sp + 56) ↦ₘ (0 : Word)))
      from by rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
                  hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

/-- Predicate-packaged bundled v4 call+skip stack wrapper for the runtime
    Phase-1b branch split. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_runtime_branch_pred_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hbranch : n4CallSkipRuntimeBranchV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  rw [n4CallSkipRuntimeBranchV4_def] at hbranch
  cases hbranch with
  | inl hrhat =>
      exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_rhatdd_hi_zero_pred_hb3nz
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hb3nz hshift_nz halign hborrow hrhat
  | inr h_no_wrap =>
      exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_no_wrap_pred_hb3nz
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hb3nz hshift_nz halign hborrow h_no_wrap


/-- Predicate-packaged bundled no-NOP v4 call+skip stack wrapper in the runtime
    no-wrap branch, without a separate 128/64 upper-bound premise. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_no_wrap_pred_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (h_no_wrap : n4CallSkipNoWrapV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  rw [n4CallSkipNoWrapV4_def] at h_no_wrap
  have hbnz : b ≠ 0 := evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz
  have hbltu : isCallTrialN4Evm a b :=
    isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz
  have h_pre := evm_div_n4_full_call_skip_stack_pre_spec_v4_noNop sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4
    u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift :=
    (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3prime := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let u4prime := (a.getLimbN 3) >>> antiShift
  let u3prime := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let qHat := div128Quot_v4 u4prime u3prime b3prime
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    n4_call_skip_div_mod_getLimbN_v4_of_no_wrap_pred_hb3nz a b
      hb3nz hshift_nz hborrow (by
        rw [n4CallSkipNoWrapV4_def]
        exact h_no_wrap)
  refine cpsTripleWithin_weaken (fun _ hp => by
    rw [divN4StackPreCall_unfold] at hp
    xperm_hyp hp) ?_ h_pre
  intro h hq
  simp only [fullDivN4CallSkipPostV4_div128Quot_unfold, denormDivPost_unfold] at hq
  apply sepConj_mono_right memIs_implies_memOwn h
  apply sepConj_mono_left (div_n4_call_skip_stack_weaken sp a b) h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) =
      (((sp + 32) ↦ₘ qHat) **
       ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) **
       ((sp + 56) ↦ₘ (0 : Word)))
      from by rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
                  hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

/-- Predicate-packaged bundled no-NOP v4 call+skip stack wrapper for the
    runtime Phase-1b branch split. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_runtime_branch_pred_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hbranch : n4CallSkipRuntimeBranchV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  rw [n4CallSkipRuntimeBranchV4_def] at hbranch
  cases hbranch with
  | inl hrhat =>
      exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_rhatdd_hi_zero_pred_hb3nz
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hb3nz hshift_nz halign hborrow hrhat
  | inr h_no_wrap =>
      exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_no_wrap_pred_hb3nz
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hb3nz hshift_nz halign hborrow h_no_wrap

/-- Predicate-packaged v4 getLimbN bridge in the no-wrap branch. -/
theorem n4_call_skip_div_mod_getLimbN_v4_of_no_wrap_le_pred_hb3nz
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (h_no_wrap_le : n4CallSkipNoWrapLeV4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let qHat := div128Quot_v4 u4 u3 b3'
    (EvmWord.div a b).getLimbN 0 = qHat ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  rw [n4CallSkipNoWrapLeV4_def] at h_no_wrap_le
  exact n4_call_skip_div_mod_getLimbN_v4_of_runtime_no_wrap_of_le_hb3nz a b
    hb3nz hshift_nz hborrow h_no_wrap_le.1 h_no_wrap_le.2

/-- Predicate-packaged v4 getLimbN bridge for the final Phase-1b branch split. -/
theorem n4_call_skip_div_mod_getLimbN_v4_of_branch_pred_hb3nz
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hbranch : n4CallSkipBranchV4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let qHat := div128Quot_v4 u4 u3 b3'
    (EvmWord.div a b).getLimbN 0 = qHat ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  rw [n4CallSkipBranchV4_def] at hbranch
  cases hbranch with
  | inl hrhat =>
      exact n4_call_skip_div_mod_getLimbN_v4_of_rhatdd_hi_zero_pred_hb3nz a b
        hb3nz hshift_nz hborrow hrhat
  | inr h_no_wrap_le =>
      exact n4_call_skip_div_mod_getLimbN_v4_of_no_wrap_le_pred_hb3nz a b
        hb3nz hshift_nz hborrow h_no_wrap_le

/-- Predicate-packaged bundled v4 call+skip stack wrapper in the no-wrap branch. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_no_wrap_le_pred_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (h_no_wrap_le : n4CallSkipNoWrapLeV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  rw [n4CallSkipNoWrapLeV4_def] at h_no_wrap_le
  exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_shift_nz_no_wrap_of_le
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hborrow h_no_wrap_le.1 h_no_wrap_le.2

/-- Predicate-packaged bundled v4 call+skip stack wrapper for the final
    Phase-1b branch split. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_branch_pred_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hbranch : n4CallSkipBranchV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  rw [n4CallSkipBranchV4_def] at hbranch
  cases hbranch with
  | inl hrhat =>
      exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_rhatdd_hi_zero_pred_hb3nz
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hb3nz hshift_nz halign hborrow hrhat
  | inr h_no_wrap_le =>
      exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_no_wrap_le_pred_hb3nz
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hb3nz hshift_nz halign hborrow h_no_wrap_le

/-- Predicate-packaged bundled no-NOP v4 call+skip stack wrapper in the no-wrap branch. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_no_wrap_le_pred_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (h_no_wrap_le : n4CallSkipNoWrapLeV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  rw [n4CallSkipNoWrapLeV4_def] at h_no_wrap_le
  exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_shift_nz_no_wrap_of_le
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hborrow h_no_wrap_le.1 h_no_wrap_le.2

/-- Predicate-packaged bundled no-NOP v4 call+skip stack wrapper for the final
    Phase-1b branch split. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_branch_pred_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hbranch : n4CallSkipBranchV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  rw [n4CallSkipBranchV4_def] at hbranch
  cases hbranch with
  | inl hrhat =>
      exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_rhatdd_hi_zero_pred_hb3nz
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hb3nz hshift_nz halign hborrow hrhat
  | inr h_no_wrap_le =>
      exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_no_wrap_le_pred_hb3nz
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hb3nz hshift_nz halign hborrow h_no_wrap_le

/-- Final-API named v4 call+skip stack spec under the explicit branch
    certificate. The remaining unconditional work is to discharge
    `n4CallSkipBranchV4` from runtime facts. -/
theorem evm_div_n4_call_skip_stack_spec_v4_of_branch_pred_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hbranch : n4CallSkipBranchV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_branch_pred_hb3nz
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hborrow hbranch

/-- No-NOP final-API named v4 call+skip stack spec under the explicit branch
    certificate. -/
theorem evm_div_n4_call_skip_stack_spec_v4_noNop_of_branch_pred_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hbranch : n4CallSkipBranchV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_branch_pred_hb3nz
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hborrow hbranch

/-- Final-API named v4 call+skip stack spec under the runtime branch
    certificate, without the older no-wrap upper-bound side condition. -/
theorem evm_div_n4_call_skip_stack_spec_v4_of_runtime_branch_pred_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hbranch : n4CallSkipRuntimeBranchV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_runtime_branch_pred_hb3nz
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hborrow hbranch

/-- No-NOP final-API named v4 call+skip stack spec under the runtime branch
    certificate. -/
theorem evm_div_n4_call_skip_stack_spec_v4_noNop_of_runtime_branch_pred_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hbranch : n4CallSkipRuntimeBranchV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_runtime_branch_pred_hb3nz
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hborrow hbranch

end EvmAsm.Evm64
