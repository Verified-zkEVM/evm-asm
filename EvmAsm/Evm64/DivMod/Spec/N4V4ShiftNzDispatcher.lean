/-
  EvmAsm.Evm64.DivMod.Spec.N4V4ShiftNzDispatcher

  Dispatcher-level n=4, shift-nonzero DIV v4 wrapper.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntimeHighDiv
public import EvmAsm.Evm64.DivMod.Spec.CallSkipUnconditional
public import EvmAsm.Evm64.DivMod.Spec.CallSkipV4NoWrap
public import EvmAsm.Evm64.DivMod.Spec.N4V4StackPre

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Remaining runtime evidence for the n=4, shift-nonzero DIV v4 dispatcher.

    This packages the call+skip runtime branch certificate, the addback carry2 runtime
    condition, and the compact addback arithmetic bounds as one predicate. -/
def n4ShiftNzDispatcherRuntimeV4 (a b : EvmWord) : Prop :=
  n4CallSkipRuntimeBranchV4 a b ∧
  isAddbackCarry2NzN4CallV4Evm a b ∧
  n4CallAddbackBeqRuntimeBounds a b

/-- Branch-sensitive runtime evidence for the n=4, shift-nonzero DIV v4
    dispatcher.

    Unlike `n4ShiftNzDispatcherRuntimeV4`, this only asks for the addback
    carry/bounds evidence on the addback-borrow branch. -/
def n4ShiftNzDispatcherBranchRuntimeV4 (a b : EvmWord) : Prop :=
  (isSkipBorrowN4CallV4Evm a b ∧ n4CallSkipRuntimeBranchV4 a b) ∨
  (isAddbackBorrowN4CallV4Evm a b ∧
   isAddbackCarry2NzN4CallV4Evm a b ∧
   n4CallAddbackBeqRuntimeBounds a b)

/-- Raw runtime evidence for the n=4, shift-nonzero DIV v4 dispatcher.

    This is the arithmetic-facing counterpart of `n4ShiftNzDispatcherRuntimeV4`:
    the call+skip runtime certificate is global, while the addback side keeps
    the concrete high-div facts instead of a prebuilt runtime-bounds package. -/
def n4ShiftNzDispatcherRuntimeHighDivRawEvidence (a b : EvmWord) : Prop :=
  n4CallSkipRuntimeBranchV4 a b ∧
  isAddbackCarry2NzN4CallV4Evm a b ∧
  divKTrialCallV4Rhatdd
      (n4CallAddbackBeqU4 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
    (0 : Word) ∧
  (n4CallAddbackBeqQHatV4 a b).toNat ≤
    ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
        (n4CallAddbackBeqU3 a b).toNat) /
      (n4CallAddbackBeqB3Prime b).toNat ∧
  ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
      (n4CallAddbackBeqU3 a b).toNat) /
    (n4CallAddbackBeqB3Prime b).toNat ≤
      n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1

/-- Runtime evidence for the n=4, shift-nonzero DIV v4 dispatcher with
    packaged high-div addback evidence. -/
def n4ShiftNzDispatcherRuntimeHighDivEvidence (a b : EvmWord) : Prop :=
  n4CallSkipRuntimeBranchV4 a b ∧
  isAddbackCarry2NzN4CallV4Evm a b ∧
  n4CallAddbackBeqShiftHighDivEvidence a b

/-- Explicit branch/bounds evidence for the n=4, shift-nonzero DIV v4
    dispatcher.

    This is the lightweight shape produced by the arithmetic side of the n=4
    stack assembly before it has been upgraded to the runtime call+skip branch
    certificate. -/
def n4ShiftNzDispatcherBranchBoundsV4 (a b : EvmWord) : Prop :=
  n4CallSkipBranchV4 a b ∧
  isAddbackCarry2NzN4CallV4Evm a b ∧
  n4CallAddbackBeqRuntimeBounds a b

/-- Raw branch-sensitive high-div evidence for the n=4, shift-nonzero DIV
    v4 dispatcher.

    This is the arithmetic-facing form of
    `n4ShiftNzDispatcherBranchHighDivEvidence`: the addback branch carries the
    concrete `rhatdd` high-half-zero fact, the qhat/high-div inequality, and
    the surviving Knuth-A `+1` high-div bound directly. -/
def n4ShiftNzDispatcherBranchHighDivRawEvidence (a b : EvmWord) : Prop :=
  (isSkipBorrowN4CallV4Evm a b ∧ n4CallSkipRuntimeBranchV4 a b) ∨
  (isAddbackBorrowN4CallV4Evm a b ∧
   isAddbackCarry2NzN4CallV4Evm a b ∧
   divKTrialCallV4Rhatdd
       (n4CallAddbackBeqU4 a b)
       (n4CallAddbackBeqU3 a b)
       (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
     (0 : Word) ∧
   (n4CallAddbackBeqQHatV4 a b).toNat ≤
     ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
         (n4CallAddbackBeqU3 a b).toNat) /
       (n4CallAddbackBeqB3Prime b).toNat ∧
   ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
       (n4CallAddbackBeqU3 a b).toNat) /
     (n4CallAddbackBeqB3Prime b).toNat ≤
       n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)

/-- Branch-sensitive high-div evidence for the n=4, shift-nonzero DIV v4
    dispatcher.

    The skip branch carries the runtime call+skip certificate directly; the
    addback branch carries the surviving high-div `+1` evidence package, which
    can be lowered to `n4CallAddbackBeqRuntimeBounds` once the runtime borrow
    branch is known. -/
def n4ShiftNzDispatcherBranchHighDivEvidence (a b : EvmWord) : Prop :=
  (isSkipBorrowN4CallV4Evm a b ∧ n4CallSkipRuntimeBranchV4 a b) ∨
  (isAddbackBorrowN4CallV4Evm a b ∧
   isAddbackCarry2NzN4CallV4Evm a b ∧
   n4CallAddbackBeqShiftHighDivEvidence a b)

/-- Branch-sensitive compact qhat/high-div evidence for the n=4,
    shift-nonzero DIV v4 dispatcher.

    This is the addback-side projection of
    `n4ShiftNzDispatcherBranchHighDivEvidence`: the skip branch is unchanged,
    while the addback branch carries only the compact direct qhat/high-div
    evidence package. -/
def n4ShiftNzDispatcherBranchQHatHighDivEvidence (a b : EvmWord) : Prop :=
  (isSkipBorrowN4CallV4Evm a b ∧ n4CallSkipRuntimeBranchV4 a b) ∨
  (isAddbackBorrowN4CallV4Evm a b ∧
   isAddbackCarry2NzN4CallV4Evm a b ∧
   n4CallAddbackBeqRuntimeQHatHighDivEvidence a b)

theorem n4ShiftNzDispatcherRuntimeV4_def {a b : EvmWord} :
    n4ShiftNzDispatcherRuntimeV4 a b =
      (n4CallSkipRuntimeBranchV4 a b ∧
       isAddbackCarry2NzN4CallV4Evm a b ∧
       n4CallAddbackBeqRuntimeBounds a b) :=
  rfl

theorem n4ShiftNzDispatcherBranchRuntimeV4_def {a b : EvmWord} :
    n4ShiftNzDispatcherBranchRuntimeV4 a b =
      ((isSkipBorrowN4CallV4Evm a b ∧ n4CallSkipRuntimeBranchV4 a b) ∨
       (isAddbackBorrowN4CallV4Evm a b ∧
        isAddbackCarry2NzN4CallV4Evm a b ∧
        n4CallAddbackBeqRuntimeBounds a b)) :=
  rfl

theorem n4ShiftNzDispatcherRuntimeHighDivRawEvidence_def {a b : EvmWord} :
    n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b =
      (n4CallSkipRuntimeBranchV4 a b ∧
       isAddbackCarry2NzN4CallV4Evm a b ∧
       divKTrialCallV4Rhatdd
           (n4CallAddbackBeqU4 a b)
           (n4CallAddbackBeqU3 a b)
           (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
         (0 : Word) ∧
       (n4CallAddbackBeqQHatV4 a b).toNat ≤
         ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
             (n4CallAddbackBeqU3 a b).toNat) /
           (n4CallAddbackBeqB3Prime b).toNat ∧
       ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
           (n4CallAddbackBeqU3 a b).toNat) /
         (n4CallAddbackBeqB3Prime b).toNat ≤
           n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1) :=
  rfl

theorem n4ShiftNzDispatcherRuntimeHighDivEvidence_def {a b : EvmWord} :
    n4ShiftNzDispatcherRuntimeHighDivEvidence a b =
      (n4CallSkipRuntimeBranchV4 a b ∧
       isAddbackCarry2NzN4CallV4Evm a b ∧
       n4CallAddbackBeqShiftHighDivEvidence a b) :=
  rfl

theorem n4ShiftNzDispatcherBranchBoundsV4_def {a b : EvmWord} :
    n4ShiftNzDispatcherBranchBoundsV4 a b =
      (n4CallSkipBranchV4 a b ∧
       isAddbackCarry2NzN4CallV4Evm a b ∧
       n4CallAddbackBeqRuntimeBounds a b) :=
  rfl

theorem n4ShiftNzDispatcherBranchHighDivEvidence_def {a b : EvmWord} :
    n4ShiftNzDispatcherBranchHighDivEvidence a b =
      ((isSkipBorrowN4CallV4Evm a b ∧ n4CallSkipRuntimeBranchV4 a b) ∨
       (isAddbackBorrowN4CallV4Evm a b ∧
        isAddbackCarry2NzN4CallV4Evm a b ∧
        n4CallAddbackBeqShiftHighDivEvidence a b)) :=
  rfl

theorem n4ShiftNzDispatcherBranchHighDivRawEvidence_def {a b : EvmWord} :
    n4ShiftNzDispatcherBranchHighDivRawEvidence a b =
      ((isSkipBorrowN4CallV4Evm a b ∧ n4CallSkipRuntimeBranchV4 a b) ∨
       (isAddbackBorrowN4CallV4Evm a b ∧
        isAddbackCarry2NzN4CallV4Evm a b ∧
        divKTrialCallV4Rhatdd
            (n4CallAddbackBeqU4 a b)
            (n4CallAddbackBeqU3 a b)
            (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
          (0 : Word) ∧
        (n4CallAddbackBeqQHatV4 a b).toNat ≤
          ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
              (n4CallAddbackBeqU3 a b).toNat) /
            (n4CallAddbackBeqB3Prime b).toNat ∧
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat ≤
            n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)) :=
  rfl

theorem n4ShiftNzDispatcherBranchBoundsV4.callSkipBranch {a b : EvmWord}
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    n4CallSkipBranchV4 a b := by
  rw [n4ShiftNzDispatcherBranchBoundsV4_def] at hevidence
  exact hevidence.1

theorem n4ShiftNzDispatcherBranchBoundsV4.addbackCarry2 {a b : EvmWord}
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    isAddbackCarry2NzN4CallV4Evm a b := by
  rw [n4ShiftNzDispatcherBranchBoundsV4_def] at hevidence
  exact hevidence.2.1

theorem n4ShiftNzDispatcherBranchBoundsV4.addbackRuntimeBounds {a b : EvmWord}
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    n4CallAddbackBeqRuntimeBounds a b := by
  rw [n4ShiftNzDispatcherBranchBoundsV4_def] at hevidence
  exact hevidence.2.2

theorem n4ShiftNzDispatcherBranchBoundsV4.of_parts {a b : EvmWord}
    (hbranch : n4CallSkipBranchV4 a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_bounds : n4CallAddbackBeqRuntimeBounds a b) :
    n4ShiftNzDispatcherBranchBoundsV4 a b := by
  rw [n4ShiftNzDispatcherBranchBoundsV4_def]
  exact ⟨hbranch, hcarry2, h_bounds⟩

theorem n4ShiftNzDispatcherBranchBoundsV4.of_runtime_pred {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b)
    (hbranch : n4CallSkipBranchV4 a b) :
    n4ShiftNzDispatcherBranchBoundsV4 a b := by
  rw [n4ShiftNzDispatcherRuntimeV4_def] at hruntime
  rw [n4ShiftNzDispatcherBranchBoundsV4_def]
  exact ⟨hbranch, hruntime.2.1, hruntime.2.2⟩

theorem n4ShiftNzDispatcherBranchRuntimeV4.skip {a b : EvmWord}
    (hskip : isSkipBorrowN4CallV4Evm a b)
    (hbranch : n4CallSkipRuntimeBranchV4 a b) :
    n4ShiftNzDispatcherBranchRuntimeV4 a b := by
  rw [n4ShiftNzDispatcherBranchRuntimeV4_def]
  exact Or.inl ⟨hskip, hbranch⟩

theorem n4ShiftNzDispatcherBranchRuntimeV4.addback {a b : EvmWord}
    (hadd : isAddbackBorrowN4CallV4Evm a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_bounds : n4CallAddbackBeqRuntimeBounds a b) :
    n4ShiftNzDispatcherBranchRuntimeV4 a b := by
  rw [n4ShiftNzDispatcherBranchRuntimeV4_def]
  exact Or.inr ⟨hadd, hcarry2, h_bounds⟩

theorem n4ShiftNzDispatcherRuntimeV4.of_parts {a b : EvmWord}
    (hbranch : n4CallSkipRuntimeBranchV4 a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_bounds : n4CallAddbackBeqRuntimeBounds a b) :
    n4ShiftNzDispatcherRuntimeV4 a b := by
  rw [n4ShiftNzDispatcherRuntimeV4_def]
  exact ⟨hbranch, hcarry2, h_bounds⟩

theorem n4ShiftNzDispatcherRuntimeV4.callSkipRuntimeBranch {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b) :
    n4CallSkipRuntimeBranchV4 a b := by
  rw [n4ShiftNzDispatcherRuntimeV4_def] at hruntime
  exact hruntime.1

theorem n4ShiftNzDispatcherRuntimeV4.addbackCarry2 {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b) :
    isAddbackCarry2NzN4CallV4Evm a b := by
  rw [n4ShiftNzDispatcherRuntimeV4_def] at hruntime
  exact hruntime.2.1

theorem n4ShiftNzDispatcherRuntimeV4.addbackRuntimeBounds {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b) :
    n4CallAddbackBeqRuntimeBounds a b := by
  rw [n4ShiftNzDispatcherRuntimeV4_def] at hruntime
  exact hruntime.2.2

theorem n4ShiftNzDispatcherRuntimeV4.of_branch_bounds {a b : EvmWord}
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    n4ShiftNzDispatcherRuntimeV4 a b := by
  rw [n4ShiftNzDispatcherBranchBoundsV4_def] at hevidence
  rw [n4ShiftNzDispatcherRuntimeV4_def]
  exact ⟨n4CallSkipRuntimeBranchV4_of_branch_pred hevidence.1, hevidence.2.1, hevidence.2.2⟩

theorem n4ShiftNzDispatcherBranchRuntimeV4_of_runtime_pred {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b) :
    n4ShiftNzDispatcherBranchRuntimeV4 a b := by
  rw [n4ShiftNzDispatcherRuntimeV4_def] at hruntime
  cases isSkipBorrowN4CallV4Evm_or_isAddbackBorrowN4CallV4Evm a b with
  | inl hskip =>
      exact n4ShiftNzDispatcherBranchRuntimeV4.skip hskip hruntime.1
  | inr hadd =>
      exact n4ShiftNzDispatcherBranchRuntimeV4.addback hadd hruntime.2.1 hruntime.2.2

theorem n4ShiftNzDispatcherBranchRuntimeV4_of_branch_bounds {a b : EvmWord}
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    n4ShiftNzDispatcherBranchRuntimeV4 a b :=
  n4ShiftNzDispatcherBranchRuntimeV4_of_runtime_pred
    (n4ShiftNzDispatcherRuntimeV4.of_branch_bounds hevidence)

theorem n4ShiftNzDispatcherBranchBoundsV4.toRuntimeV4 {a b : EvmWord}
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    n4ShiftNzDispatcherRuntimeV4 a b :=
  n4ShiftNzDispatcherRuntimeV4.of_branch_bounds hevidence

theorem n4ShiftNzDispatcherBranchBoundsV4.toBranchRuntime {a b : EvmWord}
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    n4ShiftNzDispatcherBranchRuntimeV4 a b :=
  n4ShiftNzDispatcherBranchRuntimeV4_of_branch_bounds hevidence

theorem n4ShiftNzDispatcherBranchHighDivEvidence.skip {a b : EvmWord}
    (hskip : isSkipBorrowN4CallV4Evm a b)
    (hbranch : n4CallSkipRuntimeBranchV4 a b) :
    n4ShiftNzDispatcherBranchHighDivEvidence a b := by
  rw [n4ShiftNzDispatcherBranchHighDivEvidence_def]
  exact Or.inl ⟨hskip, hbranch⟩

theorem n4ShiftNzDispatcherBranchHighDivEvidence.addback {a b : EvmWord}
    (hadd : isAddbackBorrowN4CallV4Evm a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (hevidence : n4CallAddbackBeqShiftHighDivEvidence a b) :
    n4ShiftNzDispatcherBranchHighDivEvidence a b := by
  rw [n4ShiftNzDispatcherBranchHighDivEvidence_def]
  exact Or.inr ⟨hadd, hcarry2, hevidence⟩

theorem n4ShiftNzDispatcherBranchHighDivEvidence.addbackRaw {a b : EvmWord}
    (hadd : isAddbackBorrowN4CallV4Evm a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1) :
    n4ShiftNzDispatcherBranchHighDivEvidence a b :=
  n4ShiftNzDispatcherBranchHighDivEvidence.addback hadd hcarry2
    (n4CallAddbackBeqShiftHighDivEvidence.of_raw_parts
      h_rhat_hi_zero h_qhat_le_high_div h_high_div_le_norm_plus_one)

theorem n4ShiftNzDispatcherBranchRuntimeV4_of_high_div_evidence {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hevidence : n4ShiftNzDispatcherBranchHighDivEvidence a b) :
    n4ShiftNzDispatcherBranchRuntimeV4 a b := by
  rw [n4ShiftNzDispatcherBranchHighDivEvidence_def] at hevidence
  cases hevidence with
  | inl hskip =>
      exact n4ShiftNzDispatcherBranchRuntimeV4.skip hskip.1 hskip.2
  | inr hadd =>
      exact n4ShiftNzDispatcherBranchRuntimeV4.addback hadd.1 hadd.2.1
        (n4CallAddbackBeqRuntimeBounds_of_shift_high_div_evidence_and_borrow
          hb3nz hshift_nz hadd.2.2 hadd.1)

theorem n4ShiftNzDispatcherBranchHighDivRawEvidence.skip {a b : EvmWord}
    (hskip : isSkipBorrowN4CallV4Evm a b)
    (hbranch : n4CallSkipRuntimeBranchV4 a b) :
    n4ShiftNzDispatcherBranchHighDivRawEvidence a b := by
  rw [n4ShiftNzDispatcherBranchHighDivRawEvidence_def]
  exact Or.inl ⟨hskip, hbranch⟩

theorem n4ShiftNzDispatcherBranchHighDivRawEvidence.addback {a b : EvmWord}
    (hadd : isAddbackBorrowN4CallV4Evm a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1) :
    n4ShiftNzDispatcherBranchHighDivRawEvidence a b := by
  rw [n4ShiftNzDispatcherBranchHighDivRawEvidence_def]
  exact Or.inr
    ⟨hadd, hcarry2, h_rhat_hi_zero, h_qhat_le_high_div, h_high_div_le_norm_plus_one⟩

theorem n4ShiftNzDispatcherBranchHighDivEvidence_of_raw {a b : EvmWord}
    (hevidence : n4ShiftNzDispatcherBranchHighDivRawEvidence a b) :
    n4ShiftNzDispatcherBranchHighDivEvidence a b := by
  rw [n4ShiftNzDispatcherBranchHighDivRawEvidence_def] at hevidence
  cases hevidence with
  | inl hskip =>
      exact n4ShiftNzDispatcherBranchHighDivEvidence.skip hskip.1 hskip.2
  | inr hadd =>
      exact n4ShiftNzDispatcherBranchHighDivEvidence.addbackRaw
        hadd.1 hadd.2.1 hadd.2.2.1 hadd.2.2.2.1 hadd.2.2.2.2

theorem n4ShiftNzDispatcherBranchRuntimeV4_of_high_div_raw_evidence {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hevidence : n4ShiftNzDispatcherBranchHighDivRawEvidence a b) :
    n4ShiftNzDispatcherBranchRuntimeV4 a b :=
  n4ShiftNzDispatcherBranchRuntimeV4_of_high_div_evidence
    hb3nz hshift_nz
    (n4ShiftNzDispatcherBranchHighDivEvidence_of_raw hevidence)

theorem n4ShiftNzDispatcherRuntimeHighDivEvidence.of_parts {a b : EvmWord}
    (hbranch : n4CallSkipRuntimeBranchV4 a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (hevidence : n4CallAddbackBeqShiftHighDivEvidence a b) :
    n4ShiftNzDispatcherRuntimeHighDivEvidence a b := by
  rw [n4ShiftNzDispatcherRuntimeHighDivEvidence_def]
  exact ⟨hbranch, hcarry2, hevidence⟩

theorem n4ShiftNzDispatcherRuntimeHighDivEvidence.callSkipRuntimeBranch {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivEvidence a b) :
    n4CallSkipRuntimeBranchV4 a b := by
  rw [n4ShiftNzDispatcherRuntimeHighDivEvidence_def] at hruntime
  exact hruntime.1

theorem n4ShiftNzDispatcherRuntimeHighDivEvidence.addbackCarry2 {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivEvidence a b) :
    isAddbackCarry2NzN4CallV4Evm a b := by
  rw [n4ShiftNzDispatcherRuntimeHighDivEvidence_def] at hruntime
  exact hruntime.2.1

theorem n4ShiftNzDispatcherRuntimeHighDivEvidence.addbackHighDivEvidence {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivEvidence a b) :
    n4CallAddbackBeqShiftHighDivEvidence a b := by
  rw [n4ShiftNzDispatcherRuntimeHighDivEvidence_def] at hruntime
  exact hruntime.2.2

theorem n4ShiftNzDispatcherRuntimeHighDivEvidence.addbackRuntimeBounds {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivEvidence a b)
    (hadd : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqRuntimeBounds a b :=
  n4CallAddbackBeqRuntimeBounds_of_shift_high_div_evidence_and_borrow
    hb3nz hshift_nz
    (n4ShiftNzDispatcherRuntimeHighDivEvidence.addbackHighDivEvidence hruntime)
    hadd

theorem n4ShiftNzDispatcherRuntimeHighDivEvidence.semanticHoldsV4 {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivEvidence a b)
    (hadd : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_shift_runtime_high_div_evidence
    hb3nz hshift_nz
    (n4ShiftNzDispatcherRuntimeHighDivEvidence.addbackHighDivEvidence hruntime)
    hadd
    (n4ShiftNzDispatcherRuntimeHighDivEvidence.addbackCarry2 hruntime)

theorem n4ShiftNzDispatcherRuntimeHighDivEvidence.semanticHolds {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivEvidence a b)
    (hadd : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4ShiftNzDispatcherRuntimeHighDivEvidence.semanticHoldsV4
      hb3nz hshift_nz hruntime hadd

theorem n4ShiftNzDispatcherRuntimeHighDivEvidence_of_raw {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b) :
    n4ShiftNzDispatcherRuntimeHighDivEvidence a b := by
  rw [n4ShiftNzDispatcherRuntimeHighDivRawEvidence_def] at hruntime
  exact n4ShiftNzDispatcherRuntimeHighDivEvidence.of_parts
    hruntime.1 hruntime.2.1
    (n4CallAddbackBeqShiftHighDivEvidence.of_raw_parts
      hruntime.2.2.1 hruntime.2.2.2.1 hruntime.2.2.2.2)

theorem n4ShiftNzDispatcherBranchHighDivEvidence_of_runtime_high_div {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivEvidence a b) :
    n4ShiftNzDispatcherBranchHighDivEvidence a b := by
  rw [n4ShiftNzDispatcherRuntimeHighDivEvidence_def] at hruntime
  cases isSkipBorrowN4CallV4Evm_or_isAddbackBorrowN4CallV4Evm a b with
  | inl hskip =>
      exact n4ShiftNzDispatcherBranchHighDivEvidence.skip hskip hruntime.1
  | inr hadd =>
      exact n4ShiftNzDispatcherBranchHighDivEvidence.addback
        hadd hruntime.2.1 hruntime.2.2

theorem n4ShiftNzDispatcherBranchRuntimeV4_of_runtime_high_div {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivEvidence a b) :
    n4ShiftNzDispatcherBranchRuntimeV4 a b :=
  n4ShiftNzDispatcherBranchRuntimeV4_of_high_div_evidence
    hb3nz hshift_nz
    (n4ShiftNzDispatcherBranchHighDivEvidence_of_runtime_high_div hruntime)

theorem n4ShiftNzDispatcherRuntimeHighDivRawEvidence.of_parts {a b : EvmWord}
    (hbranch : n4CallSkipRuntimeBranchV4 a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1) :
    n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b := by
  rw [n4ShiftNzDispatcherRuntimeHighDivRawEvidence_def]
  exact ⟨hbranch, hcarry2, h_rhat_hi_zero, h_qhat_le_high_div, h_high_div_le_norm_plus_one⟩

theorem n4ShiftNzDispatcherRuntimeHighDivRawEvidence.callSkipRuntimeBranch {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b) :
    n4CallSkipRuntimeBranchV4 a b := by
  rw [n4ShiftNzDispatcherRuntimeHighDivRawEvidence_def] at hruntime
  exact hruntime.1

theorem n4ShiftNzDispatcherRuntimeHighDivRawEvidence.addbackCarry2 {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b) :
    isAddbackCarry2NzN4CallV4Evm a b := by
  rw [n4ShiftNzDispatcherRuntimeHighDivRawEvidence_def] at hruntime
  exact hruntime.2.1

theorem n4ShiftNzDispatcherRuntimeHighDivRawEvidence.addbackHighDivEvidence {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b) :
    n4CallAddbackBeqShiftHighDivEvidence a b :=
  n4ShiftNzDispatcherRuntimeHighDivEvidence.addbackHighDivEvidence
    (n4ShiftNzDispatcherRuntimeHighDivEvidence_of_raw hruntime)

theorem n4ShiftNzDispatcherRuntimeHighDivRawEvidence.addbackRuntimeBounds {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b)
    (hadd : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqRuntimeBounds a b :=
  n4ShiftNzDispatcherRuntimeHighDivEvidence.addbackRuntimeBounds
    hb3nz hshift_nz
    (n4ShiftNzDispatcherRuntimeHighDivEvidence_of_raw hruntime)
    hadd

theorem n4ShiftNzDispatcherRuntimeHighDivRawEvidence.semanticHoldsV4 {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b)
    (hadd : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
by
  rw [n4ShiftNzDispatcherRuntimeHighDivRawEvidence_def] at hruntime
  exact n4CallAddbackBeqSemanticHoldsV4_of_shift_runtime_high_div_raw_parts
    hb3nz hshift_nz hruntime.2.2.1 hruntime.2.2.2.1 hruntime.2.2.2.2
    hadd hruntime.2.1

theorem n4ShiftNzDispatcherRuntimeHighDivRawEvidence.semanticHolds {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b)
    (hadd : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b :=
  n4ShiftNzDispatcherRuntimeHighDivEvidence.semanticHolds
    hb3nz hshift_nz
    (n4ShiftNzDispatcherRuntimeHighDivEvidence_of_raw hruntime)
    hadd

theorem n4ShiftNzDispatcherBranchHighDivRawEvidence_of_runtime_raw {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b) :
    n4ShiftNzDispatcherBranchHighDivRawEvidence a b := by
  rw [n4ShiftNzDispatcherRuntimeHighDivRawEvidence_def] at hruntime
  cases isSkipBorrowN4CallV4Evm_or_isAddbackBorrowN4CallV4Evm a b with
  | inl hskip =>
      exact n4ShiftNzDispatcherBranchHighDivRawEvidence.skip hskip hruntime.1
  | inr hadd =>
      exact n4ShiftNzDispatcherBranchHighDivRawEvidence.addback
        hadd hruntime.2.1 hruntime.2.2.1 hruntime.2.2.2.1 hruntime.2.2.2.2

theorem n4ShiftNzDispatcherBranchRuntimeV4_of_runtime_high_div_raw {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b) :
    n4ShiftNzDispatcherBranchRuntimeV4 a b :=
  n4ShiftNzDispatcherBranchRuntimeV4_of_high_div_raw_evidence
    hb3nz hshift_nz
    (n4ShiftNzDispatcherBranchHighDivRawEvidence_of_runtime_raw hruntime)

theorem n4ShiftNzDispatcherBranchHighDivEvidence.toBranchRuntime {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hevidence : n4ShiftNzDispatcherBranchHighDivEvidence a b) :
    n4ShiftNzDispatcherBranchRuntimeV4 a b :=
  n4ShiftNzDispatcherBranchRuntimeV4_of_high_div_evidence
    hb3nz hshift_nz hevidence

theorem n4ShiftNzDispatcherBranchHighDivRawEvidence.toHighDivEvidence {a b : EvmWord}
    (hevidence : n4ShiftNzDispatcherBranchHighDivRawEvidence a b) :
    n4ShiftNzDispatcherBranchHighDivEvidence a b :=
  n4ShiftNzDispatcherBranchHighDivEvidence_of_raw hevidence

theorem n4ShiftNzDispatcherBranchHighDivRawEvidence.toBranchRuntime {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hevidence : n4ShiftNzDispatcherBranchHighDivRawEvidence a b) :
    n4ShiftNzDispatcherBranchRuntimeV4 a b :=
  n4ShiftNzDispatcherBranchRuntimeV4_of_high_div_raw_evidence
    hb3nz hshift_nz hevidence

theorem n4ShiftNzDispatcherRuntimeHighDivEvidence.toBranchHighDivEvidence {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivEvidence a b) :
    n4ShiftNzDispatcherBranchHighDivEvidence a b :=
  n4ShiftNzDispatcherBranchHighDivEvidence_of_runtime_high_div hruntime

theorem n4ShiftNzDispatcherRuntimeHighDivEvidence.toBranchRuntime {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivEvidence a b) :
    n4ShiftNzDispatcherBranchRuntimeV4 a b :=
  n4ShiftNzDispatcherBranchRuntimeV4_of_runtime_high_div
    hb3nz hshift_nz hruntime

theorem n4ShiftNzDispatcherRuntimeHighDivRawEvidence.toHighDivEvidence {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b) :
    n4ShiftNzDispatcherRuntimeHighDivEvidence a b :=
  n4ShiftNzDispatcherRuntimeHighDivEvidence_of_raw hruntime

theorem n4ShiftNzDispatcherRuntimeHighDivRawEvidence.toBranchHighDivRawEvidence {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b) :
    n4ShiftNzDispatcherBranchHighDivRawEvidence a b :=
  n4ShiftNzDispatcherBranchHighDivRawEvidence_of_runtime_raw hruntime

theorem n4ShiftNzDispatcherRuntimeHighDivRawEvidence.toBranchHighDivEvidence {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b) :
    n4ShiftNzDispatcherBranchHighDivEvidence a b :=
  n4ShiftNzDispatcherBranchHighDivEvidence_of_raw
    (n4ShiftNzDispatcherRuntimeHighDivRawEvidence.toBranchHighDivRawEvidence hruntime)

theorem n4ShiftNzDispatcherRuntimeHighDivRawEvidence.toBranchRuntime {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b) :
    n4ShiftNzDispatcherBranchRuntimeV4 a b :=
  n4ShiftNzDispatcherBranchRuntimeV4_of_runtime_high_div_raw
    hb3nz hshift_nz hruntime

/-- n=4, shift-nonzero DIV v4 dispatcher over the call branch.

    The call-trial predicate is discharged from the normalized top limb. The
    skip/addback split is runtime-complete, but this intermediate surface still
    carries the branch-specific semantic facts:
    * `n4CallSkipBranchV4` for call+skip.
    * `isAddbackCarry2NzN4CallV4Evm` and `n4CallAddbackBeqSemanticHolds` for
      call+addback.
-/
theorem evm_div_n4_shift_nz_stack_spec_v4_of_branch_pred
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbranch : n4CallSkipBranchV4 a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  have hbnz : b ≠ 0 := evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz
  have hbltu : isCallTrialN4Evm a b :=
    isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz
  cases isSkipBorrowN4CallV4Evm_or_isAddbackBorrowN4CallV4Evm a b with
  | inl hskip =>
      exact cpsTripleWithin_mono_nSteps (by decide)
        (evm_div_n4_call_skip_stack_spec_v4_of_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip hbranch)
  | inr hadd =>
      exact evm_div_n4_call_addback_beq_stack_spec
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu hadd hcarry2 hsem

/-- n=4, shift-nonzero DIV v4 dispatcher with the addback semantic marker
    derived from the existing compact runtime-bounds predicate in the addback
    branch. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_of_runtime_bounds
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbranch : n4CallSkipBranchV4 a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_bounds : n4CallAddbackBeqRuntimeBounds a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  have hbnz : b ≠ 0 := evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz
  have hbltu : isCallTrialN4Evm a b :=
    isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz
  cases isSkipBorrowN4CallV4Evm_or_isAddbackBorrowN4CallV4Evm a b with
  | inl hskip =>
      exact cpsTripleWithin_mono_nSteps (by decide)
        (evm_div_n4_call_skip_stack_spec_v4_of_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip hbranch)
  | inr hadd =>
      have hsem : n4CallAddbackBeqSemanticHolds a b := by
        exact n4CallAddbackBeqSemanticHolds_of_runtime_bounds
          hb3nz hshift_nz h_bounds hadd hcarry2
      exact evm_div_n4_call_addback_beq_stack_spec
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu hadd hcarry2 hsem

/-- n=4, shift-nonzero DIV v4 dispatcher from the packaged runtime evidence
    predicate. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_of_runtime_pred
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  have hbnz : b ≠ 0 := evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz
  have hbltu : isCallTrialN4Evm a b :=
    isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz
  have hbranchRuntime : n4ShiftNzDispatcherBranchRuntimeV4 a b :=
    n4ShiftNzDispatcherBranchRuntimeV4_of_runtime_pred hruntime
  rw [n4ShiftNzDispatcherBranchRuntimeV4_def] at hbranchRuntime
  cases hbranchRuntime with
  | inl hskip =>
      exact cpsTripleWithin_mono_nSteps (by decide)
        (evm_div_n4_call_skip_stack_spec_v4_of_runtime_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip.1 hskip.2)
  | inr haddRuntime =>
      have hsem : n4CallAddbackBeqSemanticHolds a b := by
        exact n4CallAddbackBeqSemanticHolds_of_runtime_bounds
          hb3nz hshift_nz haddRuntime.2.2 haddRuntime.1 haddRuntime.2.1
      exact evm_div_n4_call_addback_beq_stack_spec
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu haddRuntime.1 haddRuntime.2.1 hsem

/-- n=4, shift-nonzero DIV v4 dispatcher from branch-sensitive runtime
    evidence. This surface avoids requiring addback-only arithmetic evidence
    when the runtime borrow split is already known to take the call+skip path. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_of_branch_runtime
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherBranchRuntimeV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  have hbnz : b ≠ 0 := evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz
  have hbltu : isCallTrialN4Evm a b :=
    isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz
  rw [n4ShiftNzDispatcherBranchRuntimeV4_def] at hruntime
  cases hruntime with
  | inl hskip =>
      exact cpsTripleWithin_mono_nSteps (by decide)
        (evm_div_n4_call_skip_stack_spec_v4_of_runtime_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip.1 hskip.2)
  | inr haddRuntime =>
      have hsem : n4CallAddbackBeqSemanticHolds a b := by
        exact n4CallAddbackBeqSemanticHolds_of_runtime_bounds
          hb3nz hshift_nz haddRuntime.2.2 haddRuntime.1 haddRuntime.2.1
      exact evm_div_n4_call_addback_beq_stack_spec
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu haddRuntime.1 haddRuntime.2.1 hsem


/-- n=4, shift-nonzero DIV v4 dispatcher from packaged branch/bounds
    evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_of_branch_bounds
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_branch_runtime
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign
    (n4ShiftNzDispatcherBranchRuntimeV4_of_branch_bounds hevidence)

/-- No-NOP n=4, shift-nonzero DIV v4 dispatcher over the call branch. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_pred
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbranch : n4CallSkipBranchV4 a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  have hbnz : b ≠ 0 := evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz
  have hbltu : isCallTrialN4Evm a b :=
    isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz
  cases isSkipBorrowN4CallV4Evm_or_isAddbackBorrowN4CallV4Evm a b with
  | inl hskip =>
      exact cpsTripleWithin_mono_nSteps (by decide)
        (evm_div_n4_call_skip_stack_spec_v4_noNop_of_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip hbranch)
  | inr hadd =>
      exact evm_div_n4_call_addback_beq_stack_spec_noNop
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu hadd hcarry2 hsem

/-- No-NOP n=4, shift-nonzero DIV v4 dispatcher with addback semantics derived
    from compact runtime bounds in the addback branch. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_noNop_of_runtime_bounds
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbranch : n4CallSkipBranchV4 a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_bounds : n4CallAddbackBeqRuntimeBounds a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  have hbnz : b ≠ 0 := evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz
  have hbltu : isCallTrialN4Evm a b :=
    isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz
  cases isSkipBorrowN4CallV4Evm_or_isAddbackBorrowN4CallV4Evm a b with
  | inl hskip =>
      exact cpsTripleWithin_mono_nSteps (by decide)
        (evm_div_n4_call_skip_stack_spec_v4_noNop_of_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip hbranch)
  | inr hadd =>
      have hsem : n4CallAddbackBeqSemanticHolds a b := by
        exact n4CallAddbackBeqSemanticHolds_of_runtime_bounds
          hb3nz hshift_nz h_bounds hadd hcarry2
      exact evm_div_n4_call_addback_beq_stack_spec_noNop
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu hadd hcarry2 hsem

/-- No-NOP n=4, shift-nonzero DIV v4 dispatcher from packaged runtime evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_noNop_of_runtime_pred
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  have hbnz : b ≠ 0 := evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz
  have hbltu : isCallTrialN4Evm a b :=
    isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz
  have hbranchRuntime : n4ShiftNzDispatcherBranchRuntimeV4 a b :=
    n4ShiftNzDispatcherBranchRuntimeV4_of_runtime_pred hruntime
  rw [n4ShiftNzDispatcherBranchRuntimeV4_def] at hbranchRuntime
  cases hbranchRuntime with
  | inl hskip =>
      exact cpsTripleWithin_mono_nSteps (by decide)
        (evm_div_n4_call_skip_stack_spec_v4_noNop_of_runtime_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip.1 hskip.2)
  | inr haddRuntime =>
      have hsem : n4CallAddbackBeqSemanticHolds a b := by
        exact n4CallAddbackBeqSemanticHolds_of_runtime_bounds
          hb3nz hshift_nz haddRuntime.2.2 haddRuntime.1 haddRuntime.2.1
      exact evm_div_n4_call_addback_beq_stack_spec_noNop
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu haddRuntime.1 haddRuntime.2.1 hsem

/-- No-NOP n=4, shift-nonzero DIV v4 dispatcher from branch-sensitive runtime
    evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_runtime
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherBranchRuntimeV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  have hbnz : b ≠ 0 := evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz
  have hbltu : isCallTrialN4Evm a b :=
    isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz
  rw [n4ShiftNzDispatcherBranchRuntimeV4_def] at hruntime
  cases hruntime with
  | inl hskip =>
      exact cpsTripleWithin_mono_nSteps (by decide)
        (evm_div_n4_call_skip_stack_spec_v4_noNop_of_runtime_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip.1 hskip.2)
  | inr haddRuntime =>
      have hsem : n4CallAddbackBeqSemanticHolds a b := by
        exact n4CallAddbackBeqSemanticHolds_of_runtime_bounds
          hb3nz hshift_nz haddRuntime.2.2 haddRuntime.1 haddRuntime.2.1
      exact evm_div_n4_call_addback_beq_stack_spec_noNop
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu haddRuntime.1 haddRuntime.2.1 hsem


/-- No-NOP n=4, shift-nonzero DIV v4 dispatcher from packaged
    branch/bounds evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_bounds
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_runtime
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign
    (n4ShiftNzDispatcherBranchRuntimeV4_of_branch_bounds hevidence)

/-- Final named n=4, shift-nonzero DIV dispatcher surface over `divCode_v4`.
    This is the branch-predicate API consumed by later n=4 stack assembly. -/
theorem evm_div_n4_shift_nz_stack_spec
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbranch : n4CallSkipBranchV4 a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_branch_pred
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbranch hcarry2 hsem

/-- Final named no-NOP n=4, shift-nonzero DIV dispatcher surface over
    `divCode_noNop_v4`. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbranch : n4CallSkipBranchV4 a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_pred
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbranch hcarry2 hsem


/-- Final named n=4, shift-nonzero DIV dispatcher surface from packaged
    runtime evidence. This is the stable runtime-facing API for later n=4
    unconditional assembly. -/
theorem evm_div_n4_shift_nz_stack_spec_of_runtime_pred
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_runtime_pred
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hruntime

/-- Final named no-NOP n=4, shift-nonzero DIV dispatcher surface from packaged
    runtime evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop_of_runtime_pred
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_runtime_pred
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hruntime

/-- Final named n=4, shift-nonzero DIV dispatcher surface from branch-sensitive
    runtime evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_of_branch_runtime
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherBranchRuntimeV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_branch_runtime
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hruntime

/-- Final named no-NOP n=4, shift-nonzero DIV dispatcher surface from
    branch-sensitive runtime evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop_of_branch_runtime
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherBranchRuntimeV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_runtime
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hruntime


/-- Final named n=4, shift-nonzero DIV dispatcher surface from the explicit
    callskip branch certificate plus compact addback runtime bounds. -/
theorem evm_div_n4_shift_nz_stack_spec_of_runtime_bounds
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbranch : n4CallSkipBranchV4 a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_bounds : n4CallAddbackBeqRuntimeBounds a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_runtime_bounds
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbranch hcarry2 h_bounds

/-- Final named no-NOP n=4, shift-nonzero DIV dispatcher surface from the
    explicit callskip branch certificate plus compact addback runtime bounds. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop_of_runtime_bounds
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbranch : n4CallSkipBranchV4 a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_bounds : n4CallAddbackBeqRuntimeBounds a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_runtime_bounds
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbranch hcarry2 h_bounds


/-- Final named n=4, shift-nonzero DIV dispatcher surface from
    branch-sensitive high-div evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_of_high_div_evidence
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : n4ShiftNzDispatcherBranchHighDivEvidence a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_branch_runtime
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign
    (n4ShiftNzDispatcherBranchRuntimeV4_of_high_div_evidence
      hb3nz hshift_nz hevidence)

/-- Final named no-NOP n=4, shift-nonzero DIV dispatcher surface from
    branch-sensitive high-div evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop_of_high_div_evidence
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : n4ShiftNzDispatcherBranchHighDivEvidence a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_runtime
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign
    (n4ShiftNzDispatcherBranchRuntimeV4_of_high_div_evidence
      hb3nz hshift_nz hevidence)

/-- Final named n=4, shift-nonzero DIV dispatcher surface from raw
    branch-sensitive high-div evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_of_high_div_raw_evidence
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : n4ShiftNzDispatcherBranchHighDivRawEvidence a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_of_high_div_evidence
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign
    (n4ShiftNzDispatcherBranchHighDivEvidence_of_raw hevidence)

/-- Final named no-NOP n=4, shift-nonzero DIV dispatcher surface from raw
    branch-sensitive high-div evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop_of_high_div_raw_evidence
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : n4ShiftNzDispatcherBranchHighDivRawEvidence a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_noNop_of_high_div_evidence
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign
    (n4ShiftNzDispatcherBranchHighDivEvidence_of_raw hevidence)

/-- Final named n=4, shift-nonzero DIV dispatcher surface from global
    packaged high-div runtime evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_of_runtime_high_div_evidence
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivEvidence a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_of_high_div_evidence
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign
    (n4ShiftNzDispatcherBranchHighDivEvidence_of_runtime_high_div hruntime)

/-- Final named no-NOP n=4, shift-nonzero DIV dispatcher surface from global
    packaged high-div runtime evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop_of_runtime_high_div_evidence
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivEvidence a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_noNop_of_high_div_evidence
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign
    (n4ShiftNzDispatcherBranchHighDivEvidence_of_runtime_high_div hruntime)

/-- Final named n=4, shift-nonzero DIV dispatcher surface from global
    raw high-div runtime evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_of_runtime_high_div_raw
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_of_high_div_raw_evidence
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign
    (n4ShiftNzDispatcherBranchHighDivRawEvidence_of_runtime_raw hruntime)

/-- Final named no-NOP n=4, shift-nonzero DIV dispatcher surface from global
    raw high-div runtime evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop_of_runtime_high_div_raw
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherRuntimeHighDivRawEvidence a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_noNop_of_high_div_raw_evidence
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign
    (n4ShiftNzDispatcherBranchHighDivRawEvidence_of_runtime_raw hruntime)

/-- Final named n=4, shift-nonzero DIV dispatcher surface from packaged
    branch/bounds evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_of_branch_bounds
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_branch_bounds
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hevidence

/-- Final named no-NOP n=4, shift-nonzero DIV dispatcher surface from packaged
    branch/bounds evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop_of_branch_bounds
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_bounds
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hevidence

end EvmAsm.Evm64
