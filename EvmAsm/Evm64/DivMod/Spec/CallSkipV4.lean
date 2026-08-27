/-
  EvmAsm.Evm64.DivMod.Spec.CallSkipV4

  v4 analogues of the call+skip semantic predicate and `EvmWord.div`
  getLimbN bridge originally proven for the v1 algorithm in
  `Spec/CallSkip.lean`.

  Provides:

  * `n4CallSkipSemanticHoldsV4 a b : Prop` — Knuth-A lower bound at the
    val256 level for the v4 trial quotient `div128Quot_v4` (mirror of
    `n4CallSkipSemanticHolds`).
  * `n4_call_skip_div_mod_getLimbN_v4` — under `hbnz`, `hshift_nz`, the
    v4 skip-borrow runtime check `isSkipBorrowN4CallV4Evm`, and `hsem :=
    n4CallSkipSemanticHoldsV4 a b`, identifies the four limbs of
    `EvmWord.div a b` with the v4 trial quotient (low limb) and `0`
    (upper three limbs).

  Together with the no-overflow bound
  `div128Quot_v4_call_skip_mul_val256_b_le_val256_a` (see
  `EvmWordArith/Div128CallSkipCloseV4.lean`), the bridge sandwiches
  `qHat_v4.toNat` to `val256(a)/val256(b)`.

  The `hsem` precondition is left as an input here; its unconditional
  discharge under runtime conditions (v4 Knuth-A) is tracked separately
  by bead `evm-asm-9iqmw.7.1.3.1.1`.
-/
module

public import EvmAsm.Evm64.DivMod.Spec.CallSkip
public import EvmAsm.Evm64.EvmWordArith.Div128CallSkipCloseV4
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.QuotientBounds
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.ExactQuotient
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Un21Bound
public import EvmAsm.Evm64.DivMod.Compose.FullPathN4V4

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- **v4 algorithmic lower bound for `div128Quot_v4` at val256 level.**

    Mirror of `n4CallSkipSemanticHolds` (Spec/CallSkip.lean:1067), with
    the v1 trial `div128Quot` replaced by the v4 trial `div128Quot_v4`.

    Packages Knuth Theorem A (normalized divisor version) for the v4
    algorithm: `val256(a)/val256(b) ≤ qHat_v4`. The v4 algorithm with
    classical 2-correction in both Phase-1b and Phase-2 satisfies this
    bound (it computes the exact 128/64 quotient when `un21 < vTop`,
    and the val256 Knuth-A follows). The discharge under runtime
    conditions is left to a separate bead. -/
def n4CallSkipSemanticHoldsV4 (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
    (div128Quot_v4 u4 u3 b3').toNat

/-- EvmWord-level branch certificate for the final Phase-1b rhat high-half-zero
    case of the v4 n=4 call+skip path. -/
def n4CallSkipRhatddHiZeroV4 (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  divKTrialCallV4Rhatdd u4 u3 b3' >>> (32 : BitVec 6).toNat = (0 : Word)

/-- EvmWord-level branch certificate for the complementary final Phase-1b
    rhat high-half-nonzero case of the v4 n=4 call+skip path. -/
def n4CallSkipRhatddHiNonzeroV4 (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  divKTrialCallV4Rhatdd u4 u3 b3' >>> (32 : BitVec 6).toNat ≠ (0 : Word)

theorem n4CallSkipRhatddHiZeroV4_def {a b : EvmWord} :
    n4CallSkipRhatddHiZeroV4 a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     divKTrialCallV4Rhatdd u4 u3 b3' >>> (32 : BitVec 6).toNat = (0 : Word)) :=
  rfl

theorem n4CallSkipRhatddHiNonzeroV4_def {a b : EvmWord} :
    n4CallSkipRhatddHiNonzeroV4 a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     divKTrialCallV4Rhatdd u4 u3 b3' >>> (32 : BitVec 6).toNat ≠ (0 : Word)) :=
  rfl

theorem n4CallSkipRhatddHiZeroV4_or_nonzero (a b : EvmWord) :
    n4CallSkipRhatddHiZeroV4 a b ∨ n4CallSkipRhatddHiNonzeroV4 a b := by
  rw [n4CallSkipRhatddHiZeroV4_def, n4CallSkipRhatddHiNonzeroV4_def]
  exact Decidable.em _

/-- V4 call-skip lower bound in the final Phase-1b high-half-zero branch. -/
theorem div128Quot_v4_call_skip_ge_val256_div_of_rhatdd_hi_zero
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    (divKTrialCallV4Un21 u4 u3 b3').toNat < b3'.toNat →
    divKTrialCallV4Rhatdd u4 u3 b3' >>> (32 : BitVec 6).toNat = (0 : Word) →
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (div128Quot_v4 u4 u3 b3').toNat := by
  intro shift antiShift b3' u4 u3 hUn21_lt_vTop h_rhat_hi_zero
  have h_bridge := q_true_triple_bridge_to_val256_norm a0 a1 a2 a3 b0 b1 b2 b3
    hshift_nz hb3nz
  simp only [] at h_bridge
  have h_b3'_ge : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 b3 b2 hb3nz _
  have h_u4_lt_b3' : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_shift_pos : 1 ≤ (clzResult b3).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b3).1.toNat with h | h
    · exfalso
      apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have h_u4_lt_pow63 : u4.toNat < 2^63 :=
    u_top_lt_pow63_of_shift_nz a3 (clzResult b3).1 h_shift_pos
      (clzResult_fst_toNat_le b3)
  have h_core := div128Quot_v4_ge_q_true_of_rhatdd_hi_zero
    u4 u3 b3' h_b3'_ge h_u4_lt_b3' h_u4_lt_pow63 hUn21_lt_vTop h_rhat_hi_zero
  exact Nat.le_trans h_bridge h_core

/-- V4 call-skip semantic lower bound in the final Phase-1b high-half-zero branch. -/
theorem n4CallSkipSemanticHoldsV4_of_rhatdd_hi_zero (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    (divKTrialCallV4Un21 u4 u3 b3').toNat < b3'.toNat →
    divKTrialCallV4Rhatdd u4 u3 b3' >>> (32 : BitVec 6).toNat = (0 : Word) →
    n4CallSkipSemanticHoldsV4 a b := by
  intro shift antiShift b3' u4 u3 hUn21_lt_vTop h_rhat_hi_zero
  unfold n4CallSkipSemanticHoldsV4
  change
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
      (div128Quot_v4 u4 u3 b3').toNat
  have hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) :=
    isCallTrialN4_of_shift_nz (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)
      hb3nz hshift_nz
  exact div128Quot_v4_call_skip_ge_val256_div_of_rhatdd_hi_zero
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hb3nz hshift_nz hcall hUn21_lt_vTop h_rhat_hi_zero

/-- V4 call-skip semantic lower bound in the final Phase-1b high-half-zero branch,
    with the `un21 < vTop` invariant discharged from the call path. -/
theorem n4CallSkipSemanticHoldsV4_of_runtime_rhatdd_hi_zero (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    divKTrialCallV4Rhatdd u4 u3 b3' >>> (32 : BitVec 6).toNat = (0 : Word) →
    n4CallSkipSemanticHoldsV4 a b := by
  intro shift antiShift b3' u4 u3 h_rhat_hi_zero
  have hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) :=
    isCallTrialN4_of_shift_nz (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)
      hb3nz hshift_nz
  have hUn21_lt_vTop :
      (divKTrialCallV4Un21 u4 u3 b3').toNat < b3'.toNat := by
    have h := un21V4_lt_vTop_of_call (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 2) (b.getLimbN 3) hb3nz hshift_nz hcall
    simpa [algorithmUn21V4, shift, antiShift, b3', u4, u3] using h
  exact n4CallSkipSemanticHoldsV4_of_rhatdd_hi_zero a b hb3nz hshift_nz
    hUn21_lt_vTop h_rhat_hi_zero

/-- V4 call-skip semantic lower bound from runtime call conditions, the
    Phase-1 low-half no-wrap condition, and a supplied 128/64 upper bound. -/
theorem n4CallSkipSemanticHoldsV4_of_runtime_no_wrap_of_le (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    (divKTrialCallV4Q1dd u4 u3 b3').toNat *
        (divKTrialCallV4DLo b3').toNat ≤
      ((divKTrialCallV4Rhatdd u4 u3 b3').toNat % 2^32) * 2^32 +
        (divKTrialCallV4Un1 u3).toNat →
    (div128Quot_v4 u4 u3 b3').toNat ≤
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat →
    n4CallSkipSemanticHoldsV4 a b := by
  intro shift antiShift b3' u4 u3 h_no_wrap h_le
  unfold n4CallSkipSemanticHoldsV4
  change
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
      (div128Quot_v4 u4 u3 b3').toNat
  have hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) :=
    isCallTrialN4_of_shift_nz (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)
      hb3nz hshift_nz
  exact div128Quot_v4_call_skip_ge_val256_div_of_runtime_no_wrap_of_le
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hb3nz hshift_nz hcall h_no_wrap h_le

/-- V4 call-skip semantic lower bound from runtime call conditions and the
    Phase-1 low-half no-wrap condition, without a separate 128/64 upper-bound
    premise. -/
theorem n4CallSkipSemanticHoldsV4_of_runtime_no_wrap (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    (divKTrialCallV4Q1dd u4 u3 b3').toNat *
        (divKTrialCallV4DLo b3').toNat ≤
      ((divKTrialCallV4Rhatdd u4 u3 b3').toNat % 2^32) * 2^32 +
        (divKTrialCallV4Un1 u3).toNat →
    n4CallSkipSemanticHoldsV4 a b := by
  intro shift antiShift b3' u4 u3 h_no_wrap
  unfold n4CallSkipSemanticHoldsV4
  change
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
      (div128Quot_v4 u4 u3 b3').toNat
  have hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) :=
    isCallTrialN4_of_shift_nz (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)
      hb3nz hshift_nz
  exact div128Quot_v4_call_skip_ge_val256_div_of_runtime_no_wrap
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hb3nz hshift_nz hcall h_no_wrap

/-- Predicate-packaged semantic lower bound in the final Phase-1b
    high-half-zero branch. -/
theorem n4CallSkipSemanticHoldsV4_of_rhatdd_hi_zero_pred (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hrhat : n4CallSkipRhatddHiZeroV4 a b) :
    n4CallSkipSemanticHoldsV4 a b := by
  rw [n4CallSkipRhatddHiZeroV4_def] at hrhat
  exact n4CallSkipSemanticHoldsV4_of_runtime_rhatdd_hi_zero a b
    hb3nz hshift_nz hrhat

/-- A nonzero top limb witnesses that the full EVM word is nonzero. -/
theorem evmWord_ne_zero_of_getLimbN_3_ne_zero {b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0) : b ≠ 0 := by
  apply (EvmWord.ne_zero_iff_getLimbN_or).mpr
  intro h_or_zero
  exact hb3nz (EvmWord.or_eq_zero_imp_right h_or_zero)

/-- Tight v4 call-skip equality in the final Phase-1b high-half-zero branch. -/
theorem div128Quot_v4_call_skip_eq_val256_div_of_rhatdd_hi_zero
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3)
    (hskip : isSkipBorrowN4CallV4Ab a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    (divKTrialCallV4Un21 u4 u3 b3').toNat < b3'.toNat →
    divKTrialCallV4Rhatdd u4 u3 b3' >>> (32 : BitVec 6).toNat = (0 : Word) →
    (div128Quot_v4 u4 u3 b3').toNat =
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 := by
  intro shift antiShift b3' u4 u3 hUn21_lt_vTop h_rhat_hi_zero
  have h_le := div128Quot_v4_call_skip_le_val256_div
    a0 a1 a2 a3 b0 b1 b2 b3 hb3nz hshift_nz hskip
  have h_ge := div128Quot_v4_call_skip_ge_val256_div_of_rhatdd_hi_zero
    a0 a1 a2 a3 b0 b1 b2 b3 hb3nz hshift_nz hcall
    hUn21_lt_vTop h_rhat_hi_zero
  simp only [] at h_le h_ge
  exact Nat.le_antisymm h_le h_ge

/-- EvmWord-level tight v4 call-skip equality in the high-half-zero branch,
    with the `un21 < vTop` invariant discharged from the call path. -/
theorem n4CallSkipExactQuotientV4_of_runtime_rhatdd_hi_zero (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hskip : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    divKTrialCallV4Rhatdd u4 u3 b3' >>> (32 : BitVec 6).toNat = (0 : Word) →
    (div128Quot_v4 u4 u3 b3').toNat =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  intro shift antiShift b3' u4 u3 h_rhat_hi_zero
  rw [isSkipBorrowN4CallV4Evm_def] at hskip
  have hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) :=
    isCallTrialN4_of_shift_nz (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)
      hb3nz hshift_nz
  have hUn21_lt_vTop :
      (divKTrialCallV4Un21 u4 u3 b3').toNat < b3'.toNat := by
    have h := un21V4_lt_vTop_of_call (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 2) (b.getLimbN 3) hb3nz hshift_nz hcall
    simpa [algorithmUn21V4, shift, antiShift, b3', u4, u3] using h
  exact div128Quot_v4_call_skip_eq_val256_div_of_rhatdd_hi_zero
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hb3nz hshift_nz hcall hskip hUn21_lt_vTop h_rhat_hi_zero

/-- Predicate-packaged tight v4 call-skip equality in the high-half-zero branch. -/
theorem n4CallSkipExactQuotientV4_of_rhatdd_hi_zero_pred (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hskip : isSkipBorrowN4CallV4Evm a b)
    (hrhat : n4CallSkipRhatddHiZeroV4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    (div128Quot_v4 u4 u3 b3').toNat =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  rw [n4CallSkipRhatddHiZeroV4_def] at hrhat
  exact n4CallSkipExactQuotientV4_of_runtime_rhatdd_hi_zero a b
    hb3nz hshift_nz hskip hrhat

theorem n4CallSkipSemanticHoldsV4_def {a b : EvmWord} :
    n4CallSkipSemanticHoldsV4 a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
       (div128Quot_v4 u4 u3 b3').toNat) :=
  rfl

/-- **v4 getLimbN bridge for the n=4 call+skip path.**

    Mirror of `n4_call_skip_div_mod_getLimbN` (Spec/CallSkip.lean:1134),
    with the v1 algorithm replaced by `div128Quot_v4` and the v1 borrow
    predicate `isSkipBorrowN4CallEvm` replaced by its v4 counterpart
    `isSkipBorrowN4CallV4Evm`.

    Proof structure (transfers verbatim — qHat-agnostic sandwich):
    1. From T3 (v4): `qHat.toNat * val256(b) ≤ val256(a)`.
    2. From hsem (Knuth-A v4): `val256(a)/val256(b) ≤ qHat.toNat`.
    3. Sandwich gives `qHat.toNat = a.toNat / b.toNat = (EvmWord.div a b).toNat`.
    4. Since `qHat.toNat < 2^64`, only the low limb of `EvmWord.div a b` is
       non-zero; the upper three limbs vanish. -/
theorem n4_call_skip_div_mod_getLimbN_v4 (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hsem : n4CallSkipSemanticHoldsV4 a b) :
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
  intro shift antiShift b3' u4 u3 qHat
  rw [isSkipBorrowN4CallV4Evm_def] at hborrow
  rw [n4CallSkipSemanticHoldsV4_def] at hsem
  have hT3 := div128Quot_v4_call_skip_mul_val256_b_le_val256_a
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hshift_nz hborrow
  change qHat.toNat * val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
         val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) at hT3
  change val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
         qHat.toNat at hsem
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  have hb_pos : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with h | h
    · exfalso; apply hbnz; exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  rw [ha_val, hb_val] at hT3 hsem
  have hq_eq : qHat.toNat = a.toNat / b.toNat := by
    have hle : qHat.toNat ≤ a.toNat / b.toNat :=
      (Nat.le_div_iff_mul_le hb_pos).mpr hT3
    omega
  have hdiv_toNat : (EvmWord.div a b).toNat = a.toNat / b.toNat := by
    unfold EvmWord.div
    rw [if_neg hbnz]
    exact BitVec.toNat_udiv
  set q_target : EvmWord := EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => qHat | 1 => 0 | 2 => 0 | 3 => 0 with hq_target
  have hq_target_toNat : q_target.toNat = qHat.toNat := by
    simp [q_target, EvmWord.fromLimbs_toNat]
  have hq_eq_div : q_target = EvmWord.div a b :=
    BitVec.eq_of_toNat_eq (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_3

/-- V4 getLimbN bridge for the call+skip path in the final Phase-1b
    high-half-zero branch, with `hsem` discharged from runtime facts. -/
theorem n4_call_skip_div_mod_getLimbN_v4_of_runtime_rhatdd_hi_zero (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let qHat := div128Quot_v4 u4 u3 b3'
    divKTrialCallV4Rhatdd u4 u3 b3' >>> (32 : BitVec 6).toNat = (0 : Word) →
    (EvmWord.div a b).getLimbN 0 = qHat ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  intro shift antiShift b3' u4 u3 qHat h_rhat_hi_zero
  exact n4_call_skip_div_mod_getLimbN_v4 a b hbnz hshift_nz hborrow
    (n4CallSkipSemanticHoldsV4_of_runtime_rhatdd_hi_zero a b
      hb3nz hshift_nz h_rhat_hi_zero)

/-- Predicate-packaged getLimbN bridge for the call+skip path in the final
    Phase-1b high-half-zero branch. -/
theorem n4_call_skip_div_mod_getLimbN_v4_of_rhatdd_hi_zero_pred (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hrhat : n4CallSkipRhatddHiZeroV4 a b) :
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
  rw [n4CallSkipRhatddHiZeroV4_def] at hrhat
  exact n4_call_skip_div_mod_getLimbN_v4_of_runtime_rhatdd_hi_zero a b
    hbnz hb3nz hshift_nz hborrow hrhat

/-- Runtime rhat-zero getLimbN bridge with `b ≠ 0` discharged from `hb3nz`. -/
theorem n4_call_skip_div_mod_getLimbN_v4_of_runtime_rhatdd_hi_zero_hb3nz
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let qHat := div128Quot_v4 u4 u3 b3'
    divKTrialCallV4Rhatdd u4 u3 b3' >>> (32 : BitVec 6).toNat = (0 : Word) →
    (EvmWord.div a b).getLimbN 0 = qHat ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  exact n4_call_skip_div_mod_getLimbN_v4_of_runtime_rhatdd_hi_zero a b
    (evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz) hb3nz hshift_nz hborrow

/-- Runtime no-wrap getLimbN bridge with `b ≠ 0` discharged from `hb3nz`. -/
theorem n4_call_skip_div_mod_getLimbN_v4_of_runtime_no_wrap_of_le_hb3nz
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let qHat := div128Quot_v4 u4 u3 b3'
    (divKTrialCallV4Q1dd u4 u3 b3').toNat *
        (divKTrialCallV4DLo b3').toNat ≤
      ((divKTrialCallV4Rhatdd u4 u3 b3').toNat % 2^32) * 2^32 +
        (divKTrialCallV4Un1 u3).toNat →
    (div128Quot_v4 u4 u3 b3').toNat ≤
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat →
    (EvmWord.div a b).getLimbN 0 = qHat ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  intro shift antiShift b3' u4 u3 qHat h_no_wrap h_le
  exact n4_call_skip_div_mod_getLimbN_v4 a b
    (evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz)
    hshift_nz hborrow
    (n4CallSkipSemanticHoldsV4_of_runtime_no_wrap_of_le a b
      hb3nz hshift_nz h_no_wrap h_le)

/-- Predicate-packaged rhat-zero getLimbN bridge with `b ≠ 0` discharged
    from `hb3nz`. -/
theorem n4_call_skip_div_mod_getLimbN_v4_of_rhatdd_hi_zero_pred_hb3nz
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hrhat : n4CallSkipRhatddHiZeroV4 a b) :
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
  exact n4_call_skip_div_mod_getLimbN_v4_of_rhatdd_hi_zero_pred a b
    (evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz) hb3nz hshift_nz hborrow hrhat

/-- **EvmWord-form wrapper of `evm_div_n4_full_call_skip_spec_v4`.**
    Mirror of `evm_div_n4_full_call_skip_stack_pre_spec` (the v1 wrapper
    at `Spec/CallSkip.lean:323`), adapted for the v4 surface:

    * code: `divCode_v4 base` (instead of `divCode base`).
    * borrow predicate: `isSkipBorrowN4CallV4Evm` (instead of v1).
    * pre includes the v4 trial-call scratch cell `(sp + 3936) ↦ₘ scratchMem`.
    * post is `fullDivN4CallSkipPostV4` (v4 post — exposes `div128Quot_v4`).

    Translates Word-form limbs (a0..a3, b0..b3) to EvmWord (a, b) via
    `getLimbN`. -/
theorem evm_div_n4_full_call_skip_stack_pre_spec_v4 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (fullDivN4CallSkipPostV4 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        scratchMem) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  rw [isCallTrialN4Evm_def] at hbltu
  rw [isSkipBorrowN4CallV4Evm_def] at hborrow
  have hraw := evm_div_n4_full_call_skip_spec_v4 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz' hb3nz hshift_nz halign hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- No-NOP variant of `evm_div_n4_full_call_skip_stack_pre_spec_v4`. -/
theorem evm_div_n4_full_call_skip_stack_pre_spec_v4_noNop (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (fullDivN4CallSkipPostV4 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        scratchMem) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  rw [isCallTrialN4Evm_def] at hbltu
  rw [isSkipBorrowN4CallV4Evm_def] at hborrow
  have hraw := evm_div_n4_full_call_skip_spec_v4_noNop sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz' hb3nz hshift_nz halign hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- EVM-stack-level DIV spec on the v4 n=4 call+skip sub-path in the
    final Phase-1b high-half-zero branch. -/
theorem evm_div_n4_call_skip_stack_pre_spec_v4_of_runtime_rhatdd_hi_zero
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    divKTrialCallV4Rhatdd u4 u3 b3' >>> (32 : BitVec 6).toNat = (0 : Word) →
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  intro shift antiShift b3' u4 u3 h_rhat_hi_zero
  let qHat := div128Quot_v4 u4 u3 b3'
  have h_pre := evm_div_n4_full_call_skip_stack_pre_spec_v4 sp base a b
    v5 v6 v7 v10 v11Old q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
    u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    n4_call_skip_div_mod_getLimbN_v4_of_runtime_rhatdd_hi_zero a b
      hbnz hb3nz hshift_nz hborrow h_rhat_hi_zero
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
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

/-- EVM-stack-level DIV spec on the v4 n=4 call+skip sub-path from runtime
    call conditions, normalized no-wrap evidence, and a supplied 128/64 upper
    bound. -/
theorem evm_div_n4_call_skip_stack_pre_spec_v4_of_runtime_no_wrap_of_le_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    (divKTrialCallV4Q1dd u4 u3 b3').toNat *
        (divKTrialCallV4DLo b3').toNat ≤
      ((divKTrialCallV4Rhatdd u4 u3 b3').toNat % 2^32) * 2^32 +
        (divKTrialCallV4Un1 u3).toNat →
    (div128Quot_v4 u4 u3 b3').toNat ≤
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat →
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  intro shift antiShift b3' u4 u3 h_no_wrap h_le
  let qHat := div128Quot_v4 u4 u3 b3'
  have hbnz : b ≠ 0 := evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz
  have h_pre := evm_div_n4_full_call_skip_stack_pre_spec_v4 sp base a b
    v5 v6 v7 v10 v11Old q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
    u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    n4_call_skip_div_mod_getLimbN_v4_of_runtime_no_wrap_of_le_hb3nz a b
      hb3nz hshift_nz hborrow h_no_wrap h_le
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
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

/-- No-NOP variant of
    `evm_div_n4_call_skip_stack_pre_spec_v4_of_runtime_rhatdd_hi_zero`. -/
theorem evm_div_n4_call_skip_stack_pre_spec_v4_noNop_of_runtime_rhatdd_hi_zero
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    divKTrialCallV4Rhatdd u4 u3 b3' >>> (32 : BitVec 6).toNat = (0 : Word) →
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  intro shift antiShift b3' u4 u3 h_rhat_hi_zero
  let qHat := div128Quot_v4 u4 u3 b3'
  have h_pre := evm_div_n4_full_call_skip_stack_pre_spec_v4_noNop sp base a b
    v5 v6 v7 v10 v11Old q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
    u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    n4_call_skip_div_mod_getLimbN_v4_of_runtime_rhatdd_hi_zero a b
      hbnz hb3nz hshift_nz hborrow h_rhat_hi_zero
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
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

/-- No-NOP variant of
    `evm_div_n4_call_skip_stack_pre_spec_v4_of_runtime_no_wrap_of_le_hb3nz`. -/
theorem evm_div_n4_call_skip_stack_pre_spec_v4_noNop_of_runtime_no_wrap_of_le_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    (divKTrialCallV4Q1dd u4 u3 b3').toNat *
        (divKTrialCallV4DLo b3').toNat ≤
      ((divKTrialCallV4Rhatdd u4 u3 b3').toNat % 2^32) * 2^32 +
        (divKTrialCallV4Un1 u3).toNat →
    (div128Quot_v4 u4 u3 b3').toNat ≤
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat →
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  intro shift antiShift b3' u4 u3 h_no_wrap h_le
  let qHat := div128Quot_v4 u4 u3 b3'
  have hbnz : b ≠ 0 := evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz
  have h_pre := evm_div_n4_full_call_skip_stack_pre_spec_v4_noNop sp base a b
    v5 v6 v7 v10 v11Old q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
    u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    n4_call_skip_div_mod_getLimbN_v4_of_runtime_no_wrap_of_le_hb3nz a b
      hb3nz hshift_nz hborrow h_no_wrap h_le
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
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

/-- Runtime rhat-zero stack-pre wrapper with `b ≠ 0` discharged from `hb3nz`. -/
theorem evm_div_n4_call_skip_stack_pre_spec_v4_of_runtime_rhatdd_hi_zero_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    divKTrialCallV4Rhatdd u4 u3 b3' >>> (32 : BitVec 6).toNat = (0 : Word) →
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  exact evm_div_n4_call_skip_stack_pre_spec_v4_of_runtime_rhatdd_hi_zero
    sp base a b v5 v6 v7 v10 v11Old q0 q1 q2 q3 u0Old u1Old u2Old u3Old
    u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    (evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz) hb3nz hshift_nz halign hbltu hborrow

/-- No-NOP runtime rhat-zero stack-pre wrapper with `b ≠ 0` discharged
    from `hb3nz`. -/
theorem evm_div_n4_call_skip_stack_pre_spec_v4_noNop_of_runtime_rhatdd_hi_zero_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    divKTrialCallV4Rhatdd u4 u3 b3' >>> (32 : BitVec 6).toNat = (0 : Word) →
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  exact evm_div_n4_call_skip_stack_pre_spec_v4_noNop_of_runtime_rhatdd_hi_zero
    sp base a b v5 v6 v7 v10 v11Old q0 q1 q2 q3 u0Old u1Old u2Old u3Old
    u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    (evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz) hb3nz hshift_nz halign hbltu hborrow

/-- Bundled variant of
    `evm_div_n4_call_skip_stack_pre_spec_v4_of_runtime_rhatdd_hi_zero`. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_runtime_rhatdd_hi_zero
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4Top := (a.getLimbN 3) >>> antiShift
    let u3Top := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    divKTrialCallV4Rhatdd u4Top u3Top b3' >>> (32 : BitVec 6).toNat = (0 : Word) →
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  intro shift antiShift b3' u4Top u3Top h_rhat_hi_zero
  have h := evm_div_n4_call_skip_stack_pre_spec_v4_of_runtime_rhatdd_hi_zero
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow h_rhat_hi_zero
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [divN4StackPreCall_unfold] at hp
      xperm_hyp hp)
    (fun _ hq => hq)
    h

/-- Bundled no-NOP variant of
    `evm_div_n4_call_skip_stack_pre_spec_v4_noNop_of_runtime_rhatdd_hi_zero`. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_runtime_rhatdd_hi_zero
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4Top := (a.getLimbN 3) >>> antiShift
    let u3Top := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    divKTrialCallV4Rhatdd u4Top u3Top b3' >>> (32 : BitVec 6).toNat = (0 : Word) →
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  intro shift antiShift b3' u4Top u3Top h_rhat_hi_zero
  have h := evm_div_n4_call_skip_stack_pre_spec_v4_noNop_of_runtime_rhatdd_hi_zero
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow h_rhat_hi_zero
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [divN4StackPreCall_unfold] at hp
      xperm_hyp hp)
    (fun _ hq => hq)
    h

/-- Bundled variant of
    `evm_div_n4_call_skip_stack_pre_spec_v4_of_runtime_no_wrap_of_le_hb3nz`. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_runtime_no_wrap_of_le
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4Top := (a.getLimbN 3) >>> antiShift
    let u3Top := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    (divKTrialCallV4Q1dd u4Top u3Top b3').toNat *
        (divKTrialCallV4DLo b3').toNat ≤
      ((divKTrialCallV4Rhatdd u4Top u3Top b3').toNat % 2^32) * 2^32 +
        (divKTrialCallV4Un1 u3Top).toNat →
    (div128Quot_v4 u4Top u3Top b3').toNat ≤
      (u4Top.toNat * 2^64 + u3Top.toNat) / b3'.toNat →
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  intro shift antiShift b3' u4Top u3Top h_no_wrap h_le
  have h := evm_div_n4_call_skip_stack_pre_spec_v4_of_runtime_no_wrap_of_le_hb3nz
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbltu hborrow h_no_wrap h_le
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [divN4StackPreCall_unfold] at hp
      xperm_hyp hp)
    (fun _ hq => hq)
    h

/-- Bundled no-NOP variant of
    `evm_div_n4_call_skip_stack_pre_spec_v4_noNop_of_runtime_no_wrap_of_le_hb3nz`. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_runtime_no_wrap_of_le
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4Top := (a.getLimbN 3) >>> antiShift
    let u3Top := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    (divKTrialCallV4Q1dd u4Top u3Top b3').toNat *
        (divKTrialCallV4DLo b3').toNat ≤
      ((divKTrialCallV4Rhatdd u4Top u3Top b3').toNat % 2^32) * 2^32 +
        (divKTrialCallV4Un1 u3Top).toNat →
    (div128Quot_v4 u4Top u3Top b3').toNat ≤
      (u4Top.toNat * 2^64 + u3Top.toNat) / b3'.toNat →
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  intro shift antiShift b3' u4Top u3Top h_no_wrap h_le
  have h := evm_div_n4_call_skip_stack_pre_spec_v4_noNop_of_runtime_no_wrap_of_le_hb3nz
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbltu hborrow h_no_wrap h_le
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [divN4StackPreCall_unfold] at hp
      xperm_hyp hp)
    (fun _ hq => hq)
    h

/-- Bundled v4 call+skip stack wrapper in the no-wrap branch, with
    call-trial discharged from `shift ≠ 0`. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_shift_nz_no_wrap_of_le
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4Top := (a.getLimbN 3) >>> antiShift
    let u3Top := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    (divKTrialCallV4Q1dd u4Top u3Top b3').toNat *
        (divKTrialCallV4DLo b3').toNat ≤
      ((divKTrialCallV4Rhatdd u4Top u3Top b3').toNat % 2^32) * 2^32 +
        (divKTrialCallV4Un1 u3Top).toNat →
    (div128Quot_v4 u4Top u3Top b3').toNat ≤
      (u4Top.toNat * 2^64 + u3Top.toNat) / b3'.toNat →
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  intro shift antiShift b3' u4Top u3Top h_no_wrap h_le
  have hbltu : isCallTrialN4Evm a b :=
    isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz
  exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_runtime_no_wrap_of_le
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbltu hborrow h_no_wrap h_le

/-- Bundled no-NOP v4 call+skip stack wrapper in the no-wrap branch, with
    call-trial discharged from `shift ≠ 0`. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_shift_nz_no_wrap_of_le
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4Top := (a.getLimbN 3) >>> antiShift
    let u3Top := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    (divKTrialCallV4Q1dd u4Top u3Top b3').toNat *
        (divKTrialCallV4DLo b3').toNat ≤
      ((divKTrialCallV4Rhatdd u4Top u3Top b3').toNat % 2^32) * 2^32 +
        (divKTrialCallV4Un1 u3Top).toNat →
    (div128Quot_v4 u4Top u3Top b3').toNat ≤
      (u4Top.toNat * 2^64 + u3Top.toNat) / b3'.toNat →
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  intro shift antiShift b3' u4Top u3Top h_no_wrap h_le
  have hbltu : isCallTrialN4Evm a b :=
    isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz
  exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_runtime_no_wrap_of_le
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbltu hborrow h_no_wrap h_le

/-- Bundled v4 call+skip stack wrapper in the rhat-zero branch, with
    call-trial discharged from `shift ≠ 0`. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_shift_nz_rhatdd_hi_zero
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4Top := (a.getLimbN 3) >>> antiShift
    let u3Top := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    divKTrialCallV4Rhatdd u4Top u3Top b3' >>> (32 : BitVec 6).toNat = (0 : Word) →
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  intro shift antiShift b3' u4Top u3Top h_rhat_hi_zero
  have hbltu : isCallTrialN4Evm a b :=
    isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz
  exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_runtime_rhatdd_hi_zero
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow h_rhat_hi_zero

/-- Bundled no-NOP v4 call+skip stack wrapper in the rhat-zero branch, with
    call-trial discharged from `shift ≠ 0`. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_shift_nz_rhatdd_hi_zero
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4Top := (a.getLimbN 3) >>> antiShift
    let u3Top := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    divKTrialCallV4Rhatdd u4Top u3Top b3' >>> (32 : BitVec 6).toNat = (0 : Word) →
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  intro shift antiShift b3' u4Top u3Top h_rhat_hi_zero
  have hbltu : isCallTrialN4Evm a b :=
    isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz
  exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_runtime_rhatdd_hi_zero
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow h_rhat_hi_zero

/-- Predicate-packaged variant of
    `evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_shift_nz_rhatdd_hi_zero`. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_rhatdd_hi_zero_pred
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hrhat : n4CallSkipRhatddHiZeroV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  rw [n4CallSkipRhatddHiZeroV4_def] at hrhat
  exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_shift_nz_rhatdd_hi_zero
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hborrow hrhat

/-- Predicate-packaged no-NOP variant of
    `evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_shift_nz_rhatdd_hi_zero`. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_rhatdd_hi_zero_pred
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hrhat : n4CallSkipRhatddHiZeroV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  rw [n4CallSkipRhatddHiZeroV4_def] at hrhat
  exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_shift_nz_rhatdd_hi_zero
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hborrow hrhat

/-- Predicate-packaged variant with `b ≠ 0` discharged from the nonzero top limb. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_rhatdd_hi_zero_pred_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hrhat : n4CallSkipRhatddHiZeroV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_rhatdd_hi_zero_pred
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    (evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz) hb3nz hshift_nz halign hborrow hrhat

/-- Predicate-packaged no-NOP variant with `b ≠ 0` discharged from the
    nonzero top limb. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_rhatdd_hi_zero_pred_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hrhat : n4CallSkipRhatddHiZeroV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_rhatdd_hi_zero_pred
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    (evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz) hb3nz hshift_nz halign hborrow hrhat

end EvmAsm.Evm64
