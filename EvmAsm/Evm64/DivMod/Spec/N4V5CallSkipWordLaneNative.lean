/-
  EvmAsm.Evm64.DivMod.Spec.N4V5CallSkipWordLaneNative

  The native v5 call-skip word equality: `(EvmWord.div a b).getLimbN 0 =
  divKTrialCallV5QHat u4 u3 b3'` (and limbs 1,2,3 = 0), proved DIRECTLY from the
  v5 trial bounds — no v4 trial bridge and, crucially, no v4 call-skip semantic
  (`n4CallSkipSemanticHoldsV4`, the no-wrap obligation the v4 track never
  discharged: CallSkipV4NoWrap:622).

  The two v5-native bounds pin the trial to the exact quotient on the skip branch:
  * lower `divKTrialCallV5QHat_ge_val256_div` (#7637): `a/b ≤ qHat`
  * upper `divKTrialCallV5QHat_call_skip_mul_val256_b_le_val256_a` (#7638):
    `qHat·val256 b ≤ val256 a`, from the v5 skip-borrow `isSkipBorrowN4CallV5`.

  Combining (`Nat.le_div_iff_mul_le` + `omega`) gives `qHat.toNat = a.toNat /
  b.toNat`, then the `fromLimbs` reshape (mirroring `n4_call_skip_div_mod_getLimbN_v4`)
  yields the per-limb facts.  This discharges the shift≠0 call-skip semantic from
  the shape, bypassing the v4 no-wrap blocker.  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N4V5CallSkipUpperBound
public import EvmAsm.Evm64.DivMod.Spec.CallSkipV4
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5Native
public import EvmAsm.Evm64.EvmWordArith.MaxTrialVacuity

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- n=4 v5 call-skip per-limb `EvmWord.div a b` facts with the v5 trial quotient
    `divKTrialCallV5QHat`, proved natively from the v5 trial bounds — only the v5
    skip-borrow check `isSkipBorrowN4CallV5` + the n=4 shape are needed (no v4
    semantic, no v4↔v5 bridge). -/
theorem n4_call_skip_div_mod_getLimbN_v5_native (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hskip : isSkipBorrowN4CallV5
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let qHat := divKTrialCallV5QHat u4 u3 b3'
    (EvmWord.div a b).getLimbN 0 = qHat ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  intro shift antiShift b3' u4 u3 qHat
  have hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) :=
    isCallTrialN4_of_shift_nz (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) hb3nz hshift_nz
  have hT3 := divKTrialCallV5QHat_call_skip_mul_val256_b_le_val256_a
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hshift_nz hskip
  have hsem := divKTrialCallV5QHat_ge_val256_div
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hb3nz hshift_nz hcall
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

end EvmAsm.Evm64
