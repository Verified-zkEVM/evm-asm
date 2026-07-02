/-
  EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CallSkipModWordLane

  The n=4 v5 shift=0 call+skip MOD remainder word equality (limb form):
  under the v5 raw-window skip borrow `mulsubN4NoBorrow (divKTrialCallV5QHat 0 a3 b3) …`
  and `shift = 0`, the four limbs of `EvmWord.mod a b` equal the raw mulsub
  remainder `ms = mulsubN4 (divKTrialCallV5QHat 0 a3 b3) b… a…`.  At shift=0 there is
  no denormalization; the no-borrow condition gives `c3 = 0`, so
  `mulsubN4_val256_eq` collapses to `val256 a = qHat·val256 b + val256 ms`, and with
  `qHat = a/b` (from `divKTrialCallV5QHat_uHi_zero_toNat`, exactly as the DIV shift=0
  skip word lane `n4_shift0_call_skip_div_mod_getLimbN_v5` derives) this pins
  `val256 ms = a mod b`.  MOD companion of the DIV shift=0 skip word lane; these are
  the `hmod0..hmod3` the n=4 shift=0 MOD skip lane feeds to its post bridge.
-/

import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0TrialValue
import EvmAsm.Evm64.DivMod.SpecCallShift0
import EvmAsm.Evm64.DivMod.LoopSemantic

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256 val256_eq_toNat getLimb_as_getLimbN_0 getLimb_as_getLimbN_1
  getLimb_as_getLimbN_2 getLimb_as_getLimbN_3 ne_zero_iff_getLimbN_or
  val256_pos_of_or_ne_zero getLimbN_fromLimbs_0 getLimbN_fromLimbs_1
  getLimbN_fromLimbs_2 getLimbN_fromLimbs_3 fromLimbs_toNat ult_iff)

/-- n=4 v5 shift=0 call+skip per-limb `EvmWord.mod a b` remainder facts: the four
    limbs of the remainder equal the raw mulsub remainder `ms`. -/
theorem n4_shift0_call_skip_mod_getLimbN_v5 (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) (0 : Word)) :
    let qHat := divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3)
    let ms := mulsubN4 qHat (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (EvmWord.mod a b).getLimbN 0 = ms.1 ∧
    (EvmWord.mod a b).getLimbN 1 = ms.2.1 ∧
    (EvmWord.mod a b).getLimbN 2 = ms.2.2.1 ∧
    (EvmWord.mod a b).getLimbN 3 = ms.2.2.2.1 := by
  set qHat := divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3) with hqHat_def
  set ms := mulsubN4 qHat (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) with hms_def
  -- c3 = 0 from the no-borrow condition (uTop = 0).
  have hc3_zero : ms.2.2.2.2 = 0 := by
    unfold mulsubN4NoBorrow at hborrow
    simp only [] at hborrow
    by_contra hne
    have h_lt : BitVec.ult (0 : Word) ms.2.2.2.2 = true := by
      rw [ult_iff, show (0 : Word).toNat = 0 from rfl]
      exact Nat.pos_of_ne_zero (fun h => hne (BitVec.eq_of_toNat_eq (by simp [h])))
    rw [hms_def, hqHat_def] at h_lt
    rw [h_lt] at hborrow
    simp at hborrow
  have hb3_ge : (b.getLimbN 3).toNat ≥ 2 ^ 63 := clz_zero_imp_msb hshift_z
  have hb_nz_or : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    ne_zero_iff_getLimbN_or.mp hbnz
  have hb_pos_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) > 0 :=
    val256_pos_of_or_ne_zero hb_nz_or
  -- qHat = a3 / b3 ≥ val256 a / val256 b.
  have hqHat_val : qHat.toNat = (a.getLimbN 3).toNat / (b.getLimbN 3).toNat := by
    rw [hqHat_def]
    exact divKTrialCallV5QHat_uHi_zero_toNat (a.getLimbN 3) (b.getLimbN 3) hb3_ge
  have h_algo_ge :
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤ qHat.toNat := by
    rw [hqHat_val]
    exact a3_div_b3_ge_val256_div (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_ge hb_pos_val
  -- The mulsub val256 identity, collapsed by c3 = 0.
  have h_mulsub := mulsubN4_val256_eq qHat
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  simp only [← hms_def] at h_mulsub
  rw [hc3_zero, show (0 : Word).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero] at h_mulsub
  -- val256 a = val256 ms + qHat * val256 b.
  have h_qHat_mul_le : qHat.toNat *
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) := by
    have : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ≥ 0 := Nat.zero_le _
    omega
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) = a.toNat := by
    simp only [← getLimb_as_getLimbN_0, ← getLimb_as_getLimbN_1,
               ← getLimb_as_getLimbN_2, ← getLimb_as_getLimbN_3]
    exact val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) = b.toNat := by
    simp only [← getLimb_as_getLimbN_0, ← getLimb_as_getLimbN_1,
               ← getLimb_as_getLimbN_2, ← getLimb_as_getLimbN_3]
    exact val256_eq_toNat b
  have hb_pos : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simp [h])) hbnz
    · exact h
  rw [ha_val, hb_val] at h_qHat_mul_le h_algo_ge h_mulsub
  -- qHat = a / b.
  have hq_eq : qHat.toNat = a.toNat / b.toNat := by
    have hle : qHat.toNat ≤ a.toNat / b.toNat := (Nat.le_div_iff_mul_le hb_pos).mpr h_qHat_mul_le
    omega
  -- val256 ms = a mod b.
  have hms_val : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 = a.toNat % b.toNat := by
    have hdm : a.toNat = b.toNat * (a.toNat / b.toNat) + a.toNat % b.toNat := (Nat.div_add_mod a.toNat b.toNat).symm
    rw [hq_eq] at h_mulsub
    -- h_mulsub : a.toNat = val256 ms + (a/b) * b.toNat
    have hcomm : (a.toNat / b.toNat) * b.toNat = b.toNat * (a.toNat / b.toNat) := Nat.mul_comm _ _
    omega
  have hmod_toNat : (EvmWord.mod a b).toNat = a.toNat % b.toNat := by
    unfold EvmWord.mod; rw [if_neg hbnz]; exact BitVec.toNat_umod
  set r_target : EvmWord := EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => ms.1 | 1 => ms.2.1 | 2 => ms.2.2.1 | 3 => ms.2.2.2.1 with hr_target
  have hr_target_toNat : r_target.toNat = val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 := by
    rw [hr_target]; exact EvmWord.val256_eq_fromLimbs_toNat.symm
  have hr_eq_mod : r_target = EvmWord.mod a b :=
    BitVec.eq_of_toNat_eq (by rw [hr_target_toNat, hms_val, hmod_toNat])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hr_eq_mod]; exact getLimbN_fromLimbs_0
  · rw [← hr_eq_mod]; exact getLimbN_fromLimbs_1
  · rw [← hr_eq_mod]; exact getLimbN_fromLimbs_2
  · rw [← hr_eq_mod]; exact getLimbN_fromLimbs_3

end EvmAsm.Evm64
