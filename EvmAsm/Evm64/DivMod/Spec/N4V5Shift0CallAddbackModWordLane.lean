/-
  EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CallAddbackModWordLane

  The n=4 v5 shift=0 call+addback-beq MOD remainder word equality (limb form):
  under the v5 raw-window addback borrow (`c3 ≠ 0`) and `shift = 0`, the four limbs
  of `EvmWord.mod a b` equal the single-addback-corrected remainder `ab` (the
  `carry ≠ 0` branch of the loop-body `un*Out`).  On the shift=0 addback branch the
  trial `qHat = divKTrialCallV5QHat 0 a3 b3 = 1` and the firing borrow forces
  `val256 a < val256 b`, so `c3 = 1` and the FIRST addback carries (carry = 1);
  the single-addback remainder identity `val256_addback_single_eq_amod_of_facts`
  then gives `val256 ab = (val256 a) % (val256 b) = a mod b`.  MOD companion of the
  DIV shift=0 addback word lane `n4_shift0_call_addback_div_getLimbN_v5`; these are
  the `hmod0..hmod3` the n=4 shift=0 MOD addback lane feeds to its post bridge.
-/

import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0TrialBounds
import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CallAddbackCarry
import EvmAsm.Evm64.DivMod.Spec.N4V5CallAddbackModRemainder
import EvmAsm.Evm64.DivMod.SpecCallShift0

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256 val256_eq_toNat val256_bound getLimb_as_getLimbN_0 getLimb_as_getLimbN_1
  getLimb_as_getLimbN_2 getLimb_as_getLimbN_3 getLimbN_fromLimbs_0 getLimbN_fromLimbs_1
  getLimbN_fromLimbs_2 getLimbN_fromLimbs_3)

/-- n=4 v5 shift=0 call+addback-beq per-limb `EvmWord.mod a b` remainder facts: the
    four limbs of the remainder equal the single-addback-corrected `ab`. -/
theorem n4_shift0_call_addback_mod_getLimbN_v5 (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : (if BitVec.ult (0 : Word)
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word)) :
    let qHat := divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3)
    let ms := mulsubN4 qHat (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (EvmWord.mod a b).getLimbN 0 = ab.1 ∧
    (EvmWord.mod a b).getLimbN 1 = ab.2.1 ∧
    (EvmWord.mod a b).getLimbN 2 = ab.2.2.1 ∧
    (EvmWord.mod a b).getLimbN 3 = ab.2.2.2.1 := by
  set qHat := divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3) with hqHat_def
  set ms := mulsubN4 qHat (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) with hms_def
  -- c3 ≠ 0 from the firing borrow.
  have hc3_nz : ms.2.2.2.2 ≠ 0 := fun hc3z => hborrow (by rw [hc3z]; decide)
  have hb3_ge : (b.getLimbN 3).toNat ≥ 2 ^ 63 := clz_zero_imp_msb hshift_z
  -- qHat ≤ 1 and ≠ 0 ⟹ qHat = 1.
  have hqHat_le_one : qHat.toNat ≤ 1 := by
    rw [hqHat_def]; exact divKTrialCallV5QHat_uHi_zero_le_one (a.getLimbN 3) (b.getLimbN 3) hb3_ge
  have hqHat_nz : qHat ≠ 0 := by
    intro hq0
    apply hc3_nz
    rw [hms_def]
    apply c3_un_zero_of_qHat_mul_le
    rw [hq0, show (0 : Word).toNat = 0 from rfl, Nat.zero_mul]
    exact Nat.zero_le _
  have hqHat_eq_one : qHat.toNat = 1 := by
    have : qHat.toNat ≠ 0 := fun h => hqHat_nz (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    omega
  -- val256 identities.
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) = b.toNat := by
    simp only [← getLimb_as_getLimbN_0, ← getLimb_as_getLimbN_1,
               ← getLimb_as_getLimbN_2, ← getLimb_as_getLimbN_3]
    exact val256_eq_toNat b
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) = a.toNat := by
    simp only [← getLimb_as_getLimbN_0, ← getLimb_as_getLimbN_1,
               ← getLimb_as_getLimbN_2, ← getLimb_as_getLimbN_3]
    exact val256_eq_toNat a
  have hBnz : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≠ 0 := by
    rw [hb_val]; exact fun h => hbnz (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  -- val256 a < val256 b (borrow fired with qHat = 1) and c3 = 1.
  have h_mulsub := mulsubN4_val256_eq qHat
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  simp only [← hms_def] at h_mulsub
  have hc3_pos : ms.2.2.2.2.toNat ≥ 1 := by
    rcases Nat.eq_zero_or_pos ms.2.2.2.2.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) hc3_nz
    · exact h
  have h_val_ms_bound : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < 2 ^ 256 := val256_bound _ _ _ _
  have h_val_b_bound : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) < 2 ^ 256 :=
    val256_bound _ _ _ _
  have h_val_a_bound : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) < 2 ^ 256 :=
    val256_bound _ _ _ _
  have hc3_le_one : ms.2.2.2.2.toNat ≤ 1 := by nlinarith [h_mulsub, hqHat_eq_one, h_val_ms_bound, h_val_b_bound, h_val_a_bound]
  have hc3_eq_one : ms.2.2.2.2 = (1 : Word) := BitVec.eq_of_toNat_eq (by rw [show (1:Word).toNat = 1 from rfl]; omega)
  have h_val_a_lt_b :
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) <
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
    nlinarith [h_mulsub, hc3_pos, h_val_ms_bound, hqHat_eq_one]
  -- first-addback carry = 1.
  have hcarry_nz := n4_shift0_call_addback_first_carry_nz a b hshift_z hborrow
  rw [← hqHat_def, ← hms_def] at hcarry_nz
  have hcarry_one : addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) = 1 :=
    addbackN4_carry_eq_one_of_ne_zero _ _ _ _ _ _ _ _ hcarry_nz
  -- Instantiate the single-addback remainder identity at the raw shift=0 window (uTop = 0).
  have hqHat_form : qHat.toNat =
      (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) +
        (0 : Word).toNat * 2 ^ 256) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 1 := by
    have hquot : (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) +
        (0 : Word).toNat * 2 ^ 256) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) = 0 := by
      rw [show (0 : Word).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]
      exact Nat.div_eq_of_lt h_val_a_lt_b
    rw [hquot, hqHat_eq_one]
  have hamod := val256_addback_single_eq_amod_of_facts qHat
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) (0 : Word)
    (by rw [show (0:Word).toNat = 0 from rfl]; norm_num)
    (by rw [← hms_def, hc3_eq_one]; decide)
    (by rw [← hms_def]; exact hcarry_one)
    (by rw [hqHat_eq_one])
    hBnz hqHat_form
  simp only [← hms_def] at hamod
  -- val256 ab = a % b = (mod a b).toNat.
  have hab_val : val256
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1 = a.toNat % b.toNat := by
    rw [hamod, show (0 : Word).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero, ha_val, hb_val]
  have hmod_toNat : (EvmWord.mod a b).toNat = a.toNat % b.toNat := by
    unfold EvmWord.mod; rw [if_neg hbnz]; exact BitVec.toNat_umod
  set ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) with hab_def
  set r_target : EvmWord := EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => ab.1 | 1 => ab.2.1 | 2 => ab.2.2.1 | 3 => ab.2.2.2.1 with hr_target
  have hr_target_toNat : r_target.toNat = val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 := by
    rw [hr_target]; exact EvmWord.val256_eq_fromLimbs_toNat.symm
  have hr_eq_mod : r_target = EvmWord.mod a b :=
    BitVec.eq_of_toNat_eq (by rw [hr_target_toNat, hab_val, hmod_toNat])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hr_eq_mod]; exact getLimbN_fromLimbs_0
  · rw [← hr_eq_mod]; exact getLimbN_fromLimbs_1
  · rw [← hr_eq_mod]; exact getLimbN_fromLimbs_2
  · rw [← hr_eq_mod]; exact getLimbN_fromLimbs_3

end EvmAsm.Evm64
