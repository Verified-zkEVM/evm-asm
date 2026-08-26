/-
  EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CallSkipWordLane

  The n=4 v5 shift=0 call+skip word equality (limb form):
  `(EvmWord.div a b).getLimbN 0 = divKTrialCallV5QHat 0 a3 b3` (and limbs 1,2,3 = 0),
  under the v5 raw-window skip borrow `mulsubN4NoBorrow (divKTrialCallV5QHat 0 a3 b3) …`
  and `shift = 0` (`(clzResult b3).1 = 0`).  v5 mirror of the v4 shift=0 word equality
  `n4_shift0_call_skip_div_mod_getLimbN` (SpecCallShift0): same val256 lower/upper
  bound combine, but with the v5 trial quotient.  The lower bound uses
  `divKTrialCallV5QHat_uHi_zero_toNat` (#7629, the trial value `a3/b3` at uHi=0)
  composed with `a3_div_b3_ge_val256_div`; the upper bound uses the c3=0 extracted
  from the no-borrow condition and `mulsubN4_val256_eq`.  These four facts are the
  `hdiv0..hdiv3` the n=4 shift=0 call-skip lane skeleton (#7624) consumes.
  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0TrialValue
public import EvmAsm.Evm64.DivMod.SpecCallShift0

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256 val256_eq_toNat getLimb_as_getLimbN_0 getLimb_as_getLimbN_1
  getLimb_as_getLimbN_2 getLimb_as_getLimbN_3 ne_zero_iff_getLimbN_or
  val256_pos_of_or_ne_zero getLimbN_fromLimbs_0 getLimbN_fromLimbs_1
  getLimbN_fromLimbs_2 getLimbN_fromLimbs_3 fromLimbs_toNat ult_iff)

/-- n=4 v5 shift=0 call+skip per-limb `EvmWord.div a b` facts, with the v5 trial
    quotient `divKTrialCallV5QHat 0 a3 b3`.  v5 mirror of
    `n4_shift0_call_skip_div_mod_getLimbN`. -/
theorem n4_shift0_call_skip_div_mod_getLimbN_v5 (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) (0 : Word)) :
    (EvmWord.div a b).getLimbN 0 = divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3) ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  set qHat := divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3) with hqHat_def
  -- c3 = 0 from the no-borrow condition (uTop = 0).
  have hc3_zero : (mulsubN4 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 = 0 := by
    unfold mulsubN4NoBorrow at hborrow
    simp only [] at hborrow
    by_contra hne
    have h_lt : BitVec.ult (0 : Word)
        (mulsubN4 qHat
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 = true := by
      rw [ult_iff, show (0 : Word).toNat = 0 from rfl]
      exact Nat.pos_of_ne_zero (fun h => hne (BitVec.eq_of_toNat_eq (by simp [h])))
    rw [h_lt] at hborrow
    simp at hborrow
  have hb3_ge : (b.getLimbN 3).toNat ≥ 2 ^ 63 := clz_zero_imp_msb hshift_z
  have hb_nz_or : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    ne_zero_iff_getLimbN_or.mp hbnz
  have hb_pos_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) > 0 :=
    val256_pos_of_or_ne_zero hb_nz_or
  -- Lower bound (v5): qHat = a3 / b3 ≥ val256 a / val256 b.
  have hqHat_val : qHat.toNat = (a.getLimbN 3).toNat / (b.getLimbN 3).toNat := by
    rw [hqHat_def]
    exact divKTrialCallV5QHat_uHi_zero_toNat (a.getLimbN 3) (b.getLimbN 3) hb3_ge
  have h_algo_ge :
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤ qHat.toNat := by
    rw [hqHat_val]
    exact a3_div_b3_ge_val256_div (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_ge hb_pos_val
  -- Upper bound from c3 = 0: qHat * val256 b ≤ val256 a.
  have h_mulsub := mulsubN4_val256_eq qHat
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  simp only [] at h_mulsub
  rw [show (mulsubN4 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 =
      (0 : Word) from hc3_zero] at h_mulsub
  rw [show (0 : Word).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero] at h_mulsub
  have h_qHat_mul_le : qHat.toNat *
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) := by
    have h_un_bound :
        val256 (mulsubN4 qHat
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).1
          (mulsubN4 qHat
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.1
          (mulsubN4 qHat
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.1
          (mulsubN4 qHat
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.1 ≥ 0 :=
      Nat.zero_le _
    linarith
  -- Combine: qHat = val256 a / val256 b = a / b.
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
  rw [ha_val, hb_val] at h_qHat_mul_le h_algo_ge
  have hq_eq : qHat.toNat = a.toNat / b.toNat := by
    have hle : qHat.toNat ≤ a.toNat / b.toNat := (Nat.le_div_iff_mul_le hb_pos).mpr h_qHat_mul_le
    omega
  have hdiv_toNat : (EvmWord.div a b).toNat = a.toNat / b.toNat := by
    unfold EvmWord.div; rw [if_neg hbnz]; exact BitVec.toNat_udiv
  set q_target : EvmWord := EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => qHat | 1 => 0 | 2 => 0 | 3 => 0 with hq_target
  have hq_target_toNat : q_target.toNat = qHat.toNat := by
    simp [q_target, fromLimbs_toNat]
  have hq_eq_div : q_target = EvmWord.div a b := BitVec.eq_of_toNat_eq (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hq_eq_div]; exact getLimbN_fromLimbs_0
  · rw [← hq_eq_div]; exact getLimbN_fromLimbs_1
  · rw [← hq_eq_div]; exact getLimbN_fromLimbs_2
  · rw [← hq_eq_div]; exact getLimbN_fromLimbs_3

end EvmAsm.Evm64
