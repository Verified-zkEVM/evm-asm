/-
  EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CallAddbackWordLane

  The n=4 v5 shift=0 call+addback-beq word equality (limb form):
  `(EvmWord.div a b).getLimbN 0 = fullDivN4CallAddbackShift0QuotientV5 …` (and limbs
  1,2,3 = 0), under the v5 raw-window addback borrow (`c3 ≠ 0`) and `shift = 0`.
  v5 mirror of the v4 `n4_shift0_call_addback_beq_div_getLimbN` (SpecCallShift0):
  on the shift=0 addback branch the trial `qHat = divKTrialCallV5QHat 0 a3 b3` is
  `≤ 1` (#7631) and `≠ 0` (from `c3 ≠ 0`), hence `= 1`; the firing borrow forces
  `val256 a < val256 b`, so `a / b = 0`, and the corrected quotient
  `q_out = qHat + (2^64-1) = 0` (single addback, carry ≠ 0).  These are the
  `hdiv0..hdiv3` the n=4 shift=0 call-addback lane skeleton (#7625) consumes.

  Note: both `qHat` (the v5 trial) and `ms` (the mulsub tuple) are introduced as
  GENUINELY OPAQUE `obtain` variables (not `set` let-bindings), so `nlinarith` and
  `whnf` never re-enter the heavy `divKTrialCallV5QHat` / `mulsubN4` bodies (the v5
  term-size wall — see `feedback_irreducible_for_let_bindings`).
  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShift0CallAddback
public import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0TrialBounds
public import EvmAsm.Evm64.DivMod.SpecCallShift0

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256 val256_eq_toNat val256_bound getLimb_as_getLimbN_0 getLimb_as_getLimbN_1
  getLimb_as_getLimbN_2 getLimb_as_getLimbN_3 getLimbN_zero)

/-- n=4 v5 shift=0 call+addback-beq per-limb `EvmWord.div a b` facts, with the v5
    corrected quotient `fullDivN4CallAddbackShift0QuotientV5`. -/
theorem n4_shift0_call_addback_div_getLimbN_v5 (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : (if BitVec.ult (0 : Word)
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word)) :
    (EvmWord.div a b).getLimbN 0 = fullDivN4CallAddbackShift0QuotientV5
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  -- Opaque `qHat` and `ms` (obtain, not set) to dodge the v5 whnf term-size wall.
  obtain ⟨qHat, hqHat_def⟩ :
      ∃ q, q = divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3) := ⟨_, rfl⟩
  rw [← hqHat_def] at hborrow
  obtain ⟨ms, hms_def⟩ :
      ∃ m, m = mulsubN4 qHat
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) := ⟨_, rfl⟩
  rw [← hms_def] at hborrow
  -- c3 ≠ 0 from the firing borrow.
  have hc3_nz : ms.2.2.2.2 ≠ 0 := fun hc3z => hborrow (by rw [hc3z]; decide)
  have hb3_ge : (b.getLimbN 3).toNat ≥ 2 ^ 63 := clz_zero_imp_msb hshift_z
  -- qHat ≤ 1.
  have hqHat_le_one : qHat.toNat ≤ 1 := by
    rw [hqHat_def]; exact divKTrialCallV5QHat_uHi_zero_le_one (a.getLimbN 3) (b.getLimbN 3) hb3_ge
  -- qHat ≠ 0 (else mulsub c3 = 0).
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
  -- val256 a < val256 b (borrow fired with qHat = 1).
  have h_mulsub := mulsubN4_val256_eq qHat
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  simp only [] at h_mulsub
  rw [← hms_def] at h_mulsub
  have hc3_pos : ms.2.2.2.2.toNat ≥ 1 := by
    rcases Nat.eq_zero_or_pos ms.2.2.2.2.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) hc3_nz
    · exact h
  have h_val_ms_bound : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < 2 ^ 256 :=
    val256_bound _ _ _ _
  have h_val_a_lt_b :
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) <
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
    nlinarith [h_mulsub, hc3_pos, h_val_ms_bound, hqHat_eq_one]
  -- first-addback carry ≠ 0.
  have h_addback := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
  simp only [] at h_addback
  have h_ab_bound :
      val256 (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
             (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
             (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
             (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1 < 2 ^ 256 :=
    val256_bound _ _ _ _
  have hcarry_nz : addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≠ 0 := by
    intro h_carry_zero
    have h_carry_toNat : (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).toNat = 0 := by
      rw [h_carry_zero]; rfl
    rw [h_carry_toNat, Nat.zero_mul, Nat.add_zero] at h_addback
    nlinarith [h_addback, h_mulsub, hc3_pos, h_ab_bound, hqHat_eq_one]
  -- corrected quotient q_out = qHat + (2^64-1) = 0.
  have hq_out_eq : fullDivN4CallAddbackShift0QuotientV5
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) = (0 : Word) := by
    simp only [fullDivN4CallAddbackShift0QuotientV5, ← hqHat_def, ← hms_def]
    rw [if_neg hcarry_nz]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hqHat_eq_one, signExtend12_4095_toNat]
    decide
  -- a / b = 0 (a < b).
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) = a.toNat := by
    simp only [← getLimb_as_getLimbN_0, ← getLimb_as_getLimbN_1,
               ← getLimb_as_getLimbN_2, ← getLimb_as_getLimbN_3]
    exact val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) = b.toNat := by
    simp only [← getLimb_as_getLimbN_0, ← getLimb_as_getLimbN_1,
               ← getLimb_as_getLimbN_2, ← getLimb_as_getLimbN_3]
    exact val256_eq_toNat b
  have h_a_lt_b : a.toNat < b.toNat := by rw [ha_val, hb_val] at h_val_a_lt_b; exact h_val_a_lt_b
  have hdiv_eq_zero : EvmWord.div a b = 0 := by
    apply BitVec.eq_of_toNat_eq
    unfold EvmWord.div
    rw [if_neg hbnz]
    show (BitVec.udiv a b).toNat = (0 : EvmWord).toNat
    rw [show (BitVec.udiv a b).toNat = a.toNat / b.toNat from BitVec.toNat_udiv,
        show (0 : EvmWord).toNat = 0 from rfl]
    exact Nat.div_eq_of_lt h_a_lt_b
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdiv_eq_zero, getLimbN_zero, hq_out_eq]
  · rw [hdiv_eq_zero]; exact getLimbN_zero _
  · rw [hdiv_eq_zero]; exact getLimbN_zero _
  · rw [hdiv_eq_zero]; exact getLimbN_zero _

end EvmAsm.Evm64
