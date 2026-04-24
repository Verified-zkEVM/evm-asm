/-
  EvmAsm.Evm64.DivMod.Shift0AddbackMod

  Shift=0 call+addback-BEQ MOD pieces.
  Isolated to minimize whnf pressure.
-/

-- `SpecCall` transitively imports `EvmWordArith.Div128Shift0`.
import EvmAsm.Evm64.DivMod.SpecCall

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)
open EvmWord (val256)

/-- Under shift=0 + borrow-addback: `val256(a) < val256(b)`.

    Used both for `EvmWord.mod a b = a` and for the addback-BEQ bridge. -/
theorem n4_shift0_addback_val256_a_lt_b (a b : EvmWord)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) <
    val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  set qHat := div128Quot (0 : Word) (a.getLimbN 3) (b.getLimbN 3) with hqHat_def
  rw [isAddbackBorrowN4Shift0Evm_def] at hborrow
  unfold isAddbackBorrowN4Shift0 at hborrow
  simp only [] at hborrow
  have hc3_nz : mulsubN4_c3 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) ≠ 0 := by
    intro h; apply hborrow; rw [h]; decide
  have hb3_ge : (b.getLimbN 3).toNat ≥ 2^63 := clz_zero_imp_msb hshift_z
  have hqHat_le_one : qHat.toNat ≤ 1 := by
    rw [hqHat_def]; exact div128Quot_shift0_le_one _ _ hb3_ge
  have hqHat_nz : qHat ≠ 0 := by
    intro h_qHat_zero
    apply hc3_nz
    show (mulsubN4 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 = 0
    apply c3_un_zero_of_qHat_mul_le
    rw [h_qHat_zero]
    show (0 : Word).toNat * _ ≤ _
    rw [show (0 : Word).toNat = 0 from rfl, Nat.zero_mul]
    exact Nat.zero_le _
  have hqHat_eq_one : qHat.toNat = 1 := by
    have : qHat.toNat ≠ 0 := by
      intro h; apply hqHat_nz; apply BitVec.eq_of_toNat_eq; rw [h]; rfl
    omega
  have h_mulsub := mulsubN4_val256_eq qHat
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  simp only [] at h_mulsub
  set ms := mulsubN4 qHat
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) with hms_def
  have hc3_pos : ms.2.2.2.2.toNat ≥ 1 := by
    rcases Nat.eq_zero_or_pos ms.2.2.2.2.toNat with h | h
    · exfalso; apply hc3_nz
      show ms.2.2.2.2 = 0
      apply BitVec.eq_of_toNat_eq; rw [h]; rfl
    · exact h
  have h_val_ms_bound : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < 2^256 :=
    EvmWord.val256_bound _ _ _ _
  nlinarith

/-- Under shift=0 + borrow-addback + b ≠ 0: `EvmWord.mod a b = a`. -/
theorem n4_shift0_addback_mod_eq_a (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    EvmWord.mod a b = a := by
  apply BitVec.eq_of_toNat_eq
  unfold EvmWord.mod
  rw [if_neg hbnz]
  show (BitVec.umod a b).toNat = a.toNat
  have h_umod : (BitVec.umod a b).toNat = a.toNat % b.toNat := by
    show (a % b).toNat = _; exact BitVec.toNat_umod
  rw [h_umod]
  have h_val_a_lt_b := n4_shift0_addback_val256_a_lt_b a b hshift_z hborrow
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
  rw [ha_val, hb_val] at h_val_a_lt_b
  exact Nat.mod_eq_of_lt h_val_a_lt_b

/-- Under shift=0 + borrow-addback + b ≠ 0: the first-addback `carry ≠ 0`.
    Key fact that rules out double-addback under shift=0. -/
theorem n4_shift0_addback_carry_nz (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    let qHat := div128Quot (0 : Word) (a.getLimbN 3) (b.getLimbN 3)
    let ms := mulsubN4 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≠ 0 := by
  simp only []
  set qHat := div128Quot (0 : Word) (a.getLimbN 3) (b.getLimbN 3) with hqHat_def
  rw [isAddbackBorrowN4Shift0Evm_def] at hborrow
  unfold isAddbackBorrowN4Shift0 at hborrow
  simp only [] at hborrow
  have hc3_nz : mulsubN4_c3 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) ≠ 0 := by
    intro h; apply hborrow; rw [h]; decide
  have h_mulsub := mulsubN4_val256_eq qHat
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  simp only [] at h_mulsub
  set ms := mulsubN4 qHat
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) with hms_def
  have hc3_pos : ms.2.2.2.2.toNat ≥ 1 := by
    rcases Nat.eq_zero_or_pos ms.2.2.2.2.toNat with h | h
    · exfalso; apply hc3_nz
      show ms.2.2.2.2 = 0
      apply BitVec.eq_of_toNat_eq; rw [h]; rfl
    · exact h
  have h_addback := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
  simp only [] at h_addback
  set carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) with hcarry_def
  have h_val_ab_bound :
      val256 (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
             (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
             (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
             (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1 < 2^256 :=
    EvmWord.val256_bound _ _ _ _
  intro h_carry_zero
  have h_carry_toNat : carry.toNat = 0 := by rw [h_carry_zero]; rfl
  have h_ab := h_addback
  rw [h_carry_toNat, Nat.zero_mul, Nat.add_zero] at h_ab
  have h_val_ms_bound : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < 2^256 :=
    EvmWord.val256_bound _ _ _ _
  -- From h_mulsub: val256(a) + c3*2^256 = val256(ms) + qHat*val256(b)
  -- From h_ab: val256(ms) + val256(b) = val256(ab)
  -- Need val256(ab) < 2^256 (have it). Derive contradiction via c3 ≥ 1 +
  -- qHat.toNat ≤ 1 (which we don't have in this scope).
  -- Simpler argument: qHat.toNat is at most some value, but we need qHat * val256(b) ≥ val256(b) when qHat ≥ 1.
  -- c3 ≥ 1 ⟹ val256(a) + 2^256 ≤ val256(ms) + qHat*val256(b). With val256(a) < 2^256:
  -- val256(ms) + qHat*val256(b) > 2^256. If qHat = 0: val256(ms) > 2^256, impossible.
  -- So qHat ≥ 1, hence qHat*val256(b) ≥ val256(b), so val256(ms) + val256(b) ≥ val256(ms) + qHat*val256(b) - (qHat-1)*val256(b).
  -- We need: val256(ab) < 2^256 ∧ val256(ms) + val256(b) = val256(ab) + carry*2^256 = val256(ab).
  -- So val256(ms) + val256(b) < 2^256. But we want contradiction with: val256(ms) + val256(b) ≥ 2^256 (from c3 ≥ 1 + qHat ≥ 1).
  -- Need: val256(ms) + val256(b) ≥ 2^256 + val256(a) - c3*2^256 = 2^256(1-c3) + val256(a).
  -- With c3 = 1: ≥ val256(a), OK but not helpful.
  -- Wait: val256(ms) + qHat*val256(b) = val256(a) + c3*2^256 ≥ 0 + 2^256.
  -- val256(ms) + val256(b) ≥ val256(ms) + qHat*val256(b) - (qHat - 1)*val256(b).
  -- If qHat ≥ 1: val256(ms) + val256(b) ≥ 2^256 - (qHat - 1)*val256(b). Hmm not tight.
  -- Easier: qHat.toNat ≤ some bound. qHat is a Word so qHat.toNat ≤ 2^64 - 1. val256(b) ≤ 2^256 - 1.
  -- qHat*val256(b) ≤ (2^64 - 1)*(2^256 - 1) ≈ 2^320. Way bigger than 2^256. Won't help.
  -- Right approach: need qHat.toNat ≤ 1, which comes from div128Quot_shift0_le_one.
  have hb3_ge : (b.getLimbN 3).toNat ≥ 2^63 := clz_zero_imp_msb hshift_z
  have hqHat_le_one : qHat.toNat ≤ 1 := by
    rw [hqHat_def]; exact div128Quot_shift0_le_one _ _ hb3_ge
  have hb_nz_or :
      b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hb_pos_val :
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) > 0 :=
    EvmWord.val256_pos_of_or_ne_zero hb_nz_or
  have h_val_b_bound :
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) < 2^256 :=
    EvmWord.val256_bound _ _ _ _
  have h_val_a_bound :
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) < 2^256 :=
    EvmWord.val256_bound _ _ _ _
  -- h_mulsub: val256(a) + c3*2^256 = val256(ms) + qHat*val256(b)
  -- h_ab: val256(ms) + val256(b) = val256(ab)
  -- With val256(ab) < 2^256, val256(ms) + val256(b) < 2^256.
  -- With c3 ≥ 1: val256(a) + 2^256 ≤ val256(a) + c3*2^256 = val256(ms) + qHat*val256(b).
  -- So val256(ms) + qHat*val256(b) ≥ 2^256.
  -- With qHat ≤ 1: qHat*val256(b) ≤ val256(b).
  -- So val256(ms) + val256(b) ≥ val256(ms) + qHat*val256(b) - (1-qHat+some) = tricky.
  -- Direct: val256(ms) + val256(b) ≥ val256(ms) + qHat*val256(b) when qHat ≤ 1.
  -- Hmm only when qHat ≤ 1 AND we're comparing. qHat = 0 would give val256(ms) ≥ val256(ms), trivial.
  -- Let me split cases: qHat = 0 or qHat = 1.
  -- qHat = 0 ⟹ c3 = 0 (c3_un_zero_of_qHat_mul_le); contradicts hc3_pos.
  -- qHat = 1 ⟹ qHat*val256(b) = val256(b), so val256(ms) + val256(b) = val256(a) + c3*2^256 ≥ 2^256. Contradiction with val256(ab) < 2^256.
  have hqHat_nz : qHat ≠ 0 := by
    intro h_qHat_zero
    apply hc3_nz
    show (mulsubN4 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 = 0
    apply c3_un_zero_of_qHat_mul_le
    rw [h_qHat_zero]
    show (0 : Word).toNat * _ ≤ _
    rw [show (0 : Word).toNat = 0 from rfl, Nat.zero_mul]
    exact Nat.zero_le _
  have hqHat_eq_one : qHat.toNat = 1 := by
    have : qHat.toNat ≠ 0 := by
      intro h; apply hqHat_nz; apply BitVec.eq_of_toNat_eq; rw [h]; rfl
    omega
  have hq_mul : qHat.toNat * val256 (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3) =
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
    rw [hqHat_eq_one, Nat.one_mul]
  rw [hq_mul] at h_mulsub
  have h_pow : (2 : Nat) ^ 256 > 0 := by positivity
  nlinarith

/-- Helper — `val256(ab) = val256(a)` where `ab` is the first-addback output
    under shift=0 + borrow-addback. -/
theorem n4_shift0_addback_val256_ab_eq_a (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    let qHat := div128Quot (0 : Word) (a.getLimbN 3) (b.getLimbN 3)
    let ms := mulsubN4 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 =
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) := by
  simp only []
  set qHat := div128Quot (0 : Word) (a.getLimbN 3) (b.getLimbN 3) with hqHat_def
  rw [isAddbackBorrowN4Shift0Evm_def] at hborrow
  unfold isAddbackBorrowN4Shift0 at hborrow
  simp only [] at hborrow
  have hc3_nz : mulsubN4_c3 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) ≠ 0 := by
    intro h; apply hborrow; rw [h]; decide
  have hb3_ge : (b.getLimbN 3).toNat ≥ 2^63 := clz_zero_imp_msb hshift_z
  have hqHat_le_one : qHat.toNat ≤ 1 := by
    rw [hqHat_def]; exact div128Quot_shift0_le_one _ _ hb3_ge
  have hqHat_nz : qHat ≠ 0 := by
    intro h_qHat_zero
    apply hc3_nz
    show (mulsubN4 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 = 0
    apply c3_un_zero_of_qHat_mul_le
    rw [h_qHat_zero]
    show (0 : Word).toNat * _ ≤ _
    rw [show (0 : Word).toNat = 0 from rfl, Nat.zero_mul]
    exact Nat.zero_le _
  have hqHat_eq_one : qHat.toNat = 1 := by
    have : qHat.toNat ≠ 0 := by
      intro h; apply hqHat_nz; apply BitVec.eq_of_toNat_eq; rw [h]; rfl
    omega
  have h_mulsub := mulsubN4_val256_eq qHat
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  simp only [] at h_mulsub
  set ms := mulsubN4 qHat
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) with hms_def
  have hc3_pos : ms.2.2.2.2.toNat ≥ 1 := by
    rcases Nat.eq_zero_or_pos ms.2.2.2.2.toNat with h | h
    · exfalso; apply hc3_nz
      show ms.2.2.2.2 = 0
      apply BitVec.eq_of_toNat_eq; rw [h]; rfl
    · exact h
  have h_val_ms_bound : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < 2^256 :=
    EvmWord.val256_bound _ _ _ _
  have h_val_a_lt_b :
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) <
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
    nlinarith
  have hb_nz_or :
      b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hc3_le_one : ms.2.2.2.2.toNat ≤ 1 := by
    have h_q_over : qHat.toNat ≤
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 1 := by
      have h_div_zero :
          val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) = 0 :=
        Nat.div_eq_of_lt h_val_a_lt_b
      rw [h_div_zero]; omega
    exact mulsubN4_c3_le_one hb_nz_or h_q_over
  have hc3_eq_one : ms.2.2.2.2.toNat = 1 := by omega
  have h_addback := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
    ((0 : Word) - ms.2.2.2.2)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
  simp only [] at h_addback
  set ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) with hab_def
  set carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) with hcarry_def
  have h_val_ab_bound : val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 < 2^256 :=
    EvmWord.val256_bound _ _ _ _
  have h_val_b_bound :
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) < 2^256 :=
    EvmWord.val256_bound _ _ _ _
  have hcarry_le_one : carry.toNat ≤ 1 := by
    have h_pow_pos : (0 : Nat) < 2^256 := by positivity
    nlinarith
  have hcarry_nz : carry ≠ 0 := by
    intro h_carry_zero
    have h_carry_toNat : carry.toNat = 0 := by rw [h_carry_zero]; rfl
    have h_ab := h_addback
    rw [h_carry_toNat, Nat.zero_mul, Nat.add_zero] at h_ab
    have h_pow : (2 : Nat) ^ 256 > 0 := by positivity
    nlinarith
  have hcarry_pos : carry.toNat ≥ 1 := by
    rcases Nat.eq_zero_or_pos carry.toNat with h | h
    · exfalso; apply hcarry_nz
      apply BitVec.eq_of_toNat_eq; rw [h]; rfl
    · exact h
  have hcarry_eq_one : carry.toNat = 1 := by omega
  have hq_mul : qHat.toNat * val256 (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3) =
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
    rw [hqHat_eq_one, Nat.one_mul]
  rw [hq_mul] at h_mulsub
  omega

/-- Per-limb equality: `ab.1 = a.getLimbN 0` under shift=0 addback conditions. -/
theorem n4_shift0_addback_ab_eq_a_limb_0 (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    let qHat := div128Quot (0 : Word) (a.getLimbN 3) (b.getLimbN 3)
    let ms := mulsubN4 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
    = a.getLimbN 0 := by
  simp only []
  have h_val_ab_eq_a := n4_shift0_addback_val256_ab_eq_a a b hbnz hshift_z hborrow
  simp only [] at h_val_ab_eq_a
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  set ab := addbackN4 _ _ _ _ ((0 : Word) - _)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) with hab_def
  set mod_target : EvmWord := EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => ab.1 | 1 => ab.2.1 | 2 => ab.2.2.1 | 3 => ab.2.2.2.1
    with hmod_target
  have hmod_target_toNat : mod_target.toNat =
      val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 := by
    simp [mod_target, EvmWord.fromLimbs_toNat, val256]
  have hmod_target_eq_a : mod_target = a :=
    BitVec.eq_of_toNat_eq (by rw [hmod_target_toNat, h_val_ab_eq_a, ha_val])
  have : mod_target.getLimbN 0 = ab.1 := EvmWord.getLimbN_fromLimbs_0
  rw [← this, hmod_target_eq_a]

/-- Per-limb equality: `ab.2.1 = a.getLimbN 1`. -/
theorem n4_shift0_addback_ab_eq_a_limb_1 (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    let qHat := div128Quot (0 : Word) (a.getLimbN 3) (b.getLimbN 3)
    let ms := mulsubN4 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
    = a.getLimbN 1 := by
  simp only []
  have h_val_ab_eq_a := n4_shift0_addback_val256_ab_eq_a a b hbnz hshift_z hborrow
  simp only [] at h_val_ab_eq_a
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  set ab := addbackN4 _ _ _ _ ((0 : Word) - _)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) with hab_def
  set mod_target : EvmWord := EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => ab.1 | 1 => ab.2.1 | 2 => ab.2.2.1 | 3 => ab.2.2.2.1
    with hmod_target
  have hmod_target_toNat : mod_target.toNat =
      val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 := by
    simp [mod_target, EvmWord.fromLimbs_toNat, val256]
  have hmod_target_eq_a : mod_target = a :=
    BitVec.eq_of_toNat_eq (by rw [hmod_target_toNat, h_val_ab_eq_a, ha_val])
  have : mod_target.getLimbN 1 = ab.2.1 := EvmWord.getLimbN_fromLimbs_1
  rw [← this, hmod_target_eq_a]

/-- Per-limb equality: `ab.2.2.1 = a.getLimbN 2`. -/
theorem n4_shift0_addback_ab_eq_a_limb_2 (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    let qHat := div128Quot (0 : Word) (a.getLimbN 3) (b.getLimbN 3)
    let ms := mulsubN4 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
    = a.getLimbN 2 := by
  simp only []
  have h_val_ab_eq_a := n4_shift0_addback_val256_ab_eq_a a b hbnz hshift_z hborrow
  simp only [] at h_val_ab_eq_a
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  set ab := addbackN4 _ _ _ _ ((0 : Word) - _)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) with hab_def
  set mod_target : EvmWord := EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => ab.1 | 1 => ab.2.1 | 2 => ab.2.2.1 | 3 => ab.2.2.2.1
    with hmod_target
  have hmod_target_toNat : mod_target.toNat =
      val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 := by
    simp [mod_target, EvmWord.fromLimbs_toNat, val256]
  have hmod_target_eq_a : mod_target = a :=
    BitVec.eq_of_toNat_eq (by rw [hmod_target_toNat, h_val_ab_eq_a, ha_val])
  have : mod_target.getLimbN 2 = ab.2.2.1 := EvmWord.getLimbN_fromLimbs_2
  rw [← this, hmod_target_eq_a]

/-- Per-limb equality: `ab.2.2.2.1 = a.getLimbN 3`. -/
theorem n4_shift0_addback_ab_eq_a_limb_3 (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    let qHat := div128Quot (0 : Word) (a.getLimbN 3) (b.getLimbN 3)
    let ms := mulsubN4 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
    = a.getLimbN 3 := by
  simp only []
  have h_val_ab_eq_a := n4_shift0_addback_val256_ab_eq_a a b hbnz hshift_z hborrow
  simp only [] at h_val_ab_eq_a
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  set ab := addbackN4 _ _ _ _ ((0 : Word) - _)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) with hab_def
  set mod_target : EvmWord := EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => ab.1 | 1 => ab.2.1 | 2 => ab.2.2.1 | 3 => ab.2.2.2.1
    with hmod_target
  have hmod_target_toNat : mod_target.toNat =
      val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 := by
    simp [mod_target, EvmWord.fromLimbs_toNat, val256]
  have hmod_target_eq_a : mod_target = a :=
    BitVec.eq_of_toNat_eq (by rw [hmod_target_toNat, h_val_ab_eq_a, ha_val])
  have : mod_target.getLimbN 3 = ab.2.2.2.1 := EvmWord.getLimbN_fromLimbs_3
  rw [← this, hmod_target_eq_a]

/-- **EVM-stack-level MOD spec on the n=4 shift=0 call+addback-BEQ sub-path.**

    MOD counterpart to `evm_div_n4_shift0_call_addback_beq_stack_spec`. Uses
    the separately-proven `carry_nz` and per-limb equalities to avoid whnf
    blow-up on large conjunctions. -/
theorem evm_mod_n4_shift0_call_addback_beq_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hcarry2_nz : isAddbackCarry2NzN4Shift0Evm a b)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modN4CallSkipStackPost sp a b) := by
  have h_pre := evm_mod_n4_full_shift0_call_addback_beq_stack_pre_spec_bundled
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hcarry2_nz hborrow
  have h_carry_nz := n4_shift0_addback_carry_nz a b hbnz hshift_z hborrow
  have h_mod_eq_a := n4_shift0_addback_mod_eq_a a b hbnz hshift_z hborrow
  have h_ab0 := n4_shift0_addback_ab_eq_a_limb_0 a b hbnz hshift_z hborrow
  have h_ab1 := n4_shift0_addback_ab_eq_a_limb_1 a b hbnz hshift_z hborrow
  have h_ab2 := n4_shift0_addback_ab_eq_a_limb_2 a b hbnz hshift_z hborrow
  have h_ab3 := n4_shift0_addback_ab_eq_a_limb_3 a b hbnz hshift_z hborrow
  simp only [] at h_carry_nz h_ab0 h_ab1 h_ab2 h_ab3
  -- Limb equalities between the post's ab.i and (EvmWord.mod a b).getLimbN i.
  have hmod0 := (congrArg (·.getLimbN 0) h_mod_eq_a).trans h_ab0.symm
  have hmod1 := (congrArg (·.getLimbN 1) h_mod_eq_a).trans h_ab1.symm
  have hmod2 := (congrArg (·.getLimbN 2) h_mod_eq_a).trans h_ab2.symm
  have hmod3 := (congrArg (·.getLimbN 3) h_mod_eq_a).trans h_ab3.symm
  refine cpsTriple_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  unfold fullModN4Shift0CallAddbackBeqPost at hq
  apply mod_n4_call_skip_stack_weaken sp a b h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  -- The post has `un_iOut = if carry = 0 then ab'.i else ab.i`.
  -- Apply if_neg h_carry_nz to reduce to ab.i, then apply evmWordIs_sp32_limbs_eq.
  simp only [if_neg h_carry_nz] at hq
  rw [evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _
      hmod0 hmod1 hmod2 hmod3]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

end EvmAsm.Evm64
