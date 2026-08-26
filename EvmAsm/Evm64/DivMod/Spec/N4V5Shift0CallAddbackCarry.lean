/-
  EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CallAddbackCarry

  The n=4 v5 shift=0 call+addback first-addback carry is nonzero:
  `addbackN4_carry (mulsub un-components) b… ≠ 0`, under the v5 raw-window addback
  borrow (`c3 ≠ 0`) and `shift = 0`.  On the shift=0 addback branch the trial
  `qHat = divKTrialCallV5QHat 0 a3 b3` is `1` and the firing borrow forces
  `val256 a < val256 b`; the addback then carries out (single addback), so the
  first carry is nonzero.  This is exactly the fact that makes the `carry2`
  obligation of `n4Shift0LaneRuntimeCertV5` (#7626) VACUOUSLY true on the addback
  branch (its premise `carry = 0` is false), letting the shift=0 certificate be
  assembled from the shape.  Companion to the addback word equality (#7632), with
  the same opaque-`qHat`/`ms` technique to dodge the v5 whnf term-size wall.
  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0TrialBounds
public import EvmAsm.Evm64.DivMod.SpecCallShift0

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256 val256_bound)

/-- n=4 v5 shift=0 call+addback first-addback carry ≠ 0 (under the firing borrow). -/
theorem n4_shift0_call_addback_first_carry_nz (a b : EvmWord)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : (if BitVec.ult (0 : Word)
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word)) :
    addbackN4_carry
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).1
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.1
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.1
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.1
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≠ 0 := by
  -- Opaque `qHat` / `ms` to dodge the v5 whnf term-size wall.
  obtain ⟨qHat, hqHat_def⟩ :
      ∃ q, q = divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3) := ⟨_, rfl⟩
  rw [← hqHat_def] at hborrow ⊢
  obtain ⟨ms, hms_def⟩ :
      ∃ m, m = mulsubN4 qHat
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) := ⟨_, rfl⟩
  rw [← hms_def] at hborrow ⊢
  have hc3_nz : ms.2.2.2.2 ≠ 0 := fun hc3z => hborrow (by rw [hc3z]; decide)
  have hb3_ge : (b.getLimbN 3).toNat ≥ 2 ^ 63 := clz_zero_imp_msb hshift_z
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
  -- carry ≠ 0.
  intro h_carry_zero
  have h_carry_toNat : (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).toNat = 0 := by
    rw [h_carry_zero]; rfl
  rw [h_carry_toNat, Nat.zero_mul, Nat.add_zero] at h_addback
  nlinarith [h_addback, h_mulsub, hc3_pos, h_ab_bound, hqHat_eq_one, val256_bound ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1]

end EvmAsm.Evm64
