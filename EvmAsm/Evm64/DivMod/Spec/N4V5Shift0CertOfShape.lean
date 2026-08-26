/-
  EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CertOfShape

  Discharge of the n=4 v5 shift=0 runtime certificate `n4Shift0LaneRuntimeCertV5`
  from the n=4 SHAPE (`b3 ≠ 0`) plus `shift = 0`.  The skip/addback split is a
  tautology on the borrow flag `c3 = (mulsubN4 (v5 trial) b… a…).2.2.2.2`:

  * `c3 = 0` → call+skip branch: the no-borrow condition holds, and the quotient
    correctness comes from the shift=0 skip word equality (#7630).
  * `c3 ≠ 0` → call+addback branch: the borrow fires, the quotient correctness comes
    from the shift=0 addback word equality (#7632), and the `carry2` obligation is
    VACUOUSLY true because the first addback carry is nonzero (#7634).

  This is the final piece discharging the shift=0 obligation of `lane_n4` —
  feeding `hcert0` of `evm_div_n4_lane_v5_of_certs` (#7628).  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShift0
public import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CallSkipWordLane
public import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CallAddbackWordLane
public import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CallAddbackCarry

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (ult_iff)

/-- The n=4 v5 shift=0 runtime certificate holds for every n=4-shape divisor
    (`b3 ≠ 0`) on the shift=0 branch. -/
theorem evm_div_n4_shift0_cert_of_shape (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0) :
    n4Shift0LaneRuntimeCertV5 a b := by
  have hbnz : b ≠ 0 := fun h => hb3nz (by rw [h]; exact EvmWord.getLimbN_zero 3)
  unfold n4Shift0LaneRuntimeCertV5
  by_cases hc3 : (mulsubN4 (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 = 0
  · -- call+skip branch (no borrow).
    have hsb : mulsubN4NoBorrow (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) (0 : Word) := by
      unfold mulsubN4NoBorrow
      rw [hc3]; decide
    obtain ⟨hd0, hd1, hd2, hd3⟩ :=
      n4_shift0_call_skip_div_mod_getLimbN_v5 a b hbnz hshift_z hsb
    exact Or.inl ⟨hsb, hd0, hd1, hd2, hd3⟩
  · -- call+addback branch (borrow fires).
    have hc3t : (mulsubN4 (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2.toNat ≠ 0 := by
      intro h
      exact hc3 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    have hut : BitVec.ult (0 : Word)
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 = true := by
      rw [ult_iff]
      exact Nat.pos_of_ne_zero hc3t
    have hab : (if BitVec.ult (0 : Word)
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word) := by
      rw [hut]; decide
    have hcarry := n4_shift0_call_addback_first_carry_nz a b hshift_z hab
    obtain ⟨hd0, hd1, hd2, hd3⟩ :=
      n4_shift0_call_addback_div_getLimbN_v5 a b hbnz hshift_z hab
    exact Or.inr ⟨hab, fun hc0 => absurd hc0 hcarry, hd0, hd1, hd2, hd3⟩

end EvmAsm.Evm64
