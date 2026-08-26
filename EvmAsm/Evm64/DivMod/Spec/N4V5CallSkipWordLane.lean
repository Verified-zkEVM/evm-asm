/-
  EvmAsm.Evm64.DivMod.Spec.N4V5CallSkipWordLane

  The n=4 v5 call-skip word equality (limb form): `(EvmWord.div a b).getLimbN 0 =
  divKTrialCallV5QHat u4 u3 b3'` (and limbs 1,2,3 = 0), reusing the v4 EvmWord-level
  quotient correctness `n4_call_skip_div_mod_getLimbN_v4` (which gives the same with
  `div128Quot_v4`) and rewriting through the v4↔v5 trial-quotient bridge.  The
  bridge equality is taken as a hypothesis `hbridge` here (it is discharged from
  `divKTrialCallV5QHat_eq_div128Quot_v4_of_no_wrap_of_le` (#7607) + the n=4 shape /
  no-wrap conditions in the lane).  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N4V5TrialQuotientV4Bridge
public import EvmAsm.Evm64.DivMod.Spec.CallSkipV4

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- n=4 v5 call-skip per-limb `EvmWord.div a b` facts, with the v5 trial quotient
    `divKTrialCallV5QHat`.  Reuses the v4 correctness + the v4↔v5 bridge `hbridge`. -/
theorem n4_call_skip_div_mod_getLimbN_v5 (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hsem : n4CallSkipSemanticHoldsV4 a b)
    (hbridge :
      divKTrialCallV5QHat
        ((a.getLimbN 3) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
        (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
          ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
        (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
          ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))) =
      div128Quot_v4
        ((a.getLimbN 3) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
        (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
          ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
        (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
          ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))) :
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
  obtain ⟨h0, h1, h2, h3⟩ := n4_call_skip_div_mod_getLimbN_v4 a b hbnz hshift_nz hborrow hsem
  exact ⟨h0.trans hbridge.symm, h1, h2, h3⟩

end EvmAsm.Evm64
