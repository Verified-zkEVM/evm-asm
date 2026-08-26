module

public import EvmAsm.Evm64.DivMod.Spec.N1CarryZeroReducers
public import EvmAsm.Evm64.DivMod.Spec.N1FinalCarryZero
public import EvmAsm.Evm64.DivMod.Spec.N1PathCallbacks
public import EvmAsm.Evm64.DivMod.Spec.N1TrialWitnesses

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
/-- Shape-specialized n=1 full division limb theorem with the R3 carry-zero
    obligation discharged from the selected call's all-phases no-wrap
    invariant. This keeps the later R2/R1 carries, `hcarry2`, and quotient
    overestimate explicit for subsequent slices. -/
theorem n1_full_div_getLimbN_of_step_conservation_overestimate_r3_all_phases
    (a b : EvmWord) (bltu_2 bltu_1 bltu_0 : Bool)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hr3_inv : Div128AllPhasesNoWrapInv
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.2.2
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hr2_zero : fullDivN1R2CarryZero true bltu_2
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hr1_zero : fullDivN1R1CarryZero true bltu_2 bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hge : fullDivN1QuotientOverestimate true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 true bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 true bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  have hr3_zero : fullDivN1R3CarryZero true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1R3CarryZero_true_of_shape_all_phases_no_wrap
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnz hb1z hb2z hb3z hshift_nz hr3_inv
  exact n1_full_div_getLimbN_of_step_conservation_overestimate
    a b bltu_2 bltu_1 bltu_0 hbnz hb3z hb2z hb1z hshift_nz hcarry2
    hr3_zero hr2_zero hr1_zero hge

/-- Shape-specialized n=1 full division limb theorem for the all-call path.
    The R3/R2/R1 carry-zero obligations are discharged from concrete
    one-word remainder bounds plus the selected calls' all-phases no-wrap
    invariants. This leaves `hcarry2` and the quotient overestimate explicit
    for the later top-level wiring slices. -/
theorem n1_full_div_getLimbN_of_remainders_lt_all_phases_no_wrap
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hr3_lt :
      EvmWord.val256
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr2_lt :
      EvmWord.val256
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr1_lt :
      EvmWord.val256
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr3_inv : Div128AllPhasesNoWrapInv
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.2.2
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hr2_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R3 true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hr1_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R2 true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hfinal_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R1 true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hge : fullDivN1QuotientOverestimate true true true true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 true true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  obtain ⟨hr3_zero, hr2_zero, hr1_zero, _hfinal_zero⟩ :=
    fullDivN1CarryZeros_true_true_true_true_of_shape_remainders_lt_all_phases_no_wrap
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnz hb1z hb2z hb3z hshift_nz
      hr3_lt hr2_lt hr1_lt hr3_inv hr2_inv hr1_inv hfinal_inv
  exact n1_full_div_getLimbN_of_step_conservation_overestimate
    a b true true true hbnz hb3z hb2z hb1z hshift_nz hcarry2
    hr3_zero hr2_zero hr1_zero hge

/-- All-call n=1 hdiv wrapper where the legacy quotient-overestimate
    obligation is derived from the normalized final-remainder bound. -/
theorem n1_full_div_getLimbN_of_remainders_lt_all_phases_no_wrap_remainder_lt
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hr3_lt :
      EvmWord.val256
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr2_lt :
      EvmWord.val256
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr1_lt :
      EvmWord.val256
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr3_inv : Div128AllPhasesNoWrapInv
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.2.2
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hr2_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R3 true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hr1_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R2 true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hfinal_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R1 true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hrem_lt : fullDivN1NormalizedRemainderLt true true true true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 true true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  have hge :=
    fullDivN1QuotientOverestimate_true_true_true_true_of_shape_remainders_lt_all_phases_no_wrap
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_lt hr2_lt hr1_lt hr3_inv hr2_inv hr1_inv hfinal_inv hrem_lt
  exact n1_full_div_getLimbN_of_remainders_lt_all_phases_no_wrap
    a b hbnz hb3z hb2z hb1z hshift_nz hcarry2
    hr3_lt hr2_lt hr1_lt hr3_inv hr2_inv hr1_inv hfinal_inv hge

/-- `b ≠ 0` surface for the all-call n=1 hdiv limb-conjunction wrapper. -/
theorem n1_full_div_getLimbN_of_remainders_lt_all_phases_no_wrap_remainder_lt_ne_zero
    (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hr3_lt :
      EvmWord.val256
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr2_lt :
      EvmWord.val256
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr1_lt :
      EvmWord.val256
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr3_inv : Div128AllPhasesNoWrapInv
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.2.2
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hr2_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R3 true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hr1_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R2 true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hfinal_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R1 true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hrem_lt : fullDivN1NormalizedRemainderLt true true true true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 true true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  exact n1_full_div_getLimbN_of_remainders_lt_all_phases_no_wrap_remainder_lt
    a b ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz) hb3z hb2z hb1z hshift_nz hcarry2
    hr3_lt hr2_lt hr1_lt hr3_inv hr2_inv hr1_inv hfinal_inv hrem_lt

/-- Path-surface all-call n=1 hdiv wrapper. The one-word remainder bounds
    force the remaining trial branches to be `true`, so the callback can be
    consumed at the concrete `true true true` branch surface. -/
theorem n1_full_div_getLimbN_true_true_true_true_of_path_remainders_lt_all_phases_no_wrap
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hr3_lt :
      EvmWord.val256
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr2_lt :
      EvmWord.val256
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr1_lt :
      EvmWord.val256
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hpath : N1AllTruePathCallback a b) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 true true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  obtain ⟨hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_all_true_of_remainders_lt
      a b hbnz hb3z hb2z hb1z hshift_nz hr3_lt hr2_lt hr1_lt
  obtain ⟨hcarry2, hr3_inv, hr2_inv, hr1_inv, hfinal_inv, hrem_lt⟩ :=
    hpath hbltu_3 hbltu_2 hbltu_1 hbltu_0
  exact n1_full_div_getLimbN_of_remainders_lt_all_phases_no_wrap_remainder_lt_ne_zero
    a b ((EvmWord.ne_zero_iff_getLimbN_or).mpr hbnz) hb3z hb2z hb1z hshift_nz hcarry2
    hr3_lt hr2_lt hr1_lt hr3_inv hr2_inv hr1_inv hfinal_inv hrem_lt

/-- EvmWord-level all-call n=1 quotient-word wrapper from one-word step
    remainder bounds, all-phases no-wrap invariants, and the normalized
    final-remainder bound. -/
theorem n1_quotient_word_true_true_true_true_of_remainders_lt_all_phases_no_wrap
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hr3_lt :
      EvmWord.val256
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr2_lt :
      EvmWord.val256
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr1_lt :
      EvmWord.val256
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr3_inv : Div128AllPhasesNoWrapInv
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.2.2
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hr2_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R3 true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hr1_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R2 true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hfinal_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R1 true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hrem_lt : fullDivN1NormalizedRemainderLt true true true true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    fullDivN1QuotientWord true true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
      EvmWord.div a b := by
  have hword :=
    fullDivN1QuotientWord_true_true_true_true_of_shape_remainders_lt_all_phases_no_wrap
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_lt hr2_lt hr1_lt hr3_inv hr2_inv hr1_inv hfinal_inv hrem_lt
  change
      fullDivN1QuotientWord true true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div
          (EvmWord.fromLimbs fun i : Fin 4 =>
            match i with
            | 0 => a.getLimbN 0
            | 1 => a.getLimbN 1
            | 2 => a.getLimbN 2
            | 3 => a.getLimbN 3)
          (EvmWord.fromLimbs fun i : Fin 4 =>
            match i with
            | 0 => b.getLimbN 0
            | 1 => b.getLimbN 1
            | 2 => b.getLimbN 2
            | 3 => b.getLimbN 3) at hword
  exact hword.trans (by
    congr
    · exact EvmWord.fromLimbs_match_getLimbN_id a
    · exact EvmWord.fromLimbs_match_getLimbN_id b)

/-- `b ≠ 0` surface for the all-call n=1 quotient-word wrapper. -/
theorem n1_quotient_word_true_true_true_true_of_remainders_lt_all_phases_no_wrap_ne_zero
    (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hr3_lt :
      EvmWord.val256
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr2_lt :
      EvmWord.val256
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr1_lt :
      EvmWord.val256
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr3_inv : Div128AllPhasesNoWrapInv
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.2.2
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hr2_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R3 true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hr1_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R2 true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).2.1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hfinal_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R1 true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormU
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0)).1
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hrem_lt : fullDivN1NormalizedRemainderLt true true true true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    fullDivN1QuotientWord true true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
      EvmWord.div a b := by
  exact n1_quotient_word_true_true_true_true_of_remainders_lt_all_phases_no_wrap
    a b ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz) hb3z hb2z hb1z hshift_nz hcarry2
    hr3_lt hr2_lt hr1_lt hr3_inv hr2_inv hr1_inv hfinal_inv hrem_lt

/-- Path-surface all-call n=1 quotient-word wrapper. This is the word-equality
    counterpart of
    `n1_full_div_getLimbN_true_true_true_true_of_path_remainders_lt_all_phases_no_wrap`
    and matches the arithmetic evidence consumed by stack wrappers. -/
theorem n1_quotient_word_true_true_true_true_of_path_remainders_lt_all_phases_no_wrap
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hr3_lt :
      EvmWord.val256
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr2_lt :
      EvmWord.val256
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr1_lt :
      EvmWord.val256
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hpath : N1AllTruePathCallback a b) :
    fullDivN1QuotientWord true true true true
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
      EvmWord.div a b := by
  obtain ⟨hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_all_true_of_remainders_lt
      a b hbnz hb3z hb2z hb1z hshift_nz hr3_lt hr2_lt hr1_lt
  obtain ⟨hcarry2, hr3_inv, hr2_inv, hr1_inv, hfinal_inv, hrem_lt⟩ :=
    hpath hbltu_3 hbltu_2 hbltu_1 hbltu_0
  exact n1_quotient_word_true_true_true_true_of_remainders_lt_all_phases_no_wrap_ne_zero
    a b ((EvmWord.ne_zero_iff_getLimbN_or).mpr hbnz) hb3z hb2z hb1z hshift_nz hcarry2
    hr3_lt hr2_lt hr1_lt hr3_inv hr2_inv hr1_inv hfinal_inv hrem_lt

/-- Path-surface variant of
    `n1_shape_full_div_getLimbN_of_step_conservation_overestimate` where the
    callback provides the R3 all-phases no-wrap invariant instead of the R3
    carry-zero proof. -/
theorem n1_shape_full_div_getLimbN_of_step_conservation_overestimate_r3_all_phases
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1AllPhasesOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 true bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 true bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  obtain ⟨bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_call_first_of_getLimbN_shape_shift_nz
      a b hbnz hb3z hb2z hb1z hshift_nz
  obtain ⟨hcarry2, hr3_inv, hr2_zero, hr1_zero, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  exact ⟨bltu_2, bltu_1, bltu_0,
    hbltu_3, hbltu_2, hbltu_1, hbltu_0,
    n1_full_div_getLimbN_of_step_conservation_overestimate_r3_all_phases
      a b bltu_2 bltu_1 bltu_0 hbnz hb3z hb2z hb1z hshift_nz hcarry2
      hr3_inv hr2_zero hr1_zero hge⟩

/-- Quotient-word path wrapper whose callback provides the R3 all-phases
    invariant instead of the R3 carry-zero proof. -/
theorem n1_quotient_word_of_step_conservation_path_r3_all_phases
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1AllPhasesOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      fullDivN1QuotientWord true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  apply n1_quotient_word_of_step_conservation_path
    a b hbnz hb3z hb2z hb1z hshift_nz
  intro bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  obtain ⟨hcarry2, hr3_inv, hr2_zero, hr1_zero, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hr3_zero : fullDivN1R3CarryZero true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1R3CarryZero_true_of_shape_all_phases_no_wrap
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnz hb1z hb2z hb3z hshift_nz hr3_inv
  exact ⟨hcarry2, hr3_zero, hr2_zero, hr1_zero, hge⟩

/-- Quotient-word path wrapper whose callback provides the selected R3
    all-phases invariant as its three local no-wrap conjuncts. -/
theorem n1_quotient_word_of_step_conservation_path_r3_conjuncts
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1AllPhasesConjunctOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      fullDivN1QuotientWord true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  exact n1_quotient_word_of_step_conservation_path_r3_all_phases
    a b hbnz hb3z hb2z hb1z hshift_nz
    (N1AllPhasesConjunctOverestimatePathCallback.toAllPhasesOverestimatePathCallback hpath)

/-- Quotient-word package wrapper whose callback provides the R3 all-phases
    invariant instead of the R3 carry-zero proof. -/
theorem n1_quotient_word_package_of_step_conservation_path_r3_all_phases
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1AllPhasesOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      Carry2NzAll
        (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
        ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 0 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 1 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 2 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))) ∧
      fullDivN1QuotientWord true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  apply n1_quotient_word_package_of_step_conservation_path
    a b hbnz hb3z hb2z hb1z hshift_nz
  intro bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  obtain ⟨hcarry2, hr3_inv, hr2_zero, hr1_zero, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hr3_zero : fullDivN1R3CarryZero true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1R3CarryZero_true_of_shape_all_phases_no_wrap
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnz hb1z hb2z hb3z hshift_nz hr3_inv
  exact ⟨hcarry2, hr3_zero, hr2_zero, hr1_zero, hge⟩

/-- Quotient-word package wrapper whose callback provides the selected R3
    all-phases invariant as its three local no-wrap conjuncts. -/
theorem n1_quotient_word_package_of_step_conservation_path_r3_conjuncts
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1AllPhasesConjunctOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      Carry2NzAll
        (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
        ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 0 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 1 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 2 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))) ∧
      fullDivN1QuotientWord true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  exact n1_quotient_word_package_of_step_conservation_path_r3_all_phases
    a b hbnz hb3z hb2z hb1z hshift_nz
    (N1AllPhasesConjunctOverestimatePathCallback.toAllPhasesOverestimatePathCallback hpath)

/-- Normalized arithmetic package wrapper whose callback provides the R3
    all-phases invariant instead of the R3 carry-zero proof. This matches the
    package consumed by n=1 stack wrappers while reducing one arithmetic
    obligation in the callback surface. -/
theorem n1_normalized_mulsub_overestimate_of_step_conservation_path_r3_all_phases
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1AllPhasesOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      Carry2NzAll
        (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
        ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 0 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 1 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 2 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))) ∧
      fullDivN1NormalizedMulSubEq true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1QuotientOverestimate true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1QuotientWord true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  apply n1_normalized_mulsub_overestimate_of_step_conservation_path
    a b hbnz hb3z hb2z hb1z hshift_nz
  intro bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  obtain ⟨hcarry2, hr3_inv, hr2_zero, hr1_zero, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hr3_zero : fullDivN1R3CarryZero true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1R3CarryZero_true_of_shape_all_phases_no_wrap
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnz hb1z hb2z hb3z hshift_nz hr3_inv
  exact ⟨hcarry2, hr3_zero, hr2_zero, hr1_zero, hge⟩

/-- Normalized arithmetic package wrapper whose callback provides the selected
    R3 all-phases invariant as its three local no-wrap conjuncts. -/
theorem n1_normalized_mulsub_overestimate_of_step_conservation_path_r3_conjuncts
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1AllPhasesConjunctOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      Carry2NzAll
        (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
        ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 0 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 1 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 2 >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))) ∧
      fullDivN1NormalizedMulSubEq true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1QuotientOverestimate true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1QuotientWord true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  exact n1_normalized_mulsub_overestimate_of_step_conservation_path_r3_all_phases
    a b hbnz hb3z hb2z hb1z hshift_nz
    (N1AllPhasesConjunctOverestimatePathCallback.toAllPhasesOverestimatePathCallback hpath)

/-- Acceptance-shaped hdiv wrapper whose callback provides the R3 all-phases
    invariant instead of the R3 carry-zero proof. -/
theorem n1_full_div_getLimbN_of_step_conservation_path_r3_all_phases
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1AllPhasesOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 true bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 true bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  apply n1_full_div_getLimbN_of_step_conservation_path
    a b hbnz hb3z hb2z hb1z hshift_nz
  intro bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  obtain ⟨hcarry2, hr3_inv, hr2_zero, hr1_zero, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hr3_zero : fullDivN1R3CarryZero true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
    fullDivN1R3CarryZero_true_of_shape_all_phases_no_wrap
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hbnz hb1z hb2z hb3z hshift_nz hr3_inv
  exact ⟨hcarry2, hr3_zero, hr2_zero, hr1_zero, hge⟩

/-- Acceptance-shaped hdiv wrapper whose callback provides the selected R3
    all-phases invariant as its three local no-wrap conjuncts. -/
theorem n1_full_div_getLimbN_of_step_conservation_path_r3_conjuncts
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1AllPhasesConjunctOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 true bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 true bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  exact n1_full_div_getLimbN_of_step_conservation_path_r3_all_phases
    a b hbnz hb3z hb2z hb1z hshift_nz
    (N1AllPhasesConjunctOverestimatePathCallback.toAllPhasesOverestimatePathCallback hpath)

end EvmAsm.Evm64
