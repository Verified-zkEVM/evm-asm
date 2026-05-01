/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1ConservationRuntime

  Runtime-witness conservation lemmas for the n=1 full path. Split out of
  FullPathN1Conservation.lean (issue #1078) so the parent file fits under the
  1200-line cap. Contains the per-trial-step conservation theorems
  (`fullDivN1R{0..3}_step_conservation`) and their runtime-conservation
  bridges (`fullDivN1*_of_runtime`). Consumers: Spec/Dispatcher.lean.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1Conservation
import EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.CompensationCases
import EvmAsm.Evm64.EvmWordArith.DivN4DoubleAddback
import EvmAsm.Evm64.EvmWordArith.ModBridgeUtop

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem fullDivN1R3_step_conservation
    (bltu_3 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    n1StepConservation v.1 v.2.1 v.2.2.1 u.2.2.2.1 u.2.2.2.2 0 0 0
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3) := by
  intro v u
  delta n1StepConservation
  subst v; subst u
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hvnz :
      (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
    simpa [hv3z] using
      fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hc :
      Carry2NzAll (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 := by
    simpa [hv3z] using hcarry2
  have h := iterN1_val256_conservation_v3_zero_of_carry2 bltu_3
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    0 0 0 hvnz hc
  rw [fullDivN1R3_eq_iterN1_v3_zero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z]
  exact h

theorem fullDivN1R2_step_conservation
    (bltu_3 bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
    n1StepConservation v.1 v.2.1 v.2.2.1 u.2.2.1
      r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3) := by
  intro v u r3
  delta n1StepConservation
  subst v; subst u; subst r3
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hvnz :
      (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
    simpa [hv3z] using
      fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hc :
      Carry2NzAll (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 := by
    simpa [hv3z] using hcarry2
  have h := iterN1_val256_conservation_v3_zero_of_carry2 bltu_2
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    hvnz hc
  rw [fullDivN1R2_eq_iterN1_v3_zero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z]
  exact h

theorem fullDivN1R1_step_conservation
    (bltu_3 bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    n1StepConservation v.1 v.2.1 v.2.2.1 u.2.1
      r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3) := by
  intro v u r2
  delta n1StepConservation
  subst v; subst u; subst r2
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hvnz :
      (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
    simpa [hv3z] using
      fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hc :
      Carry2NzAll (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 := by
    simpa [hv3z] using hcarry2
  have h := iterN1_val256_conservation_v3_zero_of_carry2 bltu_1
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.1
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    hvnz hc
  rw [fullDivN1R1_eq_iterN1_v3_zero bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z]
  exact h

theorem fullDivN1R0_step_conservation
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    n1StepConservation v.1 v.2.1 v.2.2.1 u.1
      r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) := by
  intro v u r1
  delta n1StepConservation
  subst v; subst u; subst r1
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hvnz :
      (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
    simpa [hv3z] using
      fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hc :
      Carry2NzAll (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 := by
    simpa [hv3z] using hcarry2
  have h := iterN1_val256_conservation_v3_zero_of_carry2 bltu_0
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).1
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    hvnz hc
  rw [fullDivN1R0_eq_iterN1_v3_zero
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z]
  exact h

theorem fullDivN1StepsConservation_of_runtime
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    fullDivN1StepsConservation bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  delta fullDivN1StepsConservation
  delta n1StepsConservation
  constructor
  · exact fullDivN1R3_step_conservation
      bltu_3 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hcarry2
  constructor
  · exact fullDivN1R2_step_conservation
      bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hcarry2
  constructor
  · exact fullDivN1R1_step_conservation
      bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hcarry2
  · exact fullDivN1R0_step_conservation
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hcarry2

theorem fullDivN1StepsTelescoped_of_conservation
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hsteps : fullDivN1StepsConservation bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN1StepsTelescoped bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  delta fullDivN1StepsConservation at hsteps
  delta fullDivN1StepsTelescoped
  exact n1StepsTelescoped_of_conservation
    (fullDivN1NormV b0 b1 b2 b3)
    (fullDivN1NormU a0 a1 a2 a3 b0)
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    hsteps

theorem fullDivN1StepsTelescoped_of_runtime
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    fullDivN1StepsTelescoped bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 :=
  fullDivN1StepsTelescoped_of_conservation
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    (fullDivN1StepsConservation_of_runtime
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
      hb1z hb2z hb3z hbnz hcarry2)

theorem fullDivN1ExtendedRemainder_lt_of_runtime_quotient_le
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hge : EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat * (2^64)^3 +
        (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat * (2^64)^2 +
        (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat *
          (2^64) +
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat) :
    n1StepRemainderVal
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) +
        n1StepsCarryVal
          (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) <
      EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64) := by
  have htel := fullDivN1StepsTelescoped_of_runtime
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hb1z hb2z hb3z hbnz hcarry2
  exact fullDivN1ExtendedRemainder_lt_of_telescoped_quotient_le
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hb2z hb3z hbnz hshift_nz htel hge

theorem fullDivN1ExtendedRemainder_lt_of_runtime_quotientVal_le
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hge : EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
      fullDivN1QuotientVal bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3) :
    n1StepRemainderVal
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) +
        n1StepsCarryVal
          (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) <
      EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64) := by
  exact fullDivN1ExtendedRemainder_lt_of_runtime_quotient_le
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hb1z hb2z hb3z hbnz hshift_nz hcarry2 (by
      delta fullDivN1QuotientVal at hge
      simpa using hge)

theorem fullDivN1ExtendedRemainder_lt_of_runtime_correctedTrial_le
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hge : EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
      fullDivN1CorrectedTrialVal bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3) :
    n1StepRemainderVal
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) +
        n1StepsCarryVal
          (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) <
      EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64) := by
  have hcorr := fullDivN1CorrectedTrialVal_le_quotientVal
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z
  exact fullDivN1ExtendedRemainder_lt_of_runtime_quotientVal_le
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hb1z hb2z hb3z hbnz hshift_nz hcarry2 (Nat.le_trans hge hcorr)

theorem fullDivN1RemainderVal_eq_mod_mul_pow_of_runtime
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hlt : n1StepRemainderVal
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) +
        n1StepsCarryVal
          (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) <
      EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64)) :
    n1StepRemainderVal
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) =
      EvmWord.val256 a0 a1 a2 a3 % EvmWord.val256 b0 b1 b2 b3 *
        2 ^ ((fullDivN1Shift b0).toNat % 64) := by
  have htel := fullDivN1StepsTelescoped_of_runtime
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hb1z hb2z hb3z hbnz hcarry2
  have hbound : EvmWord.val256 a0 a1 a2 a3 % EvmWord.val256 b0 b1 b2 b3 *
        2 ^ ((fullDivN1Shift b0).toNat % 64) < 2^256 := by
    have hs : (fullDivN1Shift b0).toNat % 64 ≤ 64 := by omega
    have hb_pos : EvmWord.val256 b0 b1 b2 b3 > 0 :=
      EvmWord.val256_pos_of_or_ne_zero hbnz
    have hb3_bound : b3.toNat < 2 ^ (64 - (fullDivN1Shift b0).toNat % 64) := by
      rw [hb3z]
      positivity
    exact EvmWord.val256_mod_mul_pow_lt_pow256_of_b3_bound
      a0 a1 a2 a3 b0 b1 b2 b3 hs hb_pos hb3_bound
  exact fullDivN1RemainderVal_eq_mod_mul_pow_of_telescoped
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hb2z hb3z hshift_nz htel hlt hbound

theorem fullDivN1QuotientVal_eq_div_of_runtime
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hlt : n1StepRemainderVal
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) +
        n1StepsCarryVal
          (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) <
      EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64)) :
    EvmWord.val256
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1 =
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 := by
  have htel := fullDivN1StepsTelescoped_of_runtime
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hb1z hb2z hb3z hbnz hcarry2
  exact fullDivN1QuotientVal_eq_div_of_telescoped
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hb2z hb3z hshift_nz htel hlt

end EvmAsm.Evm64
