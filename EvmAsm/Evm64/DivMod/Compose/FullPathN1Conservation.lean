/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1Conservation

  Compact per-iteration conservation wrappers for the n=1 full path.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified
import EvmAsm.Evm64.EvmWordArith.DivN4DoubleAddback

namespace EvmAsm.Evm64

open EvmAsm.Rv64

@[irreducible]
def n1StepConservation
    (v0 v1 v2 u0 u1 u2 u3 uTop : Word)
    (out : Word × Word × Word × Word × Word × Word) : Prop :=
  EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2^256 =
    out.1.toNat * EvmWord.val256 v0 v1 v2 0 +
      EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
      out.2.2.2.2.2.toNat * 2^256

@[irreducible]
def n1StepRemainderVal (out : Word × Word × Word × Word × Word × Word) : Nat :=
  EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1

@[irreducible]
def n1StepTopVal (out : Word × Word × Word × Word × Word × Word) : Nat :=
  out.2.2.2.2.2.toNat

@[irreducible]
def n1StepsCarryVal
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word) : Nat :=
  let B := 2^64
  n1StepTopVal r0 * B^4 + n1StepTopVal r1 * B^5 +
    n1StepTopVal r2 * B^6 + n1StepTopVal r3 * B^7

theorem n1StepRemainderVal_mul_base
    (out : Word × Word × Word × Word × Word × Word) :
    let B := 2^64
    n1StepRemainderVal out * B =
      out.2.1.toNat * B + out.2.2.1.toNat * B^2 +
        out.2.2.2.1.toNat * B^3 + out.2.2.2.2.1.toNat * B^4 := by
  intro B
  delta n1StepRemainderVal
  unfold EvmWord.val256
  ring

theorem n1StepTopVal_mul_base4
    (out : Word × Word × Word × Word × Word × Word) :
    let B := 2^64
    n1StepTopVal out * B^4 = out.2.2.2.2.2.toNat * 2^256 := by
  intro B
  delta n1StepTopVal
  norm_num

theorem n1StepConservation_remainder_le_input
    (v0 v1 v2 u0 u1 u2 u3 uTop : Word)
    (out : Word × Word × Word × Word × Word × Word)
    (h : n1StepConservation v0 v1 v2 u0 u1 u2 u3 uTop out) :
    n1StepRemainderVal out ≤ EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2^256 := by
  delta n1StepConservation at h
  delta n1StepRemainderVal
  omega

theorem n1StepConservation_remainder_lt_of_input_lt
    (v0 v1 v2 u0 u1 u2 u3 uTop : Word)
    (out : Word × Word × Word × Word × Word × Word) {bound : Nat}
    (h : n1StepConservation v0 v1 v2 u0 u1 u2 u3 uTop out)
    (hinput : EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2^256 < bound) :
    n1StepRemainderVal out < bound := by
  have hle := n1StepConservation_remainder_le_input
    v0 v1 v2 u0 u1 u2 u3 uTop out h
  omega

@[irreducible]
def n1StepsTelescoped
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word) : Prop :=
  let B := 2^64
  EvmWord.val256 u.1 u.2.1 u.2.2.1 u.2.2.2.1 +
      u.2.2.2.2.toNat * B^4 =
    (r3.1.toNat * B^3 + r2.1.toNat * B^2 +
        r1.1.toNat * B + r0.1.toNat) *
      EvmWord.val256 v.1 v.2.1 v.2.2.1 0 + n1StepRemainderVal r0 +
      n1StepsCarryVal r3 r2 r1 r0

@[irreducible]
def n1StepsConservation
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word) : Prop :=
  n1StepConservation v.1 v.2.1 v.2.2.1 u.2.2.2.1 u.2.2.2.2 0 0 0 r3 ∧
  n1StepConservation v.1 v.2.1 v.2.2.1 u.2.2.1
    r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1 r2 ∧
  n1StepConservation v.1 v.2.1 v.2.2.1 u.2.1
    r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 r1 ∧
  n1StepConservation v.1 v.2.1 v.2.2.1 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 r0

theorem n1NatStepConservation_telescope
    {B V q3 q2 q1 q0 rem3 rem2 rem1 rem0 top3 top2 top1 top0
      u0 u1 u2 u3 u4 : Nat}
    (h3 : u3 + u4 * B = q3 * V + rem3 + top3 * B^4)
    (h2 : u2 + rem3 * B = q2 * V + rem2 + top2 * B^4)
    (h1 : u1 + rem2 * B = q1 * V + rem1 + top1 * B^4)
    (h0 : u0 + rem1 * B = q0 * V + rem0 + top0 * B^4) :
    u0 + u1 * B + u2 * B^2 + u3 * B^3 + u4 * B^4 =
      (q3 * B^3 + q2 * B^2 + q1 * B + q0) * V + rem0 +
        top0 * B^4 + top1 * B^5 + top2 * B^6 + top3 * B^7 := by
  have H3 := congrArg (fun x => x * B^3) h3
  have H2 := congrArg (fun x => x * B^2) h2
  have H1 := congrArg (fun x => x * B) h1
  ring_nf at H3 H2 H1 h0 ⊢
  nlinarith

@[irreducible]
def fullDivN1StepsConservation
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  n1StepsConservation v u r3 r2 r1 r0

@[irreducible]
def fullDivN1StepsTelescoped
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  n1StepsTelescoped v u r3 r2 r1 r0

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

end EvmAsm.Evm64
