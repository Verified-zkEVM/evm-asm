/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1Conservation

  Compact per-iteration conservation wrappers for the n=1 full path.
-/


import EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.CompensationCases
import EvmAsm.Evm64.EvmWordArith.DivN4DoubleAddback
import EvmAsm.Evm64.EvmWordArith.ModBridgeUtop

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

@[irreducible]
def n1StepConservationNat
    (v0 v1 v2 u0 u1 u2 u3 uTop : Word)
    (out : Word × Word × Word × Word × Word × Word) : Prop :=
  u0.toNat + u1.toNat * 2^64 + u2.toNat * 2^128 + u3.toNat * 2^192 +
      uTop.toNat * 2^256 =
    out.1.toNat * EvmWord.val256 v0 v1 v2 0 +
      n1StepRemainderVal out + n1StepTopVal out * 2^256

theorem n1StepConservationNat_of_conservation
    (v0 v1 v2 u0 u1 u2 u3 uTop : Word)
    (out : Word × Word × Word × Word × Word × Word)
    (h : n1StepConservation v0 v1 v2 u0 u1 u2 u3 uTop out) :
    n1StepConservationNat v0 v1 v2 u0 u1 u2 u3 uTop out := by
  delta n1StepConservation at h
  delta n1StepConservationNat
  unfold EvmWord.val256 at h ⊢
  delta n1StepRemainderVal n1StepTopVal
  exact h

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

theorem n1StepExtendedRemainder_lt_of_floor_le
    (v0 v1 v2 u0 u1 u2 u3 uTop : Word)
    (out : Word × Word × Word × Word × Word × Word)
    (hbnz : v0 ||| v1 ||| v2 ||| (0 : Word) ≠ 0)
    (h : n1StepConservation v0 v1 v2 u0 u1 u2 u3 uTop out)
    (hge : (EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2^256) /
        EvmWord.val256 v0 v1 v2 0 ≤ out.1.toNat) :
    n1StepRemainderVal out + n1StepTopVal out * 2^256 <
      EvmWord.val256 v0 v1 v2 0 := by
  have hv_pos : 0 < EvmWord.val256 v0 v1 v2 0 :=
    EvmWord.val256_pos_of_or_ne_zero hbnz
  have heq : EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2^256 =
      out.1.toNat * EvmWord.val256 v0 v1 v2 0 +
        (n1StepRemainderVal out + n1StepTopVal out * 2^256) := by
    delta n1StepConservation at h
    delta n1StepRemainderVal n1StepTopVal
    omega
  have ⟨_, hr_lt⟩ := EvmWord.remainder_lt_of_ge_floor hv_pos heq hge
  exact hr_lt

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

@[irreducible]
def n1StepsConservationNat
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word) : Prop :=
  n1StepConservationNat v.1 v.2.1 v.2.2.1 u.2.2.2.1 u.2.2.2.2 0 0 0 r3 ∧
  n1StepConservationNat v.1 v.2.1 v.2.2.1 u.2.2.1
    r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1 r2 ∧
  n1StepConservationNat v.1 v.2.1 v.2.2.1 u.2.1
    r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 r1 ∧
  n1StepConservationNat v.1 v.2.1 v.2.2.1 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 r0

@[irreducible]
def n1StepsTelescopeInput
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word) : Prop :=
  let B := 2^64
  let V := EvmWord.val256 v.1 v.2.1 v.2.2.1 0
  u.2.2.2.1.toNat + u.2.2.2.2.toNat * B =
    r3.1.toNat * V + n1StepRemainderVal r3 + n1StepTopVal r3 * B^4 ∧
  u.2.2.1.toNat + n1StepRemainderVal r3 * B =
    r2.1.toNat * V + n1StepRemainderVal r2 + n1StepTopVal r2 * B^4 ∧
  u.2.1.toNat + n1StepRemainderVal r2 * B =
    r1.1.toNat * V + n1StepRemainderVal r1 + n1StepTopVal r1 * B^4 ∧
  u.1.toNat + n1StepRemainderVal r1 * B =
    r0.1.toNat * V + n1StepRemainderVal r0 + n1StepTopVal r0 * B^4

theorem n1StepsConservationNat_of_conservation
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word)
    (hsteps : n1StepsConservation v u r3 r2 r1 r0) :
    n1StepsConservationNat v u r3 r2 r1 r0 := by
  delta n1StepsConservation at hsteps
  delta n1StepsConservationNat
  rcases hsteps with ⟨h3, h2, h1, h0⟩
  exact ⟨
    n1StepConservationNat_of_conservation _ _ _ _ _ _ _ _ _ h3,
    n1StepConservationNat_of_conservation _ _ _ _ _ _ _ _ _ h2,
    n1StepConservationNat_of_conservation _ _ _ _ _ _ _ _ _ h1,
    n1StepConservationNat_of_conservation _ _ _ _ _ _ _ _ _ h0⟩

theorem n1TelescopeInput3_of_nat
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 : Word × Word × Word × Word × Word × Word)
    (h3 : n1StepConservationNat v.1 v.2.1 v.2.2.1
      u.2.2.2.1 u.2.2.2.2 0 0 0 r3) :
    let B := 2^64
    let V := EvmWord.val256 v.1 v.2.1 v.2.2.1 0
    u.2.2.2.1.toNat + u.2.2.2.2.toNat * B =
      r3.1.toNat * V + n1StepRemainderVal r3 + n1StepTopVal r3 * B^4 := by
  intro B V
  delta n1StepConservationNat at h3
  subst B; subst V
  simp at h3 ⊢
  exact h3

theorem n1TelescopeInput_of_nat_remainder
    (v0 v1 v2 u0 : Word)
    (rin rout : Word × Word × Word × Word × Word × Word)
    (h : n1StepConservationNat v0 v1 v2 u0
      rin.2.1 rin.2.2.1 rin.2.2.2.1 rin.2.2.2.2.1 rout) :
    let B := 2^64
    let V := EvmWord.val256 v0 v1 v2 0
    u0.toNat + n1StepRemainderVal rin * B =
      rout.1.toNat * V + n1StepRemainderVal rout + n1StepTopVal rout * B^4 := by
  intro B V
  delta n1StepConservationNat at h
  rw [n1StepRemainderVal_mul_base]
  subst B; subst V
  norm_num at h ⊢
  omega

theorem n1StepsTelescopeInput_of_nat_conservation
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word)
    (hsteps : n1StepsConservationNat v u r3 r2 r1 r0) :
    n1StepsTelescopeInput v u r3 r2 r1 r0 := by
  delta n1StepsConservationNat at hsteps
  delta n1StepsTelescopeInput
  rcases hsteps with ⟨h3, h2, h1, h0⟩
  exact ⟨
    n1TelescopeInput3_of_nat v u r3 h3,
    n1TelescopeInput_of_nat_remainder v.1 v.2.1 v.2.2.1 u.2.2.1 r3 r2 h2,
    n1TelescopeInput_of_nat_remainder v.1 v.2.1 v.2.2.1 u.2.1 r2 r1 h1,
    n1TelescopeInput_of_nat_remainder v.1 v.2.1 v.2.2.1 u.1 r1 r0 h0⟩

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

theorem n1StepsTelescoped_of_telescopeInput
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word)
    (hinput : n1StepsTelescopeInput v u r3 r2 r1 r0) :
    n1StepsTelescoped v u r3 r2 r1 r0 := by
  delta n1StepsTelescopeInput at hinput
  delta n1StepsTelescoped n1StepsCarryVal
  rcases hinput with ⟨h3, h2, h1, h0⟩
  have ht := n1NatStepConservation_telescope h3 h2 h1 h0
  unfold EvmWord.val256 at ht ⊢
  ring_nf at ht ⊢
  exact ht

theorem n1StepsTelescoped_of_nat_conservation
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word)
    (hsteps : n1StepsConservationNat v u r3 r2 r1 r0) :
    n1StepsTelescoped v u r3 r2 r1 r0 :=
  n1StepsTelescoped_of_telescopeInput v u r3 r2 r1 r0
    (n1StepsTelescopeInput_of_nat_conservation v u r3 r2 r1 r0 hsteps)

theorem n1StepsTelescoped_of_conservation
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word)
    (hsteps : n1StepsConservation v u r3 r2 r1 r0) :
    n1StepsTelescoped v u r3 r2 r1 r0 :=
  n1StepsTelescoped_of_nat_conservation v u r3 r2 r1 r0
    (n1StepsConservationNat_of_conservation v u r3 r2 r1 r0 hsteps)

theorem n1StepsRemainderVal_eq_of_extended_eq_lt_pow256
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word) {target : Nat}
    (h : n1StepRemainderVal r0 + n1StepsCarryVal r3 r2 r1 r0 = target)
    (ht : target < 2^256) :
    n1StepRemainderVal r0 = target := by
  delta n1StepsCarryVal n1StepTopVal at h
  norm_num at h ht ⊢
  have hr : n1StepRemainderVal r0 < 2^256 := by
    delta n1StepRemainderVal
    exact EvmWord.val256_bound _ _ _ _
  omega

theorem n1StepsRemainderVal_eq_mod_mul_pow_of_normalized_euclidean
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word)
    {aVal bVal qVal s : Nat}
    (heq : aVal * 2^s =
      qVal * (bVal * 2^s) + (n1StepRemainderVal r0 + n1StepsCarryVal r3 r2 r1 r0))
    (hlt : n1StepRemainderVal r0 + n1StepsCarryVal r3 r2 r1 r0 < bVal * 2^s)
    (hbound : aVal % bVal * 2^s < 2^256) :
    n1StepRemainderVal r0 = aVal % bVal * 2^s := by
  have htarget := EvmWord.normalized_remainder_eq_mod_mul_pow s heq hlt
  exact n1StepsRemainderVal_eq_of_extended_eq_lt_pow256 r3 r2 r1 r0 htarget hbound

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

@[irreducible]
def fullDivN1QuotientVal
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Nat :=
  let B := 2^64
  let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  r3.1.toNat * B^3 + r2.1.toNat * B^2 + r1.1.toNat * B + r0.1.toNat

@[irreducible]
def fullDivN1CorrectedTrialVal
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Nat :=
  let B := 2^64
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let qHat3 : Word := if bltu_3 then div128Quot u.2.2.2.2 u.2.2.2.1 v.1
    else signExtend12 4095
  let qHat2 : Word := if bltu_2 then div128Quot r3.2.1 u.2.2.1 v.1
    else signExtend12 4095
  let qHat1 : Word := if bltu_1 then div128Quot r2.2.1 u.2.1 v.1
    else signExtend12 4095
  let qHat0 : Word := if bltu_0 then div128Quot r1.2.1 u.1 v.1
    else signExtend12 4095
  (qHat3.toNat - 2) * B^3 + (qHat2.toNat - 2) * B^2 +
    (qHat1.toNat - 2) * B + (qHat0.toNat - 2)

theorem fullDivN1QuotientVal_eq_val256
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN1QuotientVal bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.val256
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  delta fullDivN1QuotientVal
  unfold EvmWord.val256
  ring

theorem fullDivN1TrialBranches_of_isTrial
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
    let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    bltu_3 = BitVec.ult u.2.2.2.2 v.1 ∧
      bltu_2 = BitVec.ult r3.2.1 v.1 ∧
      bltu_1 = BitVec.ult r2.2.1 v.1 ∧
      bltu_0 = BitVec.ult r1.2.1 v.1 := by
  intro v u r3 r2 r1
  subst v; subst u; subst r3; subst r2; subst r1
  constructor
  · delta isTrialN1_j3 fullDivN1NormU fullDivN1NormV
      fullDivN1Shift fullDivN1AntiShift at hbltu_3 ⊢
    simpa using hbltu_3
  constructor
  · delta isTrialN1_j2 fullDivN1R3 fullDivN1NormU fullDivN1NormV
      fullDivN1Shift fullDivN1AntiShift at hbltu_2 ⊢
    simpa using hbltu_2
  constructor
  · delta isTrialN1_j1 fullDivN1R2 fullDivN1R3 fullDivN1NormU fullDivN1NormV
      fullDivN1Shift fullDivN1AntiShift at hbltu_1 ⊢
    simpa using hbltu_1
  · delta isTrialN1_j0 fullDivN1R1 fullDivN1R2 fullDivN1R3 fullDivN1NormU
      fullDivN1NormV fullDivN1Shift fullDivN1AntiShift at hbltu_0 ⊢
    simpa using hbltu_0

theorem fullDivN1NormV_shape_of_high_zero
    (b0 b1 b2 b3 : Word) (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0) (hshift_nz : fullDivN1Shift b0 ≠ 0) :
    let v := fullDivN1NormV b0 b1 b2 b3
    v.2.1 = 0 ∧ v.2.2.1 = 0 ∧ v.2.2.2 = 0 ∧
      v.1 ||| v.2.1 ||| v.2.2.1 ||| v.2.2.2 ≠ 0 := by
  intro v
  subst v
  exact ⟨
    fullDivN1NormV_v1_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_v2_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z,
    fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz⟩

theorem fullDivN1NormV_val256_eq_v0_of_high_zero
    (b0 b1 b2 b3 : Word) (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0) :
    let v := fullDivN1NormV b0 b1 b2 b3
    EvmWord.val256 v.1 v.2.1 v.2.2.1 v.2.2.2 = v.1.toNat := by
  intro v
  have hv1 := fullDivN1NormV_v1_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hshift_nz
  have hv2 := fullDivN1NormV_v2_eq_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z
  have hv3 := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  subst v
  rw [hv1, hv2, hv3]
  unfold EvmWord.val256
  simp

theorem iterN1_rawTrial_ge_local_floor_of_top_lt_pow63
    (bltu : Bool) (v0 u0 uTop : Word)
    (hv0_ge : v0.toNat ≥ 2^63)
    (huTop_lt_pow63 : uTop.toNat < 2^63)
    (hbranch : bltu = BitVec.ult uTop v0) :
    let qHat : Word := if bltu then div128Quot uTop u0 v0 else signExtend12 4095
    (uTop.toNat * 2^64 + u0.toNat) / v0.toNat ≤ qHat.toNat := by
  intro qHat
  subst qHat
  have huTop_lt_v0 : uTop.toNat < v0.toNat := by omega
  have hult : BitVec.ult uTop v0 = true := (EvmWord.ult_iff).mpr huTop_lt_v0
  cases hbltu : bltu
  · have hfalse : BitVec.ult uTop v0 = false := by
      simpa [hbltu] using hbranch
    rw [hult] at hfalse
    cases hfalse
  · simp only [if_true]
    exact div128Quot_ge_q_true_normalized uTop u0 v0 hv0_ge huTop_lt_v0 huTop_lt_pow63

theorem fullDivN1R3_rawTrial_ge_local_floor
    (bltu_3 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let qHat : Word := if bltu_3 then div128Quot u.2.2.2.2 u.2.2.2.1 v.1
      else signExtend12 4095
    (u.2.2.2.2.toNat * 2^64 + u.2.2.2.1.toNat) / v.1.toNat ≤ qHat.toNat := by
  intro v u qHat
  subst v
  subst u
  subst qHat
  have hv0_ge : ((fullDivN1NormV b0 b1 b2 b3).1).toNat ≥ 2^63 :=
    fullDivN1NormV_v0_ge_pow63_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have h_shift_pos : 1 ≤ (fullDivN1Shift b0).toNat :=
    fullDivN1Shift_toNat_pos_of_ne_zero hshift_nz
  have h_shift_le : (fullDivN1Shift b0).toNat ≤ 63 := by
    have hlt := fullDivN1Shift_toNat_lt_64 b0
    omega
  have huTop_lt_pow63 : ((fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2).toNat <
      2^63 := by
    rw [fullDivN1NormU_unfold]
    simp only []
    rw [fullDivN1AntiShift_unfold]
    exact u_top_lt_pow63_of_shift_nz a3 (fullDivN1Shift b0) h_shift_pos
      h_shift_le
  exact iterN1_rawTrial_ge_local_floor_of_top_lt_pow63 bltu_3
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    hv0_ge huTop_lt_pow63 (by
      delta isTrialN1_j3 at hbltu_3
      simpa [fullDivN1NormU_unfold, fullDivN1NormV_unfold,
        fullDivN1Shift_unfold, fullDivN1AntiShift_unfold] using hbltu_3)

theorem iterWithDoubleAddback_qout_ge_sub_two
    (q v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) (hq2 : 2 ≤ q.toNat) :
    let out := iterWithDoubleAddback q v0 v1 v2 v3 u0 u1 u2 u3 uTop
    q.toNat - 2 ≤ out.1.toNat := by
  intro out
  subst out
  by_cases hb : BitVec.ult uTop (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  · rw [iterWithDoubleAddback_borrow (qHat := q) (v0 := v0) (v1 := v1)
      (v2 := v2) (v3 := v3) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
      (uTop := uTop) hb]
    let ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
      (uTop - ms.2.2.2.2) v0 v1 v2 v3
    by_cases hcarry : carry = 0
    · rw [if_pos hcarry]
      rw [add_signExtend12_4095_add_signExtend12_4095_toNat q hq2]
    · rw [if_neg hcarry]
      rw [add_signExtend12_4095_toNat q (by omega)]
      omega
  · rw [iterWithDoubleAddback_no_borrow (qHat := q) (v0 := v0) (v1 := v1)
      (v2 := v2) (v3 := v3) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
      (uTop := uTop) hb]
    simp

theorem iterWithDoubleAddback_qout_ge_tsub_two
    (q v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    let out := iterWithDoubleAddback q v0 v1 v2 v3 u0 u1 u2 u3 uTop
    q.toNat - 2 ≤ out.1.toNat := by
  intro out
  by_cases hq2 : 2 ≤ q.toNat
  · exact iterWithDoubleAddback_qout_ge_sub_two q v0 v1 v2 v3 u0 u1 u2 u3 uTop hq2
  · have hzero : q.toNat - 2 = 0 := by omega
    rw [hzero]
    exact Nat.zero_le _

theorem iterN1_qout_ge_trial_sub_two
    (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    let qHat : Word := if bltu then div128Quot u1 u0 v0 else signExtend12 4095
    let out := iterN1 bltu v0 v1 v2 v3 u0 u1 u2 u3 uTop
    qHat.toNat - 2 ≤ out.1.toNat := by
  intro qHat out
  subst qHat
  subst out
  cases bltu
  · simp only [iterN1_false]
    unfold iterN1Max
    exact iterWithDoubleAddback_qout_ge_sub_two
      (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 uTop (by
        rw [signExtend12_4095_toNat]
        norm_num)
  · simp only [ite_true, iterN1_true]
    unfold iterN1Call
    exact iterWithDoubleAddback_qout_ge_tsub_two
      (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop

theorem fullDivN1R3_qout_ge_trial_sub_two
    (bltu_3 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb2z : b2 = 0) (hb3z : b3 = 0) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let qHat : Word := if bltu_3 then div128Quot u.2.2.2.2 u.2.2.2.1 v.1
      else signExtend12 4095
    qHat.toNat - 2 ≤
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat := by
  intro v u qHat
  subst v
  subst u
  subst qHat
  rw [fullDivN1R3_eq_iterN1_v3_zero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z]
  exact iterN1_qout_ge_trial_sub_two bltu_3
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    0
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    0 0 0

theorem fullDivN1R2_qout_ge_trial_sub_two
    (bltu_3 bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb2z : b2 = 0) (hb3z : b3 = 0) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
    let qHat : Word := if bltu_2 then div128Quot r3.2.1 u.2.2.1 v.1
      else signExtend12 4095
    qHat.toNat - 2 ≤
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat := by
  intro v u r3 qHat
  subst v
  subst u
  subst r3
  subst qHat
  rw [fullDivN1R2_eq_iterN1_v3_zero
    bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z]
  exact iterN1_qout_ge_trial_sub_two bltu_2
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    0
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1

theorem fullDivN1R1_qout_ge_trial_sub_two
    (bltu_3 bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb2z : b2 = 0) (hb3z : b3 = 0) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    let qHat : Word := if bltu_1 then div128Quot r2.2.1 u.2.1 v.1
      else signExtend12 4095
    qHat.toNat - 2 ≤
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat := by
  intro v u r2 qHat
  subst v
  subst u
  subst r2
  subst qHat
  rw [fullDivN1R1_eq_iterN1_v3_zero
    bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z]
  exact iterN1_qout_ge_trial_sub_two bltu_1
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    0
    (fullDivN1NormU a0 a1 a2 a3 b0).2.1
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1

theorem fullDivN1R0_qout_ge_trial_sub_two
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb2z : b2 = 0) (hb3z : b3 = 0) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    let qHat : Word := if bltu_0 then div128Quot r1.2.1 u.1 v.1
      else signExtend12 4095
    qHat.toNat - 2 ≤
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat := by
  intro v u r1 qHat
  subst v
  subst u
  subst r1
  subst qHat
  rw [fullDivN1R0_eq_iterN1_v3_zero
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z]
  exact iterN1_qout_ge_trial_sub_two bltu_0
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    0
    (fullDivN1NormU a0 a1 a2 a3 b0).1
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1

theorem fullDivN1CorrectedTrialVal_le_quotientVal
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb2z : b2 = 0) (hb3z : b3 = 0) :
    fullDivN1CorrectedTrialVal bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 ≤
      fullDivN1QuotientVal bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 := by
  have h3 := fullDivN1R3_qout_ge_trial_sub_two
    bltu_3 a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z
  have h2 := fullDivN1R2_qout_ge_trial_sub_two
    bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z
  have h1 := fullDivN1R1_qout_ge_trial_sub_two
    bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z
  have h0 := fullDivN1R0_qout_ge_trial_sub_two
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z
  delta fullDivN1CorrectedTrialVal fullDivN1QuotientVal
  simp only [] at h3 h2 h1 h0 ⊢
  nlinarith [h3, h2, h1, h0]

theorem fullDivN1RemainderVal_eq_mod_mul_pow_of_telescoped
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (htel : fullDivN1StepsTelescoped bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hlt : n1StepRemainderVal
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) +
        n1StepsCarryVal
          (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
          (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) <
      EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64))
    (hbound : EvmWord.val256 a0 a1 a2 a3 % EvmWord.val256 b0 b1 b2 b3 *
        2 ^ ((fullDivN1Shift b0).toNat % 64) < 2^256) :
    n1StepRemainderVal
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) =
      EvmWord.val256 a0 a1 a2 a3 % EvmWord.val256 b0 b1 b2 b3 *
        2 ^ ((fullDivN1Shift b0).toNat % 64) := by
  let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let qVal := r3.1.toNat * (2^64)^3 + r2.1.toNat * (2^64)^2 +
    r1.1.toNat * (2^64) + r0.1.toNat
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hnormu := fullDivN1NormU_val256_eq_scaled_with_overflow
    a0 a1 a2 a3 b0 hshift_nz
  have hnormv := fullDivN1NormV_val256_eq_scaled b0 b1 b2 b3 hb3z hshift_nz
  have heq : EvmWord.val256 a0 a1 a2 a3 * 2 ^ ((fullDivN1Shift b0).toNat % 64) =
      qVal * (EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64)) +
        (n1StepRemainderVal r0 + n1StepsCarryVal r3 r2 r1 r0) := by
    delta fullDivN1StepsTelescoped n1StepsTelescoped at htel
    dsimp only at htel
    rw [← hnormu]
    rw [← hnormv]
    rw [hv3z]
    simp only [qVal, r0, r1, r2, r3]
    norm_num at htel ⊢
    omega
  exact n1StepsRemainderVal_eq_mod_mul_pow_of_normalized_euclidean r3 r2 r1 r0 heq hlt hbound

theorem fullDivN1QuotientVal_eq_div_of_telescoped
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (htel : fullDivN1StepsTelescoped bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
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
  let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let qVal := r3.1.toNat * (2^64)^3 + r2.1.toNat * (2^64)^2 +
    r1.1.toNat * (2^64) + r0.1.toNat
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hnormu := fullDivN1NormU_val256_eq_scaled_with_overflow
    a0 a1 a2 a3 b0 hshift_nz
  have hnormv := fullDivN1NormV_val256_eq_scaled b0 b1 b2 b3 hb3z hshift_nz
  have heq : EvmWord.val256 a0 a1 a2 a3 * 2 ^ ((fullDivN1Shift b0).toNat % 64) =
      qVal * (EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64)) +
        (n1StepRemainderVal r0 + n1StepsCarryVal r3 r2 r1 r0) := by
    delta fullDivN1StepsTelescoped n1StepsTelescoped at htel
    dsimp only at htel
    rw [← hnormu]
    rw [← hnormv]
    rw [hv3z]
    simp only [qVal, r0, r1, r2, r3]
    norm_num at htel ⊢
    omega
  have hq := EvmWord.div_quotient_of_normalized heq hlt
  rw [← hq]
  rw [← EvmWord.accumulated_eq_val256_n1]
  simp only [qVal, r0, r1, r2, r3]
  norm_num

theorem fullDivN1ExtendedRemainder_lt_of_telescoped_floor_le
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (htel : fullDivN1StepsTelescoped bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge : (EvmWord.val256 a0 a1 a2 a3 * 2 ^ ((fullDivN1Shift b0).toNat % 64)) /
        (EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64)) ≤
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
  let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let qVal := r3.1.toNat * (2^64)^3 + r2.1.toNat * (2^64)^2 +
    r1.1.toNat * (2^64) + r0.1.toNat
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hnormu := fullDivN1NormU_val256_eq_scaled_with_overflow
    a0 a1 a2 a3 b0 hshift_nz
  have hnormv := fullDivN1NormV_val256_eq_scaled b0 b1 b2 b3 hb3z hshift_nz
  have heq : EvmWord.val256 a0 a1 a2 a3 * 2 ^ ((fullDivN1Shift b0).toNat % 64) =
      qVal * (EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64)) +
        (n1StepRemainderVal r0 + n1StepsCarryVal r3 r2 r1 r0) := by
    delta fullDivN1StepsTelescoped n1StepsTelescoped at htel
    dsimp only at htel
    rw [← hnormu]
    rw [← hnormv]
    rw [hv3z]
    simp only [qVal, r0, r1, r2, r3]
    norm_num at htel ⊢
    omega
  have hb_pos : 0 < EvmWord.val256 b0 b1 b2 b3 *
      2 ^ ((fullDivN1Shift b0).toNat % 64) := by
    have hb : 0 < EvmWord.val256 b0 b1 b2 b3 := EvmWord.val256_pos_of_or_ne_zero hbnz
    positivity
  have hge' : (EvmWord.val256 a0 a1 a2 a3 * 2 ^ ((fullDivN1Shift b0).toNat % 64)) /
        (EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64)) ≤
      qVal := by
    simpa [qVal, r0, r1, r2, r3] using hge
  have ⟨_, hr_lt⟩ := EvmWord.remainder_lt_of_ge_floor hb_pos heq hge'
  exact hr_lt

theorem div_mul_pow_mul_pow_eq_div (a b s : Nat) :
    (a * 2^s) / (b * 2^s) = a / b :=
  Nat.mul_div_mul_right a b (by positivity : 0 < 2^s)

theorem fullDivN1QuotientVal_le_div_of_telescoped
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (htel : fullDivN1StepsTelescoped bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN1QuotientVal bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 ≤
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 := by
  let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let qVal := r3.1.toNat * (2^64)^3 + r2.1.toNat * (2^64)^2 +
    r1.1.toNat * (2^64) + r0.1.toNat
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hnormu := fullDivN1NormU_val256_eq_scaled_with_overflow
    a0 a1 a2 a3 b0 hshift_nz
  have hnormv := fullDivN1NormV_val256_eq_scaled b0 b1 b2 b3 hb3z hshift_nz
  have heq : EvmWord.val256 a0 a1 a2 a3 * 2 ^ ((fullDivN1Shift b0).toNat % 64) =
      qVal * (EvmWord.val256 b0 b1 b2 b3 * 2 ^ ((fullDivN1Shift b0).toNat % 64)) +
        (n1StepRemainderVal r0 + n1StepsCarryVal r3 r2 r1 r0) := by
    delta fullDivN1StepsTelescoped n1StepsTelescoped at htel
    dsimp only at htel
    rw [← hnormu]
    rw [← hnormv]
    rw [hv3z]
    simp only [qVal, r0, r1, r2, r3]
    norm_num at htel ⊢
    omega
  have hb_pos : 0 < EvmWord.val256 b0 b1 b2 b3 *
      2 ^ ((fullDivN1Shift b0).toNat % 64) := by
    have hb : 0 < EvmWord.val256 b0 b1 b2 b3 := EvmWord.val256_pos_of_or_ne_zero hbnz
    positivity
  have hq_le := EvmWord.quotient_le_of_euclidean hb_pos heq
  rw [div_mul_pow_mul_pow_eq_div] at hq_le
  delta fullDivN1QuotientVal
  simp only [qVal, r0, r1, r2, r3] at hq_le ⊢
  exact hq_le

theorem fullDivN1ExtendedRemainder_lt_of_telescoped_quotient_le
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (htel : fullDivN1StepsTelescoped bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
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
  exact fullDivN1ExtendedRemainder_lt_of_telescoped_floor_le
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hb2z hb3z hbnz hshift_nz htel (by
      rw [div_mul_pow_mul_pow_eq_div]
      exact hge)

end EvmAsm.Evm64
