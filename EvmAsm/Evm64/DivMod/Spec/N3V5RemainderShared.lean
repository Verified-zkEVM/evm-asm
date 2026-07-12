/- Shared declaration home for the n=3 V5 MOD remainder arithmetic. -/

import EvmAsm.Evm64.DivMod.Spec.N3RemainderWordV4
import EvmAsm.Evm64.DivMod.Spec.N2V5FamiliesShapeShared
import EvmAsm.Evm64.DivMod.Spec.N3V5DigitStepIter
import EvmAsm.Evm64.EvmWordArith.DivN3NormVStructure
import EvmAsm.Evm64.EvmWordArith.DivLimbBridge
import EvmAsm.Evm64.EvmWordArith.DenormLemmas

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- **Top-4-limb first-window core (n=3).**  Generic Nat lemma: if the 5 limbs of
    the normalized dividend sum (with weights) to `A·S` (`A < 2^256`, `S > 0`) and
    the divisor value `B ≥ 2^128`, then the top-4-limb window is `< 2^64·(B·S)`.
    The n=3 analog of `first_window_core` (which extracts the top 3 limbs). -/
theorem first_window_core_n3 (n0 n1 n2 n3 n4 A B S : Nat)
    (hU : n0 + 2 ^ 64 * n1 + 2 ^ 128 * n2 + 2 ^ 192 * n3 + 2 ^ 256 * n4 = A * S)
    (hA : A < 2 ^ 256) (hB : 2 ^ 128 ≤ B) (hSpos : 0 < S) :
    n1 + 2 ^ 64 * n2 + 2 ^ 128 * n3 + 2 ^ 192 * n4 < 2 ^ 64 * (B * S) := by
  have hW1le : 2 ^ 64 * (n1 + 2 ^ 64 * n2 + 2 ^ 128 * n3 + 2 ^ 192 * n4) ≤ A * S := by
    nlinarith [hU]
  have hAB : A * S < 2 ^ 128 * (B * S) := by nlinarith [hA, hB, hSpos]
  have hchain : 2 ^ 64 * (n1 + 2 ^ 64 * n2 + 2 ^ 128 * n3 + 2 ^ 192 * n4)
      < 2 ^ 64 * (2 ^ 64 * (B * S)) := by nlinarith [hW1le, hAB]
  exact Nat.lt_of_mul_lt_mul_left hchain

/-- **v5 n=3 first-window validity (digit r1).**  The top-4-limb normalized
    window `(u₁,u₂,u₃,u₄)` is `< 2^64 · val256 normV`, the `hvalid` hypothesis of
    the digit-1 per-digit step.  Follows from the normalization scaling bridge
    (`val256 normU + nu₄·2^256 = val256 a·2^s`), the dividend bound
    `val256 a < 2^256`, and the divisor bound `val256 b ≥ 2^128` (3-limb, `b₂≠0`). -/
theorem fullDivN3_first_window_valid (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3z : b3 = 0) (hshift_nz : (clzResult b2).1 ≠ 0) (hb2nz : b2 ≠ 0) :
    val256 (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
      < 2 ^ 64 * val256 (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1 (fullDivN3NormV b0 b1 b2 b3).2.2.1 0 := by
  have hsnz : fullDivN3Shift b2 ≠ 0 := by unfold fullDivN3Shift; exact hshift_nz
  have hscaleU := fullDivN3NormU_val256_eq_scaled_with_overflow a0 a1 a2 a3 b2 hsnz
  have hscaleV := fullDivN3NormV_val256_eq_scaled_of_b3_zero b0 b1 b2 b3 hsnz hb3z
  have hvtop := fullDivN3NormV_top_zero_of_shape_shift_nz b0 b1 b2 b3 hb3z hshift_nz
  rw [hvtop] at hscaleV
  have hA := val256_bound a0 a1 a2 a3
  have hB : 2 ^ 128 ≤ val256 b0 b1 b2 b3 := val256_ge_pow128_of_limb2 b0 b1 b2 b3 hb2nz
  have hSpos : 0 < 2 ^ (fullDivN3Shift b2).toNat := by positivity
  have hU : (fullDivN3NormU a0 a1 a2 a3 b2).1.toNat
      + 2 ^ 64 * (fullDivN3NormU a0 a1 a2 a3 b2).2.1.toNat
      + 2 ^ 128 * (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1.toNat
      + 2 ^ 192 * (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1.toNat
      + 2 ^ 256 * (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2.toNat
      = val256 a0 a1 a2 a3 * 2 ^ (fullDivN3Shift b2).toNat := by
    rw [← hscaleU]; simp only [EvmWord.val256]; ring
  have hWexp : val256 (fullDivN3NormU a0 a1 a2 a3 b2).2.1
      (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
      (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
      (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
      = (fullDivN3NormU a0 a1 a2 a3 b2).2.1.toNat
        + 2 ^ 64 * (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1.toNat
        + 2 ^ 128 * (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1.toNat
        + 2 ^ 192 * (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2.toNat := by
    simp only [EvmWord.val256]; ring
  rw [hWexp, hscaleV]
  exact first_window_core_n3 _ _ _ _ _ _ _ _ hU hA hB hSpos

/-- **v5 n=3 unified per-digit step** (dispatch on the runtime flag `bltu`).
    Combines the call/max per-digit steps (`N3V5DigitStepIter`) into the single
    `bltu`-parameterized form consumed by the `_step_of_shape` telescope lemmas,
    mirroring n2's `iterN2V5_step`.  `hcall`/`hmax` are the dispatched `u₃ < v₂`
    comparisons. -/
theorem iterN3V5_step (bltu : Bool) (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63)
    (hvalid : val256 u0 u1 u2 u3 < 2 ^ 64 * val256 v0 v1 v2 0)
    (hcall : bltu = true → BitVec.ult u3 v2 = true)
    (hmax : bltu = false → ¬ BitVec.ult u3 v2) :
    val256 u0 u1 u2 u3 =
        (iterN3V5 bltu v0 v1 v2 0 u0 u1 u2 u3 0).1.toNat * val256 v0 v1 v2 0 +
        ((iterN3V5 bltu v0 v1 v2 0 u0 u1 u2 u3 0).2.1.toNat +
          2 ^ 64 * (iterN3V5 bltu v0 v1 v2 0 u0 u1 u2 u3 0).2.2.1.toNat +
          2 ^ 128 * (iterN3V5 bltu v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.1.toNat) ∧
      (iterN3V5 bltu v0 v1 v2 0 u0 u1 u2 u3 0).2.1.toNat +
          2 ^ 64 * (iterN3V5 bltu v0 v1 v2 0 u0 u1 u2 u3 0).2.2.1.toNat +
          2 ^ 128 * (iterN3V5 bltu v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.1.toNat <
        val256 v0 v1 v2 0 := by
  cases bltu with
  | true =>
    have hu : u3.toNat < v2.toNat := by
      have := hcall rfl; rw [BitVec.ult] at this; exact of_decide_eq_true this
    exact iterN3V5_call_step v0 v1 v2 u0 u1 u2 u3 hv2 hu
  | false =>
    exact iterN3V5_max_step v0 v1 v2 u0 u1 u2 u3 hv2 (hmax rfl) hvalid

/-- **v5 n=3 unified per-digit remainder collapse** (dispatch on `bltu`).  The
    3-limb-divisor remainder fits in three limbs: `rem₃` and the overflow carry
    are both zero.  Mirrors n2's `iterN2V5_collapse`. -/
theorem iterN3V5_collapse (bltu : Bool) (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63)
    (hvalid : val256 u0 u1 u2 u3 < 2 ^ 64 * val256 v0 v1 v2 0)
    (hcall : bltu = true → BitVec.ult u3 v2 = true)
    (hmax : bltu = false → ¬ BitVec.ult u3 v2) :
    (iterN3V5 bltu v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.1 = 0 ∧
    (iterN3V5 bltu v0 v1 v2 0 u0 u1 u2 u3 0).2.2.2.2.2 = 0 := by
  cases bltu with
  | true =>
    have hu : u3.toNat < v2.toNat := by
      have := hcall rfl; rw [BitVec.ult] at this; exact of_decide_eq_true this
    exact iterN3V5_call_collapse v0 v1 v2 u0 u1 u2 u3 hv2 hu
  | false =>
    exact iterN3V5_max_collapse v0 v1 v2 u0 u1 u2 u3 hv2 (hmax rfl) hvalid

/-- **Next-window validity (n=3).**  If the previous 3-limb remainder is `< V`,
    the next digit's 4-limb window `val256(nu, r₀, r₁, r₂)` is `< 2^64·V`.
    Propagates the window-validity invariant across the two n=3 digits.  The
    n=3 analog of `n2_next_window_lt` (one limb wider). -/
theorem n3_next_window_lt (nu r0 r1 r2 : Word) (V : Nat)
    (h : r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat < V) :
    val256 nu r0 r1 r2 < 2 ^ 64 * V := by
  have hnu := nu.isLt
  have hexp : val256 nu r0 r1 r2 =
      nu.toNat + 2 ^ 64 * (r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat) := by
    simp only [EvmWord.val256]; ring
  rw [hexp]
  calc nu.toNat + 2 ^ 64 * (r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat)
      < 2 ^ 64 + 2 ^ 64 * (r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat) := by omega
    _ = 2 ^ 64 * ((r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat) + 1) := by ring
    _ ≤ 2 ^ 64 * V := Nat.mul_le_mul_left _ h

/-- **fullDivN3R1V5 step over the normalized window** (digit 1, the first
    window).  `hvalid` is derived internally from `fullDivN3_first_window_valid`. -/
theorem fullDivN3R1V5_step_of_shape (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_1 : Bool)
    (hb3z : b3 = 0) (hshift_nz : (clzResult b2).1 ≠ 0) (hb2nz : b2 ≠ 0)
    (hcall : bltu_1 = true →
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hmax : bltu_1 = false →
      ¬ BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1) :
    val256 (fullDivN3NormU a0 a1 a2 a3 b2).2.1 (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1 (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 =
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat *
        val256 (fullDivN3NormV b0 b1 b2 b3).1 (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1 0 +
        ((fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat +
          2 ^ 64 * (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat +
          2 ^ 128 * (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat) ∧
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat +
          2 ^ 64 * (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat +
          2 ^ 128 * (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat <
        val256 (fullDivN3NormV b0 b1 b2 b3).1 (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1 0 := by
  have hvtop := fullDivN3NormV_top_zero_of_shape_shift_nz b0 b1 b2 b3 hb3z hshift_nz
  have hmsb := fullDivN3NormV_msb_of_b2_ne_zero b0 b1 b2 b3 hb2nz
  have hvalid := fullDivN3_first_window_valid a0 a1 a2 a3 b0 b1 b2 b3 hb3z hshift_nz hb2nz
  have hrw : fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 =
      iterN3V5 bltu_1 (fullDivN3NormV b0 b1 b2 b3).1 (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 0
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1 (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1 (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 0 := by
    unfold fullDivN3R1V5; dsimp only; rw [hvtop]
  rw [hrw]
  exact iterN3V5_step bltu_1 _ _ _ _ _ _ _ hmsb hvalid hcall hmax

/-- **fullDivN3R1V5 remainder collapse** (digit 1): `rem₃` and carry are zero. -/
theorem fullDivN3R1V5_collapse_of_shape (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_1 : Bool)
    (hb3z : b3 = 0) (hshift_nz : (clzResult b2).1 ≠ 0) (hb2nz : b2 ≠ 0)
    (hcall : bltu_1 = true →
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hmax : bltu_1 = false →
      ¬ BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1) :
    (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0 ∧
    (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2 = 0 := by
  have hvtop := fullDivN3NormV_top_zero_of_shape_shift_nz b0 b1 b2 b3 hb3z hshift_nz
  have hmsb := fullDivN3NormV_msb_of_b2_ne_zero b0 b1 b2 b3 hb2nz
  have hvalid := fullDivN3_first_window_valid a0 a1 a2 a3 b0 b1 b2 b3 hb3z hshift_nz hb2nz
  have hrw : fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 =
      iterN3V5 bltu_1 (fullDivN3NormV b0 b1 b2 b3).1 (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 0
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1 (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1 (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 0 := by
    unfold fullDivN3R1V5; dsimp only; rw [hvtop]
  rw [hrw]
  exact iterN3V5_collapse bltu_1 _ _ _ _ _ _ _ hmsb hvalid hcall hmax

/-- **fullDivN3R0V5 step over the normalized window** (digit 0, chained on the
    digit-1 remainder via `hpc : r₁.rem₃ = 0` and the propagated `hvalid`). -/
theorem fullDivN3R0V5_step_of_shape (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_1 bltu_0 : Bool)
    (hb3z : b3 = 0) (hshift_nz : (clzResult b2).1 ≠ 0) (hb2nz : b2 ≠ 0)
    (hpc : (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0)
    (hvalid : val256 (fullDivN3NormU a0 a1 a2 a3 b2).1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        < 2 ^ 64 * val256 (fullDivN3NormV b0 b1 b2 b3).1 (fullDivN3NormV b0 b1 b2 b3).2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1 0)
    (hcall : bltu_0 = true →
      BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hmax : bltu_0 = false →
      ¬ BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1) :
    val256 (fullDivN3NormU a0 a1 a2 a3 b2).1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 =
      (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat *
        val256 (fullDivN3NormV b0 b1 b2 b3).1 (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1 0 +
        ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat +
          2 ^ 64 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat +
          2 ^ 128 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat) ∧
      (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat +
          2 ^ 64 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat +
          2 ^ 128 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat <
        val256 (fullDivN3NormV b0 b1 b2 b3).1 (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1 0 := by
  have hvtop := fullDivN3NormV_top_zero_of_shape_shift_nz b0 b1 b2 b3 hb3z hshift_nz
  have hmsb := fullDivN3NormV_msb_of_b2_ne_zero b0 b1 b2 b3 hb2nz
  have hrw : fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
      iterN3V5 bltu_0 (fullDivN3NormV b0 b1 b2 b3).1 (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 0
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 0 := by
    unfold fullDivN3R0V5; dsimp only; rw [hvtop, hpc]
  rw [hrw]
  exact iterN3V5_step bltu_0 _ _ _ _ _ _ _ hmsb hvalid hcall hmax

/-- The v5 n=3 2-digit accumulation (pure `Nat`).  `W1` is the top 4-limb window
    value; `R1r` is the collapsed 3-limb intermediate remainder, `R0r` the final
    remainder.  The n=3 analog of `fullDivN2V5_three_step_nat`, one digit shorter
    (4-limb dividend / 3-limb divisor → 2 digits). -/
theorem fullDivN3V5_two_step_nat
    {a V q1 q0 nu0 W1 R1r R0r : Nat}
    (hfirst : a = nu0 + 2 ^ 64 * W1)
    (hstep1 : W1 = q1 * V + R1r)
    (hstep0 : nu0 + 2 ^ 64 * R1r = q0 * V + R0r) :
    a = (q1 * 2 ^ 64 + q0) * V + R0r := by
  subst hfirst hstep1
  nlinarith [hstep0]

/-- **v5 n=3 accumulated quotient correctness (shift≠0).**  The two v5 n=3
    quotient digits combine to exactly `val256 a / val256 b`.  Telescopes the two
    per-digit steps (R1/R0) — chained via the window-validity invariant and the
    digit-1 collapse — through `fullDivN3V5_two_step_nat` into the normalized
    Euclidean equation, then `div_quotient_of_normalized` recovers the quotient.
    The `bltu` arguments match the per-digit `u₃ < v₂` comparisons. -/
theorem fullDivN3_acc_quot_eq_div_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_1 bltu_0 : Bool)
    (hb3z : b3 = 0) (hshift_nz : (clzResult b2).1 ≠ 0) (hb2nz : b2 ≠ 0)
    (hc1 : bltu_1 = true →
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm1 : bltu_1 = false →
      ¬ BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hc0 : bltu_0 = true →
      BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1) :
    (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat * 2 ^ 64
        + (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat
      = val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 := by
  have hsnz : fullDivN3Shift b2 ≠ 0 := by unfold fullDivN3Shift; exact hshift_nz
  have hR1 := fullDivN3R1V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_1 hb3z hshift_nz hb2nz hc1 hm1
  have hR1c := fullDivN3R1V5_collapse_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_1 hb3z hshift_nz hb2nz hc1 hm1
  have hR0valid := n3_next_window_lt (fullDivN3NormU a0 a1 a2 a3 b2).1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 _ hR1.2
  have hR0 := fullDivN3R0V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_1 bltu_0
      hb3z hshift_nz hb2nz hR1c.1 hR0valid hc0 hm0
  have hscaleU := fullDivN3NormU_val256_eq_scaled_with_overflow a0 a1 a2 a3 b2 hsnz
  have hscaleV := fullDivN3NormV_val256_eq_scaled_of_b3_zero b0 b1 b2 b3 hsnz hb3z
  have hvtop := fullDivN3NormV_top_zero_of_shape_shift_nz b0 b1 b2 b3 hb3z hshift_nz
  rw [hvtop] at hscaleV
  have hfirst : val256 a0 a1 a2 a3 * 2 ^ (fullDivN3Shift b2).toNat =
      (fullDivN3NormU a0 a1 a2 a3 b2).1.toNat
        + 2 ^ 64 * val256 (fullDivN3NormU a0 a1 a2 a3 b2).2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 := by
    rw [← hscaleU]; simp only [EvmWord.val256]; ring
  have hw0 : val256 (fullDivN3NormU a0 a1 a2 a3 b2).1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      = (fullDivN3NormU a0 a1 a2 a3 b2).1.toNat
        + 2 ^ 64 * ((fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
          + 2 ^ 64 * (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat
          + 2 ^ 128 * (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat) := by
    simp only [EvmWord.val256]; ring
  rw [hw0] at hR0
  have htele := fullDivN3V5_two_step_nat hfirst hR1.1 hR0.1
  rw [hscaleV] at htele
  have hlt : (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
      + 2 ^ 64 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat
      + 2 ^ 128 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat
      < val256 b0 b1 b2 b3 * 2 ^ (fullDivN3Shift b2).toNat := by
    rw [← hscaleV]; exact hR0.2
  have hfin := div_quotient_of_normalized htele hlt
  linarith [hfin]


open EvmWord EvmAsm.Rv64

/-- **v5 n=3 normalized Euclidean equation from shape (shift≠0).**
    `val256 a · 2^s = Q · (val256 b · 2^s) + R_norm` (mulsub form) together with the
    remainder bound `R_norm < val256 b · 2^s`, where `Q = R1.1·2^64 + R0.1` and
    `R_norm` is the 3-limb normalized remainder.  Same telescope as
    `fullDivN3_acc_quot_eq_div_of_shape`, stopped before the quotient recovery.
    n=3 analog of `fullDivN2_normalized_euclidean_of_shape`. -/
theorem fullDivN3_normalized_euclidean_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_1 bltu_0 : Bool)
    (hb3z : b3 = 0) (hshift_nz : (clzResult b2).1 ≠ 0) (hb2nz : b2 ≠ 0)
    (hc1 : bltu_1 = true →
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm1 : bltu_1 = false →
      ¬ BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hc0 : bltu_0 = true →
      BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1) :
    (val256 a0 a1 a2 a3 * 2 ^ (fullDivN3Shift b2).toNat =
        ((fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat * 2 ^ 64
          + (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat)
          * (val256 b0 b1 b2 b3 * 2 ^ (fullDivN3Shift b2).toNat)
        + ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
          + 2 ^ 64 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat
          + 2 ^ 128 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat)) ∧
    ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
        + 2 ^ 64 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat
        + 2 ^ 128 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat
      < val256 b0 b1 b2 b3 * 2 ^ (fullDivN3Shift b2).toNat) := by
  have hsnz : fullDivN3Shift b2 ≠ 0 := by unfold fullDivN3Shift; exact hshift_nz
  have hR1 := fullDivN3R1V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_1 hb3z hshift_nz hb2nz hc1 hm1
  have hR1c := fullDivN3R1V5_collapse_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_1 hb3z hshift_nz hb2nz hc1 hm1
  have hR0valid := n3_next_window_lt (fullDivN3NormU a0 a1 a2 a3 b2).1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 _ hR1.2
  have hR0 := fullDivN3R0V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_1 bltu_0
      hb3z hshift_nz hb2nz hR1c.1 hR0valid hc0 hm0
  have hscaleU := fullDivN3NormU_val256_eq_scaled_with_overflow a0 a1 a2 a3 b2 hsnz
  have hscaleV := fullDivN3NormV_val256_eq_scaled_of_b3_zero b0 b1 b2 b3 hsnz hb3z
  have hvtop := fullDivN3NormV_top_zero_of_shape_shift_nz b0 b1 b2 b3 hb3z hshift_nz
  rw [hvtop] at hscaleV
  have hfirst : val256 a0 a1 a2 a3 * 2 ^ (fullDivN3Shift b2).toNat =
      (fullDivN3NormU a0 a1 a2 a3 b2).1.toNat
        + 2 ^ 64 * val256 (fullDivN3NormU a0 a1 a2 a3 b2).2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 := by
    rw [← hscaleU]; simp only [EvmWord.val256]; ring
  have hw0 : val256 (fullDivN3NormU a0 a1 a2 a3 b2).1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      = (fullDivN3NormU a0 a1 a2 a3 b2).1.toNat
        + 2 ^ 64 * ((fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
          + 2 ^ 64 * (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat
          + 2 ^ 128 * (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat) := by
    simp only [EvmWord.val256]; ring
  rw [hw0] at hR0
  have htele := fullDivN3V5_two_step_nat hfirst hR1.1 hR0.1
  rw [hscaleV] at htele
  have hlt : (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
      + 2 ^ 64 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat
      + 2 ^ 128 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat
      < val256 b0 b1 b2 b3 * 2 ^ (fullDivN3Shift b2).toNat := by
    rw [← hscaleV]; exact hR0.2
  exact ⟨htele, hlt⟩

/-- The n=3 remainder's top (4th) limb is zero — the 3-limb divisor gives a
    ≤3-limb remainder. -/
theorem fullDivN3R0V5_top_limb_zero_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_1 bltu_0 : Bool)
    (hb3z : b3 = 0) (hshift_nz : (clzResult b2).1 ≠ 0) (hb2nz : b2 ≠ 0)
    (hc1 : bltu_1 = true →
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm1 : bltu_1 = false →
      ¬ BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hc0 : bltu_0 = true →
      BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1) :
    (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0 := by
  have hvtop := fullDivN3NormV_top_zero_of_shape_shift_nz b0 b1 b2 b3 hb3z hshift_nz
  have hmsb := fullDivN3NormV_msb_of_b2_ne_zero b0 b1 b2 b3 hb2nz
  have hR1 := fullDivN3R1V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_1 hb3z hshift_nz hb2nz hc1 hm1
  have hR1c := fullDivN3R1V5_collapse_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_1 hb3z hshift_nz hb2nz hc1 hm1
  have hR0valid := n3_next_window_lt (fullDivN3NormU a0 a1 a2 a3 b2).1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 _ hR1.2
  have hrw : fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
      iterN3V5 bltu_0 (fullDivN3NormV b0 b1 b2 b3).1 (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 0
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 0 := by
    unfold fullDivN3R0V5; dsimp only; rw [hvtop, hR1c.1]
  rw [hrw]
  exact (iterN3V5_collapse bltu_0 _ _ _ _ _ _ _ hmsb hR0valid hc0 hm0).1

/-- Pack the four denormalized v5 n=3 MOD remainder limbs (funnel-shift-down of
    `fullDivN3R0V5`'s remainder by `fullDivN3Shift b2`) into a single `EvmWord`. -/
@[irreducible]
def fullModN3RemainderWordV5 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 =>
        ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))
    | 1 =>
        ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))
    | 2 =>
        ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))
    | 3 =>
        (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64))

/-- **v5 n=3 MOD remainder correctness (shift≠0), from shape + `bltu` matches.**
    `fullModN3RemainderWordV5 = EvmWord.mod a b`. -/
theorem fullModN3RemainderWordV5_eq_mod_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_1 bltu_0 : Bool)
    (hb3z : b3 = 0) (hshift_nz : (clzResult b2).1 ≠ 0) (hb2nz : b2 ≠ 0)
    (hc1 : bltu_1 = true →
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm1 : bltu_1 = false →
      ¬ BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hc0 : bltu_0 = true →
      BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1) :
    fullModN3RemainderWordV5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  have h0 : (0 : Word).toNat = 0 := rfl
  have hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    exact hb2nz (BitVec.or_eq_zero_iff.mp h2).2
  have heucl := fullDivN3_normalized_euclidean_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    bltu_1 bltu_0 hb3z hshift_nz hb2nz hc1 hm1 hc0 hm0
  have htop := fullDivN3R0V5_top_limb_zero_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    bltu_1 bltu_0 hb3z hshift_nz hb2nz hc1 hm1 hc0 hm0
  -- shift/antiShift normalizations
  have h_shift_pos : 1 ≤ (clzResult b2).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b2).1.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simp [h])) hshift_nz
    · exact h
  have hle63 := clzResult_fst_toNat_le b2
  have hsmod : (fullDivN3Shift b2).toNat % 64 = (fullDivN3Shift b2).toNat := by
    unfold fullDivN3Shift; exact Nat.mod_eq_of_lt (by omega)
  have hamod : (signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64
      = 64 - (fullDivN3Shift b2).toNat := by
    unfold fullDivN3Shift; exact antiShift_toNat_mod_eq h_shift_pos hle63
  have hslt : (fullDivN3Shift b2).toNat < 64 := by unfold fullDivN3Shift; omega
  have hspos : 0 < (fullDivN3Shift b2).toNat := by unfold fullDivN3Shift; omega
  have hr_denorm :
      val256
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<< ((signExtend12 (0:BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<< ((signExtend12 (0:BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<< ((signExtend12 (0:BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>> ((fullDivN3Shift b2).toNat % 64))
      = ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
          + 2 ^ 64 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat
          + 2 ^ 128 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat)
        / 2 ^ (fullDivN3Shift b2).toNat := by
    rw [hsmod, hamod, val256_denormalize hspos hslt, htop]
    simp only [EvmWord.val256, h0]; ring_nf
  have hmulsub : val256 a0 a1 a2 a3 * 2 ^ (fullDivN3Shift b2).toNat =
      val256 (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 0 0
        * (val256 b0 b1 b2 b3 * 2 ^ (fullDivN3Shift b2).toNat)
      + ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
        + 2 ^ 64 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat
        + 2 ^ 128 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat) := by
    rw [show val256 (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 0 0
        = (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat * 2 ^ 64
          + (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat
        from by simp only [EvmWord.val256, h0]; ring]
    exact heucl.1
  unfold fullModN3RemainderWordV5
  exact mod_correct_normalized hbnz (fullDivN3Shift b2).toNat hmulsub heucl.2 hr_denorm

/-- Per-limb projection of the n=3 MOD remainder word equality into the four
    `(EvmWord.mod a b).getLimbN` funnel-shift equalities. -/
theorem fullModN3V5_hmods_of_word_eq
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_1 bltu_0 : Bool)
    (hmod : fullModN3RemainderWordV5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b) :
    (EvmWord.mod a b).getLimbN 0 =
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 1 =
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 2 =
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 3 =
        ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hmod]; delta fullModN3RemainderWordV5; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hmod]; delta fullModN3RemainderWordV5; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hmod]; delta fullModN3RemainderWordV5; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hmod]; delta fullModN3RemainderWordV5; exact EvmWord.getLimbN_fromLimbs_3

end EvmAsm.Evm64
