/-
  EvmAsm.Evm64.DivMod.Spec.N1V5LaneBltu

  The four per-digit `bltu = true` facts for the v5 n=1 lane, discharged from the
  divisor shape.  In the n=1 normalized call regime the running remainder stays
  `< v0` (the single-limb divisor), so every digit takes the call path.  These are
  exactly the `hbltu_3/2/1/0` hypotheses of `divK_loop_n1_call_unified_v5`
  (instantiated at the normalized inputs), reduced to the existing shape lemmas via
  the `bltu`-discharge primitive `n1v5_bltu_limb0_of_val256_lt`.  Bead
  `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N1V5DigitSteps

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- `bltu`-discharge primitive: a remainder whose `val256` is below the
    single-limb divisor `v0` has its low limb `< v0`, so `BitVec.ult limb0 v0`. -/
theorem n1v5_bltu_limb0_of_val256_lt {x0 x1 x2 x3 v0 : Word}
    (h : EvmWord.val256 x0 x1 x2 x3 < v0.toNat) : BitVec.ult x0 v0 := by
  obtain ⟨h1, h2, h3⟩ := val256_high_limbs_zero_of_lt_word x0 x1 x2 x3 v0 h
  rw [EvmWord.ult_iff]
  have hval : EvmWord.val256 x0 x1 x2 x3 = x0.toNat := by rw [h1, h2, h3]; simp [EvmWord.val256]
  omega

/-- n=1 lane, j=3 (top digit) `bltu`: `uHi < v0` for the normalized inputs. -/
theorem n1v5_lane_bltu_3_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    BitVec.ult (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (fullDivN1NormV b0 b1 b2 b3).1 :=
  EvmWord.ult_iff.mpr (fullDivN1NormU_top_lt_normV_limb0_of_shape_shift_nz
    a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)

/-- n=1 lane, j=2 `bltu`: the j=3 remainder's low limb `< v0`. -/
theorem n1v5_lane_bltu_2_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    BitVec.ult (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).1 :=
  n1v5_bltu_limb0_of_val256_lt
    (fullDivN1R3V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)

/-- n=1 lane, j=1 `bltu`: the j=2 remainder's low limb `< v0`. -/
theorem n1v5_lane_bltu_1_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    BitVec.ult (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).1 :=
  n1v5_bltu_limb0_of_val256_lt
    (fullDivN1R2V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)

/-- n=1 lane, j=0 `bltu`: the j=1 remainder's low limb `< v0`. -/
theorem n1v5_lane_bltu_0_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    BitVec.ult (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).1 :=
  n1v5_bltu_limb0_of_val256_lt
    (fullDivN1R1V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)

end EvmAsm.Evm64
