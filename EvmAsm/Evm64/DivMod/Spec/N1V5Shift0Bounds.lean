/-
  EvmAsm.Evm64.DivMod.Spec.N1V5Shift0Bounds

  Foundational bounds for the v5 n=1 **shift=0** lane.  When `(clzResult b0).1 = 0`
  the divisor `b0` already has its top bit set (`b0 ≥ 2^63`), so on the shift=0
  branch the loop runs on the copy-AU outputs `v = (b0, 0, 0, 0)`,
  `u = (a0, a1, a2, a3, 0)` with an already-normalized single-limb divisor.

  The generic per-digit invariant core (`iterN1V5_true_remainder_lt_of_v0_norm_call`)
  only needs `v0 ≥ 2^63` and `uTop < v0`; both hold trivially here (`v0 = b0`,
  `uTop = 0`).  This file provides the `b0 ≥ 2^63` fact, which is the shift=0
  counterpart of `fullDivN1NormV_limb0_ge_pow63_of_shape` (whose `b0 <<< shift`
  collapses to `b0` at shift=0).  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.MaxTrialVacuity

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- On the shift=0 branch (`(clzResult b0).1 = 0`) the divisor's top bit is set:
    `2^63 ≤ b0.toNat`.  Specializes `b3_shifted_ge_pow63` at the zero shift
    amount (`b0 <<< 0 = b0`). -/
theorem b0_ge_pow63_of_clz_zero (b0 : Word) (hb0nz : b0 ≠ 0)
    (hclz : (clzResult b0).1 = 0) :
    2 ^ 63 ≤ b0.toNat := by
  have h := b3_shifted_ge_pow63 hb0nz
  rw [hclz] at h
  simpa using h

/-- Corollary: any single-limb top window `0 < b0` on the shift=0 branch, i.e.
    `BitVec.ult 0 b0` (the trivial `uTop = 0 < v0 = b0` bound feeding the
    first-digit `bltu`). -/
theorem zero_ult_b0_of_clz_zero (b0 : Word) (hb0nz : b0 ≠ 0)
    (hclz : (clzResult b0).1 = 0) :
    BitVec.ult (0 : Word) b0 := by
  have h := b0_ge_pow63_of_clz_zero b0 hb0nz hclz
  have hz : (0 : Word).toNat = 0 := by decide
  rw [EvmWord.ult_iff, hz]
  omega

end EvmAsm.Evm64
