/-
  EvmAsm.Evm64.EvmWordArith.MaxTrialVacuity

  Toward `isMaxTrialN4_false_of_shift_nz` (Option A of the
  max-trial vacuity discovery — see
  `memory/project_max_trial_vacuous_discovery.md`).

  The main claim (to be proven via 3 sublemmas):
  `isMaxTrialN4 a3 b2 b3 ∧ (clzResult b3).1 ≠ 0 → False`.

  This file hosts the sublemma pieces. Currently contains:
  - `u_top_lt_pow63_of_shift_nz` (Step 3 of the plan).
-/

import EvmAsm.Evm64.EvmWordArith.CLZLemmas

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- For `shift.toNat ∈ [1, 63]`, the value `a3 >>> (64 - shift)` is bounded above
    by `2^63`. Concretely, the max-trial algorithm's `u_top` lies in `[0, 2^63)`
    under a non-zero shift.

    Proof chain: `signExtend12 0 - shift = 2^64 - shift.toNat` (Word), its `%64 =
    64 - shift.toNat`, then `BitVec.toNat_ushiftRight` + power split. -/
theorem u_top_lt_pow63_of_shift_nz (a3 shift : Word)
    (h1 : 1 ≤ shift.toNat) (h63 : shift.toNat ≤ 63) :
    (a3 >>> ((signExtend12 (0 : BitVec 12) - shift).toNat % 64)).toNat < 2^63 := by
  have h0 : (signExtend12 (0 : BitVec 12) : Word) = 0 := by decide
  rw [h0]
  have hshift_toNat : ((0 : Word) - shift).toNat = 2^64 - shift.toNat := by
    rw [BitVec.toNat_sub]
    simp
    omega
  rw [hshift_toNat]
  have hmod : (2^64 - shift.toNat) % 64 = 64 - shift.toNat := by
    have : 2^64 - shift.toNat = (2^64 - 64) + (64 - shift.toNat) := by omega
    rw [this, Nat.add_mod]
    have : (2^64 - 64) % 64 = 0 := by decide
    rw [this]
    simp
    omega
  rw [hmod]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have ha3 : a3.toNat < 2^64 := a3.isLt
  have hsplit : (2 : Nat)^64 = 2^shift.toNat * 2^(64 - shift.toNat) := by
    rw [← pow_add, show shift.toNat + (64 - shift.toNat) = 64 from by omega]
  have hlt_pow_shift : a3.toNat / 2^(64 - shift.toNat) < 2^shift.toNat := by
    rw [hsplit, Nat.mul_comm] at ha3
    exact Nat.div_lt_of_lt_mul ha3
  exact lt_of_lt_of_le hlt_pow_shift (Nat.pow_le_pow_right (by norm_num) h63)

end EvmAsm.Evm64
