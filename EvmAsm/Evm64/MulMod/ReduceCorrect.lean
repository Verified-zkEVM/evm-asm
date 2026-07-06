/-
  EvmAsm.Evm64.MulMod.ReduceCorrect

  Correctness of the bit-serial 512-by-256 MULMOD reducer's semantic step,
  carry-aware. The existing `mulModReduceStep` shifts the 256-bit remainder
  left by one in `EvmWord = BitVec 256`, which silently truncates the
  carry-out (bit 256 of `2r`). That is only sound when the modulus is at most
  `2^255` (so the remainder stays below `2^255` and `2r` never overflows). For
  the EVM MULMOD semantics — `(a*b) % n` for *every* nonzero `n < 2^256` — the
  carry-out must be folded into the "subtract `n`" decision.

  `mulModReduceStepCarry` is that carry-aware step, and
  `mulModReduceStepCarry_toNat` proves it computes the exact modular step
  `(2r + bit) % n` for any remainder `r < n` with `0 < n`. This is the
  semantic foundation for the total reducer-correctness theorem; the RV64
  inner step will be adjusted to match it.
-/

import EvmAsm.Evm64.MulMod.ReduceSemantics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Carry-aware bit-serial reducer step. Shift the remainder left by one and
    insert the consumed product bit; subtract the modulus `n` when the true
    `2r + bit` is at least `n` — which happens exactly when the 256-bit shift
    overflowed (the carry-out `r.getLsbD 255`) *or* the truncated value is
    already `≥ n`. The 256-bit subtraction `shifted - n` wraps to the correct
    `(2r + bit) - n` in the overflow case. -/
def mulModReduceStepCarry (r n : EvmWord) (bit : Bool) : EvmWord :=
  let shifted := mulModReduceShiftInBit r bit
  if r.getLsbD 255 = true ∨ ¬ (shifted.toNat < n.toNat) then shifted - n else shifted

/-- The shifted remainder's value: the OR with the inserted bit is an
    addition, because the left-shift clears bit 0. -/
theorem shiftInBit_toNat (r : EvmWord) (bit : Bool) :
    (mulModReduceShiftInBit r bit).toNat
      = 2 * r.toNat % 2 ^ 256 + (if bit then 1 else 0) := by
  unfold mulModReduceShiftInBit mulModReduceBitWord
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  cases bit
  · simp; omega
  · simp only [reduceIte]
    have e1 : r.toNat * 2 ^ 1 % 2 ^ 256 = 2 ^ 1 * (r.toNat % 2 ^ 255) := by omega
    rw [show ((1 : EvmWord).toNat) = 1 from by decide, e1,
      ← Nat.two_pow_add_eq_or_of_lt (show (1 : Nat) < 2 ^ 1 from by decide) (r.toNat % 2 ^ 255)]
    omega

/-- The carry-aware step computes the exact modular reduction step: for any
    remainder `r < n` with `0 < n`, it returns `(2 * r + bit) % n`. -/
theorem mulModReduceStepCarry_toNat (r n : EvmWord) (bit : Bool)
    (hn : 0 < n.toNat) (hr : r.toNat < n.toNat) :
    (mulModReduceStepCarry r n bit).toNat
      = (2 * r.toNat + (if bit then 1 else 0)) % n.toNat := by
  have hsh := shiftInBit_toNat r bit
  have hb : (if bit then (1 : Nat) else 0) ≤ 1 := by cases bit <;> decide
  have hgl : r.getLsbD 255 = decide (2 ^ 255 ≤ r.toNat) := BitVec.getLsbD_succ_last r
  -- The RHS modulus `n` is a variable, which `omega` cannot reason about
  -- (`n * q` is nonlinear). Resolve it to a branch-free subtraction first; the
  -- remaining `% 2 ^ 256` mods are by a constant and stay in `omega`'s reach.
  have hmod : (2 * r.toNat + (if bit then 1 else 0)) % n.toNat
      = if n.toNat ≤ 2 * r.toNat + (if bit then 1 else 0)
        then 2 * r.toNat + (if bit then 1 else 0) - n.toNat
        else 2 * r.toNat + (if bit then 1 else 0) := by
    by_cases hc : n.toNat ≤ 2 * r.toNat + (if bit then 1 else 0)
    · rw [if_pos hc, Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)]
    · rw [if_neg hc, Nat.mod_eq_of_lt (by omega)]
  rw [hmod]
  unfold mulModReduceStepCarry
  by_cases h : r.getLsbD 255 = true ∨ ¬ ((mulModReduceShiftInBit r bit).toNat < n.toNat)
  · rw [if_pos h]
    simp only [hgl, decide_eq_true_eq] at h
    rw [if_pos (show n.toNat ≤ 2 * r.toNat + (if bit then 1 else 0) by
      rcases h with h | h <;> omega)]
    bv_omega
  · rw [if_neg h]
    simp only [not_or, hgl, decide_eq_true_eq] at h
    rw [if_neg (show ¬ n.toNat ≤ 2 * r.toNat + (if bit then 1 else 0) by omega)]
    bv_omega

end EvmAsm.Evm64
