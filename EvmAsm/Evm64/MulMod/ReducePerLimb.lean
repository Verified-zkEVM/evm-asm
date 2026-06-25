/-
  EvmAsm.Evm64.MulMod.ReducePerLimb

  Value-level (Horner) correctness of one 64-bit carry-aware bit loop.

  `mulModReduceStepNCarry r n w 64` folds all 64 bits of the product limb `w`
  into the remainder, MSB first. This file proves it computes exactly the
  base-`2^64` Horner step modulo `n`:

      (mulModReduceStepNCarry r n w k).toNat = (r.toNat * 2^k + w.toNat / 2^(64-k)) % n.toNat

  for every `k ≤ 64` and remainder `r < n` (positive `n`). At `k = 64` this is
  `(r.toNat * 2^64 + w.toNat) % n.toNat`, the per-limb step the outer fold
  chains into `product % n`.

  The proof is a `k`-induction over `mulModReduceStepCarry_toNat` (the exact
  single-step modular law), the `< n` invariant (`mulModReduceStepCarry_lt`),
  and a bit-extraction identity reduced to the general `Nat` fact
  `W/(a*b)*b + W%(a*b)/a = W/a`.
-/

import EvmAsm.Evm64.MulMod.ReduceFoldInvariant

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- General base-splitting identity: the high digit times the base plus the
    low part's high bits reconstructs `W`'s high bits. -/
private theorem div_mul_add_mod_div (W a b : Nat) :
    W / (a * b) * b + W % (a * b) / a = W / a := by
  rw [Nat.mod_mul_right_div_self, ← Nat.div_div_eq_div_mul, Nat.div_add_mod']

/-- The bit-extraction identity driving the induction step: inserting the
    top bit `W / 2^63` (scaled by `2^k`) on top of the shifted limb's high
    bits yields `W`'s top `k+1` bits. -/
private theorem reduce_bit_identity (W k : Nat) (hk : k ≤ 63) :
    W / 2 ^ 63 * 2 ^ k + 2 * W % 2 ^ 64 / 2 ^ (64 - k) = W / 2 ^ (63 - k) := by
  have e2 : (2 : Nat) ^ (64 - k) = 2 * 2 ^ (63 - k) := by
    rw [show 64 - k = (63 - k) + 1 from by omega, Nat.pow_succ, Nat.mul_comm]
  have e64 : (2 : Nat) ^ 64 = 2 * 2 ^ 63 := by decide
  have e3 : (2 : Nat) ^ (63 - k) * 2 ^ k = 2 ^ 63 := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [e64, Nat.mul_mod_mul_left, e2,
    Nat.mul_div_mul_left _ _ (by decide : (0 : Nat) < 2), ← e3, div_mul_add_mod_div]

/-- `(w <<< 1).toNat` as a `Nat`: double modulo `2^64`. -/
private theorem shiftLeft_one_toNat (w : Word) :
    (w <<< 1).toNat = 2 * w.toNat % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm]

/-- The consumed input bit as a `Nat`: the top bit `w.toNat / 2^63`. -/
private theorem inputBit_eq_div (w : Word) :
    (if mulModReduceInputBit w then (1 : Nat) else 0) = w.toNat / 2 ^ 63 := by
  have hlt : w.toNat < 2 ^ 64 := w.isLt
  have e64 : (2 : Nat) ^ 64 = 2 * 2 ^ 63 := by decide
  unfold mulModReduceInputBit
  rw [show w.getLsbD 63 = decide (2 ^ 63 ≤ w.toNat) from BitVec.getLsbD_succ_last w]
  by_cases h : 2 ^ 63 ≤ w.toNat
  · have hd : w.toNat / 2 ^ 63 = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [h, hd]
  · have hd : w.toNat / 2 ^ 63 = 0 := Nat.div_eq_of_lt (by omega)
    simp [h, hd]

/-- Per-limb Horner correctness of the carry-aware 64-bit bit loop. -/
theorem mulModReduceStepNCarry_toNat (n : EvmWord) (hn : 0 < n.toNat) :
    ∀ (k : Nat), k ≤ 64 → ∀ (w : Word) (r : EvmWord), r.toNat < n.toNat →
      (mulModReduceStepNCarry r n w k).toNat
        = (r.toNat * 2 ^ k + w.toNat / 2 ^ (64 - k)) % n.toNat := by
  intro k
  induction k with
  | zero =>
    intro _ w r hr
    rw [mulModReduceStepNCarry_zero, Nat.pow_zero, Nat.mul_one, Nat.sub_zero,
      Nat.div_eq_of_lt w.isLt, Nat.add_zero, Nat.mod_eq_of_lt hr]
  | succ k ih =>
    intro hk w r hr
    rw [mulModReduceStepNCarry_succ,
      ih (by omega) (w <<< 1) (mulModReduceStepCarry r n (mulModReduceInputBit w))
        (mulModReduceStepCarry_lt r n (mulModReduceInputBit w) hn hr),
      mulModReduceStepCarry_toNat r n (mulModReduceInputBit w) hn hr,
      shiftLeft_one_toNat, inputBit_eq_div, show 64 - (k + 1) = 63 - k from by omega,
      Nat.add_mod ((2 * r.toNat + w.toNat / 2 ^ 63) % n.toNat * 2 ^ k)
        (2 * w.toNat % 2 ^ 64 / 2 ^ (64 - k)) n.toNat,
      Nat.mod_mul_mod, ← Nat.add_mod]
    have hbi := reduce_bit_identity w.toNat k (by omega)
    have hpk : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have h2r : 2 * r.toNat * 2 ^ k = r.toNat * 2 ^ (k + 1) := by
      rw [hpk, ← Nat.mul_assoc, Nat.mul_comm r.toNat 2]
    rw [Nat.add_mul, h2r, Nat.add_assoc, hbi]

/-- The full 64-bit limb step folds all of `w` into the remainder: a single
    base-`2^64` Horner step `(r * 2^64 + w) % n`. This is the per-limb law the
    outer fold chains across the eight product limbs. -/
theorem mulModReduceStepNCarry_toNat_full (n : EvmWord) (w : Word) (r : EvmWord)
    (hn : 0 < n.toNat) (hr : r.toNat < n.toNat) :
    (mulModReduceStepNCarry r n w 64).toNat = (r.toNat * 2 ^ 64 + w.toNat) % n.toNat := by
  have h := mulModReduceStepNCarry_toNat n hn 64 (Nat.le_refl 64) w r hr
  rw [show (64 : Nat) - 64 = 0 from rfl, Nat.pow_zero, Nat.div_one] at h
  exact h

end EvmAsm.Evm64
