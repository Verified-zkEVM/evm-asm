/-
  EvmAsm.Evm64.MulMod.ReduceOuterHorner

  Value-level (Horner) correctness of the full carry-aware outer fold.

  `mulModReduceOuterFoldCarry` folds the 64-bit per-limb step across the
  product limbs, `limb 0` most significant. This file proves it computes the
  base-`2^64` Horner accumulation modulo `n`:

      (mulModReduceOuterFoldCarry n limb r m).toNat
        = (r.toNat * 2^(64*m) + mulModLimbsValue limb m) % n.toNat

  for every limb count `m` and remainder `r < n` (positive `n`), where
  `mulModLimbsValue limb m` is the base-`2^64` integer with digits
  `limb 0 .. limb (m-1)`. Starting from `r = 0` (the reducer's initial state)
  this is `mulModLimbsValue limb m % n.toNat`.

  The proof is an `m`-induction over the per-limb law
  `mulModReduceStepNCarry_toNat_full` and the `< n` invariant
  `mulModReduceOuterFoldCarry`/`mulModReduceStepNCarry_lt`, with the
  cross-limb carry handled — as in `ReducePerLimb` — by the core
  `Nat.add_mod`/`Nat.mod_mul_mod` modular laws rather than `omega`.
-/

import EvmAsm.Evm64.MulMod.ReducePerLimb

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The base-`2^64` value of product limbs `limb 0 .. limb (m-1)`, with
    `limb 0` the most significant digit (the order the reducer consumes them). -/
def mulModLimbsValue (limb : Nat → Word) : Nat → Nat
  | 0 => 0
  | m + 1 => (limb 0).toNat * 2 ^ (64 * m) + mulModLimbsValue (fun i => limb (i + 1)) m

@[simp] theorem mulModLimbsValue_zero (limb : Nat → Word) :
    mulModLimbsValue limb 0 = 0 := rfl

theorem mulModLimbsValue_succ (limb : Nat → Word) (m : Nat) :
    mulModLimbsValue limb (m + 1)
      = (limb 0).toNat * 2 ^ (64 * m) + mulModLimbsValue (fun i => limb (i + 1)) m := rfl

/-- Horner correctness of the carry-aware outer fold. -/
theorem mulModReduceOuterFoldCarry_toNat (n : EvmWord) (hn : 0 < n.toNat) :
    ∀ (m : Nat) (limb : Nat → Word) (r : EvmWord), r.toNat < n.toNat →
      (mulModReduceOuterFoldCarry n limb r m).toNat
        = (r.toNat * 2 ^ (64 * m) + mulModLimbsValue limb m) % n.toNat := by
  intro m
  induction m with
  | zero =>
    intro limb r hr
    rw [mulModReduceOuterFoldCarry_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one,
      mulModLimbsValue_zero, Nat.add_zero, Nat.mod_eq_of_lt hr]
  | succ m ih =>
    intro limb r hr
    rw [mulModReduceOuterFoldCarry_succ,
      ih (fun i => limb (i + 1)) (mulModReduceStepNCarry r n (limb 0) 64)
        (mulModReduceStepNCarry_lt n hn 64 (limb 0) r hr),
      mulModReduceStepNCarry_toNat_full n (limb 0) r hn hr,
      mulModLimbsValue_succ,
      Nat.add_mod ((r.toNat * 2 ^ 64 + (limb 0).toNat) % n.toNat * 2 ^ (64 * m))
        (mulModLimbsValue (fun i => limb (i + 1)) m) n.toNat,
      Nat.mod_mul_mod, ← Nat.add_mod]
    have hpow : (2 : Nat) ^ 64 * 2 ^ (64 * m) = 2 ^ (64 * (m + 1)) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hr2 : r.toNat * 2 ^ 64 * 2 ^ (64 * m) = r.toNat * 2 ^ (64 * (m + 1)) := by
      rw [Nat.mul_assoc, hpow]
    rw [Nat.add_mul, hr2, Nat.add_assoc]

/-- From the reducer's initial state `r = 0`, the carry-aware outer fold of the
    product limbs is exactly the base-`2^64` integer reduced modulo `n`. -/
theorem mulModReduceOuterFoldCarry_toNat_zero_start (n : EvmWord) (limb : Nat → Word) (m : Nat)
    (hn : 0 < n.toNat) :
    (mulModReduceOuterFoldCarry n limb 0 m).toNat = mulModLimbsValue limb m % n.toNat := by
  have h0 : (0 : EvmWord).toNat < n.toNat := by simpa using hn
  have h := mulModReduceOuterFoldCarry_toNat n hn m limb 0 h0
  rw [show (0 : EvmWord).toNat = 0 from by simp, Nat.zero_mul, Nat.zero_add] at h
  exact h

end EvmAsm.Evm64
