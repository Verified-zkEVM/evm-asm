/-
  EvmAsm.Evm64.MulMod.ReduceFoldInvariant

  Carry-aware analogues of the bit-serial reducer folds, together with the
  `r < n` invariant that every accumulator value satisfies.

  `ReduceSemantics` defines the folds (`mulModReduceStepN`,
  `mulModReduceOuterFold`) over the *non* carry-aware step `mulModReduceStep`,
  matching the currently-assembled inner step — which is only sound for
  `n ≤ 2^255`. Here we mirror those folds over the carry-aware step
  `mulModReduceStepCarry` (see `ReduceCorrect`), which is exact for *every*
  modulus. The non-carry definitions are left untouched so the existing RV64
  specs still apply; once the inner step captures the carry-out the assembly
  specs re-target these folds.

  The key reusable fact proved here is the loop invariant: starting from a
  remainder below `n`, every carry-aware step / bit-loop / outer-loop keeps the
  remainder below `n`. This is the side condition the eventual value-level
  (Horner) correctness proof needs at each induction step.
-/

import EvmAsm.Evm64.MulMod.ReduceCorrect

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The carry-aware step preserves the remainder invariant `r < n`: its value
    is `(2r + bit) % n`, which is always below a positive modulus. -/
theorem mulModReduceStepCarry_lt (r n : EvmWord) (bit : Bool)
    (hn : 0 < n.toNat) (hr : r.toNat < n.toNat) :
    (mulModReduceStepCarry r n bit).toNat < n.toNat := by
  rw [mulModReduceStepCarry_toNat r n bit hn hr]
  exact Nat.mod_lt _ hn

/-- Carry-aware analogue of `mulModReduceStepN`: iterate the carry-aware step
    over the top `k` bits of the product limb `w`, MSB first. -/
def mulModReduceStepNCarry (r n : EvmWord) (w : Word) : Nat → EvmWord
  | 0 => r
  | k + 1 =>
    mulModReduceStepNCarry (mulModReduceStepCarry r n (mulModReduceInputBit w)) n (w <<< 1) k

@[simp] theorem mulModReduceStepNCarry_zero (r n : EvmWord) (w : Word) :
    mulModReduceStepNCarry r n w 0 = r := rfl

theorem mulModReduceStepNCarry_succ (r n : EvmWord) (w : Word) (k : Nat) :
    mulModReduceStepNCarry r n w (k + 1) =
      mulModReduceStepNCarry (mulModReduceStepCarry r n (mulModReduceInputBit w)) n (w <<< 1) k :=
  rfl

/-- The `k`-bit carry-aware bit loop preserves the remainder invariant. -/
theorem mulModReduceStepNCarry_lt (n : EvmWord) (hn : 0 < n.toNat) :
    ∀ (k : Nat) (w : Word) (r : EvmWord), r.toNat < n.toNat →
      (mulModReduceStepNCarry r n w k).toNat < n.toNat := by
  intro k
  induction k with
  | zero => intro w r hr; exact hr
  | succ k ih =>
    intro w r hr
    rw [mulModReduceStepNCarry_succ]
    exact ih (w <<< 1) _ (mulModReduceStepCarry_lt r n _ hn hr)

/-- Carry-aware analogue of `mulModReduceOuterFold`: fold the carry-aware
    64-bit bit loop over `m` product limbs, highest limb first. -/
def mulModReduceOuterFoldCarry (n : EvmWord) (limb : Nat → Word) (r : EvmWord) : Nat → EvmWord
  | 0 => r
  | m + 1 =>
    mulModReduceOuterFoldCarry n (fun i => limb (i + 1))
      (mulModReduceStepNCarry r n (limb 0) 64) m

@[simp] theorem mulModReduceOuterFoldCarry_zero (n : EvmWord) (limb : Nat → Word) (r : EvmWord) :
    mulModReduceOuterFoldCarry n limb r 0 = r := rfl

theorem mulModReduceOuterFoldCarry_succ (n : EvmWord) (limb : Nat → Word) (r : EvmWord) (m : Nat) :
    mulModReduceOuterFoldCarry n limb r (m + 1) =
      mulModReduceOuterFoldCarry n (fun i => limb (i + 1))
        (mulModReduceStepNCarry r n (limb 0) 64) m :=
  rfl

/-- The carry-aware outer fold over any number of product limbs preserves the
    remainder invariant `r < n`. -/
theorem mulModReduceOuterFoldCarry_lt (n : EvmWord) (hn : 0 < n.toNat) :
    ∀ (m : Nat) (limb : Nat → Word) (r : EvmWord), r.toNat < n.toNat →
      (mulModReduceOuterFoldCarry n limb r m).toNat < n.toNat := by
  intro m
  induction m with
  | zero => intro limb r hr; exact hr
  | succ m ih =>
    intro limb r hr
    rw [mulModReduceOuterFoldCarry_succ]
    exact ih _ _ (mulModReduceStepNCarry_lt n hn 64 (limb 0) r hr)

end EvmAsm.Evm64
