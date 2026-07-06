/-
  EvmAsm.Evm64.MulMod.ReduceCarryAgree

  The currently-assembled (non carry-aware) reducer is correct for every
  modulus `n ≤ 2^255`.

  The shipped inner step computes `mulModReduceStep`, which truncates the
  shift's carry-out. That truncation only ever loses information once a
  remainder reaches `2^255`; while the modulus satisfies `n ≤ 2^255` the
  invariant `r < n ≤ 2^255` keeps every remainder below `2^255`, so the
  non-carry step coincides bit-for-bit with the carry-aware
  `mulModReduceStepCarry`. Lifting that agreement through the 64-bit bit loop
  and the outer limb fold, and composing with the carry-aware Horner result
  (`ReduceOuterHorner`) and the product-limbs bridge (`ProductLimbsValue`),
  shows the non-carry fold of the product limbs equals `(a·b) % n` whenever
  `0 < n ≤ 2^255`.

  This is partial total-MULMOD correctness for the existing program — no
  opcode change. Full correctness for `n > 2^255` needs the carry-capturing
  inner step.
-/

import EvmAsm.Evm64.MulMod.ProductLimbsValue

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.MulMod.ProductAlgebra

/-- Below `2^255` the shift never overflows, so the shipped non-carry step
    agrees with the carry-aware step. -/
theorem mulModReduceStep_eq_carry_of_lt (r n : EvmWord) (bit : Bool)
    (hr : r.toNat < 2 ^ 255) :
    mulModReduceStep r n bit = mulModReduceStepCarry r n bit := by
  have hgl : r.getLsbD 255 = false := by
    rw [show r.getLsbD 255 = decide (2 ^ 255 ≤ r.toNat) from BitVec.getLsbD_succ_last r]
    simp only [decide_eq_false_iff_not]; omega
  unfold mulModReduceStep mulModReduceStepCarry
  simp only [hgl, Bool.false_eq_true, false_or]
  by_cases h : (mulModReduceShiftInBit r bit).toNat < n.toNat
  · simp only [h, if_true, not_true, if_false]
  · simp only [h, if_false, not_false_eq_true, if_true]

/-- The 64-bit bit loop agrees with its carry-aware version while the modulus
    stays at most `2^255`. -/
theorem mulModReduceStepN_eq_carry (n : EvmWord) (hn : n.toNat ≤ 2 ^ 255) :
    ∀ (k : Nat) (w : Word) (r : EvmWord), r.toNat < n.toNat →
      mulModReduceStepN r n w k = mulModReduceStepNCarry r n w k := by
  intro k
  induction k with
  | zero => intro w r _; rfl
  | succ k ih =>
    intro w r hr
    rw [mulModReduceStepN_succ, mulModReduceStepNCarry_succ,
      mulModReduceStep_eq_carry_of_lt r n (mulModReduceInputBit w) (by omega)]
    exact ih (w <<< 1) _ (mulModReduceStepCarry_lt r n (mulModReduceInputBit w) (by omega) hr)

/-- The outer limb fold agrees with its carry-aware version while the modulus
    stays at most `2^255`. -/
theorem mulModReduceOuterFold_eq_carry (n : EvmWord) (hn : n.toNat ≤ 2 ^ 255) :
    ∀ (m : Nat) (limb : Nat → Word) (r : EvmWord), r.toNat < n.toNat →
      mulModReduceOuterFold n limb r m = mulModReduceOuterFoldCarry n limb r m := by
  intro m
  induction m with
  | zero => intro limb r _; rfl
  | succ m ih =>
    intro limb r hr
    rw [mulModReduceOuterFold_succ, mulModReduceOuterFoldCarry_succ,
      mulModReduceStepN_eq_carry n hn 64 (limb 0) r hr]
    exact ih (fun i => limb (i + 1)) _
      (mulModReduceStepNCarry_lt n (by omega) 64 (limb 0) r hr)

/-- Partial total-MULMOD correctness of the shipped reducer: from the `r = 0`
    initial state, the non-carry outer fold of the product limbs computes
    `(a·b) % n` for every modulus `0 < n ≤ 2^255`. -/
theorem mulModReduceOuterFold_productLimb_eq_mod (a b n : EvmWord)
    (hn0 : 0 < n.toNat) (hn : n.toNat ≤ 2 ^ 255) :
    (mulModReduceOuterFold n (fun i => productLimb a b (7 - i)) 0 8).toNat
      = a.toNat * b.toNat % n.toNat := by
  rw [mulModReduceOuterFold_eq_carry n hn 8 (fun i => productLimb a b (7 - i)) 0
      (by simpa using hn0),
    mulModReduceOuterFoldCarry_toNat_zero_start n _ 8 hn0, mulModLimbsValue_productLimb]

/-- The shipped reducer's output is a valid remainder (`< n`) for `0 < n ≤ 2^255`. -/
theorem mulModReduceOuterFold_productLimb_lt (a b n : EvmWord)
    (hn0 : 0 < n.toNat) (hn : n.toNat ≤ 2 ^ 255) :
    (mulModReduceOuterFold n (fun i => productLimb a b (7 - i)) 0 8).toNat < n.toNat := by
  rw [mulModReduceOuterFold_productLimb_eq_mod a b n hn0 hn]
  exact Nat.mod_lt _ hn0

/-- EvmWord form: for `0 < n ≤ 2^255` the shipped reducer leaves exactly the
    EVM `MULMOD` result word `((a·b) mod n)` truncated to 256 bits. -/
theorem mulModReduceOuterFold_productLimb_eq_evmWord (a b n : EvmWord)
    (hn0 : 0 < n.toNat) (hn : n.toNat ≤ 2 ^ 255) :
    mulModReduceOuterFold n (fun i => productLimb a b (7 - i)) 0 8
      = BitVec.ofNat 256 (a.toNat * b.toNat % n.toNat) := by
  have hlt256 : a.toNat * b.toNat % n.toNat < 2 ^ 256 := by
    have h1 := Nat.mod_lt (a.toNat * b.toNat) hn0
    have h2 : (2 : Nat) ^ 255 < 2 ^ 256 := Nat.pow_lt_pow_right (by decide) (by decide)
    omega
  rw [← BitVec.toNat_inj, mulModReduceOuterFold_productLimb_eq_mod a b n hn0 hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt256]

end EvmAsm.Evm64
