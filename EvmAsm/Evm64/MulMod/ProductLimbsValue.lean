/-
  EvmAsm.Evm64.MulMod.ProductLimbsValue

  Bridge from the eight product limbs to the integer product `a·b`.

  The bit-serial reducer consumes the 512-bit product `a.toNat * b.toNat` as
  eight 64-bit limbs, highest limb first. `mulModLimbsValue` (see
  `ReduceOuterHorner`) reconstructs the base-`2^64` value of a limb stream with
  `limb 0` most significant. Feeding it the product limbs in descending order
  (`fun i => productLimb a b (7 - i)`) therefore recovers the full product:

      mulModLimbsValue (fun i => productLimb a b (7 - i)) 8 = a.toNat * b.toNat

  Since `productLimb a b i = ⌊(a·b) / 2^(64 i)⌋ mod 2^64` is by definition the
  `i`-th base-`2^64` digit, this is a pure digit-reconstruction proved by
  induction with `Nat.mod_mul`; the product fits in `2^512` so the final `mod`
  is the identity.
-/

import EvmAsm.Evm64.MulMod.ReduceOuterHorner
import EvmAsm.Evm64.MulMod.ProductAlgebra

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.MulMod.ProductAlgebra

/-- The `i`-th product limb's value is the `i`-th base-`2^64` digit of `a·b`. -/
theorem productLimb_toNat_eq (a b : EvmWord) (i : Nat) :
    (productLimb a b i).toNat = a.toNat * b.toNat / 2 ^ (64 * i) % 2 ^ 64 := by
  simp only [productLimb, productNat, BitVec.toNat_ofNat]

/-- Reconstructing the limbs `top, top-1, …, 0` highest-first recovers the low
    `64*(top+1)` bits of the product. -/
theorem mulModLimbsValue_productLimb_mod (a b : EvmWord) :
    ∀ top, mulModLimbsValue (fun i => productLimb a b (top - i)) (top + 1)
      = a.toNat * b.toNat % 2 ^ (64 * (top + 1)) := by
  intro top
  induction top with
  | zero =>
    rw [mulModLimbsValue_succ, mulModLimbsValue_zero]
    simp only [Nat.sub_zero, productLimb_toNat_eq, Nat.mul_zero, Nat.pow_zero, Nat.mul_one,
      Nat.add_zero, Nat.div_one, Nat.zero_add]
  | succ top ih =>
    rw [mulModLimbsValue_succ]
    simp only [Nat.sub_zero, Nat.succ_sub_succ, productLimb_toNat_eq]
    rw [ih, show 64 * (top + 1 + 1) = 64 * (top + 1) + 64 from by omega, Nat.pow_add,
      Nat.mod_mul, Nat.add_comm, Nat.mul_comm (2 ^ (64 * (top + 1)))]

/-- The eight product limbs, consumed highest-first, reconstruct the full
    integer product `a·b`. -/
theorem mulModLimbsValue_productLimb (a b : EvmWord) :
    mulModLimbsValue (fun i => productLimb a b (7 - i)) 8 = a.toNat * b.toNat := by
  have hlt : a.toNat * b.toNat < 2 ^ (64 * 8) := by
    have h := Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt
    rw [← Nat.pow_add] at h
    rwa [show (256 : Nat) + 256 = 64 * 8 from rfl] at h
  have h := mulModLimbsValue_productLimb_mod a b 7
  rw [show 64 * (7 + 1) = 64 * 8 from rfl, Nat.mod_eq_of_lt hlt] at h
  exact h

/-- Total MULMOD correctness of the carry-aware reducer: from the `r = 0`
    initial state, the carry-aware outer fold of the product limbs computes
    `(a·b) % n` for **every** positive modulus `n` (no `n ≤ 2^255`
    restriction). -/
theorem mulModReduceOuterFoldCarry_productLimb_eq_mod (a b n : EvmWord)
    (hn0 : 0 < n.toNat) :
    (mulModReduceOuterFoldCarry n (fun i => productLimb a b (7 - i)) 0 8).toNat
      = a.toNat * b.toNat % n.toNat := by
  rw [mulModReduceOuterFoldCarry_toNat_zero_start n _ 8 hn0, mulModLimbsValue_productLimb]

/-- EvmWord form: for every positive modulus `n` the carry-aware reducer leaves
    exactly the EVM `MULMOD` result word `((a·b) mod n)` truncated to 256 bits.
    Total: no `n ≤ 2^255` hypothesis, since `(a·b) % n < n < 2^256` always. -/
theorem mulModReduceOuterFoldCarry_productLimb_eq_evmWord (a b n : EvmWord)
    (hn0 : 0 < n.toNat) :
    mulModReduceOuterFoldCarry n (fun i => productLimb a b (7 - i)) 0 8
      = BitVec.ofNat 256 (a.toNat * b.toNat % n.toNat) := by
  have hlt256 : a.toNat * b.toNat % n.toNat < 2 ^ 256 := by
    have h1 := Nat.mod_lt (a.toNat * b.toNat) hn0
    have h2 : n.toNat < 2 ^ 256 := n.isLt
    omega
  rw [← BitVec.toNat_inj, mulModReduceOuterFoldCarry_productLimb_eq_mod a b n hn0,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt256]

end EvmAsm.Evm64
