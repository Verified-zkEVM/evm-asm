/-
  EvmAsm.Evm64.EvmWordArith.AddModCondSub

  Phase-3 M3d value bridges for the total ADDMOD carry branch (issue #9704):
  the two genuinely-semantic facts the machine `Ld` sub-chain needs to fold
  the branch-free conditional subtract into `EvmWord.addmod`.

  * `evm_add_carry3_eq_overflow` — the `evm_add` 4-limb carry-out (`x5` in
    `evm_add_stack_spec_within`, the `carry3` let-chain) equals the 257th-bit
    overflow indicator `if a.toNat + b.toNat ≥ 2^256 then 1 else 0`.
    `add_carry_chain_correct` proves the *result* limbs but not the carry-out;
    this closes that gap via `addback_4limb_val256`.
  * `condSub_mask_eq` — the machine mask word `0 − (carry ||| (b3 ^^^ 1))`
    (a 64-bit register value applied per-limb) equals `if take then -1 else 0`
    with `take = m.toNat + rMod.toNat ≥ N.toNat`, given `carry` = the add
    overflow bit and `b3` = the `(m+rMod) < N` borrow-out. This is the
    take-flag equivalence that lets `masked_sub_eq_modAdd` apply.
-/

import EvmAsm.Evm64.EvmWordArith.AddMod
import EvmAsm.Evm64.EvmWordArith.Arithmetic
import EvmAsm.Evm64.EvmWordArith.DivAddbackLimb

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- evm_add carry-out = 257th-bit overflow
-- ============================================================================

/-- The `evm_add` 4-limb carry-out. Mirrors the `carry3` let-chain of
    `evm_add_stack_spec_within` exactly (same intermediate lets), and proves it
    equals the overflow indicator `if a.toNat + b.toNat ≥ 2^256 then 1 else 0`. -/
theorem evm_add_carry3_eq_overflow (a b : EvmWord) :
    let a0 := a.getLimb 0; let b0 := b.getLimb 0
    let a1 := a.getLimb 1; let b1 := b.getLimb 1
    let a2 := a.getLimb 2; let b2 := b.getLimb 2
    let a3 := a.getLimb 3; let b3 := b.getLimb 3
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    let carry3 := carry3a ||| carry3b
    carry3 = if a.toNat + b.toNat ≥ 2 ^ 256 then (1 : Word) else 0 := by
  intro a0 b0 a1 b1 a2 b2 a3 b3 sum0 carry0 psum1 carry1a result1 carry1b carry1
    psum2 carry2a result2 carry2b carry2 psum3 carry3a result3 carry3b carry3
  -- carry toNat via the division helpers
  have hc0 : carry0.toNat = (a0.toNat + b0.toNat) / 2 ^ 64 := carry_toNat
  have hc0_le : carry0.toNat ≤ 1 := by have := a0.isLt; have := b0.isLt; rw [hc0]; omega
  have hc1 : carry1.toNat = (a1.toNat + b1.toNat + carry0.toNat) / 2 ^ 64 :=
    combined_carry_toNat hc0_le
  have hc1_le : carry1.toNat ≤ 1 := by have := a1.isLt; have := b1.isLt; rw [hc1]; omega
  have hc2 : carry2.toNat = (a2.toNat + b2.toNat + carry1.toNat) / 2 ^ 64 :=
    combined_carry_toNat hc1_le
  have hc2_le : carry2.toNat ≤ 1 := by have := a2.isLt; have := b2.isLt; rw [hc2]; omega
  have hc3 : carry3.toNat = (a3.toNat + b3.toNat + carry2.toNat) / 2 ^ 64 :=
    combined_carry_toNat hc2_le
  have hc3_le : carry3.toNat ≤ 1 := by have := a3.isLt; have := b3.isLt; rw [hc3]; omega
  -- per-limb Nat equations (x = (x / W) * W + x % W); result limbs are the mod parts
  have e0 : a0.toNat + b0.toNat = carry0.toNat * 2 ^ 64 + sum0.toNat := by
    have hs : sum0.toNat = (a0.toNat + b0.toNat) % 2 ^ 64 := BitVec.toNat_add a0 b0
    rw [hc0, hs]; omega
  have e1 : a1.toNat + b1.toNat + carry0.toNat = carry1.toNat * 2 ^ 64 + result1.toNat := by
    have hr : result1.toNat = (psum1.toNat + carry0.toNat) % 2 ^ 64 := BitVec.toNat_add psum1 carry0
    have hp : psum1.toNat = (a1.toNat + b1.toNat) % 2 ^ 64 := BitVec.toNat_add a1 b1
    have hb := b1.isLt; have ha := a1.isLt
    have hres : result1.toNat = (a1.toNat + b1.toNat + carry0.toNat) % 2 ^ 64 := by
      rw [hr, hp]; omega
    rw [hc1, hres]; omega
  have e2 : a2.toNat + b2.toNat + carry1.toNat = carry2.toNat * 2 ^ 64 + result2.toNat := by
    have hr : result2.toNat = (psum2.toNat + carry1.toNat) % 2 ^ 64 := BitVec.toNat_add psum2 carry1
    have hp : psum2.toNat = (a2.toNat + b2.toNat) % 2 ^ 64 := BitVec.toNat_add a2 b2
    have hb := b2.isLt; have ha := a2.isLt
    have hres : result2.toNat = (a2.toNat + b2.toNat + carry1.toNat) % 2 ^ 64 := by
      rw [hr, hp]; omega
    rw [hc2, hres]; omega
  have e3 : a3.toNat + b3.toNat + carry2.toNat = carry3.toNat * 2 ^ 64 + result3.toNat := by
    have hr : result3.toNat = (psum3.toNat + carry2.toNat) % 2 ^ 64 := BitVec.toNat_add psum3 carry2
    have hp : psum3.toNat = (a3.toNat + b3.toNat) % 2 ^ 64 := BitVec.toNat_add a3 b3
    have hb := b3.isLt; have ha := a3.isLt
    have hres : result3.toNat = (a3.toNat + b3.toNat + carry2.toNat) % 2 ^ 64 := by
      rw [hr, hp]; omega
    rw [hc3, hres]; omega
  -- 4-limb telescoping: val256 a + val256 b = val256 result + carry3.toNat * 2^256
  have hval := addback_4limb_val256 a0 a1 a2 a3 b0 b1 b2 b3 sum0 result1 result2 result3
    carry0.toNat carry1.toNat carry2.toNat carry3.toNat e0 e1 e2 e3
  rw [val256_eq_toNat a, val256_eq_toNat b] at hval
  have hsumLt : val256 sum0 result1 result2 result3 < 2 ^ 256 := val256_bound _ _ _ _
  -- a.toNat + b.toNat = val256 result + carry3.toNat * 2^256, val256 result < 2^256, carry3 ≤ 1
  have hc3_val : carry3.toNat = if a.toNat + b.toNat ≥ 2 ^ 256 then 1 else 0 := by
    split <;> omega
  apply BitVec.eq_of_toNat_eq
  rw [hc3_val]
  split <;> simp [BitVec.toNat_ofNat]

-- ============================================================================
-- take-flag mask equivalence
-- ============================================================================

/-- Bit-algebra: for `carry, b3 ∈ {0,1}` as words,
    `0 − (carry ||| (b3 ^^^ 1)) = -1` iff `carry = 1 ∨ b3 = 0`, else `0`. -/
private theorem mask_word_cases (carry b3 : Word)
    (hc : carry = 0 ∨ carry = 1) (hb : b3 = 0 ∨ b3 = 1) :
    (0 : Word) - (carry ||| (b3 ^^^ (1 : Word))) =
      if carry = 1 ∨ b3 = 0 then (-1 : Word) else 0 := by
  rcases hc with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- **Take-flag equivalence.** The machine mask word `0 − (carry ||| (b3 ^^^ 1))`
    equals `if take then -1 else 0` (the 64-bit per-limb select) with
    `take = m.toNat + rMod.toNat ≥ N.toNat`, given `carry` = the add overflow bit
    (`m.toNat + rMod.toNat ≥ 2^256`), `b3` = the `(m+rMod) < N` borrow-out, and
    the pre-reduced operand bounds `m, rMod < N`. -/
theorem condSub_mask_eq (m rMod N : EvmWord) (carry b3 : Word)
    (hcarry : carry = if m.toNat + rMod.toNat ≥ 2 ^ 256 then (1 : Word) else 0)
    (hb3 : b3 = if BitVec.ult (m + rMod) N then (1 : Word) else 0) :
    (0 : Word) - (carry ||| (b3 ^^^ (1 : Word))) =
      if m.toNat + rMod.toNat ≥ N.toNat then (-1 : Word) else 0 := by
  have hN256 : N.toNat < 2 ^ 256 := N.isLt
  have hc01 : carry = 0 ∨ carry = 1 := by rw [hcarry]; split <;> simp
  have hb01 : b3 = 0 ∨ b3 = 1 := by rw [hb3]; split <;> simp
  rw [mask_word_cases carry b3 hc01 hb01]
  have hsum : (m + rMod).toNat = (m.toNat + rMod.toNat) % 2 ^ 256 := BitVec.toNat_add m rMod
  by_cases htake : m.toNat + rMod.toNat ≥ N.toNat
  · rw [if_pos htake, if_pos]
    by_cases hov : m.toNat + rMod.toNat ≥ 2 ^ 256
    · left; rw [hcarry, if_pos hov]
    · right
      rw [hb3]
      have hlt : (m + rMod).toNat = m.toNat + rMod.toNat := by
        rw [hsum, Nat.mod_eq_of_lt (by omega)]
      have hnult : ¬ BitVec.ult (m + rMod) N := by
        rw [BitVec.ult]; simp only [decide_eq_true_eq]; rw [hlt]; omega
      rw [if_neg hnult]
  · rw [if_neg htake, if_neg]
    have hov : ¬ m.toNat + rMod.toNat ≥ 2 ^ 256 := by omega
    have hlt : (m + rMod).toNat = m.toNat + rMod.toNat := by
      rw [hsum, Nat.mod_eq_of_lt (by omega)]
    have hult : BitVec.ult (m + rMod) N := by
      rw [BitVec.ult]; simp only [decide_eq_true_eq]; rw [hlt]; omega
    rw [not_or]
    refine ⟨by rw [hcarry, if_neg hov]; decide, ?_⟩
    rw [hb3, if_pos hult]; decide

/-- **Carry-path result bridge.** The pre-reduced modular add's machine output
    `(m + rMod) − (N &&& condSubMask take)` — with `m = pow256ModN N`,
    `rMod = mod (a+b) N`, and `take` the arithmetic subtract-fires flag — equals
    the EVM `ADDMOD` result, when the 257-bit add carried. Combines
    `masked_sub_eq_modAdd` (the pre-reduced cond-subtract) with
    `addmod_carry_eq_modAdd` (the carry-split semantics). This is the pure value
    fold the Ld machine chain lands into. -/
theorem sum_minus_masked_N_eq_addmod (a b N : EvmWord) (hN : N ≠ 0)
    (hcarry : (EvmWord.addCarry a b).fst = true) :
    (EvmWord.pow256ModN N + EvmWord.mod (a + b) N)
        - (N &&& EvmWord.condSubMask
            (decide ((EvmWord.pow256ModN N).toNat
              + (EvmWord.mod (a + b) N).toNat ≥ N.toNat)))
      = EvmWord.addmod a b N := by
  have hNpos : 0 < N.toNat := by
    have : N.toNat ≠ 0 := fun hz => hN (BitVec.eq_of_toNat_eq (by simpa using hz))
    omega
  have hm : (EvmWord.pow256ModN N).toNat < N.toNat := EvmWord.pow256ModN_lt N hN
  have hr : (EvmWord.mod (a + b) N).toNat < N.toNat := by
    rw [EvmWord.mod_correct, if_neg hN]; exact Nat.mod_lt _ hNpos
  rw [EvmWord.masked_sub_eq_modAdd (EvmWord.pow256ModN N) (EvmWord.mod (a + b) N) N
    hm hr _ (by simp)]
  exact (EvmWord.addmod_carry_eq_modAdd a b N hN hcarry).symm

end EvmWord

end EvmAsm.Evm64
