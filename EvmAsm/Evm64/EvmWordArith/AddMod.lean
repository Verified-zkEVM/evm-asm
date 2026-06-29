/-
  EvmAsm.Evm64.EvmWordArith.AddMod

  EVM ADDMOD semantics: word-level definition and correctness theorem.

  Provides:
  * `EvmWord.addmod a b N` — the EVM `ADDMOD` operation: `(a + b) mod N`
    with `N = 0 ⇒ 0`, where the intermediate sum `a + b` is taken at
    full 257-bit precision (carry out of bit 255).
  * `EvmWord.addCarry a b` — the 257-bit add helper: returns the
    Boolean carry-out alongside the truncated 256-bit sum, with a
    proof that the pair faithfully represents the natural-number sum
    `a.toNat + b.toNat`.
  * `EvmWord.addmod_correct` — algebraic correctness:
    `(addmod a b N).toNat = if N = 0 then 0 else (a.toNat + b.toNat) % N.toNat`.

  This is the slice-2 deliverable for GH issue #91 (ADDMOD/MULMOD)
  and matches the algebraic shape required by the future
  `evm_addmod_stack_spec` (slice 3, beads `evm-asm-sord`).

  See `docs/91-addmod-mulmod-survey.md` §1.3, §3, §4 for context.
-/

import EvmAsm.Evm64.EvmWordArith.DivCorrect

namespace EvmAsm.Evm64

namespace EvmWord

-- ============================================================================
-- 257-bit add helper
-- ============================================================================

/-- Pair of (carry-out, truncated 256-bit sum) for the addition of two
    `EvmWord`s. The carry bit is `true` exactly when `a.toNat + b.toNat`
    overflows 256 bits, i.e. equals `2^256` or more. -/
def addCarry (a b : EvmWord) : Bool × EvmWord :=
  (decide (a.toNat + b.toNat ≥ 2 ^ 256), a + b)

/-- The 257-bit identity for `addCarry`: the natural-number sum of the
    inputs is exactly `(carry · 2^256) + truncated`. This is the
    algebraic shape downstream proofs use to bridge the limb-level
    RISC-V add-with-carry to the EVM word-level model. -/
theorem addCarry_spec (a b : EvmWord) :
    a.toNat + b.toNat =
      (if (addCarry a b).fst then 2 ^ 256 else 0) + (addCarry a b).snd.toNat := by
  unfold addCarry
  simp only [BitVec.toNat_add]
  have ha : a.toNat < 2 ^ 256 := a.isLt
  have hb : b.toNat < 2 ^ 256 := b.isLt
  by_cases h : a.toNat + b.toNat ≥ 2 ^ 256
  · simp only [decide_eq_true_eq, h, ↓reduceIte]
    have hmod : (a.toNat + b.toNat) % 2 ^ 256 = a.toNat + b.toNat - 2 ^ 256 := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]; omega
  · simp only [decide_eq_true_eq, h, ↓reduceIte]
    have hlt : a.toNat + b.toNat < 2 ^ 256 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

-- ============================================================================
-- ADDMOD
-- ============================================================================

/-- EVM `ADDMOD` semantics: `(a + b) mod N` evaluated at full 257-bit
    precision when `N ≠ 0`; returns `0` when `N = 0`. -/
def addmod (a b N : EvmWord) : EvmWord :=
  if N = 0 then 0 else BitVec.ofNat 256 ((a.toNat + b.toNat) % N.toNat)

/-- Algebraic correctness of `EvmWord.addmod`. -/
theorem addmod_correct (a b N : EvmWord) :
    (EvmWord.addmod a b N).toNat =
      if N = 0 then 0 else (a.toNat + b.toNat) % N.toNat := by
  unfold addmod
  by_cases h : N = 0
  · simp [h]
  · simp only [if_neg h]
    rw [BitVec.toNat_ofNat]
    -- The mod result is < N.toNat ≤ 2^256 - 1 < 2^256, so no further
    -- reduction modulo 2^256 is needed.
    have hNpos : 0 < N.toNat := by
      have hne : N.toNat ≠ 0 := by
        intro hz
        apply h
        exact BitVec.eq_of_toNat_eq (by simpa using hz)
      omega
    have hlt : (a.toNat + b.toNat) % N.toNat < 2 ^ 256 := by
      have hN : N.toNat < 2 ^ 256 := N.isLt
      have : (a.toNat + b.toNat) % N.toNat < N.toNat := Nat.mod_lt _ hNpos
      omega
    exact Nat.mod_eq_of_lt hlt

-- ============================================================================
-- modAdd: pre-reduced ADDMOD helper
-- ============================================================================
--
-- A specialized variant of `addmod` that assumes both operands are already
-- reduced modulo `N`, i.e. `a.toNat < N.toNat` and `b.toNat < N.toNat`. Under
-- this precondition `a.toNat + b.toNat < 2 * N.toNat`, so the modular sum
-- equals either the sum itself or the sum minus `N` (a single conditional
-- subtraction). This shape models what the RISC-V `ADDMOD` program emits at
-- the limb level — a 257-bit add followed by a conditional subtract — without
-- the full division step that `addmod` would otherwise need to model.
--
-- The bridge lemma `modAdd_correct` lets downstream Programs (notably
-- `evm_addmod`, beads `evm-asm-sord`) reason about the post-condition
-- `(a + b) mod N` without re-deriving the bound from `addmod_correct` plus
-- the operand-bound side-conditions. Refs GH #91, beads `evm-asm-539jk`.

/-- Pre-reduced ADDMOD: `(a + b) mod N` assuming `a, b < N`. Distinct from
    `addmod` in that the precondition rules out the `N = 0` branch, so the
    result coincides with `BitVec.ofNat 256 ((a.toNat + b.toNat) % N.toNat)`
    unconditionally. -/
def modAdd (a b N : EvmWord) : EvmWord :=
  BitVec.ofNat 256 ((a.toNat + b.toNat) % N.toNat)

/-- Algebraic correctness of `EvmWord.modAdd` under the pre-reduced
    precondition `a, b < N`: the `BitVec` truncation is a no-op because
    `(a + b) mod N < N ≤ 2^256`. -/
theorem modAdd_correct (a b N : EvmWord)
    (ha : a.toNat < N.toNat) (_hb : b.toNat < N.toNat) :
    (EvmWord.modAdd a b N).toNat = (a.toNat + b.toNat) % N.toNat := by
  unfold modAdd
  rw [BitVec.toNat_ofNat]
  -- The precondition forces `N.toNat > 0` (since `a.toNat < N.toNat` with
  -- `a.toNat ≥ 0` implies `N.toNat ≥ 1`), so the mod result is `< N.toNat`,
  -- hence `< 2^256`, hence already in range.
  have hNpos : 0 < N.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) ha
  have hN : N.toNat < 2 ^ 256 := N.isLt
  have hlt : (a.toNat + b.toNat) % N.toNat < 2 ^ 256 := by
    have : (a.toNat + b.toNat) % N.toNat < N.toNat := Nat.mod_lt _ hNpos
    omega
  exact Nat.mod_eq_of_lt hlt

/-- `modAdd` agrees with the unconstrained `addmod` whenever `N ≠ 0`: both
    return `BitVec.ofNat 256 ((a.toNat + b.toNat) % N.toNat)`. This makes
    `modAdd` a drop-in replacement at call sites that already discharge the
    pre-reduction bounds, while keeping `addmod` available for the unguarded
    EVM semantics. -/
theorem modAdd_eq_addmod_of_ne_zero (a b N : EvmWord) (h : N ≠ 0) :
    EvmWord.modAdd a b N = EvmWord.addmod a b N := by
  unfold modAdd addmod
  rw [if_neg h]

-- ============================================================================
-- Carry-split bridge for ADDMOD
-- ============================================================================

/-- ADDMOD-via-carry-split: when `N ≠ 0`, the algebraic ADDMOD result is the
    `mod N` of `addCarry`'s outputs combined as a 257-bit Nat.

    This is the algebraic bridge used by the runtime spec (slice 3,
    `evm-asm-sord`): the RISC-V add-with-carry pipeline returns a
    `(carry-bit, truncated-256-bit-sum)` pair, and downstream code wants
    to identify the post-condition with `EvmWord.addmod`. The lemma is a
    direct consequence of `addCarry_spec` and `addmod_correct`. -/
theorem addmod_eq_carry_split (a b N : EvmWord) (h : N ≠ 0) :
    (EvmWord.addmod a b N).toNat =
      ((if (addCarry a b).fst then 2 ^ 256 else 0) + (addCarry a b).snd.toNat)
        % N.toNat := by
  rw [addmod_correct, if_neg h, ← addCarry_spec]

/-- If `a + b` does not overflow 256 bits, then reducing the truncated EVM word
    sum is the same as ADDMOD's full-precision sum. This is the semantic bridge
    for the current ADDMOD skeleton, whose MOD call sees only `a + b`. -/
theorem mod_truncated_sum_eq_addmod_of_no_overflow (a b N : EvmWord)
    (hNoOverflow : a.toNat + b.toNat < 2 ^ 256) :
    EvmWord.mod (a + b) N = EvmWord.addmod a b N := by
  apply BitVec.eq_of_toNat_eq
  rw [mod_correct, addmod_correct]
  by_cases hN : N = 0
  · simp [hN]
  · simp only [if_neg hN]
    have hsum : (a + b).toNat = a.toNat + b.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hNoOverflow]
    rw [hsum]

-- ============================================================================
-- pow256ModN: 2^256 mod N
-- ============================================================================
--
-- Constant the runtime needs to materialize the algebraic value
-- `2^256 mod N` as an `EvmWord`. Used by the runtime variants of
-- ADDMOD/MULMOD that produce a `(high, low)` pair from a wider
-- intermediate (carry-bit + 256-bit sum for ADDMOD; 256+256 schoolbook
-- product for MULMOD) and need to reduce the high half by N. The
-- natural-number identity
--
--     (h * 2^256 + l) % N = (h * (2^256 % N) + l) % N
--
-- means the runtime can multiply the high half by the constant
-- `pow256ModN N` (a 256-bit value) instead of working with a wider
-- intermediate.
--
-- Slice scope: pure word-level definition + correctness lemma; downstream
-- slices wire it into the runtime programs (beads parent evm-asm-z7qm,
-- GH #91).

/-- The constant `2^256 mod N` as an `EvmWord`. Returns 0 when `N = 0`,
    matching the convention used by `addmod` / `mulmod`. The truncation
    via `BitVec.ofNat 256` is a no-op because `2^256 % N.toNat < N.toNat
    ≤ 2^256`. -/
def pow256ModN (N : EvmWord) : EvmWord :=
  if N = 0 then 0 else BitVec.ofNat 256 (2 ^ 256 % N.toNat)

/-- Algebraic correctness of `EvmWord.pow256ModN`. -/
theorem pow256ModN_correct (N : EvmWord) :
    (EvmWord.pow256ModN N).toNat =
      if N = 0 then 0 else 2 ^ 256 % N.toNat := by
  unfold pow256ModN
  by_cases h : N = 0
  · simp [h]
  · simp only [if_neg h]
    rw [BitVec.toNat_ofNat]
    have hNpos : 0 < N.toNat := by
      have hne : N.toNat ≠ 0 := by
        intro hz
        apply h
        exact BitVec.eq_of_toNat_eq (by simpa using hz)
      omega
    have hlt : 2 ^ 256 % N.toNat < 2 ^ 256 := by
      have hN : N.toNat < 2 ^ 256 := N.isLt
      have : 2 ^ 256 % N.toNat < N.toNat := Nat.mod_lt _ hNpos
      omega
    exact Nat.mod_eq_of_lt hlt

end EvmWord

end EvmAsm.Evm64
