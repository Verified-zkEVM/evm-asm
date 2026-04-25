/-
  EvmAsm.Evm64.EvmWordArith.MultiLimb

  Multi-limb arithmetic foundations for division correctness proofs.
  Provides Nat-level properties of half-word decomposition, rv64_divu,
  rv64_mulhu, and multi-limb value representation.
-/

import EvmAsm.Evm64.EvmWordArith.Common
import EvmAsm.Rv64.Instructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- Half-word (32-bit) decomposition of 64-bit words
-- ============================================================================

/-- The upper 32 bits of a 64-bit word: `x >>> 32`. -/
def hi32 (x : Word) : Word := x >>> 32

/-- The lower 32 bits of a 64-bit word: `(x <<< 32) >>> 32`. -/
def lo32 (x : Word) : Word := (x <<< 32) >>> 32

/-- `hi32 x` is bounded by 2^32. -/
theorem hi32_toNat_lt {x : Word} : (hi32 x).toNat < 2 ^ 32 := by
  unfold hi32
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (show x.toNat < 2 ^ 32 * 2 ^ 32 by have := x.isLt; omega)

/-- `lo32 x` is bounded by 2^32. -/
theorem lo32_toNat_lt {x : Word} : (lo32 x).toNat < 2 ^ 32 := by
  unfold lo32
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow]
  simp only [Nat.shiftLeft_eq]
  apply Nat.div_lt_of_lt_mul
  calc x.toNat * 2 ^ 32 % 2 ^ 64
      < 2 ^ 64 := Nat.mod_lt _ (by positivity)
    _ = 2 ^ 32 * 2 ^ 32 := by ring

/-- Half-word decomposition: `x = hi32(x) * 2^32 + lo32(x)` at the Nat level. -/
theorem halfword_decompose {x : Word} :
    x.toNat = (hi32 x).toNat * 2 ^ 32 + (lo32 x).toNat := by
  unfold hi32 lo32
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  simp only [Nat.shiftLeft_eq]
  have h_lo : x.toNat * 2 ^ 32 % 2 ^ 64 / 2 ^ 32 = x.toNat % 2 ^ 32 := by
    have := x.isLt; omega
  rw [h_lo]
  have := Nat.div_add_mod x.toNat (2 ^ 32)
  omega

-- ============================================================================
-- rv64_divu Nat-level correctness
-- ============================================================================

private theorem beq_zero_false {b : Word} (hb : b ≠ 0) : (b == 0#64) = false := by
  cases h : b == 0#64
  · rfl
  · exfalso; apply hb; exact eq_of_beq h

/-- rv64_divu computes Nat-level division when divisor is nonzero. -/
theorem rv64_divu_toNat (a b : Word) (hb : b ≠ 0) :
    (rv64_divu a b).toNat = a.toNat / b.toNat := by
  unfold rv64_divu; rw [beq_zero_false hb]; exact BitVec.toNat_udiv

/-- rv64_divu quotient times divisor doesn't exceed dividend. -/
theorem rv64_divu_mul_le (a b : Word) (hb : b ≠ 0) :
    (rv64_divu a b).toNat * b.toNat ≤ a.toNat := by
  rw [rv64_divu_toNat a b hb]; exact Nat.div_mul_le_self a.toNat b.toNat

/-- Nat modulo is less than a nonzero Word divisor. -/
theorem word_mod_lt (a b : Word) (hb : b ≠ 0) :
    a.toNat % b.toNat < b.toNat := by
  apply Nat.mod_lt
  exact Nat.pos_of_ne_zero (by intro h; apply hb; exact BitVec.eq_of_toNat_eq h)

/-- rv64_divu Euclidean property at the Nat level. -/
theorem rv64_divu_euclidean (a b : Word) (hb : b ≠ 0) :
    a.toNat = (rv64_divu a b).toNat * b.toNat + a.toNat % b.toNat := by
  rw [rv64_divu_toNat a b hb]
  have := Nat.div_add_mod a.toNat b.toNat
  linarith [Nat.mul_comm b.toNat (a.toNat / b.toNat)]

-- ============================================================================
-- rv64_mulhu Nat-level correctness
-- ============================================================================

/-- rv64_mulhu gives the high 64 bits of the full 128-bit product. -/
theorem rv64_mulhu_toNat {a b : Word} :
    (rv64_mulhu a b).toNat = (a.toNat * b.toNat) / 2 ^ 64 := by
  unfold rv64_mulhu
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
             BitVec.toNat_mul (n := 128), Nat.shiftRight_eq_div_pow]
  have := a.isLt; have := b.isLt
  have hprod : a.toNat * b.toNat < 2 ^ 128 := by nlinarith
  rw [Nat.mod_eq_of_lt (show a.toNat < 2 ^ 128 by omega),
      Nat.mod_eq_of_lt (show b.toNat < 2 ^ 128 by omega),
      Nat.mod_eq_of_lt hprod, Nat.mod_eq_of_lt]
  exact Nat.div_lt_of_lt_mul (by linarith)

/-- MUL gives the low 64 bits of the product (mod 2^64). -/
theorem mul_toNat {a b : Word} : (a * b).toNat = (a.toNat * b.toNat) % 2 ^ 64 :=
  BitVec.toNat_mul a b

/-- MULHU * 2^64 + MUL = full product (Nat level). -/
theorem mul_full_product (a b : Word) :
    (rv64_mulhu a b).toNat * 2 ^ 64 + (a * b).toNat = a.toNat * b.toNat := by
  rw [rv64_mulhu_toNat, mul_toNat]
  have := Nat.div_add_mod (a.toNat * b.toNat) (2 ^ 64)
  linarith [Nat.mul_comm (2 ^ 64) (a.toNat * b.toNat / 2 ^ 64)]

/-- Each partial product q*v_i decomposes into lo (MUL) and hi (MULHU) parts. -/
theorem partial_product_decompose (q vi : Word) :
    q.toNat * vi.toNat =
    (rv64_mulhu q vi).toNat * 2 ^ 64 + (q * vi).toNat :=
  (mul_full_product q vi).symm

-- ============================================================================
-- 128-bit value representation
-- ============================================================================

/-- A 128-bit value represented as hi * 2^64 + lo. -/
def val128 (hi lo : Word) : Nat := hi.toNat * 2 ^ 64 + lo.toNat

theorem val128_bound {hi lo : Word} : val128 hi lo < 2 ^ 128 := by
  unfold val128; have := hi.isLt; have := lo.isLt; nlinarith

/-- If the high half is less than d, the 128-bit value is less than d * 2^64. -/
theorem val128_lt_of_hi_lt (hi lo : Word) (d : Nat) (hhi : hi.toNat < d) :
    val128 hi lo < d * 2 ^ 64 := by
  unfold val128; have := lo.isLt; nlinarith

-- ============================================================================
-- Multi-limb (256-bit) value representation
-- ============================================================================

/-- The Nat value of a 4-limb number. -/
def val256 (l0 l1 l2 l3 : Word) : Nat :=
  l0.toNat + l1.toNat * 2 ^ 64 + l2.toNat * 2 ^ 128 + l3.toNat * 2 ^ 192

theorem val256_eq_fromLimbs_toNat {l0 l1 l2 l3 : Word} :
    val256 l0 l1 l2 l3 = (fromLimbs (fun i : Fin 4 =>
      match i with | 0 => l0 | 1 => l1 | 2 => l2 | 3 => l3)).toNat := by
  unfold val256; rw [fromLimbs_toNat]

theorem val256_bound (l0 l1 l2 l3 : Word) : val256 l0 l1 l2 l3 < 2 ^ 256 := by
  unfold val256
  have := l0.isLt; have := l1.isLt
  have := l2.isLt; have := l3.isLt
  nlinarith

/-- Connecting val256 to EvmWord.toNat via getLimb decomposition. -/
theorem val256_eq_toNat (v : EvmWord) :
    val256 (v.getLimb 0) (v.getLimb 1) (v.getLimb 2) (v.getLimb 3) = v.toNat := by
  unfold val256; exact (toNat_getLimb_decompose v).symm

-- ============================================================================
-- Word subtraction Nat-level properties
-- ============================================================================

/-- Word subtraction wraps mod 2^64. -/
theorem word_sub_toNat {a b : Word} :
    (a - b).toNat = (a.toNat + 2 ^ 64 - b.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_sub]; have := b.isLt; omega

/-- When a ≥ b at Nat level, subtraction is exact. -/
theorem word_sub_toNat_of_le (a b : Word) (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

/-- SLTU gives 1 iff a < b at Nat level. -/
theorem sltu_eq_ite (a b : Word) :
    (if BitVec.ult a b then (1 : Word) else (0 : Word)).toNat =
    if a.toNat < b.toNat then 1 else 0 := by
  by_cases h : a.toNat < b.toNat
  · have : BitVec.ult a b := decide_eq_true (BitVec.lt_def.mpr h)
    simp [this, h]
  · have : ¬ BitVec.ult a b := by
      intro hc; exact h (BitVec.lt_def.mp (of_decide_eq_true hc))
    simp [this, h]

/-- Subtraction cases: exact when a ≥ b, wraps when a < b. -/
theorem word_sub_cases (a b : Word) :
    ((a - b).toNat = a.toNat - b.toNat ∧ a.toNat ≥ b.toNat) ∨
    ((a - b).toNat = a.toNat + 2 ^ 64 - b.toNat ∧ a.toNat < b.toNat) := by
  by_cases h : a.toNat ≥ b.toNat
  · left; exact ⟨BitVec.toNat_sub_of_le (BitVec.le_def.mpr h), h⟩
  · right
    constructor
    · rw [word_sub_toNat]; have := a.isLt; have := b.isLt; omega
    · omega

-- ============================================================================
-- Single-limb × multi-limb product (Nat level)
-- ============================================================================

/-- When multiplying a single limb q by a 4-limb number v, the Nat-level product
    distributes over the limbs. -/
theorem single_mul_val256 (q v0 v1 v2 v3 : Word) :
    q.toNat * val256 v0 v1 v2 v3 =
    q.toNat * v0.toNat + q.toNat * v1.toNat * 2 ^ 64 +
    q.toNat * v2.toNat * 2 ^ 128 + q.toNat * v3.toNat * 2 ^ 192 := by
  unfold val256; ring

end EvmWord

end EvmAsm.Evm64
