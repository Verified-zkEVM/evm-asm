/-
  EvmAsm.Evm64.EvmWordArith.DivBridge

  Master bridge theorems connecting Nat-level Euclidean properties to
  EvmWord.div/mod correctness. These are the final lemmas needed to
  prove the algorithm's output equals BitVec.udiv/umod.

  Key theorems:
  - bv_eq_of_nat_eq: Nat equation → BitVec equation (auto no-overflow)
  - div_of_nat_euclidean: Nat Euclidean property → q = EvmWord.div a b
  - mod_of_nat_euclidean: Nat Euclidean property → r = EvmWord.mod a b
-/

import EvmAsm.Evm64.EvmWordArith.Normalization

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- Nat → BitVec bridge
-- ============================================================================

/-- If the Nat-level equation `a = b * q + r` holds and `a < 2^256`,
    then the BitVec-level equation `a = b * q + r` holds (no overflow). -/
theorem bv_eq_of_nat_eq {a b q r : EvmWord}
    (h_nat : a.toNat = b.toNat * q.toNat + r.toNat) :
    a = b * q + r := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_mul]
  have := a.isLt
  rw [Nat.mod_eq_of_lt (show b.toNat * q.toNat < 2^256 by omega),
      Nat.mod_eq_of_lt (show b.toNat * q.toNat + r.toNat < 2^256 by omega)]
  exact h_nat

/-- Nat strict inequality implies BitVec strict inequality. -/
theorem bv_lt_of_nat_lt {a b : EvmWord} (h : a.toNat < b.toNat) : a < b :=
  BitVec.lt_def.mpr h

-- ============================================================================
-- Master bridge: Nat Euclidean → EvmWord.div/mod
-- ============================================================================

/-- If the Nat-level Euclidean property holds (`a = b * q + r` with `r < b`),
    then `q = EvmWord.div a b`.

    This is the master bridge theorem: to prove the algorithm computes
    the correct quotient, it suffices to show the Euclidean property at
    the Nat level. The no-overflow condition is automatic since `a < 2^256`. -/
theorem div_of_nat_euclidean (a b q r : EvmWord) (hbnz : b ≠ 0)
    (h_nat_eq : a.toNat = b.toNat * q.toNat + r.toNat)
    (h_nat_lt : r.toNat < b.toNat) :
    q = EvmWord.div a b :=
  div_eq_of_euclidean hbnz
    (bv_eq_of_nat_eq h_nat_eq)
    (bv_lt_of_nat_lt h_nat_lt)
    (by have := a.isLt; omega)

/-- If the Nat-level Euclidean property holds (`a = b * q + r` with `r < b`),
    then `r = EvmWord.mod a b`. -/
theorem mod_of_nat_euclidean (a b q r : EvmWord) (hbnz : b ≠ 0)
    (h_nat_eq : a.toNat = b.toNat * q.toNat + r.toNat)
    (h_nat_lt : r.toNat < b.toNat) :
    r = EvmWord.mod a b :=
  mod_eq_of_euclidean hbnz
    (bv_eq_of_nat_eq h_nat_eq)
    (bv_lt_of_nat_lt h_nat_lt)
    (by have := a.isLt; omega)

-- ============================================================================
-- fromLimbs helpers for connecting limb-level specs to EvmWord-level
-- ============================================================================

/-- fromLimbs with a single nonzero limb in position 0: toNat = q.toNat. -/
theorem fromLimbs_single_toNat (q : Word) :
    (fromLimbs fun i : Fin 4 => match i with | 0 => q | _ => 0).toNat = q.toNat := by
  rw [fromLimbs_toNat]; simp

/-- val256 expressed via fromLimbs.toNat. -/
theorem val256_fromLimbs (l0 l1 l2 l3 : Word) :
    val256 l0 l1 l2 l3 =
    (fromLimbs fun i : Fin 4 => match i with | 0 => l0 | 1 => l1 | 2 => l2 | 3 => l3).toNat :=
  val256_eq_fromLimbs_toNat l0 l1 l2 l3

/-- Connecting val256 to EvmWord operations via toNat. -/
theorem val256_mul_single (q v0 v1 v2 v3 : Word) :
    q.toNat * val256 v0 v1 v2 v3 =
    q.toNat * v0.toNat + q.toNat * v1.toNat * 2^64 +
    q.toNat * v2.toNat * 2^128 + q.toNat * v3.toNat * 2^192 :=
  single_mul_val256 q v0 v1 v2 v3

-- ============================================================================
-- End-to-end: from mulsub chain to div/mod correctness
-- ============================================================================

/-- If the multiply-subtract chain gives `val256 a = val256 r + q * val256 b`
    (no underflow) and `val256 r < val256 b`, then `fromLimbs q_limbs = div a b`.

    This connects `mulsub_chain_no_underflow` to `div_of_nat_euclidean`. -/
theorem div_from_mulsub {a b q r : EvmWord}
    (hbnz : b ≠ 0)
    (h_chain : a.toNat = b.toNat * q.toNat + r.toNat)
    (h_rem : r.toNat < b.toNat) :
    q = EvmWord.div a b ∧ r = EvmWord.mod a b :=
  ⟨div_of_nat_euclidean a b q r hbnz h_chain h_rem,
   mod_of_nat_euclidean a b q r hbnz h_chain h_rem⟩

end EvmWord

end EvmAsm.Evm64
