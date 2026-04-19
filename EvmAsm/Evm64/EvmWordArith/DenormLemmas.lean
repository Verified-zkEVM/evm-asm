/-
  EvmAsm.Evm64.EvmWordArith.DenormLemmas

  Denormalization round-trip lemmas for the remainder in Knuth's algorithm D:
  after normalized-mulsub produces r_norm (scaled by 2^s), right-shifting by s
  bits recovers val256(r_norm)/2^s = val256(r_un), i.e. the un-normalized
  remainder as a Nat value.

  Builds on:
  - BitVec.add_eq_or_of_and_eq_zero (disjoint OR = ADD)
  - BitVec.toNat_add_of_and_eq_zero
  - Existing `halfword_combine` proof pattern in Div128Lemmas.lean.
-/

import EvmAsm.Evm64.EvmWordArith.MultiLimb

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- Single-pair funnel-shift: (x >>> s) ||| (y <<< (64 - s))
-- ============================================================================

/-- Disjointness of the two halves of a funnel-shift: the bit positions of
    `x >>> s` (bits 0..63-s) and `y <<< (64 - s)` (bits 64-s..63) do not
    overlap when `0 < s < 64`. -/
theorem denorm_pair_and_eq_zero {s : Nat} (hs0 : 0 < s) (hs : s < 64) (x y : Word) :
    (x >>> s) &&& (y <<< (64 - s)) = 0 := by
  ext i
  simp only [BitVec.getElem_and, BitVec.getElem_ushiftRight,
             BitVec.getElem_shiftLeft]
  by_cases hi : (i : Nat) < 64 - s
  · simp [hi]
  · rw [show x.getLsbD (s + i) = false from by apply BitVec.getLsbD_of_ge; omega]
    simp

/-- Funnel-shift-right at Nat level: combining the high `(64 - s)` bits of `x`
    (shifted down) with the low `s` bits of `y` (shifted up) packs into a
    64-bit word whose Nat value is `x / 2^s + (y % 2^s) * 2^(64 - s)`. -/
theorem denorm_pair_toNat {s : Nat} (hs0 : 0 < s) (hs : s < 64) (x y : Word) :
    ((x >>> s) ||| (y <<< (64 - s))).toNat =
    x.toNat / 2^s + (y.toNat % 2^s) * 2^(64 - s) := by
  have hdisj := denorm_pair_and_eq_zero hs0 hs x y
  rw [(BitVec.add_eq_or_of_and_eq_zero (x >>> s) (y <<< (64 - s)) hdisj).symm,
      BitVec.toNat_add_of_and_eq_zero hdisj,
      BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      Nat.shiftRight_eq_div_pow]
  simp only [Nat.shiftLeft_eq]
  -- Goal: x.toNat / 2^s + y.toNat * 2^(64 - s) % 2^64
  --     = x.toNat / 2^s + y.toNat % 2^s * 2^(64 - s)
  congr 1
  -- y.toNat * 2^(64-s) % 2^64 = (y.toNat % 2^s) * 2^(64-s)
  have hpow : (2 : Nat) ^ 64 = 2 ^ s * 2 ^ (64 - s) := by
    rw [← pow_add, show s + (64 - s) = 64 from by omega]
  rw [hpow, Nat.mul_comm (2 ^ s) (2 ^ (64 - s)),
      Nat.mul_comm y.toNat (2 ^ (64 - s)),
      Nat.mul_mod_mul_left, Nat.mul_comm (2 ^ (64 - s))]

-- ============================================================================
-- 256-bit denormalization: val256(denorm) = val256(r) / 2^s
-- ============================================================================

/-- Denormalization round-trip at 256-bit level: applying the funnel-shift-right
    pattern to four limbs produces a Nat value equal to `val256(r) / 2^s`.
    This is the core val256-level equivalence between the normalized mulsub
    remainder (after algorithm D's denormalization epilogue) and the original
    un-normalized remainder value. -/
theorem val256_denormalize {s : Nat} (hs0 : 0 < s) (hs : s < 64)
    (r0 r1 r2 r3 : Word) :
    val256 ((r0 >>> s) ||| (r1 <<< (64 - s)))
           ((r1 >>> s) ||| (r2 <<< (64 - s)))
           ((r2 >>> s) ||| (r3 <<< (64 - s)))
           (r3 >>> s)
      = val256 r0 r1 r2 r3 / 2^s := by
  unfold val256
  rw [denorm_pair_toNat hs0 hs, denorm_pair_toNat hs0 hs, denorm_pair_toNat hs0 hs,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hspos : 0 < 2 ^ s := Nat.pos_of_ne_zero (by positivity)
  have hpow64 : (2 : Nat) ^ (64 - s) * 2 ^ s = 2 ^ 64 := by
    rw [← pow_add, show (64 - s) + s = 64 from by omega]
  have hr0_lt : r0.toNat % 2 ^ s < 2 ^ s := Nat.mod_lt _ hspos
  -- Abstract the Nat-subtraction power as a fresh variable so `ring` doesn't
  -- have to see through Nat subtraction; the only relation we need is
  -- `t * 2^s = 2^64`, expressible at ring level.
  -- Introduce abbreviations for r_k's mod and div components.
  set mod1 := r1.toNat % 2 ^ s
  set div1 := r1.toNat / 2 ^ s
  set mod2 := r2.toNat % 2 ^ s
  set div2 := r2.toNat / 2 ^ s
  set mod3 := r3.toNat % 2 ^ s
  set div3 := r3.toNat / 2 ^ s
  set mod0 := r0.toNat % 2 ^ s
  set div0 := r0.toNat / 2 ^ s
  have hr0 : mod0 + div0 * 2 ^ s = r0.toNat := by
    show r0.toNat % 2 ^ s + r0.toNat / 2 ^ s * 2 ^ s = r0.toNat
    rw [Nat.mul_comm]; exact Nat.mod_add_div _ _
  have hr1 : mod1 + div1 * 2 ^ s = r1.toNat := by
    show r1.toNat % 2 ^ s + r1.toNat / 2 ^ s * 2 ^ s = r1.toNat
    rw [Nat.mul_comm]; exact Nat.mod_add_div _ _
  have hr2 : mod2 + div2 * 2 ^ s = r2.toNat := by
    show r2.toNat % 2 ^ s + r2.toNat / 2 ^ s * 2 ^ s = r2.toNat
    rw [Nat.mul_comm]; exact Nat.mod_add_div _ _
  have hr3 : mod3 + div3 * 2 ^ s = r3.toNat := by
    show r3.toNat % 2 ^ s + r3.toNat / 2 ^ s * 2 ^ s = r3.toNat
    rw [Nat.mul_comm]; exact Nat.mod_add_div _ _
  set t := (2 : Nat) ^ (64 - s) with ht_def
  have ht : t * 2 ^ s = 2 ^ 64 := hpow64
  -- Current LHS (goal RHS before division step):
  --   div0 + mod1 * t + (div1 + mod2 * t) * 2^64
  --        + (div2 + mod3 * t) * 2^128 + div3 * 2^192
  -- Show this equals val256 / 2^s.
  set L : Nat :=
    div0 + mod1 * t + (div1 + mod2 * t) * 2 ^ 64 +
      (div2 + mod3 * t) * 2 ^ 128 + div3 * 2 ^ 192 with hL_def
  set V : Nat :=
    r0.toNat + r1.toNat * 2 ^ 64 + r2.toNat * 2 ^ 128 + r3.toNat * 2 ^ 192 with hV_def
  -- Key identity: V = L * 2^s + mod0, with mod0 < 2^s.
  have hkey : V = L * 2 ^ s + mod0 := by
    rw [hV_def, hL_def, ← hr0, ← hr1, ← hr2, ← hr3,
        show (2 : Nat) ^ 64 = t * 2 ^ s from ht.symm,
        show (2 : Nat) ^ 128 = t * 2 ^ s * (t * 2 ^ s) from by rw [ht]; decide,
        show (2 : Nat) ^ 192 = t * 2 ^ s * (t * 2 ^ s) * (t * 2 ^ s) from by rw [ht]; decide]
    ring
  -- Divide out 2^s.
  rw [hkey, show L * 2 ^ s + mod0 = mod0 + L * 2 ^ s from by ring,
      Nat.add_mul_div_right _ _ hspos, Nat.div_eq_of_lt hr0_lt]
  omega

end EvmWord

end EvmAsm.Evm64
