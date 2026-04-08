/-
  EvmAsm.Evm64.EvmWordArith.Div

  EVM DIV/MOD semantics: word-level definitions and getLimb lemmas for zero case.
  Bridge lemmas connecting the RISC-V limb-level computation to EvmWord.div/mod.
-/

import EvmAsm.Evm64.EvmWordArith.Common

namespace EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- EVM DIV/MOD semantics
-- ============================================================================

/-- EVM DIV semantics: unsigned integer division, returning 0 when divisor is 0. -/
def div (a b : EvmWord) : EvmWord :=
  if b = 0 then 0 else BitVec.udiv a b

/-- EVM MOD semantics: unsigned modulus, returning 0 when divisor is 0. -/
def mod (a b : EvmWord) : EvmWord :=
  if b = 0 then 0 else BitVec.umod a b

-- ============================================================================
-- Zero divisor lemmas
-- ============================================================================

theorem div_zero_right (a : EvmWord) : div a 0 = 0 := by
  simp [div]

theorem mod_zero_right (a : EvmWord) : mod a 0 = 0 := by
  simp [mod]

private theorem getLimb_zero (i : Fin 4) : (0 : EvmWord).getLimb i = 0 := by
  simp [getLimb]

theorem div_getLimb_zero_right (a : EvmWord) (i : Fin 4) :
    (div a 0).getLimb i = 0 := by
  rw [div_zero_right]; exact getLimb_zero i

theorem mod_getLimb_zero_right (a : EvmWord) (i : Fin 4) :
    (mod a 0).getLimb i = 0 := by
  rw [mod_zero_right]; exact getLimb_zero i

-- ============================================================================
-- b = 0 ↔ all limbs OR to zero (bridge for program specs)
-- ============================================================================

/-- b0 ||| b1 ||| b2 ||| b3 = 0 implies all individual limbs are zero. -/
theorem limbs_or_eq_zero_imp (b0 b1 b2 b3 : Word) (h : b0 ||| b1 ||| b2 ||| b3 = 0) :
    b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 := by
  -- h : ((b0 ||| b1) ||| b2) ||| b3 = 0 (left-associated)
  have ⟨h012, h3⟩ := bv_or_eq_zero h
  have ⟨h01, h2⟩ := bv_or_eq_zero h012
  have ⟨h0, h1⟩ := bv_or_eq_zero h01
  exact ⟨h0, h1, h2, h3⟩

/-- A 256-bit word is zero iff the OR of all its limbs is zero. -/
theorem eq_zero_iff_limbs_or (b : EvmWord) :
    b = 0 ↔ b.getLimb 0 ||| b.getLimb 1 ||| b.getLimb 2 ||| b.getLimb 3 = 0 := by
  constructor
  · intro h; subst h
    show (0 : EvmWord).getLimb 0 ||| (0 : EvmWord).getLimb 1 |||
         (0 : EvmWord).getLimb 2 ||| (0 : EvmWord).getLimb 3 = 0
    native_decide
  · intro h
    set b0 := b.getLimb 0 with hb0_def
    set b1 := b.getLimb 1 with hb1_def
    set b2 := b.getLimb 2 with hb2_def
    set b3 := b.getLimb 3 with hb3_def
    have ⟨h0, h1, h2, h3⟩ := limbs_or_eq_zero_imp b0 b1 b2 b3 h
    exact (eq_zero_iff_limbs b).mpr ⟨hb0_def ▸ h0, hb1_def ▸ h1, hb2_def ▸ h2, hb3_def ▸ h3⟩

-- ============================================================================
-- Division algebra: Euclidean property and uniqueness
-- ============================================================================

/-- BitVec Euclidean division property: `y * (x / y) + x % y = x`.
    Derived from `Nat.div_add_mod` via `toNat` conversion. -/
theorem bv_udiv_add_umod {n : Nat} (x y : BitVec n) :
    y * (x / y) + x % y = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_umod]
  have hdiv := Nat.div_add_mod x.toNat y.toNat
  have hx := x.isLt
  have hmul_le : y.toNat * (x.toNat / y.toNat) ≤ x.toNat := by omega
  rw [Nat.mod_eq_of_lt (by omega : y.toNat * (x.toNat / y.toNat) < 2 ^ n),
      hdiv, Nat.mod_eq_of_lt hx]

/-- Uniqueness of BitVec unsigned division: if `a = b * q + r` with `r < b`
    and no overflow in `b * q + r`, then `q = a / b` and `r = a % b`. -/
theorem bv_udiv_umod_unique {n : Nat} (a b q r : BitVec n)
    (hr : r < b)
    (hno : b.toNat * q.toNat + r.toNat < 2 ^ n)
    (h : a = b * q + r) :
    q = a / b ∧ r = a % b := by
  have hr_nat : r.toNat < b.toNat := BitVec.lt_def.mp hr
  have h_eq := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_mul] at h_eq
  rw [Nat.mod_eq_of_lt (by omega : b.toNat * q.toNat < 2 ^ n),
      Nat.mod_eq_of_lt hno] at h_eq
  have hq_eq : q.toNat = a.toNat / b.toNat := by
    apply Eq.symm; apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm]; omega
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm q.toNat b.toNat]; omega
  have hr_eq : r.toNat = a.toNat % b.toNat := by
    have := Nat.div_add_mod a.toNat b.toNat; rw [← hq_eq] at this; omega
  exact ⟨BitVec.eq_of_toNat_eq (hq_eq ▸ (BitVec.toNat_udiv).symm),
         BitVec.eq_of_toNat_eq (hr_eq ▸ (BitVec.toNat_umod).symm)⟩

-- ============================================================================
-- EvmWord-level division correctness framework
-- ============================================================================

/-- EvmWord Euclidean division property: `b * (div a b) + mod a b = a` when b ≠ 0. -/
theorem div_mod_add_eq (a b : EvmWord) (hbnz : b ≠ 0) :
    b * (div a b) + mod a b = a := by
  simp only [div, mod, if_neg hbnz]
  exact bv_udiv_add_umod a b

/-- EvmWord division uniqueness: if `a = b * q + r` with `r < b` and no overflow,
    then `q = div a b` and `r = mod a b`. -/
theorem div_mod_unique (a b q r : EvmWord) (hbnz : b ≠ 0)
    (hr : r < b)
    (hno : b.toNat * q.toNat + r.toNat < 2 ^ 256)
    (h : a = b * q + r) :
    q = div a b ∧ r = mod a b := by
  have ⟨hq, hrem⟩ := bv_udiv_umod_unique a b q r hr hno h
  constructor
  · rw [hq]; unfold div; rw [if_neg hbnz]; rfl
  · rw [hrem]; unfold mod; rw [if_neg hbnz]; rfl

/-- Key bridge theorem: if limb-level output satisfies the division property,
    then it equals EvmWord.div/mod.

    To complete the DIV/MOD stack specs, one must prove that the Knuth Algorithm D
    output (q0v..q3v, u0out..u3out) satisfies:
    - `fromLimbs a_limbs = fromLimbs b_limbs * fromLimbs q_limbs + fromLimbs r_limbs`
    - `fromLimbs r_limbs < fromLimbs b_limbs`
    - `(fromLimbs b_limbs).toNat * (fromLimbs q_limbs).toNat + (fromLimbs r_limbs).toNat < 2^256`
    Then this theorem gives `fromLimbs q_limbs = div a b`. -/
theorem div_eq_of_euclidean (a b : EvmWord) (q r : EvmWord) (hbnz : b ≠ 0)
    (h_eq : a = b * q + r) (h_rem_lt : r < b)
    (h_no_overflow : b.toNat * q.toNat + r.toNat < 2 ^ 256) :
    q = div a b :=
  (div_mod_unique a b q r hbnz h_rem_lt h_no_overflow h_eq).1

theorem mod_eq_of_euclidean (a b : EvmWord) (q r : EvmWord) (hbnz : b ≠ 0)
    (h_eq : a = b * q + r) (h_rem_lt : r < b)
    (h_no_overflow : b.toNat * q.toNat + r.toNat < 2 ^ 256) :
    r = mod a b :=
  (div_mod_unique a b q r hbnz h_rem_lt h_no_overflow h_eq).2

end EvmWord

end EvmAsm.Rv64
