/-
  EvmAsm.Evm64.EvmWordArith.Exp

  Pure EVM EXP semantics over 256-bit words. This is the semantic target for
  the executable EXP opcode proof: exponentiation in Nat, reduced modulo 2^256.
-/

import EvmAsm.Evm64.Basic

namespace EvmAsm.Evm64

namespace EvmWord

/-- EVM EXP semantics: `base ^ exponent`, reduced modulo `2^256`. -/
def exp (base exponent : EvmWord) : EvmWord :=
  BitVec.ofNat 256 (base.toNat ^ exponent.toNat)

/-- `EvmWord.exp` is Nat exponentiation modulo the 256-bit word modulus. -/
theorem exp_correct (base exponent : EvmWord) :
    (exp base exponent).toNat = base.toNat ^ exponent.toNat % 2^256 := by
  simp [exp, BitVec.toNat_ofNat]

/-- EVM's `0^0` case follows Nat exponentiation and returns one. -/
theorem exp_zero_zero : exp 0 0 = 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  decide

/-- Any base raised to the zero EVM word is one. -/
theorem exp_zero_right (base : EvmWord) : exp base 0 = 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  simp

/-- The maximum EVM word raised to zero is one. -/
theorem exp_max_zero_right : exp (-1 : EvmWord) 0 = 1 := by
  exact exp_zero_right (-1 : EvmWord)

/-- One raised to any exponent remains one. -/
theorem exp_one_left (exponent : EvmWord) : exp 1 exponent = 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  simp

/-- Zero raised to any nonzero EVM exponent remains zero. -/
theorem exp_zero_left_of_ne_zero (exponent : EvmWord) (h : exponent ≠ 0) :
    exp 0 exponent = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  have hpos : 0 < exponent.toNat := by
    rcases Nat.eq_zero_or_pos exponent.toNat with hz | hp
    · exact absurd (BitVec.eq_of_toNat_eq (by simp [hz])) h
    · exact hp
  simp [Nat.zero_pow hpos]

/-- Zero raised to an exponent with positive Nat value remains zero. -/
theorem exp_zero_left_of_toNat_pos (exponent : EvmWord)
    (h_pos : 0 < exponent.toNat) :
    exp 0 exponent = 0 := by
  exact exp_zero_left_of_ne_zero exponent (by
    intro h_zero
    rw [h_zero] at h_pos
    simp at h_pos)

/-- Zero raised to one remains zero. -/
theorem exp_zero_one : exp (0 : EvmWord) 1 = 0 := by
  exact exp_zero_left_of_ne_zero 1 (by decide)

/-- Zero raised to the maximum EVM word exponent remains zero. -/
theorem exp_zero_left_max : exp 0 (-1 : EvmWord) = 0 := by
  exact exp_zero_left_of_ne_zero (-1 : EvmWord) (by decide)

/-- Any base raised to the EVM word one is itself. -/
theorem exp_one_right (base : EvmWord) : exp base 1 = base := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  simp [Nat.mod_eq_of_lt base.isLt]

/-- The maximum EVM word raised to one remains the maximum EVM word. -/
theorem exp_max_one_right : exp (-1 : EvmWord) 1 = (-1 : EvmWord) := by
  exact exp_one_right (-1 : EvmWord)

/-- Two raised to one remains two. -/
theorem exp_two_one : exp (2 : EvmWord) 1 = 2 := by
  exact exp_one_right (2 : EvmWord)

/-- Successor recurrence for EXP when the exponent increment does not wrap. -/
theorem exp_succ_right_of_toNat_lt (base exponent : EvmWord)
    (h : exponent.toNat + 1 < 2^256) :
    exp base (exponent + 1) = base * exp base exponent := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  have hSucc : (exponent + 1).toNat = exponent.toNat + 1 := by
    rw [BitVec.toNat_add]
    have h1 : (1 : EvmWord).toNat = 1 := by decide
    rw [h1]
    exact Nat.mod_eq_of_lt h
  rw [hSucc]
  rw [BitVec.toNat_mul]
  rw [exp_correct]
  rw [Nat.pow_succ]
  rw [Nat.mul_comm (base.toNat ^ exponent.toNat) base.toNat]
  rw [Nat.mul_mod]
  rw [Nat.mod_eq_of_lt base.isLt]

/-- Squaring recurrence for EXP when the next exponent is twice the previous
    exponent. -/
theorem exp_double_right_of_toNat_eq (base exponent nextExponent : EvmWord)
    (hNext : nextExponent.toNat = 2 * exponent.toNat) :
    exp base nextExponent = exp base exponent * exp base exponent := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct, BitVec.toNat_mul, exp_correct, hNext]
  rw [show base.toNat ^ (2 * exponent.toNat) =
      base.toNat ^ exponent.toNat * base.toNat ^ exponent.toNat by
    rw [show 2 * exponent.toNat = exponent.toNat + exponent.toNat by omega]
    rw [Nat.pow_add]]
  rw [← Nat.mul_mod]

/-- Square-and-multiply recurrence for EXP when the next exponent is twice the
    previous exponent plus one. -/
theorem exp_double_add_one_right_of_toNat_eq
    (base exponent nextExponent : EvmWord)
    (hNext : nextExponent.toNat = 2 * exponent.toNat + 1) :
    exp base nextExponent = base * (exp base exponent * exp base exponent) := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct, BitVec.toNat_mul, BitVec.toNat_mul, exp_correct, hNext]
  rw [show base.toNat ^ (2 * exponent.toNat + 1) =
      base.toNat * (base.toNat ^ exponent.toNat * base.toNat ^ exponent.toNat) by
    rw [show 2 * exponent.toNat + 1 =
        (exponent.toNat + exponent.toNat) + 1 by omega]
    rw [Nat.pow_succ, Nat.pow_add]
    rw [Nat.mul_comm
      (base.toNat ^ exponent.toNat * base.toNat ^ exponent.toNat) base.toNat]]
  rw [← Nat.mul_mod
    (base.toNat ^ exponent.toNat) (base.toNat ^ exponent.toNat) (2^256)]
  rw [Nat.mul_mod
    (base.toNat) (base.toNat ^ exponent.toNat * base.toNat ^ exponent.toNat)
    (2^256)]
  rw [Nat.mul_mod
    (base.toNat)
    ((base.toNat ^ exponent.toNat * base.toNat ^ exponent.toNat) % 2^256)
    (2^256)]
  rw [Nat.mod_mod]

/-- One MSB-first square-and-multiply step on the accumulator: square, then
    multiply by `base` when the current exponent bit is set. This is the pure
    per-iteration accumulator update performed by the EXP loop body. -/
def expSqMulStep (base acc : EvmWord) (bit : Bool) : EvmWord :=
  if bit then base * (acc * acc) else acc * acc

/-- Accumulator invariant preservation for one square-and-multiply step.

    If the accumulator currently equals `exp base e` (the running power for the
    processed exponent prefix `e`), then after one MSB-first step consuming
    `bit` it equals `exp base e'`, where `e'` is the extended prefix
    `e' = 2*e + bit`.  This is the per-iteration semantic bridge the EXP loop
    body realizes; it unifies `exp_double_right_of_toNat_eq` (bit = 0) and
    `exp_double_add_one_right_of_toNat_eq` (bit = 1). -/
theorem expSqMulStep_correct (base e e' : EvmWord) (bit : Bool)
    (hNext : e'.toNat = 2 * e.toNat + (if bit then 1 else 0)) :
    expSqMulStep base (exp base e) bit = exp base e' := by
  unfold expSqMulStep
  cases bit with
  | false =>
    show exp base e * exp base e = exp base e'
    have hNext' : e'.toNat = 2 * e.toNat := by simpa using hNext
    exact (exp_double_right_of_toNat_eq base e e' hNext').symm
  | true =>
    show base * (exp base e * exp base e) = exp base e'
    have hNext' : e'.toNat = 2 * e.toNat + 1 := by simpa using hNext
    exact (exp_double_add_one_right_of_toNat_eq base e e' hNext').symm

/-- The square-and-multiply step from the unit accumulator (`exp base 0 = 1`)
    yields `base^bit`: the first MSB-first iteration's accumulator value. -/
theorem expSqMulStep_one (base e' : EvmWord) (bit : Bool)
    (hNext : e'.toNat = (if bit then 1 else 0)) :
    expSqMulStep base (1 : EvmWord) bit = exp base e' := by
  have h1 : (1 : EvmWord) = exp base (0 : EvmWord) := (exp_zero_right base).symm
  rw [h1]
  exact expSqMulStep_correct base 0 e' bit (by simpa using hNext)

/-- The GH #92 cross-limb boundary case `EXP(2, 64)`. -/
theorem exp_two_64 : exp (2 : EvmWord) (64 : EvmWord) =
    BitVec.ofNat 256 (2^64) := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  decide

/-- The GH #92 mid-word boundary case `EXP(2, 128)`. -/
theorem exp_two_128 : exp (2 : EvmWord) (128 : EvmWord) =
    BitVec.ofNat 256 (2^128) := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  decide

/-- The GH #92 pre-wrap boundary case `EXP(2, 255)` is the high bit. -/
theorem exp_two_255 : exp (2 : EvmWord) (255 : EvmWord) =
    BitVec.ofNat 256 (2^255) := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  decide

/-- The GH #92 boundary case `EXP(2, 256)` wraps to zero modulo `2^256`. -/
theorem exp_two_256 : exp (2 : EvmWord) (256 : EvmWord) = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  decide

-- Edge checks required by GH #92's EXP acceptance notes.
example : exp (0 : EvmWord) (0 : EvmWord) = 1 := by
  exact exp_zero_zero

example : exp (2 : EvmWord) (256 : EvmWord) = 0 := by
  exact exp_two_256

end EvmWord

end EvmAsm.Evm64
