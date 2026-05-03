/-
  EvmAsm.Evm64.EvmWordArith.Exp

  Pure EVM EXP semantics over 256-bit words. This is the semantic target for
  the executable EXP opcode proof: exponentiation in Nat, reduced modulo 2^256.
-/

import EvmAsm.Evm64.EvmWordArith.Common

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
  native_decide

/-- Any base raised to the zero EVM word is one. -/
theorem exp_zero_right (base : EvmWord) : exp base 0 = 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  simp

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
    by_contra hnot
    have hz : exponent.toNat = 0 := by omega
    apply h
    apply BitVec.eq_of_toNat_eq
    simp [hz]
  simp [Nat.zero_pow hpos]

/-- Any base raised to the EVM word one is itself. -/
theorem exp_one_right (base : EvmWord) : exp base 1 = base := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  simp [Nat.mod_eq_of_lt base.isLt]

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

/-- The GH #92 boundary case `EXP(2, 256)` wraps to zero modulo `2^256`. -/
theorem exp_two_256 : exp (2 : EvmWord) (256 : EvmWord) = 0 := by
  native_decide

-- Edge checks required by GH #92's EXP acceptance notes.
example : exp (0 : EvmWord) (0 : EvmWord) = 1 := by
  native_decide

example : exp (2 : EvmWord) (256 : EvmWord) = 0 := by
  exact exp_two_256

end EvmWord

end EvmAsm.Evm64
