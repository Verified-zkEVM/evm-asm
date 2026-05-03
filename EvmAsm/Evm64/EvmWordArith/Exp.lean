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

/-- Any base raised to the EVM word one is itself. -/
theorem exp_one_right (base : EvmWord) : exp base 1 = base := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  simp [Nat.mod_eq_of_lt base.isLt]

-- Edge checks required by GH #92's EXP acceptance notes.
example : exp (0 : EvmWord) (0 : EvmWord) = 1 := by
  native_decide

example : exp (2 : EvmWord) (256 : EvmWord) = 0 := by
  native_decide

end EvmWord

end EvmAsm.Evm64
