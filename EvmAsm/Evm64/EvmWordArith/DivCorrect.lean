/-
  EvmAsm.Evm64.EvmWordArith.DivCorrect

  Public EvmWord-level correctness surface for DIV/MOD.
-/

module

public import EvmAsm.Evm64.EvmWordArith.Div

@[expose] public section

namespace EvmAsm.Evm64

namespace EvmWord

/-- EVM DIV agrees with unsigned natural-number division, with EVM's
    zero-divisor result of zero. -/
theorem div_correct (a b : EvmWord) :
    (EvmWord.div a b).toNat = if b = 0 then 0 else a.toNat / b.toNat := by
  by_cases h : b = 0
  · rw [h, div_zero_right]
    simp
  · unfold EvmWord.div
    rw [if_neg h, if_neg h]
    exact BitVec.toNat_udiv

/-- EVM MOD agrees with unsigned natural-number modulus, with EVM's
    zero-divisor result of zero. -/
theorem mod_correct (a b : EvmWord) :
    (EvmWord.mod a b).toNat = if b = 0 then 0 else a.toNat % b.toNat := by
  by_cases h : b = 0
  · rw [h, mod_zero_right]
    simp
  · unfold EvmWord.mod
    rw [if_neg h, if_neg h]
    exact BitVec.toNat_umod

end EvmWord

end EvmAsm.Evm64
