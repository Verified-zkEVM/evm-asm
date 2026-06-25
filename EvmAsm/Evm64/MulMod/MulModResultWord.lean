/-
  EvmAsm.Evm64.MulMod.MulModResultWord

  Bridging lemmas between the EVM `MULMOD` reference word `EvmWord.mulmod`
  and the concrete result words produced by the two dispatch arms of the
  assembled `evm_mulmod` program. The reducer (N ≠ 0 arm) leaves
  `BitVec.ofNat 256 ((a·b) mod n)`; the zero path (N = 0 arm) leaves `0`.
  These align both arms to a single `EvmWord.mulmod a b n` result word, the
  unified postcondition the top-level dispatch merge converges on.
-/

import EvmAsm.Evm64.EvmWordArith.MulMod

namespace EvmAsm.Evm64

namespace EvmWord

/-- The `N = 0` arm: `MULMOD` returns the zero word. -/
@[simp] theorem mulmod_zero (a b : EvmWord) : EvmWord.mulmod a b 0 = 0 := by
  simp [EvmWord.mulmod]

/-- The `N ≠ 0` arm: `MULMOD` is the reduced product word `(a·b) mod N`. -/
theorem mulmod_of_ne_zero (a b n : EvmWord) (h : n ≠ 0) :
    EvmWord.mulmod a b n = BitVec.ofNat 256 (a.toNat * b.toNat % n.toNat) := by
  unfold EvmWord.mulmod
  rw [if_neg h]

end EvmWord

end EvmAsm.Evm64
