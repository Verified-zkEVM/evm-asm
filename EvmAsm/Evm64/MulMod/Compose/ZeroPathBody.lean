/-
  EvmAsm.Evm64.MulMod.Compose.ZeroPathBody

  Compose the N = 0 path tail `reduce_zero_path ;; epilogue` into a single
  `cpsTripleWithin` over `evm_mulmod_program_code` (`base + 32` → `base + 52`).
  When the modulus is zero the EVM `MULMOD` result is `0`: this body zeroes the
  four result limbs (`sp + 64 .. sp + 88`) and advances `x12` to the result base
  `sp + 64`. The epilogue spec is framed with the (now zeroed) result window,
  which it does not touch, so its precondition matches the zero-path output.
-/

import EvmAsm.Evm64.MulMod.Compose.Base

namespace EvmAsm.Evm64.MulMod.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64

/-- N = 0 path body: zero the result window and advance `x12` to `sp + 64`. -/
theorem evm_mulmod_zero_path_body_evm_mulmod_spec_within
    (sp m0 m1 m2 m3 base : Word) :
    cpsTripleWithin (4 + 1) (base + 32) ((base + 48) + 4) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ m3))
      ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ (0 : Word))) := by
  have h1 := evm_mulmod_reduce_zero_path_evm_mulmod_spec_within sp m0 m1 m2 m3 base
  have hmid : (base + 32) + 16 = base + 48 := by rw [BitVec.add_assoc]; congr 1
  rw [hmid] at h1
  have h2 := cpsTripleWithin_frameR
    (((sp + signExtend12 (64 : BitVec 12)) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ (0 : Word)))
    (by pcFree)
    (evm_mulmod_epilogue_evm_mulmod_spec_within sp base)
  exact cpsTripleWithin_seq_same_cr h1 h2

end EvmAsm.Evm64.MulMod.Compose
