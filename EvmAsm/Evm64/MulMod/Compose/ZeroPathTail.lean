/-
  EvmAsm.Evm64.MulMod.Compose.ZeroPathTail

  The complete N = 0 path from the zero-store through the skip jump:
  `reduce_zero_path ;; epilogue ;; zero_path_skip_nonzero`, composed over
  `evm_mulmod_program_code` (`base + 32` → `base + 2160`, the program exit). The
  zero-path body (`ZeroPathBody`) zeroes the result window and advances `x12`;
  the final `JAL` (`zero_path_skip_nonzero`) jumps over the N ≠ 0 path to the
  program exit while owning nothing, so it is framed with the (untouched)
  result window. This is the `h_f` continuation of the top-level dispatch merge.
-/

import EvmAsm.Evm64.MulMod.Compose.ZeroPathBody

namespace EvmAsm.Evm64.MulMod.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64

/-- Full N = 0 path: zero the result window, advance `x12`, and jump to the
    program exit. -/
theorem evm_mulmod_zero_path_tail_evm_mulmod_spec_within
    (sp m0 m1 m2 m3 base : Word) :
    cpsTripleWithin (4 + 1 + 1) (base + 32) ((base + 52) + signExtend21 (2108 : BitVec 21))
      (evm_mulmod_program_code base)
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
  have h1 := evm_mulmod_zero_path_body_evm_mulmod_spec_within sp m0 m1 m2 m3 base
  have hc1exit : (base + 48) + 4 = base + 52 := by rw [BitVec.add_assoc]; congr 1
  rw [hc1exit] at h1
  have h2 := cpsTripleWithin_frameL
    ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
     ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ (0 : Word)))
    (by pcFree)
    (evm_mulmod_zero_path_skip_nonzero_evm_mulmod_spec_within base)
  rw [sepConj_emp_right'] at h2
  exact cpsTripleWithin_seq_same_cr h1 h2

end EvmAsm.Evm64.MulMod.Compose
