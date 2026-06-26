import EvmAsm.Evm64.MulMod.Compose.Base
import EvmAsm.Evm64.MulMod.ReduceOuterInduction

namespace EvmAsm.Evm64.MulMod.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

local macro "evm_mulmod_reduce512_slice_rfl" : tactic =>
  `(tactic|
    first
      | rfl
      | (unfold evm_mulmod evm_mulmod_reduce512
            evm_mulmod_nonzero_or_zero_prefix evm_mulmod_reduce_zero_path
            evm_mulmod_epilogue evm_mulmod_zero_path_skip_nonzero
            evm_mulmod_product_layout evm_mulmod_reduce512_init
            evm_mulmod_reduce512_loop evm_mulmod_reduce512_write_result
            LD OR' BNE SD ADDI JAL MUL MULHU ADD SLTU single seq
         rfl))

/-- The full reducer block at offset 1816 is subsumed by the top-level
    `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_reduce512_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1816) evm_mulmod_reduce512) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1816) evm_mulmod
    evm_mulmod_reduce512 454 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_reduce512_slice_rfl
  · rw [evm_mulmod_length, evm_mulmod_reduce512_length]
  · rw [evm_mulmod_length]; decide

/-- The whole 512-bit reducer spec lifted onto the full program code
    `evm_mulmod_program_code` at offset 1816. -/
theorem evm_mulmod_reduce512_evm_mulmod_spec_within
    (sp base : Word) (v16Old v18Old r0 r1 r2 r3 : Word) (n : EvmWord) (limbs : Nat → Word) :
    cpsTripleWithin (6 + (2 + 66 * 64 + 2 + 1) * 8 + 8 + 1) (base + 1816) ((base + 1816) + 344)
      (evm_mulmod_program_code base)
      (((.x12 ↦ᵣ sp) ** (.x16 ↦ᵣ v16Old) ** (.x18 ↦ᵣ v18Old) ** (.x0 ↦ᵣ 0) **
        ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3)) **
       ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10 ** regOwn .x11 **
         regOwn .x13 ** regOwn .x17 ** regOwn .x15 ** regOwn .x19 ** regOwn .x20 **
         ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
         ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
         ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
         ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)) **
        limbChain (sp + signExtend12 (3992 : BitVec 12)) limbs 8))
      ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
       (((.x5 ↦ᵣ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 3) **
         ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 0) **
         ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 1) **
         ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 2) **
         ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 3) **
         ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 0) **
         ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 1) **
         ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 2) **
         ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN (mulModReduceOuterFoldCarry n limbs (0 : EvmWord) 8) 3)) **
        (((.x15 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
          regOwn .x17 ** regOwn .x19 ** regOwn .x20 ** regOwn .x16 ** regOwn .x18) **
         limbChain (sp + signExtend12 (3992 : BitVec 12)) limbs 8))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_reduce512_spec_within sp (base + 1816)
      v16Old v18Old r0 r1 r2 r3 n limbs)
    (hmono := evm_mulmod_program_code_reduce512_sub base)

end EvmAsm.Evm64.MulMod.Compose
