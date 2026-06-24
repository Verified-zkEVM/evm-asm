import EvmAsm.Evm64.MulMod.Compose.Base

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

end EvmAsm.Evm64.MulMod.Compose
