/-
  EvmAsm.Evm64.Pop.Spec

  256-bit EVM POP specs.
-/

import EvmAsm.Evm64.Pop.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

/-- POP: advances stack pointer by 32 bytes (discards top 256-bit element).
    1 instruction = 4 bytes. -/
theorem evm_pop_spec (sp base : Word) :
    cpsTriple base (base + 4) (evm_pop_code base)
      (.x12 ↦ᵣ sp)
      (.x12 ↦ᵣ (sp + 32)) := by
  have h := addi_spec_gen_same .x12 sp 32 base (by nofun)
  simp only [signExtend12_32] at h
  runBlock h

/-- POP stack spec: discards top element, rest untouched. -/
theorem evm_pop_stack_spec (sp base : Word)
    (a : EvmWord) (rest : List EvmWord) :
    cpsTriple base (base + 4) (evm_pop_code base)
      ((.x12 ↦ᵣ sp) ** evmWordIs sp a ** evmStackIs (sp + 32) rest)
      ((.x12 ↦ᵣ (sp + 32)) ** evmWordIs sp a ** evmStackIs (sp + 32) rest) :=
  cpsTriple_frame_left _ _ _ _ _
    (evmWordIs sp a ** evmStackIs (sp + 32) rest)
    (pcFree_sepConj (pcFree_evmWordIs sp a) (pcFree_evmStackIs (sp + 32) rest))
    (evm_pop_spec sp base)

end EvmAsm.Rv64
