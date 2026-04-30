/-
  EvmAsm.Evm64.Push0.Spec

  256-bit EVM PUSH0 specs.
-/

import EvmAsm.Evm64.Push0.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- PUSH0: writes 4 zero limbs at nsp, moves SP backward by 32.
    5 instructions = 20 bytes. nsp is the NEW stack pointer (after decrement). -/
theorem evm_push0_spec_within (nsp base : Word)
    (d0 d1 d2 d3 : Word) :
    let code := evm_push0_code base
    cpsTripleWithin 5 base (base + 20) code
      ((.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3))
      ((.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0)) := by
  have LADDI := addi_spec_gen_same_within .x12 (nsp + 32) (-32) base (by nofun)
  simp only [signExtend12_neg32] at LADDI
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at LADDI
  have L0 := sd_x0_spec_gen_within .x12 nsp d0 0 (base + 4)
  have L1 := sd_x0_spec_gen_within .x12 nsp d1 8 (base + 8)
  have L2 := sd_x0_spec_gen_within .x12 nsp d2 16 (base + 12)
  have L3 := sd_x0_spec_gen_within .x12 nsp d3 24 (base + 16)
  runBlock LADDI L0 L1 L2 L3


/-- PUSH0 stack spec: pushes EvmWord 0 onto stack. -/
theorem evm_push0_stack_spec_within (nsp base : Word)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord) :
    let code := evm_push0_code base
    cpsTripleWithin 5 base (base + 20) code
      ((.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       evmStackIs (nsp + 32) rest)
      ((.x12 ↦ᵣ nsp) ** evmWordIs nsp 0 ** evmStackIs (nsp + 32) rest) :=
  cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by simp only [evmWordIs, EvmWord.getLimbN_zero]; xperm_hyp hq)
    (cpsTripleWithin_frameR
      (evmStackIs (nsp + 32) rest)
      pcFree_evmStackIs
      (evm_push0_spec_within nsp base d0 d1 d2 d3))


end EvmAsm.Evm64
