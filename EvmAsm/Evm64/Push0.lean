/-
  EvmAsm.Evm64.Push0

  256-bit EVM PUSH0: push 0 onto stack, sp -= 32.
  5 instructions (ADDI + 4 × SD x0).
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Program definition
-- ============================================================================

def evm_push0 : Program :=
  ADDI .x12 .x12 (-32) ;;
  SD .x12 .x0 0 ;; SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

-- ============================================================================
-- CodeReq
-- ============================================================================

abbrev evm_push0_code (base : Addr) : CodeReq :=
  CodeReq.ofProg base evm_push0

-- ============================================================================
-- PUSH0 spec
-- ============================================================================

set_option maxHeartbeats 6400000 in
/-- PUSH0: writes 4 zero limbs at nsp, moves SP backward by 32.
    5 instructions = 20 bytes. nsp is the NEW stack pointer (after decrement). -/
theorem evm_push0_spec (nsp base : Addr)
    (d0 d1 d2 d3 : Word)
    (hvalid : ValidMemRange nsp 4) :
    let code := evm_push0_code base
    cpsTriple base (base + 20) code
      ((.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3))
      ((.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0)) := by
  have LADDI := addi_spec_gen_same .x12 (nsp + 32) (-32) base (by nofun)
  simp only [signExtend12_neg32] at LADDI
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at LADDI
  have L0 := sd_x0_spec_gen .x12 nsp d0 0 (base + 4) (by validMem)
  have L1 := sd_x0_spec_gen .x12 nsp d1 8 (base + 8) (by validMem)
  have L2 := sd_x0_spec_gen .x12 nsp d2 16 (base + 12) (by validMem)
  have L3 := sd_x0_spec_gen .x12 nsp d3 24 (base + 16) (by validMem)
  runBlock LADDI L0 L1 L2 L3

/-- PUSH0 stack spec: pushes EvmWord 0 onto stack. -/
theorem evm_push0_stack_spec (nsp base : Addr)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord)
    (hvalid : ValidMemRange nsp 4) :
    let code := evm_push0_code base
    cpsTriple base (base + 20) code
      ((.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       evmStackIs (nsp + 32) rest)
      ((.x12 ↦ᵣ nsp) ** evmWordIs nsp 0 ** evmStackIs (nsp + 32) rest) :=
  cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by simp only [evmWordIs, EvmWord.getLimb_zero]; xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ _
      (evmStackIs (nsp + 32) rest)
      (by exact pcFree_evmStackIs (nsp + 32) rest)
      (evm_push0_spec nsp base d0 d1 d2 d3 hvalid))

end EvmAsm.Rv64
