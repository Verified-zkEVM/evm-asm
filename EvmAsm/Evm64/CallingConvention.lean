/-
  EvmAsm.Evm64.CallingConvention

  LP64-aligned calling convention for RISC-V RV64IM, adapted to the
  x0–x12 register subset used by this project.

  Register conventions (per zkvm-standards LP64):
    x0  (zero) — hardwired zero
    x1  (ra)   — return address (caller-saved)
    x2  (sp)   — call stack pointer, grows DOWN (callee-saved)
    x5  (t0)   — temporary (caller-saved)
    x6  (t1)   — temporary (caller-saved)
    x7  (t2)   — temporary (caller-saved)
    x10 (a0)   — argument 0 / return value 0 (caller-saved)
    x11 (a1)   — argument 1 / return value 1 (caller-saved)
    x12 (a2)   — argument 2 / EVM stack pointer (caller-saved)

  Call sequence:
    Caller:  JAL x1, offset  (near)  or  JALR x1, target, 0  (far)
    Leaf:    body ;; JALR x0, x1, 0
    Non-leaf: prologue ;; body ;; epilogue

  Prologue (16-byte frame): ADDI sp, sp, -16 ;; SD sp, ra, 8
  Epilogue:                 LD ra, sp, 8 ;; ADDI sp, sp, 16 ;; JALR x0, ra, 0
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Program snippets
-- ============================================================================

/-- Return from function: JALR x0, x1, 0 (jump to ra, discard write to x0). -/
def cc_ret : Program := JALR .x0 .x1 0

/-- Non-leaf prologue: allocate 16-byte stack frame, save ra.
    ADDI sp, sp, -16 ;; SD sp, ra, 8  (2 instructions, 8 bytes) -/
def cc_prologue : Program :=
  ADDI .x2 .x2 (-16) ;; SD .x2 .x1 8

/-- Non-leaf epilogue: restore ra, deallocate frame, return.
    LD ra, sp, 8 ;; ADDI sp, sp, 16 ;; JALR x0, ra, 0  (3 instructions, 12 bytes) -/
def cc_epilogue : Program :=
  LD .x1 .x2 8 ;; ADDI .x2 .x2 16 ;; cc_ret

-- CodeReq abbreviations
abbrev cc_ret_code (base : Word) : CodeReq := CodeReq.ofProg base cc_ret
abbrev cc_prologue_code (base : Word) : CodeReq := CodeReq.ofProg base cc_prologue
abbrev cc_epilogue_code (base : Word) : CodeReq := CodeReq.ofProg base cc_epilogue

-- ============================================================================
-- Call / return specs
-- ============================================================================

/-- Near call: JAL x1, offset.
    Saves PC+4 in ra (x1), jumps to PC + sext(offset). -/
theorem callNear_spec_within (offset : BitVec 21) (base : Word) (old_ra : Word) :
    cpsTripleWithin 1 base (base + signExtend21 offset)
      (CodeReq.singleton base (.JAL .x1 offset))
      (.x1 ↦ᵣ old_ra)
      (.x1 ↦ᵣ (base + 4)) :=
  jal_spec_within .x1 old_ra offset base (by nofun)

/-- Far call: JALR x1, target, 0.
    Saves PC+4 in ra (x1), jumps to target.
    target must differ from x1 (enforced by sep conj). -/
theorem callFar_spec_within (target : Reg) (v_target old_ra : Word) (base : Word) :
    cpsTripleWithin 1 base ((v_target + signExtend12 0) &&& ~~~1)
      (CodeReq.singleton base (.JALR .x1 target 0))
      ((target ↦ᵣ v_target) ** (.x1 ↦ᵣ old_ra))
      ((target ↦ᵣ v_target) ** (.x1 ↦ᵣ (base + 4))) :=
  jalr_spec_within .x1 target v_target old_ra 0 base (by nofun)

/-- Return: JALR x0, x1, 0.
    Jumps to (ra + 0) &&& ~1. Preserves ra in x1. -/
theorem ret_spec_within (base : Word) (ra_val : Word) :
    cpsTripleWithin 1 base ((ra_val + signExtend12 0) &&& ~~~1)
      (CodeReq.singleton base (.JALR .x0 .x1 0))
      (.x1 ↦ᵣ ra_val)
      (.x1 ↦ᵣ ra_val) :=
  jalr_x0_spec_gen_within .x1 ra_val 0 base

/-- Return with simplified exit: ra &&& ~1 (signExtend12 0 = 0 eliminated). -/
theorem ret_spec_within' (base : Word) (ra_val : Word) :
    cpsTripleWithin 1 base (ra_val &&& ~~~1)
      (CodeReq.singleton base (.JALR .x0 .x1 0))
      (.x1 ↦ᵣ ra_val)
      (.x1 ↦ᵣ ra_val) := by
  have h := ret_spec_within base ra_val
  simp only [signExtend12_0] at h
  rw [show ra_val + (0 : Word) = ra_val from by bv_omega] at h
  exact h

-- ============================================================================
-- Prologue spec
-- ============================================================================

/-- Non-leaf prologue: allocate 16-byte frame, save ra at sp-8.
    sp_val is the ORIGINAL sp on entry.
    After prologue: sp = sp_val - 16, ra saved at mem[sp_val - 8]. -/
theorem cc_prologue_spec_within (base sp_val ra_val old_slot : Word) :
    cpsTripleWithin 2 base (base + 8) (cc_prologue_code base)
      ((.x2 ↦ᵣ sp_val) ** (.x1 ↦ᵣ ra_val) ** ((sp_val - 8) ↦ₘ old_slot))
      ((.x2 ↦ᵣ (sp_val - 16)) ** (.x1 ↦ᵣ ra_val) ** ((sp_val - 8) ↦ₘ ra_val)) := by
  have hADDI := addi_spec_gen_same_within .x2 sp_val (-16 : BitVec 12) base (by nofun)
  simp only [signExtend12_neg16] at hADDI
  rw [show sp_val + (-16 : Word) = sp_val - 16 from by bv_omega] at hADDI
  have hSD := sd_spec_gen_within .x2 .x1 (sp_val - 16) ra_val old_slot
    (8 : BitVec 12) (base + 4)
  simp only [signExtend12_8] at hSD
  rw [show (sp_val - 16 : Word) + (8 : Word) = sp_val - 8 from by bv_omega] at hSD
  runBlock hADDI hSD

-- ============================================================================
-- Epilogue spec
-- ============================================================================

/-- Non-leaf epilogue: restore ra, deallocate frame, return.
    sp_val is the FRAME sp (= original - 16).
    After epilogue: sp = sp_val + 16 (= original), ra restored, jumps to saved_ra. -/
theorem cc_epilogue_spec_within (base sp_val old_x1 saved_ra : Word) :
    cpsTripleWithin 3 base (saved_ra &&& ~~~1) (cc_epilogue_code base)
      ((.x2 ↦ᵣ sp_val) ** (.x1 ↦ᵣ old_x1) ** ((sp_val + 8) ↦ₘ saved_ra))
      ((.x2 ↦ᵣ (sp_val + 16)) ** (.x1 ↦ᵣ saved_ra) ** ((sp_val + 8) ↦ₘ saved_ra)) := by
  -- LD x1, x2, 8: load saved_ra into x1
  have hLD := ld_spec_gen_within .x1 .x2 sp_val old_x1 saved_ra (8 : BitVec 12) base
    (by nofun)
  simp only [signExtend12_8] at hLD
  -- ADDI x2, x2, 16: deallocate frame
  have hADDI := addi_spec_gen_same_within .x2 sp_val (16 : BitVec 12) (base + 4) (by nofun)
  simp only [signExtend12_16] at hADDI
  -- Compose LD ;; ADDI (sequential, both exit at next instruction)
  -- LD: bounded triple base → base+4, loading saved_ra into x1.
  -- ADDI: bounded triple base+4 → base+8, deallocating the frame.
  -- After LD+ADDI: x2=sp+16, x1=saved_ra, mem=saved_ra
  -- JALR x0, x1, 0: bounded triple base+8 → saved_ra &&& ~1.
  have hJALR := ret_spec_within' (base + 8) saved_ra
  -- Compose LD ;; ADDI first
  runBlock hLD hADDI hJALR

end EvmAsm.Evm64
