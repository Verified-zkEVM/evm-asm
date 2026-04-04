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
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

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
theorem callNear_spec (offset : BitVec 21) (base : Word) (old_ra : Word) :
    cpsTriple base (base + signExtend21 offset)
      (CodeReq.singleton base (.JAL .x1 offset))
      (.x1 ↦ᵣ old_ra)
      (.x1 ↦ᵣ (base + 4)) :=
  jal_spec .x1 old_ra offset base (by nofun)

/-- Far call: JALR x1, target, 0.
    Saves PC+4 in ra (x1), jumps to target.
    target must differ from x1 (enforced by sep conj). -/
theorem callFar_spec (target : Reg) (v_target old_ra : Word) (base : Word) :
    cpsTriple base ((v_target + signExtend12 0) &&& ~~~1)
      (CodeReq.singleton base (.JALR .x1 target 0))
      ((target ↦ᵣ v_target) ** (.x1 ↦ᵣ old_ra))
      ((target ↦ᵣ v_target) ** (.x1 ↦ᵣ (base + 4))) :=
  jalr_spec .x1 target v_target old_ra 0 base (by nofun)

/-- Return: JALR x0, x1, 0.
    Jumps to (ra + 0) &&& ~1. Preserves ra in x1. -/
theorem ret_spec (base : Word) (ra_val : Word) :
    cpsTriple base ((ra_val + signExtend12 0) &&& ~~~1)
      (CodeReq.singleton base (.JALR .x0 .x1 0))
      (.x1 ↦ᵣ ra_val)
      (.x1 ↦ᵣ ra_val) :=
  jalr_x0_spec_gen .x1 ra_val 0 base

/-- Return with simplified exit: ra &&& ~1 (signExtend12 0 = 0 eliminated). -/
theorem ret_spec' (base : Word) (ra_val : Word) :
    cpsTriple base (ra_val &&& ~~~1)
      (CodeReq.singleton base (.JALR .x0 .x1 0))
      (.x1 ↦ᵣ ra_val)
      (.x1 ↦ᵣ ra_val) := by
  have h := ret_spec base ra_val
  simp only [signExtend12_0] at h
  rw [show ra_val + (0 : Word) = ra_val from by bv_omega] at h
  exact h

-- ============================================================================
-- Prologue spec
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- Non-leaf prologue: allocate 16-byte frame, save ra at sp-8.
    sp_val is the ORIGINAL sp on entry.
    After prologue: sp = sp_val - 16, ra saved at mem[sp_val - 8]. -/
theorem cc_prologue_spec (base sp_val ra_val old_slot : Word)
    (hvalid : isValidDwordAccess (sp_val - 8) = true) :
    cpsTriple base (base + 8) (cc_prologue_code base)
      ((.x2 ↦ᵣ sp_val) ** (.x1 ↦ᵣ ra_val) ** ((sp_val - 8) ↦ₘ old_slot))
      ((.x2 ↦ᵣ (sp_val - 16)) ** (.x1 ↦ᵣ ra_val) ** ((sp_val - 8) ↦ₘ ra_val)) := by
  have hADDI := addi_spec_gen_same .x2 sp_val (-16 : BitVec 12) base (by nofun)
  simp only [signExtend12_neg16] at hADDI
  rw [show sp_val + (-16 : Word) = sp_val - 16 from by bv_omega] at hADDI
  have haddr : (sp_val - 16) + signExtend12 (8 : BitVec 12) = sp_val - 8 := by
    simp only [signExtend12_8]; bv_omega
  have hvalid' : isValidDwordAccess ((sp_val - 16) + signExtend12 (8 : BitVec 12)) = true := by
    rw [haddr]; exact hvalid
  have hSD := sd_spec_gen .x2 .x1 (sp_val - 16) ra_val old_slot
    (8 : BitVec 12) (base + 4) hvalid'
  simp only [signExtend12_8] at hSD
  rw [show (sp_val - 16 : Word) + (8 : Word) = sp_val - 8 from by bv_omega] at hSD
  runBlock hADDI hSD

-- ============================================================================
-- Epilogue spec
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- Non-leaf epilogue: restore ra, deallocate frame, return.
    sp_val is the FRAME sp (= original - 16).
    After epilogue: sp = sp_val + 16 (= original), ra restored, jumps to saved_ra. -/
theorem cc_epilogue_spec (base sp_val old_x1 saved_ra : Word)
    (hvalid : isValidDwordAccess (sp_val + 8) = true) :
    cpsTriple base (saved_ra &&& ~~~1) (cc_epilogue_code base)
      ((.x2 ↦ᵣ sp_val) ** (.x1 ↦ᵣ old_x1) ** ((sp_val + 8) ↦ₘ saved_ra))
      ((.x2 ↦ᵣ (sp_val + 16)) ** (.x1 ↦ᵣ saved_ra) ** ((sp_val + 8) ↦ₘ saved_ra)) := by
  -- LD x1, x2, 8: load saved_ra into x1
  have hvalid' : isValidDwordAccess (sp_val + signExtend12 (8 : BitVec 12)) = true := by
    simp only [signExtend12_8]; exact hvalid
  have hLD := ld_spec_gen .x1 .x2 sp_val old_x1 saved_ra (8 : BitVec 12) base
    (by nofun) hvalid'
  simp only [signExtend12_8] at hLD
  -- ADDI x2, x2, 16: deallocate frame
  have hADDI := addi_spec_gen_same .x2 sp_val (16 : BitVec 12) (base + 4) (by nofun)
  simp only [signExtend12_16] at hADDI
  -- Compose LD ;; ADDI (sequential, both exit at next instruction)
  -- LD: cpsTriple base (base+4) _ (x2=sp, x1=old, mem=saved_ra) (x2=sp, x1=saved_ra, mem=saved_ra)
  -- ADDI: cpsTriple (base+4) (base+8) _ (x2=sp) (x2=sp+16)
  -- After LD+ADDI: x2=sp+16, x1=saved_ra, mem=saved_ra
  -- JALR x0, x1, 0: cpsTriple (base+8) (saved_ra &&& ~1) _ (x1=saved_ra) (x1=saved_ra)
  have hJALR := ret_spec' (base + 8) saved_ra
  -- Compose LD ;; ADDI first
  runBlock hLD hADDI hJALR

-- ============================================================================
-- Composition: calling a function with a known spec
-- ============================================================================

/-- Call a function via JAL and return to call_site + 4.
    The function has a "callable spec" parameterized by return address:
    for any ra, it runs from func_entry to ra &&& ~1 transforming P to Q
    while preserving ra in x1.

    This theorem composes the JAL with the function's spec, yielding a
    round-trip: call_site → function → call_site + 4. -/
theorem callNear_function_spec
    (call_site func_entry : Word) (offset : BitVec 21)
    (cr_func : CodeReq) (P Q : Assertion) (old_ra : Word)
    (hP : P.pcFree)
    (hoff : call_site + signExtend21 offset = func_entry)
    (hd : (CodeReq.singleton call_site (.JAL .x1 offset)).Disjoint cr_func)
    (hfunc : ∀ (ra_val : Word),
      cpsTriple func_entry (ra_val &&& ~~~1) cr_func
        ((.x1 ↦ᵣ ra_val) ** P)
        ((.x1 ↦ᵣ ra_val) ** Q)) :
    cpsTriple call_site ((call_site + 4) &&& ~~~1)
      ((CodeReq.singleton call_site (.JAL .x1 offset)).union cr_func)
      ((.x1 ↦ᵣ old_ra) ** P)
      ((.x1 ↦ᵣ (call_site + 4)) ** Q) := by
  have hcall := cpsTriple_frame_left call_site (call_site + signExtend21 offset)
    (CodeReq.singleton call_site (.JAL .x1 offset))
    (.x1 ↦ᵣ old_ra) (.x1 ↦ᵣ (call_site + 4))
    P hP (callNear_spec offset call_site old_ra)
  rw [hoff] at hcall
  exact cpsTriple_seq call_site func_entry ((call_site + 4) &&& ~~~1)
    (CodeReq.singleton call_site (.JAL .x1 offset)) cr_func hd
    ((.x1 ↦ᵣ old_ra) ** P) ((.x1 ↦ᵣ (call_site + 4)) ** P) ((.x1 ↦ᵣ (call_site + 4)) ** Q)
    hcall (hfunc (call_site + 4))

-- ============================================================================
-- Prologue-body-epilogue composition
-- ============================================================================

/-- Compose prologue + body + epilogue for a non-leaf function.
    The body runs with frame sp (= original sp - 16) and must preserve
    x1 (ra), x2 (frame sp), and the saved-ra slot at mem[sp_val - 8].
    The epilogue restores ra from the stack and returns to the caller.

    sp_val: ORIGINAL sp on entry.
    The overall function runs from prol_base to ra &&& ~1, preserving sp. -/
theorem nonleaf_function_spec
    (prol_base body_entry body_exit epi_base : Word)
    (sp_val ra_val old_slot : Word)
    (cr_prol cr_body cr_epi : CodeReq) (P Q : Assertion)
    (hprol_exit : prol_base + 8 = body_entry)
    (hbody_exit : body_exit = epi_base)
    (hd1 : cr_prol.Disjoint cr_body)
    (hd2 : (cr_prol.union cr_body).Disjoint cr_epi)
    (hprol : cpsTriple prol_base (prol_base + 8) cr_prol
      ((.x2 ↦ᵣ sp_val) ** (.x1 ↦ᵣ ra_val) ** ((sp_val - 8) ↦ₘ old_slot) ** P)
      ((.x2 ↦ᵣ (sp_val - 16)) ** (.x1 ↦ᵣ ra_val) ** ((sp_val - 8) ↦ₘ ra_val) ** P))
    (hbody : cpsTriple body_entry body_exit cr_body
      ((.x2 ↦ᵣ (sp_val - 16)) ** (.x1 ↦ᵣ ra_val) ** ((sp_val - 8) ↦ₘ ra_val) ** P)
      ((.x2 ↦ᵣ (sp_val - 16)) ** (.x1 ↦ᵣ ra_val) ** ((sp_val - 8) ↦ₘ ra_val) ** Q))
    (hepi : cpsTriple epi_base (ra_val &&& ~~~1) cr_epi
      ((.x2 ↦ᵣ (sp_val - 16)) ** (.x1 ↦ᵣ ra_val) ** ((sp_val - 8) ↦ₘ ra_val) ** Q)
      ((.x2 ↦ᵣ sp_val) ** (.x1 ↦ᵣ ra_val) ** ((sp_val - 8) ↦ₘ ra_val) ** Q)) :
    cpsTriple prol_base (ra_val &&& ~~~1) ((cr_prol.union cr_body).union cr_epi)
      ((.x2 ↦ᵣ sp_val) ** (.x1 ↦ᵣ ra_val) ** ((sp_val - 8) ↦ₘ old_slot) ** P)
      ((.x2 ↦ᵣ sp_val) ** (.x1 ↦ᵣ ra_val) ** ((sp_val - 8) ↦ₘ ra_val) ** Q) := by
  rw [← hprol_exit] at hbody
  rw [← hbody_exit] at hepi
  exact cpsTriple_seq prol_base body_exit (ra_val &&& ~~~1)
    (cr_prol.union cr_body) cr_epi hd2
    _ _ _
    (cpsTriple_seq prol_base (prol_base + 8) body_exit cr_prol cr_body hd1 _ _ _ hprol hbody)
    hepi

end EvmAsm.Rv64
