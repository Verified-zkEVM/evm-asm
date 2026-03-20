/-
  EvmAsm.Evm64.SignExtendSpec

  CPS specifications for the 256-bit EVM SIGNEXTEND program (64-bit).
  Modular decomposition:
  - Per-body helper: signext_inplace_spec (4 instrs): LD + SLL + SRA + SD
  - Body specs: signext_body_N_spec for N = 0..3
  - Done spec: signext_done_spec (1 instr): ADDI x12, x12, 32
  - Phase B: signext_phase_b_spec (5 instrs, same computation as BYTE Phase B)
-/

import EvmAsm.Evm64.SignExtend.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64


-- ============================================================================
-- Per-body Helper: Sign-extend in-place (4 instructions)
-- ============================================================================

/-- CodeReq for sign-extend in-place (4 instructions):
    LD x5, off(x12); SLL x5,x5,x6; SRA x5,x5,x6; SD x12,x5,off -/
abbrev signext_inplace_code (off : BitVec 12) (base : Addr) : CodeReq :=
  CodeReq.ofProg base (signext_inplace_prog off)

/-- Sign-extend in-place spec (4 instructions):
    LD x5, off(x12); SLL x5,x5,x6; SRA x5,x5,x6; SD x12,x5,off

    Loads a 64-bit limb, sign-extends using shift_amount, stores back.
    Result = BitVec.sshiftRight (limb <<< (sa % 64)) (sa % 64) -/
theorem signext_inplace_spec (off : BitVec 12)
    (sp limb v5 shift_amount : Word) (base : Addr)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let result := BitVec.sshiftRight (limb <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)
    let code := signext_inplace_code off base
    cpsTriple base (base + 16) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift_amount) **
       ((sp + signExtend12 off) ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift_amount) **
       ((sp + signExtend12 off) ↦ₘ result)) := by
  have L := ld_spec_gen .x5 .x12 sp v5 limb off base (by nofun) hvalid
  have SL := sll_spec_gen_rd_eq_rs1 .x5 .x6 limb shift_amount (base + 4) (by nofun)
  have SR := sra_spec_gen_rd_eq_rs1 .x5 .x6 (limb <<< (shift_amount.toNat % 64)) shift_amount (base + 8) (by nofun)
  have SD_ := sd_spec_gen .x12 .x5 sp (BitVec.sshiftRight (limb <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) limb off (base + 12) hvalid
  runBlock L SL SR SD_

-- ============================================================================
-- Body Specs
-- ============================================================================

/-- CodeReq for sign-extend body 3 (5 instructions):
    LD + SLL + SRA + SD at sp+56 + JAL. -/
abbrev signext_body_3_code (base : Addr) (jal_off : BitVec 21) : CodeReq :=
  CodeReq.ofProg base (signext_body_3_prog jal_off)

/-- Body 3: limb_idx=3, sign-extend limb 3 at sp+56 (5 instrs).
    4 instructions: LD + SLL + SRA + SD + JAL. No higher limbs to fill. -/
theorem signext_body_3_spec (sp : Word)
    (v5 shift_amount : Word) (v3 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 16) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result := BitVec.sshiftRight (v3 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)
    let code := signext_body_3_code base jal_off
    cpsTriple base exit code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift_amount) **
       ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift_amount) **
       ((sp + 56) ↦ₘ result)) := by
  have IP := signext_inplace_spec 56 sp v3 v5 shift_amount base (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 16)
  rw [hexit] at JL
  runBlock IP JL

/-- CodeReq for sign-extend body 2 (7 instructions):
    LD + SLL + SRA + SD at sp+48 + SRAI + SD at sp+56 + JAL. -/
abbrev signext_body_2_code (base : Addr) (jal_off : BitVec 21) : CodeReq :=
  CodeReq.ofProg base (signext_body_2_prog jal_off)

/-- Body 2: limb_idx=2, sign-extend limb 2 at sp+48, fill limb 3 (7 instrs).
    LD + SLL + SRA + SD + SRAI + SD + JAL. -/
theorem signext_body_2_spec (sp : Word)
    (v5 v10 shift_amount : Word) (v2 v3 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 24) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result := BitVec.sshiftRight (v2 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)
    let sign_fill := BitVec.sshiftRight result 63
    let code := signext_body_2_code base jal_off
    cpsTriple base exit code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift_amount) ** (.x10 ↦ᵣ v10) **
       ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift_amount) ** (.x10 ↦ᵣ sign_fill) **
       ((sp + 48) ↦ₘ result) ** ((sp + 56) ↦ₘ sign_fill)) := by
  have h63 : (63 : BitVec 6).toNat = 63 := by native_decide
  have IP := signext_inplace_spec 48 sp v2 v5 shift_amount base (by validMem)
  have SR := srai_spec_gen .x10 .x5 v10
    (BitVec.sshiftRight (v2 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64))
    63 (base + 16) (by nofun)
  simp only [h63] at SR
  have S0 := sd_spec_gen .x12 .x10 sp
    (BitVec.sshiftRight (BitVec.sshiftRight (v2 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) 63)
    v3 56 (base + 20) (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 24)
  rw [hexit] at JL
  runBlock IP SR S0 JL

/-- CodeReq for sign-extend body 1 (8 instructions):
    LD + SLL + SRA + SD at sp+40 + SRAI + SD at sp+48 + SD at sp+56 + JAL. -/
abbrev signext_body_1_code (base : Addr) (jal_off : BitVec 21) : CodeReq :=
  CodeReq.ofProg base (signext_body_1_prog jal_off)

/-- Body 1: limb_idx=1, sign-extend limb 1 at sp+40, fill limbs 2-3 (8 instrs).
    LD + SLL + SRA + SD + SRAI + SD + SD + JAL. -/
theorem signext_body_1_spec (sp : Word)
    (v5 v10 shift_amount : Word) (v1 v2 v3 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 28) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result := BitVec.sshiftRight (v1 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)
    let sign_fill := BitVec.sshiftRight result 63
    let code := signext_body_1_code base jal_off
    cpsTriple base exit code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift_amount) ** (.x10 ↦ᵣ v10) **
       ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift_amount) ** (.x10 ↦ᵣ sign_fill) **
       ((sp + 40) ↦ₘ result) ** ((sp + 48) ↦ₘ sign_fill) ** ((sp + 56) ↦ₘ sign_fill)) := by
  have h63 : (63 : BitVec 6).toNat = 63 := by native_decide
  have IP := signext_inplace_spec 40 sp v1 v5 shift_amount base (by validMem)
  have SR := srai_spec_gen .x10 .x5 v10
    (BitVec.sshiftRight (v1 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64))
    63 (base + 16) (by nofun)
  simp only [h63] at SR
  have S0 := sd_spec_gen .x12 .x10 sp
    (BitVec.sshiftRight (BitVec.sshiftRight (v1 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) 63)
    v2 48 (base + 20) (by validMem)
  have S1 := sd_spec_gen .x12 .x10 sp
    (BitVec.sshiftRight (BitVec.sshiftRight (v1 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) 63)
    v3 56 (base + 24) (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 28)
  rw [hexit] at JL
  runBlock IP SR S0 S1 JL

/-- CodeReq for sign-extend body 0 (8 instructions):
    LD + SLL + SRA + SD at sp+32 + SRAI + SD at sp+40 + SD at sp+48 + SD at sp+56.
    Falls through to done. -/
abbrev signext_body_0_code (base : Addr) : CodeReq :=
  CodeReq.ofProg base signext_body_0

/-- Body 0: limb_idx=0, sign-extend limb 0 at sp+32, fill limbs 1-3 (8 instrs).
    LD + SLL + SRA + SD + SRAI + SD + SD + SD. Falls through to done. -/
theorem signext_body_0_spec (sp : Word)
    (v5 v10 shift_amount : Word) (v0 v1 v2 v3 : Word)
    (base : Addr)
    (hvalid : ValidMemRange sp 8) :
    let result := BitVec.sshiftRight (v0 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)
    let sign_fill := BitVec.sshiftRight result 63
    let code := signext_body_0_code base
    cpsTriple base (base + 32) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift_amount) ** (.x10 ↦ᵣ v10) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift_amount) ** (.x10 ↦ᵣ sign_fill) **
       ((sp + 32) ↦ₘ result) ** ((sp + 40) ↦ₘ sign_fill) ** ((sp + 48) ↦ₘ sign_fill) ** ((sp + 56) ↦ₘ sign_fill)) := by
  have h63 : (63 : BitVec 6).toNat = 63 := by native_decide
  have IP := signext_inplace_spec 32 sp v0 v5 shift_amount base (by validMem)
  have SR := srai_spec_gen .x10 .x5 v10
    (BitVec.sshiftRight (v0 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64))
    63 (base + 16) (by nofun)
  simp only [h63] at SR
  have S0 := sd_spec_gen .x12 .x10 sp
    (BitVec.sshiftRight (BitVec.sshiftRight (v0 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) 63)
    v1 40 (base + 20) (by validMem)
  have S1 := sd_spec_gen .x12 .x10 sp
    (BitVec.sshiftRight (BitVec.sshiftRight (v0 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) 63)
    v2 48 (base + 24) (by validMem)
  have S2 := sd_spec_gen .x12 .x10 sp
    (BitVec.sshiftRight (BitVec.sshiftRight (v0 <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) 63)
    v3 56 (base + 28) (by validMem)
  runBlock IP SR S0 S1 S2

-- ============================================================================
-- Done Spec: pop b word (1 instruction)
-- ============================================================================

/-- Done spec: ADDI x12, x12, 32 (pop b word). -/
theorem signext_done_spec (sp : Word) (base : Addr) :
    let nsp := sp + signExtend12 (32 : BitVec 12)
    let code := CodeReq.singleton base (.ADDI .x12 .x12 32)
    cpsTriple base (base + 4) code
      ((.x12 ↦ᵣ sp))
      ((.x12 ↦ᵣ nsp)) := by
  exact addi_spec_gen_same .x12 sp 32 base (by nofun)

-- ============================================================================
-- Phase B Spec: Compute shift_amount and limb_idx (5 instructions)
-- ============================================================================

/-- CodeReq for sign-extend phase B (5 instructions):
    ANDI x10,x5,7; SLLI x10,x10,3; ADDI x6,x0,56; SUB x6,x6,x10; SRLI x5,x5,3. -/
abbrev signext_phase_b_code (base : Addr) : CodeReq :=
  CodeReq.ofProg base signext_phase_b

/-- Phase B spec: compute sign-extension parameters.
    ANDI x10,x5,7; SLLI x10,x10,3; ADDI x6,x0,56;
    SUB x6,x6,x10; SRLI x5,x5,3.
    Outputs: x6 = 56 - (b%8)*8 (shift_amount), x5 = b/8 (limb_idx).
    Same computation as byte_phase_b_spec. -/
theorem signext_phase_b_spec (b r6 r10 : Word) (base : Addr) :
    let byte_in_limb := b &&& signExtend12 (7 : BitVec 12)
    let byte_shift := byte_in_limb <<< (3 : BitVec 6).toNat
    let shift_amount := (56 : Word) - byte_shift
    let limb_idx := b >>> (3 : BitVec 6).toNat
    let code := signext_phase_b_code base
    cpsTriple base (base + 20) code
      ((.x5 ↦ᵣ b) ** (.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10))
      ((.x5 ↦ᵣ limb_idx) ** (.x6 ↦ᵣ shift_amount) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ byte_shift)) := by
  have A := andi_spec_gen .x10 .x5 r10 b 7 base (by nofun)
  have SL := slli_spec_gen_same .x10 (b &&& signExtend12 7) 3 (base + 4) (by nofun)
  have AD := addi_x0_spec_gen .x6 r6 56 (base + 8) (by nofun)
  have SU := sub_spec_gen_rd_eq_rs1 .x6 .x10 (signExtend12 56)
    ((b &&& signExtend12 7) <<< (3 : BitVec 6).toNat) (base + 12) (by nofun)
  have SR := srli_spec_gen_same .x5 b 3 (base + 16) (by nofun)
  runBlock A SL AD SU SR

-- ============================================================================
-- LD/OR Accumulator Helper (2 instructions)
-- ============================================================================

abbrev signext_ld_or_acc_code (off : BitVec 12) (base : Addr) : CodeReq :=
  CodeReq.ofProg base (signext_ld_or_acc_prog off)

theorem signext_ld_or_acc_spec (sp acc prev_x10 val : Word) (off : BitVec 12)
    (base : Addr)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let code := signext_ld_or_acc_code off base
    cpsTriple base (base + 8) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ acc) ** (.x10 ↦ᵣ prev_x10) ** ((sp + signExtend12 off) ↦ₘ val))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (acc ||| val)) ** (.x10 ↦ᵣ val) ** ((sp + signExtend12 off) ↦ₘ val)) := by
  have L := ld_spec_gen .x10 .x12 sp prev_x10 val off base (by nofun) hvalid
  have OR_ := or_spec_gen_rd_eq_rs1 .x5 .x10 acc val (base + 4) (by nofun)
  runBlock L OR_

-- ============================================================================
-- Cascade Step Helper (2 instructions)
-- ============================================================================

abbrev signext_cascade_step_code (k : BitVec 12) (offset : BitVec 13) (base : Addr) : CodeReq :=
  CodeReq.ofProg base (signext_cascade_step_prog k offset)

/-- Cascade step: ADDI x10,x0,k followed by BEQ x5,x10,off.
    Produces a cpsBranch with clean postconditions (no pure facts). -/
theorem signext_cascade_step_spec (v5 v10 : Word)
    (k : BitVec 12) (offset : BitVec 13) (base target : Addr)
    (htarget : (base + 4) + signExtend13 offset = target) :
    let k_val := (0 : Word) + signExtend12 k
    let code := signext_cascade_step_code k offset base
    cpsBranch base code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      target ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val))
      (base + 8) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val)) := by
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have hd : CodeReq.Disjoint
      (CodeReq.singleton base (.ADDI .x10 .x0 k))
      (CodeReq.singleton (base + 4) (.BEQ .x5 .x10 offset)) :=
    CodeReq.Disjoint.singleton (by bv_omega) _ _
  have s1 := addi_spec_gen .x10 .x0 v10 0 k base (by nofun)
  have s1' : cpsTriple base (base + 4) (CodeReq.singleton base (.ADDI .x10 .x0 k))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 k))) :=
    cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTriple_frame_left _ _ _ _ _ (.x5 ↦ᵣ v5) (by pcFree) s1)
  have s2_raw := beq_spec_gen .x5 .x10 offset v5 ((0 : Word) + signExtend12 k) (base + 4)
  rw [htarget, ha1] at s2_raw
  have s2' : cpsBranch (base + 4) (CodeReq.singleton (base + 4) (.BEQ .x5 .x10 offset))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)))
      target ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)))
      (base + 8) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 k))) :=
    cpsBranch_consequence _ _ _ _
      target _ _ (base + 8) _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsBranch_frame_left _ _ _ _ _ _ _ (.x0 ↦ᵣ (0 : Word)) (by pcFree)
        (cpsBranch_consequence (base + 4) _ _ _
          target _ _ (base + 8) _ _
          (fun _ hp => hp)
          (fun h hp => sepConj_mono_right
            (fun h' hp' => ((sepConj_pure_right _ (v5 = (0 : Word) + signExtend12 k) h').1 hp').1) h hp)
          (fun h hp => sepConj_mono_right
            (fun h' hp' => ((sepConj_pure_right _ (v5 ≠ (0 : Word) + signExtend12 k) h').1 hp').1) h hp)
          s2_raw))
  exact cpsTriple_seq_cpsBranch_with_perm _ _ _ _ hd _ _ _ target _ (base + 8) _
    (fun _ hp => hp) s1' s2'

-- ============================================================================
-- Phase A: Check b >= 31 (9 instructions, cpsBranch)
-- ============================================================================

private theorem regIs_to_regOwn (r : Reg) (v : Word) : ∀ h, (r ↦ᵣ v) h → (regOwn r) h :=
  fun _ hp => ⟨v, hp⟩

/-- Phase A code as explicit union of sub-CRs (matching disjoint composition structure).
    9 instructions: LD + LD/OR + LD/OR + BNE + LD + SLTIU + BEQ -/
abbrev signext_phase_a_code (base : Addr) : CodeReq :=
  -- LD x5 x12 8 at base
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 8))
  -- LD x10 x12 16 + OR x5 x5 x10 at base+4, base+8
  (CodeReq.union (signext_ld_or_acc_code 16 (base + 4))
  -- LD x10 x12 24 + OR x5 x5 x10 at base+12, base+16
  (CodeReq.union (signext_ld_or_acc_code 24 (base + 12))
  -- BNE x5 x0 168 at base+20
  (CodeReq.union (CodeReq.singleton (base + 20) (.BNE .x5 .x0 168))
  -- LD x5 x12 0 at base+24
  (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x5 .x12 0))
  -- SLTIU x10 x5 31 at base+28
  (CodeReq.union (CodeReq.singleton (base + 28) (.SLTIU .x10 .x5 31))
  -- BEQ x10 x0 156 at base+32
  (CodeReq.singleton (base + 32) (.BEQ .x10 .x0 156)))))))

set_option maxHeartbeats 6400000 in
/-- Phase A spec: Check b >= 31.
    9 instructions, cpsBranch with 2 exits:
    - Taken (done_path): b >= 31 (high limbs nonzero or b[0] >= 31)
    - Not-taken (base+36): b < 31, x5 = b0
    Uses disjoint composition throughout (no extend_code). -/
theorem signext_phase_a_spec (sp r5 r10 : Word)
    (b0 b1 b2 b3 : Word)
    (base done_path : Addr)
    (hdone1 : (base + 20) + signExtend13 168 = done_path)
    (hdone2 : (base + 32) + signExtend13 156 = done_path)
    (hvalid : ValidMemRange sp 4) :
    let code := signext_phase_a_code base
    cpsBranch base code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3))
      done_path
      ((.x12 ↦ᵣ sp) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3))
      (base + 36)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3)) := by
  -- Memory validity
  have hv0 : isValidDwordAccess sp = true := by
    have := hvalid.get (i := 0) (by omega); simpa using this
  have hv8 : isValidDwordAccess (sp + 8) = true := by
    have := hvalid.get (i := 1) (by omega); simpa using this
  have hv16 : isValidDwordAccess (sp + 16) = true := by
    have := hvalid.get (i := 2) (by omega); simpa using this
  have hv24 : isValidDwordAccess (sp + 24) = true := by
    have := hvalid.get (i := 3) (by omega); simpa using this
  -- Address arithmetic
  have ha48 : (base + 4 : Addr) + 8 = base + 12 := by bv_omega
  have ha128 : (base + 12 : Addr) + 8 = base + 20 := by bv_omega
  have ha20 : (base + 20 : Addr) + 4 = base + 24 := by bv_omega
  have ha24 : (base + 24 : Addr) + 4 = base + 28 := by bv_omega
  have ha28 : (base + 28 : Addr) + 4 = base + 32 := by bv_omega
  have ha32 : (base + 32 : Addr) + 4 = base + 36 := by bv_omega
  -- Sub-CRs for each instruction group
  let cr_ld1 := CodeReq.singleton base (.LD .x5 .x12 8)
  let cr_lor2 := signext_ld_or_acc_code 16 (base + 4)
  let cr_lor3 := signext_ld_or_acc_code 24 (base + 12)
  let cr_bne := CodeReq.singleton (base + 20) (.BNE .x5 .x0 168)
  let cr_ld5 := CodeReq.singleton (base + 24) (.LD .x5 .x12 0)
  let cr_sltiu := CodeReq.singleton (base + 28) (.SLTIU .x10 .x5 31)
  let cr_beq := CodeReq.singleton (base + 32) (.BEQ .x10 .x0 156)
  -- ── Part 1: Linear chain base..base+20 (LD + LD/OR + LD/OR) ──
  have lw1 := ld_spec_gen .x5 .x12 sp r5 b1 8 base (by nofun)
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_8] at lw1
  have lor2 := signext_ld_or_acc_spec sp b1 r10 b2 16 (base + 4)
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_16] at lor2
  rw [ha48] at lor2
  have hd_ld1_lor2 : cr_ld1.Disjoint cr_lor2 :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega) _ _)
      (CodeReq.Disjoint.singleton (by bv_omega) _ _)
  have lw1f := cpsTriple_frame_left base (base + 4) cr_ld1
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** ((sp + 8) ↦ₘ b1))
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b1) ** ((sp + 8) ↦ₘ b1))
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) ** (sp ↦ₘ b0) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3))
    (by pcFree) lw1
  have lor2f := cpsTriple_frame_left (base + 4) (base + 12) cr_lor2
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b1) ** (.x10 ↦ᵣ r10) ** ((sp + 16) ↦ₘ b2))
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b1 ||| b2)) ** (.x10 ↦ᵣ b2) ** ((sp + 16) ↦ₘ b2))
    ((.x0 ↦ᵣ (0 : Word)) ** (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 24) ↦ₘ b3))
    (by pcFree) lor2
  have c12 := cpsTriple_seq_with_perm base (base + 4) (base + 12) cr_ld1 cr_lor2 hd_ld1_lor2
    _ _ _ _
    (fun h hp => by xperm_hyp hp) lw1f lor2f
  have lor3 := signext_ld_or_acc_spec sp (b1 ||| b2) b2 b3 24 (base + 12)
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at lor3
  rw [ha128] at lor3
  have lor3f := cpsTriple_frame_left (base + 12) (base + 20) cr_lor3
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b1 ||| b2)) ** (.x10 ↦ᵣ b2) ** ((sp + 24) ↦ₘ b3))
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** ((sp + 24) ↦ₘ b3))
    ((.x0 ↦ᵣ (0 : Word)) ** (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2))
    (by pcFree) lor3
  have hd_12_lor3 : (cr_ld1.union cr_lor2).Disjoint cr_lor3 :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton (by bv_omega) _ _)
        (CodeReq.Disjoint.singleton (by bv_omega) _ _))
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton (by bv_omega) _ _)
          (CodeReq.Disjoint.singleton (by bv_omega) _ _))
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton (by bv_omega) _ _)
          (CodeReq.Disjoint.singleton (by bv_omega) _ _)))
  have c13 := cpsTriple_seq_with_perm base (base + 12) (base + 20)
    (cr_ld1.union cr_lor2) cr_lor3 hd_12_lor3
    _ _ _ _
    (fun h hp => by xperm_hyp hp) c12 lor3f
  let cr_linear := (cr_ld1.union cr_lor2).union cr_lor3
  -- ── Part 2: BNE at base+20 (first branch) ──
  have bne_raw := bne_spec_gen .x5 .x0 168 (b1 ||| b2 ||| b3) (0 : Word) (base + 20)
  rw [hdone1, ha20] at bne_raw
  have bne1 : cpsBranch (base + 20) cr_bne
      ((.x5 ↦ᵣ (b1 ||| b2 ||| b3)) ** (.x0 ↦ᵣ (0 : Word)))
      done_path ((.x5 ↦ᵣ (b1 ||| b2 ||| b3)) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 24) ((.x5 ↦ᵣ (b1 ||| b2 ||| b3)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence (base + 20) _ _ _
      done_path _ _ (base + 24) _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      bne_raw
  have bne1f := cpsBranch_frame_left (base + 20) cr_bne
    ((.x5 ↦ᵣ (b1 ||| b2 ||| b3)) ** (.x0 ↦ᵣ (0 : Word)))
    done_path _ (base + 24) _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3))
    (by pcFree) bne1
  have hd_lin_bne : cr_linear.Disjoint cr_bne :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.singleton (by bv_omega) _ _)
        (CodeReq.Disjoint.union_left
          (CodeReq.Disjoint.singleton (by bv_omega) _ _)
          (CodeReq.Disjoint.singleton (by bv_omega) _ _)))
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.singleton (by bv_omega) _ _)
        (CodeReq.Disjoint.singleton (by bv_omega) _ _))
  have br1 := cpsTriple_seq_cpsBranch_with_perm base (base + 20) cr_linear cr_bne hd_lin_bne
    _ _ _ done_path _ (base + 24) _
    (fun h hp => by xperm_hyp hp) c13 bne1f
  -- ── Part 3: Fall-through path (base+24..base+32): LD + SLTIU + BEQ ──
  have lw5 := ld_spec_gen .x5 .x12 sp
    (b1 ||| b2 ||| b3) b0 0 (base + 24) (by nofun)
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_omega]; exact hv0)
  simp only [signExtend12_0] at lw5
  rw [show sp + (0 : Word) = sp from by bv_omega] at lw5
  rw [ha24] at lw5
  have sltiu_raw := sltiu_spec_gen .x10 .x5 b3 b0 31 (base + 28) (by nofun)
  rw [ha28] at sltiu_raw
  let sltiu_val := (if BitVec.ult b0 (signExtend12 (31 : BitVec 12)) then (1 : Word) else (0 : Word))
  have hd_ld5_sltiu : cr_ld5.Disjoint cr_sltiu :=
    CodeReq.Disjoint.singleton (by bv_omega) _ _
  have lw5f := cpsTriple_frame_left (base + 24) (base + 28) cr_ld5
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b1 ||| b2 ||| b3)) ** (sp ↦ₘ b0))
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0) ** (sp ↦ₘ b0))
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ b3) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3))
    (by pcFree) lw5
  have sltiuf := cpsTriple_frame_left (base + 28) (base + 32) cr_sltiu
    ((.x5 ↦ᵣ b0) ** (.x10 ↦ᵣ b3))
    ((.x5 ↦ᵣ b0) ** (.x10 ↦ᵣ sltiu_val))
    ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3))
    (by pcFree) sltiu_raw
  have c56 := cpsTriple_seq_with_perm (base + 24) (base + 28) (base + 32)
    cr_ld5 cr_sltiu hd_ld5_sltiu
    _ _ _ _
    (fun h hp => by xperm_hyp hp) lw5f sltiuf
  have beq_raw := beq_spec_gen .x10 .x0 156 sltiu_val (0 : Word) (base + 32)
  rw [hdone2, ha32] at beq_raw
  have beq1 : cpsBranch (base + 32) cr_beq
      ((.x10 ↦ᵣ sltiu_val) ** (.x0 ↦ᵣ (0 : Word)))
      done_path ((.x10 ↦ᵣ sltiu_val) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 36) ((.x10 ↦ᵣ sltiu_val) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence (base + 32) _ _ _
      done_path _ _ (base + 36) _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      beq_raw
  have beq1f := cpsBranch_frame_left (base + 32) cr_beq
    ((.x10 ↦ᵣ sltiu_val) ** (.x0 ↦ᵣ (0 : Word)))
    done_path _ (base + 36) _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0) ** (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3))
    (by pcFree) beq1
  have hd_56_beq : (cr_ld5.union cr_sltiu).Disjoint cr_beq :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.singleton (by bv_omega) _ _)
      (CodeReq.Disjoint.singleton (by bv_omega) _ _)
  have br2 := cpsTriple_seq_cpsBranch_with_perm (base + 24) (base + 32)
    (cr_ld5.union cr_sltiu) cr_beq hd_56_beq
    _ _ _ done_path _ (base + 36) _
    (fun h hp => by xperm_hyp hp) c56 beq1f
  let cr_tail := (cr_ld5.union cr_sltiu).union cr_beq
  -- ── Part 4: Combine br1 and br2 ──
  have sd_tail (a : Addr) (i : Instr)
      (h24 : a ≠ base + 24) (h28 : a ≠ base + 28) (h32 : a ≠ base + 32) :
      (CodeReq.singleton a i).Disjoint cr_tail :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h24 _ _)
        (CodeReq.Disjoint.singleton h28 _ _))
      (CodeReq.Disjoint.singleton h32 _ _)
  have hd_lor2_tail : cr_lor2.Disjoint cr_tail :=
    CodeReq.Disjoint.union_left
      (sd_tail (base + 4) _ (by bv_omega) (by bv_omega) (by bv_omega))
      (sd_tail (base + 4 + 4) _ (by bv_omega) (by bv_omega) (by bv_omega))
  have hd_lor3_tail : cr_lor3.Disjoint cr_tail :=
    CodeReq.Disjoint.union_left
      (sd_tail (base + 12) _ (by bv_omega) (by bv_omega) (by bv_omega))
      (sd_tail (base + 12 + 4) _ (by bv_omega) (by bv_omega) (by bv_omega))
  have hd_ld1_tail : cr_ld1.Disjoint cr_tail :=
    sd_tail base _ (by bv_omega) (by bv_omega) (by bv_omega)
  have hd_bne_tail : cr_bne.Disjoint cr_tail :=
    sd_tail (base + 20) _ (by bv_omega) (by bv_omega) (by bv_omega)
  have hd_lin_bne_tail : (cr_linear.union cr_bne).Disjoint cr_tail :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.union_left hd_ld1_tail hd_lor2_tail) hd_lor3_tail)
      hd_bne_tail
  have hd_br1_br2 : (cr_linear.union cr_bne).Disjoint cr_tail :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.union_left hd_ld1_tail hd_lor2_tail) hd_lor3_tail)
      hd_bne_tail
  -- Combine: br1 (taken → done_path, ntaken → base+24) with br2 (base+24 → done_path or base+36)
  have combined := cpsBranch_seq_cpsBranch_with_perm
    base (base + 24) done_path (base + 36)
    (cr_linear.union cr_bne) cr_tail hd_br1_br2
    _ _ _ _ _ _ _
    br1 (fun h hp => by xperm_hyp hp) br2
    -- ht1: weaken BNE taken path (x5 = b1|||b2|||b3, x10 = b3) → regOwn
    (fun h hp => by
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) **
           (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
           (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3))
          from by xperm) h).mp hp)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ sp) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3))
        from by xperm) h).mp w1)
    -- ht2: weaken BEQ taken path (x5 = b0, x10 = sltiu_val) → regOwn
    (fun h hp => by
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ b0) ** (.x10 ↦ᵣ sltiu_val) **
           (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
           (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3))
          from by xperm) h).mp hp)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ sp) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3))
        from by xperm) h).mp w1)
  -- CR reassociation: (cr_linear ∪ cr_bne) ∪ cr_tail = signext_phase_a_code base
  have hcr_eq : (cr_linear.union cr_bne).union cr_tail = signext_phase_a_code base := by
    show ((((CodeReq.singleton base (.LD .x5 .x12 8)).union (signext_ld_or_acc_code 16 (base + 4))).union
            (signext_ld_or_acc_code 24 (base + 12))).union
           (CodeReq.singleton (base + 20) (.BNE .x5 .x0 168))).union
          (((CodeReq.singleton (base + 24) (.LD .x5 .x12 0)).union
            (CodeReq.singleton (base + 28) (.SLTIU .x10 .x5 31))).union
           (CodeReq.singleton (base + 32) (.BEQ .x10 .x0 156)))
        = signext_phase_a_code base
    simp only [signext_phase_a_code, signext_ld_or_acc_code, CodeReq.union_assoc]
  have result : cpsBranch base (signext_phase_a_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3))
      done_path
      ((.x12 ↦ᵣ sp) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3))
      (base + 36)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3)) := by
    rw [← hcr_eq]
    exact cpsBranch_consequence base _ _ _
      done_path _ _ (base + 36) _ _
      (fun h hp => by xperm_hyp hp)
      (fun _ hp => hp)
      (fun h hp => by
        have w0 := sepConj_mono_left (regIs_to_regOwn .x10 _) h
          ((congrFun (show _ =
            ((.x10 ↦ᵣ sltiu_val) **
             (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0) ** (.x0 ↦ᵣ (0 : Word)) **
             (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3))
            from by xperm) h).mp hp)
        exact (congrFun (show _ =
          ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
           (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3))
          from by xperm) h).mp w0)
      combined
  exact result

-- ============================================================================
-- Phase C: Cascade dispatch on limb_idx (5 instructions, cpsNBranch)
-- ============================================================================

/-- Phase C code as explicit union of sub-CRs (matching disjoint composition structure). -/
abbrev signext_phase_c_code (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.BEQ .x5 .x0 100))
  (CodeReq.union (signext_cascade_step_code 1 60 (base + 4))
  (signext_cascade_step_code 2 24 (base + 12)))

set_option maxHeartbeats 3200000 in
/-- Phase C spec: cascade dispatch on limb_idx (0-3).
    Uses disjoint composition to chain BEQ + two cascade steps. -/
theorem signext_phase_c_spec (v5 v10 : Word) (base : Addr)
    (e0 e1 e2 e3 : Addr)
    (he0 : base + signExtend13 100 = e0)
    (he1 : (base + 8) + signExtend13 60 = e1)
    (he2 : (base + 16) + signExtend13 24 = e2)
    (he3 : base + 20 = e3) :
    let code := signext_phase_c_code base
    cpsNBranch base code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      [(e0, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10)),
       (e1, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1))),
       (e2, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2))),
       (e3, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)))] := by
  -- Address arithmetic
  have hc1 : ((base + 4 : Addr) + 4) + signExtend13 60 = e1 := by
    rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]; exact he1
  have hc2 : ((base + 12 : Addr) + 4) + signExtend13 24 = e2 := by
    rw [show (base + 12 : Addr) + 4 = base + 16 from by bv_omega]; exact he2
  -- Sub-CRs
  let cr_beq0 := CodeReq.singleton base (.BEQ .x5 .x0 100)
  let cr_cs1 := signext_cascade_step_code 1 60 (base + 4)
  let cr_cs2 := signext_cascade_step_code 2 24 (base + 12)
  -- Disjointness proofs
  have hd_beq0_cs1 : cr_beq0.Disjoint cr_cs1 :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega) _ _)
      (CodeReq.Disjoint.singleton (by bv_omega) _ _)
  have hd_beq0_cs2 : cr_beq0.Disjoint cr_cs2 :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega) _ _)
      (CodeReq.Disjoint.singleton (by bv_omega) _ _)
  have hd_cs1_cs2 : cr_cs1.Disjoint cr_cs2 :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton (by bv_omega) _ _)
        (CodeReq.Disjoint.singleton (by bv_omega) _ _))
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton (by bv_omega) _ _)
        (CodeReq.Disjoint.singleton (by bv_omega) _ _))
  -- Step 0: BEQ x5 x0 100 at base
  have beq0_raw := beq_spec_gen .x5 .x0 100 v5 (0 : Word) base
  rw [he0] at beq0_raw
  have beq0 : cpsBranch base cr_beq0
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)))
      e0 ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 4) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence base _ _ _ e0 _ _ (base + 4) _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ (v5 = (0 : Word)) h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ (v5 ≠ (0 : Word)) h').1 hp').1) h hp)
      beq0_raw
  have beq0f := cpsBranch_frame_left base cr_beq0
    ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)))
    e0 _ (base + 4) _
    (.x10 ↦ᵣ v10) (by pcFree) beq0
  -- Step 1: cascade step at base+4
  have cs1 := signext_cascade_step_spec v5 v10 1 60 (base + 4) e1 hc1
  rw [show (base + 4 : Addr) + 8 = base + 12 from by bv_omega] at cs1
  -- Step 2: cascade step at base+12
  have cs2 := signext_cascade_step_spec v5 ((0 : Word) + signExtend12 1) 2 24 (base + 12) e2 hc2
  rw [show (base + 12 : Addr) + 8 = base + 20 from by bv_omega] at cs2
  -- Fallthrough at base+20
  have ft := cpsNBranch_refl (base + 20)
    ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)))
    _ (fun _ hp => hp)
  -- Chain step 2 + fallthrough
  have n3 := cpsBranch_cons_cpsNBranch (base + 12) cr_cs2 CodeReq.empty
    (CodeReq.Disjoint.empty_right cr_cs2)
    _ e2 _ (base + 20) _ _ cs2 ft
  have hunion_empty : ∀ (cr : CodeReq), cr.union CodeReq.empty = cr := by
    intro cr; funext a; simp only [CodeReq.union, CodeReq.empty]; cases cr a <;> rfl
  -- Chain step 1 + n3
  have hd_cs1_rest : cr_cs1.Disjoint (cr_cs2.union CodeReq.empty) := by
    rw [hunion_empty]; exact hd_cs1_cs2
  have n2 := cpsBranch_cons_cpsNBranch_with_perm (base + 4) cr_cs1 (cr_cs2.union CodeReq.empty)
    hd_cs1_rest
    _ e1 _ (base + 12) _ _ _
    (fun h hp => by xperm_hyp hp) cs1 n3
  -- Chain step 0 + n2
  have hd_beq0_rest : cr_beq0.Disjoint (cr_cs1.union (cr_cs2.union CodeReq.empty)) := by
    rw [hunion_empty]; exact CodeReq.Disjoint.union_right hd_beq0_cs1 hd_beq0_cs2
  have n1 := cpsBranch_cons_cpsNBranch_with_perm base cr_beq0 (cr_cs1.union (cr_cs2.union CodeReq.empty))
    hd_beq0_rest
    _ e0 _ (base + 4) _ _ _
    (fun h hp => by xperm_hyp hp) beq0f n2
  -- Simplify CR and match goal
  have hcr_eq : cr_beq0.union (cr_cs1.union (cr_cs2.union CodeReq.empty)) = signext_phase_c_code base := by
    simp only [hunion_empty]; rfl
  intro code
  have n1_rw := hcr_eq ▸ n1
  exact cpsNBranch_weaken_posts _ _ _ _ _ (cpsNBranch_weaken_pre _ _ _ _ _ (fun h hp => by xperm_hyp hp) n1_rw)
    (fun ex hmem => by
      simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false, false_or] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, List.Mem.head _, rfl, fun h hp => by xperm_hyp hp⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, fun h hp => by xperm_hyp hp⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl, fun h hp => by xperm_hyp hp⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))), he3.symm, fun h hp => by xperm_hyp hp⟩)

-- ============================================================================
-- Cascade step with pure dispatch facts
-- ============================================================================

/-- Cascade step with pure dispatch facts: each exit includes ⌜v5 = k_val⌝ / ⌜v5 ≠ k_val⌝. -/
theorem signext_cascade_step_spec_pure (v5 v10 : Word)
    (k : BitVec 12) (offset : BitVec 13) (base target : Addr)
    (htarget : (base + 4) + signExtend13 offset = target) :
    let k_val := (0 : Word) + signExtend12 k
    let code := signext_cascade_step_code k offset base
    cpsBranch base code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      target ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val) ** ⌜v5 = k_val⌝)
      (base + 8) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val) ** ⌜v5 ≠ k_val⌝) := by
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have hd : CodeReq.Disjoint
      (CodeReq.singleton base (.ADDI .x10 .x0 k))
      (CodeReq.singleton (base + 4) (.BEQ .x5 .x10 offset)) :=
    CodeReq.Disjoint.singleton (by bv_omega) _ _
  have s1 := addi_spec_gen .x10 .x0 v10 0 k base (by nofun)
  have s1' : cpsTriple base (base + 4) (CodeReq.singleton base (.ADDI .x10 .x0 k))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 k))) :=
    cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTriple_frame_left _ _ _ _ _ (.x5 ↦ᵣ v5) (by pcFree) s1)
  have s2_raw := beq_spec_gen .x5 .x10 offset v5 ((0 : Word) + signExtend12 k) (base + 4)
  rw [htarget, ha1] at s2_raw
  have s2' : cpsBranch (base + 4) (CodeReq.singleton (base + 4) (.BEQ .x5 .x10 offset))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)))
      target ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)) ** ⌜v5 = (0 : Word) + signExtend12 k⌝)
      (base + 8) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)) ** ⌜v5 ≠ (0 : Word) + signExtend12 k⌝) :=
    cpsBranch_consequence _ _ _ _
      target _ _ (base + 8) _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsBranch_frame_left _ _ _ _ _ _ _ (.x0 ↦ᵣ (0 : Word)) (by pcFree) s2_raw)
  exact cpsTriple_seq_cpsBranch_with_perm _ _ _ _ hd _ _ _ target _ (base + 8) _
    (fun _ hp => hp) s1' s2'

-- ============================================================================
-- Phase C with pure dispatch facts
-- ============================================================================

set_option maxHeartbeats 6400000 in
/-- Phase C spec with pure dispatch facts: each exit postcondition includes
    the constraint that identifies which branch was taken. -/
theorem signext_phase_c_spec_pure (v5 v10 : Word) (base : Addr)
    (e0 e1 e2 e3 : Addr)
    (he0 : base + signExtend13 100 = e0)
    (he1 : (base + 8) + signExtend13 60 = e1)
    (he2 : (base + 16) + signExtend13 24 = e2)
    (he3 : base + 20 = e3) :
    let code := signext_phase_c_code base
    cpsNBranch base code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      [(e0, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** ⌜v5 = 0⌝),
       (e1, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 = (0 : Word) + signExtend12 1⌝),
       (e2, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 = (0 : Word) + signExtend12 2⌝),
       (e3, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1 ∧ v5 ≠ (0 : Word) + signExtend12 2⌝)] := by
  have hc1 : ((base + 4 : Addr) + 4) + signExtend13 60 = e1 := by
    rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]; exact he1
  have hc2 : ((base + 12 : Addr) + 4) + signExtend13 24 = e2 := by
    rw [show (base + 12 : Addr) + 4 = base + 16 from by bv_omega]; exact he2
  let cr_beq0 := CodeReq.singleton base (.BEQ .x5 .x0 100)
  let cr_cs1 := signext_cascade_step_code 1 60 (base + 4)
  let cr_cs2 := signext_cascade_step_code 2 24 (base + 12)
  have hd_beq0_cs1 : cr_beq0.Disjoint cr_cs1 :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega) _ _)
      (CodeReq.Disjoint.singleton (by bv_omega) _ _)
  have hd_beq0_cs2 : cr_beq0.Disjoint cr_cs2 :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega) _ _)
      (CodeReq.Disjoint.singleton (by bv_omega) _ _)
  have hd_cs1_cs2 : cr_cs1.Disjoint cr_cs2 :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton (by bv_omega) _ _)
        (CodeReq.Disjoint.singleton (by bv_omega) _ _))
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton (by bv_omega) _ _)
        (CodeReq.Disjoint.singleton (by bv_omega) _ _))
  -- Step 0: BEQ x5 x0 100
  have beq0_raw := beq_spec_gen .x5 .x0 100 v5 (0 : Word) base
  rw [he0] at beq0_raw
  have beq0f : cpsBranch base cr_beq0
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      e0 ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** ⌜v5 = 0⌝)
      (base + 4) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** ⌜v5 ≠ 0⌝) :=
    cpsBranch_consequence _ _ _ _ e0 _ _ (base + 4) _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsBranch_frame_left _ _ _ _ _ _ _ (.x10 ↦ᵣ v10) (by pcFree) beq0_raw)
  -- Step 1: cascade step at base+4
  have cs1_raw := signext_cascade_step_spec_pure v5 v10 1 60 (base + 4) e1 hc1
  rw [show (base + 4 : Addr) + 8 = base + 12 from by bv_omega] at cs1_raw
  have cs1f := cpsBranch_frame_left _ _ _ _ _ _ _ (⌜v5 ≠ (0 : Word)⌝) (pcFree_pure _) cs1_raw
  have cs1_clean : cpsBranch (base + 4) cr_cs1
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** ⌜v5 ≠ (0 : Word)⌝)
      e1 ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 = (0 : Word) + signExtend12 1⌝)
      (base + 12) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1⌝) :=
    cpsBranch_consequence _ _ _ _ e1 _ _ (base + 12) _ _
      (fun h hp => (congrFun (show _ = _ from by xperm) h).mp hp)
      (fun h hp => (sepConj_pure_right _ _ h).1 hp |>.1)
      (fun h hp => by
        have ⟨hinner, hne0⟩ := (sepConj_pure_right _ _ h).1 hp
        have hne1 := sepConj_extract_pure_end3 _ _ _ _ h hinner
        have hregs := sepConj_strip_pure_end3 _ _ _ _ h hinner
        exact (congrFun (show _ = _ from by xperm) h).mp
          ((sepConj_pure_right _ _ h).2 (And.intro hregs (And.intro hne0 hne1))))
      cs1f
  -- Step 2: cascade step at base+12
  have cs2_raw := signext_cascade_step_spec_pure v5 ((0 : Word) + signExtend12 1) 2 24 (base + 12) e2 hc2
  rw [show (base + 12 : Addr) + 8 = base + 20 from by bv_omega] at cs2_raw
  have cs2f := cpsBranch_frame_left _ _ _ _ _ _ _
    (⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1⌝) (pcFree_pure _) cs2_raw
  have cs2_clean : cpsBranch (base + 12) cr_cs2
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1⌝)
      e2 ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 = (0 : Word) + signExtend12 2⌝)
      (base + 20) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1 ∧ v5 ≠ (0 : Word) + signExtend12 2⌝) :=
    cpsBranch_consequence _ _ _ _ e2 _ _ (base + 20) _ _
      (fun h hp => (congrFun (show _ = _ from by xperm) h).mp hp)
      (fun h hp => (sepConj_pure_right _ _ h).1 hp |>.1)
      (fun h hp => by
        have ⟨hinner, ⟨hne0, hne1⟩⟩ := (sepConj_pure_right _ _ h).1 hp
        have hne2 := sepConj_extract_pure_end3 _ _ _ _ h hinner
        have hregs := sepConj_strip_pure_end3 _ _ _ _ h hinner
        exact (congrFun (show _ = _ from by xperm) h).mp
          ((sepConj_pure_right _ _ h).2 (And.intro hregs (And.intro hne0 (And.intro hne1 hne2)))))
      cs2f
  -- Fallthrough at base+20
  have ft := cpsNBranch_refl (base + 20)
    ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1 ∧ v5 ≠ (0 : Word) + signExtend12 2⌝)
    _ (fun _ hp => hp)
  have hunion_empty : ∀ (cr : CodeReq), cr.union CodeReq.empty = cr := by
    intro cr; funext a; simp only [CodeReq.union, CodeReq.empty]; cases cr a <;> rfl
  have n3 := cpsBranch_cons_cpsNBranch (base + 12) cr_cs2 CodeReq.empty
    (CodeReq.Disjoint.empty_right cr_cs2)
    _ e2 _ (base + 20) _ _ cs2_clean ft
  have hd_cs1_rest : cr_cs1.Disjoint (cr_cs2.union CodeReq.empty) := by
    rw [hunion_empty]; exact hd_cs1_cs2
  have n2 := cpsBranch_cons_cpsNBranch_with_perm (base + 4) cr_cs1 (cr_cs2.union CodeReq.empty)
    hd_cs1_rest _ e1 _ (base + 12) _ _ _
    (fun h hp => by xperm_hyp hp) cs1_clean n3
  have hd_beq0_rest : cr_beq0.Disjoint (cr_cs1.union (cr_cs2.union CodeReq.empty)) := by
    rw [hunion_empty]; exact CodeReq.Disjoint.union_right hd_beq0_cs1 hd_beq0_cs2
  have n1 := cpsBranch_cons_cpsNBranch_with_perm base cr_beq0 (cr_cs1.union (cr_cs2.union CodeReq.empty))
    hd_beq0_rest _ e0 _ (base + 4) _ _ _
    (fun h hp => by xperm_hyp hp) beq0f n2
  have hcr_eq : cr_beq0.union (cr_cs1.union (cr_cs2.union CodeReq.empty)) = signext_phase_c_code base := by
    simp only [hunion_empty]; rfl
  intro code
  have n1_rw := hcr_eq ▸ n1
  exact cpsNBranch_weaken_posts _ _ _ _ _ (cpsNBranch_weaken_pre _ _ _ _ _ (fun h hp => by xperm_hyp hp) n1_rw)
    (fun ex hmem => by
      simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false, false_or] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, List.Mem.head _, rfl, fun h hp => by xperm_hyp hp⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, fun h hp => by xperm_hyp hp⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl, fun h hp => by xperm_hyp hp⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))), he3.symm, fun h hp => by xperm_hyp hp⟩)

end EvmAsm.Rv64
