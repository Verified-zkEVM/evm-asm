/-
  EvmAsm.Evm64.SignExtendSpec

  CPS specifications for the 256-bit EVM SIGNEXTEND program (64-bit).
  Modular decomposition:
  - Per-body helper: signext_inplace_spec (4 instrs): LD + SLL + SRA + SD
  - Body specs: signext_body_N_spec for N = 0..3
  - Done spec: signext_done_spec (1 instr): ADDI x12, x12, 32
  - Phase B: signext_phase_b_spec (5 instrs, same computation as BYTE Phase B)
-/

import EvmAsm.Evm64.SignExtend
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

set_option maxHeartbeats 800000

-- ============================================================================
-- Per-body Helper: Sign-extend in-place (4 instructions)
-- ============================================================================

/-- CodeReq for sign-extend in-place (4 instructions):
    LD x5, off(x12); SLL x5,x5,x6; SRA x5,x5,x6; SD x12,x5,off -/
abbrev signext_inplace_code (off : BitVec 12) (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 off))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SLL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SRA .x5 .x5 .x6))
   (CodeReq.singleton (base + 12) (.SD .x12 .x5 off))))

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
  have SL := sll_spec_gen_rd_eq_rs1 .x5 .x6 limb shift_amount (base + 4) (by nofun) (by nofun)
  have SR := sra_spec_gen_rd_eq_rs1 .x5 .x6 (limb <<< (shift_amount.toNat % 64)) shift_amount (base + 8) (by nofun) (by nofun)
  have SD_ := sd_spec_gen .x12 .x5 sp (BitVec.sshiftRight (limb <<< (shift_amount.toNat % 64)) (shift_amount.toNat % 64)) limb off (base + 12) hvalid
  runBlock L SL SR SD_

-- ============================================================================
-- Body Specs
-- ============================================================================

/-- CodeReq for sign-extend body 3 (5 instructions):
    LD + SLL + SRA + SD at sp+56 + JAL. -/
abbrev signext_body_3_code (base : Addr) (jal_off : BitVec 21) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 56))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SLL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SRA .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x5 56))
   (CodeReq.singleton (base + 16) (.JAL .x0 jal_off)))))

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
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 48))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SLL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SRA .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x5 48))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SRAI .x10 .x5 63))
  (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x10 56))
   (CodeReq.singleton (base + 24) (.JAL .x0 jal_off)))))))

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
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 40))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SLL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SRA .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x5 40))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SRAI .x10 .x5 63))
  (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x10 48))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SD .x12 .x10 56))
   (CodeReq.singleton (base + 28) (.JAL .x0 jal_off))))))))

set_option maxHeartbeats 1600000 in
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
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 32))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SLL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SRA .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x5 32))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SRAI .x10 .x5 63))
  (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x10 40))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SD .x12 .x10 48))
   (CodeReq.singleton (base + 28) (.SD .x12 .x10 56))))))))

set_option maxHeartbeats 1600000 in
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

set_option maxHeartbeats 1600000 in
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
    ((b &&& signExtend12 7) <<< (3 : BitVec 6).toNat) (base + 12) (by nofun) (by nofun)
  have SR := srli_spec_gen_same .x5 b 3 (base + 16) (by nofun)
  runBlock A SL AD SU SR

end EvmAsm.Rv64
