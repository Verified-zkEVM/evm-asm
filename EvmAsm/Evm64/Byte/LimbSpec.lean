/-
  EvmAsm.Evm64.Byte.LimbSpec

  CPS specifications for the 256-bit EVM BYTE program (64-bit).
  Modular decomposition:
  - Phase B: byte_phase_b_spec (5 instrs): compute bit_shift and limb_from_msb
  - body_3: extract from limb 0 at sp+32, JAL to store (4 instrs)
  - body_2: extract from limb 1 at sp+40, JAL to store (4 instrs)
  - body_1: extract from limb 2 at sp+48, JAL to store (4 instrs)
  - body_0: extract from limb 3 at sp+56, falls through to store (3 instrs)
  - store: pop index word, write byte result + 3 zero limbs (6 instrs)
  - zero_path: pop index word, write all zeros (5 instrs)
-/

import EvmAsm.Evm64.Byte.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Phase A: OR-reduce high index limbs (5 instructions, offset 0-16)
-- Uses full byte_phase_a code as CodeReq for composition.
-- ============================================================================

abbrev byte_phase_a_code (base : Addr) : CodeReq :=
  CodeReq.ofProg base byte_phase_a

/-- Phase A OR-reduce body: LD idx[1], LD idx[2], OR, LD idx[3], OR.
    Produces x5 = idx1 ||| idx2 ||| idx3. Uses full phase_a code. -/
theorem byte_phase_a_or_reduce_spec (sp v5 v10 idx1 idx2 idx3 : Word) (base : Addr)
    (hv1 : isValidDwordAccess (sp + signExtend12 (8 : BitVec 12)) = true)
    (hv2 : isValidDwordAccess (sp + signExtend12 (16 : BitVec 12)) = true)
    (hv3 : isValidDwordAccess (sp + signExtend12 (24 : BitVec 12)) = true) :
    let or_high := idx1 ||| idx2 ||| idx3
    let cr := byte_phase_a_code base
    cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 8) ↦ₘ idx1) **
       ((sp + signExtend12 16) ↦ₘ idx2) **
       ((sp + signExtend12 24) ↦ₘ idx3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ or_high) ** (.x10 ↦ᵣ idx3) **
       ((sp + signExtend12 8) ↦ₘ idx1) **
       ((sp + signExtend12 16) ↦ₘ idx2) **
       ((sp + signExtend12 24) ↦ₘ idx3)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 idx1 8 base (by nofun) hv1
  have I1 := ld_spec_gen .x10 .x12 sp v10 idx2 16 (base + 4) (by nofun) hv2
  have I2 := or_spec_gen_rd_eq_rs1 .x5 .x10 idx1 idx2 (base + 8) (by nofun)
  have I3 := ld_spec_gen .x10 .x12 sp idx2 idx3 24 (base + 12) (by nofun) hv3
  have I4 := or_spec_gen_rd_eq_rs1 .x5 .x10 (idx1 ||| idx2) idx3 (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

-- ============================================================================
-- Phase A: Load idx[0] and check < 32 (2 instructions, offset 24-28)
-- ============================================================================

/-- Phase A low-check: LD idx[0] into x5, SLTIU x10 = (idx0 < 32).
    Located at offset 24 within byte_phase_a (after OR-reduce + BNE). -/
theorem byte_phase_a_low_check_spec (sp v5 idx0 v10 : Word) (base : Addr)
    (hvalid : isValidDwordAccess (sp + signExtend12 (0 : BitVec 12)) = true) :
    let cr := byte_phase_a_code base
    cpsTriple (base + 24) (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 0) ↦ₘ idx0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ idx0) **
       (.x10 ↦ᵣ (if BitVec.ult idx0 (signExtend12 32) then (1 : Word) else 0)) **
       ((sp + signExtend12 0) ↦ₘ idx0)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 idx0 0 (base + 24) (by nofun) hvalid
  have I1 := sltiu_spec_gen .x10 .x5 v10 idx0 32 (base + 28) (by nofun)
  runBlock I0 I1

-- ============================================================================
-- Phase B: Compute bit_shift and limb_from_msb (5 instructions)
-- Same computation as SignExtend Phase B
-- ============================================================================

abbrev byte_phase_b_code (base : Addr) : CodeReq :=
  CodeReq.ofProg base byte_phase_b

/-- Phase B spec: compute byte extraction parameters.
    ANDI x10,x5,7; SLLI x10,x10,3; ADDI x6,x0,56;
    SUB x6,x6,x10; SRLI x5,x5,3.
    Outputs: x6 = 56 - (idx%8)*8 (bit_shift), x5 = idx/8 (limb_from_msb). -/
theorem byte_phase_b_spec (idx r6 r10 : Word) (base : Addr) :
    let byte_in_limb := idx &&& signExtend12 (7 : BitVec 12)
    let byte_shift := byte_in_limb <<< (3 : BitVec 6).toNat
    let shift_amount := (56 : Word) - byte_shift
    let limb_from_msb := idx >>> (3 : BitVec 6).toNat
    let code := byte_phase_b_code base
    cpsTriple base (base + 20) code
      ((.x5 ↦ᵣ idx) ** (.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10))
      ((.x5 ↦ᵣ limb_from_msb) ** (.x6 ↦ᵣ shift_amount) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ byte_shift)) := by
  have A := andi_spec_gen .x10 .x5 r10 idx 7 base (by nofun)
  have SL := slli_spec_gen_same .x10 (idx &&& signExtend12 7) 3 (base + 4) (by nofun)
  have AD := addi_x0_spec_gen .x6 r6 56 (base + 8) (by nofun)
  have SU := sub_spec_gen_rd_eq_rs1 .x6 .x10 (signExtend12 56)
    ((idx &&& signExtend12 7) <<< (3 : BitVec 6).toNat) (base + 12) (by nofun)
  have SR := srli_spec_gen_same .x5 idx 3 (base + 16) (by nofun)
  runBlock A SL AD SU SR

-- ============================================================================
-- Body specs: extract byte from limb (LD + SRL + ANDI 0xFF + optional JAL)
-- ============================================================================

-- body_3: LD sp+32, SRL, ANDI 0xFF, JAL 48 (4 instrs)
-- limb_from_msb = 3 → extract from limb 0 (LSB) at sp+32

abbrev byte_body_3_code (base : Addr) : CodeReq :=
  CodeReq.ofProg base byte_body_3

/-- body_3 spec: load limb 0 from sp+32, extract byte, jump to store. -/
theorem byte_body_3_spec (sp v5 shift_amount limb : Word) (base : Addr)
    (hvalid : isValidDwordAccess (sp + signExtend12 (32 : BitVec 12)) = true) :
    let result := (limb >>> (shift_amount.toNat % 64)) &&& signExtend12 (255 : BitVec 12)
    let code := byte_body_3_code base
    cpsTriple base ((base + 12) + signExtend21 (48 : BitVec 21)) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift_amount) **
       ((sp + signExtend12 32) ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift_amount) **
       ((sp + signExtend12 32) ↦ₘ limb)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 limb 32 base (by nofun) hvalid
  have I1 := srl_spec_gen_rd_eq_rs1 .x5 .x6 limb shift_amount (base + 4) (by nofun)
  have I2 := andi_spec_gen_same .x5 (limb >>> (shift_amount.toNat % 64)) 255 (base + 8) (by nofun)
  have I3 := jal_x0_spec_gen (48 : BitVec 21) (base + 12)
  runBlock I0 I1 I2 I3

-- body_2: LD sp+40, SRL, ANDI 0xFF, JAL 32 (4 instrs)
-- limb_from_msb = 2 → extract from limb 1 at sp+40

abbrev byte_body_2_code (base : Addr) : CodeReq :=
  CodeReq.ofProg base byte_body_2

/-- body_2 spec: load limb 1 from sp+40, extract byte, jump to store. -/
theorem byte_body_2_spec (sp v5 shift_amount limb : Word) (base : Addr)
    (hvalid : isValidDwordAccess (sp + signExtend12 (40 : BitVec 12)) = true) :
    let result := (limb >>> (shift_amount.toNat % 64)) &&& signExtend12 (255 : BitVec 12)
    let code := byte_body_2_code base
    cpsTriple base ((base + 12) + signExtend21 (32 : BitVec 21)) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift_amount) **
       ((sp + signExtend12 40) ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift_amount) **
       ((sp + signExtend12 40) ↦ₘ limb)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 limb 40 base (by nofun) hvalid
  have I1 := srl_spec_gen_rd_eq_rs1 .x5 .x6 limb shift_amount (base + 4) (by nofun)
  have I2 := andi_spec_gen_same .x5 (limb >>> (shift_amount.toNat % 64)) 255 (base + 8) (by nofun)
  have I3 := jal_x0_spec_gen (32 : BitVec 21) (base + 12)
  runBlock I0 I1 I2 I3

-- body_1: LD sp+48, SRL, ANDI 0xFF, JAL 16 (4 instrs)
-- limb_from_msb = 1 → extract from limb 2 at sp+48

abbrev byte_body_1_code (base : Addr) : CodeReq :=
  CodeReq.ofProg base byte_body_1

/-- body_1 spec: load limb 2 from sp+48, extract byte, jump to store. -/
theorem byte_body_1_spec (sp v5 shift_amount limb : Word) (base : Addr)
    (hvalid : isValidDwordAccess (sp + signExtend12 (48 : BitVec 12)) = true) :
    let result := (limb >>> (shift_amount.toNat % 64)) &&& signExtend12 (255 : BitVec 12)
    let code := byte_body_1_code base
    cpsTriple base ((base + 12) + signExtend21 (16 : BitVec 21)) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift_amount) **
       ((sp + signExtend12 48) ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift_amount) **
       ((sp + signExtend12 48) ↦ₘ limb)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 limb 48 base (by nofun) hvalid
  have I1 := srl_spec_gen_rd_eq_rs1 .x5 .x6 limb shift_amount (base + 4) (by nofun)
  have I2 := andi_spec_gen_same .x5 (limb >>> (shift_amount.toNat % 64)) 255 (base + 8) (by nofun)
  have I3 := jal_x0_spec_gen (16 : BitVec 21) (base + 12)
  runBlock I0 I1 I2 I3

-- body_0: LD sp+56, SRL, ANDI 0xFF (3 instrs, falls through to store)
-- limb_from_msb = 0 → extract from limb 3 (MSB) at sp+56

abbrev byte_body_0_code (base : Addr) : CodeReq :=
  CodeReq.ofProg base byte_body_0

/-- body_0 spec: load limb 3 from sp+56, extract byte. Falls through to store. -/
theorem byte_body_0_spec (sp v5 shift_amount limb : Word) (base : Addr)
    (hvalid : isValidDwordAccess (sp + signExtend12 (56 : BitVec 12)) = true) :
    let result := (limb >>> (shift_amount.toNat % 64)) &&& signExtend12 (255 : BitVec 12)
    let code := byte_body_0_code base
    cpsTriple base (base + 12) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ shift_amount) **
       ((sp + signExtend12 56) ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ shift_amount) **
       ((sp + signExtend12 56) ↦ₘ limb)) := by
  have I0 := ld_spec_gen .x5 .x12 sp v5 limb 56 base (by nofun) hvalid
  have I1 := srl_spec_gen_rd_eq_rs1 .x5 .x6 limb shift_amount (base + 4) (by nofun)
  have I2 := andi_spec_gen_same .x5 (limb >>> (shift_amount.toNat % 64)) 255 (base + 8) (by nofun)
  runBlock I0 I1 I2

-- ============================================================================
-- Store: pop index word, write byte result + 3 zero limbs (6 instrs)
-- ============================================================================

abbrev byte_store_code (base : Addr) : CodeReq :=
  CodeReq.ofProg base byte_store

/-- Store spec: ADDI x12 32, SD result, SD 0×3, JAL 24.
    Pops the index word (sp → sp+32), writes result at sp+32 and zeros at sp+40..56. -/
theorem byte_store_spec (sp result m0 m8 m16 m24 : Word) (base : Addr)
    (hvalid : ValidMemRange sp 8) :
    let nsp := sp + signExtend12 (32 : BitVec 12)
    let code := byte_store_code base
    cpsTriple base ((base + 20) + signExtend21 (24 : BitVec 21)) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ nsp) ** (.x5 ↦ᵣ result) **
       ((sp + 32) ↦ₘ result) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  have I0 := addi_spec_gen_same .x12 sp 32 base (by nofun)
  have I1 := sd_spec_gen .x12 .x5 (sp + signExtend12 32) result m0 0 (base + 4) (by validMem)
  have I2 := sd_x0_spec_gen .x12 (sp + signExtend12 32) m8 8 (base + 8) (by validMem)
  have I3 := sd_x0_spec_gen .x12 (sp + signExtend12 32) m16 16 (base + 12) (by validMem)
  have I4 := sd_x0_spec_gen .x12 (sp + signExtend12 32) m24 24 (base + 16) (by validMem)
  have I5 := jal_x0_spec_gen (24 : BitVec 21) (base + 20)
  runBlock I0 I1 I2 I3 I4 I5

-- ============================================================================
-- Zero path: pop index word, write all zeros (5 instrs)
-- ============================================================================

abbrev byte_zero_path_code (base : Addr) : CodeReq :=
  CodeReq.ofProg base byte_zero_path

/-- Zero path spec: ADDI x12 32, SD 0×4.
    Pops the index word (sp → sp+32), writes zeros at sp+32..56. -/
theorem byte_zero_path_spec (sp m0 m8 m16 m24 : Word) (base : Addr)
    (hvalid : ValidMemRange sp 8) :
    let nsp := sp + signExtend12 (32 : BitVec 12)
    let code := byte_zero_path_code base
    cpsTriple base (base + 20) code
      ((.x12 ↦ᵣ sp) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ nsp) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  have I0 := addi_spec_gen_same .x12 sp 32 base (by nofun)
  have I1 := sd_x0_spec_gen .x12 (sp + signExtend12 32) m0 0 (base + 4) (by validMem)
  have I2 := sd_x0_spec_gen .x12 (sp + signExtend12 32) m8 8 (base + 8) (by validMem)
  have I3 := sd_x0_spec_gen .x12 (sp + signExtend12 32) m16 16 (base + 12) (by validMem)
  have I4 := sd_x0_spec_gen .x12 (sp + signExtend12 32) m24 24 (base + 16) (by validMem)
  runBlock I0 I1 I2 I3 I4

end EvmAsm.Rv64
