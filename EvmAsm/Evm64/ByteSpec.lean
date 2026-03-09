/-
  EvmAsm.Evm64.ByteSpec

  CPS specifications for the 256-bit EVM BYTE (extract byte) program (64-bit).
  Modular decomposition:
  - Per-body helpers: byte_extract_spec (3 instrs): LD + SRL + ANDI
  - Body specs: byte_body_N_spec for N = 0..3 (extract + JAL to store)
  - Store path: byte_store_spec (6 instrs): ADDI + 4×SD + JAL
  - Zero path: reuses shr_zero_path_spec from ShiftSpec
  - Phase B: byte_phase_b_spec (5 instrs)
-/

import EvmAsm.Evm64.Byte
import EvmAsm.Evm64.ShiftSpec  -- for shr_zero_path_spec, shr_phase_a_spec, etc.

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

set_option maxHeartbeats 800000

-- ============================================================================
-- Per-body Helper: Byte Extraction (3 instructions)
-- ============================================================================

/-- Byte extraction spec (3 instructions):
    LD x5, off(x12); SRL x5,x5,x6; ANDI x5,x5,255

    Loads a 64-bit limb from memory, shifts right by bit_shift, masks to byte.
    Result = (limb >>> (bit_shift.toNat % 64)) &&& signExtend12 255 -/
theorem byte_extract_spec (off : BitVec 12)
    (sp limb v5 bit_shift : Word) (base : Addr)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let result := (limb >>> (bit_shift.toNat % 64)) &&& signExtend12 (255 : BitVec 12)
    let code :=
      (base ↦ᵢ .LD .x5 .x12 off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
      ((base + 8) ↦ᵢ .ANDI .x5 .x5 255)
    cpsTriple base (base + 12)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       ((sp + signExtend12 off) ↦ₘ limb))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       ((sp + signExtend12 off) ↦ₘ limb)) := by
  have L := ld_spec_gen .x5 .x12 sp v5 limb off base (by nofun) hvalid
  have S := srl_spec_gen_rd_eq_rs1 .x5 .x6 limb bit_shift (base + 4) (by nofun) (by nofun)
  have A := andi_spec_gen_same .x5 (limb >>> (bit_shift.toNat % 64)) 255 (base + 8) (by nofun)
  runBlock L S A

-- ============================================================================
-- Body Specs (extract + JAL for bodies 1-3, extract only for body 0)
-- ============================================================================

/-- Body 3: limb_from_msb=3, extract byte from limb 0 at sp+32.
    4 instructions: LD + SRL + ANDI + JAL. -/
theorem byte_body_3_spec (sp : Word)
    (v5 v10 bit_shift : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 12) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result := (v0 >>> (bit_shift.toNat % 64)) &&& signExtend12 (255 : BitVec 12)
    let code :=
      (base ↦ᵢ .LD .x5 .x12 32) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
      ((base + 8) ↦ᵢ .ANDI .x5 .x5 255) ** ((base + 12) ↦ᵢ .JAL .x0 jal_off)
    cpsTriple base exit
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       ((sp + 32) ↦ₘ v0))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       ((sp + 32) ↦ₘ v0)) := by
  have EX := byte_extract_spec 32 sp v0 v5 bit_shift base (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 12)
  rw [hexit] at JL
  runBlock EX JL

/-- Body 2: limb_from_msb=2, extract byte from limb 1 at sp+40.
    4 instructions: LD + SRL + ANDI + JAL. -/
theorem byte_body_2_spec (sp : Word)
    (v5 v10 bit_shift : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 12) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result := (v1 >>> (bit_shift.toNat % 64)) &&& signExtend12 (255 : BitVec 12)
    let code :=
      (base ↦ᵢ .LD .x5 .x12 40) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
      ((base + 8) ↦ᵢ .ANDI .x5 .x5 255) ** ((base + 12) ↦ᵢ .JAL .x0 jal_off)
    cpsTriple base exit
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       ((sp + 40) ↦ₘ v1))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       ((sp + 40) ↦ₘ v1)) := by
  have EX := byte_extract_spec 40 sp v1 v5 bit_shift base (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 12)
  rw [hexit] at JL
  runBlock EX JL

/-- Body 1: limb_from_msb=1, extract byte from limb 2 at sp+48.
    4 instructions: LD + SRL + ANDI + JAL. -/
theorem byte_body_1_spec (sp : Word)
    (v5 v10 bit_shift : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 12) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result := (v2 >>> (bit_shift.toNat % 64)) &&& signExtend12 (255 : BitVec 12)
    let code :=
      (base ↦ᵢ .LD .x5 .x12 48) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
      ((base + 8) ↦ᵢ .ANDI .x5 .x5 255) ** ((base + 12) ↦ᵢ .JAL .x0 jal_off)
    cpsTriple base exit
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       ((sp + 48) ↦ₘ v2))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       ((sp + 48) ↦ₘ v2)) := by
  have EX := byte_extract_spec 48 sp v2 v5 bit_shift base (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 12)
  rw [hexit] at JL
  runBlock EX JL

/-- Body 0: limb_from_msb=0, extract byte from limb 3 at sp+56.
    3 instructions: LD + SRL + ANDI (falls through to store). -/
theorem byte_body_0_spec (sp : Word)
    (v5 v10 bit_shift : Word)
    (v0 v1 v2 v3 : Word)
    (base : Addr)
    (hvalid : ValidMemRange sp 8) :
    let result := (v3 >>> (bit_shift.toNat % 64)) &&& signExtend12 (255 : BitVec 12)
    let code :=
      (base ↦ᵢ .LD .x5 .x12 56) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
      ((base + 8) ↦ᵢ .ANDI .x5 .x5 255)
    cpsTriple base (base + 12)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       ((sp + 56) ↦ₘ v3))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       ((sp + 56) ↦ₘ v3)) := by
  exact byte_extract_spec 56 sp v3 v5 bit_shift base (by validMem)

-- ============================================================================
-- Store Path Spec (6 instructions): ADDI + 4×SD + JAL
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Store path spec: pop index word, write byte result + 3 zeros, jump to exit.
    6 instructions: ADDI x12,x12,32; SD x12,x5,0; SD x12,x0,8;
    SD x12,x0,16; SD x12,x0,24; JAL x0,jal_off -/
theorem byte_store_spec (sp byte_result : Word)
    (d0 d1 d2 d3 : Word)   -- old values at result locations
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 20) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange (sp + 32) 4) :
    let nsp := sp + 32
    let code :=
      (base ↦ᵢ .ADDI .x12 .x12 32) ** ((base + 4) ↦ᵢ .SD .x12 .x5 0) **
      ((base + 8) ↦ᵢ .SD .x12 .x0 8) ** ((base + 12) ↦ᵢ .SD .x12 .x0 16) **
      ((base + 16) ↦ᵢ .SD .x12 .x0 24) ** ((base + 20) ↦ᵢ .JAL .x0 jal_off)
    cpsTriple base exit
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ byte_result) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3))
      (code **
       (.x12 ↦ᵣ nsp) ** (.x5 ↦ᵣ byte_result) **
       (nsp ↦ₘ byte_result) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0)) := by
  intro nsp
  have A := addi_spec_gen_same .x12 sp 32 base (by nofun)
  rw [show sp + signExtend12 (32 : BitVec 12) = nsp from by simp only [signExtend12_32]; rfl] at A
  have S0 := sd_spec_gen .x12 .x5 nsp byte_result d0 0 (base + 4) (by validMem)
  have S1 := sd_x0_spec_gen .x12 nsp d1 8 (base + 8) (by validMem)
  have S2 := sd_x0_spec_gen .x12 nsp d2 16 (base + 12) (by validMem)
  have S3 := sd_x0_spec_gen .x12 nsp d3 24 (base + 16) (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 20)
  rw [hexit] at JL
  runBlock A S0 S1 S2 S3 JL

-- ============================================================================
-- Phase B Spec: Compute bit_shift and limb_from_msb (5 instructions)
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- Phase B spec: compute byte extraction parameters.
    ANDI x10,x5,7; SLLI x10,x10,3; ADDI x6,x0,56;
    SUB x6,x6,x10; SRLI x5,x5,3.
    Outputs: x6 = 56 - (index%8)*8, x5 = index/8. -/
theorem byte_phase_b_spec (index r6 r10 : Word) (base : Addr) :
    let byte_in_limb := index &&& signExtend12 (7 : BitVec 12)
    let byte_shift := byte_in_limb <<< (3 : BitVec 6).toNat
    let bit_shift := (56 : Word) - byte_shift
    let limb_from_msb := index >>> (3 : BitVec 6).toNat
    let code :=
      (base ↦ᵢ .ANDI .x10 .x5 7) ** ((base + 4) ↦ᵢ .SLLI .x10 .x10 3) **
      ((base + 8) ↦ᵢ .ADDI .x6 .x0 56) ** ((base + 12) ↦ᵢ .SUB .x6 .x6 .x10) **
      ((base + 16) ↦ᵢ .SRLI .x5 .x5 3)
    cpsTriple base (base + 20)
      (code **
       (.x5 ↦ᵣ index) ** (.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10))
      (code **
       (.x5 ↦ᵣ limb_from_msb) ** (.x6 ↦ᵣ bit_shift) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ byte_shift)) := by
  runBlock

end EvmAsm.Rv64
