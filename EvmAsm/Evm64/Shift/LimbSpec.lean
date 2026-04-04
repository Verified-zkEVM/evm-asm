/-
  EvmAsm.Evm64.Shift.LimbSpec

  CPS specifications for the 256-bit EVM SHR (logical shift right) program (64-bit).
  Modern CodeReq-based approach.

  Modular decomposition:
  - Per-limb helpers: shr_merge_limb_spec (7 instrs), shr_last_limb_spec (3 instrs)
  - Zero path: shr_zero_path_spec (5 instrs, shift >= 256)
  - Phase B: shr_phase_b_spec (7 instrs, extract parameters)
  - Cascade step: shr_cascade_step_spec (2 instrs)
  - Phase C: shr_phase_c_spec (5 instrs, cascade dispatch)
  - LD/OR accumulator: shr_ld_or_acc_spec (2 instrs)
  - Phase A: shr_phase_a_spec (9 instrs, check shift >= 256)
  - Shift bodies: shr_body_L_spec for L = 0..3
-/

import EvmAsm.Evm64.Shift.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Section 1: Per-limb Helpers
-- ============================================================================

-- SHR Merge Limb (7 instructions)

abbrev shr_merge_limb_code (src_off next_off dst_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (shr_merge_limb_prog src_off next_off dst_off)

theorem shr_merge_limb_spec (src_off next_off dst_off : BitVec 12)
    (sp src next dst_old v5 v10 bit_shift anti_shift mask : Word) (base : Word)
    (hvalid_src : isValidDwordAccess (sp + signExtend12 src_off) = true)
    (hvalid_next : isValidDwordAccess (sp + signExtend12 next_off) = true)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 dst_off) = true) :
    let mem_src := sp + signExtend12 src_off
    let mem_next := sp + signExtend12 next_off
    let mem_dst := sp + signExtend12 dst_off
    let shifted_src := src >>> (bit_shift.toNat % 64)
    let shifted_next := (next <<< (anti_shift.toNat % 64)) &&& mask
    let result := shifted_src ||| shifted_next
    let code := shr_merge_limb_code src_off next_off dst_off base
    cpsTriple base (base + 28) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (mem_src ↦ₘ src) ** (mem_next ↦ₘ next) ** (mem_dst ↦ₘ dst_old))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ shifted_next) ** (.x11 ↦ᵣ mask) **
       (mem_src ↦ₘ src) ** (mem_next ↦ₘ next) ** (mem_dst ↦ₘ result)) := by
  have L1 := ld_spec_gen .x5 .x12 sp v5 src src_off base (by nofun) hvalid_src
  have SR := srl_spec_gen_rd_eq_rs1 .x5 .x6 src bit_shift (base + 4) (by nofun)
  have L2 := ld_spec_gen .x10 .x12 sp v10 next next_off (base + 8) (by nofun) hvalid_next
  have SL := sll_spec_gen_rd_eq_rs1 .x10 .x7 next anti_shift (base + 12) (by nofun)
  have AN := and_spec_gen_rd_eq_rs1 .x10 .x11 (next <<< (anti_shift.toNat % 64)) mask (base + 16) (by nofun)
  have OR_ := or_spec_gen_rd_eq_rs1 .x5 .x10 (src >>> (bit_shift.toNat % 64)) ((next <<< (anti_shift.toNat % 64)) &&& mask) (base + 20) (by nofun)
  have SD_ := sd_spec_gen .x12 .x5 sp ((src >>> (bit_shift.toNat % 64)) ||| ((next <<< (anti_shift.toNat % 64)) &&& mask)) dst_old dst_off (base + 24) hvalid_dst
  runBlock L1 SR L2 SL AN OR_ SD_

-- SHR Last Limb (3 instructions)

abbrev shr_last_limb_code (dst_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (shr_last_limb_prog dst_off)

theorem shr_last_limb_spec (dst_off : BitVec 12)
    (sp src dst_old v5 bit_shift : Word) (base : Word)
    (hvalid_src : isValidDwordAccess (sp + signExtend12 (24 : BitVec 12)) = true)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 dst_off) = true) :
    let mem_src := sp + signExtend12 (24 : BitVec 12)
    let mem_dst := sp + signExtend12 dst_off
    let result := src >>> (bit_shift.toNat % 64)
    let code := shr_last_limb_code dst_off base
    cpsTriple base (base + 12) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (mem_src ↦ₘ src) ** (mem_dst ↦ₘ dst_old))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (mem_src ↦ₘ src) ** (mem_dst ↦ₘ result)) := by
  have L := ld_spec_gen .x5 .x12 sp v5 src 24 base (by nofun) hvalid_src
  have SR := srl_spec_gen_rd_eq_rs1 .x5 .x6 src bit_shift (base + 4) (by nofun)
  have SD_ := sd_spec_gen .x12 .x5 sp (src >>> (bit_shift.toNat % 64)) dst_old dst_off (base + 8) hvalid_dst
  runBlock L SR SD_

-- SHR Merge Limb In-place (7 instructions, src_off = dst_off)

abbrev shr_merge_limb_inplace_code (off next_off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (shr_merge_limb_inplace_prog off next_off)

theorem shr_merge_limb_inplace_spec (off next_off : BitVec 12)
    (sp src next v5 v10 bit_shift anti_shift mask : Word) (base : Word)
    (hvalid_loc : isValidDwordAccess (sp + signExtend12 off) = true)
    (hvalid_next : isValidDwordAccess (sp + signExtend12 next_off) = true) :
    let mem_loc := sp + signExtend12 off
    let mem_next := sp + signExtend12 next_off
    let shifted_src := src >>> (bit_shift.toNat % 64)
    let shifted_next := (next <<< (anti_shift.toNat % 64)) &&& mask
    let result := shifted_src ||| shifted_next
    let code := shr_merge_limb_inplace_code off next_off base
    cpsTriple base (base + 28) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (mem_loc ↦ₘ src) ** (mem_next ↦ₘ next))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ shifted_next) ** (.x11 ↦ᵣ mask) **
       (mem_loc ↦ₘ result) ** (mem_next ↦ₘ next)) := by
  have L1 := ld_spec_gen .x5 .x12 sp v5 src off base (by nofun) hvalid_loc
  have SR := srl_spec_gen_rd_eq_rs1 .x5 .x6 src bit_shift (base + 4) (by nofun)
  have L2 := ld_spec_gen .x10 .x12 sp v10 next next_off (base + 8) (by nofun) hvalid_next
  have SL := sll_spec_gen_rd_eq_rs1 .x10 .x7 next anti_shift (base + 12) (by nofun)
  have AN := and_spec_gen_rd_eq_rs1 .x10 .x11 (next <<< (anti_shift.toNat % 64)) mask (base + 16) (by nofun)
  have OR_ := or_spec_gen_rd_eq_rs1 .x5 .x10 (src >>> (bit_shift.toNat % 64)) ((next <<< (anti_shift.toNat % 64)) &&& mask) (base + 20) (by nofun)
  have SD_ := sd_spec_gen .x12 .x5 sp ((src >>> (bit_shift.toNat % 64)) ||| ((next <<< (anti_shift.toNat % 64)) &&& mask)) src off (base + 24) hvalid_loc
  runBlock L1 SR L2 SL AN OR_ SD_

-- SHR Last Limb In-place (3 instructions, dst_off = 24)

abbrev shr_last_limb_inplace_code (base : Word) : CodeReq :=
  CodeReq.ofProg base shr_last_limb_inplace_prog

theorem shr_last_limb_inplace_spec
    (sp src v5 bit_shift : Word) (base : Word)
    (hvalid : isValidDwordAccess (sp + signExtend12 (24 : BitVec 12)) = true) :
    let mem := sp + signExtend12 (24 : BitVec 12)
    let result := src >>> (bit_shift.toNat % 64)
    let code := shr_last_limb_inplace_code base
    cpsTriple base (base + 12) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ src))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ result)) := by
  have L := ld_spec_gen .x5 .x12 sp v5 src 24 base (by nofun) hvalid
  have SR := srl_spec_gen_rd_eq_rs1 .x5 .x6 src bit_shift (base + 4) (by nofun)
  have SD_ := sd_spec_gen .x12 .x5 sp (src >>> (bit_shift.toNat % 64)) src 24 (base + 8) hvalid
  runBlock L SR SD_

-- ============================================================================
-- Section 2: Zero Path (5 instructions)
-- ============================================================================

abbrev shr_zero_path_code (base : Word) : CodeReq :=
  CodeReq.ofProg base shr_zero_path

set_option maxHeartbeats 3200000 in
theorem shr_zero_path_spec (sp : Word)
    (d0 d1 d2 d3 : Word)
    (base : Word)
    (hvalid : ValidMemRange (sp + 32) 4) :
    let nsp := sp + 32
    let code := shr_zero_path_code base
    cpsTriple base (base + 20) code
      ((.x12 ↦ᵣ sp) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3))
      ((.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0)) := by
  intro nsp
  have A := addi_spec_gen_same .x12 sp 32 base (by nofun)
  rw [show sp + signExtend12 (32 : BitVec 12) = nsp from by simp only [signExtend12_32]; rfl] at A
  have S0 := sd_x0_spec_gen .x12 nsp d0 0 (base + 4) (by validMem)
  have S1 := sd_x0_spec_gen .x12 nsp d1 8 (base + 8) (by validMem)
  have S2 := sd_x0_spec_gen .x12 nsp d2 16 (base + 12) (by validMem)
  have S3 := sd_x0_spec_gen .x12 nsp d3 24 (base + 16) (by validMem)
  runBlock A S0 S1 S2 S3

-- ============================================================================
-- Section 3: Phase B (7 instructions)
-- ============================================================================

abbrev shr_phase_b_code (base : Word) : CodeReq :=
  CodeReq.ofProg base shr_phase_b

set_option maxHeartbeats 1600000 in
theorem shr_phase_b_spec (shift0 sp r6 r7 r11 : Word) (base : Word) :
    let bit_shift := shift0 &&& signExtend12 63
    let limb_shift := shift0 >>> (6 : BitVec 6).toNat
    let cond := if BitVec.ult (0 : Word) bit_shift then (1 : Word) else 0
    let mask := (0 : Word) - cond
    let anti_shift := (64 : Word) - bit_shift
    let code := shr_phase_b_code base
    cpsTriple base (base + 28) code
      ((.x5 ↦ᵣ shift0) ** (.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ r11) ** (.x7 ↦ᵣ r7) ** (.x12 ↦ᵣ sp))
      ((.x5 ↦ᵣ limb_shift) ** (.x6 ↦ᵣ bit_shift) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ mask) ** (.x7 ↦ᵣ anti_shift) ** (.x12 ↦ᵣ (sp + signExtend12 32))) := by
  have A1 := andi_spec_gen .x6 .x5 r6 shift0 63 base (by nofun)
  have SR := srli_spec_gen_same .x5 shift0 6 (base + 4) (by nofun)
  have SL := sltu_spec_gen .x11 .x0 .x6 r11 (0 : Word) (shift0 &&& signExtend12 63) (base + 8) (by nofun)
  have SU := sub_spec_gen_rd_eq_rs2 .x11 .x0 (0 : Word) (if BitVec.ult (0 : Word) (shift0 &&& signExtend12 63) then (1 : Word) else 0) (base + 12) (by nofun)
  have LI_ := li_spec_gen .x7 r7 64 (base + 16) (by nofun)
  have SU2 := sub_spec_gen_rd_eq_rs1 .x7 .x6 (64 : Word) (shift0 &&& signExtend12 63) (base + 20) (by nofun)
  have AD := addi_spec_gen_same .x12 sp 32 (base + 24) (by nofun)
  runBlock A1 SR SL SU LI_ SU2 AD

-- ============================================================================
-- Section 4: LD/OR Accumulator Helper (2 instructions)
-- ============================================================================

abbrev shr_ld_or_acc_code (off : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (shr_ld_or_acc_prog off)

theorem shr_ld_or_acc_spec (sp acc prev_x10 val : Word) (off : BitVec 12)
    (base : Word)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let code := shr_ld_or_acc_code off base
    cpsTriple base (base + 8) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ acc) ** (.x10 ↦ᵣ prev_x10) ** ((sp + signExtend12 off) ↦ₘ val))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (acc ||| val)) ** (.x10 ↦ᵣ val) ** ((sp + signExtend12 off) ↦ₘ val)) := by
  have L := ld_spec_gen .x10 .x12 sp prev_x10 val off base (by nofun) hvalid
  have OR_ := or_spec_gen_rd_eq_rs1 .x5 .x10 acc val (base + 4) (by nofun)
  runBlock L OR_

-- ============================================================================
-- Section 5: Body Specs
-- ============================================================================

-- Body 3: limb_shift=3, 7 instructions

abbrev shr_body_3_code (jal_off : BitVec 21) (base : Word) : CodeReq :=
  CodeReq.ofProg base (shr_body_3_prog jal_off)

theorem shr_body_3_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Word) (jal_off : BitVec 21)
    (hexit : (base + 24) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 4) :
    let result0 := v3 >>> (bit_shift.toNat % 64)
    let code := shr_body_3_code jal_off base
    cpsTriple base exit code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 8) ↦ₘ v1) ** ((sp + 16) ↦ₘ v2) ** ((sp + 24) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result0) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 8) ↦ₘ 0) ** ((sp + 16) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0)) := by
  have LL := shr_last_limb_spec 0 sp v3 v0 v5 bit_shift base (by validMem) (by validMem)
  have S0 := sd_x0_spec_gen .x12 sp v1 8 (base + 12) (by validMem)
  have S1 := sd_x0_spec_gen .x12 sp v2 16 (base + 16) (by validMem)
  have S2 := sd_x0_spec_gen .x12 sp v3 24 (base + 20) (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 24)
  rw [hexit] at JL
  runBlock LL S0 S1 S2 JL

-- Body 2: limb_shift=2, 13 instructions

abbrev shr_body_2_code (jal_off : BitVec 21) (base : Word) : CodeReq :=
  CodeReq.ofProg base (shr_body_2_prog jal_off)

set_option maxHeartbeats 3200000 in
theorem shr_body_2_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Word) (jal_off : BitVec 21)
    (hexit : (base + 48) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 4) :
    let result0 := (v2 >>> (bit_shift.toNat % 64)) ||| ((v3 <<< (anti_shift.toNat % 64)) &&& mask)
    let result1 := v3 >>> (bit_shift.toNat % 64)
    let code := shr_body_2_code jal_off base
    cpsTriple base exit code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 8) ↦ₘ v1) ** ((sp + 16) ↦ₘ v2) ** ((sp + 24) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result1) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v3 <<< (anti_shift.toNat % 64)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 8) ↦ₘ result1) ** ((sp + 16) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0)) := by
  have MM := shr_merge_limb_spec 16 24 0 sp v2 v3 v0 v5 v10 bit_shift anti_shift mask base (by validMem) (by validMem) (by validMem)
  have LL := shr_last_limb_spec 8 sp v3 v1
    ((v2 >>> (bit_shift.toNat % 64)) ||| ((v3 <<< (anti_shift.toNat % 64)) &&& mask))
    bit_shift (base + 28) (by validMem) (by validMem)
  have S0 := sd_x0_spec_gen .x12 sp v2 16 (base + 40) (by validMem)
  have S1 := sd_x0_spec_gen .x12 sp v3 24 (base + 44) (by validMem)
  subst exit
  have JL := jal_x0_spec_gen jal_off (base + 48)
  runBlock MM LL S0 S1 JL

-- Body 1: limb_shift=1, 19 instructions

abbrev shr_body_1_code (jal_off : BitVec 21) (base : Word) : CodeReq :=
  CodeReq.ofProg base (shr_body_1_prog jal_off)

set_option maxHeartbeats 3200000 in
theorem shr_body_1_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Word) (jal_off : BitVec 21)
    (hexit : (base + 72) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 4) :
    let result0 := (v1 >>> (bit_shift.toNat % 64)) ||| ((v2 <<< (anti_shift.toNat % 64)) &&& mask)
    let result1 := (v2 >>> (bit_shift.toNat % 64)) ||| ((v3 <<< (anti_shift.toNat % 64)) &&& mask)
    let result2 := v3 >>> (bit_shift.toNat % 64)
    let code := shr_body_1_code jal_off base
    cpsTriple base exit code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 8) ↦ₘ v1) ** ((sp + 16) ↦ₘ v2) ** ((sp + 24) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result2) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v3 <<< (anti_shift.toNat % 64)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 8) ↦ₘ result1) ** ((sp + 16) ↦ₘ result2) ** ((sp + 24) ↦ₘ 0)) := by
  have MM1 := shr_merge_limb_spec 8 16 0 sp v1 v2 v0 v5 v10 bit_shift anti_shift mask base (by validMem) (by validMem) (by validMem)
  have MM2 := shr_merge_limb_spec 16 24 8 sp v2 v3 v1
    ((v1 >>> (bit_shift.toNat % 64)) ||| ((v2 <<< (anti_shift.toNat % 64)) &&& mask))
    ((v2 <<< (anti_shift.toNat % 64)) &&& mask)
    bit_shift anti_shift mask (base + 28) (by validMem) (by validMem) (by validMem)
  have LL := shr_last_limb_spec 16 sp v3 v2
    ((v2 >>> (bit_shift.toNat % 64)) ||| ((v3 <<< (anti_shift.toNat % 64)) &&& mask))
    bit_shift (base + 56) (by validMem) (by validMem)
  have S0 := sd_x0_spec_gen .x12 sp v3 24 (base + 68) (by validMem)
  subst exit
  have JL := jal_x0_spec_gen jal_off (base + 72)
  runBlock MM1 MM2 LL S0 JL

-- Body 0: limb_shift=0, 25 instructions

abbrev shr_body_0_code (jal_off : BitVec 21) (base : Word) : CodeReq :=
  CodeReq.ofProg base (shr_body_0_prog jal_off)

set_option maxHeartbeats 3200000 in
theorem shr_body_0_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Word) (jal_off : BitVec 21)
    (hexit : (base + 96) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 4) :
    let result0 := (v0 >>> (bit_shift.toNat % 64)) ||| ((v1 <<< (anti_shift.toNat % 64)) &&& mask)
    let result1 := (v1 >>> (bit_shift.toNat % 64)) ||| ((v2 <<< (anti_shift.toNat % 64)) &&& mask)
    let result2 := (v2 >>> (bit_shift.toNat % 64)) ||| ((v3 <<< (anti_shift.toNat % 64)) &&& mask)
    let result3 := v3 >>> (bit_shift.toNat % 64)
    let code := shr_body_0_code jal_off base
    cpsTriple base exit code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 8) ↦ₘ v1) ** ((sp + 16) ↦ₘ v2) ** ((sp + 24) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result3) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v3 <<< (anti_shift.toNat % 64)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 8) ↦ₘ result1) ** ((sp + 16) ↦ₘ result2) ** ((sp + 24) ↦ₘ result3)) := by
  have MM1 := shr_merge_limb_inplace_spec 0 8 sp v0 v1 v5 v10 bit_shift anti_shift mask base (by validMem) (by validMem)
  have MM2 := shr_merge_limb_inplace_spec 8 16 sp v1 v2
    ((v0 >>> (bit_shift.toNat % 64)) ||| ((v1 <<< (anti_shift.toNat % 64)) &&& mask))
    ((v1 <<< (anti_shift.toNat % 64)) &&& mask)
    bit_shift anti_shift mask (base + 28) (by validMem) (by validMem)
  have MM3 := shr_merge_limb_inplace_spec 16 24 sp v2 v3
    ((v1 >>> (bit_shift.toNat % 64)) ||| ((v2 <<< (anti_shift.toNat % 64)) &&& mask))
    ((v2 <<< (anti_shift.toNat % 64)) &&& mask)
    bit_shift anti_shift mask (base + 56) (by validMem) (by validMem)
  have LL := shr_last_limb_inplace_spec sp v3
    ((v2 >>> (bit_shift.toNat % 64)) ||| ((v3 <<< (anti_shift.toNat % 64)) &&& mask))
    bit_shift (base + 84) (by validMem)
  subst exit
  have JL := jal_x0_spec_gen jal_off (base + 96)
  runBlock MM1 MM2 MM3 LL JL

-- ============================================================================
-- Section 6: Cascade Step Helper (2 instructions)
-- ============================================================================

abbrev shr_cascade_step_code (k : BitVec 12) (offset : BitVec 13) (base : Word) : CodeReq :=
  CodeReq.ofProg base (shr_cascade_step_prog k offset)

/-- Cascade step: ADDI x10,x0,k followed by BEQ x5,x10,off.
    Produces a cpsBranch with clean postconditions (no pure facts).
    Uses disjoint composition of the two singleton CRs. -/
theorem shr_cascade_step_spec (v5 v10 : Word)
    (k : BitVec 12) (offset : BitVec 13) (base target : Word)
    (htarget : (base + 4) + signExtend13 offset = target) :
    let k_val := (0 : Word) + signExtend12 k
    let code := shr_cascade_step_code k offset base
    cpsBranch base code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      target ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val))
      (base + 8) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val)) := by
  have ha1 : (base + 4 : Word) + 4 = base + 8 := by bv_omega
  -- Disjointness of the two singletons
  have hd : CodeReq.Disjoint
      (CodeReq.singleton base (.ADDI .x10 .x0 k))
      (CodeReq.singleton (base + 4) (.BEQ .x5 .x10 offset)) :=
    CodeReq.Disjoint.singleton (by bv_omega) _ _
  -- Step 1: ADDI x10, x0, k at base (singleton CR)
  have s1 := addi_spec_gen .x10 .x0 v10 0 k base (by nofun)
  -- Frame ADDI with x5 and permute
  have s1' : cpsTriple base (base + 4) (CodeReq.singleton base (.ADDI .x10 .x0 k))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 k))) :=
    cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTriple_frame_left _ _ _ _ _ (.x5 ↦ᵣ v5) (by pcFree) s1)
  -- Step 2: BEQ x5, x10, offset at base+4 (singleton CR)
  have s2_raw := beq_spec_gen .x5 .x10 offset v5 ((0 : Word) + signExtend12 k) (base + 4)
  rw [htarget, ha1] at s2_raw
  -- Strip pure facts + frame with x0 + permute
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
  -- Compose with disjoint CRs
  exact cpsTriple_seq_cpsBranch_with_perm _ _ _ _ hd _ _ _ target _ (base + 8) _
    (fun _ hp => hp) s1' s2'

/-- Cascade step variant that preserves pure dispatch facts.
    Taken postcondition includes `⌜v5 = k_val⌝`, not-taken includes `⌜v5 ≠ k_val⌝`. -/
theorem shr_cascade_step_spec_pure (v5 v10 : Word)
    (k : BitVec 12) (offset : BitVec 13) (base target : Word)
    (htarget : (base + 4) + signExtend13 offset = target) :
    let k_val := (0 : Word) + signExtend12 k
    let code := shr_cascade_step_code k offset base
    cpsBranch base code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      target ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val) ** ⌜v5 = k_val⌝)
      (base + 8) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val) ** ⌜v5 ≠ k_val⌝) := by
  have ha1 : (base + 4 : Word) + 4 = base + 8 := by bv_omega
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
  -- Keep pure facts: frame with x0 + permute, preserving ⌜v5 = k_val⌝ / ⌜v5 ≠ k_val⌝
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
-- Section 7: Phase C Cascade (5 instructions, cpsNBranch with 4 exits)
-- ============================================================================

/-- Phase C code as explicit union of sub-CRs (matching disjoint composition structure). -/
abbrev shr_phase_c_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.BEQ .x5 .x0 176))
  (CodeReq.union (shr_cascade_step_code 1 92 (base + 4))
  (shr_cascade_step_code 2 32 (base + 12)))

set_option maxHeartbeats 3200000 in
/-- Phase C spec: cascade dispatch on limb_shift (0-3).
    Uses disjoint composition to chain BEQ + two cascade steps. -/
theorem shr_phase_c_spec (v5 v10 : Word) (base : Word)
    (e0 e1 e2 e3 : Word)
    (he0 : base + signExtend13 176 = e0)
    (he1 : (base + 8) + signExtend13 92 = e1)
    (he2 : (base + 16) + signExtend13 32 = e2)
    (he3 : base + 20 = e3) :
    let code := shr_phase_c_code base
    cpsNBranch base code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      [(e0, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10)),
       (e1, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1))),
       (e2, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2))),
       (e3, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)))] := by
  -- Address arithmetic
  have hc1 : ((base + 4 : Word) + 4) + signExtend13 92 = e1 := by
    rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega]; exact he1
  have hc2 : ((base + 12 : Word) + 4) + signExtend13 32 = e2 := by
    rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega]; exact he2
  -- Sub-CRs
  let cr_beq0 := CodeReq.singleton base (.BEQ .x5 .x0 176)
  let cr_cs1 := shr_cascade_step_code 1 92 (base + 4)
  let cr_cs2 := shr_cascade_step_code 2 32 (base + 12)
  -- Disjointness proofs between sub-CRs
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
  -- Step 0: BEQ x5 x0 176 at base (singleton CR)
  have beq0_raw := beq_spec_gen .x5 .x0 176 v5 (0 : Word) base
  rw [he0] at beq0_raw
  -- Strip pure facts
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
  -- Frame BEQ with x10
  have beq0f := cpsBranch_frame_left base cr_beq0
    ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)))
    e0 _ (base + 4) _
    (.x10 ↦ᵣ v10) (by pcFree) beq0
  -- Step 1: cascade step at base+4 (CR = cr_cs1)
  have cs1 := shr_cascade_step_spec v5 v10 1 92 (base + 4) e1 hc1
  rw [show (base + 4 : Word) + 8 = base + 12 from by bv_omega] at cs1
  -- Step 2: cascade step at base+12 (CR = cr_cs2)
  have cs2 := shr_cascade_step_spec v5 ((0 : Word) + signExtend12 1) 2 32 (base + 12) e2 hc2
  rw [show (base + 12 : Word) + 8 = base + 20 from by bv_omega] at cs2
  -- Fallthrough at base+20 (CR = empty)
  have ft := cpsNBranch_refl (base + 20)
    ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)))
    _ (fun _ hp => hp)
  -- Chain step 2 + fallthrough (disjoint: cr_cs2 vs empty)
  have n3 := cpsBranch_cons_cpsNBranch (base + 12) cr_cs2 CodeReq.empty
    (CodeReq.Disjoint.empty_right cr_cs2)
    _ e2 _ (base + 20) _ _ cs2 ft
  -- Helper: union with empty is identity
  have hunion_empty : ∀ (cr : CodeReq), cr.union CodeReq.empty = cr := by
    intro cr; funext a; simp only [CodeReq.union, CodeReq.empty]; cases cr a <;> rfl
  -- Chain step 1 + n3 (disjoint: cr_cs1 vs cr_cs2.union empty)
  have hd_cs1_rest : cr_cs1.Disjoint (cr_cs2.union CodeReq.empty) := by
    rw [hunion_empty]; exact hd_cs1_cs2
  have n2 := cpsBranch_cons_cpsNBranch_with_perm (base + 4) cr_cs1 (cr_cs2.union CodeReq.empty)
    hd_cs1_rest
    _ e1 _ (base + 12) _ _ _
    (fun h hp => by xperm_hyp hp) cs1 n3
  -- Chain step 0 + n2 (disjoint: cr_beq0 vs cr_cs1.union (cr_cs2.union empty))
  have hd_beq0_rest : cr_beq0.Disjoint (cr_cs1.union (cr_cs2.union CodeReq.empty)) := by
    rw [hunion_empty]; exact CodeReq.Disjoint.union_right hd_beq0_cs1 hd_beq0_cs2
  have n1 := cpsBranch_cons_cpsNBranch_with_perm base cr_beq0 (cr_cs1.union (cr_cs2.union CodeReq.empty))
    hd_beq0_rest
    _ e0 _ (base + 4) _ _ _
    (fun h hp => by xperm_hyp hp) beq0f n2
  -- The CR now is: cr_beq0.union (cr_cs1.union (cr_cs2.union empty))
  -- Simplify empty away and match the goal CR
  have hcr_eq : cr_beq0.union (cr_cs1.union (cr_cs2.union CodeReq.empty)) = shr_phase_c_code base := by
    simp only [hunion_empty]; rfl
  -- Weaken precondition and rewrite CR
  -- Rewrite CR, weaken pre, and weaken post
  intro code
  have n1_rw := hcr_eq ▸ n1
  exact cpsNBranch_weaken_posts _ _ _ _ _ (cpsNBranch_weaken_pre _ _ _ _ _ (fun h hp => by xperm_hyp hp) n1_rw)
    (fun ex hmem => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, List.Mem.head _, rfl, fun h hp => by xperm_hyp hp⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, fun h hp => by xperm_hyp hp⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl, fun h hp => by xperm_hyp hp⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))), he3.symm, fun h hp => by xperm_hyp hp⟩)

set_option maxHeartbeats 6400000 in
/-- Phase C spec with pure dispatch facts: each exit postcondition includes
    the constraint that identifies which branch was taken.
    Built by composing sub-specs with pure-fact framing. -/
theorem shr_phase_c_spec_pure (v5 v10 : Word) (base : Word)
    (e0 e1 e2 e3 : Word)
    (he0 : base + signExtend13 176 = e0)
    (he1 : (base + 8) + signExtend13 92 = e1)
    (he2 : (base + 16) + signExtend13 32 = e2)
    (he3 : base + 20 = e3) :
    let code := shr_phase_c_code base
    cpsNBranch base code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      [(e0, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** ⌜v5 = 0⌝),
       (e1, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 = (0 : Word) + signExtend12 1⌝),
       (e2, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 = (0 : Word) + signExtend12 2⌝),
       (e3, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1 ∧ v5 ≠ (0 : Word) + signExtend12 2⌝)] := by
  have hc1 : ((base + 4 : Word) + 4) + signExtend13 92 = e1 := by
    rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega]; exact he1
  have hc2 : ((base + 12 : Word) + 4) + signExtend13 32 = e2 := by
    rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega]; exact he2
  let cr_beq0 := CodeReq.singleton base (.BEQ .x5 .x0 176)
  let cr_cs1 := shr_cascade_step_code 1 92 (base + 4)
  let cr_cs2 := shr_cascade_step_code 2 32 (base + 12)
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
  -- Step 0: BEQ x5 x0 176 — keep ⌜v5 = 0⌝ / ⌜v5 ≠ 0⌝
  have beq0_raw := beq_spec_gen .x5 .x0 176 v5 (0 : Word) base
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
  -- Step 1: cascade step at base+4 with pure facts, framed with ⌜v5 ≠ 0⌝
  have cs1_raw := shr_cascade_step_spec_pure v5 v10 1 92 (base + 4) e1 hc1
  rw [show (base + 4 : Word) + 8 = base + 12 from by bv_omega] at cs1_raw
  have cs1f := cpsBranch_frame_left _ _ _ _ _ _ _ (⌜v5 ≠ (0 : Word)⌝) (pcFree_pure _) cs1_raw
  -- cs1f taken: (regs ** ⌜v5 = 1⌝) ** ⌜v5 ≠ 0⌝
  -- cs1f ntaken: (regs ** ⌜v5 ≠ 1⌝) ** ⌜v5 ≠ 0⌝
  have cs1_clean : cpsBranch (base + 4) cr_cs1
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** ⌜v5 ≠ (0 : Word)⌝)
      e1 ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 = (0 : Word) + signExtend12 1⌝)
      (base + 12) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1⌝) :=
    cpsBranch_consequence _ _ _ _ e1 _ _ (base + 12) _ _
      (fun h hp => (congrFun (show _ = _ from by xperm) h).mp hp)
      -- taken: strip ⌜v5 ≠ 0⌝ frame
      (fun h hp => (sepConj_pure_right _ _ h).1 hp |>.1)
      -- ntaken: (regs ** ⌜v5 ≠ 1⌝) ** ⌜v5 ≠ 0⌝ → regs ** ⌜v5 ≠ 0 ∧ v5 ≠ 1⌝
      (fun h hp => by
        -- hp : ((x5 ** x0 ** x10 ** ⌜v5 ≠ 1⌝) ** ⌜v5 ≠ 0⌝) h
        have ⟨hinner, hne0⟩ := (sepConj_pure_right _ _ h).1 hp
        -- hinner : (x5 ** x0 ** x10 ** ⌜v5 ≠ 1⌝) h
        have hne1 := sepConj_extract_pure_end3 _ _ _ _ h hinner
        have hregs := sepConj_strip_pure_end3 _ _ _ _ h hinner
        -- Reconstruct: regs ** ⌜v5 ≠ 0 ∧ v5 ≠ 1⌝
        exact (congrFun (show _ = _ from by xperm) h).mp
          ((sepConj_pure_right _ _ h).2 (And.intro hregs (And.intro hne0 hne1))))
      cs1f
  -- Step 2: cascade step at base+12, framed with ⌜v5 ≠ 0 ∧ v5 ≠ 1⌝
  have cs2_raw := shr_cascade_step_spec_pure v5 ((0 : Word) + signExtend12 1) 2 32 (base + 12) e2 hc2
  rw [show (base + 12 : Word) + 8 = base + 20 from by bv_omega] at cs2_raw
  have cs2f := cpsBranch_frame_left _ _ _ _ _ _ _
    (⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1⌝) (pcFree_pure _) cs2_raw
  -- cs2f taken: (regs ** ⌜v5 = 2⌝) ** ⌜v5 ≠ 0 ∧ v5 ≠ 1⌝
  -- cs2f ntaken: (regs ** ⌜v5 ≠ 2⌝) ** ⌜v5 ≠ 0 ∧ v5 ≠ 1⌝
  -- cs2_clean: reshape postconditions, use identity for precondition
  -- cs2f pre: ((.x5 ** .x0 ** .x10) ** ⌜conj⌝), same shape as cs2_clean pre after assoc
  -- Use sepConj_assoc' to make types match
  have cs2_clean : cpsBranch (base + 12) cr_cs2
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1⌝)
      e2 ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 = (0 : Word) + signExtend12 2⌝)
      (base + 20) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1 ∧ v5 ≠ (0 : Word) + signExtend12 2⌝) :=
    cpsBranch_consequence _ _ _ _ e2 _ _ (base + 20) _ _
      -- pre: right-assoc ↔ left-nested
      (fun h hp => (congrFun (show _ = _ from by xperm) h).mp hp)
      -- taken: (regs ** ⌜v5=2⌝) ** ⌜conj⌝ → regs ** ⌜v5=2⌝
      (fun h hp => (sepConj_pure_right _ _ h).1 hp |>.1)
      -- ntaken: (regs ** ⌜v5≠2⌝) ** ⌜v5≠0 ∧ v5≠1⌝ → regs ** ⌜v5≠0 ∧ v5≠1 ∧ v5≠2⌝
      (fun h hp => by
        -- hp : ((x5 ** x0 ** x10 ** ⌜v5 ≠ 2⌝) ** ⌜v5 ≠ 0 ∧ v5 ≠ 1⌝) h
        have ⟨hinner, ⟨hne0, hne1⟩⟩ := (sepConj_pure_right _ _ h).1 hp
        have hne2 := sepConj_extract_pure_end3 _ _ _ _ h hinner
        have hregs := sepConj_strip_pure_end3 _ _ _ _ h hinner
        exact (congrFun (show _ = _ from by xperm) h).mp
          ((sepConj_pure_right _ _ h).2 (And.intro hregs (And.intro hne0 (And.intro hne1 hne2)))))
      cs2f
  -- Fallthrough at base+20: trivial cpsNBranch
  have ft := cpsNBranch_refl (base + 20)
    ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)) ** ⌜v5 ≠ 0 ∧ v5 ≠ (0 : Word) + signExtend12 1 ∧ v5 ≠ (0 : Word) + signExtend12 2⌝)
    _ (fun _ hp => hp)
  have hunion_empty : ∀ (cr : CodeReq), cr.union CodeReq.empty = cr := by
    intro cr; funext a; simp only [CodeReq.union, CodeReq.empty]; cases cr a <;> rfl
  -- Chain cs2_clean + ft
  have n3 := cpsBranch_cons_cpsNBranch (base + 12) cr_cs2 CodeReq.empty
    (CodeReq.Disjoint.empty_right cr_cs2)
    _ e2 _ (base + 20) _ _ cs2_clean ft
  -- Chain cs1_clean + n3
  have hd_cs1_rest : cr_cs1.Disjoint (cr_cs2.union CodeReq.empty) := by
    rw [hunion_empty]; exact hd_cs1_cs2
  have n2 := cpsBranch_cons_cpsNBranch_with_perm (base + 4) cr_cs1 (cr_cs2.union CodeReq.empty)
    hd_cs1_rest
    _ e1 _ (base + 12) _ _ _
    (fun h hp => by xperm_hyp hp) cs1_clean n3
  -- Chain beq0f + n2
  have hd_beq0_rest : cr_beq0.Disjoint (cr_cs1.union (cr_cs2.union CodeReq.empty)) := by
    rw [hunion_empty]; exact CodeReq.Disjoint.union_right hd_beq0_cs1 hd_beq0_cs2
  have n1 := cpsBranch_cons_cpsNBranch_with_perm base cr_beq0 (cr_cs1.union (cr_cs2.union CodeReq.empty))
    hd_beq0_rest
    _ e0 _ (base + 4) _ _ _
    (fun h hp => by xperm_hyp hp) beq0f n2
  -- Simplify CR and match goal
  have hcr_eq : cr_beq0.union (cr_cs1.union (cr_cs2.union CodeReq.empty)) = shr_phase_c_code base := by
    simp only [hunion_empty]; rfl
  intro code
  have n1_rw := hcr_eq ▸ n1
  exact cpsNBranch_weaken_posts _ _ _ _ _ (cpsNBranch_weaken_pre _ _ _ _ _ (fun h hp => by xperm_hyp hp) n1_rw)
    (fun ex hmem => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, List.Mem.head _, rfl, fun h hp => by xperm_hyp hp⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, fun h hp => by xperm_hyp hp⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl, fun h hp => by xperm_hyp hp⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))), he3.symm, fun h hp => by xperm_hyp hp⟩)

-- ============================================================================
-- Section 8: Phase A (9 instructions, cpsBranch)
-- ============================================================================

-- Helper: weaken concrete regs to regOwn
private theorem regIs_to_regOwn (r : Reg) (v : Word) : ∀ h, (r ↦ᵣ v) h → (regOwn r) h :=
  fun _ hp => ⟨v, hp⟩

/-- Phase A code as explicit union of sub-CRs (matching disjoint composition structure).
    9 instructions: LD + LD/OR + LD/OR + BNE + LD + SLTIU + BEQ -/
abbrev shr_phase_a_code (base : Word) : CodeReq :=
  -- LD x5 x12 8 at base
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 8))
  -- LD x10 x12 16 + OR x5 x5 x10 at base+4, base+8
  (CodeReq.union (shr_ld_or_acc_code 16 (base + 4))
  -- LD x10 x12 24 + OR x5 x5 x10 at base+12, base+16
  (CodeReq.union (shr_ld_or_acc_code 24 (base + 12))
  -- BNE x5 x0 320 at base+20
  (CodeReq.union (CodeReq.singleton (base + 20) (.BNE .x5 .x0 320))
  -- LD x5 x12 0 at base+24
  (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x5 .x12 0))
  -- SLTIU x10 x5 256 at base+28
  (CodeReq.union (CodeReq.singleton (base + 28) (.SLTIU .x10 .x5 256))
  -- BEQ x10 x0 308 at base+32
  (CodeReq.singleton (base + 32) (.BEQ .x10 .x0 308)))))))

set_option maxHeartbeats 6400000 in
/-- Phase A spec: Check shift >= 256.
    9 instructions, cpsBranch with 2 exits:
    - Taken (zero_path): shift >= 256, x5/x10 are regOwn (existential)
    - Not-taken (base+36): shift < 256, x5=s0, x10 is regOwn
    Uses disjoint composition throughout (no extend_code). -/
theorem shr_phase_a_spec (sp r5 r10 : Word)
    (s0 s1 s2 s3 : Word)
    (base zero_path : Word)
    (hzero : (base + 20) + signExtend13 320 = zero_path)
    (hzero2 : (base + 32) + signExtend13 308 = zero_path)
    (hvalid : ValidMemRange sp 8) :
    let code := shr_phase_a_code base
    cpsBranch base code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
      zero_path
      ((.x12 ↦ᵣ sp) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
      (base + 36)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3)) := by
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
  have ha48 : (base + 4 : Word) + 8 = base + 12 := by bv_omega
  have ha128 : (base + 12 : Word) + 8 = base + 20 := by bv_omega
  have ha20 : (base + 20 : Word) + 4 = base + 24 := by bv_omega
  have ha24 : (base + 24 : Word) + 4 = base + 28 := by bv_omega
  have ha28 : (base + 28 : Word) + 4 = base + 32 := by bv_omega
  have ha32 : (base + 32 : Word) + 4 = base + 36 := by bv_omega
  -- Sub-CRs for each instruction group
  let cr_ld1 := CodeReq.singleton base (.LD .x5 .x12 8)
  let cr_lor2 := shr_ld_or_acc_code 16 (base + 4)
  let cr_lor3 := shr_ld_or_acc_code 24 (base + 12)
  let cr_bne := CodeReq.singleton (base + 20) (.BNE .x5 .x0 320)
  let cr_ld5 := CodeReq.singleton (base + 24) (.LD .x5 .x12 0)
  let cr_sltiu := CodeReq.singleton (base + 28) (.SLTIU .x10 .x5 256)
  let cr_beq := CodeReq.singleton (base + 32) (.BEQ .x10 .x0 308)
  -- ── Part 1: Linear chain base..base+20 (LD + LD/OR + LD/OR) ──
  -- Step 1: LD x5 x12 8 at base (CR = cr_ld1)
  have lw1 := ld_spec_gen .x5 .x12 sp r5 s1 8 base (by nofun)
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_8] at lw1
  -- Step 2: shr_ld_or_acc at base+4 (CR = cr_lor2, exit = (base+4)+8 = base+12)
  have lor2 := shr_ld_or_acc_spec sp s1 r10 s2 16 (base + 4)
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_16] at lor2
  rw [ha48] at lor2
  -- Disjoint: cr_ld1 vs cr_lor2
  have hd_ld1_lor2 : cr_ld1.Disjoint cr_lor2 :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega) _ _)
      (CodeReq.Disjoint.singleton (by bv_omega) _ _)
  -- Compose LD + LD/OR (need to frame + perm)
  have lw1f := cpsTriple_frame_left base (base + 4) cr_ld1
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** ((sp + 8) ↦ₘ s1))
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s1) ** ((sp + 8) ↦ₘ s1))
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) ** (sp ↦ₘ s0) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) lw1
  have lor2f := cpsTriple_frame_left (base + 4) (base + 12) cr_lor2
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s1) ** (.x10 ↦ᵣ r10) ** ((sp + 16) ↦ₘ s2))
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (s1 ||| s2)) ** (.x10 ↦ᵣ s2) ** ((sp + 16) ↦ₘ s2))
    ((.x0 ↦ᵣ (0 : Word)) ** (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) lor2
  have c12 := cpsTriple_seq_with_perm base (base + 4) (base + 12) cr_ld1 cr_lor2 hd_ld1_lor2
    _ _ _ _
    (fun h hp => by xperm_hyp hp) lw1f lor2f
  -- Step 3: shr_ld_or_acc at base+12 (CR = cr_lor3, exit = (base+12)+8 = base+20)
  have lor3 := shr_ld_or_acc_spec sp (s1 ||| s2) s2 s3 24 (base + 12)
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at lor3
  rw [ha128] at lor3
  have lor3f := cpsTriple_frame_left (base + 12) (base + 20) cr_lor3
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (s1 ||| s2)) ** (.x10 ↦ᵣ s2) ** ((sp + 24) ↦ₘ s3))
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (s1 ||| s2 ||| s3)) ** (.x10 ↦ᵣ s3) ** ((sp + 24) ↦ₘ s3))
    ((.x0 ↦ᵣ (0 : Word)) ** (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2))
    (by pcFree) lor3
  -- Disjoint: (cr_ld1 ∪ cr_lor2) vs cr_lor3
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
  -- CR so far: (cr_ld1 ∪ cr_lor2) ∪ cr_lor3
  let cr_linear := (cr_ld1.union cr_lor2).union cr_lor3
  -- ── Part 2: BNE at base+20 (first branch) ──
  have bne_raw := bne_spec_gen .x5 .x0 320 (s1 ||| s2 ||| s3) (0 : Word) (base + 20)
  rw [hzero, ha20] at bne_raw
  -- Strip pure facts from BNE
  have bne1 : cpsBranch (base + 20) cr_bne
      ((.x5 ↦ᵣ (s1 ||| s2 ||| s3)) ** (.x0 ↦ᵣ (0 : Word)))
      zero_path ((.x5 ↦ᵣ (s1 ||| s2 ||| s3)) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 24) ((.x5 ↦ᵣ (s1 ||| s2 ||| s3)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence (base + 20) _ _ _
      zero_path _ _ (base + 24) _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      bne_raw
  -- Frame BNE with remaining state
  have bne1f := cpsBranch_frame_left (base + 20) cr_bne
    ((.x5 ↦ᵣ (s1 ||| s2 ||| s3)) ** (.x0 ↦ᵣ (0 : Word)))
    zero_path _ (base + 24) _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ s3) ** (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) bne1
  -- Disjoint: cr_linear vs cr_bne
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
  -- Compose linear chain + BNE branch
  have br1 := cpsTriple_seq_cpsBranch_with_perm base (base + 20) cr_linear cr_bne hd_lin_bne
    _ _ _ zero_path _ (base + 24) _
    (fun h hp => by xperm_hyp hp) c13 bne1f
  -- BR1 CR: cr_linear ∪ cr_bne
  -- ── Part 3: Fall-through path (base+24..base+32): LD + SLTIU + BEQ ──
  -- Step 5: LD x5 x12 0 at base+24
  have lw5 := ld_spec_gen .x5 .x12 sp
    (s1 ||| s2 ||| s3) s0 0 (base + 24) (by nofun)
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_omega]; exact hv0)
  simp only [signExtend12_0] at lw5
  rw [show sp + (0 : Word) = sp from by bv_omega] at lw5
  rw [ha24] at lw5
  -- Step 6: SLTIU x10 x5 256 at base+28
  have sltiu_raw := sltiu_spec_gen .x10 .x5 s3 s0 256 (base + 28) (by nofun)
  rw [ha28] at sltiu_raw
  let sltiu_val := (if BitVec.ult s0 (signExtend12 (256 : BitVec 12)) then (1 : Word) else (0 : Word))
  -- Disjoint: cr_ld5 vs cr_sltiu
  have hd_ld5_sltiu : cr_ld5.Disjoint cr_sltiu :=
    CodeReq.Disjoint.singleton (by bv_omega) _ _
  -- Frame and compose LD + SLTIU
  have lw5f := cpsTriple_frame_left (base + 24) (base + 28) cr_ld5
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (s1 ||| s2 ||| s3)) ** (sp ↦ₘ s0))
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (sp ↦ₘ s0))
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ s3) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) lw5
  have sltiuf := cpsTriple_frame_left (base + 28) (base + 32) cr_sltiu
    ((.x5 ↦ᵣ s0) ** (.x10 ↦ᵣ s3))
    ((.x5 ↦ᵣ s0) ** (.x10 ↦ᵣ sltiu_val))
    ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) sltiu_raw
  have c56 := cpsTriple_seq_with_perm (base + 24) (base + 28) (base + 32)
    cr_ld5 cr_sltiu hd_ld5_sltiu
    _ _ _ _
    (fun h hp => by xperm_hyp hp) lw5f sltiuf
  -- Step 7: BEQ x10 x0 308 at base+32
  have beq_raw := beq_spec_gen .x10 .x0 308 sltiu_val (0 : Word) (base + 32)
  rw [hzero2, ha32] at beq_raw
  -- Strip pure facts from BEQ
  have beq1 : cpsBranch (base + 32) cr_beq
      ((.x10 ↦ᵣ sltiu_val) ** (.x0 ↦ᵣ (0 : Word)))
      zero_path ((.x10 ↦ᵣ sltiu_val) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 36) ((.x10 ↦ᵣ sltiu_val) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence (base + 32) _ _ _
      zero_path _ _ (base + 36) _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      beq_raw
  -- Frame BEQ with remaining state
  have beq1f := cpsBranch_frame_left (base + 32) cr_beq
    ((.x10 ↦ᵣ sltiu_val) ** (.x0 ↦ᵣ (0 : Word)))
    zero_path _ (base + 36) _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) beq1
  -- Disjoint: (cr_ld5 ∪ cr_sltiu) vs cr_beq
  have hd_56_beq : (cr_ld5.union cr_sltiu).Disjoint cr_beq :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.singleton (by bv_omega) _ _)
      (CodeReq.Disjoint.singleton (by bv_omega) _ _)
  -- Compose LD+SLTIU chain with BEQ branch
  have br2 := cpsTriple_seq_cpsBranch_with_perm (base + 24) (base + 32)
    (cr_ld5.union cr_sltiu) cr_beq hd_56_beq
    _ _ _ zero_path _ (base + 36) _
    (fun h hp => by xperm_hyp hp) c56 beq1f
  -- BR2 CR: (cr_ld5 ∪ cr_sltiu) ∪ cr_beq
  let cr_tail := (cr_ld5.union cr_sltiu).union cr_beq
  -- ── Part 4: Combine br1 and br2 ──
  -- Disjoint: (cr_linear ∪ cr_bne) vs cr_tail
  -- All addresses in left (base..base+20) distinct from right (base+24..base+32)
  -- Helper: "singleton at addr is disjoint from cr_tail"
  have sd_tail (a : Word) (i : Instr)
      (h24 : a ≠ base + 24) (h28 : a ≠ base + 28) (h32 : a ≠ base + 32) :
      (CodeReq.singleton a i).Disjoint cr_tail :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.singleton h24 _ _)
        (CodeReq.Disjoint.singleton h28 _ _))
      (CodeReq.Disjoint.singleton h32 _ _)
  -- cr_lor2 = singleton (base+4) ∪ singleton (base+4+4), each vs cr_tail
  have hd_lor2_tail : cr_lor2.Disjoint cr_tail :=
    CodeReq.Disjoint.union_left
      (sd_tail (base + 4) _ (by bv_omega) (by bv_omega) (by bv_omega))
      (sd_tail (base + 4 + 4) _ (by bv_omega) (by bv_omega) (by bv_omega))
  -- cr_lor3 = singleton (base+12) ∪ singleton (base+12+4), each vs cr_tail
  have hd_lor3_tail : cr_lor3.Disjoint cr_tail :=
    CodeReq.Disjoint.union_left
      (sd_tail (base + 12) _ (by bv_omega) (by bv_omega) (by bv_omega))
      (sd_tail (base + 12 + 4) _ (by bv_omega) (by bv_omega) (by bv_omega))
  have hd_br1_br2 : (cr_linear.union cr_bne).Disjoint cr_tail :=
    CodeReq.Disjoint.union_left
      -- cr_linear = (cr_ld1 ∪ cr_lor2) ∪ cr_lor3
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.union_left
          (sd_tail base _ (by bv_omega) (by bv_omega) (by bv_omega))
          hd_lor2_tail)
        hd_lor3_tail)
      -- cr_bne
      (sd_tail (base + 20) _ (by bv_omega) (by bv_omega) (by bv_omega))
  have combined := cpsBranch_seq_cpsBranch_with_perm
    base (base + 24) zero_path (base + 36)
    (cr_linear.union cr_bne) cr_tail hd_br1_br2
    _ _ _ _ _ _ _
    br1 (fun h hp => by xperm_hyp hp) br2
    -- ht1: weaken first taken path (BNE taken: x5 = s1|||s2|||s3, x10 = s3)
    (fun h hp => by
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (s1 ||| s2 ||| s3)) ** (.x10 ↦ᵣ s3) **
           (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
           (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
          from by xperm) h).mp hp)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ sp) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
        from by xperm) h).mp w1)
    -- ht2: weaken second taken path (BEQ taken: x5 = s0, x10 = sltiu_val)
    (fun h hp => by
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ s0) ** (.x10 ↦ᵣ sltiu_val) **
           (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
           (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
          from by xperm) h).mp hp)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ sp) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
        from by xperm) h).mp w1)
  -- The CR is now: (cr_linear ∪ cr_bne) ∪ cr_tail
  -- Show this equals shr_phase_a_code
  -- hcr_eq: prove the composition CR equals the definition by reassociating unions
  have hcr_eq : (cr_linear.union cr_bne).union cr_tail = shr_phase_a_code base := by
    -- Unfold let bindings to shr_phase_a_code components
    show ((((CodeReq.singleton base (.LD .x5 .x12 8)).union (shr_ld_or_acc_code 16 (base + 4))).union
            (shr_ld_or_acc_code 24 (base + 12))).union
           (CodeReq.singleton (base + 20) (.BNE .x5 .x0 320))).union
          (((CodeReq.singleton (base + 24) (.LD .x5 .x12 0)).union
            (CodeReq.singleton (base + 28) (.SLTIU .x10 .x5 256))).union
           (CodeReq.singleton (base + 32) (.BEQ .x10 .x0 308)))
        = shr_phase_a_code base
    -- Unfold definitions and reassociate both sides
    simp only [shr_phase_a_code, shr_ld_or_acc_code, CodeReq.union_assoc]
  -- Final: weaken not-taken postcondition and rewrite CR
  have result : cpsBranch base (shr_phase_a_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
      zero_path
      ((.x12 ↦ᵣ sp) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
      (base + 36)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3)) := by
    rw [← hcr_eq]
    exact cpsBranch_consequence base _ _ _
      zero_path _ _ (base + 36) _ _
      (fun h hp => by xperm_hyp hp)
      (fun _ hp => hp)
      (fun h hp => by
        have w0 := sepConj_mono_left (regIs_to_regOwn .x10 _) h
          ((congrFun (show _ =
            ((.x10 ↦ᵣ sltiu_val) **
             (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) **
             (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
            from by xperm) h).mp hp)
        exact (congrFun (show _ =
          ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
           (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
          from by xperm) h).mp w0)
      combined
  exact result

end EvmAsm.Rv64
