/-
  EvmAsm.Evm32.ShiftSpec

  CPS specifications for the 256-bit EVM SHR (logical shift right) program.
  Modular decomposition:
  - Per-limb helpers: shr_merge_limb_spec (7 instrs), shr_last_limb_spec (3 instrs)
  - Zero-fill helper: shr_sw_zero_spec (1 instr)
  - Zero path: shr_zero_path_spec (9 instrs, shift >= 256)
  - Shift bodies: shr_body_L_spec for L = 0..7
  - Full composition: evm_shr_spec
-/

import EvmAsm.Evm32.Shift
import EvmAsm.Rv32.SyscallSpecs
import EvmAsm.Rv32.Tactics.XSimp
import EvmAsm.Rv32.Tactics.RunBlock

open EvmAsm.Tactics

namespace EvmAsm

set_option maxHeartbeats 800000

local macro "bv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]))

-- ============================================================================
-- Per-limb Specs: SHR Merge Limb (7 instructions)
-- ============================================================================

/-- Instruction memory assertion for shr_merge_limb (7 instructions). -/
abbrev shr_merge_limb_code (src_off next_off dst_off : BitVec 12) (base : Addr) : Assertion :=
  (base ↦ᵢ .LW .x5 .x12 src_off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 24) ↦ᵢ .SW .x12 .x5 dst_off)

/-- SHR merge limb spec (7 instructions):
    LW x5, src_off(x12); SRL x5,x5,x6; LW x10, next_off(x12);
    SLL x10,x10,x7; AND x10,x10,x11; OR x5,x5,x10; SW x12,x5,dst_off

    Computes: result = (src >>> bit_shift) ||| ((next <<< anti_shift) &&& mask)
    and stores at dst_off.

    Preserves: x12, x6, x7, x11, memory at src and next.
    Modifies: x5 (= result), x10 (= (next <<< anti_shift) &&& mask), memory at dst. -/
theorem shr_merge_limb_spec (src_off next_off dst_off : BitVec 12)
    (sp src next dst_old v5 v10 bit_shift anti_shift mask : Word) (base : Addr)
    (hvalid_src : isValidMemAccess (sp + signExtend12 src_off) = true)
    (hvalid_next : isValidMemAccess (sp + signExtend12 next_off) = true)
    (hvalid_dst : isValidMemAccess (sp + signExtend12 dst_off) = true) :
    let mem_src := sp + signExtend12 src_off
    let mem_next := sp + signExtend12 next_off
    let mem_dst := sp + signExtend12 dst_off
    let shifted_src := src >>> (bit_shift.toNat % 32)
    let shifted_next := (next <<< (anti_shift.toNat % 32)) &&& mask
    let result := shifted_src ||| shifted_next
    cpsTriple base (base + 28) CodeReq.empty
      ((base ↦ᵢ .LW .x5 .x12 src_off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 24) ↦ᵢ .SW .x12 .x5 dst_off) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (mem_src ↦ₘ src) ** (mem_next ↦ₘ next) ** (mem_dst ↦ₘ dst_old))
      ((base ↦ᵢ .LW .x5 .x12 src_off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 24) ↦ᵢ .SW .x12 .x5 dst_off) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ shifted_next) ** (.x11 ↦ᵣ mask) **
       (mem_src ↦ₘ src) ** (mem_next ↦ₘ next) ** (mem_dst ↦ₘ result)) := by
  sorry
-- ============================================================================
-- Per-limb Specs: SHR Last Limb (3 instructions)
-- ============================================================================

/-- Instruction memory assertion for shr_last_limb (3 instructions). -/
abbrev shr_last_limb_code (dst_off : BitVec 12) (base : Addr) : Assertion :=
  (base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 8) ↦ᵢ .SW .x12 .x5 dst_off)

/-- SHR last limb spec (3 instructions):
    LW x5, 28(x12); SRL x5,x5,x6; SW x12,x5,dst_off

    Computes: result = value[7] >>> bit_shift
    and stores at dst_off. This is the highest non-zero limb in a shift body.

    Preserves: x12, x6, x7, x10, x11, memory at value[7].
    Modifies: x5 (= result), memory at dst. -/
theorem shr_last_limb_spec (dst_off : BitVec 12)
    (sp src dst_old v5 bit_shift : Word) (base : Addr)
    (hvalid_src : isValidMemAccess (sp + signExtend12 (28 : BitVec 12)) = true)
    (hvalid_dst : isValidMemAccess (sp + signExtend12 dst_off) = true) :
    let mem_src := sp + signExtend12 (28 : BitVec 12)
    let mem_dst := sp + signExtend12 dst_off
    let result := src >>> (bit_shift.toNat % 32)
    cpsTriple base (base + 12) CodeReq.empty
      ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .SW .x12 .x5 dst_off) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (mem_src ↦ₘ src) ** (mem_dst ↦ₘ dst_old))
      ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .SW .x12 .x5 dst_off) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (mem_src ↦ₘ src) ** (mem_dst ↦ₘ result)) := by
  sorry
-- ============================================================================
-- Per-limb Specs: SHR Merge Limb In-place (7 instructions, src_off = dst_off)
-- ============================================================================

/-- Instruction memory assertion for shr_merge_limb_inplace (7 instructions). -/
abbrev shr_merge_limb_inplace_code (off next_off : BitVec 12) (base : Addr) : Assertion :=
  (base ↦ᵢ .LW .x5 .x12 off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 24) ↦ᵢ .SW .x12 .x5 off)

/-- SHR merge limb in-place spec (7 instructions):
    Same as shr_merge_limb_spec but src_off = dst_off. The source value is
    read then overwritten in place. Only 2 memory cells needed (no separate dst). -/
theorem shr_merge_limb_inplace_spec (off next_off : BitVec 12)
    (sp src next v5 v10 bit_shift anti_shift mask : Word) (base : Addr)
    (hvalid_loc : isValidMemAccess (sp + signExtend12 off) = true)
    (hvalid_next : isValidMemAccess (sp + signExtend12 next_off) = true) :
    let mem_loc := sp + signExtend12 off
    let mem_next := sp + signExtend12 next_off
    let shifted_src := src >>> (bit_shift.toNat % 32)
    let shifted_next := (next <<< (anti_shift.toNat % 32)) &&& mask
    let result := shifted_src ||| shifted_next
    cpsTriple base (base + 28) CodeReq.empty
      ((base ↦ᵢ .LW .x5 .x12 off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 24) ↦ᵢ .SW .x12 .x5 off) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (mem_loc ↦ₘ src) ** (mem_next ↦ₘ next))
      ((base ↦ᵢ .LW .x5 .x12 off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 24) ↦ᵢ .SW .x12 .x5 off) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ shifted_next) ** (.x11 ↦ᵣ mask) **
       (mem_loc ↦ₘ result) ** (mem_next ↦ₘ next)) := by
  sorry
-- ============================================================================
-- Per-limb Specs: SHR Last Limb In-place (3 instructions, dst_off = 28)
-- ============================================================================

/-- Instruction memory assertion for shr_last_limb_inplace (3 instructions). -/
abbrev shr_last_limb_inplace_code (base : Addr) : Assertion :=
  (base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 8) ↦ᵢ .SW .x12 .x5 28)

/-- SHR last limb in-place spec (3 instructions):
    LW x5, 28(x12); SRL x5,x5,x6; SW x12,x5,28
    Reads and writes the same memory cell at sp+28. -/
theorem shr_last_limb_inplace_spec
    (sp src v5 bit_shift : Word) (base : Addr)
    (hvalid : isValidMemAccess (sp + signExtend12 (28 : BitVec 12)) = true) :
    let mem := sp + signExtend12 (28 : BitVec 12)
    let result := src >>> (bit_shift.toNat % 32)
    cpsTriple base (base + 12) CodeReq.empty
      ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .SW .x12 .x5 28) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ src))
      ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .SW .x12 .x5 28) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ result)) := by
  sorry
-- ============================================================================
-- Zero-fill helper: SW x12, x0, offset (1 instruction)
-- ============================================================================

/-- Store zero at offset: SW x12, x0, offset.
    Writes 0 to memory at sp + sext(offset). -/
theorem shr_sw_zero_spec (offset : BitVec 12)
    (sp old_val : Word) (base : Addr)
    (hvalid : isValidMemAccess (sp + signExtend12 offset) = true) :
    cpsTriple base (base + 4) (CodeReq.singleton base (.SW .x12 .x0 offset))
      ((.x12 ↦ᵣ sp) ** ((sp + signExtend12 offset) ↦ₘ old_val))
      ((.x12 ↦ᵣ sp) ** ((sp + signExtend12 offset) ↦ₘ 0)) :=
  sw_x0_spec_gen .x12 sp old_val offset base hvalid

-- ============================================================================
-- Zero path spec (9 instructions): shift >= 256, result is all zeros
-- ============================================================================

/-- Instruction memory assertion for shr_zero_path (9 instructions). -/
abbrev shr_zero_path_code (base : Addr) : Assertion :=
  (base ↦ᵢ .ADDI .x12 .x12 32) ** ((base + 4) ↦ᵢ .SW .x12 .x0 0) **
  ((base + 8) ↦ᵢ .SW .x12 .x0 4) ** ((base + 12) ↦ᵢ .SW .x12 .x0 8) **
  ((base + 16) ↦ᵢ .SW .x12 .x0 12) ** ((base + 20) ↦ᵢ .SW .x12 .x0 16) **
  ((base + 24) ↦ᵢ .SW .x12 .x0 20) ** ((base + 28) ↦ᵢ .SW .x12 .x0 24) **
  ((base + 32) ↦ᵢ .SW .x12 .x0 28)

set_option maxHeartbeats 3200000 in
/-- Zero path spec: ADDI x12, x12, 32 followed by 8 SW x12, x0, N.
    This is used when shift >= 256. Advances sp by 32 and zeros all 8 result limbs. -/
theorem shr_zero_path_spec (sp : Word)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word)   -- old values at result locations
    (base : Addr)
    (hvalid : ValidMemRange (sp + 32) 8) :
    let nsp := sp + 32
    let code := shr_zero_path_code base
    cpsTriple base (base + 36) CodeReq.empty
      (code **
       (.x12 ↦ᵣ sp) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
      (code **
       (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 12) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 20) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) ** ((nsp + 28) ↦ₘ 0)) := by
  sorry
-- ============================================================================
-- Phase B spec: Extract parameters (7 instructions)
-- ============================================================================

/-- Instruction memory assertion for shr_phase_b (7 instructions). -/
abbrev shr_phase_b_code (base : Addr) : Assertion :=
  (base ↦ᵢ .ANDI .x6 .x5 31) ** ((base + 4) ↦ᵢ .SRLI .x5 .x5 5) **
  ((base + 8) ↦ᵢ .SLTU .x11 .x0 .x6) ** ((base + 12) ↦ᵢ .SUB .x11 .x0 .x11) **
  ((base + 16) ↦ᵢ .LI .x7 32) ** ((base + 20) ↦ᵢ .SUB .x7 .x7 .x6) **
  ((base + 24) ↦ᵢ .ADDI .x12 .x12 32)

set_option maxHeartbeats 1600000 in
/-- Phase B spec: Extract bit_shift, limb_shift, mask, anti_shift from shift0.
    ANDI x6,x5,31; SRLI x5,x5,5; SLTU x11,x0,x6; SUB x11,x0,x11;
    LI x7,32; SUB x7,x7,x6; ADDI x12,x12,32.
    Requires .x0 ↦ᵣ 0 for SLTU and SUB instructions using x0. -/
theorem shr_phase_b_spec (shift0 sp r6 r7 r11 : Word) (base : Addr) :
    let bit_shift := shift0 &&& signExtend12 31
    let limb_shift := shift0 >>> (5 : BitVec 5).toNat
    let cond := if BitVec.ult (0 : Word) bit_shift then (1 : Word) else 0
    let mask := (0 : Word) - cond
    let anti_shift := (32 : Word) - bit_shift
    let code := shr_phase_b_code base
    cpsTriple base (base + 28) CodeReq.empty
      (code **
       (.x5 ↦ᵣ shift0) ** (.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ r11) ** (.x7 ↦ᵣ r7) ** (.x12 ↦ᵣ sp))
      (code **
       (.x5 ↦ᵣ limb_shift) ** (.x6 ↦ᵣ bit_shift) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ mask) ** (.x7 ↦ᵣ anti_shift) ** (.x12 ↦ᵣ (sp + signExtend12 32))) := by
  sorry
-- ============================================================================
-- Cascade step helper: ADDI x10,x0,k; BEQ x5,x10,off (2 instructions)
-- ============================================================================

/-- Cascade step: ADDI x10,x0,k followed by BEQ x5,x10,off.
    Produces a cpsBranch with clean postconditions (no pure facts).
    Both taken and not-taken paths have the same register state;
    the branch is reflected only in which exit address is reached. -/
theorem shr_cascade_step_spec (v5 v10 : Word)
    (k : BitVec 12) (offset : BitVec 13) (base target : Addr)
    (htarget : (base + 4) + signExtend13 offset = target) :
    let k_val := (0 : Word) + signExtend12 k
    cpsBranch base
      (CodeReq.union (CodeReq.singleton base (.ADDI .x10 .x0 k))
       (CodeReq.singleton (base + 4) (.BEQ .x5 .x10 offset)))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      target
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val))
      (base + 8)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val)) := by
  sorry
-- ============================================================================
-- Phase C spec: cascade dispatch (13 instructions, cpsNBranch with 8 exits)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Phase C spec: cascade dispatch on limb_shift (0-7).
    BEQ x5,x0 for ls0, then 6 × (ADDI x10,x0,k; BEQ x5,x10) for ls1-ls6,
    fall-through to ls7. 13 instructions total. -/
theorem shr_phase_c_spec (v5 v10 : Word) (base : Addr)
    (e0 e1 e2 e3 e4 e5 e6 e7 : Addr)
    (he0 : base + signExtend13 864 = e0)
    (he1 : (base + 8) + signExtend13 668 = e1)
    (he2 : (base + 16) + signExtend13 496 = e2)
    (he3 : (base + 24) + signExtend13 348 = e3)
    (he4 : (base + 32) + signExtend13 224 = e4)
    (he5 : (base + 40) + signExtend13 124 = e5)
    (he6 : (base + 48) + signExtend13 48 = e6)
    (he7 : base + 52 = e7) :
    cpsNBranch base CodeReq.empty
      ((base ↦ᵢ .BEQ .x5 .x0 864) **
       ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
       ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
       ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
       ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
       ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
       ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48) **
       (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      [(e0, (base ↦ᵢ .BEQ .x5 .x0 864) **
            ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
            ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
            ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
            ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
            ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
            ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48) **
            (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10)),
       (e1, (base ↦ᵢ .BEQ .x5 .x0 864) **
            ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
            ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
            ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
            ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
            ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
            ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48) **
            (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1))),
       (e2, (base ↦ᵢ .BEQ .x5 .x0 864) **
            ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
            ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
            ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
            ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
            ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
            ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48) **
            (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2))),
       (e3, (base ↦ᵢ .BEQ .x5 .x0 864) **
            ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
            ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
            ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
            ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
            ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
            ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48) **
            (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 3))),
       (e4, (base ↦ᵢ .BEQ .x5 .x0 864) **
            ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
            ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
            ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
            ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
            ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
            ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48) **
            (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 4))),
       (e5, (base ↦ᵢ .BEQ .x5 .x0 864) **
            ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
            ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
            ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
            ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
            ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
            ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48) **
            (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 5))),
       (e6, (base ↦ᵢ .BEQ .x5 .x0 864) **
            ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
            ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
            ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
            ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
            ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
            ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48) **
            (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 6))),
       (e7, (base ↦ᵢ .BEQ .x5 .x0 864) **
            ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
            ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
            ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
            ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
            ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
            ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48) **
            (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 6)))] := by
  sorry
-- ============================================================================
-- Shift body spec: body_7 (limb_shift=7, 11 instructions)
-- ============================================================================

/-- Instruction memory assertion for shr_body_7 (11 instructions). -/
abbrev shr_body_7_code (jal_off : BitVec 21) (base : Addr) : Assertion :=
  (base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 8) ↦ᵢ .SW .x12 .x5 0) **
  ((base + 12) ↦ᵢ .SW .x12 .x0 4) ** ((base + 16) ↦ᵢ .SW .x12 .x0 8) **
  ((base + 20) ↦ᵢ .SW .x12 .x0 12) ** ((base + 24) ↦ᵢ .SW .x12 .x0 16) **
  ((base + 28) ↦ᵢ .SW .x12 .x0 20) ** ((base + 32) ↦ᵢ .SW .x12 .x0 24) **
  ((base + 36) ↦ᵢ .SW .x12 .x0 28) ** ((base + 40) ↦ᵢ .JAL .x0 jal_off)

set_option maxHeartbeats 3200000 in
/-- Shift body 7: limb_shift=7. Result[0] = value[7] >>> bit_shift, rest = 0.
    Comprises: shr_last_limb 0, 7× SW x12 x0 N, JAL x0 to exit.
    11 instructions from base to exit (via JAL). -/
theorem shr_body_7_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 40) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := v7 >>> (bit_shift.toNat % 32)
    let code := shr_body_7_code jal_off base
    cpsTriple base exit CodeReq.empty
      (code **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result0) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ 0) ** ((sp + 8) ↦ₘ 0) ** ((sp + 12) ↦ₘ 0) **
       ((sp + 16) ↦ₘ 0) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  sorry
-- ============================================================================
-- Shift body spec: body_6 (limb_shift=6, 17 instructions)
-- ============================================================================

/-- Instruction memory assertion for shr_body_6 (17 instructions). -/
abbrev shr_body_6_code (jal_off : BitVec 21) (base : Addr) : Assertion :=
  (base ↦ᵢ .LW .x5 .x12 24) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 8) ↦ᵢ .LW .x10 .x12 28) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
  ((base + 28) ↦ᵢ .LW .x5 .x12 28) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 36) ↦ᵢ .SW .x12 .x5 4) **
  ((base + 40) ↦ᵢ .SW .x12 .x0 8) ** ((base + 44) ↦ᵢ .SW .x12 .x0 12) **
  ((base + 48) ↦ᵢ .SW .x12 .x0 16) ** ((base + 52) ↦ᵢ .SW .x12 .x0 20) **
  ((base + 56) ↦ᵢ .SW .x12 .x0 24) ** ((base + 60) ↦ᵢ .SW .x12 .x0 28) **
  ((base + 64) ↦ᵢ .JAL .x0 jal_off)

set_option maxHeartbeats 3200000 in
/-- Shift body 6: limb_shift=6.
    Result[0] = (value[6] >>> bs) ||| ((value[7] <<< as) &&& mask),
    Result[1] = value[7] >>> bs, rest = 0.
    Comprises: shr_merge_limb(24,28,0), shr_last_limb(4), 6x SW, JAL.
    17 instructions from base to exit (via JAL). -/
theorem shr_body_6_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 64) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := v7 >>> (bit_shift.toNat % 32)
    let code := shr_body_6_code jal_off base
    cpsTriple base exit CodeReq.empty
      (code **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result1) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ 0) ** ((sp + 12) ↦ₘ 0) **
       ((sp + 16) ↦ₘ 0) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  sorry
-- ============================================================================
-- Shift body spec: body_5 (limb_shift=5, 23 instructions)
-- ============================================================================

/-- Instruction memory assertion for shr_body_5 (23 instructions). -/
abbrev shr_body_5_code (jal_off : BitVec 21) (base : Addr) : Assertion :=
  (base ↦ᵢ .LW .x5 .x12 20) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 8) ↦ᵢ .LW .x10 .x12 24) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
  ((base + 28) ↦ᵢ .LW .x5 .x12 24) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 36) ↦ᵢ .LW .x10 .x12 28) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
  ((base + 56) ↦ᵢ .LW .x5 .x12 28) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 64) ↦ᵢ .SW .x12 .x5 8) **
  ((base + 68) ↦ᵢ .SW .x12 .x0 12) ** ((base + 72) ↦ᵢ .SW .x12 .x0 16) **
  ((base + 76) ↦ᵢ .SW .x12 .x0 20) ** ((base + 80) ↦ᵢ .SW .x12 .x0 24) **
  ((base + 84) ↦ᵢ .SW .x12 .x0 28) **
  ((base + 88) ↦ᵢ .JAL .x0 jal_off)

set_option maxHeartbeats 3200000 in
/-- Shift body 5: limb_shift=5.
    Result[0] = (v5 >>> bs) ||| ((v6 <<< as) &&& mask),
    Result[1] = (v6 >>> bs) ||| ((v7 <<< as) &&& mask),
    Result[2] = v7 >>> bs, rest = 0.
    Comprises: merge_limb(20,24,0), merge_limb(24,28,4), last_limb(8), 5× SW, JAL.
    23 instructions from base to exit (via JAL). -/
theorem shr_body_5_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 88) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := v7 >>> (bit_shift.toNat % 32)
    let code := shr_body_5_code jal_off base
    cpsTriple base exit CodeReq.empty
      (code **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result2) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ 0) **
       ((sp + 16) ↦ₘ 0) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  sorry
-- ============================================================================
-- Shift body spec: body_4 (limb_shift=4, 29 instructions)
-- ============================================================================

/-- Instruction memory assertion for shr_body_4 (29 instructions). -/
abbrev shr_body_4_code (jal_off : BitVec 21) (base : Addr) : Assertion :=
  (base ↦ᵢ .LW .x5 .x12 16) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 8) ↦ᵢ .LW .x10 .x12 20) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
  ((base + 28) ↦ᵢ .LW .x5 .x12 20) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
  ((base + 56) ↦ᵢ .LW .x5 .x12 24) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 64) ↦ᵢ .LW .x10 .x12 28) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
  ((base + 84) ↦ᵢ .LW .x5 .x12 28) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 92) ↦ᵢ .SW .x12 .x5 12) **
  ((base + 96) ↦ᵢ .SW .x12 .x0 16) ** ((base + 100) ↦ᵢ .SW .x12 .x0 20) **
  ((base + 104) ↦ᵢ .SW .x12 .x0 24) ** ((base + 108) ↦ᵢ .SW .x12 .x0 28) **
  ((base + 112) ↦ᵢ .JAL .x0 jal_off)

set_option maxHeartbeats 3200000 in
/-- Shift body 4: limb_shift=4.
    Result[0] = (v4 >>> bs) ||| ((v5 <<< as) &&& mask),
    Result[1] = (v5 >>> bs) ||| ((v6 <<< as) &&& mask),
    Result[2] = (v6 >>> bs) ||| ((v7 <<< as) &&& mask),
    Result[3] = v7 >>> bs, rest = 0.
    Comprises: merge_limb(16,20,0), merge_limb(20,24,4), merge_limb(24,28,8),
    last_limb(12), 4× SW, JAL. 29 instructions. -/
theorem shr_body_4_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 112) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result3 := v7 >>> (bit_shift.toNat % 32)
    let code := shr_body_4_code jal_off base
    cpsTriple base exit CodeReq.empty
      (code **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result3) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ 0) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  sorry
-- ============================================================================
-- Shift body spec: body_3 (limb_shift=3, 35 instructions)
-- ============================================================================

/-- Instruction memory assertion for shr_body_3 (35 instructions). -/
abbrev shr_body_3_code (jal_off : BitVec 21) (base : Addr) : Assertion :=
  (base ↦ᵢ .LW .x5 .x12 12) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 8) ↦ᵢ .LW .x10 .x12 16) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
  ((base + 28) ↦ᵢ .LW .x5 .x12 16) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 36) ↦ᵢ .LW .x10 .x12 20) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
  ((base + 56) ↦ᵢ .LW .x5 .x12 20) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 64) ↦ᵢ .LW .x10 .x12 24) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
  ((base + 84) ↦ᵢ .LW .x5 .x12 24) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 92) ↦ᵢ .LW .x10 .x12 28) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
  ((base + 112) ↦ᵢ .LW .x5 .x12 28) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 120) ↦ᵢ .SW .x12 .x5 16) **
  ((base + 124) ↦ᵢ .SW .x12 .x0 20) ** ((base + 128) ↦ᵢ .SW .x12 .x0 24) **
  ((base + 132) ↦ᵢ .SW .x12 .x0 28) **
  ((base + 136) ↦ᵢ .JAL .x0 jal_off)

set_option maxHeartbeats 3200000 in
/-- Shift body 3: limb_shift=3.
    Result[0..3] = merge results, Result[4] = v7 >>> bs, rest = 0.
    Comprises: merge_limb(12,16,0), merge_limb(16,20,4), merge_limb(20,24,8),
    merge_limb(24,28,12), last_limb(16), 3x SW, JAL. 35 instructions. -/
theorem shr_body_3_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 136) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result3 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result4 := v7 >>> (bit_shift.toNat % 32)
    let code := shr_body_3_code jal_off base
    cpsTriple base exit CodeReq.empty
      (code **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result4) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ result4) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  sorry
-- ============================================================================
-- Shift body spec: body_2 (limb_shift=2, 41 instructions)
-- ============================================================================

/-- Instruction memory assertion for shr_body_2 (41 instructions). -/
abbrev shr_body_2_code (jal_off : BitVec 21) (base : Addr) : Assertion :=
  (base ↦ᵢ .LW .x5 .x12 8) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 8) ↦ᵢ .LW .x10 .x12 12) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
  ((base + 28) ↦ᵢ .LW .x5 .x12 12) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 36) ↦ᵢ .LW .x10 .x12 16) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
  ((base + 56) ↦ᵢ .LW .x5 .x12 16) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 64) ↦ᵢ .LW .x10 .x12 20) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
  ((base + 84) ↦ᵢ .LW .x5 .x12 20) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 92) ↦ᵢ .LW .x10 .x12 24) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
  ((base + 112) ↦ᵢ .LW .x5 .x12 24) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 120) ↦ᵢ .LW .x10 .x12 28) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
  ((base + 140) ↦ᵢ .LW .x5 .x12 28) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 148) ↦ᵢ .SW .x12 .x5 20) **
  ((base + 152) ↦ᵢ .SW .x12 .x0 24) ** ((base + 156) ↦ᵢ .SW .x12 .x0 28) **
  ((base + 160) ↦ᵢ .JAL .x0 jal_off)

set_option maxHeartbeats 3200000 in
/-- Shift body 2: limb_shift=2.
    Result[0..4] = merge results, Result[5] = v7 >>> bs, rest = 0.
    Comprises: 5× merge_limb, last_limb(20), 2× SW, JAL. 41 instructions. -/
theorem shr_body_2_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 160) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := (v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    let result3 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result4 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result5 := v7 >>> (bit_shift.toNat % 32)
    let code := shr_body_2_code jal_off base
    cpsTriple base exit CodeReq.empty
      (code **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ result4) ** ((sp + 20) ↦ₘ result5) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  sorry
/-- Instruction memory assertion for shr_body_1 (47 instructions). -/
abbrev shr_body_1_code (jal_off : BitVec 21) (base : Addr) : Assertion :=
  (base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 8) ↦ᵢ .LW .x10 .x12 8) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
  ((base + 28) ↦ᵢ .LW .x5 .x12 8) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 36) ↦ᵢ .LW .x10 .x12 12) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
  ((base + 56) ↦ᵢ .LW .x5 .x12 12) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 64) ↦ᵢ .LW .x10 .x12 16) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
  ((base + 84) ↦ᵢ .LW .x5 .x12 16) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 92) ↦ᵢ .LW .x10 .x12 20) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
  ((base + 112) ↦ᵢ .LW .x5 .x12 20) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 120) ↦ᵢ .LW .x10 .x12 24) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
  ((base + 140) ↦ᵢ .LW .x5 .x12 24) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 148) ↦ᵢ .LW .x10 .x12 28) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
  ((base + 168) ↦ᵢ .LW .x5 .x12 28) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 176) ↦ᵢ .SW .x12 .x5 24) **
  ((base + 180) ↦ᵢ .SW .x12 .x0 28) **
  ((base + 184) ↦ᵢ .JAL .x0 jal_off)

set_option maxHeartbeats 3200000 in
/-- Shift body 1: limb_shift=1.
    Result[0..5] = merge results, Result[6] = v7 >>> bs, Result[7] = 0.
    Comprises: 6× merge_limb, last_limb(24), 1× SW, JAL. 47 instructions. -/
theorem shr_body_1_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 184) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := (v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    let result3 := (v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    let result4 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result5 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result6 := v7 >>> (bit_shift.toNat % 32)
    let code := shr_body_1_code jal_off base
    cpsTriple base exit CodeReq.empty
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result6) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ result4) ** ((sp + 20) ↦ₘ result5) ** ((sp + 24) ↦ₘ result6) ** ((sp + 28) ↦ₘ 0)) := by
  sorry
/-- Instruction memory assertion for shr_body_0 (53 instructions). -/
abbrev shr_body_0_code (jal_off : BitVec 21) (base : Addr) : Assertion :=
  (base ↦ᵢ .LW .x5 .x12 0) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 8) ↦ᵢ .LW .x10 .x12 4) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
  ((base + 28) ↦ᵢ .LW .x5 .x12 4) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 36) ↦ᵢ .LW .x10 .x12 8) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
  ((base + 56) ↦ᵢ .LW .x5 .x12 8) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 64) ↦ᵢ .LW .x10 .x12 12) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
  ((base + 84) ↦ᵢ .LW .x5 .x12 12) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 92) ↦ᵢ .LW .x10 .x12 16) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
  ((base + 112) ↦ᵢ .LW .x5 .x12 16) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 120) ↦ᵢ .LW .x10 .x12 20) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
  ((base + 140) ↦ᵢ .LW .x5 .x12 20) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 148) ↦ᵢ .LW .x10 .x12 24) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
  ((base + 168) ↦ᵢ .LW .x5 .x12 24) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 176) ↦ᵢ .LW .x10 .x12 28) ** ((base + 180) ↦ᵢ .SLL .x10 .x10 .x7) **
  ((base + 184) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 188) ↦ᵢ .OR .x5 .x5 .x10) **
  ((base + 192) ↦ᵢ .SW .x12 .x5 24) **
  ((base + 196) ↦ᵢ .LW .x5 .x12 28) ** ((base + 200) ↦ᵢ .SRL .x5 .x5 .x6) **
  ((base + 204) ↦ᵢ .SW .x12 .x5 28) **
  ((base + 208) ↦ᵢ .JAL .x0 jal_off)

set_option maxHeartbeats 6400000 in
/-- Shift body 0: limb_shift=0. All merge limbs are in-place (src_off = dst_off).
    Result[i] = (v[i] >>> bs) ||| ((v[i+1] <<< as) &&& mask), Result[7] = v7 >>> bs.
    Comprises: 7x merge_limb_inplace, last_limb_inplace, JAL. 53 instructions. -/
theorem shr_body_0_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 208) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := (v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    let result3 := (v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    let result4 := (v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    let result5 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result6 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result7 := v7 >>> (bit_shift.toNat % 32)
    let code := shr_body_0_code jal_off base
    cpsTriple base exit CodeReq.empty
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result7) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ result4) ** ((sp + 20) ↦ₘ result5) ** ((sp + 24) ↦ₘ result6) ** ((sp + 28) ↦ₘ result7)) := by
  sorry
/-- Instruction memory assertion for shr_lw_or_acc (2 instructions). -/
abbrev shr_lw_or_acc_code (off : BitVec 12) (base : Addr) : Assertion :=
  (base ↦ᵢ .LW .x10 .x12 off) ** ((base + 4) ↦ᵢ .OR .x5 .x5 .x10)

theorem shr_lw_or_acc_spec (sp acc prev_x10 val : Word) (off : BitVec 12)
    (base : Addr)
    (hvalid : isValidMemAccess (sp + signExtend12 off) = true) :
    cpsTriple base (base + 8) CodeReq.empty
      ((base ↦ᵢ .LW .x10 .x12 off) ** ((base + 4) ↦ᵢ .OR .x5 .x5 .x10) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ acc) ** (.x10 ↦ᵣ prev_x10) ** ((sp + signExtend12 off) ↦ₘ val))
      ((base ↦ᵢ .LW .x10 .x12 off) ** ((base + 4) ↦ᵢ .OR .x5 .x5 .x10) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (acc ||| val)) ** (.x10 ↦ᵣ val) ** ((sp + signExtend12 off) ↦ₘ val)) := by
  sorry
private theorem regIs_to_regOwn (r : Reg) (v : Word) : ∀ h, (r ↦ᵣ v) h → (regOwn r) h :=
  fun _ hp => ⟨v, hp⟩

/-- Helper: weaken two concrete regs to regOwn in a flat conjunction.
    Given P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** Q, produce P ** regOwn r1 ** regOwn r2 ** Q. -/
private theorem weaken_two_regs (P Q : Assertion) (r1 r2 : Reg) (v1 v2 : Word) :
    ∀ h, (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** Q) h →
         (P ** (regOwn r1) ** (regOwn r2) ** Q) h :=
  sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn r1 v1)
      (sepConj_mono_left (regIs_implies_regOwn r2 v2)))
/-- Helper: weaken one concrete reg to regOwn in a flat conjunction.
    Given P ** (r ↦ᵣ v) ** Q, produce P ** regOwn r ** Q. -/
private theorem weaken_one_reg (P Q : Assertion) (r : Reg) (v : Word) :
    ∀ h, (P ** (r ↦ᵣ v) ** Q) h → (P ** (regOwn r) ** Q) h :=
  sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn r v))
set_option maxHeartbeats 6400000 in
/-- Phase A spec: Check shift >= 256.
    OR-reduce high limbs (s1|..|s7), BNE to zero_path if nonzero.
    Then load s0, SLTIU, BEQ to zero_path if s0 >= 256.
    17 instructions, cpsBranch with 2 exits:
    - Taken (zero_path): shift >= 256, x5/x10 are regOwn (existential)
    - Not-taken (base+68): shift < 256, x5=s0, x10 is regOwn -/
theorem shr_phase_a_spec (sp r5 r10 : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (base zero_path : Addr)
    (hzero : (base + 52) + signExtend13 1120 = zero_path)
    (hzero2 : (base + 64) + signExtend13 1108 = zero_path)
    (hvalid : ValidMemRange sp 8) :
    cpsBranch base CodeReq.empty
      ((base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .LW .x10 .x12 8) ** ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 12) ↦ᵢ .LW .x10 .x12 12) ** ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 20) ↦ᵢ .LW .x10 .x12 16) ** ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 28) ↦ᵢ .LW .x10 .x12 20) ** ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 44) ↦ᵢ .LW .x10 .x12 28) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
       ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
       ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
       ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
       ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
      zero_path
      ((base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .LW .x10 .x12 8) ** ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 12) ↦ᵢ .LW .x10 .x12 12) ** ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 20) ↦ᵢ .LW .x10 .x12 16) ** ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 28) ↦ᵢ .LW .x10 .x12 20) ** ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 44) ↦ᵢ .LW .x10 .x12 28) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
       ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
       ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
       ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) **
       (.x12 ↦ᵣ sp) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
       ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
      (base + 68)
      ((base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .LW .x10 .x12 8) ** ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 12) ↦ᵢ .LW .x10 .x12 12) ** ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 20) ↦ᵢ .LW .x10 .x12 16) ** ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 28) ↦ᵢ .LW .x10 .x12 20) ** ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 44) ↦ᵢ .LW .x10 .x12 28) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
       ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
       ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
       ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
       ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7)) := by
  sorry
/-- Helper: convert memIs to memOwn. -/
private theorem memIs_to_memOwn (a : Addr) (v : Word) : ∀ h, (a ↦ₘ v) h → (memOwn a) h :=
  fun _ hp => ⟨v, hp⟩

/-- Weaken zero path postcondition: convert concrete regs to regOwn, concrete mems to memOwn. -/
theorem weaken_zp_post (sp : Addr) (r6 r7 r11 : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word) : ∀ h,
    ((.x12 ↦ᵣ (sp + 32)) **
     ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 36) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 44) ↦ₘ (0 : Word)) **
     ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 52) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) ** ((sp + 60) ↦ₘ (0 : Word)) **
     (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
     (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7)) h →
    ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
     (regOwn .x10) ** (regOwn .x11) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
     (memOwn (sp + 32)) ** (memOwn (sp + 36)) ** (memOwn (sp + 40)) ** (memOwn (sp + 44)) **
     (memOwn (sp + 48)) ** (memOwn (sp + 52)) ** (memOwn (sp + 56)) ** (memOwn (sp + 60))) h := by
  intro h hyp
  have mid := sepConj_mono_right
    (sepConj_mono (memIs_implies_memOwn _ (0 : Word))
      (sepConj_mono (memIs_implies_memOwn _ (0 : Word))
        (sepConj_mono (memIs_implies_memOwn _ (0 : Word))
          (sepConj_mono (memIs_implies_memOwn _ (0 : Word))
            (sepConj_mono (memIs_implies_memOwn _ (0 : Word))
              (sepConj_mono (memIs_implies_memOwn _ (0 : Word))
                (sepConj_mono (memIs_implies_memOwn _ (0 : Word))
                  (sepConj_mono (memIs_implies_memOwn _ (0 : Word))
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono (regIs_implies_regOwn .x6 r6)
                        (sepConj_mono (regIs_implies_regOwn .x7 r7)
                          (sepConj_mono_left (regIs_implies_regOwn .x11 r11)))))))))))))))
    h hyp
  xperm_hyp mid
/-- Weaken body postcondition: convert concrete regs (.x5,.x6,.x7,.x10,.x11) to regOwn
    and concrete mems ((sp+32)..(sp+60)) to memOwn. Used for all 8 shift body exits. -/
theorem weaken_body_post (sp : Addr) (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (r5 r6 r7 r10 r11 : Word) (m0 m1 m2 m3 m4 m5 m6 m7 : Word) : ∀ h,
    ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ r5) ** (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) **
     (.x10 ↦ᵣ r10) ** (.x11 ↦ᵣ r11) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
     ((sp + 32) ↦ₘ m0) ** ((sp + 36) ↦ₘ m1) ** ((sp + 40) ↦ₘ m2) ** ((sp + 44) ↦ₘ m3) **
     ((sp + 48) ↦ₘ m4) ** ((sp + 52) ↦ₘ m5) ** ((sp + 56) ↦ₘ m6) ** ((sp + 60) ↦ₘ m7)) h →
    ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
     (regOwn .x10) ** (regOwn .x11) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
     (memOwn (sp + 32)) ** (memOwn (sp + 36)) ** (memOwn (sp + 40)) ** (memOwn (sp + 44)) **
     (memOwn (sp + 48)) ** (memOwn (sp + 52)) ** (memOwn (sp + 56)) ** (memOwn (sp + 60))) h :=
  sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x5 r5)
      (sepConj_mono (regIs_implies_regOwn .x6 r6)
        (sepConj_mono (regIs_implies_regOwn .x7 r7)
          (sepConj_mono (regIs_implies_regOwn .x10 r10)
            (sepConj_mono (regIs_implies_regOwn .x11 r11)
              (sepConj_mono_right -- skip .x0
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono (memIs_implies_memOwn _ m0)
                      (sepConj_mono (memIs_implies_memOwn _ m1)
                        (sepConj_mono (memIs_implies_memOwn _ m2)
                          (sepConj_mono (memIs_implies_memOwn _ m3)
                            (sepConj_mono (memIs_implies_memOwn _ m4)
                              (sepConj_mono (memIs_implies_memOwn _ m5)
                                (sepConj_mono (memIs_implies_memOwn _ m6)
                                  (memIs_implies_memOwn _ m7))))))))))))))))))))))

-- ============================================================================
-- Infrastructure for full composition
-- ============================================================================

/-- progAt_append for Program (needed because Program is a def, not abbrev). -/
private theorem progAt_append_program (base : Addr) (p1 p2 : Program) :
    progAt base (p1 ++ p2) = (progAt base p1 ** progAt (base + BitVec.ofNat 32 (4 * p1.length)) p2) :=
  progAt_append base p1 p2

-- Program length computations (via native_decide)
private theorem shr_phase_a_len : shr_phase_a.length = 17 := by native_decide
private theorem shr_phase_b_len : shr_phase_b.length = 7 := by native_decide
private theorem shr_phase_c_len : shr_phase_c.length = 13 := by native_decide
private theorem shr_body_7_len : shr_body_7.length = 11 := by native_decide
private theorem shr_body_6_len : shr_body_6.length = 17 := by native_decide
private theorem shr_body_5_len : shr_body_5.length = 23 := by native_decide
private theorem shr_body_4_len : shr_body_4.length = 29 := by native_decide
private theorem shr_body_3_len : shr_body_3.length = 35 := by native_decide
private theorem shr_body_2_len : shr_body_2.length = 41 := by native_decide
private theorem shr_body_1_len : shr_body_1.length = 47 := by native_decide
private theorem shr_body_0_len : shr_body_0.length = 53 := by native_decide

-- BitVec.ofNat normalization for phase offsets
private theorem bv_ofNat_pa : BitVec.ofNat 32 (4 * 17) = (68 : BitVec 32) := by native_decide
private theorem bv_ofNat_pb : BitVec.ofNat 32 (4 * 7) = (28 : BitVec 32) := by native_decide
private theorem bv_ofNat_pc : BitVec.ofNat 32 (4 * 13) = (52 : BitVec 32) := by native_decide
private theorem bv_ofNat_b7 : BitVec.ofNat 32 (4 * 11) = (44 : BitVec 32) := by native_decide
private theorem bv_ofNat_b6 : BitVec.ofNat 32 (4 * 17) = (68 : BitVec 32) := by native_decide
private theorem bv_ofNat_b5 : BitVec.ofNat 32 (4 * 23) = (92 : BitVec 32) := by native_decide
private theorem bv_ofNat_b4 : BitVec.ofNat 32 (4 * 29) = (116 : BitVec 32) := by native_decide
private theorem bv_ofNat_b3 : BitVec.ofNat 32 (4 * 35) = (140 : BitVec 32) := by native_decide
private theorem bv_ofNat_b2 : BitVec.ofNat 32 (4 * 41) = (164 : BitVec 32) := by native_decide
private theorem bv_ofNat_b1 : BitVec.ofNat 32 (4 * 47) = (188 : BitVec 32) := by native_decide
private theorem bv_ofNat_b0 : BitVec.ofNat 32 (4 * 53) = (212 : BitVec 32) := by native_decide

-- Address normalization for accumulated offsets
@[simp] private theorem addr_norm_96  (b : Addr) : b + 68 + 28 = b + 96 := by bv_omega
@[simp] private theorem addr_norm_148 (b : Addr) : b + 96 + 52 = b + 148 := by bv_omega
@[simp] private theorem addr_norm_192 (b : Addr) : b + 148 + 44 = b + 192 := by bv_omega
@[simp] private theorem addr_norm_260 (b : Addr) : b + 192 + 68 = b + 260 := by bv_omega
@[simp] private theorem addr_norm_352 (b : Addr) : b + 260 + 92 = b + 352 := by bv_omega
@[simp] private theorem addr_norm_468 (b : Addr) : b + 352 + 116 = b + 468 := by bv_omega
@[simp] private theorem addr_norm_608 (b : Addr) : b + 468 + 140 = b + 608 := by bv_omega
@[simp] private theorem addr_norm_772 (b : Addr) : b + 608 + 164 = b + 772 := by bv_omega
@[simp] private theorem addr_norm_960 (b : Addr) : b + 772 + 188 = b + 960 := by bv_omega
@[simp] private theorem addr_norm_1172 (b : Addr) : b + 960 + 212 = b + 1172 := by bv_omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
/-- Split progAt base evm_shr into per-phase progAt blocks. -/
theorem progAt_evm_shr_split (base : Addr) :
    progAt base evm_shr =
    (progAt base shr_phase_a **
     progAt (base + 68) shr_phase_b **
     progAt (base + 96) shr_phase_c **
     progAt (base + 148) shr_body_7 **
     progAt (base + 192) shr_body_6 **
     progAt (base + 260) shr_body_5 **
     progAt (base + 352) shr_body_4 **
     progAt (base + 468) shr_body_3 **
     progAt (base + 608) shr_body_2 **
     progAt (base + 772) shr_body_1 **
     progAt (base + 960) shr_body_0 **
     progAt (base + 1172) shr_zero_path) := by
  sorry
end EvmAsm
