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
    let code :=
      (base ↦ᵢ .LW .x5 .x12 src_off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
      ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
      ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
      ((base + 24) ↦ᵢ .SW .x12 .x5 dst_off)
    cpsTriple base (base + 28)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (mem_src ↦ₘ src) ** (mem_next ↦ₘ next) ** (mem_dst ↦ₘ dst_old))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ shifted_next) ** (.x11 ↦ᵣ mask) **
       (mem_src ↦ₘ src) ** (mem_next ↦ₘ next) ** (mem_dst ↦ₘ result)) := by
  runBlock

-- ============================================================================
-- Per-limb Specs: SHR Last Limb (3 instructions)
-- ============================================================================

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
    let code :=
      (base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
      ((base + 8) ↦ᵢ .SW .x12 .x5 dst_off)
    cpsTriple base (base + 12)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (mem_src ↦ₘ src) ** (mem_dst ↦ₘ dst_old))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (mem_src ↦ₘ src) ** (mem_dst ↦ₘ result)) := by
  runBlock

-- ============================================================================
-- Per-limb Specs: SHR Merge Limb In-place (7 instructions, src_off = dst_off)
-- ============================================================================

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
    let code :=
      (base ↦ᵢ .LW .x5 .x12 off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
      ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
      ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
      ((base + 24) ↦ᵢ .SW .x12 .x5 off)
    cpsTriple base (base + 28)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (mem_loc ↦ₘ src) ** (mem_next ↦ₘ next))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ shifted_next) ** (.x11 ↦ᵣ mask) **
       (mem_loc ↦ₘ result) ** (mem_next ↦ₘ next)) := by
  runBlock

-- ============================================================================
-- Per-limb Specs: SHR Last Limb In-place (3 instructions, dst_off = 28)
-- ============================================================================

/-- SHR last limb in-place spec (3 instructions):
    LW x5, 28(x12); SRL x5,x5,x6; SW x12,x5,28
    Reads and writes the same memory cell at sp+28. -/
theorem shr_last_limb_inplace_spec
    (sp src v5 bit_shift : Word) (base : Addr)
    (hvalid : isValidMemAccess (sp + signExtend12 (28 : BitVec 12)) = true) :
    let mem := sp + signExtend12 (28 : BitVec 12)
    let result := src >>> (bit_shift.toNat % 32)
    let code :=
      (base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
      ((base + 8) ↦ᵢ .SW .x12 .x5 28)
    cpsTriple base (base + 12)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ src))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ result)) := by
  runBlock

-- ============================================================================
-- Zero-fill helper: SW x12, x0, offset (1 instruction)
-- ============================================================================

/-- Store zero at offset: SW x12, x0, offset.
    Writes 0 to memory at sp + sext(offset). -/
theorem shr_sw_zero_spec (offset : BitVec 12)
    (sp old_val : Word) (base : Addr)
    (hvalid : isValidMemAccess (sp + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .SW .x12 .x0 offset) **
       (.x12 ↦ᵣ sp) ** ((sp + signExtend12 offset) ↦ₘ old_val))
      ((base ↦ᵢ .SW .x12 .x0 offset) **
       (.x12 ↦ᵣ sp) ** ((sp + signExtend12 offset) ↦ₘ 0)) :=
  sw_x0_spec_gen .x12 sp old_val offset base hvalid

-- ============================================================================
-- Zero path spec (9 instructions): shift >= 256, result is all zeros
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Zero path spec: ADDI x12, x12, 32 followed by 8 SW x12, x0, N.
    This is used when shift >= 256. Advances sp by 32 and zeros all 8 result limbs. -/
theorem shr_zero_path_spec (sp : Word)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word)   -- old values at result locations
    (base : Addr)
    (hvalid : ValidMemRange (sp + 32) 8) :
    let nsp := sp + 32
    let code :=
      (base ↦ᵢ .ADDI .x12 .x12 32) ** ((base + 4) ↦ᵢ .SW .x12 .x0 0) **
      ((base + 8) ↦ᵢ .SW .x12 .x0 4) ** ((base + 12) ↦ᵢ .SW .x12 .x0 8) **
      ((base + 16) ↦ᵢ .SW .x12 .x0 12) ** ((base + 20) ↦ᵢ .SW .x12 .x0 16) **
      ((base + 24) ↦ᵢ .SW .x12 .x0 20) ** ((base + 28) ↦ᵢ .SW .x12 .x0 24) **
      ((base + 32) ↦ᵢ .SW .x12 .x0 28)
    cpsTriple base (base + 36)
      (code **
       (.x12 ↦ᵣ sp) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
      (code **
       (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 12) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 20) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) ** ((nsp + 28) ↦ₘ 0)) := by
  -- Introduce nsp as opaque fvar to prevent address flattening
  intro nsp
  -- Compose: ADDI + 8x SW x0 via runBlock
  have A := addi_spec_gen_same .x12 sp 32 base (by nofun)
  rw [show sp + signExtend12 (32 : BitVec 12) = nsp from by simp only [signExtend12_32]; rfl] at A
  have S0 := sw_x0_spec_gen .x12 nsp d0 0 (base + 4) (by validMem)
  have S1 := sw_x0_spec_gen .x12 nsp d1 4 (base + 8) (by validMem)
  have S2 := sw_x0_spec_gen .x12 nsp d2 8 (base + 12) (by validMem)
  have S3 := sw_x0_spec_gen .x12 nsp d3 12 (base + 16) (by validMem)
  have S4 := sw_x0_spec_gen .x12 nsp d4 16 (base + 20) (by validMem)
  have S5 := sw_x0_spec_gen .x12 nsp d5 20 (base + 24) (by validMem)
  have S6 := sw_x0_spec_gen .x12 nsp d6 24 (base + 28) (by validMem)
  have S7 := sw_x0_spec_gen .x12 nsp d7 28 (base + 32) (by validMem)
  runBlock A S0 S1 S2 S3 S4 S5 S6 S7

-- ============================================================================
-- Phase B spec: Extract parameters (7 instructions)
-- ============================================================================

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
    let code :=
      (base ↦ᵢ .ANDI .x6 .x5 31) ** ((base + 4) ↦ᵢ .SRLI .x5 .x5 5) **
      ((base + 8) ↦ᵢ .SLTU .x11 .x0 .x6) ** ((base + 12) ↦ᵢ .SUB .x11 .x0 .x11) **
      ((base + 16) ↦ᵢ .LI .x7 32) ** ((base + 20) ↦ᵢ .SUB .x7 .x7 .x6) **
      ((base + 24) ↦ᵢ .ADDI .x12 .x12 32)
    cpsTriple base (base + 28)
      (code **
       (.x5 ↦ᵣ shift0) ** (.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ r11) ** (.x7 ↦ᵣ r7) ** (.x12 ↦ᵣ sp))
      (code **
       (.x5 ↦ᵣ limb_shift) ** (.x6 ↦ᵣ bit_shift) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ mask) ** (.x7 ↦ᵣ anti_shift) ** (.x12 ↦ᵣ (sp + signExtend12 32))) := by
  runBlock

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
      ((base ↦ᵢ .ADDI .x10 .x0 k) ** ((base + 4) ↦ᵢ .BEQ .x5 .x10 offset) **
       (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      target ((base ↦ᵢ .ADDI .x10 .x0 k) ** ((base + 4) ↦ᵢ .BEQ .x5 .x10 offset) **
              (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val))
      (base + 8) ((base ↦ᵢ .ADDI .x10 .x0 k) ** ((base + 4) ↦ᵢ .BEQ .x5 .x10 offset) **
                   (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val)) := by
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  -- Step 1: ADDI x10, x0, k at base (rd=x10, rs1=x0, rd≠rs1)
  have s1 := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .BEQ .x5 .x10 offset) ** (.x5 ↦ᵣ v5))
    (by pcFree) (addi_spec_gen .x10 .x0 v10 0 k base (by nofun) (by nofun))
  -- Step 2: BEQ x5, x10, offset at base+4
  -- Get BEQ spec and immediately drop pure facts from postconditions
  have s2_raw := beq_spec_gen .x5 .x10 offset v5 ((0 : Word) + signExtend12 k) (base + 4)
  rw [htarget, ha1] at s2_raw
  have s2 : cpsBranch (base + 4)
      (((base + 4) ↦ᵢ .BEQ .x5 .x10 offset) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)))
      target (((base + 4) ↦ᵢ .BEQ .x5 .x10 offset) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)))
      (base + 8) (((base + 4) ↦ᵢ .BEQ .x5 .x10 offset) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 k))) :=
    cpsBranch_consequence (base + 4) _ _ target _ _ (base + 8) _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ (v5 = (0 : Word) + signExtend12 k) h').1 hp').1)) h hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ (v5 ≠ (0 : Word) + signExtend12 k) h').1 hp').1)) h hp)
      s2_raw
  -- Frame BEQ with ADDI instrAt and x0
  have s2f := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .ADDI .x10 .x0 k) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) s2
  -- Compose: cpsTriple followed by cpsBranch, with permutation
  have composed := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1 s2f
  -- Final permutation of postconditions
  exact cpsBranch_consequence _
    _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

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
    cpsNBranch base
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
  -- Address arithmetic: cascade step not-taken exits (base' + 8)
  have ha1 : (base + 4 : Addr) + 8 = base + 12 := by bv_omega
  have ha2 : (base + 12 : Addr) + 8 = base + 20 := by bv_omega
  have ha3 : (base + 20 : Addr) + 8 = base + 28 := by bv_omega
  have ha4 : (base + 28 : Addr) + 8 = base + 36 := by bv_omega
  have ha5 : (base + 36 : Addr) + 8 = base + 44 := by bv_omega
  have ha6 : (base + 44 : Addr) + 8 = base + 52 := by bv_omega
  -- Address arithmetic: cascade step's inner BEQ addresses ((base' + 4) + 4 = base' + 8)
  -- Needed so that shr_cascade_step_spec's htarget can be satisfied
  have hc1 : ((base + 4 : Addr) + 4) + signExtend13 668 = e1 := by rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]; exact he1
  have hc2 : ((base + 12 : Addr) + 4) + signExtend13 496 = e2 := by rw [show (base + 12 : Addr) + 4 = base + 16 from by bv_omega]; exact he2
  have hc3 : ((base + 20 : Addr) + 4) + signExtend13 348 = e3 := by rw [show (base + 20 : Addr) + 4 = base + 24 from by bv_omega]; exact he3
  have hc4 : ((base + 28 : Addr) + 4) + signExtend13 224 = e4 := by rw [show (base + 28 : Addr) + 4 = base + 32 from by bv_omega]; exact he4
  have hc5 : ((base + 36 : Addr) + 4) + signExtend13 124 = e5 := by rw [show (base + 36 : Addr) + 4 = base + 40 from by bv_omega]; exact he5
  have hc6 : ((base + 44 : Addr) + 4) + signExtend13 48 = e6 := by rw [show (base + 44 : Addr) + 4 = base + 48 from by bv_omega]; exact he6
  -- Address arithmetic: normalize (base + N) + 4 = base + (N+4) for BEQ instrAt
  have hb1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have hb2 : (base + 12 : Addr) + 4 = base + 16 := by bv_omega
  have hb3 : (base + 20 : Addr) + 4 = base + 24 := by bv_omega
  have hb4 : (base + 28 : Addr) + 4 = base + 32 := by bv_omega
  have hb5 : (base + 36 : Addr) + 4 = base + 40 := by bv_omega
  have hb6 : (base + 44 : Addr) + 4 = base + 48 := by bv_omega
  -- Abbreviation for the instrAt block (all 13 instructions)
  -- We'll use framing to carry the instrAt through each step.
  -- Step 0: BEQ x5 x0 864 at base
  -- First get the raw BEQ spec and drop pure facts
  have beq0_raw := beq_spec_gen .x5 .x0 864 v5 (0 : Word) base
  rw [he0] at beq0_raw
  have beq0 : cpsBranch base
      ((base ↦ᵢ .BEQ .x5 .x0 864) ** (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)))
      e0 ((base ↦ᵢ .BEQ .x5 .x0 864) ** (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 4) ((base ↦ᵢ .BEQ .x5 .x0 864) ** (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence base _ _ e0 _ _ (base + 4) _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ (v5 = (0 : Word)) h').1 hp').1)) h hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ (v5 ≠ (0 : Word)) h').1 hp').1)) h hp)
      beq0_raw
  -- Frame beq0 with remaining instrAt + x10
  have beq0f := cpsBranch_frame_left _ _ _ _ _ _
    (((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
     ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
     ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
     ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
     ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
     ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48) **
     (.x10 ↦ᵣ v10))
    (by pcFree) beq0
  -- Step 1: cascade step at base+4 (ADDI x10,x0,1 + BEQ x5,x10,668)
  have cs1 := shr_cascade_step_spec v5 v10 1 668 (base + 4) e1 hc1
  rw [ha1, hb1] at cs1
  have cs1f := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .BEQ .x5 .x0 864) **
     ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
     ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
     ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
     ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
     ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48))
    (by pcFree) cs1
  -- Step 2: cascade step at base+12
  have cs2 := shr_cascade_step_spec v5 ((0 : Word) + signExtend12 1) 2 496 (base + 12) e2 hc2
  rw [ha2, hb2] at cs2
  have cs2f := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .BEQ .x5 .x0 864) **
     ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
     ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
     ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
     ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
     ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48))
    (by pcFree) cs2
  -- Step 3: cascade step at base+20
  have cs3 := shr_cascade_step_spec v5 ((0 : Word) + signExtend12 2) 3 348 (base + 20) e3 hc3
  rw [ha3, hb3] at cs3
  have cs3f := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .BEQ .x5 .x0 864) **
     ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
     ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
     ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
     ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
     ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48))
    (by pcFree) cs3
  -- Step 4: cascade step at base+28
  have cs4 := shr_cascade_step_spec v5 ((0 : Word) + signExtend12 3) 4 224 (base + 28) e4 hc4
  rw [ha4, hb4] at cs4
  have cs4f := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .BEQ .x5 .x0 864) **
     ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
     ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
     ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
     ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
     ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48))
    (by pcFree) cs4
  -- Step 5: cascade step at base+36
  have cs5 := shr_cascade_step_spec v5 ((0 : Word) + signExtend12 4) 5 124 (base + 36) e5 hc5
  rw [ha5, hb5] at cs5
  have cs5f := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .BEQ .x5 .x0 864) **
     ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
     ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
     ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
     ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
     ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48))
    (by pcFree) cs5
  -- Step 6: cascade step at base+44
  have cs6 := shr_cascade_step_spec v5 ((0 : Word) + signExtend12 5) 6 48 (base + 44) e6 hc6
  rw [ha6, hb6] at cs6
  have cs6f := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .BEQ .x5 .x0 864) **
     ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
     ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
     ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
     ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
     ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124))
    (by pcFree) cs6
  -- Now chain them together using cpsBranch_cons_cpsNBranch_with_perm
  -- Start from the last: cs6 not-taken is base+52 = e7, which is the fallthrough
  -- Fallthrough: cpsNBranch_refl at base+52 with identity
  have ft := cpsNBranch_refl (base + 52)
    ((base ↦ᵢ .BEQ .x5 .x0 864) **
     ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
     ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
     ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
     ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
     ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
     ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48) **
     (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 6)))
    _ (fun _ hp => hp)
  -- Chain cs6 with fallthrough
  have n7 := cpsBranch_cons_cpsNBranch_with_perm _ _ _ _ (base + 52) _ _ _
    (fun h hp => by xperm_hyp hp) cs6f ft
  -- Chain cs5 with n7
  have n6 := cpsBranch_cons_cpsNBranch_with_perm _ _ _ _ (base + 44) _ _ _
    (fun h hp => by xperm_hyp hp) cs5f n7
  -- Chain cs4 with n6
  have n5 := cpsBranch_cons_cpsNBranch_with_perm _ _ _ _ (base + 36) _ _ _
    (fun h hp => by xperm_hyp hp) cs4f n6
  -- Chain cs3 with n5
  have n4 := cpsBranch_cons_cpsNBranch_with_perm _ _ _ _ (base + 28) _ _ _
    (fun h hp => by xperm_hyp hp) cs3f n5
  -- Chain cs2 with n4
  have n3 := cpsBranch_cons_cpsNBranch_with_perm _ _ _ _ (base + 20) _ _ _
    (fun h hp => by xperm_hyp hp) cs2f n4
  -- Chain cs1 with n3
  have n2 := cpsBranch_cons_cpsNBranch_with_perm _ _ _ _ (base + 12) _ _ _
    (fun h hp => by xperm_hyp hp) cs1f n3
  -- Chain beq0 with n2
  have n1 := cpsBranch_cons_cpsNBranch_with_perm _ _ _ _ (base + 4) _ _ _
    (fun h hp => by xperm_hyp hp) beq0f n2
  -- Weaken precondition to match goal's flat shape
  have n1' := cpsNBranch_weaken_pre base _
    ((base ↦ᵢ .BEQ .x5 .x0 864) **
     ((base + 4) ↦ᵢ .ADDI .x10 .x0 1) ** ((base + 8) ↦ᵢ .BEQ .x5 .x10 668) **
     ((base + 12) ↦ᵢ .ADDI .x10 .x0 2) ** ((base + 16) ↦ᵢ .BEQ .x5 .x10 496) **
     ((base + 20) ↦ᵢ .ADDI .x10 .x0 3) ** ((base + 24) ↦ᵢ .BEQ .x5 .x10 348) **
     ((base + 28) ↦ᵢ .ADDI .x10 .x0 4) ** ((base + 32) ↦ᵢ .BEQ .x5 .x10 224) **
     ((base + 36) ↦ᵢ .ADDI .x10 .x0 5) ** ((base + 40) ↦ᵢ .BEQ .x5 .x10 124) **
     ((base + 44) ↦ᵢ .ADDI .x10 .x0 6) ** ((base + 48) ↦ᵢ .BEQ .x5 .x10 48) **
     (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
    _ (fun h hp => by xperm_hyp hp) n1
  -- Weaken postconditions to match goal
  -- n1' exits: [(e0, Q0), (e1, Q1), ..., (e6, Q6), (base+52, Q7)]
  -- goal exits: [(e0, Q0'), ..., (e6, Q6'), (e7, Q7')]
  -- For exits 0-6: address matches by rfl, post matches by xperm_hyp
  -- For exit 7: address matches via he7.symm, post matches by xperm_hyp
  exact cpsNBranch_weaken_posts _ _ _ _ n1'
    (fun ex hmem => by
      simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false, false_or] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- e0 case
      · exact ⟨_, List.Mem.head _, rfl, fun h hp => by xperm_hyp hp⟩
      -- e1 case
      · exact ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, fun h hp => by xperm_hyp hp⟩
      -- e2 case
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl, fun h hp => by xperm_hyp hp⟩
      -- e3 case
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))), rfl, fun h hp => by xperm_hyp hp⟩
      -- e4 case
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))), rfl, fun h hp => by xperm_hyp hp⟩
      -- e5 case
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))), rfl, fun h hp => by xperm_hyp hp⟩
      -- e6 case
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))), rfl, fun h hp => by xperm_hyp hp⟩
      -- e7 case (base + 52 = e7)
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))), he7.symm, fun h hp => by xperm_hyp hp⟩)

-- ============================================================================
-- Shift body spec: body_7 (limb_shift=7, 11 instructions)
-- ============================================================================

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
    let code :=
      (base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
      ((base + 8) ↦ᵢ .SW .x12 .x5 0) **
      ((base + 12) ↦ᵢ .SW .x12 .x0 4) ** ((base + 16) ↦ᵢ .SW .x12 .x0 8) **
      ((base + 20) ↦ᵢ .SW .x12 .x0 12) ** ((base + 24) ↦ᵢ .SW .x12 .x0 16) **
      ((base + 28) ↦ᵢ .SW .x12 .x0 20) ** ((base + 32) ↦ᵢ .SW .x12 .x0 24) **
      ((base + 36) ↦ᵢ .SW .x12 .x0 28) ** ((base + 40) ↦ᵢ .JAL .x0 jal_off)
    cpsTriple base exit
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
  -- Compose: shr_last_limb(0) + 7x SW x0 + JAL via runBlock
  have LL := shr_last_limb_spec 0 sp v7 v0 v5 bit_shift base (by validMem) (by validMem)
  have S0 := sw_x0_spec_gen .x12 sp v1 4 (base + 12) (by validMem)
  have S1 := sw_x0_spec_gen .x12 sp v2 8 (base + 16) (by validMem)
  have S2 := sw_x0_spec_gen .x12 sp v3 12 (base + 20) (by validMem)
  have S3 := sw_x0_spec_gen .x12 sp v4 16 (base + 24) (by validMem)
  have S4 := sw_x0_spec_gen .x12 sp v5v 20 (base + 28) (by validMem)
  have S5 := sw_x0_spec_gen .x12 sp v6 24 (base + 32) (by validMem)
  have S6 := sw_x0_spec_gen .x12 sp v7 28 (base + 36) (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 40)
  rw [hexit] at JL
  runBlock LL S0 S1 S2 S3 S4 S5 S6 JL

-- ============================================================================
-- Shift body spec: body_6 (limb_shift=6, 17 instructions)
-- ============================================================================

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
    let code :=
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
    cpsTriple base exit
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
  -- Compose: 1x merge_limb + last_limb + 6x SW x0 + JAL via runBlock
  have MM := shr_merge_limb_spec 24 28 0 sp v6 v7 v0 v5 v10 bit_shift anti_shift mask base (by validMem) (by validMem) (by validMem)
  have LL := shr_last_limb_spec 4 sp v7 v1
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 28) (by validMem) (by validMem)
  have T0 := sw_x0_spec_gen .x12 sp v2 8 (base + 40) (by validMem)
  have T1 := sw_x0_spec_gen .x12 sp v3 12 (base + 44) (by validMem)
  have T2 := sw_x0_spec_gen .x12 sp v4 16 (base + 48) (by validMem)
  have T3 := sw_x0_spec_gen .x12 sp v5v 20 (base + 52) (by validMem)
  have T4 := sw_x0_spec_gen .x12 sp v6 24 (base + 56) (by validMem)
  have T5 := sw_x0_spec_gen .x12 sp v7 28 (base + 60) (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 64)
  rw [hexit] at JL
  runBlock MM LL T0 T1 T2 T3 T4 T5 JL

-- ============================================================================
-- Shift body spec: body_5 (limb_shift=5, 23 instructions)
-- ============================================================================

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
    let code :=
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
    cpsTriple base exit
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
  -- Compose: 2x merge_limb + last_limb + 5x SW x0 + JAL via runBlock
  have MM1 := shr_merge_limb_spec 20 24 0 sp v5v v6 v0 v5 v10 bit_shift anti_shift mask base (by validMem) (by validMem) (by validMem)
  have MM2 := shr_merge_limb_spec 24 28 4 sp v6 v7 v1
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28) (by validMem) (by validMem) (by validMem)
  have LL := shr_last_limb_spec 8 sp v7 v2
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 56) (by validMem) (by validMem)
  have T0 := sw_x0_spec_gen .x12 sp v3 12 (base + 68) (by validMem)
  have T1 := sw_x0_spec_gen .x12 sp v4 16 (base + 72) (by validMem)
  have T2 := sw_x0_spec_gen .x12 sp v5v 20 (base + 76) (by validMem)
  have T3 := sw_x0_spec_gen .x12 sp v6 24 (base + 80) (by validMem)
  have T4 := sw_x0_spec_gen .x12 sp v7 28 (base + 84) (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 88)
  rw [hexit] at JL
  runBlock MM1 MM2 LL T0 T1 T2 T3 T4 JL

-- ============================================================================
-- Shift body spec: body_4 (limb_shift=4, 29 instructions)
-- ============================================================================

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
    let code :=
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
    cpsTriple base exit
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
  -- Compose: 3x merge_limb + last_limb + 4x SW x0 + JAL via runBlock
  have MM1 := shr_merge_limb_spec 16 20 0 sp v4 v5v v0 v5 v10 bit_shift anti_shift mask base (by validMem) (by validMem) (by validMem)
  have MM2 := shr_merge_limb_spec 20 24 4 sp v5v v6 v1
    ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))
    ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28) (by validMem) (by validMem) (by validMem)
  have MM3 := shr_merge_limb_spec 24 28 8 sp v6 v7 v2
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 56) (by validMem) (by validMem) (by validMem)
  have LL := shr_last_limb_spec 12 sp v7 v3
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 84) (by validMem) (by validMem)
  have T0 := sw_x0_spec_gen .x12 sp v4 16 (base + 96) (by validMem)
  have T1 := sw_x0_spec_gen .x12 sp v5v 20 (base + 100) (by validMem)
  have T2 := sw_x0_spec_gen .x12 sp v6 24 (base + 104) (by validMem)
  have T3 := sw_x0_spec_gen .x12 sp v7 28 (base + 108) (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 112)
  rw [hexit] at JL
  runBlock MM1 MM2 MM3 LL T0 T1 T2 T3 JL

-- ============================================================================
-- Shift body spec: body_3 (limb_shift=3, 35 instructions)
-- ============================================================================

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
    let code :=
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
    cpsTriple base exit
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
  -- Compose: 4x merge_limb + last_limb + 3x SW x0 + JAL via runBlock
  have MM1 := shr_merge_limb_spec 12 16 0 sp v3 v4 v0 v5 v10 bit_shift anti_shift mask base (by validMem) (by validMem) (by validMem)
  have MM2 := shr_merge_limb_spec 16 20 4 sp v4 v5v v1
    ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28) (by validMem) (by validMem) (by validMem)
  have MM3 := shr_merge_limb_spec 20 24 8 sp v5v v6 v2
    ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))
    ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 56) (by validMem) (by validMem) (by validMem)
  have MM4 := shr_merge_limb_spec 24 28 12 sp v6 v7 v3
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 84) (by validMem) (by validMem) (by validMem)
  have LL := shr_last_limb_spec 16 sp v7 v4
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 112) (by validMem) (by validMem)
  have T0 := sw_x0_spec_gen .x12 sp v5v 20 (base + 124) (by validMem)
  have T1 := sw_x0_spec_gen .x12 sp v6 24 (base + 128) (by validMem)
  have T2 := sw_x0_spec_gen .x12 sp v7 28 (base + 132) (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 136)
  rw [hexit] at JL
  runBlock MM1 MM2 MM3 MM4 LL T0 T1 T2 JL
-- ============================================================================
-- Shift body spec: body_2 (limb_shift=2, 41 instructions)
-- ============================================================================

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
    let code :=
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
    cpsTriple base exit
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
  -- Compose: 5x merge_limb + last_limb + 2x SW x0 + JAL via runBlock
  have MM1 := shr_merge_limb_spec 8 12 0 sp v2 v3 v0 v5 v10 bit_shift anti_shift mask base (by validMem) (by validMem) (by validMem)
  have MM2 := shr_merge_limb_spec 12 16 4 sp v3 v4 v1
    ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28) (by validMem) (by validMem) (by validMem)
  have MM3 := shr_merge_limb_spec 16 20 8 sp v4 v5v v2
    ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 56) (by validMem) (by validMem) (by validMem)
  have MM4 := shr_merge_limb_spec 20 24 12 sp v5v v6 v3
    ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))
    ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 84) (by validMem) (by validMem) (by validMem)
  have MM5 := shr_merge_limb_spec 24 28 16 sp v6 v7 v4
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 112) (by validMem) (by validMem) (by validMem)
  have LL := shr_last_limb_spec 20 sp v7 v5v
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 140) (by validMem) (by validMem)
  have T0 := sw_x0_spec_gen .x12 sp v6 24 (base + 152) (by validMem)
  have T1 := sw_x0_spec_gen .x12 sp v7 28 (base + 156) (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 160)
  rw [hexit] at JL
  runBlock MM1 MM2 MM3 MM4 MM5 LL T0 T1 JL
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
    let code :=
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
    cpsTriple base exit
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
  -- Compose: 6x merge_limb + last_limb + 1x SW x0 + JAL via runBlock
  have MM1 := shr_merge_limb_spec 4 8 0 sp v1 v2 v0 v5 v10 bit_shift anti_shift mask base (by validMem) (by validMem) (by validMem)
  have MM2 := shr_merge_limb_spec 8 12 4 sp v2 v3 v1
    ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v2 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28) (by validMem) (by validMem) (by validMem)
  have MM3 := shr_merge_limb_spec 12 16 8 sp v3 v4 v2
    ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 56) (by validMem) (by validMem) (by validMem)
  have MM4 := shr_merge_limb_spec 16 20 12 sp v4 v5v v3
    ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 84) (by validMem) (by validMem) (by validMem)
  have MM5 := shr_merge_limb_spec 20 24 16 sp v5v v6 v4
    ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))
    ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 112) (by validMem) (by validMem) (by validMem)
  have MM6 := shr_merge_limb_spec 24 28 20 sp v6 v7 v5v
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 140) (by validMem) (by validMem) (by validMem)
  have LL := shr_last_limb_spec 24 sp v7 v6
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 168) (by validMem) (by validMem)
  have T0 := sw_x0_spec_gen .x12 sp v7 28 (base + 180) (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 184)
  rw [hexit] at JL
  runBlock MM1 MM2 MM3 MM4 MM5 MM6 LL T0 JL
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
    let code :=
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
    cpsTriple base exit
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
  -- Compose: 7x merge_limb_inplace + last_limb_inplace + JAL via runBlock
  have MM1 := shr_merge_limb_inplace_spec 0 4 sp v0 v1 v5 v10 bit_shift anti_shift mask base (by validMem) (by validMem)
  have MM2 := shr_merge_limb_inplace_spec 4 8 sp v1 v2
    ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v1 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28) (by validMem) (by validMem)
  have MM3 := shr_merge_limb_inplace_spec 8 12 sp v2 v3
    ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v2 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 56) (by validMem) (by validMem)
  have MM4 := shr_merge_limb_inplace_spec 12 16 sp v3 v4
    ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 84) (by validMem) (by validMem)
  have MM5 := shr_merge_limb_inplace_spec 16 20 sp v4 v5v
    ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 112) (by validMem) (by validMem)
  have MM6 := shr_merge_limb_inplace_spec 20 24 sp v5v v6
    ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))
    ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 140) (by validMem) (by validMem)
  have MM7 := shr_merge_limb_inplace_spec 24 28 sp v6 v7
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 168) (by validMem) (by validMem)
  have LL := shr_last_limb_inplace_spec sp v7
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 196) (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 208)
  rw [hexit] at JL
  runBlock MM1 MM2 MM3 MM4 MM5 MM6 MM7 LL JL
theorem shr_lw_or_acc_spec (sp acc prev_x10 val : Word) (off : BitVec 12)
    (base : Addr)
    (hvalid : isValidMemAccess (sp + signExtend12 off) = true) :
    let code :=
      (base ↦ᵢ .LW .x10 .x12 off) ** ((base + 4) ↦ᵢ .OR .x5 .x5 .x10)
    cpsTriple base (base + 8)
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ acc) ** (.x10 ↦ᵣ prev_x10) ** ((sp + signExtend12 off) ↦ₘ val))
      (code **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (acc ||| val)) ** (.x10 ↦ᵣ val) ** ((sp + signExtend12 off) ↦ₘ val)) := by
  runBlock
private theorem regIs_to_regOwn (r : Reg) (v : Word) : ∀ h, (r ↦ᵣ v) h → (regOwn r) h :=
  fun _ hp => ⟨v, hp⟩

/-- Helper: weaken two concrete regs to regOwn in a flat conjunction.
    Given P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** Q, produce P ** regOwn r1 ** regOwn r2 ** Q. -/
private theorem weaken_two_regs (P Q : Assertion) (r1 r2 : Reg) (v1 v2 : Word) :
    ∀ h, (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** Q) h →
         (P ** (regOwn r1) ** (regOwn r2) ** Q) h := by
  intro h hp
  exact sepConj_mono_right (sepConj_mono (regIs_to_regOwn r1 v1) (sepConj_mono_left (regIs_to_regOwn r2 v2))) h hp

/-- Helper: weaken one concrete reg to regOwn in a flat conjunction.
    Given P ** (r ↦ᵣ v) ** Q, produce P ** regOwn r ** Q. -/
private theorem weaken_one_reg (P Q : Assertion) (r : Reg) (v : Word) :
    ∀ h, (P ** (r ↦ᵣ v) ** Q) h → (P ** (regOwn r) ** Q) h := by
  intro h hp
  exact sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn r v)) h hp

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
    cpsBranch base
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
  -- Address arithmetic
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have ha52 : (base + 52 : Addr) + 4 = base + 56 := by bv_omega
  have ha56 : (base + 56 : Addr) + 4 = base + 60 := by bv_omega
  have ha60 : (base + 60 : Addr) + 4 = base + 64 := by bv_omega
  have ha64 : (base + 64 : Addr) + 4 = base + 68 := by bv_omega
  -- Step 1: LW x5 x12 4 at base (loads s1 into x5)
  have lw1 := lw_spec_gen .x5 .x12 sp r5 s1 4 base (by nofun)
    (by validMem)
  simp only [signExtend12_4] at lw1
  -- Exit address normalization for shr_lw_or_acc_spec calls
  have he4  : (base + 4  : Addr) + 8 = base + 12 := by bv_omega
  have he12 : (base + 12 : Addr) + 8 = base + 20 := by bv_omega
  have he20 : (base + 20 : Addr) + 8 = base + 28 := by bv_omega
  have he28 : (base + 28 : Addr) + 8 = base + 36 := by bv_omega
  have he36 : (base + 36 : Addr) + 8 = base + 44 := by bv_omega
  have he44 : (base + 44 : Addr) + 8 = base + 52 := by bv_omega
  have lw1f := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .LW .x10 .x12 8) ** ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LW .x10 .x12 12) ** ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LW .x10 .x12 16) ** ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 28) ↦ᵢ .LW .x10 .x12 20) ** ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 44) ↦ᵢ .LW .x10 .x12 28) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
     ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
     ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) **
     (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
    (by pcFree) lw1
  -- Step 2: shr_lw_or_acc_spec at base+4 (LW x10 x12 8 + OR x5 x5 x10) -> x5 = s1|s2
  have lor2 := shr_lw_or_acc_spec sp s1 r10 s2 8 (base + 4)
    (by validMem)
  simp only [signExtend12_8] at lor2
  rw [ha1, he4] at lor2
  have lor2f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 4) **
     ((base + 12) ↦ᵢ .LW .x10 .x12 12) ** ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LW .x10 .x12 16) ** ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 28) ↦ᵢ .LW .x10 .x12 20) ** ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 44) ↦ᵢ .LW .x10 .x12 28) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
     ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
     ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) **
     (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
    (by pcFree) lor2
  have c12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) lw1f lor2f; clear lw1 lw1f lor2 lor2f
  -- Step 3: shr_lw_or_acc_spec at base+12 -> x5 = s1|s2|s3
  have lor3 := shr_lw_or_acc_spec sp (s1 ||| s2) s2 s3 12 (base + 12)
    (by validMem)
  simp only [signExtend12_12] at lor3
  rw [show (base + 12 : Addr) + 4 = base + 16 from by bv_omega, he12] at lor3
  have lor3f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .LW .x10 .x12 8) ** ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LW .x10 .x12 16) ** ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 28) ↦ᵢ .LW .x10 .x12 20) ** ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 44) ↦ᵢ .LW .x10 .x12 28) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
     ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
     ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) **
     (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
    (by pcFree) lor3
  have c13 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c12 lor3f; clear c12 lor3 lor3f
  -- Step 4: shr_lw_or_acc_spec at base+20 -> x5 = s1|s2|s3|s4
  have lor4 := shr_lw_or_acc_spec sp (s1 ||| s2 ||| s3) s3 s4 16 (base + 20)
    (by validMem)
  simp only [signExtend12_16] at lor4
  rw [show (base + 20 : Addr) + 4 = base + 24 from by bv_omega, he20] at lor4
  have lor4f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .LW .x10 .x12 8) ** ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LW .x10 .x12 12) ** ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 28) ↦ᵢ .LW .x10 .x12 20) ** ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 44) ↦ᵢ .LW .x10 .x12 28) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
     ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
     ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) **
     (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
    (by pcFree) lor4
  have c14 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c13 lor4f; clear c13 lor4 lor4f
  -- Step 5: shr_lw_or_acc_spec at base+28 -> x5 = s1|..|s5
  have lor5 := shr_lw_or_acc_spec sp (s1 ||| s2 ||| s3 ||| s4) s4 s5 20 (base + 28)
    (by validMem)
  simp only [signExtend12_20] at lor5
  rw [show (base + 28 : Addr) + 4 = base + 32 from by bv_omega, he28] at lor5
  have lor5f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .LW .x10 .x12 8) ** ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LW .x10 .x12 12) ** ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LW .x10 .x12 16) ** ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 44) ↦ᵢ .LW .x10 .x12 28) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
     ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
     ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) **
     (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
    (by pcFree) lor5
  have c15 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c14 lor5f; clear c14 lor5 lor5f
  -- Step 6: shr_lw_or_acc_spec at base+36 -> x5 = s1|..|s6
  have lor6 := shr_lw_or_acc_spec sp (s1 ||| s2 ||| s3 ||| s4 ||| s5) s5 s6 24 (base + 36)
    (by validMem)
  simp only [signExtend12_24] at lor6
  rw [show (base + 36 : Addr) + 4 = base + 40 from by bv_omega, he36] at lor6
  have lor6f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .LW .x10 .x12 8) ** ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LW .x10 .x12 12) ** ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LW .x10 .x12 16) ** ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 28) ↦ᵢ .LW .x10 .x12 20) ** ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 44) ↦ᵢ .LW .x10 .x12 28) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
     ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
     ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) **
     (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 28) ↦ₘ s7))
    (by pcFree) lor6
  have c16 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c15 lor6f; clear c15 lor6 lor6f
  -- Step 7: shr_lw_or_acc_spec at base+44 -> x5 = s1|..|s7
  have lor7 := shr_lw_or_acc_spec sp (s1 ||| s2 ||| s3 ||| s4 ||| s5 ||| s6) s6 s7 28 (base + 44)
    (by validMem)
  simp only [signExtend12_28] at lor7
  rw [show (base + 44 : Addr) + 4 = base + 48 from by bv_omega, he44] at lor7
  have lor7f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .LW .x10 .x12 8) ** ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LW .x10 .x12 12) ** ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LW .x10 .x12 16) ** ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 28) ↦ᵢ .LW .x10 .x12 20) ** ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
     ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
     ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) **
     (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6))
    (by pcFree) lor7
  -- c17: cpsTriple base (base+52), x5 = s1|..|s7, x10 = s7
  have c17 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c16 lor7f; clear c16 lor7 lor7f
  -- Step 8: BNE x5 x0 1120 at base+52
  -- Get BNE spec, drop pure facts
  have bne_raw := bne_spec_gen .x5 .x0 1120
    (s1 ||| s2 ||| s3 ||| s4 ||| s5 ||| s6 ||| s7) (0 : Word) (base + 52)
  rw [hzero, ha52] at bne_raw
  have bne1 : cpsBranch (base + 52)
      (((base + 52) ↦ᵢ .BNE .x5 .x0 1120) ** (.x5 ↦ᵣ (s1 ||| s2 ||| s3 ||| s4 ||| s5 ||| s6 ||| s7)) ** (.x0 ↦ᵣ (0 : Word)))
      zero_path (((base + 52) ↦ᵢ .BNE .x5 .x0 1120) ** (.x5 ↦ᵣ (s1 ||| s2 ||| s3 ||| s4 ||| s5 ||| s6 ||| s7)) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 56) (((base + 52) ↦ᵢ .BNE .x5 .x0 1120) ** (.x5 ↦ᵣ (s1 ||| s2 ||| s3 ||| s4 ||| s5 ||| s6 ||| s7)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence (base + 52) _ _ zero_path _ _ (base + 56) _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
      bne_raw
  -- Frame BNE with remaining code + regs + mem
  have bne1f := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .LW .x10 .x12 8) ** ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LW .x10 .x12 12) ** ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LW .x10 .x12 16) ** ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 28) ↦ᵢ .LW .x10 .x12 20) ** ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 44) ↦ᵢ .LW .x10 .x12 28) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
     ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
     ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) **
     (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ s7) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
    (by pcFree) bne1
  -- Compose c17 with bne1f: cpsBranch base -> {zero_path, base+56}
  have br1 := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c17 bne1f; clear c17 bne_raw bne1 bne1f
  -- On the fall-through (base+56): LW x5 x12 0, SLTIU x10 x5 256, BEQ x10 x0 1108
  -- Step 9: LW x5 x12 0 at base+56 (loads s0 into x5)
  have lw9 := lw_spec_gen .x5 .x12 sp
    (s1 ||| s2 ||| s3 ||| s4 ||| s5 ||| s6 ||| s7) s0 0 (base + 56) (by nofun)
    (by validMem)
  simp only [signExtend12_0] at lw9
  rw [show sp + (0 : Word) = sp from by bv_addr] at lw9
  rw [ha56] at lw9
  have lw9f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .LW .x10 .x12 8) ** ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LW .x10 .x12 12) ** ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LW .x10 .x12 16) ** ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 28) ↦ᵢ .LW .x10 .x12 20) ** ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 44) ↦ᵢ .LW .x10 .x12 28) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
     ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
     ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) **
     (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ s7) **
     ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
    (by pcFree) lw9
  -- Step 10: SLTIU x10 x5 256 at base+60 (rd=x10, rs1=x5, rd≠rs1)
  have sltiu_raw := sltiu_spec_gen .x10 .x5 s7 s0 256 (base + 60) (by nofun) (by nofun)
  rw [ha60] at sltiu_raw
  have sltiuf := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .LW .x10 .x12 8) ** ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LW .x10 .x12 12) ** ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LW .x10 .x12 16) ** ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 28) ↦ᵢ .LW .x10 .x12 20) ** ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 44) ↦ᵢ .LW .x10 .x12 28) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
     ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) **
     (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
    (by pcFree) sltiu_raw
  -- sltiu_val abbreviation
  let sltiu_val := (if BitVec.ult s0 (signExtend12 (256 : BitVec 12)) then (1 : Word) else (0 : Word))
  -- c910: cpsTriple (base+56) (base+64)
  have c910 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) lw9f sltiuf; clear lw9 lw9f sltiu_raw sltiuf
  -- Step 11: BEQ x10 x0 1108 at base+64
  have beq_raw := beq_spec_gen .x10 .x0 1108 sltiu_val (0 : Word) (base + 64)
  rw [hzero2, ha64] at beq_raw
  have beq1 : cpsBranch (base + 64)
      (((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) ** (.x10 ↦ᵣ sltiu_val) ** (.x0 ↦ᵣ (0 : Word)))
      zero_path (((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) ** (.x10 ↦ᵣ sltiu_val) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 68) (((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) ** (.x10 ↦ᵣ sltiu_val) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence (base + 64) _ _ zero_path _ _ (base + 68) _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
      (fun h hp => sepConj_mono_right (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp)
      beq_raw
  -- Frame BEQ with remaining code + regs + mem
  have beq1f := cpsBranch_frame_left _ _ _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .LW .x10 .x12 8) ** ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LW .x10 .x12 12) ** ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LW .x10 .x12 16) ** ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 28) ↦ᵢ .LW .x10 .x12 20) ** ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 44) ↦ᵢ .LW .x10 .x12 28) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
     ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
     (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
    (by pcFree) beq1
  -- Compose c910 (cpsTriple base+56 → base+64) with beq1f (cpsBranch base+64)
  -- to get cpsBranch base+56 → {zero_path, base+68}
  have br2 := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c910 beq1f; clear c910 beq_raw beq1 beq1f
  -- Now combine br1 (cpsBranch base → {zero_path, base+56}) with br2 (cpsBranch base+56 → {zero_path, base+68})
  -- using cpsBranch_seq_cpsBranch_with_perm
  -- br1: cpsBranch base → zero_path (taken) / base+56 (not-taken)
  -- br2: cpsBranch base+56 → zero_path (taken) / base+68 (not-taken)
  -- Result: cpsBranch base → zero_path (merged taken) / base+68 (not-taken)
  -- Both taken paths need to weaken to the same Q_t
  have combined := cpsBranch_seq_cpsBranch_with_perm
    base (base + 56) zero_path (base + 68) _ _ _ _ _ _ _
    br1 (fun _ hp => by xperm_hyp hp) br2
    -- ht1: weaken first taken path to target (concrete x5, x10 -> regOwn)
    (fun h hp => by
      -- Permute to put x5, x10 at front for weakening
      have hp' := (congrFun (show _ =
        ((.x5 ↦ᵣ (s1 ||| s2 ||| s3 ||| s4 ||| s5 ||| s6 ||| s7)) ** (.x10 ↦ᵣ s7) **
         (base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .LW .x10 .x12 8) ** ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 12) ↦ᵢ .LW .x10 .x12 12) ** ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 20) ↦ᵢ .LW .x10 .x12 16) ** ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 28) ↦ᵢ .LW .x10 .x12 20) ** ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 44) ↦ᵢ .LW .x10 .x12 28) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
         ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
         ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
         ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
         (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
         ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
        from by xperm) h).mp hp
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h hp'
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
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
        from by xperm) h).mp w1)
    -- ht2: weaken second taken path to target (concrete x5, x10 -> regOwn)
    (fun h hp => by
      have hp' := (congrFun (show _ =
        ((.x5 ↦ᵣ s0) ** (.x10 ↦ᵣ sltiu_val) **
         (base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .LW .x10 .x12 8) ** ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 12) ↦ᵢ .LW .x10 .x12 12) ** ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 20) ↦ᵢ .LW .x10 .x12 16) ** ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 28) ↦ᵢ .LW .x10 .x12 20) ** ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 44) ↦ᵢ .LW .x10 .x12 28) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
         ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
         ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
         ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
         (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
         ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
        from by xperm) h).mp hp
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h hp'
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
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
        from by xperm) h).mp w1)
  -- Final: weaken the not-taken postcondition (x10 has sltiu_val, need regOwn)
  exact cpsBranch_consequence base _ _ zero_path _ _ (base + 68) _ _
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => hp)
    (fun h hp => by
      have hp' := (congrFun (show _ =
        ((.x10 ↦ᵣ sltiu_val) **
         (base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .LW .x10 .x12 8) ** ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 12) ↦ᵢ .LW .x10 .x12 12) ** ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 20) ↦ᵢ .LW .x10 .x12 16) ** ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 28) ↦ᵢ .LW .x10 .x12 20) ** ((base + 32) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 44) ↦ᵢ .LW .x10 .x12 28) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
         ((base + 52) ↦ᵢ .BNE .x5 .x0 1120) **
         ((base + 56) ↦ᵢ .LW .x5 .x12 0) **
         ((base + 60) ↦ᵢ .SLTIU .x10 .x5 256) **
         ((base + 64) ↦ᵢ .BEQ .x10 .x0 1108) **
         (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) **
         (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
         ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
        from by xperm) h).mp hp
      have w0 := sepConj_mono_left (regIs_to_regOwn .x10 _) h hp'
      exact (congrFun (show _ =
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
         ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
        from by xperm) h).mp w0)
    combined
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
  intro h hp
  -- Step 1: Permute to move items-to-weaken to the front
  have hp' := (congrFun (show _ =
    ((.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
    ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 36) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 44) ↦ₘ (0 : Word)) **
    ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 52) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) ** ((sp + 60) ↦ₘ (0 : Word)) **
    (.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
    (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
    ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
    from by xperm) h).mp hp
  -- Step 2: Weaken positions 0-10 (left to right)
  have w0 := sepConj_mono_left (regIs_to_regOwn .x6 r6) h hp'
  have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x7 r7)) h w0
  have w2 := sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (regIs_to_regOwn .x11 r11))) h w1
  have w3 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 32) 0)))) h w2
  have w4 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 36) 0))))) h w3
  have w5 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 40) 0)))))) h w4
  have w6 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 44) 0))))))) h w5
  have w7 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 48) 0)))))))) h w6
  have w8 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 52) 0))))))))) h w7
  have w9 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 56) 0)))))))))) h w8
  have w10 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 60) 0))))))))))) h w9
  -- Step 3: Permute to target order
  exact (congrFun (show _ = _ by xperm) h).mp w10

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
     (memOwn (sp + 48)) ** (memOwn (sp + 52)) ** (memOwn (sp + 56)) ** (memOwn (sp + 60))) h := by
  intro h hp
  -- Step 1: Permute to move items-to-weaken to the front
  have hp' := (congrFun (show _ =
    ((.x5 ↦ᵣ r5) ** (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x10 ↦ᵣ r10) ** (.x11 ↦ᵣ r11) **
    ((sp + 32) ↦ₘ m0) ** ((sp + 36) ↦ₘ m1) ** ((sp + 40) ↦ₘ m2) ** ((sp + 44) ↦ₘ m3) **
    ((sp + 48) ↦ₘ m4) ** ((sp + 52) ↦ₘ m5) ** ((sp + 56) ↦ₘ m6) ** ((sp + 60) ↦ₘ m7) **
    (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
    (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
    ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
    from by xperm) h).mp hp
  -- Step 2: Weaken positions 0-12 (5 regs + 8 mems)
  have w0 := sepConj_mono_left (regIs_to_regOwn .x5 r5) h hp'
  have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 r6)) h w0
  have w2 := sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (regIs_to_regOwn .x7 r7))) h w1
  have w3 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (regIs_to_regOwn .x10 r10)))) h w2
  have w4 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (regIs_to_regOwn .x11 r11))))) h w3
  have w5 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 32) m0)))))) h w4
  have w6 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 36) m1))))))) h w5
  have w7 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 40) m2)))))))) h w6
  have w8 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 44) m3))))))))) h w7
  have w9 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 48) m4)))))))))) h w8
  have w10 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 52) m5))))))))))) h w9
  have w11 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 56) m6)))))))))))) h w10
  have w12 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 60) m7))))))))))))) h w11
  -- Step 3: Permute to target order
  exact (congrFun (show _ = _ from by xperm) h).mp w12

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
  unfold evm_shr seq
  simp only [progAt_append_program,
    shr_phase_a_len, shr_phase_b_len, shr_phase_c_len,
    shr_body_7_len, shr_body_6_len, shr_body_5_len, shr_body_4_len,
    shr_body_3_len, shr_body_2_len, shr_body_1_len, shr_body_0_len,
    bv_ofNat_pa, bv_ofNat_pb, bv_ofNat_pc, bv_ofNat_b7,
    bv_ofNat_b5, bv_ofNat_b4, bv_ofNat_b3, bv_ofNat_b2, bv_ofNat_b1, bv_ofNat_b0,
    addr_norm_96, addr_norm_148, addr_norm_192, addr_norm_260, addr_norm_352,
    addr_norm_468, addr_norm_608, addr_norm_772, addr_norm_960, addr_norm_1172]

-- evm_shr_spec is proved in EvmAsm.Evm32.ShiftComposition

end EvmAsm
