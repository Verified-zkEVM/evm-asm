/-
  EvmAsm.Evm.ShiftSpec

  CPS specifications for the 256-bit EVM SHR (logical shift right) program.
  Modular decomposition:
  - Per-limb helpers: shr_merge_limb_spec (7 instrs), shr_last_limb_spec (3 instrs)
  - Zero-fill helper: shr_sw_zero_spec (1 instr)
  - Zero path: shr_zero_path_spec (9 instrs, shift >= 256)
  - Shift bodies: shr_body_L_spec for L = 0..7
  - Full composition: evm_shr_spec
-/

import EvmAsm.Evm.Shift
import EvmAsm.SyscallSpecs
import EvmAsm.Tactics.XSimp

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
    cpsTriple base (base + 28)
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
  -- Address normalization
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have ha2 : (base + 8 : Addr) + 4 = base + 12 := by bv_omega
  have ha3 : (base + 12 : Addr) + 4 = base + 16 := by bv_omega
  have ha4 : (base + 16 : Addr) + 4 = base + 20 := by bv_omega
  have ha5 : (base + 20 : Addr) + 4 = base + 24 := by bv_omega
  have ha6 : (base + 24 : Addr) + 4 = base + 28 := by bv_omega
  -- Step 1: LW x5 x12 src_off at base
  have s1 := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) ** ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) **
     ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) ** ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) ** ((base + 24) ↦ᵢ .SW .x12 .x5 dst_off) **
     (.x6 ↦ᵣ bit_shift) ** (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 next_off) ↦ₘ next) ** ((sp + signExtend12 dst_off) ↦ₘ dst_old))
    (by pcFree) (lw_spec_gen .x5 .x12 sp v5 src src_off base (by nofun) hvalid_src)
  -- Step 2: SRL x5 x5 x6 at base+4
  have s2_raw := srl_spec_gen_rd_eq_rs1 .x5 .x6 src bit_shift (base + 4) (by nofun) (by nofun)
  rw [ha1] at s2_raw
  have s2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 src_off) ** ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) **
     ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) ** ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) ** ((base + 24) ↦ᵢ .SW .x12 .x5 dst_off) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 src_off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next) ** ((sp + signExtend12 dst_off) ↦ₘ dst_old))
    (by pcFree) s2_raw
  have s12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1 s2; clear s1 s2 s2_raw
  -- Step 3: LW x10 x12 next_off at base+8
  have s3_raw := lw_spec_gen .x10 .x12 sp v10 next next_off (base + 8) (by nofun) hvalid_next
  rw [ha2] at s3_raw
  have s3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 src_off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) ** ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) ** ((base + 24) ↦ᵢ .SW .x12 .x5 dst_off) **
     (.x5 ↦ᵣ (src >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 src_off) ↦ₘ src) ** ((sp + signExtend12 dst_off) ↦ₘ dst_old))
    (by pcFree) s3_raw
  have s123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s12 s3; clear s12 s3 s3_raw
  -- Step 4: SLL x10 x10 x7 at base+12
  have s4_raw := sll_spec_gen_rd_eq_rs1 .x10 .x7 next anti_shift (base + 12) (by nofun) (by nofun)
  rw [ha3] at s4_raw
  have s4 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 src_off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) ** ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) ** ((base + 24) ↦ᵢ .SW .x12 .x5 dst_off) **
     (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (src >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x11 ↦ᵣ mask) ** ((sp + signExtend12 src_off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next) ** ((sp + signExtend12 dst_off) ↦ₘ dst_old))
    (by pcFree) s4_raw
  have s1234 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s123 s4; clear s123 s4 s4_raw
  -- Step 5: AND x10 x10 x11 at base+16
  have s5_raw := and_spec_gen_rd_eq_rs1 .x10 .x11 (next <<< (anti_shift.toNat % 32)) mask (base + 16) (by nofun) (by nofun)
  rw [ha4] at s5_raw
  have s5 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 src_off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) ** ((base + 24) ↦ᵢ .SW .x12 .x5 dst_off) **
     (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (src >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** ((sp + signExtend12 src_off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next) ** ((sp + signExtend12 dst_off) ↦ₘ dst_old))
    (by pcFree) s5_raw
  have s12345 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1234 s5; clear s1234 s5 s5_raw
  -- Step 6: OR x5 x5 x10 at base+20
  have s6_raw := or_spec_gen_rd_eq_rs1 .x5 .x10
    (src >>> (bit_shift.toNat % 32)) ((next <<< (anti_shift.toNat % 32)) &&& mask)
    (base + 20) (by nofun) (by nofun)
  rw [ha5] at s6_raw
  have s6 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 src_off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 24) ↦ᵢ .SW .x12 .x5 dst_off) **
     (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ bit_shift) ** (.x7 ↦ᵣ anti_shift) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 src_off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next) ** ((sp + signExtend12 dst_off) ↦ₘ dst_old))
    (by pcFree) s6_raw
  have s123456 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s12345 s6; clear s12345 s6 s6_raw
  -- Step 7: SW x12 x5 dst_off at base+24
  have s7_raw := sw_spec_gen .x12 .x5 sp
    ((src >>> (bit_shift.toNat % 32)) ||| ((next <<< (anti_shift.toNat % 32)) &&& mask))
    dst_old dst_off (base + 24) hvalid_dst
  rw [ha6] at s7_raw
  have s7 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 src_off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     (.x6 ↦ᵣ bit_shift) ** (.x7 ↦ᵣ anti_shift) **
     (.x10 ↦ᵣ ((next <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 src_off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next))
    (by pcFree) s7_raw
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) s123456 s7)

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
    cpsTriple base (base + 12)
      ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .SW .x12 .x5 dst_off) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (mem_src ↦ₘ src) ** (mem_dst ↦ₘ dst_old))
      ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .SW .x12 .x5 dst_off) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (mem_src ↦ₘ src) ** (mem_dst ↦ₘ result)) := by
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have ha2 : (base + 8 : Addr) + 4 = base + 12 := by bv_omega
  -- Step 1: LW x5 x12 28 at base
  have s1 := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) ** ((base + 8) ↦ᵢ .SW .x12 .x5 dst_off) **
     (.x6 ↦ᵣ bit_shift) ** ((sp + signExtend12 dst_off) ↦ₘ dst_old))
    (by pcFree) (lw_spec_gen .x5 .x12 sp v5 src 28 base (by nofun) hvalid_src)
  -- Step 2: SRL x5 x5 x6 at base+4
  have s2_raw := srl_spec_gen_rd_eq_rs1 .x5 .x6 src bit_shift (base + 4) (by nofun) (by nofun)
  rw [ha1] at s2_raw
  have s2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 8) ↦ᵢ .SW .x12 .x5 dst_off) **
     (.x12 ↦ᵣ sp) ** ((sp + signExtend12 (28 : BitVec 12)) ↦ₘ src) ** ((sp + signExtend12 dst_off) ↦ₘ dst_old))
    (by pcFree) s2_raw
  have s12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1 s2
  clear s1 s2 s2_raw
  -- Step 3: SW x12 x5 dst_off at base+8
  have s3_raw := sw_spec_gen .x12 .x5 sp (src >>> (bit_shift.toNat % 32)) dst_old dst_off (base + 8) hvalid_dst
  rw [ha2] at s3_raw
  have s3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     (.x6 ↦ᵣ bit_shift) ** ((sp + signExtend12 (28 : BitVec 12)) ↦ₘ src))
    (by pcFree) s3_raw
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) s12 s3)

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
    cpsTriple base (base + 28)
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
  -- Address normalization
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have ha2 : (base + 8 : Addr) + 4 = base + 12 := by bv_omega
  have ha3 : (base + 12 : Addr) + 4 = base + 16 := by bv_omega
  have ha4 : (base + 16 : Addr) + 4 = base + 20 := by bv_omega
  have ha5 : (base + 20 : Addr) + 4 = base + 24 := by bv_omega
  have ha6 : (base + 24 : Addr) + 4 = base + 28 := by bv_omega
  -- Step 1: LW x5 x12 off at base
  have s1 := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) ** ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) **
     ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) ** ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) ** ((base + 24) ↦ᵢ .SW .x12 .x5 off) **
     (.x6 ↦ᵣ bit_shift) ** (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 next_off) ↦ₘ next))
    (by pcFree) (lw_spec_gen .x5 .x12 sp v5 src off base (by nofun) hvalid_loc)
  -- Step 2: SRL x5 x5 x6 at base+4
  have s2_raw := srl_spec_gen_rd_eq_rs1 .x5 .x6 src bit_shift (base + 4) (by nofun) (by nofun)
  rw [ha1] at s2_raw
  have s2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 off) ** ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) **
     ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) ** ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) ** ((base + 24) ↦ᵢ .SW .x12 .x5 off) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next))
    (by pcFree) s2_raw
  have s12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1 s2; clear s1 s2 s2_raw
  -- Step 3: LW x10 x12 next_off at base+8
  have s3_raw := lw_spec_gen .x10 .x12 sp v10 next next_off (base + 8) (by nofun) hvalid_next
  rw [ha2] at s3_raw
  have s3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) ** ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) ** ((base + 24) ↦ᵢ .SW .x12 .x5 off) **
     (.x5 ↦ᵣ (src >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 off) ↦ₘ src))
    (by pcFree) s3_raw
  have s123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s12 s3; clear s12 s3 s3_raw
  -- Step 4: SLL x10 x10 x7 at base+12
  have s4_raw := sll_spec_gen_rd_eq_rs1 .x10 .x7 next anti_shift (base + 12) (by nofun) (by nofun)
  rw [ha3] at s4_raw
  have s4 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) ** ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) ** ((base + 24) ↦ᵢ .SW .x12 .x5 off) **
     (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (src >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x11 ↦ᵣ mask) ** ((sp + signExtend12 off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next))
    (by pcFree) s4_raw
  have s1234 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s123 s4; clear s123 s4 s4_raw
  -- Step 5: AND x10 x10 x11 at base+16
  have s5_raw := and_spec_gen_rd_eq_rs1 .x10 .x11 (next <<< (anti_shift.toNat % 32)) mask (base + 16) (by nofun) (by nofun)
  rw [ha4] at s5_raw
  have s5 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) ** ((base + 24) ↦ᵢ .SW .x12 .x5 off) **
     (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (src >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** ((sp + signExtend12 off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next))
    (by pcFree) s5_raw
  have s12345 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1234 s5; clear s1234 s5 s5_raw
  -- Step 6: OR x5 x5 x10 at base+20
  have s6_raw := or_spec_gen_rd_eq_rs1 .x5 .x10
    (src >>> (bit_shift.toNat % 32)) ((next <<< (anti_shift.toNat % 32)) &&& mask)
    (base + 20) (by nofun) (by nofun)
  rw [ha5] at s6_raw
  have s6 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 24) ↦ᵢ .SW .x12 .x5 off) **
     (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ bit_shift) ** (.x7 ↦ᵣ anti_shift) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next))
    (by pcFree) s6_raw
  have s123456 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s12345 s6; clear s12345 s6 s6_raw
  -- Step 7: SW x12 x5 off at base+24 (overwrites mem_loc)
  have s7_raw := sw_spec_gen .x12 .x5 sp
    ((src >>> (bit_shift.toNat % 32)) ||| ((next <<< (anti_shift.toNat % 32)) &&& mask))
    src off (base + 24) hvalid_loc
  rw [ha6] at s7_raw
  have s7 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 off) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 next_off) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     (.x6 ↦ᵣ bit_shift) ** (.x7 ↦ᵣ anti_shift) **
     (.x10 ↦ᵣ ((next <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 next_off) ↦ₘ next))
    (by pcFree) s7_raw
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) s123456 s7)

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
    cpsTriple base (base + 12)
      ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .SW .x12 .x5 28) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ src))
      ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .SW .x12 .x5 28) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ result)) := by
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have ha2 : (base + 8 : Addr) + 4 = base + 12 := by bv_omega
  -- Step 1: LW x5 x12 28 at base
  have s1 := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) ** ((base + 8) ↦ᵢ .SW .x12 .x5 28) ** (.x6 ↦ᵣ bit_shift))
    (by pcFree) (lw_spec_gen .x5 .x12 sp v5 src 28 base (by nofun) hvalid)
  -- Step 2: SRL x5 x5 x6 at base+4 (rd=rs1=x5, rs2=x6)
  have s2_raw := srl_spec_gen_rd_eq_rs1 .x5 .x6 src bit_shift (base + 4) (by nofun) (by nofun)
  rw [ha1] at s2_raw
  have s2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 8) ↦ᵢ .SW .x12 .x5 28) **
     (.x12 ↦ᵣ sp) ** ((sp + signExtend12 (28 : BitVec 12)) ↦ₘ src))
    (by pcFree) s2_raw
  have s12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1 s2
  clear s1 s2 s2_raw
  -- Step 3: SW x12 x5 28 at base+8
  have s3_raw := sw_spec_gen .x12 .x5 sp (src >>> (bit_shift.toNat % 32)) src 28 (base + 8) hvalid
  rw [ha2] at s3_raw
  have s3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) ** (.x6 ↦ᵣ bit_shift))
    (by pcFree) s3_raw
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) s12 s3)

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
    cpsTriple base (base + 36)
      ((base ↦ᵢ .ADDI .x12 .x12 32) ** ((base + 4) ↦ᵢ .SW .x12 .x0 0) **
       ((base + 8) ↦ᵢ .SW .x12 .x0 4) ** ((base + 12) ↦ᵢ .SW .x12 .x0 8) **
       ((base + 16) ↦ᵢ .SW .x12 .x0 12) ** ((base + 20) ↦ᵢ .SW .x12 .x0 16) **
       ((base + 24) ↦ᵢ .SW .x12 .x0 20) ** ((base + 28) ↦ᵢ .SW .x12 .x0 24) **
       ((base + 32) ↦ᵢ .SW .x12 .x0 28) **
       (.x12 ↦ᵣ sp) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
      ((base ↦ᵢ .ADDI .x12 .x12 32) ** ((base + 4) ↦ᵢ .SW .x12 .x0 0) **
       ((base + 8) ↦ᵢ .SW .x12 .x0 4) ** ((base + 12) ↦ᵢ .SW .x12 .x0 8) **
       ((base + 16) ↦ᵢ .SW .x12 .x0 12) ** ((base + 20) ↦ᵢ .SW .x12 .x0 16) **
       ((base + 24) ↦ᵢ .SW .x12 .x0 20) ** ((base + 28) ↦ᵢ .SW .x12 .x0 24) **
       ((base + 32) ↦ᵢ .SW .x12 .x0 28) **
       (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 12) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 20) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) ** ((nsp + 28) ↦ₘ 0)) := by
  -- Define nsp locally to match the let in the goal
  have nsp_def : sp + signExtend12 (32 : BitVec 12) = sp + 32 := by simp only [signExtend12_32]
  let nsp : Word := sp + 32
  -- Address arithmetic
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have ha2 : (base + 8 : Addr) + 4 = base + 12 := by bv_omega
  have ha3 : (base + 12 : Addr) + 4 = base + 16 := by bv_omega
  have ha4 : (base + 16 : Addr) + 4 = base + 20 := by bv_omega
  have ha5 : (base + 20 : Addr) + 4 = base + 24 := by bv_omega
  have ha6 : (base + 24 : Addr) + 4 = base + 28 := by bv_omega
  have ha7 : (base + 28 : Addr) + 4 = base + 32 := by bv_omega
  have ha8 : (base + 32 : Addr) + 4 = base + 36 := by bv_omega
  -- Memory address normalization
  have hm0 : (sp + 32) + signExtend12 (0 : BitVec 12) = (sp + 32) := by
    simp only [signExtend12_0]; bv_omega
  have hm4 : (sp + 32) + signExtend12 (4 : BitVec 12) = (sp + 32) + 4 := by simp only [signExtend12_4]
  have hm8 : (sp + 32) + signExtend12 (8 : BitVec 12) = (sp + 32) + 8 := by simp only [signExtend12_8]
  have hm12 : (sp + 32) + signExtend12 (12 : BitVec 12) = (sp + 32) + 12 := by simp only [signExtend12_12]
  have hm16 : (sp + 32) + signExtend12 (16 : BitVec 12) = (sp + 32) + 16 := by simp only [signExtend12_16]
  have hm20 : (sp + 32) + signExtend12 (20 : BitVec 12) = (sp + 32) + 20 := by simp only [signExtend12_20]
  have hm24 : (sp + 32) + signExtend12 (24 : BitVec 12) = (sp + 32) + 24 := by simp only [signExtend12_24]
  have hm28 : (sp + 32) + signExtend12 (28 : BitVec 12) = (sp + 32) + 28 := by simp only [signExtend12_28]
  -- Memory validity from ValidMemRange (sp + 32) 8
  have hv0 : isValidMemAccess (sp + 32) = true := by
    have := hvalid.get (i := 0) (by omega); simpa using this
  have hv4 : isValidMemAccess ((sp + 32) + 4) = true := by
    have := hvalid.get (i := 1) (by omega); simpa using this
  have hv8 : isValidMemAccess ((sp + 32) + 8) = true := by
    have := hvalid.get (i := 2) (by omega); simpa using this
  have hv12 : isValidMemAccess ((sp + 32) + 12) = true := by
    have := hvalid.get (i := 3) (by omega); simpa using this
  have hv16 : isValidMemAccess ((sp + 32) + 16) = true := by
    have := hvalid.get (i := 4) (by omega); simpa using this
  have hv20 : isValidMemAccess ((sp + 32) + 20) = true := by
    have := hvalid.get (i := 5) (by omega); simpa using this
  have hv24 : isValidMemAccess ((sp + 32) + 24) = true := by
    have := hvalid.get (i := 6) (by omega); simpa using this
  have hv28 : isValidMemAccess ((sp + 32) + 28) = true := by
    have := hvalid.get (i := 7) (by omega); simpa using this
  -- ADDI result: sp + signExtend12 32 = sp + 32
  have h_addi : sp + signExtend12 (32 : BitVec 12) = sp + 32 := by
    simp only [signExtend12_32]
  -- Step 1: ADDI x12 x12 32 at base
  have s1_raw := addi_spec_gen_same .x12 sp 32 base (by nofun)
  rw [h_addi] at s1_raw
  have s1 := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .SW .x12 .x0 0) ** ((base + 8) ↦ᵢ .SW .x12 .x0 4) **
     ((base + 12) ↦ᵢ .SW .x12 .x0 8) ** ((base + 16) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 20) ↦ᵢ .SW .x12 .x0 16) ** ((base + 24) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 24) ** ((base + 32) ↦ᵢ .SW .x12 .x0 28) **
     (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
     ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
    (by pcFree) s1_raw
  -- Step 2: SW x12 x0 0 at base+4 (store 0 at nsp)
  have s2_raw := sw_x0_spec_gen .x12 nsp d0 0 (base + 4) (by rw [hm0]; exact hv0)
  rw [ha1, hm0] at s2_raw
  have s2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 32) ** ((base + 8) ↦ᵢ .SW .x12 .x0 4) **
     ((base + 12) ↦ᵢ .SW .x12 .x0 8) ** ((base + 16) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 20) ↦ᵢ .SW .x12 .x0 16) ** ((base + 24) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 24) ** ((base + 32) ↦ᵢ .SW .x12 .x0 28) **
     ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
     ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
    (by pcFree) s2_raw
  have s12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1 s2; clear s1 s2 s1_raw s2_raw
  -- Step 3: SW x12 x0 4 at base+8
  have s3_raw := sw_x0_spec_gen .x12 nsp d1 4 (base + 8) (by rw [hm4]; exact hv4)
  rw [ha2, hm4] at s3_raw
  have s3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 32) ** ((base + 4) ↦ᵢ .SW .x12 .x0 0) **
     ((base + 12) ↦ᵢ .SW .x12 .x0 8) ** ((base + 16) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 20) ↦ᵢ .SW .x12 .x0 16) ** ((base + 24) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 24) ** ((base + 32) ↦ᵢ .SW .x12 .x0 28) **
     (nsp ↦ₘ 0) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
     ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
    (by pcFree) s3_raw
  have s123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s12 s3; clear s12 s3 s3_raw
  -- Step 4: SW x12 x0 8 at base+12
  have s4_raw := sw_x0_spec_gen .x12 nsp d2 8 (base + 12) (by rw [hm8]; exact hv8)
  rw [ha3, hm8] at s4_raw
  have s4 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 32) ** ((base + 4) ↦ᵢ .SW .x12 .x0 0) **
     ((base + 8) ↦ᵢ .SW .x12 .x0 4) ** ((base + 16) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 20) ↦ᵢ .SW .x12 .x0 16) ** ((base + 24) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 24) ** ((base + 32) ↦ᵢ .SW .x12 .x0 28) **
     (nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 12) ↦ₘ d3) **
     ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
    (by pcFree) s4_raw
  have s1234 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s123 s4; clear s123 s4 s4_raw
  -- Step 5: SW x12 x0 12 at base+16
  have s5_raw := sw_x0_spec_gen .x12 nsp d3 12 (base + 16) (by rw [hm12]; exact hv12)
  rw [ha4, hm12] at s5_raw
  have s5 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 32) ** ((base + 4) ↦ᵢ .SW .x12 .x0 0) **
     ((base + 8) ↦ᵢ .SW .x12 .x0 4) ** ((base + 12) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 20) ↦ᵢ .SW .x12 .x0 16) ** ((base + 24) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 24) ** ((base + 32) ↦ᵢ .SW .x12 .x0 28) **
     (nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) **
     ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
    (by pcFree) s5_raw
  have s12345 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1234 s5; clear s1234 s5 s5_raw
  -- Step 6: SW x12 x0 16 at base+20
  have s6_raw := sw_x0_spec_gen .x12 nsp d4 16 (base + 20) (by rw [hm16]; exact hv16)
  rw [ha5, hm16] at s6_raw
  have s6 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 32) ** ((base + 4) ↦ᵢ .SW .x12 .x0 0) **
     ((base + 8) ↦ᵢ .SW .x12 .x0 4) ** ((base + 12) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 16) ↦ᵢ .SW .x12 .x0 12) ** ((base + 24) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 24) ** ((base + 32) ↦ᵢ .SW .x12 .x0 28) **
     (nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 12) ↦ₘ 0) **
     ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
    (by pcFree) s6_raw
  have s123456 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s12345 s6; clear s12345 s6 s6_raw
  -- Step 7: SW x12 x0 20 at base+24
  have s7_raw := sw_x0_spec_gen .x12 nsp d5 20 (base + 24) (by rw [hm20]; exact hv20)
  rw [ha6, hm20] at s7_raw
  have s7 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 32) ** ((base + 4) ↦ᵢ .SW .x12 .x0 0) **
     ((base + 8) ↦ᵢ .SW .x12 .x0 4) ** ((base + 12) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 16) ↦ᵢ .SW .x12 .x0 12) ** ((base + 20) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 24) ** ((base + 32) ↦ᵢ .SW .x12 .x0 28) **
     (nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 12) ↦ₘ 0) **
     ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
    (by pcFree) s7_raw
  have s1234567 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s123456 s7; clear s123456 s7 s7_raw
  -- Step 8: SW x12 x0 24 at base+28
  have s8_raw := sw_x0_spec_gen .x12 nsp d6 24 (base + 28) (by rw [hm24]; exact hv24)
  rw [ha7, hm24] at s8_raw
  have s8 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 32) ** ((base + 4) ↦ᵢ .SW .x12 .x0 0) **
     ((base + 8) ↦ᵢ .SW .x12 .x0 4) ** ((base + 12) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 16) ↦ᵢ .SW .x12 .x0 12) ** ((base + 20) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 24) ↦ᵢ .SW .x12 .x0 20) ** ((base + 32) ↦ᵢ .SW .x12 .x0 28) **
     (nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 12) ↦ₘ 0) **
     ((nsp + 16) ↦ₘ 0) ** ((nsp + 20) ↦ₘ 0) ** ((nsp + 28) ↦ₘ d7))
    (by pcFree) s8_raw
  have s12345678 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1234567 s8; clear s1234567 s8 s8_raw
  -- Step 9: SW x12 x0 28 at base+32
  have s9_raw := sw_x0_spec_gen .x12 nsp d7 28 (base + 32) (by rw [hm28]; exact hv28)
  rw [ha8, hm28] at s9_raw
  have s9 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 32) ** ((base + 4) ↦ᵢ .SW .x12 .x0 0) **
     ((base + 8) ↦ᵢ .SW .x12 .x0 4) ** ((base + 12) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 16) ↦ᵢ .SW .x12 .x0 12) ** ((base + 20) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 24) ↦ᵢ .SW .x12 .x0 20) ** ((base + 28) ↦ᵢ .SW .x12 .x0 24) **
     (nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 12) ↦ₘ 0) **
     ((nsp + 16) ↦ₘ 0) ** ((nsp + 20) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0))
    (by pcFree) s9_raw
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) s12345678 s9)

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
    cpsTriple base (base + 28)
      ((base ↦ᵢ .ANDI .x6 .x5 31) ** ((base + 4) ↦ᵢ .SRLI .x5 .x5 5) **
       ((base + 8) ↦ᵢ .SLTU .x11 .x0 .x6) ** ((base + 12) ↦ᵢ .SUB .x11 .x0 .x11) **
       ((base + 16) ↦ᵢ .LI .x7 32) ** ((base + 20) ↦ᵢ .SUB .x7 .x7 .x6) **
       ((base + 24) ↦ᵢ .ADDI .x12 .x12 32) **
       (.x5 ↦ᵣ shift0) ** (.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ r11) ** (.x7 ↦ᵣ r7) ** (.x12 ↦ᵣ sp))
      ((base ↦ᵢ .ANDI .x6 .x5 31) ** ((base + 4) ↦ᵢ .SRLI .x5 .x5 5) **
       ((base + 8) ↦ᵢ .SLTU .x11 .x0 .x6) ** ((base + 12) ↦ᵢ .SUB .x11 .x0 .x11) **
       ((base + 16) ↦ᵢ .LI .x7 32) ** ((base + 20) ↦ᵢ .SUB .x7 .x7 .x6) **
       ((base + 24) ↦ᵢ .ADDI .x12 .x12 32) **
       (.x5 ↦ᵣ limb_shift) ** (.x6 ↦ᵣ bit_shift) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ mask) ** (.x7 ↦ᵣ anti_shift) ** (.x12 ↦ᵣ (sp + signExtend12 32))) := by
  -- Address normalization
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have ha2 : (base + 8 : Addr) + 4 = base + 12 := by bv_omega
  have ha3 : (base + 12 : Addr) + 4 = base + 16 := by bv_omega
  have ha4 : (base + 16 : Addr) + 4 = base + 20 := by bv_omega
  have ha5 : (base + 20 : Addr) + 4 = base + 24 := by bv_omega
  have ha6 : (base + 24 : Addr) + 4 = base + 28 := by bv_omega
  -- Step 1: ANDI x6, x5, 31 at base (rd=x6, rs1=x5, rd≠rs1)
  have s1 := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .SRLI .x5 .x5 5) ** ((base + 8) ↦ᵢ .SLTU .x11 .x0 .x6) **
     ((base + 12) ↦ᵢ .SUB .x11 .x0 .x11) ** ((base + 16) ↦ᵢ .LI .x7 32) **
     ((base + 20) ↦ᵢ .SUB .x7 .x7 .x6) ** ((base + 24) ↦ᵢ .ADDI .x12 .x12 32) **
     (.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ r11) ** (.x7 ↦ᵣ r7) ** (.x12 ↦ᵣ sp))
    (by pcFree) (andi_spec_gen .x6 .x5 r6 shift0 31 base (by nofun) (by nofun))
  -- Step 2: SRLI x5, x5, 5 at base+4 (rd=rs1=x5)
  have s2_raw := srli_spec_gen_same .x5 shift0 5 (base + 4) (by nofun)
  rw [ha1] at s2_raw
  have s2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ANDI .x6 .x5 31) ** ((base + 8) ↦ᵢ .SLTU .x11 .x0 .x6) **
     ((base + 12) ↦ᵢ .SUB .x11 .x0 .x11) ** ((base + 16) ↦ᵢ .LI .x7 32) **
     ((base + 20) ↦ᵢ .SUB .x7 .x7 .x6) ** ((base + 24) ↦ᵢ .ADDI .x12 .x12 32) **
     (.x6 ↦ᵣ (shift0 &&& signExtend12 31)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x11 ↦ᵣ r11) ** (.x7 ↦ᵣ r7) ** (.x12 ↦ᵣ sp))
    (by pcFree) s2_raw
  have s12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1 s2; clear s1 s2 s2_raw
  -- Step 3: SLTU x11, x0, x6 at base+8 (rd=x11, rs1=x0, rs2=x6, 3-reg spec)
  have s3_raw := sltu_spec_gen .x11 .x0 .x6 r11 0 (shift0 &&& signExtend12 31) (base + 8) (by nofun)
  rw [ha2] at s3_raw
  have s3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ANDI .x6 .x5 31) ** ((base + 4) ↦ᵢ .SRLI .x5 .x5 5) **
     ((base + 12) ↦ᵢ .SUB .x11 .x0 .x11) ** ((base + 16) ↦ᵢ .LI .x7 32) **
     ((base + 20) ↦ᵢ .SUB .x7 .x7 .x6) ** ((base + 24) ↦ᵢ .ADDI .x12 .x12 32) **
     (.x5 ↦ᵣ (shift0 >>> (5 : BitVec 5).toNat)) ** (.x7 ↦ᵣ r7) ** (.x12 ↦ᵣ sp))
    (by pcFree) s3_raw
  have s123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s12 s3; clear s12 s3 s3_raw
  -- Step 4: SUB x11, x0, x11 at base+12 (rd=x11, rs1=x0, rs2=x11 -> rd_eq_rs2)
  have s4_raw := sub_spec_gen_rd_eq_rs2 .x11 .x0
    (0 : Word) (if BitVec.ult (0 : Word) (shift0 &&& signExtend12 31) then (1 : Word) else 0)
    (base + 12) (by nofun) (by nofun)
  rw [ha3] at s4_raw
  have s4 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ANDI .x6 .x5 31) ** ((base + 4) ↦ᵢ .SRLI .x5 .x5 5) **
     ((base + 8) ↦ᵢ .SLTU .x11 .x0 .x6) ** ((base + 16) ↦ᵢ .LI .x7 32) **
     ((base + 20) ↦ᵢ .SUB .x7 .x7 .x6) ** ((base + 24) ↦ᵢ .ADDI .x12 .x12 32) **
     (.x5 ↦ᵣ (shift0 >>> (5 : BitVec 5).toNat)) ** (.x6 ↦ᵣ (shift0 &&& signExtend12 31)) **
     (.x7 ↦ᵣ r7) ** (.x12 ↦ᵣ sp))
    (by pcFree) s4_raw
  have s1234 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s123 s4; clear s123 s4 s4_raw
  -- Step 5: LI x7, 32 at base+16 (rd=x7)
  have s5_raw := li_spec_gen .x7 r7 32 (base + 16) (by nofun)
  rw [ha4] at s5_raw
  have s5 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ANDI .x6 .x5 31) ** ((base + 4) ↦ᵢ .SRLI .x5 .x5 5) **
     ((base + 8) ↦ᵢ .SLTU .x11 .x0 .x6) ** ((base + 12) ↦ᵢ .SUB .x11 .x0 .x11) **
     ((base + 20) ↦ᵢ .SUB .x7 .x7 .x6) ** ((base + 24) ↦ᵢ .ADDI .x12 .x12 32) **
     (.x5 ↦ᵣ (shift0 >>> (5 : BitVec 5).toNat)) ** (.x6 ↦ᵣ (shift0 &&& signExtend12 31)) **
     (.x0 ↦ᵣ (0 : Word)) **
     (.x11 ↦ᵣ ((0 : Word) - (if BitVec.ult (0 : Word) (shift0 &&& signExtend12 31) then (1 : Word) else 0))) **
     (.x12 ↦ᵣ sp))
    (by pcFree) s5_raw
  have s12345 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1234 s5; clear s1234 s5 s5_raw
  -- Step 6: SUB x7, x7, x6 at base+20 (rd=x7, rs1=x7, rs2=x6 -> rd_eq_rs1)
  have s6_raw := sub_spec_gen_rd_eq_rs1 .x7 .x6 32 (shift0 &&& signExtend12 31) (base + 20) (by nofun) (by nofun)
  rw [ha5] at s6_raw
  have s6 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ANDI .x6 .x5 31) ** ((base + 4) ↦ᵢ .SRLI .x5 .x5 5) **
     ((base + 8) ↦ᵢ .SLTU .x11 .x0 .x6) ** ((base + 12) ↦ᵢ .SUB .x11 .x0 .x11) **
     ((base + 16) ↦ᵢ .LI .x7 32) ** ((base + 24) ↦ᵢ .ADDI .x12 .x12 32) **
     (.x5 ↦ᵣ (shift0 >>> (5 : BitVec 5).toNat)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x11 ↦ᵣ ((0 : Word) - (if BitVec.ult (0 : Word) (shift0 &&& signExtend12 31) then (1 : Word) else 0))) **
     (.x12 ↦ᵣ sp))
    (by pcFree) s6_raw
  have s123456 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s12345 s6; clear s12345 s6 s6_raw
  -- Step 7: ADDI x12, x12, 32 at base+24 (rd=rs1=x12)
  have s7_raw := addi_spec_gen_same .x12 sp 32 (base + 24) (by nofun)
  rw [ha6] at s7_raw
  have s7 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ANDI .x6 .x5 31) ** ((base + 4) ↦ᵢ .SRLI .x5 .x5 5) **
     ((base + 8) ↦ᵢ .SLTU .x11 .x0 .x6) ** ((base + 12) ↦ᵢ .SUB .x11 .x0 .x11) **
     ((base + 16) ↦ᵢ .LI .x7 32) ** ((base + 20) ↦ᵢ .SUB .x7 .x7 .x6) **
     (.x5 ↦ᵣ (shift0 >>> (5 : BitVec 5).toNat)) ** (.x6 ↦ᵣ (shift0 &&& signExtend12 31)) **
     (.x0 ↦ᵣ (0 : Word)) **
     (.x11 ↦ᵣ ((0 : Word) - (if BitVec.ult (0 : Word) (shift0 &&& signExtend12 31) then (1 : Word) else 0))) **
     (.x7 ↦ᵣ (32 : Word) - (shift0 &&& signExtend12 31)))
    (by pcFree) s7_raw
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) s123456 s7)

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
    cpsTriple base exit
      (-- Code: 11 instructions
       (base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .SW .x12 .x5 0) **
       ((base + 12) ↦ᵢ .SW .x12 .x0 4) ** ((base + 16) ↦ᵢ .SW .x12 .x0 8) **
       ((base + 20) ↦ᵢ .SW .x12 .x0 12) ** ((base + 24) ↦ᵢ .SW .x12 .x0 16) **
       ((base + 28) ↦ᵢ .SW .x12 .x0 20) ** ((base + 32) ↦ᵢ .SW .x12 .x0 24) **
       ((base + 36) ↦ᵢ .SW .x12 .x0 28) ** ((base + 40) ↦ᵢ .JAL .x0 jal_off) **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      (-- Same code + updated regs + mem
       (base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .SW .x12 .x5 0) **
       ((base + 12) ↦ᵢ .SW .x12 .x0 4) ** ((base + 16) ↦ᵢ .SW .x12 .x0 8) **
       ((base + 20) ↦ᵢ .SW .x12 .x0 12) ** ((base + 24) ↦ᵢ .SW .x12 .x0 16) **
       ((base + 28) ↦ᵢ .SW .x12 .x0 20) ** ((base + 32) ↦ᵢ .SW .x12 .x0 24) **
       ((base + 36) ↦ᵢ .SW .x12 .x0 28) ** ((base + 40) ↦ᵢ .JAL .x0 jal_off) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result0) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ 0) ** ((sp + 8) ↦ₘ 0) ** ((sp + 12) ↦ₘ 0) **
       ((sp + 16) ↦ₘ 0) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  -- Memory validity from ValidMemRange sp 8
  have hv0 : isValidMemAccess sp = true := by
    have := hvalid.get (i := 0) (by omega); simpa using this
  have hv4 : isValidMemAccess (sp + 4) = true := by
    have := hvalid.get (i := 1) (by omega); simpa using this
  have hv8 : isValidMemAccess (sp + 8) = true := by
    have := hvalid.get (i := 2) (by omega); simpa using this
  have hv12 : isValidMemAccess (sp + 12) = true := by
    have := hvalid.get (i := 3) (by omega); simpa using this
  have hv16 : isValidMemAccess (sp + 16) = true := by
    have := hvalid.get (i := 4) (by omega); simpa using this
  have hv20 : isValidMemAccess (sp + 20) = true := by
    have := hvalid.get (i := 5) (by omega); simpa using this
  have hv24 : isValidMemAccess (sp + 24) = true := by
    have := hvalid.get (i := 6) (by omega); simpa using this
  have hv28 : isValidMemAccess (sp + 28) = true := by
    have := hvalid.get (i := 7) (by omega); simpa using this
  -- Step 1: shr_last_limb with dst_off = 0
  have LL := shr_last_limb_spec 0 sp v7 v0 v5 bit_shift base
    (by simp only [signExtend12_28]; exact hv28)
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
  simp only [signExtend12_0] at LL
  rw [show sp + (0 : Word) = sp from by bv_addr] at LL
  have LLf := cpsTriple_frame_left _ _ _ _
    (((base + 12) ↦ᵢ .SW .x12 .x0 4) ** ((base + 16) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 20) ↦ᵢ .SW .x12 .x0 12) ** ((base + 24) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 20) ** ((base + 32) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 36) ↦ᵢ .SW .x12 .x0 28) ** ((base + 40) ↦ᵢ .JAL .x0 jal_off) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6))
    (by pcFree) LL
  -- Steps 2-8: 7 SW x12 x0 N for offsets 4,8,...,28
  have S0 := sw_x0_spec_gen .x12 sp v1 4 (base + 12)
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_4] at S0
  rw [show (base + 12 : Addr) + 4 = base + 16 from by bv_omega] at S0
  have S0f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 16) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 20) ↦ᵢ .SW .x12 .x0 12) ** ((base + 24) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 20) ** ((base + 32) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 36) ↦ᵢ .SW .x12 .x0 28) ** ((base + 40) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) S0
  have S1 := sw_x0_spec_gen .x12 sp v2 8 (base + 16)
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_8] at S1
  rw [show (base + 16 : Addr) + 4 = base + 20 from by bv_omega] at S1
  have S1f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 12) ↦ᵢ .SW .x12 .x0 4) **
     ((base + 20) ↦ᵢ .SW .x12 .x0 12) ** ((base + 24) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 20) ** ((base + 32) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 36) ↦ᵢ .SW .x12 .x0 28) ** ((base + 40) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 4) ↦ₘ (0 : Word)) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) S1
  have S2 := sw_x0_spec_gen .x12 sp v3 12 (base + 20)
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_12] at S2
  rw [show (base + 20 : Addr) + 4 = base + 24 from by bv_omega] at S2
  have S2f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 12) ↦ᵢ .SW .x12 .x0 4) ** ((base + 16) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 24) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 20) ** ((base + 32) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 36) ↦ᵢ .SW .x12 .x0 28) ** ((base + 40) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 4) ↦ₘ (0 : Word)) ** ((sp + 8) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) S2
  have S3 := sw_x0_spec_gen .x12 sp v4 16 (base + 24)
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_16] at S3
  rw [show (base + 24 : Addr) + 4 = base + 28 from by bv_omega] at S3
  have S3f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 12) ↦ᵢ .SW .x12 .x0 4) ** ((base + 16) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 20) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 20) ** ((base + 32) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 36) ↦ᵢ .SW .x12 .x0 28) ** ((base + 40) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 4) ↦ₘ (0 : Word)) ** ((sp + 8) ↦ₘ (0 : Word)) **
     ((sp + 12) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) S3
  have S4 := sw_x0_spec_gen .x12 sp v5v 20 (base + 28)
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_20] at S4
  rw [show (base + 28 : Addr) + 4 = base + 32 from by bv_omega] at S4
  have S4f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 12) ↦ᵢ .SW .x12 .x0 4) ** ((base + 16) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 20) ↦ᵢ .SW .x12 .x0 12) ** ((base + 24) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 32) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 36) ↦ᵢ .SW .x12 .x0 28) ** ((base + 40) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 4) ↦ₘ (0 : Word)) ** ((sp + 8) ↦ₘ (0 : Word)) **
     ((sp + 12) ↦ₘ (0 : Word)) ** ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) S4
  have S5 := sw_x0_spec_gen .x12 sp v6 24 (base + 32)
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at S5
  rw [show (base + 32 : Addr) + 4 = base + 36 from by bv_omega] at S5
  have S5f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 12) ↦ᵢ .SW .x12 .x0 4) ** ((base + 16) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 20) ↦ᵢ .SW .x12 .x0 12) ** ((base + 24) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 36) ↦ᵢ .SW .x12 .x0 28) ** ((base + 40) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 4) ↦ₘ (0 : Word)) ** ((sp + 8) ↦ₘ (0 : Word)) **
     ((sp + 12) ↦ₘ (0 : Word)) ** ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) S5
  have S6 := sw_x0_spec_gen .x12 sp v7 28 (base + 36)
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at S6
  rw [show (base + 36 : Addr) + 4 = base + 40 from by bv_omega] at S6
  have S6f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 12) ↦ᵢ .SW .x12 .x0 4) ** ((base + 16) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 20) ↦ᵢ .SW .x12 .x0 12) ** ((base + 24) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 20) ** ((base + 32) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 40) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 4) ↦ₘ (0 : Word)) ** ((sp + 8) ↦ₘ (0 : Word)) **
     ((sp + 12) ↦ₘ (0 : Word)) ** ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ (0 : Word)))
    (by pcFree) S6
  -- Step 9: JAL x0 to exit
  have JL := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 28) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 12) ↦ᵢ .SW .x12 .x0 4) ** ((base + 16) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 20) ↦ᵢ .SW .x12 .x0 12) ** ((base + 24) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 28) ↦ᵢ .SW .x12 .x0 20) ** ((base + 32) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 36) ↦ᵢ .SW .x12 .x0 28) **
     (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 4) ↦ₘ (0 : Word)) ** ((sp + 8) ↦ₘ (0 : Word)) **
     ((sp + 12) ↦ₘ (0 : Word)) ** ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) **
     ((sp + 24) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ (0 : Word)))
    (by pcFree) (jal_x0_spec_gen jal_off (base + 40))
  rw [hexit] at JL
  -- Compose all steps
  clear LL S0 S1 S2 S3 S4 S5 S6
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  have c01 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) LLf S0f; clear LLf S0f
  have c02 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 S1f; clear c01 S1f
  have c03 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 S2f; clear c02 S2f
  have c04 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 S3f; clear c03 S3f
  have c05 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 S4f; clear c04 S4f
  have c06 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 S5f; clear c05 S5f
  have c07 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 S6f; clear c06 S6f
  have cfull := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 JL; clear c07 JL
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

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
    cpsTriple base exit
      (-- Code: 17 instructions (merge_limb 7 + last_limb 3 + 6 SW + JAL)
       (base ↦ᵢ .LW .x5 .x12 24) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .LW .x10 .x12 28) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
       ((base + 28) ↦ᵢ .LW .x5 .x12 28) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 36) ↦ᵢ .SW .x12 .x5 4) **
       ((base + 40) ↦ᵢ .SW .x12 .x0 8) ** ((base + 44) ↦ᵢ .SW .x12 .x0 12) **
       ((base + 48) ↦ᵢ .SW .x12 .x0 16) ** ((base + 52) ↦ᵢ .SW .x12 .x0 20) **
       ((base + 56) ↦ᵢ .SW .x12 .x0 24) ** ((base + 60) ↦ᵢ .SW .x12 .x0 28) **
       ((base + 64) ↦ᵢ .JAL .x0 jal_off) **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      (-- Same code + updated regs + mem
       (base ↦ᵢ .LW .x5 .x12 24) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .LW .x10 .x12 28) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
       ((base + 28) ↦ᵢ .LW .x5 .x12 28) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 36) ↦ᵢ .SW .x12 .x5 4) **
       ((base + 40) ↦ᵢ .SW .x12 .x0 8) ** ((base + 44) ↦ᵢ .SW .x12 .x0 12) **
       ((base + 48) ↦ᵢ .SW .x12 .x0 16) ** ((base + 52) ↦ᵢ .SW .x12 .x0 20) **
       ((base + 56) ↦ᵢ .SW .x12 .x0 24) ** ((base + 60) ↦ᵢ .SW .x12 .x0 28) **
       ((base + 64) ↦ᵢ .JAL .x0 jal_off) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result1) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ 0) ** ((sp + 12) ↦ₘ 0) **
       ((sp + 16) ↦ₘ 0) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  -- Memory validity from ValidMemRange sp 8
  have hv0 : isValidMemAccess sp = true := by
    have := hvalid.get (i := 0) (by omega); simpa using this
  have hv4 : isValidMemAccess (sp + 4) = true := by
    have := hvalid.get (i := 1) (by omega); simpa using this
  have hv8 : isValidMemAccess (sp + 8) = true := by
    have := hvalid.get (i := 2) (by omega); simpa using this
  have hv12 : isValidMemAccess (sp + 12) = true := by
    have := hvalid.get (i := 3) (by omega); simpa using this
  have hv16 : isValidMemAccess (sp + 16) = true := by
    have := hvalid.get (i := 4) (by omega); simpa using this
  have hv20 : isValidMemAccess (sp + 20) = true := by
    have := hvalid.get (i := 5) (by omega); simpa using this
  have hv24 : isValidMemAccess (sp + 24) = true := by
    have := hvalid.get (i := 6) (by omega); simpa using this
  have hv28 : isValidMemAccess (sp + 28) = true := by
    have := hvalid.get (i := 7) (by omega); simpa using this
  -- Step 1: shr_merge_limb(24, 28, 0): base → base+28
  have MM := shr_merge_limb_spec 24 28 0 sp v6 v7 v0 v5 v10 bit_shift anti_shift mask base
    (by simp only [signExtend12_24]; exact hv24)
    (by simp only [signExtend12_28]; exact hv28)
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
  simp only [signExtend12_24, signExtend12_28, signExtend12_0] at MM
  rw [show sp + (0 : Word) = sp from by bv_addr] at MM
  have MMf := cpsTriple_frame_left _ _ _ _
    (((base + 28) ↦ᵢ .LW .x5 .x12 28) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 40) ↦ᵢ .SW .x12 .x0 8) ** ((base + 44) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 48) ↦ᵢ .SW .x12 .x0 16) ** ((base + 52) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 56) ↦ᵢ .SW .x12 .x0 24) ** ((base + 60) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 64) ↦ᵢ .JAL .x0 jal_off) **
     ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v))
    (by pcFree) MM
  -- Step 2: shr_last_limb(4): base+28 → base+40
  have LL := shr_last_limb_spec 4 sp v7 v1
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 28)
    (by simp only [signExtend12_28]; exact hv28)
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_4, signExtend12_28] at LL
  rw [show (base + 28 : Addr) + 4 = base + 32 from by bv_omega] at LL
  rw [show (base + 28 : Addr) + 8 = base + 36 from by bv_omega] at LL
  have LLf := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 24) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 28) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 40) ↦ᵢ .SW .x12 .x0 8) ** ((base + 44) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 48) ↦ᵢ .SW .x12 .x0 16) ** ((base + 52) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 56) ↦ᵢ .SW .x12 .x0 24) ** ((base + 60) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 64) ↦ᵢ .JAL .x0 jal_off) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) ** ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6))
    (by pcFree) LL
  rw [show (base + 28) + 12 = base + 40 from by bv_omega] at LLf
  -- Steps 3-8: 6 SW x12, x0, N for offsets 8,12,16,20,24,28
  have T0 := sw_x0_spec_gen .x12 sp v2 8 (base + 40)
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_8] at T0
  rw [show (base + 40 : Addr) + 4 = base + 44 from by bv_omega] at T0
  have T0f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 24) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 28) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 28) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 44) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 48) ↦ᵢ .SW .x12 .x0 16) ** ((base + 52) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 56) ↦ᵢ .SW .x12 .x0 24) ** ((base + 60) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 64) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) **
     ((sp + 12) ↦ₘ v3) ** ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T0
  have T1 := sw_x0_spec_gen .x12 sp v3 12 (base + 44)
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_12] at T1
  rw [show (base + 44 : Addr) + 4 = base + 48 from by bv_omega] at T1
  have T1f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 24) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 28) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 28) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 40) ↦ᵢ .SW .x12 .x0 8) **
     ((base + 48) ↦ᵢ .SW .x12 .x0 16) ** ((base + 52) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 56) ↦ᵢ .SW .x12 .x0 24) ** ((base + 60) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 64) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 8) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T1
  have T2 := sw_x0_spec_gen .x12 sp v4 16 (base + 48)
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_16] at T2
  rw [show (base + 48 : Addr) + 4 = base + 52 from by bv_omega] at T2
  have T2f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 24) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 28) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 28) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 40) ↦ᵢ .SW .x12 .x0 8) ** ((base + 44) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 52) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 56) ↦ᵢ .SW .x12 .x0 24) ** ((base + 60) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 64) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 8) ↦ₘ (0 : Word)) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T2
  have T3 := sw_x0_spec_gen .x12 sp v5v 20 (base + 52)
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_20] at T3
  rw [show (base + 52 : Addr) + 4 = base + 56 from by bv_omega] at T3
  have T3f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 24) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 28) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 28) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 40) ↦ᵢ .SW .x12 .x0 8) ** ((base + 44) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 48) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 56) ↦ᵢ .SW .x12 .x0 24) ** ((base + 60) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 64) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 8) ↦ₘ (0 : Word)) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T3
  have T4 := sw_x0_spec_gen .x12 sp v6 24 (base + 56)
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at T4
  rw [show (base + 56 : Addr) + 4 = base + 60 from by bv_omega] at T4
  have T4f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 24) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 28) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 28) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 40) ↦ᵢ .SW .x12 .x0 8) ** ((base + 44) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 48) ↦ᵢ .SW .x12 .x0 16) ** ((base + 52) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 60) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 64) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 8) ↦ₘ (0 : Word)) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T4
  have T5 := sw_x0_spec_gen .x12 sp v7 28 (base + 60)
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at T5
  rw [show (base + 60 : Addr) + 4 = base + 64 from by bv_omega] at T5
  have T5f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 24) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 28) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 28) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 40) ↦ᵢ .SW .x12 .x0 8) ** ((base + 44) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 48) ↦ᵢ .SW .x12 .x0 16) ** ((base + 52) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 56) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 64) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 8) ↦ₘ (0 : Word)) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ (0 : Word)))
    (by pcFree) T5
  -- Step 9: JAL x0 to exit
  have JL := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 24) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 28) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 28) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 40) ↦ᵢ .SW .x12 .x0 8) ** ((base + 44) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 48) ↦ᵢ .SW .x12 .x0 16) ** ((base + 52) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 56) ↦ᵢ .SW .x12 .x0 24) ** ((base + 60) ↦ᵢ .SW .x12 .x0 28) **
     (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 8) ↦ₘ (0 : Word)) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ (0 : Word)))
    (by pcFree) (jal_x0_spec_gen jal_off (base + 64))
  rw [hexit] at JL
  -- Compose all steps
  clear MM LL T0 T1 T2 T3 T4 T5
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  have c01 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) MMf LLf; clear MMf LLf
  have c02 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 T0f; clear c01 T0f
  have c03 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 T1f; clear c02 T1f
  have c04 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 T2f; clear c03 T2f
  have c05 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 T3f; clear c04 T3f
  have c06 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 T4f; clear c05 T4f
  have c07 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 T5f; clear c06 T5f
  have cfull := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 JL; clear c07 JL
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

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
    cpsTriple base exit
      (-- Code: 23 instructions
       -- merge_limb(20,24,0): 7 instructions at base..base+24
       (base ↦ᵢ .LW .x5 .x12 20) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .LW .x10 .x12 24) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
       -- merge_limb(24,28,4): 7 instructions at base+28..base+52
       ((base + 28) ↦ᵢ .LW .x5 .x12 24) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 36) ↦ᵢ .LW .x10 .x12 28) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
       -- last_limb(8): 3 instructions at base+56..base+64
       ((base + 56) ↦ᵢ .LW .x5 .x12 28) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 64) ↦ᵢ .SW .x12 .x5 8) **
       -- 5x SW x0 at base+68..base+84
       ((base + 68) ↦ᵢ .SW .x12 .x0 12) ** ((base + 72) ↦ᵢ .SW .x12 .x0 16) **
       ((base + 76) ↦ᵢ .SW .x12 .x0 20) ** ((base + 80) ↦ᵢ .SW .x12 .x0 24) **
       ((base + 84) ↦ᵢ .SW .x12 .x0 28) **
       -- JAL at base+88
       ((base + 88) ↦ᵢ .JAL .x0 jal_off) **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      (-- Same code + updated regs + mem
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
       ((base + 88) ↦ᵢ .JAL .x0 jal_off) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result2) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ 0) **
       ((sp + 16) ↦ₘ 0) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  -- Memory validity from ValidMemRange sp 8
  have hv0 : isValidMemAccess sp = true := by
    have := hvalid.get (i := 0) (by omega); simpa using this
  have hv4 : isValidMemAccess (sp + 4) = true := by
    have := hvalid.get (i := 1) (by omega); simpa using this
  have hv8 : isValidMemAccess (sp + 8) = true := by
    have := hvalid.get (i := 2) (by omega); simpa using this
  have hv12 : isValidMemAccess (sp + 12) = true := by
    have := hvalid.get (i := 3) (by omega); simpa using this
  have hv16 : isValidMemAccess (sp + 16) = true := by
    have := hvalid.get (i := 4) (by omega); simpa using this
  have hv20 : isValidMemAccess (sp + 20) = true := by
    have := hvalid.get (i := 5) (by omega); simpa using this
  have hv24 : isValidMemAccess (sp + 24) = true := by
    have := hvalid.get (i := 6) (by omega); simpa using this
  have hv28 : isValidMemAccess (sp + 28) = true := by
    have := hvalid.get (i := 7) (by omega); simpa using this
  -- Step 1: merge_limb(20,24,0): base → base+28
  have MM1 := shr_merge_limb_spec 20 24 0 sp v5v v6 v0 v5 v10 bit_shift anti_shift mask base
    (by simp only [signExtend12_20]; exact hv20)
    (by simp only [signExtend12_24]; exact hv24)
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
  simp only [signExtend12_20, signExtend12_24, signExtend12_0] at MM1
  rw [show sp + (0 : Word) = sp from by bv_addr] at MM1
  have MM1f := cpsTriple_frame_left _ _ _ _
    (((base + 28) ↦ᵢ .LW .x5 .x12 24) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 28) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 28) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .SW .x12 .x5 8) **
     ((base + 68) ↦ᵢ .SW .x12 .x0 12) ** ((base + 72) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 76) ↦ᵢ .SW .x12 .x0 20) ** ((base + 80) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 84) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 88) ↦ᵢ .JAL .x0 jal_off) **
     ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM1
  -- Step 2: merge_limb(24,28,4): base+28 → base+56
  have MM2 := shr_merge_limb_spec 24 28 4 sp v6 v7 v1
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28)
    (by simp only [signExtend12_24]; exact hv24)
    (by simp only [signExtend12_28]; exact hv28)
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_24, signExtend12_28, signExtend12_4] at MM2
  rw [show (base + 28 : Addr) + 4 = base + 32 from by bv_omega,
      show (base + 28 : Addr) + 8 = base + 36 from by bv_omega,
      show (base + 28 : Addr) + 12 = base + 40 from by bv_omega,
      show (base + 28 : Addr) + 16 = base + 44 from by bv_omega,
      show (base + 28 : Addr) + 20 = base + 48 from by bv_omega,
      show (base + 28 : Addr) + 24 = base + 52 from by bv_omega,
      show (base + 28 : Addr) + 28 = base + 56 from by bv_omega] at MM2
  have MM2f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 20) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 24) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 28) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .SW .x12 .x5 8) **
     ((base + 68) ↦ᵢ .SW .x12 .x0 12) ** ((base + 72) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 76) ↦ᵢ .SW .x12 .x0 20) ** ((base + 80) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 84) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 88) ↦ᵢ .JAL .x0 jal_off) **
     (sp ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v))
    (by pcFree) MM2
  -- Step 3: last_limb(8): base+56 → base+68
  have LL := shr_last_limb_spec 8 sp v7 v2
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 56)
    (by simp only [signExtend12_28]; exact hv28)
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_8, signExtend12_28] at LL
  rw [show (base + 56 : Addr) + 4 = base + 60 from by bv_omega,
      show (base + 56 : Addr) + 8 = base + 64 from by bv_omega] at LL
  have LLf := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 20) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 24) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 24) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 28) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 68) ↦ᵢ .SW .x12 .x0 12) ** ((base + 72) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 76) ↦ᵢ .SW .x12 .x0 20) ** ((base + 80) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 84) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 88) ↦ᵢ .JAL .x0 jal_off) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ v3) ** ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6))
    (by pcFree) LL
  rw [show (base + 56 : Addr) + 12 = base + 68 from by bv_omega] at LLf
  -- Steps 4-8: 5 SW x12 x0 N for offsets 12,16,20,24,28
  have T0 := sw_x0_spec_gen .x12 sp v3 12 (base + 68)
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_12] at T0
  rw [show (base + 68 : Addr) + 4 = base + 72 from by bv_omega] at T0
  have T0f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 20) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 24) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 24) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 28) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 28) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .SW .x12 .x5 8) **
     ((base + 72) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 76) ↦ᵢ .SW .x12 .x0 20) ** ((base + 80) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 84) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 88) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T0
  have T1 := sw_x0_spec_gen .x12 sp v4 16 (base + 72)
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_16] at T1
  rw [show (base + 72 : Addr) + 4 = base + 76 from by bv_omega] at T1
  have T1f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 20) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 24) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     ((base + 28) ↦ᵢ .LW .x5 .x12 24) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 28) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     ((base + 56) ↦ᵢ .LW .x5 .x12 28) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .SW .x12 .x5 8) **
     ((base + 68) ↦ᵢ .SW .x12 .x0 12) **
     ((base + 76) ↦ᵢ .SW .x12 .x0 20) ** ((base + 80) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 84) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 88) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T1
  have T2 := sw_x0_spec_gen .x12 sp v5v 20 (base + 76)
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_20] at T2
  rw [show (base + 76 : Addr) + 4 = base + 80 from by bv_omega] at T2
  have T2f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 20) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
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
     ((base + 80) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 84) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 88) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T2
  have T3 := sw_x0_spec_gen .x12 sp v6 24 (base + 80)
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at T3
  rw [show (base + 80 : Addr) + 4 = base + 84 from by bv_omega] at T3
  have T3f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 20) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
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
     ((base + 76) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 84) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 88) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T3
  have T4 := sw_x0_spec_gen .x12 sp v7 28 (base + 84)
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at T4
  rw [show (base + 84 : Addr) + 4 = base + 88 from by bv_omega] at T4
  have T4f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 20) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
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
     ((base + 88) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ (0 : Word)))
    (by pcFree) T4
  -- Step 9: JAL x0 to exit
  have JL := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 20) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
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
     (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) **
     ((sp + 24) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ (0 : Word)))
    (by pcFree) (jal_x0_spec_gen jal_off (base + 88))
  rw [hexit] at JL
  -- Compose all steps
  clear MM1 MM2 LL T0 T1 T2 T3 T4
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  have c01 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) MM1f MM2f; clear MM1f MM2f
  have c02 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 LLf; clear c01 LLf
  have c03 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 T0f; clear c02 T0f
  have c04 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 T1f; clear c03 T1f
  have c05 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 T2f; clear c04 T2f
  have c06 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 T3f; clear c05 T3f
  have c07 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 T4f; clear c06 T4f
  have cfull := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 JL; clear c07 JL
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

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
    cpsTriple base exit
      (-- Code: 29 instructions
       -- merge_limb(16,20,0): 7 instructions at base+0..base+24
       (base ↦ᵢ .LW .x5 .x12 16) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .LW .x10 .x12 20) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
       -- merge_limb(20,24,4): 7 instructions at base+28..base+52
       ((base + 28) ↦ᵢ .LW .x5 .x12 20) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
       -- merge_limb(24,28,8): 7 instructions at base+56..base+80
       ((base + 56) ↦ᵢ .LW .x5 .x12 24) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 64) ↦ᵢ .LW .x10 .x12 28) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
       -- last_limb(12): 3 instructions at base+84..base+92
       ((base + 84) ↦ᵢ .LW .x5 .x12 28) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 92) ↦ᵢ .SW .x12 .x5 12) **
       -- 4x SW x0: at base+96..base+108
       ((base + 96) ↦ᵢ .SW .x12 .x0 16) ** ((base + 100) ↦ᵢ .SW .x12 .x0 20) **
       ((base + 104) ↦ᵢ .SW .x12 .x0 24) ** ((base + 108) ↦ᵢ .SW .x12 .x0 28) **
       -- JAL x0 at base+112
       ((base + 112) ↦ᵢ .JAL .x0 jal_off) **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      (-- Same code + updated regs + mem
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
       ((base + 112) ↦ᵢ .JAL .x0 jal_off) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result3) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ 0) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  -- Memory validity from ValidMemRange sp 8
  have hv0 : isValidMemAccess sp = true := by
    have := hvalid.get (i := 0) (by omega); simpa using this
  have hv4 : isValidMemAccess (sp + 4) = true := by
    have := hvalid.get (i := 1) (by omega); simpa using this
  have hv8 : isValidMemAccess (sp + 8) = true := by
    have := hvalid.get (i := 2) (by omega); simpa using this
  have hv12 : isValidMemAccess (sp + 12) = true := by
    have := hvalid.get (i := 3) (by omega); simpa using this
  have hv16 : isValidMemAccess (sp + 16) = true := by
    have := hvalid.get (i := 4) (by omega); simpa using this
  have hv20 : isValidMemAccess (sp + 20) = true := by
    have := hvalid.get (i := 5) (by omega); simpa using this
  have hv24 : isValidMemAccess (sp + 24) = true := by
    have := hvalid.get (i := 6) (by omega); simpa using this
  have hv28 : isValidMemAccess (sp + 28) = true := by
    have := hvalid.get (i := 7) (by omega); simpa using this
  -- Step 1: merge_limb(16,20,0): base -> base+28
  have MM1 := shr_merge_limb_spec 16 20 0 sp v4 v5v v0 v5 v10 bit_shift anti_shift mask base
    (by simp only [signExtend12_16]; exact hv16)
    (by simp only [signExtend12_20]; exact hv20)
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
  simp only [signExtend12_16, signExtend12_20, signExtend12_0] at MM1
  rw [show sp + (0 : Word) = sp from by bv_addr] at MM1
  have MM1f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 20) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 24) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 28) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- last_limb instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 28) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .SW .x12 .x5 12) **
     -- SW x0 instrAt
     ((base + 96) ↦ᵢ .SW .x12 .x0 16) ** ((base + 100) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 104) ↦ᵢ .SW .x12 .x0 24) ** ((base + 108) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 112) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM1
  -- Step 2: merge_limb(20,24,4): base+28 -> base+56
  have MM2 := shr_merge_limb_spec 20 24 4 sp v5v v6 v1
    ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))
    ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28)
    (by simp only [signExtend12_20]; exact hv20)
    (by simp only [signExtend12_24]; exact hv24)
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_20, signExtend12_24, signExtend12_4] at MM2
  rw [show (base + 28) + 4 = base + 32 from by bv_omega,
      show (base + 28) + 8 = base + 36 from by bv_omega,
      show (base + 28) + 12 = base + 40 from by bv_omega,
      show (base + 28) + 16 = base + 44 from by bv_omega,
      show (base + 28) + 20 = base + 48 from by bv_omega,
      show (base + 28) + 24 = base + 52 from by bv_omega] at MM2
  have MM2f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt (preserved)
     (base ↦ᵢ .LW .x5 .x12 16) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 20) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 24) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 28) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- last_limb instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 28) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .SW .x12 .x5 12) **
     -- SW x0 instrAt
     ((base + 96) ↦ᵢ .SW .x12 .x0 16) ** ((base + 100) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 104) ↦ᵢ .SW .x12 .x0 24) ** ((base + 108) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 112) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM2
  rw [show (base + 28) + 28 = base + 56 from by bv_omega] at MM2f
  -- Step 3: merge_limb(24,28,8): base+56 -> base+84
  have MM3 := shr_merge_limb_spec 24 28 8 sp v6 v7 v2
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 56)
    (by simp only [signExtend12_24]; exact hv24)
    (by simp only [signExtend12_28]; exact hv28)
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_24, signExtend12_28, signExtend12_8] at MM3
  rw [show (base + 56) + 4 = base + 60 from by bv_omega,
      show (base + 56) + 8 = base + 64 from by bv_omega,
      show (base + 56) + 12 = base + 68 from by bv_omega,
      show (base + 56) + 16 = base + 72 from by bv_omega,
      show (base + 56) + 20 = base + 76 from by bv_omega,
      show (base + 56) + 24 = base + 80 from by bv_omega] at MM3
  have MM3f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 16) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 20) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 20) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- last_limb instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 28) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .SW .x12 .x5 12) **
     -- SW x0 instrAt
     ((base + 96) ↦ᵢ .SW .x12 .x0 16) ** ((base + 100) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 104) ↦ᵢ .SW .x12 .x0 24) ** ((base + 108) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 112) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ v3) ** ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v))
    (by pcFree) MM3
  rw [show (base + 56) + 28 = base + 84 from by bv_omega] at MM3f
  -- Step 4: last_limb(12): base+84 -> base+96
  have LL := shr_last_limb_spec 12 sp v7 v3
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 84)
    (by simp only [signExtend12_28]; exact hv28)
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_12, signExtend12_28] at LL
  rw [show (base + 84) + 4 = base + 88 from by bv_omega,
      show (base + 84) + 8 = base + 92 from by bv_omega] at LL
  have LLf := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 16) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 20) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 20) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 24) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 24) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 28) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- SW x0 instrAt
     ((base + 96) ↦ᵢ .SW .x12 .x0 16) ** ((base + 100) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 104) ↦ᵢ .SW .x12 .x0 24) ** ((base + 108) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 112) ↦ᵢ .JAL .x0 jal_off) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6))
    (by pcFree) LL
  rw [show (base + 84) + 12 = base + 96 from by bv_omega] at LLf
  -- Steps 5-8: 4 SW zeros
  have T0 := sw_x0_spec_gen .x12 sp v4 16 (base + 96)
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_16] at T0
  rw [show (base + 96 : Addr) + 4 = base + 100 from by bv_omega] at T0
  have T0f := cpsTriple_frame_left _ _ _ _
    (-- all instrAt except (base+96)
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
     ((base + 100) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 104) ↦ᵢ .SW .x12 .x0 24) ** ((base + 108) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 112) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T0
  have T1 := sw_x0_spec_gen .x12 sp v5v 20 (base + 100)
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_20] at T1
  rw [show (base + 100 : Addr) + 4 = base + 104 from by bv_omega] at T1
  have T1f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 16) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
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
     ((base + 96) ↦ᵢ .SW .x12 .x0 16) **
     ((base + 104) ↦ᵢ .SW .x12 .x0 24) ** ((base + 108) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 112) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 16) ↦ₘ (0 : Word)) **
     ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T1
  have T2 := sw_x0_spec_gen .x12 sp v6 24 (base + 104)
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at T2
  rw [show (base + 104 : Addr) + 4 = base + 108 from by bv_omega] at T2
  have T2f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 16) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
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
     ((base + 108) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 112) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 16) ↦ₘ (0 : Word)) **
     ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T2
  have T3 := sw_x0_spec_gen .x12 sp v7 28 (base + 108)
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at T3
  rw [show (base + 108 : Addr) + 4 = base + 112 from by bv_omega] at T3
  have T3f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 16) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
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
     ((base + 104) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 112) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 16) ↦ₘ (0 : Word)) **
     ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ (0 : Word)))
    (by pcFree) T3
  -- JAL x0 to exit
  have JL := cpsTriple_frame_left _ _ _ _
    (-- all instrAt except (base+112)
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
     (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 16) ↦ₘ (0 : Word)) **
     ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ (0 : Word)))
    (by pcFree) (jal_x0_spec_gen jal_off (base + 112))
  rw [hexit] at JL
  -- Compose all steps
  clear MM1 MM2 MM3 LL T0 T1 T2 T3
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  have c01 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) MM1f MM2f; clear MM1f MM2f
  have c02 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 MM3f; clear c01 MM3f
  have c03 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 LLf; clear c02 LLf
  have c04 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 T0f; clear c03 T0f
  have c05 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 T1f; clear c04 T1f
  have c06 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 T2f; clear c05 T2f
  have c07 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 T3f; clear c06 T3f
  have cfull := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 JL; clear c07 JL
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

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
    cpsTriple base exit
      (-- Code: 35 instructions
       -- merge_limb(12,16,0): 7 instructions at base..base+24
       (base ↦ᵢ .LW .x5 .x12 12) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .LW .x10 .x12 16) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
       -- merge_limb(16,20,4): 7 instructions at base+28..base+52
       ((base + 28) ↦ᵢ .LW .x5 .x12 16) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 36) ↦ᵢ .LW .x10 .x12 20) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
       -- merge_limb(20,24,8): 7 instructions at base+56..base+80
       ((base + 56) ↦ᵢ .LW .x5 .x12 20) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 64) ↦ᵢ .LW .x10 .x12 24) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
       -- merge_limb(24,28,12): 7 instructions at base+84..base+108
       ((base + 84) ↦ᵢ .LW .x5 .x12 24) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 92) ↦ᵢ .LW .x10 .x12 28) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
       -- last_limb(16): 3 instructions at base+112..base+120
       ((base + 112) ↦ᵢ .LW .x5 .x12 28) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 120) ↦ᵢ .SW .x12 .x5 16) **
       -- 3x SW x0 at base+124..base+132
       ((base + 124) ↦ᵢ .SW .x12 .x0 20) ** ((base + 128) ↦ᵢ .SW .x12 .x0 24) **
       ((base + 132) ↦ᵢ .SW .x12 .x0 28) **
       -- JAL at base+136
       ((base + 136) ↦ᵢ .JAL .x0 jal_off) **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      (-- Same code + updated regs + mem
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
       ((base + 136) ↦ᵢ .JAL .x0 jal_off) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result4) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ result4) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  -- Memory validity from ValidMemRange sp 8
  have hv0 : isValidMemAccess sp = true := by
    have := hvalid.get (i := 0) (by omega); simpa using this
  have hv4 : isValidMemAccess (sp + 4) = true := by
    have := hvalid.get (i := 1) (by omega); simpa using this
  have hv8 : isValidMemAccess (sp + 8) = true := by
    have := hvalid.get (i := 2) (by omega); simpa using this
  have hv12 : isValidMemAccess (sp + 12) = true := by
    have := hvalid.get (i := 3) (by omega); simpa using this
  have hv16 : isValidMemAccess (sp + 16) = true := by
    have := hvalid.get (i := 4) (by omega); simpa using this
  have hv20 : isValidMemAccess (sp + 20) = true := by
    have := hvalid.get (i := 5) (by omega); simpa using this
  have hv24 : isValidMemAccess (sp + 24) = true := by
    have := hvalid.get (i := 6) (by omega); simpa using this
  have hv28 : isValidMemAccess (sp + 28) = true := by
    have := hvalid.get (i := 7) (by omega); simpa using this
  -- Step 1: merge_limb(12,16,0): base -> base+28
  have MM1 := shr_merge_limb_spec 12 16 0 sp v3 v4 v0 v5 v10 bit_shift anti_shift mask base
    (by simp only [signExtend12_12]; exact hv12)
    (by simp only [signExtend12_16]; exact hv16)
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
  simp only [signExtend12_12, signExtend12_16, signExtend12_0] at MM1
  rw [show sp + (0 : Word) = sp from by bv_addr] at MM1
  have MM1f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 16) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 20) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 20) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 24) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 24) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 28) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- last_limb instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 28) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .SW .x12 .x5 16) **
     -- SW x0 instrAt
     ((base + 124) ↦ᵢ .SW .x12 .x0 20) ** ((base + 128) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 132) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 136) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM1
  -- Step 2: merge_limb(16,20,4): base+28 -> base+56
  have MM2 := shr_merge_limb_spec 16 20 4 sp v4 v5v v1
    ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28)
    (by simp only [signExtend12_16]; exact hv16)
    (by simp only [signExtend12_20]; exact hv20)
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_16, signExtend12_20, signExtend12_4] at MM2
  rw [show (base + 28) + 4 = base + 32 from by bv_omega,
      show (base + 28) + 8 = base + 36 from by bv_omega,
      show (base + 28) + 12 = base + 40 from by bv_omega,
      show (base + 28) + 16 = base + 44 from by bv_omega,
      show (base + 28) + 20 = base + 48 from by bv_omega,
      show (base + 28) + 24 = base + 52 from by bv_omega] at MM2
  have MM2f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt (preserved)
     (base ↦ᵢ .LW .x5 .x12 12) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 16) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 20) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 24) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 24) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 28) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- last_limb instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 28) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .SW .x12 .x5 16) **
     -- SW x0 instrAt
     ((base + 124) ↦ᵢ .SW .x12 .x0 20) ** ((base + 128) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 132) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 136) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM2
  rw [show (base + 28) + 28 = base + 56 from by bv_omega] at MM2f
  -- Step 3: merge_limb(20,24,8): base+56 -> base+84
  have MM3 := shr_merge_limb_spec 20 24 8 sp v5v v6 v2
    ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))
    ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 56)
    (by simp only [signExtend12_20]; exact hv20)
    (by simp only [signExtend12_24]; exact hv24)
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_20, signExtend12_24, signExtend12_8] at MM3
  rw [show (base + 56) + 4 = base + 60 from by bv_omega,
      show (base + 56) + 8 = base + 64 from by bv_omega,
      show (base + 56) + 12 = base + 68 from by bv_omega,
      show (base + 56) + 16 = base + 72 from by bv_omega,
      show (base + 56) + 20 = base + 76 from by bv_omega,
      show (base + 56) + 24 = base + 80 from by bv_omega] at MM3
  have MM3f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 12) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 16) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 16) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 20) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 24) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 28) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- last_limb instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 28) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .SW .x12 .x5 16) **
     -- SW x0 instrAt
     ((base + 124) ↦ᵢ .SW .x12 .x0 20) ** ((base + 128) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 132) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 136) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ v3) ** ((sp + 16) ↦ₘ v4) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM3
  rw [show (base + 56) + 28 = base + 84 from by bv_omega] at MM3f
  -- Step 4: merge_limb(24,28,12): base+84 -> base+112
  have MM4 := shr_merge_limb_spec 24 28 12 sp v6 v7 v3
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 84)
    (by simp only [signExtend12_24]; exact hv24)
    (by simp only [signExtend12_28]; exact hv28)
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_24, signExtend12_28, signExtend12_12] at MM4
  rw [show (base + 84) + 4 = base + 88 from by bv_omega,
      show (base + 84) + 8 = base + 92 from by bv_omega,
      show (base + 84) + 12 = base + 96 from by bv_omega,
      show (base + 84) + 16 = base + 100 from by bv_omega,
      show (base + 84) + 20 = base + 104 from by bv_omega,
      show (base + 84) + 24 = base + 108 from by bv_omega] at MM4
  have MM4f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 12) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 16) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 16) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 20) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 20) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 24) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- last_limb instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 28) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .SW .x12 .x5 16) **
     -- SW x0 instrAt
     ((base + 124) ↦ᵢ .SW .x12 .x0 20) ** ((base + 128) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 132) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 136) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v))
    (by pcFree) MM4
  rw [show (base + 84) + 28 = base + 112 from by bv_omega] at MM4f
  -- Step 5: last_limb(16): base+112 -> base+124
  have LL := shr_last_limb_spec 16 sp v7 v4
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 112)
    (by simp only [signExtend12_28]; exact hv28)
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_16, signExtend12_28] at LL
  rw [show (base + 112 : Addr) + 4 = base + 116 from by bv_omega,
      show (base + 112 : Addr) + 8 = base + 120 from by bv_omega] at LL
  have LLf := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 12) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 16) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 16) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 20) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 20) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 24) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 24) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 28) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- SW x0 instrAt
     ((base + 124) ↦ᵢ .SW .x12 .x0 20) ** ((base + 128) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 132) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 136) ↦ᵢ .JAL .x0 jal_off) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6))
    (by pcFree) LL
  rw [show (base + 112 : Addr) + 12 = base + 124 from by bv_omega] at LLf
  -- Steps 6-8: 3 SW zeros
  have T0 := sw_x0_spec_gen .x12 sp v5v 20 (base + 124)
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_20] at T0
  rw [show (base + 124 : Addr) + 4 = base + 128 from by bv_omega] at T0
  have T0f := cpsTriple_frame_left _ _ _ _
    (-- all instrAt except (base+124)
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
     ((base + 128) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 132) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 136) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) **
     ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T0
  have T1 := sw_x0_spec_gen .x12 sp v6 24 (base + 128)
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at T1
  rw [show (base + 128 : Addr) + 4 = base + 132 from by bv_omega] at T1
  have T1f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 12) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
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
     ((base + 124) ↦ᵢ .SW .x12 .x0 20) **
     ((base + 132) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 136) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 20) ↦ₘ (0 : Word)) **
     ((sp + 28) ↦ₘ v7))
    (by pcFree) T1
  have T2 := sw_x0_spec_gen .x12 sp v7 28 (base + 132)
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at T2
  rw [show (base + 132 : Addr) + 4 = base + 136 from by bv_omega] at T2
  have T2f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 12) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
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
     ((base + 136) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 20) ↦ₘ (0 : Word)) **
     ((sp + 24) ↦ₘ (0 : Word)))
    (by pcFree) T2
  -- JAL x0 to exit
  have JL := cpsTriple_frame_left _ _ _ _
    (-- all instrAt except (base+136)
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
     (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 20) ↦ₘ (0 : Word)) **
     ((sp + 24) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ (0 : Word)))
    (by pcFree) (jal_x0_spec_gen jal_off (base + 136))
  rw [hexit] at JL
  -- Compose all steps
  clear MM1 MM2 MM3 MM4 LL T0 T1 T2
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  have c01 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) MM1f MM2f; clear MM1f MM2f
  have c02 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 MM3f; clear c01 MM3f
  have c03 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 MM4f; clear c02 MM4f
  have c04 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 LLf; clear c03 LLf
  have c05 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 T0f; clear c04 T0f
  have c06 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 T1f; clear c05 T1f
  have c07 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 T2f; clear c06 T2f
  have cfull := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 JL; clear c07 JL
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull
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
    cpsTriple base exit
      (-- Code: 41 instructions
       -- merge_limb(8,12,0): 7 instructions at base..base+24
       (base ↦ᵢ .LW .x5 .x12 8) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .LW .x10 .x12 12) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
       -- merge_limb(12,16,4): 7 instructions at base+28..base+52
       ((base + 28) ↦ᵢ .LW .x5 .x12 12) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 36) ↦ᵢ .LW .x10 .x12 16) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
       -- merge_limb(16,20,8): 7 instructions at base+56..base+80
       ((base + 56) ↦ᵢ .LW .x5 .x12 16) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 64) ↦ᵢ .LW .x10 .x12 20) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
       -- merge_limb(20,24,12): 7 instructions at base+84..base+108
       ((base + 84) ↦ᵢ .LW .x5 .x12 20) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 92) ↦ᵢ .LW .x10 .x12 24) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
       -- merge_limb(24,28,16): 7 instructions at base+112..base+136
       ((base + 112) ↦ᵢ .LW .x5 .x12 24) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 120) ↦ᵢ .LW .x10 .x12 28) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
       -- last_limb(20): 3 instructions at base+140..base+148
       ((base + 140) ↦ᵢ .LW .x5 .x12 28) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 148) ↦ᵢ .SW .x12 .x5 20) **
       -- 2x SW x0 at base+152..base+156
       ((base + 152) ↦ᵢ .SW .x12 .x0 24) ** ((base + 156) ↦ᵢ .SW .x12 .x0 28) **
       -- JAL at base+160
       ((base + 160) ↦ᵢ .JAL .x0 jal_off) **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      (-- Same code + updated regs + mem
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
       ((base + 160) ↦ᵢ .JAL .x0 jal_off) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ result4) ** ((sp + 20) ↦ₘ result5) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  -- Memory validity from ValidMemRange sp 8
  have hv0 : isValidMemAccess sp = true := by
    have := hvalid.get (i := 0) (by omega); simpa using this
  have hv4 : isValidMemAccess (sp + 4) = true := by
    have := hvalid.get (i := 1) (by omega); simpa using this
  have hv8 : isValidMemAccess (sp + 8) = true := by
    have := hvalid.get (i := 2) (by omega); simpa using this
  have hv12 : isValidMemAccess (sp + 12) = true := by
    have := hvalid.get (i := 3) (by omega); simpa using this
  have hv16 : isValidMemAccess (sp + 16) = true := by
    have := hvalid.get (i := 4) (by omega); simpa using this
  have hv20 : isValidMemAccess (sp + 20) = true := by
    have := hvalid.get (i := 5) (by omega); simpa using this
  have hv24 : isValidMemAccess (sp + 24) = true := by
    have := hvalid.get (i := 6) (by omega); simpa using this
  have hv28 : isValidMemAccess (sp + 28) = true := by
    have := hvalid.get (i := 7) (by omega); simpa using this
  -- Step 1: merge_limb(8,12,0): base -> base+28
  have MM1 := shr_merge_limb_spec 8 12 0 sp v2 v3 v0 v5 v10 bit_shift anti_shift mask base
    (by simp only [signExtend12_8]; exact hv8)
    (by simp only [signExtend12_12]; exact hv12)
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
  simp only [signExtend12_8, signExtend12_12, signExtend12_0] at MM1
  rw [show sp + (0 : Word) = sp from by bv_addr] at MM1
  have MM1f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 12) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 16) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 16) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 20) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 20) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 24) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 24) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 28) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- last_limb instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 28) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .SW .x12 .x5 20) **
     -- SW x0 instrAt
     ((base + 152) ↦ᵢ .SW .x12 .x0 24) ** ((base + 156) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 160) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     ((sp + 4) ↦ₘ v1) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM1
  -- Step 2: merge_limb(12,16,4): base+28 -> base+56
  have MM2 := shr_merge_limb_spec 12 16 4 sp v3 v4 v1
    ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28)
    (by simp only [signExtend12_12]; exact hv12)
    (by simp only [signExtend12_16]; exact hv16)
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_12, signExtend12_16, signExtend12_4] at MM2
  rw [show (base + 28) + 4 = base + 32 from by bv_omega,
      show (base + 28) + 8 = base + 36 from by bv_omega,
      show (base + 28) + 12 = base + 40 from by bv_omega,
      show (base + 28) + 16 = base + 44 from by bv_omega,
      show (base + 28) + 20 = base + 48 from by bv_omega,
      show (base + 28) + 24 = base + 52 from by bv_omega] at MM2
  have MM2f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt (preserved)
     (base ↦ᵢ .LW .x5 .x12 8) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 12) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 16) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 20) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 20) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 24) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 24) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 28) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- last_limb instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 28) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .SW .x12 .x5 20) **
     -- SW x0 instrAt
     ((base + 152) ↦ᵢ .SW .x12 .x0 24) ** ((base + 156) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 160) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ v2) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM2
  rw [show (base + 28) + 28 = base + 56 from by bv_omega] at MM2f
  -- Step 3: merge_limb(16,20,8): base+56 -> base+84
  have MM3 := shr_merge_limb_spec 16 20 8 sp v4 v5v v2
    ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 56)
    (by simp only [signExtend12_16]; exact hv16)
    (by simp only [signExtend12_20]; exact hv20)
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_16, signExtend12_20, signExtend12_8] at MM3
  rw [show (base + 56) + 4 = base + 60 from by bv_omega,
      show (base + 56) + 8 = base + 64 from by bv_omega,
      show (base + 56) + 12 = base + 68 from by bv_omega,
      show (base + 56) + 16 = base + 72 from by bv_omega,
      show (base + 56) + 20 = base + 76 from by bv_omega,
      show (base + 56) + 24 = base + 80 from by bv_omega] at MM3
  have MM3f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 8) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 12) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 12) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 16) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 20) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 24) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 24) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 28) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- last_limb instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 28) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .SW .x12 .x5 20) **
     -- SW x0 instrAt
     ((base + 152) ↦ᵢ .SW .x12 .x0 24) ** ((base + 156) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 160) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ v3) **
     ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM3
  rw [show (base + 56) + 28 = base + 84 from by bv_omega] at MM3f
  -- Step 4: merge_limb(20,24,12): base+84 -> base+112
  have MM4 := shr_merge_limb_spec 20 24 12 sp v5v v6 v3
    ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))
    ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 84)
    (by simp only [signExtend12_20]; exact hv20)
    (by simp only [signExtend12_24]; exact hv24)
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_20, signExtend12_24, signExtend12_12] at MM4
  rw [show (base + 84) + 4 = base + 88 from by bv_omega,
      show (base + 84) + 8 = base + 92 from by bv_omega,
      show (base + 84) + 12 = base + 96 from by bv_omega,
      show (base + 84) + 16 = base + 100 from by bv_omega,
      show (base + 84) + 20 = base + 104 from by bv_omega,
      show (base + 84) + 24 = base + 108 from by bv_omega] at MM4
  have MM4f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 8) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 12) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 12) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 16) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 16) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 20) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 24) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 28) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- last_limb instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 28) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .SW .x12 .x5 20) **
     -- SW x0 instrAt
     ((base + 152) ↦ᵢ .SW .x12 .x0 24) ** ((base + 156) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 160) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM4
  rw [show (base + 84) + 28 = base + 112 from by bv_omega] at MM4f
  -- Step 5: merge_limb(24,28,16): base+112 -> base+140
  have MM5 := shr_merge_limb_spec 24 28 16 sp v6 v7 v4
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 112)
    (by simp only [signExtend12_24]; exact hv24)
    (by simp only [signExtend12_28]; exact hv28)
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_24, signExtend12_28, signExtend12_16] at MM5
  rw [show (base + 112) + 4 = base + 116 from by bv_omega,
      show (base + 112) + 8 = base + 120 from by bv_omega,
      show (base + 112) + 12 = base + 124 from by bv_omega,
      show (base + 112) + 16 = base + 128 from by bv_omega,
      show (base + 112) + 20 = base + 132 from by bv_omega,
      show (base + 112) + 24 = base + 136 from by bv_omega] at MM5
  have MM5f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 8) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 12) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 12) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 16) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 16) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 20) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 20) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 24) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- last_limb instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 28) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .SW .x12 .x5 20) **
     -- SW x0 instrAt
     ((base + 152) ↦ᵢ .SW .x12 .x0 24) ** ((base + 156) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 160) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ v5v))
    (by pcFree) MM5
  rw [show (base + 112) + 28 = base + 140 from by bv_omega] at MM5f
  -- Step 6: last_limb(20): base+140 -> base+152
  have LL := shr_last_limb_spec 20 sp v7 v5v
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 140)
    (by simp only [signExtend12_28]; exact hv28)
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_20, signExtend12_28] at LL
  rw [show (base + 140 : Addr) + 4 = base + 144 from by bv_omega,
      show (base + 140 : Addr) + 8 = base + 148 from by bv_omega] at LL
  have LLf := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 8) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 12) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 12) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 16) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 16) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 20) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 20) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 24) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 24) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 28) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- SW x0 instrAt
     ((base + 152) ↦ᵢ .SW .x12 .x0 24) ** ((base + 156) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 160) ↦ᵢ .JAL .x0 jal_off) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 24) ↦ₘ v6))
    (by pcFree) LL
  rw [show (base + 140 : Addr) + 12 = base + 152 from by bv_omega] at LLf
  -- Steps 7-8: 2 SW zeros
  have T0 := sw_x0_spec_gen .x12 sp v6 24 (base + 152)
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at T0
  rw [show (base + 152 : Addr) + 4 = base + 156 from by bv_omega] at T0
  have T0f := cpsTriple_frame_left _ _ _ _
    (-- all instrAt except (base+152)
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
     ((base + 156) ↦ᵢ .SW .x12 .x0 28) **
     ((base + 160) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) **
     ((sp + 28) ↦ₘ v7))
    (by pcFree) T0
  have T1 := sw_x0_spec_gen .x12 sp v7 28 (base + 156)
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at T1
  rw [show (base + 156 : Addr) + 4 = base + 160 from by bv_omega] at T1
  have T1f := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x5 .x12 8) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
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
     ((base + 152) ↦ᵢ .SW .x12 .x0 24) **
     ((base + 160) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) **
     ((sp + 24) ↦ₘ (0 : Word)))
    (by pcFree) T1
  -- JAL x0 to exit
  have JL := cpsTriple_frame_left _ _ _ _
    (-- all instrAt except (base+160)
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
     (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) **
     ((sp + 24) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ (0 : Word)))
    (by pcFree) (jal_x0_spec_gen jal_off (base + 160))
  rw [hexit] at JL
  -- Compose all steps
  clear MM1 MM2 MM3 MM4 MM5 LL T0 T1
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  have c01 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) MM1f MM2f; clear MM1f MM2f
  have c02 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 MM3f; clear c01 MM3f
  have c03 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 MM4f; clear c02 MM4f
  have c04 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 MM5f; clear c03 MM5f
  have c05 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 LLf; clear c04 LLf
  have c06 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 T0f; clear c05 T0f
  have c07 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 T1f; clear c06 T1f
  have cfull := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 JL; clear c07 JL
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull
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
    cpsTriple base exit
      (-- Code: 47 instructions
       -- merge_limb(4,8,0): 7 instructions at base..base+24
       (base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .LW .x10 .x12 8) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
       -- merge_limb(8,12,4): 7 instructions at base+28..base+52
       ((base + 28) ↦ᵢ .LW .x5 .x12 8) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 36) ↦ᵢ .LW .x10 .x12 12) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
       -- merge_limb(12,16,8): 7 instructions at base+56..base+80
       ((base + 56) ↦ᵢ .LW .x5 .x12 12) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 64) ↦ᵢ .LW .x10 .x12 16) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
       -- merge_limb(16,20,12): 7 instructions at base+84..base+108
       ((base + 84) ↦ᵢ .LW .x5 .x12 16) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 92) ↦ᵢ .LW .x10 .x12 20) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
       -- merge_limb(20,24,16): 7 instructions at base+112..base+136
       ((base + 112) ↦ᵢ .LW .x5 .x12 20) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 120) ↦ᵢ .LW .x10 .x12 24) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
       -- merge_limb(24,28,20): 7 instructions at base+140..base+164
       ((base + 140) ↦ᵢ .LW .x5 .x12 24) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 148) ↦ᵢ .LW .x10 .x12 28) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
       -- last_limb(24): 3 instructions at base+168..base+176
       ((base + 168) ↦ᵢ .LW .x5 .x12 28) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 176) ↦ᵢ .SW .x12 .x5 24) **
       -- 1x SW x0 at base+180
       ((base + 180) ↦ᵢ .SW .x12 .x0 28) **
       -- JAL at base+184
       ((base + 184) ↦ᵢ .JAL .x0 jal_off) **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      (-- Same code + updated regs + mem
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
       ((base + 184) ↦ᵢ .JAL .x0 jal_off) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result6) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ result4) ** ((sp + 20) ↦ₘ result5) ** ((sp + 24) ↦ₘ result6) ** ((sp + 28) ↦ₘ 0)) := by
  -- Memory validity from ValidMemRange sp 8
  have hv0 : isValidMemAccess sp = true := by
    have := hvalid.get (i := 0) (by omega); simpa using this
  have hv4 : isValidMemAccess (sp + 4) = true := by
    have := hvalid.get (i := 1) (by omega); simpa using this
  have hv8 : isValidMemAccess (sp + 8) = true := by
    have := hvalid.get (i := 2) (by omega); simpa using this
  have hv12 : isValidMemAccess (sp + 12) = true := by
    have := hvalid.get (i := 3) (by omega); simpa using this
  have hv16 : isValidMemAccess (sp + 16) = true := by
    have := hvalid.get (i := 4) (by omega); simpa using this
  have hv20 : isValidMemAccess (sp + 20) = true := by
    have := hvalid.get (i := 5) (by omega); simpa using this
  have hv24 : isValidMemAccess (sp + 24) = true := by
    have := hvalid.get (i := 6) (by omega); simpa using this
  have hv28 : isValidMemAccess (sp + 28) = true := by
    have := hvalid.get (i := 7) (by omega); simpa using this
  -- Step 1: merge_limb(4,8,0): base -> base+28
  have MM1 := shr_merge_limb_spec 4 8 0 sp v1 v2 v0 v5 v10 bit_shift anti_shift mask base
    (by simp only [signExtend12_4]; exact hv4)
    (by simp only [signExtend12_8]; exact hv8)
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
  simp only [signExtend12_4, signExtend12_8, signExtend12_0] at MM1
  rw [show sp + (0 : Word) = sp from by bv_addr] at MM1
  have MM1f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 8) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 12) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 12) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 16) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 16) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 20) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 20) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 24) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- merge_limb 6 instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 24) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .LW .x10 .x12 28) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
     -- last_limb instrAt
     ((base + 168) ↦ᵢ .LW .x5 .x12 28) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 176) ↦ᵢ .SW .x12 .x5 24) **
     -- SW x0 instrAt
     ((base + 180) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 184) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     ((sp + 12) ↦ₘ v3) ** ((sp + 16) ↦ₘ v4) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM1
  -- Step 2: merge_limb(8,12,4): base+28 -> base+56
  have MM2 := shr_merge_limb_spec 8 12 4 sp v2 v3 v1
    ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v2 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28)
    (by simp only [signExtend12_8]; exact hv8)
    (by simp only [signExtend12_12]; exact hv12)
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_8, signExtend12_12, signExtend12_4] at MM2
  rw [show (base + 28) + 4 = base + 32 from by bv_omega,
      show (base + 28) + 8 = base + 36 from by bv_omega,
      show (base + 28) + 12 = base + 40 from by bv_omega,
      show (base + 28) + 16 = base + 44 from by bv_omega,
      show (base + 28) + 20 = base + 48 from by bv_omega,
      show (base + 28) + 24 = base + 52 from by bv_omega] at MM2
  have MM2f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt (preserved)
     (base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 8) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 12) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 16) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 16) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 20) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 20) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 24) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- merge_limb 6 instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 24) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .LW .x10 .x12 28) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
     -- last_limb instrAt
     ((base + 168) ↦ᵢ .LW .x5 .x12 28) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 176) ↦ᵢ .SW .x12 .x5 24) **
     -- SW x0 instrAt
     ((base + 180) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 184) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ v4) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM2
  rw [show (base + 28) + 28 = base + 56 from by bv_omega] at MM2f
  -- Step 3: merge_limb(12,16,8): base+56 -> base+84
  have MM3 := shr_merge_limb_spec 12 16 8 sp v3 v4 v2
    ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 56)
    (by simp only [signExtend12_12]; exact hv12)
    (by simp only [signExtend12_16]; exact hv16)
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_12, signExtend12_16, signExtend12_8] at MM3
  rw [show (base + 56) + 4 = base + 60 from by bv_omega,
      show (base + 56) + 8 = base + 64 from by bv_omega,
      show (base + 56) + 12 = base + 68 from by bv_omega,
      show (base + 56) + 16 = base + 72 from by bv_omega,
      show (base + 56) + 20 = base + 76 from by bv_omega,
      show (base + 56) + 24 = base + 80 from by bv_omega] at MM3
  have MM3f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 8) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 8) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 12) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 16) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 20) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 20) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 24) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- merge_limb 6 instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 24) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .LW .x10 .x12 28) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
     -- last_limb instrAt
     ((base + 168) ↦ᵢ .LW .x5 .x12 28) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 176) ↦ᵢ .SW .x12 .x5 24) **
     -- SW x0 instrAt
     ((base + 180) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 184) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM3
  rw [show (base + 56) + 28 = base + 84 from by bv_omega] at MM3f
  -- Step 4: merge_limb(16,20,12): base+84 -> base+112
  have MM4 := shr_merge_limb_spec 16 20 12 sp v4 v5v v3
    ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 84)
    (by simp only [signExtend12_16]; exact hv16)
    (by simp only [signExtend12_20]; exact hv20)
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_16, signExtend12_20, signExtend12_12] at MM4
  rw [show (base + 84) + 4 = base + 88 from by bv_omega,
      show (base + 84) + 8 = base + 92 from by bv_omega,
      show (base + 84) + 12 = base + 96 from by bv_omega,
      show (base + 84) + 16 = base + 100 from by bv_omega,
      show (base + 84) + 20 = base + 104 from by bv_omega,
      show (base + 84) + 24 = base + 108 from by bv_omega] at MM4
  have MM4f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 8) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 8) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 12) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 12) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 16) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 20) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 24) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- merge_limb 6 instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 24) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .LW .x10 .x12 28) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
     -- last_limb instrAt
     ((base + 168) ↦ᵢ .LW .x5 .x12 28) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 176) ↦ᵢ .SW .x12 .x5 24) **
     -- SW x0 instrAt
     ((base + 180) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 184) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM4
  rw [show (base + 84) + 28 = base + 112 from by bv_omega] at MM4f
  -- Step 5: merge_limb(20,24,16): base+112 -> base+140
  have MM5 := shr_merge_limb_spec 20 24 16 sp v5v v6 v4
    ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))
    ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 112)
    (by simp only [signExtend12_20]; exact hv20)
    (by simp only [signExtend12_24]; exact hv24)
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_20, signExtend12_24, signExtend12_16] at MM5
  rw [show (base + 112) + 4 = base + 116 from by bv_omega,
      show (base + 112) + 8 = base + 120 from by bv_omega,
      show (base + 112) + 12 = base + 124 from by bv_omega,
      show (base + 112) + 16 = base + 128 from by bv_omega,
      show (base + 112) + 20 = base + 132 from by bv_omega,
      show (base + 112) + 24 = base + 136 from by bv_omega] at MM5
  have MM5f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 8) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 8) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 12) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 12) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 16) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 16) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 20) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb 6 instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 24) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .LW .x10 .x12 28) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
     -- last_limb instrAt
     ((base + 168) ↦ᵢ .LW .x5 .x12 28) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 176) ↦ᵢ .SW .x12 .x5 24) **
     -- SW x0 instrAt
     ((base + 180) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 184) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 28) ↦ₘ v7))
    (by pcFree) MM5
  rw [show (base + 112) + 28 = base + 140 from by bv_omega] at MM5f
  -- Step 6: merge_limb(24,28,20): base+140 -> base+168
  have MM6 := shr_merge_limb_spec 24 28 20 sp v6 v7 v5v
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 140)
    (by simp only [signExtend12_24]; exact hv24)
    (by simp only [signExtend12_28]; exact hv28)
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_24, signExtend12_28, signExtend12_20] at MM6
  rw [show (base + 140) + 4 = base + 144 from by bv_omega,
      show (base + 140) + 8 = base + 148 from by bv_omega,
      show (base + 140) + 12 = base + 152 from by bv_omega,
      show (base + 140) + 16 = base + 156 from by bv_omega,
      show (base + 140) + 20 = base + 160 from by bv_omega,
      show (base + 140) + 24 = base + 164 from by bv_omega] at MM6
  have MM6f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 8) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 8) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 12) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 12) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 16) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 16) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 20) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 20) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 24) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- last_limb instrAt
     ((base + 168) ↦ᵢ .LW .x5 .x12 28) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 176) ↦ᵢ .SW .x12 .x5 24) **
     -- SW x0 instrAt
     ((base + 180) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 184) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))))
    (by pcFree) MM6
  rw [show (base + 140) + 28 = base + 168 from by bv_omega] at MM6f
  -- Step 7: last_limb(24): base+168 -> base+180
  have LL := shr_last_limb_spec 24 sp v7 v6
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 168)
    (by simp only [signExtend12_28]; exact hv28)
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24, signExtend12_28] at LL
  rw [show (base + 168 : Addr) + 4 = base + 172 from by bv_omega,
      show (base + 168 : Addr) + 8 = base + 176 from by bv_omega] at LL
  have LLf := cpsTriple_frame_left _ _ _ _
    (-- merge_limb 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 4) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 8) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 8) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 12) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 12) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 16) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 16) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 20) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 20) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 24) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- merge_limb 6 instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 24) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .LW .x10 .x12 28) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
     -- SW x0 instrAt
     ((base + 180) ↦ᵢ .SW .x12 .x0 28) **
     -- JAL instrAt
     ((base + 184) ↦ᵢ .JAL .x0 jal_off) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))))
    (by pcFree) LL
  rw [show (base + 168 : Addr) + 12 = base + 180 from by bv_omega] at LLf
  -- Step 8: 1 SW zero
  have T0 := sw_x0_spec_gen .x12 sp v7 28 (base + 180)
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at T0
  rw [show (base + 180 : Addr) + 4 = base + 184 from by bv_omega] at T0
  have T0f := cpsTriple_frame_left _ _ _ _
    (-- all instrAt except (base+180)
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
     ((base + 184) ↦ᵢ .JAL .x0 jal_off) **
     (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 24) ↦ₘ (v7 >>> (bit_shift.toNat % 32))))
    (by pcFree) T0
  -- JAL x0 to exit
  have JL := cpsTriple_frame_left _ _ _ _
    (-- all instrAt except (base+184)
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
     (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 24) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 28) ↦ₘ (0 : Word)))
    (by pcFree) (jal_x0_spec_gen jal_off (base + 184))
  rw [hexit] at JL
  -- Compose all steps
  clear MM1 MM2 MM3 MM4 MM5 MM6 LL T0
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  have c01 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) MM1f MM2f; clear MM1f MM2f
  have c02 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 MM3f; clear c01 MM3f
  have c03 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 MM4f; clear c02 MM4f
  have c04 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 MM5f; clear c03 MM5f
  have c05 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 MM6f; clear c04 MM6f
  have c06 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 LLf; clear c05 LLf
  have c07 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 T0f; clear c06 T0f
  have cfull := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 JL; clear c07 JL
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull
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
    cpsTriple base exit
      (-- Code: 53 instructions
       -- merge_limb_inplace(0,4): 7 instructions at base..base+24
       (base ↦ᵢ .LW .x5 .x12 0) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 8) ↦ᵢ .LW .x10 .x12 4) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
       -- merge_limb_inplace(4,8): 7 instructions at base+28..base+52
       ((base + 28) ↦ᵢ .LW .x5 .x12 4) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 36) ↦ᵢ .LW .x10 .x12 8) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
       -- merge_limb_inplace(8,12): 7 instructions at base+56..base+80
       ((base + 56) ↦ᵢ .LW .x5 .x12 8) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 64) ↦ᵢ .LW .x10 .x12 12) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
       -- merge_limb_inplace(12,16): 7 instructions at base+84..base+108
       ((base + 84) ↦ᵢ .LW .x5 .x12 12) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 92) ↦ᵢ .LW .x10 .x12 16) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
       -- merge_limb_inplace(16,20): 7 instructions at base+112..base+136
       ((base + 112) ↦ᵢ .LW .x5 .x12 16) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 120) ↦ᵢ .LW .x10 .x12 20) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
       -- merge_limb_inplace(20,24): 7 instructions at base+140..base+164
       ((base + 140) ↦ᵢ .LW .x5 .x12 20) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 148) ↦ᵢ .LW .x10 .x12 24) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
       -- merge_limb_inplace(24,28): 7 instructions at base+168..base+192
       ((base + 168) ↦ᵢ .LW .x5 .x12 24) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 176) ↦ᵢ .LW .x10 .x12 28) ** ((base + 180) ↦ᵢ .SLL .x10 .x10 .x7) **
       ((base + 184) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 188) ↦ᵢ .OR .x5 .x5 .x10) **
       ((base + 192) ↦ᵢ .SW .x12 .x5 24) **
       -- last_limb_inplace: 3 instructions at base+196..base+204
       ((base + 196) ↦ᵢ .LW .x5 .x12 28) ** ((base + 200) ↦ᵢ .SRL .x5 .x5 .x6) **
       ((base + 204) ↦ᵢ .SW .x12 .x5 28) **
       -- JAL at base+208
       ((base + 208) ↦ᵢ .JAL .x0 jal_off) **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      (-- Same code + updated regs + mem
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
       ((base + 208) ↦ᵢ .JAL .x0 jal_off) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result7) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ result4) ** ((sp + 20) ↦ₘ result5) ** ((sp + 24) ↦ₘ result6) ** ((sp + 28) ↦ₘ result7)) := by
  -- Memory validity from ValidMemRange sp 8
  have hv0 : isValidMemAccess sp = true := by
    have := hvalid.get (i := 0) (by omega); simpa using this
  have hv4 : isValidMemAccess (sp + 4) = true := by
    have := hvalid.get (i := 1) (by omega); simpa using this
  have hv8 : isValidMemAccess (sp + 8) = true := by
    have := hvalid.get (i := 2) (by omega); simpa using this
  have hv12 : isValidMemAccess (sp + 12) = true := by
    have := hvalid.get (i := 3) (by omega); simpa using this
  have hv16 : isValidMemAccess (sp + 16) = true := by
    have := hvalid.get (i := 4) (by omega); simpa using this
  have hv20 : isValidMemAccess (sp + 20) = true := by
    have := hvalid.get (i := 5) (by omega); simpa using this
  have hv24 : isValidMemAccess (sp + 24) = true := by
    have := hvalid.get (i := 6) (by omega); simpa using this
  have hv28 : isValidMemAccess (sp + 28) = true := by
    have := hvalid.get (i := 7) (by omega); simpa using this
  -- Step 1: merge_limb_inplace(0,4): base -> base+28
  have MM1 := shr_merge_limb_inplace_spec 0 4 sp v0 v1 v5 v10 bit_shift anti_shift mask base
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_0, signExtend12_4] at MM1
  rw [show sp + (0 : Word) = sp from by bv_addr] at MM1
  have MM1f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb_inplace 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 4) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 8) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb_inplace 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 8) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 12) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb_inplace 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 12) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 16) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb_inplace 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 16) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 20) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- merge_limb_inplace 6 instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 20) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .LW .x10 .x12 24) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
     -- merge_limb_inplace 7 instrAt
     ((base + 168) ↦ᵢ .LW .x5 .x12 24) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 176) ↦ᵢ .LW .x10 .x12 28) ** ((base + 180) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 184) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 188) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 192) ↦ᵢ .SW .x12 .x5 24) **
     -- last_limb_inplace instrAt
     ((base + 196) ↦ᵢ .LW .x5 .x12 28) ** ((base + 200) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 204) ↦ᵢ .SW .x12 .x5 28) **
     -- JAL instrAt
     ((base + 208) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM1
  -- Step 2: merge_limb_inplace(4,8): base+28 -> base+56
  have MM2 := shr_merge_limb_inplace_spec 4 8 sp v1 v2
    ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v1 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28)
    (by simp only [signExtend12_4]; exact hv4)
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_4, signExtend12_8] at MM2
  rw [show (base + 28) + 4 = base + 32 from by bv_omega,
      show (base + 28) + 8 = base + 36 from by bv_omega,
      show (base + 28) + 12 = base + 40 from by bv_omega,
      show (base + 28) + 16 = base + 44 from by bv_omega,
      show (base + 28) + 20 = base + 48 from by bv_omega,
      show (base + 28) + 24 = base + 52 from by bv_omega] at MM2
  have MM2f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb_inplace 1 instrAt (preserved)
     (base ↦ᵢ .LW .x5 .x12 0) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 4) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb_inplace 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 8) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 12) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb_inplace 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 12) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 16) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb_inplace 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 16) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 20) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- merge_limb_inplace 6 instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 20) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .LW .x10 .x12 24) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
     -- merge_limb_inplace 7 instrAt
     ((base + 168) ↦ᵢ .LW .x5 .x12 24) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 176) ↦ᵢ .LW .x10 .x12 28) ** ((base + 180) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 184) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 188) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 192) ↦ᵢ .SW .x12 .x5 24) **
     -- last_limb_inplace instrAt
     ((base + 196) ↦ᵢ .LW .x5 .x12 28) ** ((base + 200) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 204) ↦ᵢ .SW .x12 .x5 28) **
     -- JAL instrAt
     ((base + 208) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ v3) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM2
  rw [show (base + 28) + 28 = base + 56 from by bv_omega] at MM2f
  -- Step 3: merge_limb_inplace(8,12): base+56 -> base+84
  have MM3 := shr_merge_limb_inplace_spec 8 12 sp v2 v3
    ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v2 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 56)
    (by simp only [signExtend12_8]; exact hv8)
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_8, signExtend12_12] at MM3
  rw [show (base + 56) + 4 = base + 60 from by bv_omega,
      show (base + 56) + 8 = base + 64 from by bv_omega,
      show (base + 56) + 12 = base + 68 from by bv_omega,
      show (base + 56) + 16 = base + 72 from by bv_omega,
      show (base + 56) + 20 = base + 76 from by bv_omega,
      show (base + 56) + 24 = base + 80 from by bv_omega] at MM3
  have MM3f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb_inplace 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 0) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 4) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb_inplace 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 4) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 8) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb_inplace 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 12) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 16) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb_inplace 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 16) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 20) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- merge_limb_inplace 6 instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 20) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .LW .x10 .x12 24) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
     -- merge_limb_inplace 7 instrAt
     ((base + 168) ↦ᵢ .LW .x5 .x12 24) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 176) ↦ᵢ .LW .x10 .x12 28) ** ((base + 180) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 184) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 188) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 192) ↦ᵢ .SW .x12 .x5 24) **
     -- last_limb_inplace instrAt
     ((base + 196) ↦ᵢ .LW .x5 .x12 28) ** ((base + 200) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 204) ↦ᵢ .SW .x12 .x5 28) **
     -- JAL instrAt
     ((base + 208) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM3
  rw [show (base + 56) + 28 = base + 84 from by bv_omega] at MM3f
  -- Step 4: merge_limb_inplace(12,16): base+84 -> base+112
  have MM4 := shr_merge_limb_inplace_spec 12 16 sp v3 v4
    ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 84)
    (by simp only [signExtend12_12]; exact hv12)
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_12, signExtend12_16] at MM4
  rw [show (base + 84) + 4 = base + 88 from by bv_omega,
      show (base + 84) + 8 = base + 92 from by bv_omega,
      show (base + 84) + 12 = base + 96 from by bv_omega,
      show (base + 84) + 16 = base + 100 from by bv_omega,
      show (base + 84) + 20 = base + 104 from by bv_omega,
      show (base + 84) + 24 = base + 108 from by bv_omega] at MM4
  have MM4f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb_inplace 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 0) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 4) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb_inplace 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 4) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 8) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb_inplace 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 8) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 12) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb_inplace 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 16) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 20) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- merge_limb_inplace 6 instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 20) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .LW .x10 .x12 24) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
     -- merge_limb_inplace 7 instrAt
     ((base + 168) ↦ᵢ .LW .x5 .x12 24) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 176) ↦ᵢ .LW .x10 .x12 28) ** ((base + 180) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 184) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 188) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 192) ↦ᵢ .SW .x12 .x5 24) **
     -- last_limb_inplace instrAt
     ((base + 196) ↦ᵢ .LW .x5 .x12 28) ** ((base + 200) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 204) ↦ᵢ .SW .x12 .x5 28) **
     -- JAL instrAt
     ((base + 208) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM4
  rw [show (base + 84) + 28 = base + 112 from by bv_omega] at MM4f
  -- Step 5: merge_limb_inplace(16,20): base+112 -> base+140
  have MM5 := shr_merge_limb_inplace_spec 16 20 sp v4 v5v
    ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 112)
    (by simp only [signExtend12_16]; exact hv16)
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_16, signExtend12_20] at MM5
  rw [show (base + 112) + 4 = base + 116 from by bv_omega,
      show (base + 112) + 8 = base + 120 from by bv_omega,
      show (base + 112) + 12 = base + 124 from by bv_omega,
      show (base + 112) + 16 = base + 128 from by bv_omega,
      show (base + 112) + 20 = base + 132 from by bv_omega,
      show (base + 112) + 24 = base + 136 from by bv_omega] at MM5
  have MM5f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb_inplace 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 0) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 4) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb_inplace 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 4) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 8) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb_inplace 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 8) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 12) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb_inplace 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 12) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 16) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb_inplace 6 instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 20) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .LW .x10 .x12 24) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
     -- merge_limb_inplace 7 instrAt
     ((base + 168) ↦ᵢ .LW .x5 .x12 24) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 176) ↦ᵢ .LW .x10 .x12 28) ** ((base + 180) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 184) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 188) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 192) ↦ᵢ .SW .x12 .x5 24) **
     -- last_limb_inplace instrAt
     ((base + 196) ↦ᵢ .LW .x5 .x12 28) ** ((base + 200) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 204) ↦ᵢ .SW .x12 .x5 28) **
     -- JAL instrAt
     ((base + 208) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM5
  rw [show (base + 112) + 28 = base + 140 from by bv_omega] at MM5f
  -- Step 6: merge_limb_inplace(20,24): base+140 -> base+168
  have MM6 := shr_merge_limb_inplace_spec 20 24 sp v5v v6
    ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))
    ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 140)
    (by simp only [signExtend12_20]; exact hv20)
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_20, signExtend12_24] at MM6
  rw [show (base + 140) + 4 = base + 144 from by bv_omega,
      show (base + 140) + 8 = base + 148 from by bv_omega,
      show (base + 140) + 12 = base + 152 from by bv_omega,
      show (base + 140) + 16 = base + 156 from by bv_omega,
      show (base + 140) + 20 = base + 160 from by bv_omega,
      show (base + 140) + 24 = base + 164 from by bv_omega] at MM6
  have MM6f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb_inplace 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 0) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 4) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb_inplace 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 4) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 8) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb_inplace 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 8) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 12) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb_inplace 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 12) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 16) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb_inplace 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 16) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 20) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- merge_limb_inplace 7 instrAt
     ((base + 168) ↦ᵢ .LW .x5 .x12 24) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 176) ↦ᵢ .LW .x10 .x12 28) ** ((base + 180) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 184) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 188) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 192) ↦ᵢ .SW .x12 .x5 24) **
     -- last_limb_inplace instrAt
     ((base + 196) ↦ᵢ .LW .x5 .x12 28) ** ((base + 200) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 204) ↦ᵢ .SW .x12 .x5 28) **
     -- JAL instrAt
     ((base + 208) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 28) ↦ₘ v7))
    (by pcFree) MM6
  rw [show (base + 140) + 28 = base + 168 from by bv_omega] at MM6f
  -- Step 7: merge_limb_inplace(24,28): base+168 -> base+196
  have MM7 := shr_merge_limb_inplace_spec 24 28 sp v6 v7
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 168)
    (by simp only [signExtend12_24]; exact hv24)
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_24, signExtend12_28] at MM7
  rw [show (base + 168) + 4 = base + 172 from by bv_omega,
      show (base + 168) + 8 = base + 176 from by bv_omega,
      show (base + 168) + 12 = base + 180 from by bv_omega,
      show (base + 168) + 16 = base + 184 from by bv_omega,
      show (base + 168) + 20 = base + 188 from by bv_omega,
      show (base + 168) + 24 = base + 192 from by bv_omega] at MM7
  have MM7f := cpsTriple_frame_left _ _ _ _
    (-- merge_limb_inplace 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 0) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 4) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb_inplace 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 4) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 8) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb_inplace 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 8) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 12) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb_inplace 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 12) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 16) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb_inplace 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 16) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 20) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- merge_limb_inplace 6 instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 20) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .LW .x10 .x12 24) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
     -- last_limb_inplace instrAt
     ((base + 196) ↦ᵢ .LW .x5 .x12 28) ** ((base + 200) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 204) ↦ᵢ .SW .x12 .x5 28) **
     -- JAL instrAt
     ((base + 208) ↦ᵢ .JAL .x0 jal_off) **
     -- remaining mem
     (sp ↦ₘ ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))))
    (by pcFree) MM7
  rw [show (base + 168) + 28 = base + 196 from by bv_omega] at MM7f
  -- Step 8: last_limb_inplace: base+196 -> base+208
  have LL := shr_last_limb_inplace_spec sp v7
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 196)
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at LL
  rw [show (base + 196 : Addr) + 4 = base + 200 from by bv_omega,
      show (base + 196 : Addr) + 8 = base + 204 from by bv_omega] at LL
  have LLf := cpsTriple_frame_left _ _ _ _
    (-- merge_limb_inplace 1 instrAt
     (base ↦ᵢ .LW .x5 .x12 0) ** ((base + 4) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 8) ↦ᵢ .LW .x10 .x12 4) ** ((base + 12) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 16) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 20) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 24) ↦ᵢ .SW .x12 .x5 0) **
     -- merge_limb_inplace 2 instrAt
     ((base + 28) ↦ᵢ .LW .x5 .x12 4) ** ((base + 32) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 36) ↦ᵢ .LW .x10 .x12 8) ** ((base + 40) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 44) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 48) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 52) ↦ᵢ .SW .x12 .x5 4) **
     -- merge_limb_inplace 3 instrAt
     ((base + 56) ↦ᵢ .LW .x5 .x12 8) ** ((base + 60) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 64) ↦ᵢ .LW .x10 .x12 12) ** ((base + 68) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 72) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 76) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 80) ↦ᵢ .SW .x12 .x5 8) **
     -- merge_limb_inplace 4 instrAt
     ((base + 84) ↦ᵢ .LW .x5 .x12 12) ** ((base + 88) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 92) ↦ᵢ .LW .x10 .x12 16) ** ((base + 96) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 100) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 104) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 108) ↦ᵢ .SW .x12 .x5 12) **
     -- merge_limb_inplace 5 instrAt
     ((base + 112) ↦ᵢ .LW .x5 .x12 16) ** ((base + 116) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 120) ↦ᵢ .LW .x10 .x12 20) ** ((base + 124) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 128) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 132) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 136) ↦ᵢ .SW .x12 .x5 16) **
     -- merge_limb_inplace 6 instrAt
     ((base + 140) ↦ᵢ .LW .x5 .x12 20) ** ((base + 144) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 148) ↦ᵢ .LW .x10 .x12 24) ** ((base + 152) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 156) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 160) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 164) ↦ᵢ .SW .x12 .x5 20) **
     -- merge_limb_inplace 7 instrAt
     ((base + 168) ↦ᵢ .LW .x5 .x12 24) ** ((base + 172) ↦ᵢ .SRL .x5 .x5 .x6) **
     ((base + 176) ↦ᵢ .LW .x10 .x12 28) ** ((base + 180) ↦ᵢ .SLL .x10 .x10 .x7) **
     ((base + 184) ↦ᵢ .AND .x10 .x10 .x11) ** ((base + 188) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 192) ↦ᵢ .SW .x12 .x5 24) **
     -- JAL instrAt
     ((base + 208) ↦ᵢ .JAL .x0 jal_off) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 24) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))))
    (by pcFree) LL
  rw [show (base + 196 : Addr) + 12 = base + 208 from by bv_omega] at LLf
  -- JAL x0 to exit
  have JL := cpsTriple_frame_left _ _ _ _
    (-- all instrAt except (base+208)
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
     (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 24) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 28) ↦ₘ (v7 >>> (bit_shift.toNat % 32))))
    (by pcFree) (jal_x0_spec_gen jal_off (base + 208))
  rw [hexit] at JL
  -- Compose all steps
  clear MM1 MM2 MM3 MM4 MM5 MM6 MM7 LL
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  have c01 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) MM1f MM2f; clear MM1f MM2f
  have c02 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 MM3f; clear c01 MM3f
  have c03 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 MM4f; clear c02 MM4f
  have c04 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 MM5f; clear c03 MM5f
  have c05 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 MM6f; clear c04 MM6f
  have c06 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 MM7f; clear c05 MM7f
  have c07 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 LLf; clear c06 LLf
  have cfull := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 JL; clear c07 JL
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull
/-- LW x10, off(x12); OR x5, x5, x10:
    Load a word from memory and OR it into x5. 2 instructions. -/
theorem shr_lw_or_acc_spec (sp acc prev_x10 val : Word) (off : BitVec 12)
    (base : Addr)
    (hvalid : isValidMemAccess (sp + signExtend12 off) = true) :
    cpsTriple base (base + 8)
      ((base ↦ᵢ .LW .x10 .x12 off) ** ((base + 4) ↦ᵢ .OR .x5 .x5 .x10) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ acc) ** (.x10 ↦ᵣ prev_x10) ** ((sp + signExtend12 off) ↦ₘ val))
      ((base ↦ᵢ .LW .x10 .x12 off) ** ((base + 4) ↦ᵢ .OR .x5 .x5 .x10) **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (acc ||| val)) ** (.x10 ↦ᵣ val) ** ((sp + signExtend12 off) ↦ₘ val)) := by
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  -- Step 1: LW x10 x12 off at base
  have s1 := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .OR .x5 .x5 .x10) ** (.x5 ↦ᵣ acc))
    (by pcFree) (lw_spec_gen .x10 .x12 sp prev_x10 val off base (by nofun) hvalid)
  -- Step 2: OR x5 x5 x10 at base+4 (rd=rs1=x5, rs2=x10)
  have s2_raw := or_spec_gen_rd_eq_rs1 .x5 .x10 acc val (base + 4) (by nofun) (by nofun)
  rw [ha1] at s2_raw
  have s2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x10 .x12 off) ** (.x12 ↦ᵣ sp) ** ((sp + signExtend12 off) ↦ₘ val))
    (by pcFree) s2_raw
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) s1 s2)
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
  -- Memory validity from ValidMemRange sp 8
  have hv0 : isValidMemAccess sp = true := by
    have := hvalid.get (i := 0) (by omega); simpa using this
  have hv4 : isValidMemAccess (sp + 4) = true := by
    have := hvalid.get (i := 1) (by omega); simpa using this
  have hv8 : isValidMemAccess (sp + 8) = true := by
    have := hvalid.get (i := 2) (by omega); simpa using this
  have hv12 : isValidMemAccess (sp + 12) = true := by
    have := hvalid.get (i := 3) (by omega); simpa using this
  have hv16 : isValidMemAccess (sp + 16) = true := by
    have := hvalid.get (i := 4) (by omega); simpa using this
  have hv20 : isValidMemAccess (sp + 20) = true := by
    have := hvalid.get (i := 5) (by omega); simpa using this
  have hv24 : isValidMemAccess (sp + 24) = true := by
    have := hvalid.get (i := 6) (by omega); simpa using this
  have hv28 : isValidMemAccess (sp + 28) = true := by
    have := hvalid.get (i := 7) (by omega); simpa using this
  -- Address arithmetic
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have ha52 : (base + 52 : Addr) + 4 = base + 56 := by bv_omega
  have ha56 : (base + 56 : Addr) + 4 = base + 60 := by bv_omega
  have ha60 : (base + 60 : Addr) + 4 = base + 64 := by bv_omega
  have ha64 : (base + 64 : Addr) + 4 = base + 68 := by bv_omega
  -- Step 1: LW x5 x12 4 at base (loads s1 into x5)
  have lw1 := lw_spec_gen .x5 .x12 sp r5 s1 4 base (by nofun)
    (by simp only [signExtend12_4]; exact hv4)
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
    (by simp only [signExtend12_8]; exact hv8)
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
    (by simp only [signExtend12_12]; exact hv12)
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
    (by simp only [signExtend12_16]; exact hv16)
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
    (by simp only [signExtend12_20]; exact hv20)
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
    (by simp only [signExtend12_24]; exact hv24)
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
    (by simp only [signExtend12_28]; exact hv28)
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
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
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

-- evm_shr_spec is proved in EvmAsm.Evm.ShiftComposition

end EvmAsm
