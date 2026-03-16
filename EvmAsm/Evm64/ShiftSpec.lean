/-
  EvmAsm.Evm64.ShiftSpec

  CPS specifications for the 256-bit EVM SHR (logical shift right) program (64-bit).
  Modular decomposition:
  - Per-limb helpers: shr_merge_limb_spec (7 instrs), shr_last_limb_spec (3 instrs)
  - Zero path: shr_zero_path_spec (5 instrs, shift >= 256)
  - Phase B: shr_phase_b_spec (7 instrs, extract parameters)
  - Phase A: shr_phase_a_spec (9 instrs, check shift >= 256)
  - Shift bodies: shr_body_L_spec for L = 0..3
-/

import EvmAsm.Evm64.Shift
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

set_option maxHeartbeats 800000

-- ============================================================================
-- Per-limb Specs: SHR Merge Limb (7 instructions)
-- ============================================================================

abbrev shr_merge_limb_code (src_off next_off dst_off : BitVec 12) (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 src_off))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SRL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x10 .x12 next_off))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SLL .x10 .x10 .x7))
  (CodeReq.union (CodeReq.singleton (base + 16) (.AND .x10 .x10 .x11))
  (CodeReq.union (CodeReq.singleton (base + 20) (.OR .x5 .x5 .x10))
  (CodeReq.singleton (base + 24) (.SD .x12 .x5 dst_off)))))))

/-- SHR merge limb spec (7 instructions):
    LD x5, src_off(x12); SRL x5,x5,x6; LD x10, next_off(x12);
    SLL x10,x10,x7; AND x10,x10,x11; OR x5,x5,x10; SD x12,x5,dst_off

    Computes: result = (src >>> bit_shift) ||| ((next <<< anti_shift) &&& mask)
    and stores at dst_off.

    Preserves: x12, x6, x7, x11, memory at src and next.
    Modifies: x5 (= result), x10 (= (next <<< anti_shift) &&& mask), memory at dst. -/
theorem shr_merge_limb_spec (src_off next_off dst_off : BitVec 12)
    (sp src next dst_old v5 v10 bit_shift anti_shift mask : Word) (base : Addr)
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
  runBlock

-- ============================================================================
-- Per-limb Specs: SHR Last Limb (3 instructions)
-- ============================================================================

abbrev shr_last_limb_code (dst_off : BitVec 12) (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SRL .x5 .x5 .x6))
  (CodeReq.singleton (base + 8) (.SD .x12 .x5 dst_off)))

/-- SHR last limb spec (3 instructions):
    LD x5, 24(x12); SRL x5,x5,x6; SD x12,x5,dst_off

    Computes: result = value[3] >>> bit_shift
    and stores at dst_off. This is the highest non-zero limb in a shift body.

    Preserves: x12, x6, x7, x10, x11, memory at value[3].
    Modifies: x5 (= result), memory at dst. -/
theorem shr_last_limb_spec (dst_off : BitVec 12)
    (sp src dst_old v5 bit_shift : Word) (base : Addr)
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
  runBlock

-- ============================================================================
-- Per-limb Specs: SHR Merge Limb In-place (7 instructions, src_off = dst_off)
-- ============================================================================

abbrev shr_merge_limb_inplace_code (off next_off : BitVec 12) (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 off))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SRL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x10 .x12 next_off))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SLL .x10 .x10 .x7))
  (CodeReq.union (CodeReq.singleton (base + 16) (.AND .x10 .x10 .x11))
  (CodeReq.union (CodeReq.singleton (base + 20) (.OR .x5 .x5 .x10))
  (CodeReq.singleton (base + 24) (.SD .x12 .x5 off)))))))

/-- SHR merge limb in-place spec (7 instructions):
    Same as shr_merge_limb_spec but src_off = dst_off. The source value is
    read then overwritten in place. Only 2 memory cells needed (no separate dst). -/
theorem shr_merge_limb_inplace_spec (off next_off : BitVec 12)
    (sp src next v5 v10 bit_shift anti_shift mask : Word) (base : Addr)
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
  runBlock

-- ============================================================================
-- Per-limb Specs: SHR Last Limb In-place (3 instructions, dst_off = 24)
-- ============================================================================

abbrev shr_last_limb_inplace_code (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SRL .x5 .x5 .x6))
  (CodeReq.singleton (base + 8) (.SD .x12 .x5 24)))

/-- SHR last limb in-place spec (3 instructions):
    LD x5, 24(x12); SRL x5,x5,x6; SD x12,x5,24
    Reads and writes the same memory cell at sp+24. -/
theorem shr_last_limb_inplace_spec
    (sp src v5 bit_shift : Word) (base : Addr)
    (hvalid : isValidDwordAccess (sp + signExtend12 (24 : BitVec 12)) = true) :
    let mem := sp + signExtend12 (24 : BitVec 12)
    let result := src >>> (bit_shift.toNat % 64)
    let code := shr_last_limb_inplace_code base
    cpsTriple base (base + 12) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ src))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ result)) := by
  runBlock

-- ============================================================================
-- Zero path spec (5 instructions): shift >= 256, result is all zeros
-- ============================================================================

abbrev shr_zero_path_code (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ADDI .x12 .x12 32))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SD .x12 .x0 0))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SD .x12 .x0 8))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x0 16))
  (CodeReq.singleton (base + 16) (.SD .x12 .x0 24)))))

set_option maxHeartbeats 3200000 in
/-- Zero path spec: ADDI x12, x12, 32 followed by 4 SD x12, x0, N.
    This is used when shift >= 256. Advances sp by 32 and zeros all 4 result limbs. -/
theorem shr_zero_path_spec (sp : Word)
    (d0 d1 d2 d3 : Word)   -- old values at result locations
    (base : Addr)
    (hvalid : ValidMemRange (sp + 32) 4) :
    let nsp := sp + 32
    let code := shr_zero_path_code base
    cpsTriple base (base + 20) code
      ((.x12 ↦ᵣ sp) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3))
      ((.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0)) := by
  -- Introduce nsp as opaque fvar to prevent address flattening
  intro nsp
  -- Compose: ADDI + 4x SD x0 via runBlock
  have A := addi_spec_gen_same .x12 sp 32 base (by nofun)
  rw [show sp + signExtend12 (32 : BitVec 12) = nsp from by simp only [signExtend12_32]; rfl] at A
  have S0 := sd_x0_spec_gen .x12 nsp d0 0 (base + 4) (by validMem)
  have S1 := sd_x0_spec_gen .x12 nsp d1 8 (base + 8) (by validMem)
  have S2 := sd_x0_spec_gen .x12 nsp d2 16 (base + 12) (by validMem)
  have S3 := sd_x0_spec_gen .x12 nsp d3 24 (base + 16) (by validMem)
  runBlock A S0 S1 S2 S3

-- ============================================================================
-- Phase B spec: Extract parameters (7 instructions)
-- ============================================================================

abbrev shr_phase_b_code (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ANDI .x6 .x5 63))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SRLI .x5 .x5 6))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x11 .x0 .x6))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SUB .x11 .x0 .x11))
  (CodeReq.union (CodeReq.singleton (base + 16) (.LI .x7 64))
  (CodeReq.union (CodeReq.singleton (base + 20) (.SUB .x7 .x7 .x6))
  (CodeReq.singleton (base + 24) (.ADDI .x12 .x12 32)))))))

set_option maxHeartbeats 1600000 in
/-- Phase B spec: Extract bit_shift, limb_shift, mask, anti_shift from shift0.
    ANDI x6,x5,63; SRLI x5,x5,6; SLTU x11,x0,x6; SUB x11,x0,x11;
    LI x7,64; SUB x7,x7,x6; ADDI x12,x12,32.
    Requires .x0 ↦ᵣ 0 for SLTU and SUB instructions using x0. -/
theorem shr_phase_b_spec (shift0 sp r6 r7 r11 : Word) (base : Addr) :
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
    let code :=
      CodeReq.union (CodeReq.singleton base (.ADDI .x10 .x0 k))
      (CodeReq.singleton (base + 4) (.BEQ .x5 .x10 offset))
    cpsBranch base code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      target ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val))
      (base + 8) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val)) := by
  have ha1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  -- Step 1: ADDI x10, x0, k at base (rd=x10, rs1=x0, rd≠rs1)
  have s1 := cpsTriple_frame_left _ _ _ _ _
    (.x5 ↦ᵣ v5)
    (by pcFree) (addi_spec_gen .x10 .x0 v10 0 k base (by nofun))
  -- Step 2: BEQ x5, x10, offset at base+4
  -- Get BEQ spec and immediately drop pure facts from postconditions
  have s2_raw := beq_spec_gen .x5 .x10 offset v5 ((0 : Word) + signExtend12 k) (base + 4)
  rw [htarget, ha1] at s2_raw
  have s2 : cpsBranch (base + 4) _
      ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)))
      target ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)))
      (base + 8) ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 k))) :=
    cpsBranch_consequence _ _ _ _ target _ _ (base + 8) _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ (v5 = (0 : Word) + signExtend12 k) h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ (v5 ≠ (0 : Word) + signExtend12 k) h').1 hp').1) h hp)
      s2_raw
  -- Frame BEQ with x0
  have s2f := cpsBranch_frame_left _ _ _ _ _ _ _
    (.x0 ↦ᵣ (0 : Word))
    (by pcFree) s2
  -- Compose: cpsTriple followed by cpsBranch, with permutation
  have composed := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1 s2f
  -- Final permutation of postconditions
  exact cpsBranch_consequence _ _
    _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

-- ============================================================================
-- Phase C spec: cascade dispatch (5 instructions, cpsNBranch with 4 exits)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Phase C spec: cascade dispatch on limb_shift (0-3).
    BEQ x5,x0 for ls0, then (ADDI x10,x0,k; BEQ x5,x10) for ls1-ls2,
    fall-through to ls3. 5 instructions total. -/
theorem shr_phase_c_spec (v5 v10 : Word) (base : Addr)
    (e0 e1 e2 e3 : Addr)
    (he0 : base + signExtend13 176 = e0)
    (he1 : (base + 8) + signExtend13 92 = e1)
    (he2 : (base + 16) + signExtend13 32 = e2)
    (he3 : base + 20 = e3) :
    let code :=
      CodeReq.union (CodeReq.singleton base (.BEQ .x5 .x0 176))
      (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x10 .x0 1))
      (CodeReq.union (CodeReq.singleton (base + 8) (.BEQ .x5 .x10 92))
      (CodeReq.union (CodeReq.singleton (base + 12) (.ADDI .x10 .x0 2))
      (CodeReq.singleton (base + 16) (.BEQ .x5 .x10 32)))))
    cpsNBranch base code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      [(e0, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10)),
       (e1, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 1))),
       (e2, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2))),
       (e3, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)))] := by
  -- Address arithmetic
  have ha1 : (base + 4 : Addr) + 8 = base + 12 := by bv_omega
  have ha2 : (base + 12 : Addr) + 8 = base + 20 := by bv_omega
  have hc1 : ((base + 4 : Addr) + 4) + signExtend13 92 = e1 := by rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]; exact he1
  have hc2 : ((base + 12 : Addr) + 4) + signExtend13 32 = e2 := by rw [show (base + 12 : Addr) + 4 = base + 16 from by bv_omega]; exact he2
  have hb1 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have hb2 : (base + 12 : Addr) + 4 = base + 16 := by bv_omega
  -- Step 0: BEQ x5 x0 176 at base
  have beq0_raw := beq_spec_gen .x5 .x0 176 v5 (0 : Word) base
  rw [he0] at beq0_raw
  have beq0 : cpsBranch base _
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)))
      e0 ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 4) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence _ _ _ _ e0 _ _ (base + 4) _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ (v5 = (0 : Word)) h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ (v5 ≠ (0 : Word)) h').1 hp').1) h hp)
      beq0_raw
  have beq0f := cpsBranch_frame_left _ _ _ _ _ _ _
    (.x10 ↦ᵣ v10)
    (by pcFree) beq0
  -- Step 1: cascade step at base+4 (ADDI x10,x0,1 + BEQ x5,x10,92)
  have cs1 := shr_cascade_step_spec v5 v10 1 92 (base + 4) e1 hc1
  rw [ha1, hb1] at cs1
  -- Step 2: cascade step at base+12 (ADDI x10,x0,2 + BEQ x5,x10,32)
  have cs2 := shr_cascade_step_spec v5 ((0 : Word) + signExtend12 1) 2 32 (base + 12) e2 hc2
  rw [ha2, hb2] at cs2
  -- Chain: fallthrough at base+20
  have ft := cpsNBranch_refl (base + 20)
    ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 2)))
    _ (fun _ hp => hp)
  have n3 := cpsBranch_cons_cpsNBranch_with_perm _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) cs2 ft
  have n2 := cpsBranch_cons_cpsNBranch_with_perm _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) cs1 n3
  have n1 := cpsBranch_cons_cpsNBranch_with_perm _ _ _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) beq0f n2
  -- Weaken precondition
  have n1' := cpsNBranch_weaken_pre _ _
    ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
    _ (fun h hp => by xperm_hyp hp) n1
  -- Weaken postconditions
  exact cpsNBranch_weaken_posts _ _ _ _ n1'
    (fun ex hmem => by
      simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false, false_or] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- e0 case
      · exact ⟨_, List.Mem.head _, rfl, fun h hp => by xperm_hyp hp⟩
      -- e1 case
      · exact ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, fun h hp => by xperm_hyp hp⟩
      -- e2 case
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl, fun h hp => by xperm_hyp hp⟩
      -- e3 case (base + 20 = e3)
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))), he3.symm, fun h hp => by xperm_hyp hp⟩)

-- ============================================================================
-- LD/OR accumulator helper (for phase A)
-- ============================================================================

/-- LD x10, off(x12); OR x5, x5, x10: load a value and OR-accumulate into x5. -/
theorem shr_ld_or_acc_spec (sp acc prev_x10 val : Word) (off : BitVec 12)
    (base : Addr)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let code :=
      CodeReq.union (CodeReq.singleton base (.LD .x10 .x12 off))
      (CodeReq.singleton (base + 4) (.OR .x5 .x5 .x10))
    cpsTriple base (base + 8) code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ acc) ** (.x10 ↦ᵣ prev_x10) ** ((sp + signExtend12 off) ↦ₘ val))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (acc ||| val)) ** (.x10 ↦ᵣ val) ** ((sp + signExtend12 off) ↦ₘ val)) := by
  runBlock

-- ============================================================================
-- Helper: weaken concrete regs to regOwn
-- ============================================================================

private theorem regIs_to_regOwn (r : Reg) (v : Word) : ∀ h, (r ↦ᵣ v) h → (regOwn r) h :=
  fun _ hp => ⟨v, hp⟩

/-- Helper: weaken two concrete regs to regOwn in a flat conjunction. -/
private theorem weaken_two_regs (P Q : Assertion) (r1 r2 : Reg) (v1 v2 : Word) :
    ∀ h, (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** Q) h →
         (P ** (regOwn r1) ** (regOwn r2) ** Q) h := by
  intro h hp
  exact sepConj_mono_right (sepConj_mono (regIs_to_regOwn r1 v1) (sepConj_mono_left (regIs_to_regOwn r2 v2))) h hp

/-- Helper: weaken one concrete reg to regOwn in a flat conjunction. -/
private theorem weaken_one_reg (P Q : Assertion) (r : Reg) (v : Word) :
    ∀ h, (P ** (r ↦ᵣ v) ** Q) h → (P ** (regOwn r) ** Q) h := by
  intro h hp
  exact sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn r v)) h hp

-- ============================================================================
-- Phase A spec: Check shift >= 256 (9 instructions)
-- ============================================================================

set_option maxHeartbeats 6400000 in
/-- Phase A spec: Check shift >= 256.
    LD x5, 8(x12); LD x10, 16(x12); OR x5, x5, x10;
    LD x10, 24(x12); OR x5, x5, x10;
    BNE x5, x0, 320;  -- high limbs nonzero → zero_path
    LD x5, 0(x12);
    SLTIU x10, x5, 256;
    BEQ x10, x0, 308   -- shift0 >= 256 → zero_path
    9 instructions, cpsBranch with 2 exits:
    - Taken (zero_path): shift >= 256, x5/x10 are regOwn (existential)
    - Not-taken (base+36): shift < 256, x5=s0, x10 is regOwn -/
theorem shr_phase_a_spec (sp r5 r10 : Word)
    (s0 s1 s2 s3 : Word)
    (base zero_path : Addr)
    (hzero : (base + 20) + signExtend13 320 = zero_path)
    (hzero2 : (base + 32) + signExtend13 308 = zero_path)
    (hvalid : ValidMemRange sp 8) :
    let code :=
      CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 8))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x10 .x12 16))
      (CodeReq.union (CodeReq.singleton (base + 8) (.OR .x5 .x5 .x10))
      (CodeReq.union (CodeReq.singleton (base + 12) (.LD .x10 .x12 24))
      (CodeReq.union (CodeReq.singleton (base + 16) (.OR .x5 .x5 .x10))
      (CodeReq.union (CodeReq.singleton (base + 20) (.BNE .x5 .x0 320))
      (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x5 .x12 0))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SLTIU .x10 .x5 256))
      (CodeReq.singleton (base + 32) (.BEQ .x10 .x0 308)))))))))
    cpsBranch base code
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
      zero_path
      ((.x12 ↦ᵣ sp) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
      (base + 36)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3)) := by
  -- Memory validity from ValidMemRange sp 4
  have hv0 : isValidDwordAccess sp = true := by
    have := hvalid.get (i := 0) (by omega); simpa using this
  have hv8 : isValidDwordAccess (sp + 8) = true := by
    have := hvalid.get (i := 1) (by omega); simpa using this
  have hv16 : isValidDwordAccess (sp + 16) = true := by
    have := hvalid.get (i := 2) (by omega); simpa using this
  have hv24 : isValidDwordAccess (sp + 24) = true := by
    have := hvalid.get (i := 3) (by omega); simpa using this
  -- Address arithmetic
  have ha4 : (base + 4 : Addr) + 4 = base + 8 := by bv_omega
  have ha20 : (base + 20 : Addr) + 4 = base + 24 := by bv_omega
  have ha24 : (base + 24 : Addr) + 4 = base + 28 := by bv_omega
  have ha28 : (base + 28 : Addr) + 4 = base + 32 := by bv_omega
  have ha32 : (base + 32 : Addr) + 4 = base + 36 := by bv_omega
  have he4  : (base + 4  : Addr) + 8 = base + 12 := by bv_omega
  have he12 : (base + 12 : Addr) + 8 = base + 20 := by bv_omega
  -- Step 1: LD x5 x12 8 at base (loads s1 into x5)
  have lw1 := ld_spec_gen .x5 .x12 sp r5 s1 8 base (by nofun)
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_8] at lw1
  have lw1f := cpsTriple_frame_left _ _ _ _ _
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
     (sp ↦ₘ s0) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) lw1
  -- Step 2: shr_ld_or_acc_spec at base+4 (LD x10 x12 16 + OR x5 x5 x10) → x5 = s1|s2
  have lor2 := shr_ld_or_acc_spec sp s1 r10 s2 16 (base + 4)
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_16] at lor2
  rw [ha4, he4] at lor2
  have lor2f := cpsTriple_frame_left _ _ _ _ _
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) lor2
  have c12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) lw1f lor2f; clear lw1 lw1f lor2 lor2f
  -- Step 3: shr_ld_or_acc_spec at base+12 (LD x10 x12 24 + OR) → x5 = s1|s2|s3
  have lor3 := shr_ld_or_acc_spec sp (s1 ||| s2) s2 s3 24 (base + 12)
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at lor3
  rw [show (base + 12 : Addr) + 4 = base + 16 from by bv_omega, he12] at lor3
  have lor3f := cpsTriple_frame_left _ _ _ _ _
    ((.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2))
    (by pcFree) lor3
  have c13 := cpsTriple_seq_with_perm _ _ _ _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c12 lor3f; clear c12 lor3 lor3f
  -- Step 4: BNE x5 x0 320 at base+20
  have bne_raw := bne_spec_gen .x5 .x0 320
    (s1 ||| s2 ||| s3) (0 : Word) (base + 20)
  rw [hzero, ha20] at bne_raw
  have bne1 : cpsBranch (base + 20) _
      ((.x5 ↦ᵣ (s1 ||| s2 ||| s3)) ** (.x0 ↦ᵣ (0 : Word)))
      zero_path ((.x5 ↦ᵣ (s1 ||| s2 ||| s3)) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 24) ((.x5 ↦ᵣ (s1 ||| s2 ||| s3)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence _ _ _ _ zero_path _ _ (base + 24) _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      bne_raw
  have bne1f := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ s3) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) bne1
  have br1 := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c13 bne1f; clear c13 bne_raw bne1 bne1f
  -- On the fall-through (base+24): LD x5 x12 0, SLTIU x10 x5 256, BEQ x10 x0 308
  -- Step 5: LD x5 x12 0 at base+24 (loads s0 into x5)
  have lw5 := ld_spec_gen .x5 .x12 sp
    (s1 ||| s2 ||| s3) s0 0 (base + 24) (by nofun)
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_omega]; exact hv0)
  simp only [signExtend12_0] at lw5
  rw [show sp + (0 : Word) = sp from by bv_omega] at lw5
  rw [ha24] at lw5
  have lw5f := cpsTriple_frame_left _ _ _ _ _
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ s3) **
     ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) lw5
  -- Step 6: SLTIU x10 x5 256 at base+28
  have sltiu_raw := sltiu_spec_gen .x10 .x5 s3 s0 256 (base + 28) (by nofun)
  rw [ha28] at sltiu_raw
  have sltiuf := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) sltiu_raw
  let sltiu_val := (if BitVec.ult s0 (signExtend12 (256 : BitVec 12)) then (1 : Word) else (0 : Word))
  have c56 := cpsTriple_seq_with_perm _ _ _ _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) lw5f sltiuf; clear lw5 lw5f sltiu_raw sltiuf
  -- Step 7: BEQ x10 x0 308 at base+32
  have beq_raw := beq_spec_gen .x10 .x0 308 sltiu_val (0 : Word) (base + 32)
  rw [hzero2, ha32] at beq_raw
  have beq1 : cpsBranch (base + 32) _
      ((.x10 ↦ᵣ sltiu_val) ** (.x0 ↦ᵣ (0 : Word)))
      zero_path ((.x10 ↦ᵣ sltiu_val) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 36) ((.x10 ↦ᵣ sltiu_val) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranch_consequence _ _ _ _ zero_path _ _ (base + 36) _ _
      (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1) h hp)
      beq_raw
  have beq1f := cpsBranch_frame_left _ _ _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
    (by pcFree) beq1
  have br2 := cpsTriple_seq_cpsBranch_with_perm _ _ _ _ _ _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) c56 beq1f; clear c56 beq_raw beq1 beq1f
  -- Combine br1 and br2
  have combined := cpsBranch_seq_cpsBranch_with_perm
    base (base + 24) zero_path (base + 36) _ _ _ _ _ _ _ _ _ _
    br1 (fun _ hp => by xperm_hyp hp) br2
    -- ht1: weaken first taken path (BNE taken: x5 = s1|||s2|||s3, x10 = s3)
    (fun h hp => by
      have hp' := (congrFun (show _ =
        ((.x5 ↦ᵣ (s1 ||| s2 ||| s3)) ** (.x10 ↦ᵣ s3) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
         (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
        from by xperm) h).mp hp
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h hp'
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ sp) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
        from by xperm) h).mp w1)
    -- ht2: weaken second taken path (BEQ taken: x5 = s0, x10 = sltiu_val)
    (fun h hp => by
      have hp' := (congrFun (show _ =
        ((.x5 ↦ᵣ s0) ** (.x10 ↦ᵣ sltiu_val) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
         (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
        from by xperm) h).mp hp
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h hp'
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ sp) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
        from by xperm) h).mp w1)
  -- Final: weaken the not-taken postcondition (x10 has sltiu_val, need regOwn)
  exact cpsBranch_consequence _ _ _ _ zero_path _ _ (base + 36) _ _
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => hp)
    (fun h hp => by
      have hp' := (congrFun (show _ =
        ((.x10 ↦ᵣ sltiu_val) **
         (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) **
         (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
        from by xperm) h).mp hp
      have w0 := sepConj_mono_left (regIs_to_regOwn .x10 _) h hp'
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3))
        from by xperm) h).mp w0)
    combined

-- ============================================================================
-- Shift body specs (4 bodies)
-- ============================================================================

abbrev shr_body_3_code (jal_off : BitVec 21) (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SRL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SD .x12 .x5 0))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x0 8))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SD .x12 .x0 16))
  (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x0 24))
  (CodeReq.singleton (base + 24) (.JAL .x0 jal_off)))))))

/-- Shift body 3: limb_shift=3.
    Result[0] = value[3] >>> bs, rest = 0.
    Comprises: shr_last_limb(0), 3x SD, JAL.
    7 instructions from base to exit (via JAL). -/
theorem shr_body_3_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 24) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 4) :
    let result0 := v3 >>> (bit_shift.toNat % 64)
    let code := shr_body_3_code jal_off base
    cpsTriple base exit code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 8) ↦ₘ v1) ** ((sp + 16) ↦ₘ v2) ** ((sp + 24) ↦ₘ v3))
      (-- Updated regs + mem
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result0) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 8) ↦ₘ 0) ** ((sp + 16) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0)) := by
  have LL := shr_last_limb_spec 0 sp v3 v0 v5 bit_shift base (by validMem) (by validMem)
  have S0 := sd_x0_spec_gen .x12 sp v1 8 (base + 12) (by validMem)
  have S1 := sd_x0_spec_gen .x12 sp v2 16 (base + 16) (by validMem)
  have S2 := sd_x0_spec_gen .x12 sp v3 24 (base + 20) (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 24)
  rw [hexit] at JL
  runBlock LL S0 S1 S2 JL

abbrev shr_body_2_code (jal_off : BitVec 21) (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 16))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SRL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x10 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SLL .x10 .x10 .x7))
  (CodeReq.union (CodeReq.singleton (base + 16) (.AND .x10 .x10 .x11))
  (CodeReq.union (CodeReq.singleton (base + 20) (.OR .x5 .x5 .x10))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SD .x12 .x5 0))
  (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x5 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 32) (.SRL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 36) (.SD .x12 .x5 8))
  (CodeReq.union (CodeReq.singleton (base + 40) (.SD .x12 .x0 16))
  (CodeReq.union (CodeReq.singleton (base + 44) (.SD .x12 .x0 24))
  (CodeReq.singleton (base + 48) (.JAL .x0 jal_off))))))))))))))

set_option maxHeartbeats 3200000 in
/-- Shift body 2: limb_shift=2.
    Result[0] = (value[2] >>> bs) ||| ((value[3] <<< as) &&& mask),
    Result[1] = value[3] >>> bs, rest = 0.
    Comprises: shr_merge_limb(16,24,0), shr_last_limb(8), 2x SD, JAL.
    13 instructions from base to exit (via JAL). -/
theorem shr_body_2_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 48) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 4) :
    let result0 := (v2 >>> (bit_shift.toNat % 64)) ||| ((v3 <<< (anti_shift.toNat % 64)) &&& mask)
    let result1 := v3 >>> (bit_shift.toNat % 64)
    let code := shr_body_2_code jal_off base
    cpsTriple base exit code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 8) ↦ₘ v1) ** ((sp + 16) ↦ₘ v2) ** ((sp + 24) ↦ₘ v3))
      (-- Updated regs + mem
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result1) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v3 <<< (anti_shift.toNat % 64)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 8) ↦ₘ result1) ** ((sp + 16) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0)) := by
  have MM := shr_merge_limb_spec 16 24 0 sp v2 v3 v0 v5 v10 bit_shift anti_shift mask base (by validMem) (by validMem) (by validMem)
  have LL := shr_last_limb_spec 8 sp v3 v1
    ((v2 >>> (bit_shift.toNat % 64)) ||| ((v3 <<< (anti_shift.toNat % 64)) &&& mask))
    bit_shift (base + 28) (by validMem) (by validMem)
  have S0 := sd_x0_spec_gen .x12 sp v2 16 (base + 40) (by validMem)
  have S1 := sd_x0_spec_gen .x12 sp v3 24 (base + 44) (by validMem)
  have JL := jal_x0_spec_gen jal_off (base + 48)
  rw [hexit] at JL
  runBlock MM LL S0 S1 JL

abbrev shr_body_1_code (jal_off : BitVec 21) (base : Addr) : CodeReq :=
  -- merge_limb(8,16,0): 7 instructions at base..base+24
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 8))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SRL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x10 .x12 16))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SLL .x10 .x10 .x7))
  (CodeReq.union (CodeReq.singleton (base + 16) (.AND .x10 .x10 .x11))
  (CodeReq.union (CodeReq.singleton (base + 20) (.OR .x5 .x5 .x10))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SD .x12 .x5 0))
  -- merge_limb(16,24,8): 7 instructions at base+28..base+52
  (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x5 .x12 16))
  (CodeReq.union (CodeReq.singleton (base + 32) (.SRL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 36) (.LD .x10 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 40) (.SLL .x10 .x10 .x7))
  (CodeReq.union (CodeReq.singleton (base + 44) (.AND .x10 .x10 .x11))
  (CodeReq.union (CodeReq.singleton (base + 48) (.OR .x5 .x5 .x10))
  (CodeReq.union (CodeReq.singleton (base + 52) (.SD .x12 .x5 8))
  -- last_limb(16): 3 instructions at base+56..base+64
  (CodeReq.union (CodeReq.singleton (base + 56) (.LD .x5 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 60) (.SRL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 64) (.SD .x12 .x5 16))
  -- SD + JAL: 2 instructions at base+68..base+72
  (CodeReq.union (CodeReq.singleton (base + 68) (.SD .x12 .x0 24))
  (CodeReq.singleton (base + 72) (.JAL .x0 jal_off))))))))))))))))))))

set_option maxHeartbeats 3200000 in
/-- Shift body 1: limb_shift=1.
    Result[0] = merge(value[1],value[2]),
    Result[1] = merge(value[2],value[3]),
    Result[2] = value[3] >>> bs, rest = 0.
    Comprises: shr_merge_limb(8,16,0), shr_merge_limb(16,24,8),
    shr_last_limb(16), SD, JAL.
    19 instructions from base to exit (via JAL). -/
theorem shr_body_1_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 72) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 4) :
    let result0 := (v1 >>> (bit_shift.toNat % 64)) ||| ((v2 <<< (anti_shift.toNat % 64)) &&& mask)
    let result1 := (v2 >>> (bit_shift.toNat % 64)) ||| ((v3 <<< (anti_shift.toNat % 64)) &&& mask)
    let result2 := v3 >>> (bit_shift.toNat % 64)
    let code := shr_body_1_code jal_off base
    cpsTriple base exit code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 8) ↦ₘ v1) ** ((sp + 16) ↦ₘ v2) ** ((sp + 24) ↦ₘ v3))
      (-- Updated regs + mem
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result2) ** (.x6 ↦ᵣ bit_shift) **
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
  have JL := jal_x0_spec_gen jal_off (base + 72)
  rw [hexit] at JL
  runBlock MM1 MM2 LL S0 JL

abbrev shr_body_0_code (jal_off : BitVec 21) (base : Addr) : CodeReq :=
  -- merge_limb_inplace(0,8): 7 instructions at base..base+24
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 0))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SRL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x10 .x12 8))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SLL .x10 .x10 .x7))
  (CodeReq.union (CodeReq.singleton (base + 16) (.AND .x10 .x10 .x11))
  (CodeReq.union (CodeReq.singleton (base + 20) (.OR .x5 .x5 .x10))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SD .x12 .x5 0))
  -- merge_limb_inplace(8,16): 7 instructions at base+28..base+52
  (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x5 .x12 8))
  (CodeReq.union (CodeReq.singleton (base + 32) (.SRL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 36) (.LD .x10 .x12 16))
  (CodeReq.union (CodeReq.singleton (base + 40) (.SLL .x10 .x10 .x7))
  (CodeReq.union (CodeReq.singleton (base + 44) (.AND .x10 .x10 .x11))
  (CodeReq.union (CodeReq.singleton (base + 48) (.OR .x5 .x5 .x10))
  (CodeReq.union (CodeReq.singleton (base + 52) (.SD .x12 .x5 8))
  -- merge_limb_inplace(16,24): 7 instructions at base+56..base+80
  (CodeReq.union (CodeReq.singleton (base + 56) (.LD .x5 .x12 16))
  (CodeReq.union (CodeReq.singleton (base + 60) (.SRL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 64) (.LD .x10 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 68) (.SLL .x10 .x10 .x7))
  (CodeReq.union (CodeReq.singleton (base + 72) (.AND .x10 .x10 .x11))
  (CodeReq.union (CodeReq.singleton (base + 76) (.OR .x5 .x5 .x10))
  (CodeReq.union (CodeReq.singleton (base + 80) (.SD .x12 .x5 16))
  -- last_limb_inplace: 3 instructions at base+84..base+92
  (CodeReq.union (CodeReq.singleton (base + 84) (.LD .x5 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 88) (.SRL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 92) (.SD .x12 .x5 24))
  -- JAL at base+96
  (CodeReq.singleton (base + 96) (.JAL .x0 jal_off))))))))))))))))))))))))))

set_option maxHeartbeats 3200000 in
/-- Shift body 0: limb_shift=0.
    Result[i] = merge(value[i], value[i+1]) for i=0..2,
    Result[3] = value[3] >>> bs.
    Comprises: 3x shr_merge_limb_inplace + shr_last_limb_inplace + JAL.
    25 instructions from base to exit (via JAL). -/
theorem shr_body_0_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 96) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 4) :
    let result0 := (v0 >>> (bit_shift.toNat % 64)) ||| ((v1 <<< (anti_shift.toNat % 64)) &&& mask)
    let result1 := (v1 >>> (bit_shift.toNat % 64)) ||| ((v2 <<< (anti_shift.toNat % 64)) &&& mask)
    let result2 := (v2 >>> (bit_shift.toNat % 64)) ||| ((v3 <<< (anti_shift.toNat % 64)) &&& mask)
    let result3 := v3 >>> (bit_shift.toNat % 64)
    let code := shr_body_0_code jal_off base
    cpsTriple base exit code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 8) ↦ₘ v1) ** ((sp + 16) ↦ₘ v2) ** ((sp + 24) ↦ₘ v3))
      (-- Updated regs + mem
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result3) ** (.x6 ↦ᵣ bit_shift) **
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
  have JL := jal_x0_spec_gen jal_off (base + 96)
  rw [hexit] at JL
  runBlock MM1 MM2 MM3 LL JL

end EvmAsm.Rv64
