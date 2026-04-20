/-
  EvmAsm.Evm64.Shift.ShlSpec

  CPS specifications for the 256-bit EVM SHL (logical shift left) program (64-bit).
  Mirrors ShiftSpec.lean with SLL/SRL swapped and limbs processed top-down.
  Modular decomposition:
  - Per-limb helpers: shl_merge_limb_spec (7 instrs), shl_first_limb_spec (3 instrs)
  - Shift bodies: shl_body_L_spec for L = 0..3
  - Reuses SHR phase A/B/C/zero_path specs from ShiftSpec.lean
-/

import EvmAsm.Evm64.Shift.LimbSpec

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Per-limb Specs: SHL Merge Limb (7 instructions)
-- ============================================================================

abbrev shl_merge_limb_code (base : Word) (src_off prev_off dst_off : BitVec 12) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 src_off))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SLL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x10 .x12 prev_off))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SRL .x10 .x10 .x7))
  (CodeReq.union (CodeReq.singleton (base + 16) (.AND .x10 .x10 .x11))
  (CodeReq.union (CodeReq.singleton (base + 20) (.OR .x5 .x5 .x10))
   (CodeReq.singleton (base + 24) (.SD .x12 .x5 dst_off)))))))

/-- SHL merge limb spec (7 instructions):
    LD x5, src_off(x12); SLL x5,x5,x6; LD x10, prev_off(x12);
    SRL x10,x10,x7; AND x10,x10,x11; OR x5,x5,x10; SD x12,x5,dst_off

    Computes: result = (src <<< bit_shift) ||| ((prev >>> antiShift) &&& mask)
    Mirror of shr_merge_limb_spec with SLL/SRL swapped. -/
theorem shl_merge_limb_spec (src_off prev_off dst_off : BitVec 12)
    (sp src prev dstOld v5 v10 bit_shift antiShift mask : Word) (base : Word) :
    let memSrc := sp + signExtend12 src_off
    let memPrev := sp + signExtend12 prev_off
    let memDst := sp + signExtend12 dst_off
    let shiftedSrc := src <<< (bit_shift.toNat % 64)
    let shiftedPrev := (prev >>> (antiShift.toNat % 64)) &&& mask
    let result := shiftedSrc ||| shiftedPrev
    let cr := shl_merge_limb_code base src_off prev_off dst_off
    cpsTriple base (base + 28) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ antiShift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (memSrc ↦ₘ src) ** (memPrev ↦ₘ prev) ** (memDst ↦ₘ dstOld))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ antiShift) ** (.x10 ↦ᵣ shiftedPrev) ** (.x11 ↦ᵣ mask) **
       (memSrc ↦ₘ src) ** (memPrev ↦ₘ prev) ** (memDst ↦ₘ result)) := by
  have L1 := ld_spec_gen .x5 .x12 sp v5 src src_off base (by nofun)
  have SL := sll_spec_gen_rd_eq_rs1 .x5 .x6 src bit_shift (base + 4) (by nofun)
  have L2 := ld_spec_gen .x10 .x12 sp v10 prev prev_off (base + 8) (by nofun)
  have SR := srl_spec_gen_rd_eq_rs1 .x10 .x7 prev antiShift (base + 12) (by nofun)
  have AN := and_spec_gen_rd_eq_rs1 .x10 .x11 (prev >>> (antiShift.toNat % 64)) mask (base + 16) (by nofun)
  have OR_ := or_spec_gen_rd_eq_rs1 .x5 .x10 (src <<< (bit_shift.toNat % 64)) ((prev >>> (antiShift.toNat % 64)) &&& mask) (base + 20) (by nofun)
  have SD_ := sd_spec_gen .x12 .x5 sp ((src <<< (bit_shift.toNat % 64)) ||| ((prev >>> (antiShift.toNat % 64)) &&& mask)) dstOld dst_off (base + 24)
  runBlock L1 SL L2 SR AN OR_ SD_

-- ============================================================================
-- Per-limb Specs: SHL First Limb (3 instructions)
-- ============================================================================

abbrev shl_first_limb_code (base : Word) (dst_off : BitVec 12) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 0))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SLL .x5 .x5 .x6))
   (CodeReq.singleton (base + 8) (.SD .x12 .x5 dst_off)))

/-- SHL first limb spec (3 instructions):
    LD x5, 0(x12); SLL x5,x5,x6; SD x12,x5,dst_off

    Computes: result = value[0] <<< bit_shift
    Mirror of shr_last_limb_spec: reads from offset 0 (lowest limb), uses SLL. -/
theorem shl_first_limb_spec (dst_off : BitVec 12)
    (sp src dstOld v5 bit_shift : Word) (base : Word) :
    let memSrc := sp + signExtend12 (0 : BitVec 12)
    let memDst := sp + signExtend12 dst_off
    let result := src <<< (bit_shift.toNat % 64)
    let cr := shl_first_limb_code base dst_off
    cpsTriple base (base + 12) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (memSrc ↦ₘ src) ** (memDst ↦ₘ dstOld))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (memSrc ↦ₘ src) ** (memDst ↦ₘ result)) := by
  have L := ld_spec_gen .x5 .x12 sp v5 src 0 base (by nofun)
  have SL := sll_spec_gen_rd_eq_rs1 .x5 .x6 src bit_shift (base + 4) (by nofun)
  have SD_ := sd_spec_gen .x12 .x5 sp (src <<< (bit_shift.toNat % 64)) dstOld dst_off (base + 8)
  runBlock L SL SD_

-- ============================================================================
-- Per-limb Specs: SHL Merge Limb In-place (7 instructions, src_off = dst_off)
-- ============================================================================

abbrev shl_merge_limb_inplace_code (base : Word) (off prev_off : BitVec 12) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 off))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SLL .x5 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x10 .x12 prev_off))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SRL .x10 .x10 .x7))
  (CodeReq.union (CodeReq.singleton (base + 16) (.AND .x10 .x10 .x11))
  (CodeReq.union (CodeReq.singleton (base + 20) (.OR .x5 .x5 .x10))
   (CodeReq.singleton (base + 24) (.SD .x12 .x5 off)))))))

/-- SHL merge limb in-place spec (7 instructions):
    Same as shl_merge_limb_spec but src_off = dst_off. -/
theorem shl_merge_limb_inplace_spec (off prev_off : BitVec 12)
    (sp src prev v5 v10 bit_shift antiShift mask : Word) (base : Word) :
    let memLoc := sp + signExtend12 off
    let memPrev := sp + signExtend12 prev_off
    let shiftedSrc := src <<< (bit_shift.toNat % 64)
    let shiftedPrev := (prev >>> (antiShift.toNat % 64)) &&& mask
    let result := shiftedSrc ||| shiftedPrev
    let cr := shl_merge_limb_inplace_code base off prev_off
    cpsTriple base (base + 28) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ antiShift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (memLoc ↦ₘ src) ** (memPrev ↦ₘ prev))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ antiShift) ** (.x10 ↦ᵣ shiftedPrev) ** (.x11 ↦ᵣ mask) **
       (memLoc ↦ₘ result) ** (memPrev ↦ₘ prev)) := by
  have L1 := ld_spec_gen .x5 .x12 sp v5 src off base (by nofun)
  have SL := sll_spec_gen_rd_eq_rs1 .x5 .x6 src bit_shift (base + 4) (by nofun)
  have L2 := ld_spec_gen .x10 .x12 sp v10 prev prev_off (base + 8) (by nofun)
  have SR := srl_spec_gen_rd_eq_rs1 .x10 .x7 prev antiShift (base + 12) (by nofun)
  have AN := and_spec_gen_rd_eq_rs1 .x10 .x11 (prev >>> (antiShift.toNat % 64)) mask (base + 16) (by nofun)
  have OR_ := or_spec_gen_rd_eq_rs1 .x5 .x10 (src <<< (bit_shift.toNat % 64)) ((prev >>> (antiShift.toNat % 64)) &&& mask) (base + 20) (by nofun)
  have SD_ := sd_spec_gen .x12 .x5 sp ((src <<< (bit_shift.toNat % 64)) ||| ((prev >>> (antiShift.toNat % 64)) &&& mask)) src off (base + 24)
  runBlock L1 SL L2 SR AN OR_ SD_

-- ============================================================================
-- Per-limb Specs: SHL First Limb In-place (3 instructions, dst_off = 0)
-- ============================================================================

abbrev shl_first_limb_inplace_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 0))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SLL .x5 .x5 .x6))
   (CodeReq.singleton (base + 8) (.SD .x12 .x5 0)))

/-- SHL first limb in-place spec (3 instructions):
    LD x5, 0(x12); SLL x5,x5,x6; SD x12,x5,0
    Reads and writes the same memory cell at sp+0. -/
theorem shl_first_limb_inplace_spec
    (sp src v5 bit_shift : Word) (base : Word) :
    let mem := sp + signExtend12 (0 : BitVec 12)
    let result := src <<< (bit_shift.toNat % 64)
    let cr := shl_first_limb_inplace_code base
    cpsTriple base (base + 12) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ src))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ result)) := by
  have L := ld_spec_gen .x5 .x12 sp v5 src 0 base (by nofun)
  have SL := sll_spec_gen_rd_eq_rs1 .x5 .x6 src bit_shift (base + 4) (by nofun)
  have SD_ := sd_spec_gen .x12 .x5 sp (src <<< (bit_shift.toNat % 64)) src 0 (base + 8)
  runBlock L SL SD_

-- ============================================================================
-- Shift Body Specs
-- ============================================================================

abbrev shl_body_3_code (base : Word) (jal_off : BitVec 21) : CodeReq :=
  CodeReq.ofProg base (shl_body_3_prog jal_off)

/-- Shift body 3: limb_shift=3.
    Result[3] = value[0] <<< bs, rest = 0.
    Comprises: shl_first_limb(24), 3x SD, JAL.
    7 instructions from base to exit (via JAL). -/
theorem shl_body_3_spec (sp : Word)
    (v5 v10 bit_shift antiShift mask : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Word) (jal_off : BitVec 21)
    (hexit : (base + 24) + signExtend21 jal_off = exit) :
    let result3 := v0 <<< (bit_shift.toNat % 64)
    let cr := shl_body_3_code base jal_off
    cpsTriple base exit cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ antiShift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 8) ↦ₘ v1) ** ((sp + 16) ↦ₘ v2) ** ((sp + 24) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result3) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ antiShift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ 0) ** ((sp + 8) ↦ₘ 0) ** ((sp + 16) ↦ₘ 0) ** ((sp + 24) ↦ₘ result3)) := by
  have FL := shl_first_limb_spec 24 sp v0 v3 v5 bit_shift base
  have S0 := sd_x0_spec_gen .x12 sp v2 16 (base + 12)
  have S1 := sd_x0_spec_gen .x12 sp v1 8 (base + 16)
  have S2 := sd_x0_spec_gen .x12 sp v0 0 (base + 20)
  have JL := jal_x0_spec_gen jal_off (base + 24)
  rw [hexit] at JL
  runBlock FL S0 S1 S2 JL

abbrev shl_body_2_code (base : Word) (jal_off : BitVec 21) : CodeReq :=
  CodeReq.ofProg base (shl_body_2_prog jal_off)

/-- Shift body 2: limb_shift=2.
    Result[3] = (value[1] <<< bs) ||| ((value[0] >>> as) &&& mask),
    Result[2] = value[0] <<< bs, rest = 0.
    Comprises: shl_merge_limb(8,0,24), shl_first_limb(16), 2x SD, JAL.
    13 instructions from base to exit (via JAL). -/
theorem shl_body_2_spec (sp : Word)
    (v5 v10 bit_shift antiShift mask : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Word) (jal_off : BitVec 21)
    (hexit : (base + 48) + signExtend21 jal_off = exit) :
    let result3 := (v1 <<< (bit_shift.toNat % 64)) ||| ((v0 >>> (antiShift.toNat % 64)) &&& mask)
    let result2 := v0 <<< (bit_shift.toNat % 64)
    let cr := shl_body_2_code base jal_off
    cpsTriple base exit cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ antiShift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 8) ↦ₘ v1) ** ((sp + 16) ↦ₘ v2) ** ((sp + 24) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result2) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ antiShift) ** (.x10 ↦ᵣ ((v0 >>> (antiShift.toNat % 64)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ 0) ** ((sp + 8) ↦ₘ 0) ** ((sp + 16) ↦ₘ result2) ** ((sp + 24) ↦ₘ result3)) := by
  have MM := shl_merge_limb_spec 8 0 24 sp v1 v0 v3 v5 v10 bit_shift antiShift mask base
  have FL := shl_first_limb_spec 16 sp v0 v2
    ((v1 <<< (bit_shift.toNat % 64)) ||| ((v0 >>> (antiShift.toNat % 64)) &&& mask))
    bit_shift (base + 28)
  have S0 := sd_x0_spec_gen .x12 sp v1 8 (base + 40)
  have S1 := sd_x0_spec_gen .x12 sp v0 0 (base + 44)
  have JL := jal_x0_spec_gen jal_off (base + 48)
  rw [hexit] at JL
  runBlock MM FL S0 S1 JL

abbrev shl_body_1_code (base : Word) (jal_off : BitVec 21) : CodeReq :=
  CodeReq.ofProg base (shl_body_1_prog jal_off)

/-- Shift body 1: limb_shift=1.
    Result[3] = merge(value[2],value[1]),
    Result[2] = merge(value[1],value[0]),
    Result[1] = value[0] <<< bs, rest = 0.
    Comprises: shl_merge_limb(16,8,24), shl_merge_limb(8,0,16),
    shl_first_limb(8), SD, JAL.
    19 instructions from base to exit (via JAL). -/
theorem shl_body_1_spec (sp : Word)
    (v5 v10 bit_shift antiShift mask : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Word) (jal_off : BitVec 21)
    (hexit : (base + 72) + signExtend21 jal_off = exit) :
    let result3 := (v2 <<< (bit_shift.toNat % 64)) ||| ((v1 >>> (antiShift.toNat % 64)) &&& mask)
    let result2 := (v1 <<< (bit_shift.toNat % 64)) ||| ((v0 >>> (antiShift.toNat % 64)) &&& mask)
    let result1 := v0 <<< (bit_shift.toNat % 64)
    let cr := shl_body_1_code base jal_off
    cpsTriple base exit cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ antiShift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 8) ↦ₘ v1) ** ((sp + 16) ↦ₘ v2) ** ((sp + 24) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result1) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ antiShift) ** (.x10 ↦ᵣ ((v0 >>> (antiShift.toNat % 64)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ 0) ** ((sp + 8) ↦ₘ result1) ** ((sp + 16) ↦ₘ result2) ** ((sp + 24) ↦ₘ result3)) := by
  have MM1 := shl_merge_limb_spec 16 8 24 sp v2 v1 v3 v5 v10 bit_shift antiShift mask base
  have MM2 := shl_merge_limb_spec 8 0 16 sp v1 v0 v2
    ((v2 <<< (bit_shift.toNat % 64)) ||| ((v1 >>> (antiShift.toNat % 64)) &&& mask))
    ((v1 >>> (antiShift.toNat % 64)) &&& mask)
    bit_shift antiShift mask (base + 28)
  have FL := shl_first_limb_spec 8 sp v0 v1
    ((v1 <<< (bit_shift.toNat % 64)) ||| ((v0 >>> (antiShift.toNat % 64)) &&& mask))
    bit_shift (base + 56)
  have S0 := sd_x0_spec_gen .x12 sp v0 0 (base + 68)
  have JL := jal_x0_spec_gen jal_off (base + 72)
  rw [hexit] at JL
  runBlock MM1 MM2 FL S0 JL

abbrev shl_body_0_code (base : Word) (jal_off : BitVec 21) : CodeReq :=
  CodeReq.ofProg base (shl_body_0_prog jal_off)

/-- Shift body 0: limb_shift=0.
    Result[i] = merge(value[i], value[i-1]) for i=3..1,
    Result[0] = value[0] <<< bs.
    Comprises: 3x shl_merge_limb_inplace + shl_first_limb_inplace + JAL.
    25 instructions from base to exit (via JAL). -/
theorem shl_body_0_spec (sp : Word)
    (v5 v10 bit_shift antiShift mask : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Word) (jal_off : BitVec 21)
    (hexit : (base + 96) + signExtend21 jal_off = exit) :
    let result3 := (v3 <<< (bit_shift.toNat % 64)) ||| ((v2 >>> (antiShift.toNat % 64)) &&& mask)
    let result2 := (v2 <<< (bit_shift.toNat % 64)) ||| ((v1 >>> (antiShift.toNat % 64)) &&& mask)
    let result1 := (v1 <<< (bit_shift.toNat % 64)) ||| ((v0 >>> (antiShift.toNat % 64)) &&& mask)
    let result0 := v0 <<< (bit_shift.toNat % 64)
    let cr := shl_body_0_code base jal_off
    cpsTriple base exit cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ antiShift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 8) ↦ₘ v1) ** ((sp + 16) ↦ₘ v2) ** ((sp + 24) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result0) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ antiShift) ** (.x10 ↦ᵣ ((v0 >>> (antiShift.toNat % 64)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 8) ↦ₘ result1) ** ((sp + 16) ↦ₘ result2) ** ((sp + 24) ↦ₘ result3)) := by
  have MM1 := shl_merge_limb_inplace_spec 24 16 sp v3 v2 v5 v10 bit_shift antiShift mask base
  have MM2 := shl_merge_limb_inplace_spec 16 8 sp v2 v1
    ((v3 <<< (bit_shift.toNat % 64)) ||| ((v2 >>> (antiShift.toNat % 64)) &&& mask))
    ((v2 >>> (antiShift.toNat % 64)) &&& mask)
    bit_shift antiShift mask (base + 28)
  have MM3 := shl_merge_limb_inplace_spec 8 0 sp v1 v0
    ((v2 <<< (bit_shift.toNat % 64)) ||| ((v1 >>> (antiShift.toNat % 64)) &&& mask))
    ((v1 >>> (antiShift.toNat % 64)) &&& mask)
    bit_shift antiShift mask (base + 56)
  have FL := shl_first_limb_inplace_spec sp v0
    ((v1 <<< (bit_shift.toNat % 64)) ||| ((v0 >>> (antiShift.toNat % 64)) &&& mask))
    bit_shift (base + 84)
  have JL := jal_x0_spec_gen jal_off (base + 96)
  rw [hexit] at JL
  runBlock MM1 MM2 MM3 FL JL

end EvmAsm.Evm64
