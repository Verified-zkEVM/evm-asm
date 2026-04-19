/-
  EvmAsm.Evm64.Shift.SarSpec

  CPS specifications for the 256-bit EVM SAR (arithmetic shift right) program (64-bit).
  Like SHR but fills vacated bits with sign extension (MSB of value).
  Modular decomposition:
  - Per-limb helpers: sar_last_limb_spec (3 instrs), reuses shr_merge_limb_spec
  - Shift bodies: sar_body_L_spec for L = 0..3
  - Sign-fill path: sar_sign_fill_path_spec (7 instrs)
  - Reuses SHR phase A/B/C specs from ShiftSpec.lean (with different offsets)
-/

import EvmAsm.Evm64.Shift.LimbSpec
import EvmAsm.Rv64.AddrNorm

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (bv6_toNat_63)

-- ============================================================================
-- Per-limb Specs: SAR Last Limb (3 instructions)
-- ============================================================================

abbrev sar_last_limb_code (base : Word) (dst_off : BitVec 12) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SRA .x5 .x5 .x6))
   (CodeReq.singleton (base + 8) (.SD .x12 .x5 dst_off)))

/-- SAR last limb spec (3 instructions):
    LD x5, 24(x12); SRA x5,x5,x6; SD x12,x5,dst_off

    Computes: result = BitVec.sshiftRight value[3] bit_shift
    Mirror of shr_last_limb_spec with SRA (arithmetic shift right). -/
theorem sar_last_limb_spec (dst_off : BitVec 12)
    (sp src dst_old v5 bit_shift : Word) (base : Word) :
    let memSrc := sp + signExtend12 (24 : BitVec 12)
    let memDst := sp + signExtend12 dst_off
    let result := BitVec.sshiftRight src (bit_shift.toNat % 64)
    let cr := sar_last_limb_code base dst_off
    cpsTriple base (base + 12) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (memSrc ↦ₘ src) ** (memDst ↦ₘ dst_old))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (memSrc ↦ₘ src) ** (memDst ↦ₘ result)) := by
  have L := ld_spec_gen .x5 .x12 sp v5 src 24 base (by nofun)
  have SA := sra_spec_gen_rd_eq_rs1 .x5 .x6 src bit_shift (base + 4) (by nofun)
  have SD_ := sd_spec_gen .x12 .x5 sp (BitVec.sshiftRight src (bit_shift.toNat % 64)) dst_old dst_off (base + 8)
  runBlock L SA SD_

-- ============================================================================
-- Per-limb Specs: SAR Last Limb In-place (3 instructions, dst_off = 24)
-- ============================================================================

abbrev sar_last_limb_inplace_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SRA .x5 .x5 .x6))
   (CodeReq.singleton (base + 8) (.SD .x12 .x5 24)))

/-- SAR last limb in-place spec (3 instructions):
    LD x5, 24(x12); SRA x5,x5,x6; SD x12,x5,24
    Reads and writes the same memory cell at sp+24. -/
theorem sar_last_limb_inplace_spec
    (sp src v5 bit_shift : Word) (base : Word) :
    let mem := sp + signExtend12 (24 : BitVec 12)
    let result := BitVec.sshiftRight src (bit_shift.toNat % 64)
    let cr := sar_last_limb_inplace_code base
    cpsTriple base (base + 12) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ src))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ result)) := by
  have L := ld_spec_gen .x5 .x12 sp v5 src 24 base (by nofun)
  have SA := sra_spec_gen_rd_eq_rs1 .x5 .x6 src bit_shift (base + 4) (by nofun)
  have SD_ := sd_spec_gen .x12 .x5 sp (BitVec.sshiftRight src (bit_shift.toNat % 64)) src 24 (base + 8)
  runBlock L SA SD_

-- ============================================================================
-- Shift Body Specs
-- ============================================================================

abbrev sar_body_3_code (base : Word) (jal_off : BitVec 21) : CodeReq :=
  CodeReq.ofProg base (sar_body_3_prog jal_off)

/-- SAR body 3: limb_shift=3 (8 instructions).
    result[0] = value[3] SRA bs; result[1..3] = signExt.
    Comprises: sar_last_limb(0), SRAI, 3x SD, JAL. -/
theorem sar_body_3_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Word) (jal_off : BitVec 21)
    (hexit : (base + 28) + signExtend21 jal_off = exit) :
    let result0 := BitVec.sshiftRight v3 (bit_shift.toNat % 64)
    let signExt := BitVec.sshiftRight result0 63
    let cr := sar_body_3_code base jal_off
    cpsTriple base exit cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 8) ↦ₘ v1) ** ((sp + 16) ↦ₘ v2) ** ((sp + 24) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result0) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ signExt) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 8) ↦ₘ signExt) ** ((sp + 16) ↦ₘ signExt) ** ((sp + 24) ↦ₘ signExt)) := by
  have h63 := bv6_toNat_63
  have LL := sar_last_limb_spec 0 sp v3 v0 v5 bit_shift base
  have SR := srai_spec_gen .x10 .x5 v10 (BitVec.sshiftRight v3 (bit_shift.toNat % 64)) 63 (base + 12) (by nofun)
  simp only [h63] at SR
  have S0 := sd_spec_gen .x12 .x10 sp (BitVec.sshiftRight (BitVec.sshiftRight v3 (bit_shift.toNat % 64)) 63) v1 8 (base + 16)
  have S1 := sd_spec_gen .x12 .x10 sp (BitVec.sshiftRight (BitVec.sshiftRight v3 (bit_shift.toNat % 64)) 63) v2 16 (base + 20)
  have S2 := sd_spec_gen .x12 .x10 sp (BitVec.sshiftRight (BitVec.sshiftRight v3 (bit_shift.toNat % 64)) 63) v3 24 (base + 24)
  have JL := jal_x0_spec_gen jal_off (base + 28)
  rw [hexit] at JL
  runBlock LL SR S0 S1 S2 JL

abbrev sar_body_2_code (base : Word) (jal_off : BitVec 21) : CodeReq :=
  CodeReq.ofProg base (sar_body_2_prog jal_off)

/-- SAR body 2: limb_shift=2 (14 instructions).
    result[0] = merge(value[2],value[3]); result[1] = value[3] SRA bs;
    result[2..3] = signExt.
    Comprises: shr_merge_limb(16,24,0), sar_last_limb(8), SRAI, 2x SD, JAL. -/
theorem sar_body_2_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Word) (jal_off : BitVec 21)
    (hexit : (base + 52) + signExtend21 jal_off = exit) :
    let result0 := (v2 >>> (bit_shift.toNat % 64)) ||| ((v3 <<< (anti_shift.toNat % 64)) &&& mask)
    let result1 := BitVec.sshiftRight v3 (bit_shift.toNat % 64)
    let signExt := BitVec.sshiftRight result1 63
    let cr := sar_body_2_code base jal_off
    cpsTriple base exit cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 8) ↦ₘ v1) ** ((sp + 16) ↦ₘ v2) ** ((sp + 24) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result1) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ signExt) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 8) ↦ₘ result1) ** ((sp + 16) ↦ₘ signExt) ** ((sp + 24) ↦ₘ signExt)) := by
  have h63 := bv6_toNat_63
  have MM := shr_merge_limb_spec 16 24 0 sp v2 v3 v0 v5 v10 bit_shift anti_shift mask base
  have LL := sar_last_limb_spec 8 sp v3 v1
    ((v2 >>> (bit_shift.toNat % 64)) ||| ((v3 <<< (anti_shift.toNat % 64)) &&& mask))
    bit_shift (base + 28)
  have SR := srai_spec_gen .x10 .x5
    ((v3 <<< (anti_shift.toNat % 64)) &&& mask)
    (BitVec.sshiftRight v3 (bit_shift.toNat % 64)) 63 (base + 40) (by nofun)
  simp only [h63] at SR
  have S0 := sd_spec_gen .x12 .x10 sp
    (BitVec.sshiftRight (BitVec.sshiftRight v3 (bit_shift.toNat % 64)) 63) v2 16 (base + 44)
  have S1 := sd_spec_gen .x12 .x10 sp
    (BitVec.sshiftRight (BitVec.sshiftRight v3 (bit_shift.toNat % 64)) 63) v3 24 (base + 48)
  have JL := jal_x0_spec_gen jal_off (base + 52)
  rw [hexit] at JL
  runBlock MM LL SR S0 S1 JL

abbrev sar_body_1_code (base : Word) (jal_off : BitVec 21) : CodeReq :=
  CodeReq.ofProg base (sar_body_1_prog jal_off)

/-- SAR body 1: limb_shift=1 (20 instructions).
    result[0] = merge(value[1],value[2]); result[1] = merge(value[2],value[3]);
    result[2] = value[3] SRA bs; result[3] = signExt.
    Comprises: 2x shr_merge_limb, sar_last_limb(16), SRAI, SD, JAL. -/
theorem sar_body_1_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Word) (jal_off : BitVec 21)
    (hexit : (base + 76) + signExtend21 jal_off = exit) :
    let result0 := (v1 >>> (bit_shift.toNat % 64)) ||| ((v2 <<< (anti_shift.toNat % 64)) &&& mask)
    let result1 := (v2 >>> (bit_shift.toNat % 64)) ||| ((v3 <<< (anti_shift.toNat % 64)) &&& mask)
    let result2 := BitVec.sshiftRight v3 (bit_shift.toNat % 64)
    let signExt := BitVec.sshiftRight result2 63
    let cr := sar_body_1_code base jal_off
    cpsTriple base exit cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 8) ↦ₘ v1) ** ((sp + 16) ↦ₘ v2) ** ((sp + 24) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result2) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ signExt) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 8) ↦ₘ result1) ** ((sp + 16) ↦ₘ result2) ** ((sp + 24) ↦ₘ signExt)) := by
  have h63 := bv6_toNat_63
  have MM1 := shr_merge_limb_spec 8 16 0 sp v1 v2 v0 v5 v10 bit_shift anti_shift mask base
  have MM2 := shr_merge_limb_spec 16 24 8 sp v2 v3 v1
    ((v1 >>> (bit_shift.toNat % 64)) ||| ((v2 <<< (anti_shift.toNat % 64)) &&& mask))
    ((v2 <<< (anti_shift.toNat % 64)) &&& mask)
    bit_shift anti_shift mask (base + 28)
  have LL := sar_last_limb_spec 16 sp v3 v2
    ((v2 >>> (bit_shift.toNat % 64)) ||| ((v3 <<< (anti_shift.toNat % 64)) &&& mask))
    bit_shift (base + 56)
  have SR := srai_spec_gen .x10 .x5
    ((v3 <<< (anti_shift.toNat % 64)) &&& mask)
    (BitVec.sshiftRight v3 (bit_shift.toNat % 64)) 63 (base + 68) (by nofun)
  simp only [h63] at SR
  have S0 := sd_spec_gen .x12 .x10 sp
    (BitVec.sshiftRight (BitVec.sshiftRight v3 (bit_shift.toNat % 64)) 63) v3 24 (base + 72)
  have JL := jal_x0_spec_gen jal_off (base + 76)
  rw [hexit] at JL
  runBlock MM1 MM2 LL SR S0 JL

abbrev sar_body_0_code (base : Word) (jal_off : BitVec 21) : CodeReq :=
  CodeReq.ofProg base (sar_body_0_prog jal_off)

/-- SAR body 0: limb_shift=0 (25 instructions).
    result[i] = merge(value[i], value[i+1]) for i=0..2;
    result[3] = value[3] SRA bs.
    No vacated limbs — identical structure to SHR body_0 but with SRA for last limb.
    Comprises: 3x shr_merge_limb_inplace + sar_last_limb_inplace + JAL. -/
theorem sar_body_0_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 : Word)
    (base exit : Word) (jal_off : BitVec 21)
    (hexit : (base + 96) + signExtend21 jal_off = exit) :
    let result0 := (v0 >>> (bit_shift.toNat % 64)) ||| ((v1 <<< (anti_shift.toNat % 64)) &&& mask)
    let result1 := (v1 >>> (bit_shift.toNat % 64)) ||| ((v2 <<< (anti_shift.toNat % 64)) &&& mask)
    let result2 := (v2 >>> (bit_shift.toNat % 64)) ||| ((v3 <<< (anti_shift.toNat % 64)) &&& mask)
    let result3 := BitVec.sshiftRight v3 (bit_shift.toNat % 64)
    let cr := sar_body_0_code base jal_off
    cpsTriple base exit cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 8) ↦ₘ v1) ** ((sp + 16) ↦ₘ v2) ** ((sp + 24) ↦ₘ v3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result3) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v3 <<< (anti_shift.toNat % 64)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 8) ↦ₘ result1) ** ((sp + 16) ↦ₘ result2) ** ((sp + 24) ↦ₘ result3)) := by
  have MM1 := shr_merge_limb_inplace_spec 0 8 sp v0 v1 v5 v10 bit_shift anti_shift mask base
  have MM2 := shr_merge_limb_inplace_spec 8 16 sp v1 v2
    ((v0 >>> (bit_shift.toNat % 64)) ||| ((v1 <<< (anti_shift.toNat % 64)) &&& mask))
    ((v1 <<< (anti_shift.toNat % 64)) &&& mask)
    bit_shift anti_shift mask (base + 28)
  have MM3 := shr_merge_limb_inplace_spec 16 24 sp v2 v3
    ((v1 >>> (bit_shift.toNat % 64)) ||| ((v2 <<< (anti_shift.toNat % 64)) &&& mask))
    ((v2 <<< (anti_shift.toNat % 64)) &&& mask)
    bit_shift anti_shift mask (base + 56)
  have LL := sar_last_limb_inplace_spec sp v3
    ((v2 >>> (bit_shift.toNat % 64)) ||| ((v3 <<< (anti_shift.toNat % 64)) &&& mask))
    bit_shift (base + 84)
  have JL := jal_x0_spec_gen jal_off (base + 96)
  rw [hexit] at JL
  runBlock MM1 MM2 MM3 LL JL

-- ============================================================================
-- Sign-fill path spec (7 instructions)
-- ============================================================================

abbrev sar_sign_fill_path_code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x5 .x12 56))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SRAI .x5 .x5 63))
  (CodeReq.union (CodeReq.singleton (base + 8) (.ADDI .x12 .x12 32))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x5 0))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SD .x12 .x5 8))
  (CodeReq.union (CodeReq.singleton (base + 20) (.SD .x12 .x5 16))
   (CodeReq.singleton (base + 24) (.SD .x12 .x5 24)))))))

/-- SAR sign-fill path (7 instructions):
    LD x5, 56(x12); SRAI x5,x5,63; ADDI x12,x12,32;
    SD x12,x5,0; SD x12,x5,8; SD x12,x5,16; SD x12,x5,24

    Entered when shift >= 256. Computes sign extension of value[3] (at sp+56),
    pops shift word (ADDI x12, 32), fills all 4 result limbs with sign extension. -/
theorem sar_sign_fill_path_spec (sp : Word)
    (v5 v10 : Word)
    (v0 v1 v2 v3 : Word)
    (base : Word) :
    let signExt := BitVec.sshiftRight v3 63
    let cr := sar_sign_fill_path_code base
    cpsTriple base (base + 28) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 40) ↦ₘ v1) ** ((sp + 48) ↦ₘ v2) ** ((sp + 56) ↦ₘ v3))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ signExt) ** (.x10 ↦ᵣ v10) **
       ((sp + 32) ↦ₘ signExt) ** ((sp + 40) ↦ₘ signExt) ** ((sp + 48) ↦ₘ signExt) ** ((sp + 56) ↦ₘ signExt)) := by
  have h63 := bv6_toNat_63
  have LD0 := ld_spec_gen .x5 .x12 sp v5 v3 56 base (by nofun)
  have SR := srai_spec_gen_same .x5 v3 63 (base + 4) (by nofun)
  simp only [h63] at SR
  have AD := addi_spec_gen_same .x12 sp 32 (base + 8) (by nofun)
  simp only [signExtend12_32] at AD
  have S0 := sd_spec_gen .x12 .x5 (sp + 32) (BitVec.sshiftRight v3 63) v0 0 (base + 12)
  have S1 := sd_spec_gen .x12 .x5 (sp + 32) (BitVec.sshiftRight v3 63) v1 8 (base + 16)
  have S2 := sd_spec_gen .x12 .x5 (sp + 32) (BitVec.sshiftRight v3 63) v2 16 (base + 20)
  have S3 := sd_spec_gen .x12 .x5 (sp + 32) (BitVec.sshiftRight v3 63) v3 24 (base + 24)
  runBlock LD0 SR AD S0 S1 S2 S3

end EvmAsm.Evm64
