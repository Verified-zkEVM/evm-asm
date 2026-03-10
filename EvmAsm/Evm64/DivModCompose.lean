/-
  EvmAsm.Evm64.DivModCompose

  Hierarchical composition of DivMod CPS specs using progAt to avoid
  the WHNF scalability limit (25+ instruction atoms in a single theorem type).
  Each composed spec uses `progAt base evm_div` as a single code assertion.
-/

import EvmAsm.Evm64.DivModSpec

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Section 1: Program length lemmas (via native_decide)
-- ============================================================================

private theorem divK_phaseA_len : (divK_phaseA 1016).length = 8 := by native_decide
private theorem divK_phaseB_len : divK_phaseB.length = 21 := by native_decide
private theorem divK_clz_len : divK_clz.length = 24 := by native_decide
private theorem divK_phaseC2_len : (divK_phaseC2 172).length = 4 := by native_decide
private theorem divK_normB_len : divK_normB.length = 21 := by native_decide
private theorem divK_normA_len : (divK_normA 40).length = 21 := by native_decide
private theorem divK_copyAU_len : divK_copyAU.length = 9 := by native_decide
private theorem divK_loopSetup_len : (divK_loopSetup 460).length = 4 := by native_decide
private theorem divK_loopBody_len : (divK_loopBody 556 7740).length = 114 := by native_decide
private theorem divK_denorm_len : divK_denorm.length = 25 := by native_decide
private theorem divK_divEpilogue_len : (divK_div_epilogue 24).length = 10 := by native_decide
private theorem divK_zeroPath_len : divK_zeroPath.length = 5 := by native_decide
private theorem divK_nop_len : (ADDI .x0 .x0 0 : Program).length = 1 := by native_decide
private theorem divK_div128_len : divK_div128.length = 49 := by native_decide

-- ============================================================================
-- Section 2: BitVec.ofNat offset normalization (via native_decide)
-- ============================================================================

private theorem bv_off_divK_8   : BitVec.ofNat 64 (4 * 8)   = (32  : Addr) := by native_decide
private theorem bv_off_divK_21  : BitVec.ofNat 64 (4 * 21)  = (84  : Addr) := by native_decide
private theorem bv_off_divK_24  : BitVec.ofNat 64 (4 * 24)  = (96  : Addr) := by native_decide
private theorem bv_off_divK_4   : BitVec.ofNat 64 (4 * 4)   = (16  : Addr) := by native_decide
private theorem bv_off_divK_9   : BitVec.ofNat 64 (4 * 9)   = (36  : Addr) := by native_decide
private theorem bv_off_divK_114 : BitVec.ofNat 64 (4 * 114) = (456 : Addr) := by native_decide
private theorem bv_off_divK_25  : BitVec.ofNat 64 (4 * 25)  = (100 : Addr) := by native_decide
private theorem bv_off_divK_10  : BitVec.ofNat 64 (4 * 10)  = (40  : Addr) := by native_decide
private theorem bv_off_divK_5   : BitVec.ofNat 64 (4 * 5)   = (20  : Addr) := by native_decide
private theorem bv_off_divK_1   : BitVec.ofNat 64 (4 * 1)   = (4   : Addr) := by native_decide
private theorem bv_off_divK_49  : BitVec.ofNat 64 (4 * 49)  = (196 : Addr) := by native_decide

-- ============================================================================
-- Section 3: Accumulated address normalization (via bv_omega)
-- ============================================================================

@[simp] private theorem divK_addr_116  (b : Addr) : b + 32 + 84  = b + 116  := by bv_omega
@[simp] private theorem divK_addr_212  (b : Addr) : b + 116 + 96 = b + 212  := by bv_omega
@[simp] private theorem divK_addr_228  (b : Addr) : b + 212 + 16 = b + 228  := by bv_omega
@[simp] private theorem divK_addr_312  (b : Addr) : b + 228 + 84 = b + 312  := by bv_omega
@[simp] private theorem divK_addr_396  (b : Addr) : b + 312 + 84 = b + 396  := by bv_omega
@[simp] private theorem divK_addr_432  (b : Addr) : b + 396 + 36 = b + 432  := by bv_omega
@[simp] private theorem divK_addr_448  (b : Addr) : b + 432 + 16 = b + 448  := by bv_omega
@[simp] private theorem divK_addr_904  (b : Addr) : b + 448 + 456 = b + 904 := by bv_omega
@[simp] private theorem divK_addr_1004 (b : Addr) : b + 904 + 100 = b + 1004 := by bv_omega
@[simp] private theorem divK_addr_1044 (b : Addr) : b + 1004 + 40 = b + 1044 := by bv_omega
@[simp] private theorem divK_addr_1064 (b : Addr) : b + 1044 + 20 = b + 1064 := by bv_omega
@[simp] private theorem divK_addr_1068 (b : Addr) : b + 1064 + 4  = b + 1068 := by bv_omega

-- ============================================================================
-- Section 4: Full program code split into per-phase progAt blocks
-- ============================================================================

/-- The full evm_div code split into 14 per-phase progAt blocks.
    This is the canonical code assertion for all composed specs. -/
abbrev divCode (base : Addr) : Assertion :=
  progAt base (divK_phaseA 1016) **
  progAt (base + 32) divK_phaseB **
  progAt (base + 116) divK_clz **
  progAt (base + 212) (divK_phaseC2 172) **
  progAt (base + 228) divK_normB **
  progAt (base + 312) (divK_normA 40) **
  progAt (base + 396) divK_copyAU **
  progAt (base + 432) (divK_loopSetup 460) **
  progAt (base + 448) (divK_loopBody 556 7740) **
  progAt (base + 904) divK_denorm **
  progAt (base + 1004) (divK_div_epilogue 24) **
  progAt (base + 1044) divK_zeroPath **
  progAt (base + 1064) (ADDI .x0 .x0 0) **
  progAt (base + 1068) divK_div128

/-- progAt_append for Program (needed because Program is a def, not abbrev). -/
private theorem progAt_append_prog (base : Addr) (p1 p2 : Program) :
    progAt base (p1 ++ p2) = (progAt base p1 ** progAt (base + BitVec.ofNat 64 (4 * p1.length)) p2) :=
  progAt_append base p1 p2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
/-- Split progAt base evm_div into per-phase progAt blocks. -/
theorem progAt_evm_div_split (base : Addr) :
    progAt base evm_div = divCode base := by
  unfold evm_div divCode seq
  simp only [progAt_append_prog,
    divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
    divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
    divK_loopBody_len, divK_denorm_len, divK_divEpilogue_len,
    divK_zeroPath_len, divK_nop_len, divK_div128_len,
    bv_off_divK_8, bv_off_divK_21, bv_off_divK_24, bv_off_divK_4,
    bv_off_divK_9, bv_off_divK_114, bv_off_divK_25, bv_off_divK_10,
    bv_off_divK_5, bv_off_divK_1, bv_off_divK_49,
    divK_addr_116, divK_addr_212, divK_addr_228, divK_addr_312,
    divK_addr_396, divK_addr_432, divK_addr_448, divK_addr_904,
    divK_addr_1004, divK_addr_1044, divK_addr_1064, divK_addr_1068]

-- ============================================================================
-- Section 5: progAt unfolding lemmas (explicit instrAt atoms)
-- Only for blocks on current execution paths being composed.
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
/-- Unfold progAt for phaseA (8 instructions). -/
private theorem progAt_divK_phaseA (base : Addr) :
    progAt base (divK_phaseA 1016) =
    ((base ↦ᵢ .LD .x5 .x12 32) **
     ((base + 4) ↦ᵢ .LD .x10 .x12 40) **
     ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LD .x10 .x12 48) **
     ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LD .x10 .x12 56) **
     ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 28) ↦ᵢ .BEQ .x5 .x0 1016)) := by
  show progAt base ([.LD .x5 .x12 32, .LD .x10 .x12 40, .OR .x5 .x5 .x10,
    .LD .x10 .x12 48, .OR .x5 .x5 .x10, .LD .x10 .x12 56,
    .OR .x5 .x5 .x10, .BEQ .x5 .x0 1016] : List Instr) = _
  simp only [progAt, progIndexed, programAt, sepConj_emp_right']
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 = base + 28 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 = base + 24 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 = base + 20 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 = base + 16 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 = base + 12 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
/-- Unfold progAt for zeroPath (5 instructions). -/
private theorem progAt_divK_zeroPath (base : Addr) :
    progAt base divK_zeroPath =
    ((base ↦ᵢ .ADDI .x12 .x12 32) **
     ((base + 4) ↦ᵢ .SD .x12 .x0 0) **
     ((base + 8) ↦ᵢ .SD .x12 .x0 8) **
     ((base + 12) ↦ᵢ .SD .x12 .x0 16) **
     ((base + 16) ↦ᵢ .SD .x12 .x0 24)) := by
  show progAt base ([.ADDI .x12 .x12 32, .SD .x12 .x0 0, .SD .x12 .x0 8,
    .SD .x12 .x0 16, .SD .x12 .x0 24] : List Instr) = _
  simp only [progAt, progIndexed, programAt, sepConj_emp_right']
  rw [show (base + 4 : Addr) + 4 + 4 + 4 = base + 16 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 = base + 12 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
/-- Unfold progAt for phaseB (21 instructions). -/
private theorem progAt_divK_phaseB (base : Addr) :
    progAt base divK_phaseB =
    ((base ↦ᵢ .SD .x12 .x0 4088) **
     ((base + 4) ↦ᵢ .SD .x12 .x0 4080) **
     ((base + 8) ↦ᵢ .SD .x12 .x0 4072) **
     ((base + 12) ↦ᵢ .SD .x12 .x0 4064) **
     ((base + 16) ↦ᵢ .SD .x12 .x0 4016) **
     ((base + 20) ↦ᵢ .SD .x12 .x0 4008) **
     ((base + 24) ↦ᵢ .SD .x12 .x0 4000) **
     ((base + 28) ↦ᵢ .LD .x6 .x12 40) **
     ((base + 32) ↦ᵢ .LD .x7 .x12 48) **
     ((base + 36) ↦ᵢ .ADDI .x5 .x0 4) **
     ((base + 40) ↦ᵢ .BNE .x10 .x0 24) **
     ((base + 44) ↦ᵢ .ADDI .x5 .x0 3) **
     ((base + 48) ↦ᵢ .BNE .x7 .x0 16) **
     ((base + 52) ↦ᵢ .ADDI .x5 .x0 2) **
     ((base + 56) ↦ᵢ .BNE .x6 .x0 8) **
     ((base + 60) ↦ᵢ .ADDI .x5 .x0 1) **
     ((base + 64) ↦ᵢ .SD .x12 .x5 3984) **
     ((base + 68) ↦ᵢ .ADDI .x5 .x5 4095) **
     ((base + 72) ↦ᵢ .SLLI .x5 .x5 3) **
     ((base + 76) ↦ᵢ .ADD .x5 .x12 .x5) **
     ((base + 80) ↦ᵢ .LD .x5 .x5 32)) := by
  show progAt base ([.SD .x12 .x0 4088, .SD .x12 .x0 4080, .SD .x12 .x0 4072, .SD .x12 .x0 4064,
    .SD .x12 .x0 4016, .SD .x12 .x0 4008, .SD .x12 .x0 4000,
    .LD .x6 .x12 40, .LD .x7 .x12 48,
    .ADDI .x5 .x0 4, .BNE .x10 .x0 24,
    .ADDI .x5 .x0 3, .BNE .x7 .x0 16,
    .ADDI .x5 .x0 2, .BNE .x6 .x0 8,
    .ADDI .x5 .x0 1,
    .SD .x12 .x5 3984, .ADDI .x5 .x5 4095, .SLLI .x5 .x5 3, .ADD .x5 .x12 .x5,
    .LD .x5 .x5 32] : List Instr) = _
  simp only [progAt, progIndexed, programAt, sepConj_emp_right']
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 80 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 76 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 72 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 68 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 64 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 60 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 56 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 52 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 48 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 44 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 40 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 36 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 + 4 = base + 32 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 + 4 = base + 28 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 + 4 = base + 24 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 + 4 = base + 20 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 + 4 = base + 16 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 + 4 = base + 12 from by bv_omega]
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega]

-- ============================================================================
-- Section 6: pcFree lemmas for code blocks
-- ============================================================================

private theorem pcFree_divCode (base : Addr) : (divCode base).pcFree := by
  unfold divCode; pcFree

-- Abbreviation for "all code except phaseA and zeroPath"
private abbrev divCode_mid (base : Addr) : Assertion :=
  progAt (base + 32) divK_phaseB **
  progAt (base + 116) divK_clz **
  progAt (base + 212) (divK_phaseC2 172) **
  progAt (base + 228) divK_normB **
  progAt (base + 312) (divK_normA 40) **
  progAt (base + 396) divK_copyAU **
  progAt (base + 432) (divK_loopSetup 460) **
  progAt (base + 448) (divK_loopBody 556 7740) **
  progAt (base + 904) divK_denorm **
  progAt (base + 1004) (divK_div_epilogue 24) **
  progAt (base + 1064) (ADDI .x0 .x0 0) **
  progAt (base + 1068) divK_div128

private theorem pcFree_divCode_mid (base : Addr) : (divCode_mid base).pcFree := by
  unfold divCode_mid; pcFree

-- Abbreviation for "all code except phaseA and phaseB" (for Phase B composition)
private abbrev divCode_noAB (base : Addr) : Assertion :=
  progAt (base + 116) divK_clz **
  progAt (base + 212) (divK_phaseC2 172) **
  progAt (base + 228) divK_normB **
  progAt (base + 312) (divK_normA 40) **
  progAt (base + 396) divK_copyAU **
  progAt (base + 432) (divK_loopSetup 460) **
  progAt (base + 448) (divK_loopBody 556 7740) **
  progAt (base + 904) divK_denorm **
  progAt (base + 1004) (divK_div_epilogue 24) **
  progAt (base + 1044) divK_zeroPath **
  progAt (base + 1064) (ADDI .x0 .x0 0) **
  progAt (base + 1068) divK_div128

private theorem pcFree_divCode_noAB (base : Addr) : (divCode_noAB base).pcFree := by
  unfold divCode_noAB; pcFree

-- ============================================================================
-- Section 7: signExtend13 normalization
-- ============================================================================

private theorem signExtend13_1016 : signExtend13 (1016 : BitVec 13) = (1016 : Word) := by
  native_decide

private theorem signExtend13_24 : signExtend13 (24 : BitVec 13) = (24 : Word) := by
  native_decide

-- Phase B n=4: signExtend12 4 = 4 (result of ADDI x5 x0 4 via addi_x0_spec_gen)
private theorem divK_se12_4 : signExtend12 (4 : BitVec 12) = (4 : Word) := by native_decide

-- Phase B tail address: nm1_x8 = (4 + signExtend12 4095) <<< 3 = 24
private theorem divK_phaseB_n4_nm1_x8 :
    ((4 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (24 : Word) := by
  native_decide

-- signExtend12 32 = 32 (for tail load address: sp + 24 + signExtend12 32 = sp + 56)
private theorem divK_se12_32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by native_decide


-- ============================================================================
-- Section 8: Zero path composition (b = 0)
-- Phase A body → BEQ(taken) → zeroPath → exit
-- ============================================================================

set_option maxRecDepth 2048 in
set_option maxHeartbeats 12800000 in
/-- When b = 0 (all limbs zero), evm_div writes zeros and advances sp.
    Execution path: phaseA body (7 instrs), BEQ taken, zeroPath (5 instrs). -/
theorem evm_div_bzero_spec (sp base : Addr)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbz : b0 ||| b1 ||| b2 ||| b3 = 0)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 1064)
      (divCode base **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (divCode base **
       (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  -- Step 1: Phase A body (base → base+28, 7 straight-line instructions)
  have hbody := divK_phaseA_body_spec sp base b0 b1 b2 b3 v5 v10 hvalid
  -- Step 2: BEQ at base+28, eliminate ntaken via hbz
  have hbeq_raw := beq_spec_gen .x5 .x0 1016 (b0 ||| b1 ||| b2 ||| b3) (0 : Word) (base + 28)
  rw [show (base + 28 : Addr) + signExtend13 1016 = base + 1044 from by
        rw [signExtend13_1016]; bv_omega,
      show (base + 28 : Addr) + 4 = base + 32 from by bv_omega] at hbeq_raw
  have hbeq_clean := cpsBranch_elim_taken_strip_pure3 _ _ _ _ _ _ _ _ _ hbeq_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h1⟩ := hQf
      obtain ⟨_, _, _, _, _, h2⟩ := h1
      exact absurd hbz ((sepConj_pure_right _ _ _).mp h2).2)
  -- Step 3: Frame BEQ with body code atoms + x12 + x10 + mem
  have hbeq_framed := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LD .x5 .x12 32) **
     ((base + 4) ↦ᵢ .LD .x10 .x12 40) **
     ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LD .x10 .x12 48) **
     ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LD .x10 .x12 56) **
     ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq_clean
  -- Step 4: Compose body → BEQ(taken): base → base+1044
  have hAB := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  -- Step 5: Frame AB with zeroPath code (as progAt block)
  have hAB2 := cpsTriple_frame_left _ _ _ _
    (progAt (base + 1044) divK_zeroPath)
    (by pcFree) hAB
  -- Step 6: ZeroPath (base+1044 → base+1064)
  have hzp := divK_zeroPath_spec sp (base + 1044) b0 b1 b2 b3 hvalid
  rw [show (base + 1044 : Addr) + 20 = base + 1064 from by bv_omega] at hzp
  -- Frame ZP with phaseA code atoms + x5 + x10 + x0
  have hzp_framed := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LD .x5 .x12 32) **
     ((base + 4) ↦ᵢ .LD .x10 .x12 40) **
     ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LD .x10 .x12 48) **
     ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LD .x10 .x12 56) **
     ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 28) ↦ᵢ .BEQ .x5 .x0 1016) **
     (.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) hzp
  -- Step 7: Compose AB → ZP: base → base+1064
  have hABZ := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by
      rw [progAt_divK_zeroPath (base + 1044)] at hp
      xperm_hyp hp)
    hAB2 hzp_framed
  -- Step 8: Frame with remaining code blocks (mid = phaseB..epilogue + NOP + div128)
  have hfull := cpsTriple_frame_left _ _ _ _
    (divCode_mid base) (pcFree_divCode_mid base) hABZ
  -- Step 9: Final consequence — fold instrAt ↔ divCode, rewrite bor → 0
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by
      unfold divCode at hp
      rw [progAt_divK_phaseA] at hp
      unfold divCode_mid
      xperm_hyp hp)
    (fun h hq => by
      rw [hbz] at hq
      unfold divCode_mid at hq
      unfold divCode
      rw [progAt_divK_phaseA, progAt_divK_zeroPath (base + 1044)]
      xperm_hyp hq)
    hfull

-- ============================================================================
-- Section 9: Phase A not-taken composition (b ≠ 0)
-- Phase A body → BEQ(ntaken) → fall through to Phase B
-- ============================================================================

set_option maxRecDepth 2048 in
set_option maxHeartbeats 12800000 in
/-- When b ≠ 0, evm_div falls through Phase A to Phase B at base+32.
    Execution path: phaseA body (7 instrs), BEQ not taken. -/
theorem evm_div_phaseA_ntaken_spec (sp base : Addr)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 32)
      (divCode base **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (divCode base **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) := by
  -- Step 1: Phase A body (base → base+28, 7 straight-line instructions)
  have hbody := divK_phaseA_body_spec sp base b0 b1 b2 b3 v5 v10 hvalid
  -- Step 2: BEQ at base+28, eliminate taken path (b=0 absurd since hbnz)
  have hbeq_raw := beq_spec_gen .x5 .x0 1016 (b0 ||| b1 ||| b2 ||| b3) (0 : Word) (base + 28)
  rw [show (base + 28 : Addr) + signExtend13 1016 = base + 1044 from by
        rw [signExtend13_1016]; bv_omega,
      show (base + 28 : Addr) + 4 = base + 32 from by bv_omega] at hbeq_raw
  have hbeq_clean := cpsBranch_elim_ntaken_strip_pure3 _ _ _ _ _ _ _ _ _ hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h1⟩ := hQt
      obtain ⟨_, _, _, _, _, h2⟩ := h1
      exact absurd ((sepConj_pure_right _ _ _).mp h2).2 hbnz)
  -- Step 3: Frame BEQ with body code atoms + x12 + x10 + mem
  have hbeq_framed := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LD .x5 .x12 32) **
     ((base + 4) ↦ᵢ .LD .x10 .x12 40) **
     ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LD .x10 .x12 48) **
     ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LD .x10 .x12 56) **
     ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq_clean
  -- Step 4: Compose body → BEQ(ntaken): base → base+32
  have hAB := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  -- Step 5: Frame with remaining code blocks (everything except phaseA)
  have hfull := cpsTriple_frame_left _ _ _ _
    (divCode_mid base ** progAt (base + 1044) divK_zeroPath)
    (by unfold divCode_mid; pcFree) hAB
  -- Step 6: Final consequence — fold instrAt ↔ divCode
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by
      unfold divCode at hp
      rw [progAt_divK_phaseA] at hp
      unfold divCode_mid
      xperm_hyp hp)
    (fun h hq => by
      unfold divCode_mid at hq
      unfold divCode
      rw [progAt_divK_phaseA]
      xperm_hyp hq)
    hfull

-- ============================================================================
-- Section 10: MOD program code infrastructure
-- ============================================================================

private theorem divK_modEpilogue_len : (divK_mod_epilogue 24).length = 10 := by native_decide

/-- The full evm_mod code split into 14 per-phase progAt blocks.
    Identical to divCode except block 11 uses divK_mod_epilogue. -/
abbrev modCode (base : Addr) : Assertion :=
  progAt base (divK_phaseA 1016) **
  progAt (base + 32) divK_phaseB **
  progAt (base + 116) divK_clz **
  progAt (base + 212) (divK_phaseC2 172) **
  progAt (base + 228) divK_normB **
  progAt (base + 312) (divK_normA 40) **
  progAt (base + 396) divK_copyAU **
  progAt (base + 432) (divK_loopSetup 460) **
  progAt (base + 448) (divK_loopBody 556 7740) **
  progAt (base + 904) divK_denorm **
  progAt (base + 1004) (divK_mod_epilogue 24) **
  progAt (base + 1044) divK_zeroPath **
  progAt (base + 1064) (ADDI .x0 .x0 0) **
  progAt (base + 1068) divK_div128

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
/-- Split progAt base evm_mod into per-phase progAt blocks. -/
theorem progAt_evm_mod_split (base : Addr) :
    progAt base evm_mod = modCode base := by
  unfold evm_mod modCode seq
  simp only [progAt_append_prog,
    divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
    divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
    divK_loopBody_len, divK_denorm_len, divK_modEpilogue_len,
    divK_zeroPath_len, divK_nop_len,
    bv_off_divK_8, bv_off_divK_21, bv_off_divK_24, bv_off_divK_4,
    bv_off_divK_9, bv_off_divK_114, bv_off_divK_25, bv_off_divK_10,
    bv_off_divK_5, bv_off_divK_1,
    divK_addr_116, divK_addr_212, divK_addr_228, divK_addr_312,
    divK_addr_396, divK_addr_432, divK_addr_448, divK_addr_904,
    divK_addr_1004, divK_addr_1044, divK_addr_1064, divK_addr_1068]

-- Abbreviation for "all MOD code except phaseA and zeroPath"
private abbrev modCode_mid (base : Addr) : Assertion :=
  progAt (base + 32) divK_phaseB **
  progAt (base + 116) divK_clz **
  progAt (base + 212) (divK_phaseC2 172) **
  progAt (base + 228) divK_normB **
  progAt (base + 312) (divK_normA 40) **
  progAt (base + 396) divK_copyAU **
  progAt (base + 432) (divK_loopSetup 460) **
  progAt (base + 448) (divK_loopBody 556 7740) **
  progAt (base + 904) divK_denorm **
  progAt (base + 1004) (divK_mod_epilogue 24) **
  progAt (base + 1064) (ADDI .x0 .x0 0) **
  progAt (base + 1068) divK_div128

private theorem pcFree_modCode_mid (base : Addr) : (modCode_mid base).pcFree := by
  unfold modCode_mid; pcFree

-- ============================================================================
-- Section 11: MOD zero path composition (b = 0)
-- Phase A body → BEQ(taken) → zeroPath → exit
-- ============================================================================

set_option maxRecDepth 2048 in
set_option maxHeartbeats 12800000 in
/-- When b = 0 (all limbs zero), evm_mod writes zeros and advances sp.
    Execution path: phaseA body (7 instrs), BEQ taken, zeroPath (5 instrs). -/
theorem evm_mod_bzero_spec (sp base : Addr)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbz : b0 ||| b1 ||| b2 ||| b3 = 0)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 1064)
      (modCode base **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (modCode base **
       (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  -- Step 1: Phase A body (base → base+28, 7 straight-line instructions)
  have hbody := divK_phaseA_body_spec sp base b0 b1 b2 b3 v5 v10 hvalid
  -- Step 2: BEQ at base+28, eliminate ntaken via hbz
  have hbeq_raw := beq_spec_gen .x5 .x0 1016 (b0 ||| b1 ||| b2 ||| b3) (0 : Word) (base + 28)
  rw [show (base + 28 : Addr) + signExtend13 1016 = base + 1044 from by
        rw [signExtend13_1016]; bv_omega,
      show (base + 28 : Addr) + 4 = base + 32 from by bv_omega] at hbeq_raw
  have hbeq_clean := cpsBranch_elim_taken_strip_pure3 _ _ _ _ _ _ _ _ _ hbeq_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h1⟩ := hQf
      obtain ⟨_, _, _, _, _, h2⟩ := h1
      exact absurd hbz ((sepConj_pure_right _ _ _).mp h2).2)
  -- Step 3: Frame BEQ with body code atoms + x12 + x10 + mem
  have hbeq_framed := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LD .x5 .x12 32) **
     ((base + 4) ↦ᵢ .LD .x10 .x12 40) **
     ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LD .x10 .x12 48) **
     ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LD .x10 .x12 56) **
     ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq_clean
  -- Step 4: Compose body → BEQ(taken): base → base+1044
  have hAB := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  -- Step 5: Frame AB with zeroPath code (as progAt block)
  have hAB2 := cpsTriple_frame_left _ _ _ _
    (progAt (base + 1044) divK_zeroPath)
    (by pcFree) hAB
  -- Step 6: ZeroPath (base+1044 → base+1064)
  have hzp := divK_zeroPath_spec sp (base + 1044) b0 b1 b2 b3 hvalid
  rw [show (base + 1044 : Addr) + 20 = base + 1064 from by bv_omega] at hzp
  -- Frame ZP with phaseA code atoms + x5 + x10 + x0
  have hzp_framed := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LD .x5 .x12 32) **
     ((base + 4) ↦ᵢ .LD .x10 .x12 40) **
     ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LD .x10 .x12 48) **
     ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LD .x10 .x12 56) **
     ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 28) ↦ᵢ .BEQ .x5 .x0 1016) **
     (.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) hzp
  -- Step 7: Compose AB → ZP: base → base+1064
  have hABZ := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by
      rw [progAt_divK_zeroPath (base + 1044)] at hp
      xperm_hyp hp)
    hAB2 hzp_framed
  -- Step 8: Frame with remaining code blocks (mid = phaseB..mod_epilogue + NOP + div128)
  have hfull := cpsTriple_frame_left _ _ _ _
    (modCode_mid base) (pcFree_modCode_mid base) hABZ
  -- Step 9: Final consequence — fold instrAt ↔ modCode, rewrite bor → 0
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by
      unfold modCode at hp
      rw [progAt_divK_phaseA] at hp
      unfold modCode_mid
      xperm_hyp hp)
    (fun h hq => by
      rw [hbz] at hq
      unfold modCode_mid at hq
      unfold modCode
      rw [progAt_divK_phaseA, progAt_divK_zeroPath (base + 1044)]
      xperm_hyp hq)
    hfull

-- ============================================================================
-- Section 12: MOD Phase A not-taken composition (b ≠ 0)
-- ============================================================================

set_option maxRecDepth 2048 in
set_option maxHeartbeats 12800000 in
/-- When b ≠ 0, evm_mod falls through Phase A to Phase B at base+32.
    Execution path: phaseA body (7 instrs), BEQ not taken. -/
theorem evm_mod_phaseA_ntaken_spec (sp base : Addr)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 32)
      (modCode base **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (modCode base **
       (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) := by
  -- Step 1: Phase A body (base → base+28, 7 straight-line instructions)
  have hbody := divK_phaseA_body_spec sp base b0 b1 b2 b3 v5 v10 hvalid
  -- Step 2: BEQ at base+28, eliminate taken path (b=0 absurd since hbnz)
  have hbeq_raw := beq_spec_gen .x5 .x0 1016 (b0 ||| b1 ||| b2 ||| b3) (0 : Word) (base + 28)
  rw [show (base + 28 : Addr) + signExtend13 1016 = base + 1044 from by
        rw [signExtend13_1016]; bv_omega,
      show (base + 28 : Addr) + 4 = base + 32 from by bv_omega] at hbeq_raw
  have hbeq_clean := cpsBranch_elim_ntaken_strip_pure3 _ _ _ _ _ _ _ _ _ hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h1⟩ := hQt
      obtain ⟨_, _, _, _, _, h2⟩ := h1
      exact absurd ((sepConj_pure_right _ _ _).mp h2).2 hbnz)
  -- Step 3: Frame BEQ with body code atoms + x12 + x10 + mem
  have hbeq_framed := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LD .x5 .x12 32) **
     ((base + 4) ↦ᵢ .LD .x10 .x12 40) **
     ((base + 8) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 12) ↦ᵢ .LD .x10 .x12 48) **
     ((base + 16) ↦ᵢ .OR .x5 .x5 .x10) **
     ((base + 20) ↦ᵢ .LD .x10 .x12 56) **
     ((base + 24) ↦ᵢ .OR .x5 .x5 .x10) **
     (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq_clean
  -- Step 4: Compose body → BEQ(ntaken): base → base+32
  have hAB := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  -- Step 5: Frame with remaining code blocks (everything except phaseA)
  have hfull := cpsTriple_frame_left _ _ _ _
    (modCode_mid base ** progAt (base + 1044) divK_zeroPath)
    (by unfold modCode_mid; pcFree) hAB
  -- Step 6: Final consequence — fold instrAt ↔ modCode
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by
      unfold modCode at hp
      rw [progAt_divK_phaseA] at hp
      unfold modCode_mid
      xperm_hyp hp)
    (fun h hq => by
      unfold modCode_mid at hq
      unfold modCode
      rw [progAt_divK_phaseA]
      xperm_hyp hq)
    hfull

end EvmAsm.Rv64
