/-
  EvmAsm.Evm.And

  Full 256-bit EVM AND spec with ProgramAt/ValidMemRange abstractions.
-/

import EvmAsm.Evm.Bitwise

namespace EvmAsm

-- ============================================================================
-- Full 256-bit AND spec with ProgramAt/ValidMemRange
-- ============================================================================

local macro "bv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]))

set_option maxHeartbeats 6400000 in
/-- Full 256-bit EVM AND: composes 8 per-limb AND specs + sp adjustment.
    33 instructions total. Pops 2 stack words (A at sp, B at sp+32),
    writes A &&& B to sp+32..sp+60, advances sp by 32.
    Uses ValidMemRange for clean hypotheses. -/
theorem evm_and_spec (sp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 : Word)
    (hvalid : ValidMemRange sp 16) :
    cpsTriple base (base + 132)
      (-- Limb 0 code
       (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
       ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
       -- Limb 1 code
       ((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
       ((base + 24) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
       -- Limb 2 code
       ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
       ((base + 40) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
       -- Limb 3 code
       ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
       ((base + 56) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
       -- Limb 4 code
       ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
       ((base + 72) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
       -- Limb 5 code
       ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
       ((base + 88) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
       -- Limb 6 code
       ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
       ((base + 104) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
       -- Limb 7 code
       ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
       ((base + 120) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60) **
       -- ADDI
       ((base + 128) ↦ᵢ .ADDI .x12 .x12 32) **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      (-- Same code (preserved)
       (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
       ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
       ((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
       ((base + 24) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
       ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
       ((base + 40) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
       ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
       ((base + 56) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
       ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
       ((base + 72) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
       ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
       ((base + 88) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
       ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
       ((base + 104) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
       ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
       ((base + 120) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60) **
       ((base + 128) ↦ᵢ .ADDI .x12 .x12 32) **
       -- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a7 &&& b7)) ** (.x6 ↦ᵣ b7) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ (a0 &&& b0)) ** ((sp + 36) ↦ₘ (a1 &&& b1)) ** ((sp + 40) ↦ₘ (a2 &&& b2)) ** ((sp + 44) ↦ₘ (a3 &&& b3)) **
       ((sp + 48) ↦ₘ (a4 &&& b4)) ** ((sp + 52) ↦ₘ (a5 &&& b5)) ** ((sp + 56) ↦ₘ (a6 &&& b6)) ** ((sp + 60) ↦ₘ (a7 &&& b7))) := by
  -- Memory validity from ValidMemRange
  have hvm0 : isValidMemAccess (sp + signExtend12 (0 : BitVec 12)) = true := by
    simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]
    have := hvalid.get (i := 0) (by omega); simpa using this
  have hvm4 : isValidMemAccess (sp + signExtend12 (4 : BitVec 12)) = true := by
    simp only [signExtend12_4]; have := hvalid.get (i := 1) (by omega); simpa using this
  have hvm8 : isValidMemAccess (sp + signExtend12 (8 : BitVec 12)) = true := by
    simp only [signExtend12_8]; have := hvalid.get (i := 2) (by omega); simpa using this
  have hvm12 : isValidMemAccess (sp + signExtend12 (12 : BitVec 12)) = true := by
    simp only [signExtend12_12]; have := hvalid.get (i := 3) (by omega); simpa using this
  have hvm16 : isValidMemAccess (sp + signExtend12 (16 : BitVec 12)) = true := by
    simp only [signExtend12_16]; have := hvalid.get (i := 4) (by omega); simpa using this
  have hvm20 : isValidMemAccess (sp + signExtend12 (20 : BitVec 12)) = true := by
    simp only [signExtend12_20]; have := hvalid.get (i := 5) (by omega); simpa using this
  have hvm24 : isValidMemAccess (sp + signExtend12 (24 : BitVec 12)) = true := by
    simp only [signExtend12_24]; have := hvalid.get (i := 6) (by omega); simpa using this
  have hvm28 : isValidMemAccess (sp + signExtend12 (28 : BitVec 12)) = true := by
    simp only [signExtend12_28]; have := hvalid.get (i := 7) (by omega); simpa using this
  have hvm32 : isValidMemAccess (sp + signExtend12 (32 : BitVec 12)) = true := by
    simp only [signExtend12_32]; have := hvalid.get (i := 8) (by omega); simpa using this
  have hvm36 : isValidMemAccess (sp + signExtend12 (36 : BitVec 12)) = true := by
    simp only [signExtend12_36]; have := hvalid.get (i := 9) (by omega); simpa using this
  have hvm40 : isValidMemAccess (sp + signExtend12 (40 : BitVec 12)) = true := by
    simp only [signExtend12_40]; have := hvalid.get (i := 10) (by omega); simpa using this
  have hvm44 : isValidMemAccess (sp + signExtend12 (44 : BitVec 12)) = true := by
    simp only [signExtend12_44]; have := hvalid.get (i := 11) (by omega); simpa using this
  have hvm48 : isValidMemAccess (sp + signExtend12 (48 : BitVec 12)) = true := by
    simp only [signExtend12_48]; have := hvalid.get (i := 12) (by omega); simpa using this
  have hvm52 : isValidMemAccess (sp + signExtend12 (52 : BitVec 12)) = true := by
    simp only [signExtend12_52]; have := hvalid.get (i := 13) (by omega); simpa using this
  have hvm56 : isValidMemAccess (sp + signExtend12 (56 : BitVec 12)) = true := by
    simp only [signExtend12_56]; have := hvalid.get (i := 14) (by omega); simpa using this
  have hvm60 : isValidMemAccess (sp + signExtend12 (60 : BitVec 12)) = true := by
    simp only [signExtend12_60]; have := hvalid.get (i := 15) (by omega); simpa using this
  -- Define F as all 32 per-limb instrAt
  let F : Assertion :=
    (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
    ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
    ((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
    ((base + 24) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
    ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
    ((base + 40) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
    ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
    ((base + 56) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
    ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
    ((base + 72) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
    ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
    ((base + 88) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
    ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
    ((base + 104) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
    ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
    ((base + 120) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60)
  have hF : F.pcFree := by pcFree
  -- Limb 0: and_limb_spec at base, offsets 0 and 32
  have L0_raw := and_limb_spec 0 32 sp a0 b0 v7 v6 base hvm0 hvm32
  simp only [signExtend12_0] at L0_raw
  rw [show sp + (0 : Word) = sp from by bv_addr] at L0_raw
  simp only [signExtend12_32] at L0_raw
  have L0 := cpsTriple_frame_left _ _ _ _
    (((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
     ((base + 24) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
     ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
     ((base + 40) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
     ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
     ((base + 56) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
     ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
     ((base + 72) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
     ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
     ((base + 88) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
     ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
     ((base + 104) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
     ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
     ((base + 120) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60) **
     ((base + 128) ↦ᵢ .ADDI .x12 .x12 32))
    (by pcFree) L0_raw
  clear L0_raw
  -- Permute L0 into binary_bitwise_spec form: (F ** ADDI) ** regs ** 2_mem
  have L0' : cpsTriple base (base + 16)
    ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
     (sp ↦ₘ a0) ** ((sp + 32) ↦ₘ b0))
    ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a0 &&& b0)) ** (.x6 ↦ᵣ b0) **
     (sp ↦ₘ a0) ** ((sp + 32) ↦ₘ (a0 &&& b0))) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) L0
  clear L0
  -- Limb 1: and_limb_spec at base+16, offsets 4 and 36
  have L1_raw := and_limb_spec 4 36 sp a1 b1 (a0 &&& b0) b0 (base + 16) hvm4 hvm36
  simp only [signExtend12_4, signExtend12_36] at L1_raw
  rw [show (base + 16 : Addr) + 4 = base + 20 from by bv_omega,
      show (base + 16 : Addr) + 8 = base + 24 from by bv_omega,
      show (base + 16 : Addr) + 12 = base + 28 from by bv_omega,
      show (base + 16 : Addr) + 16 = base + 32 from by bv_omega] at L1_raw
  have L1 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
     ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
     ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
     ((base + 40) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
     ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
     ((base + 56) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
     ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
     ((base + 72) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
     ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
     ((base + 88) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
     ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
     ((base + 104) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
     ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
     ((base + 120) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60) **
     ((base + 128) ↦ᵢ .ADDI .x12 .x12 32))
    (by pcFree) L1_raw
  clear L1_raw
  have L1' : cpsTriple (base + 16) (base + 32)
    ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a0 &&& b0)) ** (.x6 ↦ᵣ b0) **
     ((sp + 4) ↦ₘ a1) ** ((sp + 36) ↦ₘ b1))
    ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a1 &&& b1)) ** (.x6 ↦ᵣ b1) **
     ((sp + 4) ↦ₘ a1) ** ((sp + 36) ↦ₘ (a1 &&& b1))) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) L1
  clear L1
  -- Limb 2: and_limb_spec at base+32, offsets 8 and 40
  have L2_raw := and_limb_spec 8 40 sp a2 b2 (a1 &&& b1) b1 (base + 32) hvm8 hvm40
  simp only [signExtend12_8, signExtend12_40] at L2_raw
  rw [show (base + 32 : Addr) + 4 = base + 36 from by bv_omega,
      show (base + 32 : Addr) + 8 = base + 40 from by bv_omega,
      show (base + 32 : Addr) + 12 = base + 44 from by bv_omega,
      show (base + 32 : Addr) + 16 = base + 48 from by bv_omega] at L2_raw
  have L2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
     ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
     ((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
     ((base + 24) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
     ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
     ((base + 56) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
     ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
     ((base + 72) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
     ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
     ((base + 88) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
     ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
     ((base + 104) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
     ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
     ((base + 120) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60) **
     ((base + 128) ↦ᵢ .ADDI .x12 .x12 32))
    (by pcFree) L2_raw
  clear L2_raw
  have L2' : cpsTriple (base + 32) (base + 48)
    ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a1 &&& b1)) ** (.x6 ↦ᵣ b1) **
     ((sp + 8) ↦ₘ a2) ** ((sp + 40) ↦ₘ b2))
    ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a2 &&& b2)) ** (.x6 ↦ᵣ b2) **
     ((sp + 8) ↦ₘ a2) ** ((sp + 40) ↦ₘ (a2 &&& b2))) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) L2
  clear L2
  -- Limb 3: and_limb_spec at base+48, offsets 12 and 44
  have L3_raw := and_limb_spec 12 44 sp a3 b3 (a2 &&& b2) b2 (base + 48) hvm12 hvm44
  simp only [signExtend12_12, signExtend12_44] at L3_raw
  rw [show (base + 48 : Addr) + 4 = base + 52 from by bv_omega,
      show (base + 48 : Addr) + 8 = base + 56 from by bv_omega,
      show (base + 48 : Addr) + 12 = base + 60 from by bv_omega,
      show (base + 48 : Addr) + 16 = base + 64 from by bv_omega] at L3_raw
  have L3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
     ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
     ((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
     ((base + 24) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
     ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
     ((base + 40) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
     ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
     ((base + 72) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
     ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
     ((base + 88) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
     ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
     ((base + 104) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
     ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
     ((base + 120) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60) **
     ((base + 128) ↦ᵢ .ADDI .x12 .x12 32))
    (by pcFree) L3_raw
  clear L3_raw
  have L3' : cpsTriple (base + 48) (base + 64)
    ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a2 &&& b2)) ** (.x6 ↦ᵣ b2) **
     ((sp + 12) ↦ₘ a3) ** ((sp + 44) ↦ₘ b3))
    ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a3 &&& b3)) ** (.x6 ↦ᵣ b3) **
     ((sp + 12) ↦ₘ a3) ** ((sp + 44) ↦ₘ (a3 &&& b3))) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) L3
  clear L3
  -- Limb 4: and_limb_spec at base+64, offsets 16 and 48
  have L4_raw := and_limb_spec 16 48 sp a4 b4 (a3 &&& b3) b3 (base + 64) hvm16 hvm48
  simp only [signExtend12_16, signExtend12_48] at L4_raw
  rw [show (base + 64 : Addr) + 4 = base + 68 from by bv_omega,
      show (base + 64 : Addr) + 8 = base + 72 from by bv_omega,
      show (base + 64 : Addr) + 12 = base + 76 from by bv_omega,
      show (base + 64 : Addr) + 16 = base + 80 from by bv_omega] at L4_raw
  have L4 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
     ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
     ((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
     ((base + 24) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
     ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
     ((base + 40) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
     ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
     ((base + 56) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
     ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
     ((base + 88) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
     ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
     ((base + 104) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
     ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
     ((base + 120) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60) **
     ((base + 128) ↦ᵢ .ADDI .x12 .x12 32))
    (by pcFree) L4_raw
  clear L4_raw
  have L4' : cpsTriple (base + 64) (base + 80)
    ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a3 &&& b3)) ** (.x6 ↦ᵣ b3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 48) ↦ₘ b4))
    ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a4 &&& b4)) ** (.x6 ↦ᵣ b4) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 48) ↦ₘ (a4 &&& b4))) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) L4
  clear L4
  -- Limb 5: and_limb_spec at base+80, offsets 20 and 52
  have L5_raw := and_limb_spec 20 52 sp a5 b5 (a4 &&& b4) b4 (base + 80) hvm20 hvm52
  simp only [signExtend12_20, signExtend12_52] at L5_raw
  rw [show (base + 80 : Addr) + 4 = base + 84 from by bv_omega,
      show (base + 80 : Addr) + 8 = base + 88 from by bv_omega,
      show (base + 80 : Addr) + 12 = base + 92 from by bv_omega,
      show (base + 80 : Addr) + 16 = base + 96 from by bv_omega] at L5_raw
  have L5 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
     ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
     ((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
     ((base + 24) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
     ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
     ((base + 40) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
     ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
     ((base + 56) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
     ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
     ((base + 72) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
     ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
     ((base + 104) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
     ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
     ((base + 120) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60) **
     ((base + 128) ↦ᵢ .ADDI .x12 .x12 32))
    (by pcFree) L5_raw
  clear L5_raw
  have L5' : cpsTriple (base + 80) (base + 96)
    ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a4 &&& b4)) ** (.x6 ↦ᵣ b4) **
     ((sp + 20) ↦ₘ a5) ** ((sp + 52) ↦ₘ b5))
    ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a5 &&& b5)) ** (.x6 ↦ᵣ b5) **
     ((sp + 20) ↦ₘ a5) ** ((sp + 52) ↦ₘ (a5 &&& b5))) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) L5
  clear L5
  -- Limb 6: and_limb_spec at base+96, offsets 24 and 56
  have L6_raw := and_limb_spec 24 56 sp a6 b6 (a5 &&& b5) b5 (base + 96) hvm24 hvm56
  simp only [signExtend12_24, signExtend12_56] at L6_raw
  rw [show (base + 96 : Addr) + 4 = base + 100 from by bv_omega,
      show (base + 96 : Addr) + 8 = base + 104 from by bv_omega,
      show (base + 96 : Addr) + 12 = base + 108 from by bv_omega,
      show (base + 96 : Addr) + 16 = base + 112 from by bv_omega] at L6_raw
  have L6 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
     ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
     ((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
     ((base + 24) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
     ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
     ((base + 40) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
     ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
     ((base + 56) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
     ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
     ((base + 72) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
     ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
     ((base + 88) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
     ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
     ((base + 120) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60) **
     ((base + 128) ↦ᵢ .ADDI .x12 .x12 32))
    (by pcFree) L6_raw
  clear L6_raw
  have L6' : cpsTriple (base + 96) (base + 112)
    ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a5 &&& b5)) ** (.x6 ↦ᵣ b5) **
     ((sp + 24) ↦ₘ a6) ** ((sp + 56) ↦ₘ b6))
    ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a6 &&& b6)) ** (.x6 ↦ᵣ b6) **
     ((sp + 24) ↦ₘ a6) ** ((sp + 56) ↦ₘ (a6 &&& b6))) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) L6
  clear L6
  -- Limb 7: and_limb_spec at base+112, offsets 28 and 60
  have L7_raw := and_limb_spec 28 60 sp a7 b7 (a6 &&& b6) b6 (base + 112) hvm28 hvm60
  simp only [signExtend12_28, signExtend12_60] at L7_raw
  rw [show (base + 112 : Addr) + 4 = base + 116 from by bv_omega,
      show (base + 112 : Addr) + 8 = base + 120 from by bv_omega,
      show (base + 112 : Addr) + 12 = base + 124 from by bv_omega,
      show (base + 112 : Addr) + 16 = base + 128 from by bv_omega] at L7_raw
  have L7 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
     ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
     ((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
     ((base + 24) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
     ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
     ((base + 40) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
     ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
     ((base + 56) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
     ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
     ((base + 72) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
     ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
     ((base + 88) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
     ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
     ((base + 104) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
     ((base + 128) ↦ᵢ .ADDI .x12 .x12 32))
    (by pcFree) L7_raw
  clear L7_raw
  have L7' : cpsTriple (base + 112) (base + 128)
    ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a6 &&& b6)) ** (.x6 ↦ᵣ b6) **
     ((sp + 28) ↦ₘ a7) ** ((sp + 60) ↦ₘ b7))
    ((F ** ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)) **
     (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a7 &&& b7)) ** (.x6 ↦ᵣ b7) **
     ((sp + 28) ↦ₘ a7) ** ((sp + 60) ↦ₘ (a7 &&& b7))) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) L7
  clear L7
  -- Apply binary_bitwise_spec with op = (· &&& ·)
  have h_bw := binary_bitwise_spec sp base (· &&& ·)
    a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6
    F hF L0' L1' L2' L3' L4' L5' L6' L7' hvalid
  -- Permute to match the goal
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) h_bw

-- ============================================================================
-- Stack-level AND spec
-- ============================================================================

set_option maxHeartbeats 6400000 in
/-- Stack-level 256-bit EVM AND: operates on two EvmWords via evmWordIs.
    Uses ValidMemRange for clean hypotheses. -/
theorem evm_and_stack_spec (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word)
    (hvalid : ValidMemRange sp 16) :
    cpsTriple base (base + 132)
      (-- Limb 0 code
       (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
       ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
       -- Limb 1 code
       ((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
       ((base + 24) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
       -- Limb 2 code
       ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
       ((base + 40) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
       -- Limb 3 code
       ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
       ((base + 56) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
       -- Limb 4 code
       ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
       ((base + 72) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
       -- Limb 5 code
       ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
       ((base + 88) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
       -- Limb 6 code
       ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
       ((base + 104) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
       -- Limb 7 code
       ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
       ((base + 120) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60) **
       -- ADDI
       ((base + 128) ↦ᵢ .ADDI .x12 .x12 32) **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (-- Same code (preserved)
       (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
       ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
       ((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
       ((base + 24) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
       ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
       ((base + 40) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
       ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
       ((base + 56) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
       ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
       ((base + 72) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
       ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
       ((base + 88) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
       ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
       ((base + 104) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
       ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
       ((base + 120) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60) **
       ((base + 128) ↦ᵢ .ADDI .x12 .x12 32) **
       -- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a.getLimb 7 &&& b.getLimb 7)) ** (.x6 ↦ᵣ b.getLimb 7) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a &&& b)) := by
  -- Address helpers for evmWordIs (sp + 32) unfolding
  have haddr32 : sp + (32 : Addr) + 4 = sp + 36 := by bv_omega
  have haddr36 : sp + (32 : Addr) + 8 = sp + 40 := by bv_omega
  have haddr40 : sp + (32 : Addr) + 12 = sp + 44 := by bv_omega
  have haddr44 : sp + (32 : Addr) + 16 = sp + 48 := by bv_omega
  have haddr48 : sp + (32 : Addr) + 20 = sp + 52 := by bv_omega
  have haddr52 : sp + (32 : Addr) + 24 = sp + 56 := by bv_omega
  have haddr56 : sp + (32 : Addr) + 28 = sp + 60 := by bv_omega
  -- Apply evm_and_spec with individual limbs
  have h_main := evm_and_spec sp base
    (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3)
    (a.getLimb 4) (a.getLimb 5) (a.getLimb 6) (a.getLimb 7)
    (b.getLimb 0) (b.getLimb 1) (b.getLimb 2) (b.getLimb 3)
    (b.getLimb 4) (b.getLimb 5) (b.getLimb 6) (b.getLimb 7)
    v7 v6 hvalid
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by
      simp only [evmWordIs, haddr32, haddr36, haddr40, haddr44, haddr48, haddr52, haddr56] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs, EvmWord.getLimb_and, haddr32, haddr36, haddr40, haddr44, haddr48, haddr52, haddr56]
      xperm_hyp hq)
    h_main

end EvmAsm
