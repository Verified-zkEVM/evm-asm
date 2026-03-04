/-
  EvmAsm.Evm.ArithmeticSpec

  Full 256-bit EVM arithmetic specs (ADD, SUB) composed from per-limb specs.
  Each composes 8 per-limb specs + ADDI sp adjustment into a single cpsTriple.
  62 instructions total with instrAt in both P and Q.
-/

import EvmAsm.Evm.Arithmetic
import EvmAsm.Tactics.XSimp

open EvmAsm.Tactics

namespace EvmAsm

-- ============================================================================
-- Helpers for full specs
-- ============================================================================

local macro "bv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]))

private theorem cpsTriple_addr_eq {P Q : Assertion}
    {s1 s2 e1 e2 : Addr} (hs : s1 = s2) (he : e1 = e2)
    (h : cpsTriple s1 e1 P Q) :
    cpsTriple s2 e2 P Q := by
  subst hs; subst he; exact h

-- ============================================================================
-- Full 256-bit ADD spec
-- ============================================================================

set_option maxHeartbeats 6400000 in
/-- Full 256-bit EVM ADD: composes 8 per-limb ADD specs + ADDI sp adjustment.
    62 instructions total. Pops 2 stack words (A at sp, B at sp+32),
    writes A + B to sp+32..sp+60, advances sp by 32.
    Carry propagates through limbs via x5. -/
theorem evm_add_spec (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 v5 v11 : Word)
    (hvalid : ValidMemRange sp 16) :
    -- Carry chain definitions
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    let carry3 := carry3a ||| carry3b
    let psum4 := a4 + b4
    let carry4a := if BitVec.ult psum4 b4 then (1 : Word) else 0
    let result4 := psum4 + carry3
    let carry4b := if BitVec.ult result4 carry3 then (1 : Word) else 0
    let carry4 := carry4a ||| carry4b
    let psum5 := a5 + b5
    let carry5a := if BitVec.ult psum5 b5 then (1 : Word) else 0
    let result5 := psum5 + carry4
    let carry5b := if BitVec.ult result5 carry4 then (1 : Word) else 0
    let carry5 := carry5a ||| carry5b
    let psum6 := a6 + b6
    let carry6a := if BitVec.ult psum6 b6 then (1 : Word) else 0
    let result6 := psum6 + carry5
    let carry6b := if BitVec.ult result6 carry5 then (1 : Word) else 0
    let carry6 := carry6a ||| carry6b
    let psum7 := a7 + b7
    let carry7a := if BitVec.ult psum7 b7 then (1 : Word) else 0
    let result7 := psum7 + carry6
    let carry7b := if BitVec.ult result7 carry6 then (1 : Word) else 0
    let carry7 := carry7a ||| carry7b
    cpsTriple base (base + 248)
      (-- Limb 0 code (5 instructions: base+0..base+16)
       (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
       ((base + 8) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SLTU .x5 .x7 .x6) **
       ((base + 16) ↦ᵢ .SW .x12 .x7 32) **
       -- Limb 1 code (8 instructions: base+20..base+48)
       ((base + 20) ↦ᵢ .LW .x7 .x12 4) ** ((base + 24) ↦ᵢ .LW .x6 .x12 36) **
       ((base + 28) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 32) ↦ᵢ .SLTU .x11 .x7 .x6) **
       ((base + 36) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 40) ↦ᵢ .SLTU .x6 .x7 .x5) **
       ((base + 44) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 48) ↦ᵢ .SW .x12 .x7 36) **
       -- Limb 2 code (8 instructions: base+52..base+80)
       ((base + 52) ↦ᵢ .LW .x7 .x12 8) ** ((base + 56) ↦ᵢ .LW .x6 .x12 40) **
       ((base + 60) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 64) ↦ᵢ .SLTU .x11 .x7 .x6) **
       ((base + 68) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 72) ↦ᵢ .SLTU .x6 .x7 .x5) **
       ((base + 76) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 80) ↦ᵢ .SW .x12 .x7 40) **
       -- Limb 3 code (8 instructions: base+84..base+112)
       ((base + 84) ↦ᵢ .LW .x7 .x12 12) ** ((base + 88) ↦ᵢ .LW .x6 .x12 44) **
       ((base + 92) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 96) ↦ᵢ .SLTU .x11 .x7 .x6) **
       ((base + 100) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 104) ↦ᵢ .SLTU .x6 .x7 .x5) **
       ((base + 108) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 112) ↦ᵢ .SW .x12 .x7 44) **
       -- Limb 4 code (8 instructions: base+116..base+144)
       ((base + 116) ↦ᵢ .LW .x7 .x12 16) ** ((base + 120) ↦ᵢ .LW .x6 .x12 48) **
       ((base + 124) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 128) ↦ᵢ .SLTU .x11 .x7 .x6) **
       ((base + 132) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 136) ↦ᵢ .SLTU .x6 .x7 .x5) **
       ((base + 140) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 144) ↦ᵢ .SW .x12 .x7 48) **
       -- Limb 5 code (8 instructions: base+148..base+176)
       ((base + 148) ↦ᵢ .LW .x7 .x12 20) ** ((base + 152) ↦ᵢ .LW .x6 .x12 52) **
       ((base + 156) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 160) ↦ᵢ .SLTU .x11 .x7 .x6) **
       ((base + 164) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 168) ↦ᵢ .SLTU .x6 .x7 .x5) **
       ((base + 172) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 176) ↦ᵢ .SW .x12 .x7 52) **
       -- Limb 6 code (8 instructions: base+180..base+208)
       ((base + 180) ↦ᵢ .LW .x7 .x12 24) ** ((base + 184) ↦ᵢ .LW .x6 .x12 56) **
       ((base + 188) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 192) ↦ᵢ .SLTU .x11 .x7 .x6) **
       ((base + 196) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 200) ↦ᵢ .SLTU .x6 .x7 .x5) **
       ((base + 204) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 208) ↦ᵢ .SW .x12 .x7 56) **
       -- Limb 7 code (8 instructions: base+212..base+240)
       ((base + 212) ↦ᵢ .LW .x7 .x12 28) ** ((base + 216) ↦ᵢ .LW .x6 .x12 60) **
       ((base + 220) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 224) ↦ᵢ .SLTU .x11 .x7 .x6) **
       ((base + 228) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 232) ↦ᵢ .SLTU .x6 .x7 .x5) **
       ((base + 236) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 240) ↦ᵢ .SW .x12 .x7 60) **
       -- ADDI instruction
       ((base + 244) ↦ᵢ .ADDI .x12 .x12 32) **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      (-- Same code (preserved)
       (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
       ((base + 8) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SLTU .x5 .x7 .x6) **
       ((base + 16) ↦ᵢ .SW .x12 .x7 32) **
       ((base + 20) ↦ᵢ .LW .x7 .x12 4) ** ((base + 24) ↦ᵢ .LW .x6 .x12 36) **
       ((base + 28) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 32) ↦ᵢ .SLTU .x11 .x7 .x6) **
       ((base + 36) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 40) ↦ᵢ .SLTU .x6 .x7 .x5) **
       ((base + 44) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 48) ↦ᵢ .SW .x12 .x7 36) **
       ((base + 52) ↦ᵢ .LW .x7 .x12 8) ** ((base + 56) ↦ᵢ .LW .x6 .x12 40) **
       ((base + 60) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 64) ↦ᵢ .SLTU .x11 .x7 .x6) **
       ((base + 68) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 72) ↦ᵢ .SLTU .x6 .x7 .x5) **
       ((base + 76) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 80) ↦ᵢ .SW .x12 .x7 40) **
       ((base + 84) ↦ᵢ .LW .x7 .x12 12) ** ((base + 88) ↦ᵢ .LW .x6 .x12 44) **
       ((base + 92) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 96) ↦ᵢ .SLTU .x11 .x7 .x6) **
       ((base + 100) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 104) ↦ᵢ .SLTU .x6 .x7 .x5) **
       ((base + 108) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 112) ↦ᵢ .SW .x12 .x7 44) **
       ((base + 116) ↦ᵢ .LW .x7 .x12 16) ** ((base + 120) ↦ᵢ .LW .x6 .x12 48) **
       ((base + 124) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 128) ↦ᵢ .SLTU .x11 .x7 .x6) **
       ((base + 132) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 136) ↦ᵢ .SLTU .x6 .x7 .x5) **
       ((base + 140) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 144) ↦ᵢ .SW .x12 .x7 48) **
       ((base + 148) ↦ᵢ .LW .x7 .x12 20) ** ((base + 152) ↦ᵢ .LW .x6 .x12 52) **
       ((base + 156) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 160) ↦ᵢ .SLTU .x11 .x7 .x6) **
       ((base + 164) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 168) ↦ᵢ .SLTU .x6 .x7 .x5) **
       ((base + 172) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 176) ↦ᵢ .SW .x12 .x7 52) **
       ((base + 180) ↦ᵢ .LW .x7 .x12 24) ** ((base + 184) ↦ᵢ .LW .x6 .x12 56) **
       ((base + 188) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 192) ↦ᵢ .SLTU .x11 .x7 .x6) **
       ((base + 196) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 200) ↦ᵢ .SLTU .x6 .x7 .x5) **
       ((base + 204) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 208) ↦ᵢ .SW .x12 .x7 56) **
       ((base + 212) ↦ᵢ .LW .x7 .x12 28) ** ((base + 216) ↦ᵢ .LW .x6 .x12 60) **
       ((base + 220) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 224) ↦ᵢ .SLTU .x11 .x7 .x6) **
       ((base + 228) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 232) ↦ᵢ .SLTU .x6 .x7 .x5) **
       ((base + 236) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 240) ↦ᵢ .SW .x12 .x7 60) **
       ((base + 244) ↦ᵢ .ADDI .x12 .x12 32) **
       -- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result7) ** (.x6 ↦ᵣ carry7b) ** (.x5 ↦ᵣ carry7) ** (.x11 ↦ᵣ carry7a) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ result2) ** ((sp + 44) ↦ₘ result3) **
       ((sp + 48) ↦ₘ result4) ** ((sp + 52) ↦ₘ result5) ** ((sp + 56) ↦ₘ result6) ** ((sp + 60) ↦ₘ result7)) := by
  -- Introduce let bindings
  intro sum0; intro carry0; intro psum1; intro carry1a; intro result1; intro carry1b; intro carry1
  intro psum2; intro carry2a; intro result2; intro carry2b; intro carry2
  intro psum3; intro carry3a; intro result3; intro carry3b; intro carry3
  intro psum4; intro carry4a; intro result4; intro carry4b; intro carry4
  intro psum5; intro carry5a; intro result5; intro carry5b; intro carry5
  intro psum6; intro carry6a; intro result6; intro carry6b; intro carry6
  intro psum7; intro carry7a; intro result7; intro carry7b; intro carry7
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
  -- Define F as all 61 per-limb instrAt (excluding ADDI)
  let F : Assertion :=
    -- Limb 0 (5 instrAt)
    (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
    ((base + 8) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SLTU .x5 .x7 .x6) **
    ((base + 16) ↦ᵢ .SW .x12 .x7 32) **
    -- Limb 1 (8 instrAt)
    ((base + 20) ↦ᵢ .LW .x7 .x12 4) ** ((base + 24) ↦ᵢ .LW .x6 .x12 36) **
    ((base + 28) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 32) ↦ᵢ .SLTU .x11 .x7 .x6) **
    ((base + 36) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 40) ↦ᵢ .SLTU .x6 .x7 .x5) **
    ((base + 44) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 48) ↦ᵢ .SW .x12 .x7 36) **
    -- Limb 2 (8 instrAt)
    ((base + 52) ↦ᵢ .LW .x7 .x12 8) ** ((base + 56) ↦ᵢ .LW .x6 .x12 40) **
    ((base + 60) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 64) ↦ᵢ .SLTU .x11 .x7 .x6) **
    ((base + 68) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 72) ↦ᵢ .SLTU .x6 .x7 .x5) **
    ((base + 76) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 80) ↦ᵢ .SW .x12 .x7 40) **
    -- Limb 3 (8 instrAt)
    ((base + 84) ↦ᵢ .LW .x7 .x12 12) ** ((base + 88) ↦ᵢ .LW .x6 .x12 44) **
    ((base + 92) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 96) ↦ᵢ .SLTU .x11 .x7 .x6) **
    ((base + 100) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 104) ↦ᵢ .SLTU .x6 .x7 .x5) **
    ((base + 108) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 112) ↦ᵢ .SW .x12 .x7 44) **
    -- Limb 4 (8 instrAt)
    ((base + 116) ↦ᵢ .LW .x7 .x12 16) ** ((base + 120) ↦ᵢ .LW .x6 .x12 48) **
    ((base + 124) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 128) ↦ᵢ .SLTU .x11 .x7 .x6) **
    ((base + 132) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 136) ↦ᵢ .SLTU .x6 .x7 .x5) **
    ((base + 140) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 144) ↦ᵢ .SW .x12 .x7 48) **
    -- Limb 5 (8 instrAt)
    ((base + 148) ↦ᵢ .LW .x7 .x12 20) ** ((base + 152) ↦ᵢ .LW .x6 .x12 52) **
    ((base + 156) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 160) ↦ᵢ .SLTU .x11 .x7 .x6) **
    ((base + 164) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 168) ↦ᵢ .SLTU .x6 .x7 .x5) **
    ((base + 172) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 176) ↦ᵢ .SW .x12 .x7 52) **
    -- Limb 6 (8 instrAt)
    ((base + 180) ↦ᵢ .LW .x7 .x12 24) ** ((base + 184) ↦ᵢ .LW .x6 .x12 56) **
    ((base + 188) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 192) ↦ᵢ .SLTU .x11 .x7 .x6) **
    ((base + 196) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 200) ↦ᵢ .SLTU .x6 .x7 .x5) **
    ((base + 204) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 208) ↦ᵢ .SW .x12 .x7 56) **
    -- Limb 7 (8 instrAt)
    ((base + 212) ↦ᵢ .LW .x7 .x12 28) ** ((base + 216) ↦ᵢ .LW .x6 .x12 60) **
    ((base + 220) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 224) ↦ᵢ .SLTU .x11 .x7 .x6) **
    ((base + 228) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 232) ↦ᵢ .SLTU .x6 .x7 .x5) **
    ((base + 236) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 240) ↦ᵢ .SW .x12 .x7 60)
  have hF : F.pcFree := by pcFree
  -- Abbreviation for G = F ** ADDI instrAt
  let G := F ** ((base + 244) ↦ᵢ .ADDI .x12 .x12 32)
  have hG : G.pcFree := pcFree_sepConj hF (by pcFree)
  -- Limb 0: add_limb0_spec at base (5 instr, base -> base+20)
  have L0_raw := add_limb0_spec 0 32 sp a0 b0 v7 v6 v5 base hvm0 hvm32
  simp only [signExtend12_0] at L0_raw
  rw [show sp + (0 : Word) = sp from by bv_addr] at L0_raw
  simp only [signExtend12_32] at L0_raw
  -- Frame L0 with other-limb instrAt + ADDI (only instrAt, 57 conjuncts)
  have L0 := cpsTriple_frame_left _ _ _ _
    (((base + 20) ↦ᵢ .LW .x7 .x12 4) ** ((base + 24) ↦ᵢ .LW .x6 .x12 36) **
     ((base + 28) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 32) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 36) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 40) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 44) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 48) ↦ᵢ .SW .x12 .x7 36) **
     ((base + 52) ↦ᵢ .LW .x7 .x12 8) ** ((base + 56) ↦ᵢ .LW .x6 .x12 40) **
     ((base + 60) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 64) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 68) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 72) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 76) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 80) ↦ᵢ .SW .x12 .x7 40) **
     ((base + 84) ↦ᵢ .LW .x7 .x12 12) ** ((base + 88) ↦ᵢ .LW .x6 .x12 44) **
     ((base + 92) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 96) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 100) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 104) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 108) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 112) ↦ᵢ .SW .x12 .x7 44) **
     ((base + 116) ↦ᵢ .LW .x7 .x12 16) ** ((base + 120) ↦ᵢ .LW .x6 .x12 48) **
     ((base + 124) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 128) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 132) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 136) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 140) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 144) ↦ᵢ .SW .x12 .x7 48) **
     ((base + 148) ↦ᵢ .LW .x7 .x12 20) ** ((base + 152) ↦ᵢ .LW .x6 .x12 52) **
     ((base + 156) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 160) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 164) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 168) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 172) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 176) ↦ᵢ .SW .x12 .x7 52) **
     ((base + 180) ↦ᵢ .LW .x7 .x12 24) ** ((base + 184) ↦ᵢ .LW .x6 .x12 56) **
     ((base + 188) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 192) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 196) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 200) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 204) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 208) ↦ᵢ .SW .x12 .x7 56) **
     ((base + 212) ↦ᵢ .LW .x7 .x12 28) ** ((base + 216) ↦ᵢ .LW .x6 .x12 60) **
     ((base + 220) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 224) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 228) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 232) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 236) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 240) ↦ᵢ .SW .x12 .x7 60) **
     ((base + 244) ↦ᵢ .ADDI .x12 .x12 32))
    (by pcFree) L0_raw
  clear L0_raw
  -- Permute L0 to (G ** regs ** 2mem) form, then frame with 14 mem + x11
  have L0' : cpsTriple base (base + 20)
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ sum0) ** (.x6 ↦ᵣ b0) ** (.x5 ↦ᵣ carry0) ** (.x11 ↦ᵣ v11) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L0)
  clear L0
  -- Limb 1: add_limb_carry_spec at base+20 (8 instr, base+20 -> base+52)
  have L1_raw := add_limb_carry_spec 4 36 sp a1 b1 sum0 b0 carry0 v11 (base + 20) hvm4 hvm36
  simp only [signExtend12_4, signExtend12_36] at L1_raw
  rw [show (base + 20 : Addr) + 4 = base + 24 from by bv_omega,
      show (base + 20 : Addr) + 8 = base + 28 from by bv_omega,
      show (base + 20 : Addr) + 12 = base + 32 from by bv_omega,
      show (base + 20 : Addr) + 16 = base + 36 from by bv_omega,
      show (base + 20 : Addr) + 20 = base + 40 from by bv_omega,
      show (base + 20 : Addr) + 24 = base + 44 from by bv_omega,
      show (base + 20 : Addr) + 28 = base + 48 from by bv_omega,
      show (base + 20 : Addr) + 32 = base + 52 from by bv_omega] at L1_raw
  have L1 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
     ((base + 8) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SLTU .x5 .x7 .x6) **
     ((base + 16) ↦ᵢ .SW .x12 .x7 32) **
     ((base + 52) ↦ᵢ .LW .x7 .x12 8) ** ((base + 56) ↦ᵢ .LW .x6 .x12 40) **
     ((base + 60) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 64) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 68) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 72) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 76) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 80) ↦ᵢ .SW .x12 .x7 40) **
     ((base + 84) ↦ᵢ .LW .x7 .x12 12) ** ((base + 88) ↦ᵢ .LW .x6 .x12 44) **
     ((base + 92) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 96) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 100) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 104) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 108) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 112) ↦ᵢ .SW .x12 .x7 44) **
     ((base + 116) ↦ᵢ .LW .x7 .x12 16) ** ((base + 120) ↦ᵢ .LW .x6 .x12 48) **
     ((base + 124) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 128) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 132) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 136) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 140) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 144) ↦ᵢ .SW .x12 .x7 48) **
     ((base + 148) ↦ᵢ .LW .x7 .x12 20) ** ((base + 152) ↦ᵢ .LW .x6 .x12 52) **
     ((base + 156) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 160) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 164) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 168) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 172) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 176) ↦ᵢ .SW .x12 .x7 52) **
     ((base + 180) ↦ᵢ .LW .x7 .x12 24) ** ((base + 184) ↦ᵢ .LW .x6 .x12 56) **
     ((base + 188) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 192) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 196) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 200) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 204) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 208) ↦ᵢ .SW .x12 .x7 56) **
     ((base + 212) ↦ᵢ .LW .x7 .x12 28) ** ((base + 216) ↦ᵢ .LW .x6 .x12 60) **
     ((base + 220) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 224) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 228) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 232) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 236) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 240) ↦ᵢ .SW .x12 .x7 60) **
     ((base + 244) ↦ᵢ .ADDI .x12 .x12 32))
    (by pcFree) L1_raw
  clear L1_raw
  have L1' : cpsTriple (base + 20) (base + 52)
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ sum0) ** (.x6 ↦ᵣ b0) ** (.x5 ↦ᵣ carry0) ** (.x11 ↦ᵣ v11) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result1) ** (.x6 ↦ᵣ carry1b) ** (.x5 ↦ᵣ carry1) ** (.x11 ↦ᵣ carry1a) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L1)
  clear L1
  -- Compose limbs 0 and 1
  have S01 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) L0' L1'
  clear L0' L1'
  have S01' := cpsTriple_addr_eq (rfl) (by bv_omega : (base + 52 : Addr) = base + 52) S01
  clear S01
  -- Limb 2: add_limb_carry_spec at base+52 (8 instr, base+52 -> base+84)
  have L2_raw := add_limb_carry_spec 8 40 sp a2 b2 result1 carry1b carry1 carry1a (base + 52) hvm8 hvm40
  simp only [signExtend12_8, signExtend12_40] at L2_raw
  rw [show (base + 52 : Addr) + 4 = base + 56 from by bv_omega,
      show (base + 52 : Addr) + 8 = base + 60 from by bv_omega,
      show (base + 52 : Addr) + 12 = base + 64 from by bv_omega,
      show (base + 52 : Addr) + 16 = base + 68 from by bv_omega,
      show (base + 52 : Addr) + 20 = base + 72 from by bv_omega,
      show (base + 52 : Addr) + 24 = base + 76 from by bv_omega,
      show (base + 52 : Addr) + 28 = base + 80 from by bv_omega,
      show (base + 52 : Addr) + 32 = base + 84 from by bv_omega] at L2_raw
  have L2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
     ((base + 8) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SLTU .x5 .x7 .x6) **
     ((base + 16) ↦ᵢ .SW .x12 .x7 32) **
     ((base + 20) ↦ᵢ .LW .x7 .x12 4) ** ((base + 24) ↦ᵢ .LW .x6 .x12 36) **
     ((base + 28) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 32) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 36) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 40) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 44) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 48) ↦ᵢ .SW .x12 .x7 36) **
     ((base + 84) ↦ᵢ .LW .x7 .x12 12) ** ((base + 88) ↦ᵢ .LW .x6 .x12 44) **
     ((base + 92) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 96) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 100) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 104) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 108) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 112) ↦ᵢ .SW .x12 .x7 44) **
     ((base + 116) ↦ᵢ .LW .x7 .x12 16) ** ((base + 120) ↦ᵢ .LW .x6 .x12 48) **
     ((base + 124) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 128) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 132) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 136) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 140) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 144) ↦ᵢ .SW .x12 .x7 48) **
     ((base + 148) ↦ᵢ .LW .x7 .x12 20) ** ((base + 152) ↦ᵢ .LW .x6 .x12 52) **
     ((base + 156) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 160) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 164) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 168) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 172) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 176) ↦ᵢ .SW .x12 .x7 52) **
     ((base + 180) ↦ᵢ .LW .x7 .x12 24) ** ((base + 184) ↦ᵢ .LW .x6 .x12 56) **
     ((base + 188) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 192) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 196) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 200) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 204) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 208) ↦ᵢ .SW .x12 .x7 56) **
     ((base + 212) ↦ᵢ .LW .x7 .x12 28) ** ((base + 216) ↦ᵢ .LW .x6 .x12 60) **
     ((base + 220) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 224) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 228) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 232) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 236) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 240) ↦ᵢ .SW .x12 .x7 60) **
     ((base + 244) ↦ᵢ .ADDI .x12 .x12 32))
    (by pcFree) L2_raw
  clear L2_raw
  have L2' : cpsTriple (base + 52) (base + 84)
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result1) ** (.x6 ↦ᵣ carry1b) ** (.x5 ↦ᵣ carry1) ** (.x11 ↦ᵣ carry1a) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result2) ** (.x6 ↦ᵣ carry2b) ** (.x5 ↦ᵣ carry2) ** (.x11 ↦ᵣ carry2a) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ result2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L2)
  clear L2
  have S012 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S01' L2'
  clear S01' L2'
  have S012' := cpsTriple_addr_eq (rfl) (by bv_omega : (base + 84 : Addr) = base + 84) S012
  clear S012
  -- Limb 3: add_limb_carry_spec at base+84 (8 instr, base+84 -> base+116)
  have L3_raw := add_limb_carry_spec 12 44 sp a3 b3 result2 carry2b carry2 carry2a (base + 84) hvm12 hvm44
  simp only [signExtend12_12, signExtend12_44] at L3_raw
  rw [show (base + 84 : Addr) + 4 = base + 88 from by bv_omega,
      show (base + 84 : Addr) + 8 = base + 92 from by bv_omega,
      show (base + 84 : Addr) + 12 = base + 96 from by bv_omega,
      show (base + 84 : Addr) + 16 = base + 100 from by bv_omega,
      show (base + 84 : Addr) + 20 = base + 104 from by bv_omega,
      show (base + 84 : Addr) + 24 = base + 108 from by bv_omega,
      show (base + 84 : Addr) + 28 = base + 112 from by bv_omega,
      show (base + 84 : Addr) + 32 = base + 116 from by bv_omega] at L3_raw
  have L3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
     ((base + 8) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SLTU .x5 .x7 .x6) **
     ((base + 16) ↦ᵢ .SW .x12 .x7 32) **
     ((base + 20) ↦ᵢ .LW .x7 .x12 4) ** ((base + 24) ↦ᵢ .LW .x6 .x12 36) **
     ((base + 28) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 32) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 36) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 40) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 44) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 48) ↦ᵢ .SW .x12 .x7 36) **
     ((base + 52) ↦ᵢ .LW .x7 .x12 8) ** ((base + 56) ↦ᵢ .LW .x6 .x12 40) **
     ((base + 60) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 64) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 68) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 72) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 76) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 80) ↦ᵢ .SW .x12 .x7 40) **
     ((base + 116) ↦ᵢ .LW .x7 .x12 16) ** ((base + 120) ↦ᵢ .LW .x6 .x12 48) **
     ((base + 124) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 128) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 132) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 136) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 140) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 144) ↦ᵢ .SW .x12 .x7 48) **
     ((base + 148) ↦ᵢ .LW .x7 .x12 20) ** ((base + 152) ↦ᵢ .LW .x6 .x12 52) **
     ((base + 156) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 160) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 164) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 168) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 172) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 176) ↦ᵢ .SW .x12 .x7 52) **
     ((base + 180) ↦ᵢ .LW .x7 .x12 24) ** ((base + 184) ↦ᵢ .LW .x6 .x12 56) **
     ((base + 188) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 192) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 196) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 200) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 204) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 208) ↦ᵢ .SW .x12 .x7 56) **
     ((base + 212) ↦ᵢ .LW .x7 .x12 28) ** ((base + 216) ↦ᵢ .LW .x6 .x12 60) **
     ((base + 220) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 224) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 228) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 232) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 236) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 240) ↦ᵢ .SW .x12 .x7 60) **
     ((base + 244) ↦ᵢ .ADDI .x12 .x12 32))
    (by pcFree) L3_raw
  clear L3_raw
  have L3' : cpsTriple (base + 84) (base + 116)
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result2) ** (.x6 ↦ᵣ carry2b) ** (.x5 ↦ᵣ carry2) ** (.x11 ↦ᵣ carry2a) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ result2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) ** (.x5 ↦ᵣ carry3) ** (.x11 ↦ᵣ carry3a) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ result2) ** ((sp + 44) ↦ₘ result3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L3)
  clear L3
  have S0123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S012' L3'
  clear S012' L3'
  have S0123' := cpsTriple_addr_eq (rfl) (by bv_omega : (base + 116 : Addr) = base + 116) S0123
  clear S0123
  -- Limb 4: add_limb_carry_spec at base+116 (8 instr, base+116 -> base+148)
  have L4_raw := add_limb_carry_spec 16 48 sp a4 b4 result3 carry3b carry3 carry3a (base + 116) hvm16 hvm48
  simp only [signExtend12_16, signExtend12_48] at L4_raw
  rw [show (base + 116 : Addr) + 4 = base + 120 from by bv_omega,
      show (base + 116 : Addr) + 8 = base + 124 from by bv_omega,
      show (base + 116 : Addr) + 12 = base + 128 from by bv_omega,
      show (base + 116 : Addr) + 16 = base + 132 from by bv_omega,
      show (base + 116 : Addr) + 20 = base + 136 from by bv_omega,
      show (base + 116 : Addr) + 24 = base + 140 from by bv_omega,
      show (base + 116 : Addr) + 28 = base + 144 from by bv_omega,
      show (base + 116 : Addr) + 32 = base + 148 from by bv_omega] at L4_raw
  have L4 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
     ((base + 8) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SLTU .x5 .x7 .x6) **
     ((base + 16) ↦ᵢ .SW .x12 .x7 32) **
     ((base + 20) ↦ᵢ .LW .x7 .x12 4) ** ((base + 24) ↦ᵢ .LW .x6 .x12 36) **
     ((base + 28) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 32) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 36) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 40) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 44) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 48) ↦ᵢ .SW .x12 .x7 36) **
     ((base + 52) ↦ᵢ .LW .x7 .x12 8) ** ((base + 56) ↦ᵢ .LW .x6 .x12 40) **
     ((base + 60) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 64) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 68) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 72) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 76) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 80) ↦ᵢ .SW .x12 .x7 40) **
     ((base + 84) ↦ᵢ .LW .x7 .x12 12) ** ((base + 88) ↦ᵢ .LW .x6 .x12 44) **
     ((base + 92) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 96) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 100) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 104) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 108) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 112) ↦ᵢ .SW .x12 .x7 44) **
     ((base + 148) ↦ᵢ .LW .x7 .x12 20) ** ((base + 152) ↦ᵢ .LW .x6 .x12 52) **
     ((base + 156) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 160) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 164) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 168) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 172) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 176) ↦ᵢ .SW .x12 .x7 52) **
     ((base + 180) ↦ᵢ .LW .x7 .x12 24) ** ((base + 184) ↦ᵢ .LW .x6 .x12 56) **
     ((base + 188) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 192) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 196) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 200) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 204) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 208) ↦ᵢ .SW .x12 .x7 56) **
     ((base + 212) ↦ᵢ .LW .x7 .x12 28) ** ((base + 216) ↦ᵢ .LW .x6 .x12 60) **
     ((base + 220) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 224) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 228) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 232) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 236) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 240) ↦ᵢ .SW .x12 .x7 60) **
     ((base + 244) ↦ᵢ .ADDI .x12 .x12 32))
    (by pcFree) L4_raw
  clear L4_raw
  have L4' : cpsTriple (base + 116) (base + 148)
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) ** (.x5 ↦ᵣ carry3) ** (.x11 ↦ᵣ carry3a) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ result2) ** ((sp + 44) ↦ₘ result3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result4) ** (.x6 ↦ᵣ carry4b) ** (.x5 ↦ᵣ carry4) ** (.x11 ↦ᵣ carry4a) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ result2) ** ((sp + 44) ↦ₘ result3) **
     ((sp + 48) ↦ₘ result4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L4)
  clear L4
  have S01234 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S0123' L4'
  clear S0123' L4'
  have S01234' := cpsTriple_addr_eq (rfl) (by bv_omega : (base + 148 : Addr) = base + 148) S01234
  clear S01234
  -- Limb 5: add_limb_carry_spec at base+148 (8 instr, base+148 -> base+180)
  have L5_raw := add_limb_carry_spec 20 52 sp a5 b5 result4 carry4b carry4 carry4a (base + 148) hvm20 hvm52
  simp only [signExtend12_20, signExtend12_52] at L5_raw
  rw [show (base + 148 : Addr) + 4 = base + 152 from by bv_omega,
      show (base + 148 : Addr) + 8 = base + 156 from by bv_omega,
      show (base + 148 : Addr) + 12 = base + 160 from by bv_omega,
      show (base + 148 : Addr) + 16 = base + 164 from by bv_omega,
      show (base + 148 : Addr) + 20 = base + 168 from by bv_omega,
      show (base + 148 : Addr) + 24 = base + 172 from by bv_omega,
      show (base + 148 : Addr) + 28 = base + 176 from by bv_omega,
      show (base + 148 : Addr) + 32 = base + 180 from by bv_omega] at L5_raw
  have L5 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
     ((base + 8) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SLTU .x5 .x7 .x6) **
     ((base + 16) ↦ᵢ .SW .x12 .x7 32) **
     ((base + 20) ↦ᵢ .LW .x7 .x12 4) ** ((base + 24) ↦ᵢ .LW .x6 .x12 36) **
     ((base + 28) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 32) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 36) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 40) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 44) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 48) ↦ᵢ .SW .x12 .x7 36) **
     ((base + 52) ↦ᵢ .LW .x7 .x12 8) ** ((base + 56) ↦ᵢ .LW .x6 .x12 40) **
     ((base + 60) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 64) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 68) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 72) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 76) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 80) ↦ᵢ .SW .x12 .x7 40) **
     ((base + 84) ↦ᵢ .LW .x7 .x12 12) ** ((base + 88) ↦ᵢ .LW .x6 .x12 44) **
     ((base + 92) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 96) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 100) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 104) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 108) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 112) ↦ᵢ .SW .x12 .x7 44) **
     ((base + 116) ↦ᵢ .LW .x7 .x12 16) ** ((base + 120) ↦ᵢ .LW .x6 .x12 48) **
     ((base + 124) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 128) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 132) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 136) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 140) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 144) ↦ᵢ .SW .x12 .x7 48) **
     ((base + 180) ↦ᵢ .LW .x7 .x12 24) ** ((base + 184) ↦ᵢ .LW .x6 .x12 56) **
     ((base + 188) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 192) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 196) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 200) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 204) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 208) ↦ᵢ .SW .x12 .x7 56) **
     ((base + 212) ↦ᵢ .LW .x7 .x12 28) ** ((base + 216) ↦ᵢ .LW .x6 .x12 60) **
     ((base + 220) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 224) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 228) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 232) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 236) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 240) ↦ᵢ .SW .x12 .x7 60) **
     ((base + 244) ↦ᵢ .ADDI .x12 .x12 32))
    (by pcFree) L5_raw
  clear L5_raw
  have L5' : cpsTriple (base + 148) (base + 180)
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result4) ** (.x6 ↦ᵣ carry4b) ** (.x5 ↦ᵣ carry4) ** (.x11 ↦ᵣ carry4a) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ result2) ** ((sp + 44) ↦ₘ result3) **
     ((sp + 48) ↦ₘ result4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result5) ** (.x6 ↦ᵣ carry5b) ** (.x5 ↦ᵣ carry5) ** (.x11 ↦ᵣ carry5a) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ result2) ** ((sp + 44) ↦ₘ result3) **
     ((sp + 48) ↦ₘ result4) ** ((sp + 52) ↦ₘ result5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L5)
  clear L5
  have S012345 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S01234' L5'
  clear S01234' L5'
  have S012345' := cpsTriple_addr_eq (rfl) (by bv_omega : (base + 180 : Addr) = base + 180) S012345
  clear S012345
  -- Limb 6: add_limb_carry_spec at base+180 (8 instr, base+180 -> base+212)
  have L6_raw := add_limb_carry_spec 24 56 sp a6 b6 result5 carry5b carry5 carry5a (base + 180) hvm24 hvm56
  simp only [signExtend12_24, signExtend12_56] at L6_raw
  rw [show (base + 180 : Addr) + 4 = base + 184 from by bv_omega,
      show (base + 180 : Addr) + 8 = base + 188 from by bv_omega,
      show (base + 180 : Addr) + 12 = base + 192 from by bv_omega,
      show (base + 180 : Addr) + 16 = base + 196 from by bv_omega,
      show (base + 180 : Addr) + 20 = base + 200 from by bv_omega,
      show (base + 180 : Addr) + 24 = base + 204 from by bv_omega,
      show (base + 180 : Addr) + 28 = base + 208 from by bv_omega,
      show (base + 180 : Addr) + 32 = base + 212 from by bv_omega] at L6_raw
  have L6 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
     ((base + 8) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SLTU .x5 .x7 .x6) **
     ((base + 16) ↦ᵢ .SW .x12 .x7 32) **
     ((base + 20) ↦ᵢ .LW .x7 .x12 4) ** ((base + 24) ↦ᵢ .LW .x6 .x12 36) **
     ((base + 28) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 32) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 36) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 40) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 44) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 48) ↦ᵢ .SW .x12 .x7 36) **
     ((base + 52) ↦ᵢ .LW .x7 .x12 8) ** ((base + 56) ↦ᵢ .LW .x6 .x12 40) **
     ((base + 60) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 64) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 68) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 72) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 76) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 80) ↦ᵢ .SW .x12 .x7 40) **
     ((base + 84) ↦ᵢ .LW .x7 .x12 12) ** ((base + 88) ↦ᵢ .LW .x6 .x12 44) **
     ((base + 92) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 96) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 100) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 104) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 108) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 112) ↦ᵢ .SW .x12 .x7 44) **
     ((base + 116) ↦ᵢ .LW .x7 .x12 16) ** ((base + 120) ↦ᵢ .LW .x6 .x12 48) **
     ((base + 124) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 128) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 132) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 136) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 140) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 144) ↦ᵢ .SW .x12 .x7 48) **
     ((base + 148) ↦ᵢ .LW .x7 .x12 20) ** ((base + 152) ↦ᵢ .LW .x6 .x12 52) **
     ((base + 156) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 160) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 164) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 168) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 172) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 176) ↦ᵢ .SW .x12 .x7 52) **
     ((base + 212) ↦ᵢ .LW .x7 .x12 28) ** ((base + 216) ↦ᵢ .LW .x6 .x12 60) **
     ((base + 220) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 224) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 228) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 232) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 236) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 240) ↦ᵢ .SW .x12 .x7 60) **
     ((base + 244) ↦ᵢ .ADDI .x12 .x12 32))
    (by pcFree) L6_raw
  clear L6_raw
  have L6' : cpsTriple (base + 180) (base + 212)
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result5) ** (.x6 ↦ᵣ carry5b) ** (.x5 ↦ᵣ carry5) ** (.x11 ↦ᵣ carry5a) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ result2) ** ((sp + 44) ↦ₘ result3) **
     ((sp + 48) ↦ₘ result4) ** ((sp + 52) ↦ₘ result5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result6) ** (.x6 ↦ᵣ carry6b) ** (.x5 ↦ᵣ carry6) ** (.x11 ↦ᵣ carry6a) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ result2) ** ((sp + 44) ↦ₘ result3) **
     ((sp + 48) ↦ₘ result4) ** ((sp + 52) ↦ₘ result5) ** ((sp + 56) ↦ₘ result6) ** ((sp + 60) ↦ₘ b7)) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L6)
  clear L6
  have S0123456 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S012345' L6'
  clear S012345' L6'
  have S0123456' := cpsTriple_addr_eq (rfl) (by bv_omega : (base + 212 : Addr) = base + 212) S0123456
  clear S0123456
  -- Limb 7: add_limb_carry_spec at base+212 (8 instr, base+212 -> base+244)
  have L7_raw := add_limb_carry_spec 28 60 sp a7 b7 result6 carry6b carry6 carry6a (base + 212) hvm28 hvm60
  simp only [signExtend12_28, signExtend12_60] at L7_raw
  rw [show (base + 212 : Addr) + 4 = base + 216 from by bv_omega,
      show (base + 212 : Addr) + 8 = base + 220 from by bv_omega,
      show (base + 212 : Addr) + 12 = base + 224 from by bv_omega,
      show (base + 212 : Addr) + 16 = base + 228 from by bv_omega,
      show (base + 212 : Addr) + 20 = base + 232 from by bv_omega,
      show (base + 212 : Addr) + 24 = base + 236 from by bv_omega,
      show (base + 212 : Addr) + 28 = base + 240 from by bv_omega,
      show (base + 212 : Addr) + 32 = base + 244 from by bv_omega] at L7_raw
  have L7 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
     ((base + 8) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SLTU .x5 .x7 .x6) **
     ((base + 16) ↦ᵢ .SW .x12 .x7 32) **
     ((base + 20) ↦ᵢ .LW .x7 .x12 4) ** ((base + 24) ↦ᵢ .LW .x6 .x12 36) **
     ((base + 28) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 32) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 36) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 40) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 44) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 48) ↦ᵢ .SW .x12 .x7 36) **
     ((base + 52) ↦ᵢ .LW .x7 .x12 8) ** ((base + 56) ↦ᵢ .LW .x6 .x12 40) **
     ((base + 60) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 64) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 68) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 72) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 76) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 80) ↦ᵢ .SW .x12 .x7 40) **
     ((base + 84) ↦ᵢ .LW .x7 .x12 12) ** ((base + 88) ↦ᵢ .LW .x6 .x12 44) **
     ((base + 92) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 96) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 100) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 104) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 108) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 112) ↦ᵢ .SW .x12 .x7 44) **
     ((base + 116) ↦ᵢ .LW .x7 .x12 16) ** ((base + 120) ↦ᵢ .LW .x6 .x12 48) **
     ((base + 124) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 128) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 132) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 136) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 140) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 144) ↦ᵢ .SW .x12 .x7 48) **
     ((base + 148) ↦ᵢ .LW .x7 .x12 20) ** ((base + 152) ↦ᵢ .LW .x6 .x12 52) **
     ((base + 156) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 160) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 164) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 168) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 172) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 176) ↦ᵢ .SW .x12 .x7 52) **
     ((base + 180) ↦ᵢ .LW .x7 .x12 24) ** ((base + 184) ↦ᵢ .LW .x6 .x12 56) **
     ((base + 188) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 192) ↦ᵢ .SLTU .x11 .x7 .x6) **
     ((base + 196) ↦ᵢ .ADD .x7 .x7 .x5) ** ((base + 200) ↦ᵢ .SLTU .x6 .x7 .x5) **
     ((base + 204) ↦ᵢ .OR .x5 .x11 .x6) ** ((base + 208) ↦ᵢ .SW .x12 .x7 56) **
     ((base + 244) ↦ᵢ .ADDI .x12 .x12 32))
    (by pcFree) L7_raw
  clear L7_raw
  have L7' : cpsTriple (base + 212) (base + 244)
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result6) ** (.x6 ↦ᵣ carry6b) ** (.x5 ↦ᵣ carry6) ** (.x11 ↦ᵣ carry6a) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ result2) ** ((sp + 44) ↦ₘ result3) **
     ((sp + 48) ↦ₘ result4) ** ((sp + 52) ↦ₘ result5) ** ((sp + 56) ↦ₘ result6) ** ((sp + 60) ↦ₘ b7))
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result7) ** (.x6 ↦ᵣ carry7b) ** (.x5 ↦ᵣ carry7) ** (.x11 ↦ᵣ carry7a) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ result2) ** ((sp + 44) ↦ₘ result3) **
     ((sp + 48) ↦ₘ result4) ** ((sp + 52) ↦ₘ result5) ** ((sp + 56) ↦ₘ result6) ** ((sp + 60) ↦ₘ result7)) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L7)
  clear L7
  have S01234567 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S0123456' L7'
  clear S0123456' L7'
  have S01234567' := cpsTriple_addr_eq (rfl) (by bv_omega : (base + 244 : Addr) = base + 244) S01234567
  clear S01234567
  -- ADDI: addi_spec_gen_same at base+244 (base+244 -> base+248)
  have Laddi := addi_spec_gen_same .x12 sp 32 (base + 244) (by nofun)
  simp only [signExtend12_32] at Laddi
  rw [show (base + 244 : Addr) + 4 = base + 248 from by bv_omega] at Laddi
  -- Frame ADDI step 1: add F instrAt (61 conjuncts, ~122 steps < 128)
  have Laddi_f1 := cpsTriple_frame_left _ _ _ _ F hF Laddi
  clear Laddi
  -- Frame ADDI step 2: add remaining regs + mem (20 conjuncts)
  have Laddi' : cpsTriple (base + 244) (base + 248)
    (G ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result7) ** (.x6 ↦ᵣ carry7b) ** (.x5 ↦ᵣ carry7) ** (.x11 ↦ᵣ carry7a) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ result2) ** ((sp + 44) ↦ₘ result3) **
     ((sp + 48) ↦ₘ result4) ** ((sp + 52) ↦ₘ result5) ** ((sp + 56) ↦ₘ result6) ** ((sp + 60) ↦ₘ result7))
    (G ** (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result7) ** (.x6 ↦ᵣ carry7b) ** (.x5 ↦ᵣ carry7) ** (.x11 ↦ᵣ carry7a) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ result2) ** ((sp + 44) ↦ₘ result3) **
     ((sp + 48) ↦ₘ result4) ** ((sp + 52) ↦ₘ result5) ** ((sp + 56) ↦ₘ result6) ** ((sp + 60) ↦ₘ result7)) :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTriple_frame_left _ _ _ _ _ (by pcFree) Laddi_f1)
  clear Laddi_f1
  -- Final composition: limbs 0-7 + ADDI
  have Sfull := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S01234567' Laddi'
  clear S01234567' Laddi'
  -- Permute to match goal
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) Sfull

end EvmAsm
