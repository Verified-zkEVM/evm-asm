/-
  EvmAsm.Evm32.ArithmeticSpec

  Full 256-bit EVM arithmetic specs (ADD, SUB) composed from per-limb specs.
  Each composes 8 per-limb specs + ADDI sp adjustment into a single cpsTriple.
  62 instructions total with instrAt in both P and Q.
-/

import EvmAsm.Evm32.Arithmetic
import EvmAsm.Rv32.Tactics.XSimp

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
    let code :=
      -- Limb 0 code (5 instructions: base+0..base+16)
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
      ((base + 244) ↦ᵢ .ADDI .x12 .x12 32)
    cpsTriple base (base + 248)
      (code **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      (code **
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
  -- Compose 8 per-limb ADD specs + ADDI via runBlock (manual mode with address normalization)
  have L0 := add_limb0_spec 0 32 sp a0 b0 v7 v6 v5 base (by validMem) (by validMem)
  have L1 := add_limb_carry_spec 4 36 sp a1 b1 sum0 b0 carry0 v11 (base + 20) (by validMem) (by validMem)
  have L2 := add_limb_carry_spec 8 40 sp a2 b2 result1 carry1b carry1 carry1a (base + 52) (by validMem) (by validMem)
  have L3 := add_limb_carry_spec 12 44 sp a3 b3 result2 carry2b carry2 carry2a (base + 84) (by validMem) (by validMem)
  have L4 := add_limb_carry_spec 16 48 sp a4 b4 result3 carry3b carry3 carry3a (base + 116) (by validMem) (by validMem)
  have L5 := add_limb_carry_spec 20 52 sp a5 b5 result4 carry4b carry4 carry4a (base + 148) (by validMem) (by validMem)
  have L6 := add_limb_carry_spec 24 56 sp a6 b6 result5 carry5b carry5 carry5a (base + 180) (by validMem) (by validMem)
  have L7 := add_limb_carry_spec 28 60 sp a7 b7 result6 carry6b carry6 carry6a (base + 212) (by validMem) (by validMem)
  have Laddi := addi_spec_gen_same .x12 sp 32 (base + 244) (by nofun)
  runBlock L0 L1 L2 L3 L4 L5 L6 L7 Laddi

end EvmAsm
