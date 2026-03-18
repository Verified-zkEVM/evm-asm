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

private theorem cpsTriple_addr_eq {cr : CodeReq} {P Q : Assertion}
    {s1 s2 e1 e2 : Addr} (hs : s1 = s2) (he : e1 = e2)
    (h : cpsTriple s1 e1 cr P Q) :
    cpsTriple s2 e2 cr P Q := by
  subst hs; subst he; exact h

-- ============================================================================
-- Full 256-bit ADD spec
-- ============================================================================

/-- Instruction memory assertion for the 256-bit EVM ADD operation (RV32). -/
abbrev evm_add_code (base : Addr) : CodeReq :=
  -- Limb 0 code (5 instructions: base+0..base+16)
  CodeReq.union (CodeReq.singleton base (.LW .x7 .x12 0))
  (CodeReq.union (CodeReq.singleton (base + 4) (.LW .x6 .x12 32))
  (CodeReq.union (CodeReq.singleton (base + 8) (.ADD .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SLTU .x5 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SW .x12 .x7 32))
  -- Limb 1 code (8 instructions: base+20..base+48)
  (CodeReq.union (CodeReq.singleton (base + 20) (.LW .x7 .x12 4))
  (CodeReq.union (CodeReq.singleton (base + 24) (.LW .x6 .x12 36))
  (CodeReq.union (CodeReq.singleton (base + 28) (.ADD .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 32) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 36) (.ADD .x7 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 40) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 44) (.OR .x5 .x11 .x6))
  (CodeReq.union (CodeReq.singleton (base + 48) (.SW .x12 .x7 36))
  -- Limb 2 code (8 instructions: base+52..base+80)
  (CodeReq.union (CodeReq.singleton (base + 52) (.LW .x7 .x12 8))
  (CodeReq.union (CodeReq.singleton (base + 56) (.LW .x6 .x12 40))
  (CodeReq.union (CodeReq.singleton (base + 60) (.ADD .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 64) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 68) (.ADD .x7 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 72) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 76) (.OR .x5 .x11 .x6))
  (CodeReq.union (CodeReq.singleton (base + 80) (.SW .x12 .x7 40))
  -- Limb 3 code (8 instructions: base+84..base+112)
  (CodeReq.union (CodeReq.singleton (base + 84) (.LW .x7 .x12 12))
  (CodeReq.union (CodeReq.singleton (base + 88) (.LW .x6 .x12 44))
  (CodeReq.union (CodeReq.singleton (base + 92) (.ADD .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 96) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 100) (.ADD .x7 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 104) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 108) (.OR .x5 .x11 .x6))
  (CodeReq.union (CodeReq.singleton (base + 112) (.SW .x12 .x7 44))
  -- Limb 4 code (8 instructions: base+116..base+144)
  (CodeReq.union (CodeReq.singleton (base + 116) (.LW .x7 .x12 16))
  (CodeReq.union (CodeReq.singleton (base + 120) (.LW .x6 .x12 48))
  (CodeReq.union (CodeReq.singleton (base + 124) (.ADD .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 128) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 132) (.ADD .x7 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 136) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 140) (.OR .x5 .x11 .x6))
  (CodeReq.union (CodeReq.singleton (base + 144) (.SW .x12 .x7 48))
  -- Limb 5 code (8 instructions: base+148..base+176)
  (CodeReq.union (CodeReq.singleton (base + 148) (.LW .x7 .x12 20))
  (CodeReq.union (CodeReq.singleton (base + 152) (.LW .x6 .x12 52))
  (CodeReq.union (CodeReq.singleton (base + 156) (.ADD .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 160) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 164) (.ADD .x7 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 168) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 172) (.OR .x5 .x11 .x6))
  (CodeReq.union (CodeReq.singleton (base + 176) (.SW .x12 .x7 52))
  -- Limb 6 code (8 instructions: base+180..base+208)
  (CodeReq.union (CodeReq.singleton (base + 180) (.LW .x7 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 184) (.LW .x6 .x12 56))
  (CodeReq.union (CodeReq.singleton (base + 188) (.ADD .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 192) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 196) (.ADD .x7 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 200) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 204) (.OR .x5 .x11 .x6))
  (CodeReq.union (CodeReq.singleton (base + 208) (.SW .x12 .x7 56))
  -- Limb 7 code (8 instructions: base+212..base+240)
  (CodeReq.union (CodeReq.singleton (base + 212) (.LW .x7 .x12 28))
  (CodeReq.union (CodeReq.singleton (base + 216) (.LW .x6 .x12 60))
  (CodeReq.union (CodeReq.singleton (base + 220) (.ADD .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 224) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 228) (.ADD .x7 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 232) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 236) (.OR .x5 .x11 .x6))
  (CodeReq.union (CodeReq.singleton (base + 240) (.SW .x12 .x7 60))
  -- ADDI instruction
   (CodeReq.singleton (base + 244) (.ADDI .x12 .x12 32))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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
    let code := evm_add_code base
    cpsTriple base (base + 248) code
      -- Registers + memory
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      -- Registers + memory (updated)
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result7) ** (.x6 ↦ᵣ carry7b) ** (.x5 ↦ᵣ carry7) ** (.x11 ↦ᵣ carry7a) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ result2) ** ((sp + 44) ↦ₘ result3) **
       ((sp + 48) ↦ₘ result4) ** ((sp + 52) ↦ₘ result5) ** ((sp + 56) ↦ₘ result6) ** ((sp + 60) ↦ₘ result7)) := by
  -- Carry chain intermediate values
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
  -- Limb 0: 5 instructions (base+0 .. base+16)
  have L0 := add_limb0_spec 0 32 sp a0 b0 v7 v6 v5 base
    (by validMem) (by validMem)
  -- Limb 1: 8 instructions (base+20 .. base+48)
  have L1 := add_limb_carry_spec 4 36 sp a1 b1 sum0 b0 carry0 v11
    (base + 20) (by validMem) (by validMem)
  -- Limb 2: 8 instructions (base+52 .. base+80)
  have L2 := add_limb_carry_spec 8 40 sp a2 b2 result1 carry1b carry1 carry1a
    (base + 52) (by validMem) (by validMem)
  -- Limb 3: 8 instructions (base+84 .. base+112)
  have L3 := add_limb_carry_spec 12 44 sp a3 b3 result2 carry2b carry2 carry2a
    (base + 84) (by validMem) (by validMem)
  -- Limb 4: 8 instructions (base+116 .. base+144)
  have L4 := add_limb_carry_spec 16 48 sp a4 b4 result3 carry3b carry3 carry3a
    (base + 116) (by validMem) (by validMem)
  -- Limb 5: 8 instructions (base+148 .. base+176)
  have L5 := add_limb_carry_spec 20 52 sp a5 b5 result4 carry4b carry4 carry4a
    (base + 148) (by validMem) (by validMem)
  -- Limb 6: 8 instructions (base+180 .. base+208)
  have L6 := add_limb_carry_spec 24 56 sp a6 b6 result5 carry5b carry5 carry5a
    (base + 180) (by validMem) (by validMem)
  -- Limb 7: 8 instructions (base+212 .. base+240)
  have L7 := add_limb_carry_spec 28 60 sp a7 b7 result6 carry6b carry6 carry6a
    (base + 212) (by validMem) (by validMem)
  -- ADDI sp adjustment (base+244)
  have L8 := addi_spec_gen_same .x12 sp 32 (base + 244) (by nofun)
  runBlock L0 L1 L2 L3 L4 L5 L6 L7 L8

end EvmAsm
