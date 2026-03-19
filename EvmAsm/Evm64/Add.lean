/-
  EvmAsm.Evm64.Add

  Full 256-bit EVM ADD spec composed from per-limb specs.
  30 instructions total (5 + 3×8 + 1 ADDI).
-/

import EvmAsm.Evm64.Arithmetic

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

/-- CodeReq for the 256-bit EVM ADD operation.
    30 instructions = 120 bytes. 4 per-limb ADD blocks + ADDI sp adjustment. -/
abbrev evm_add_code (base : Addr) : CodeReq :=
  CodeReq.ofProg base evm_add

set_option maxHeartbeats 6400000 in
/-- Full 256-bit EVM ADD: composes 4 per-limb ADD specs + ADDI sp adjustment.
    30 instructions total. Pops 2 stack words (A at sp, B at sp+32),
    writes A + B to sp+32..sp+56, advances sp by 32.
    Carry propagates through limbs via x5. -/
theorem evm_add_spec (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (v7 v6 v5 v11 : Word)
    (hvalid : ValidMemRange sp 8) :
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
    let code := evm_add_code base
    cpsTriple base (base + 120) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) ** (.x5 ↦ᵣ carry3) ** (.x11 ↦ᵣ carry3a) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ sum0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) ** ((sp + 56) ↦ₘ result3)) := by
  intro sum0; intro carry0; intro psum1; intro carry1a; intro result1; intro carry1b; intro carry1
  intro psum2; intro carry2a; intro result2; intro carry2b; intro carry2
  intro psum3; intro carry3a; intro result3; intro carry3b; intro carry3
  have L0 := add_limb0_spec 0 32 sp a0 b0 v7 v6 v5 base (by validMem) (by validMem)
  have L1 := add_limb_carry_spec 8 40 sp a1 b1 sum0 b0 carry0 v11 (base + 20) (by validMem) (by validMem)
  have L2 := add_limb_carry_spec 16 48 sp a2 b2 result1 carry1b carry1 carry1a (base + 52) (by validMem) (by validMem)
  have L3 := add_limb_carry_spec 24 56 sp a3 b3 result2 carry2b carry2 carry2a (base + 84) (by validMem) (by validMem)
  have Laddi := addi_spec_gen_same .x12 sp 32 (base + 116) (by nofun)
  runBlock L0 L1 L2 L3 Laddi

end EvmAsm.Rv64
