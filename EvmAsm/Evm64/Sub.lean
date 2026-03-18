/-
  EvmAsm.Evm64.Sub

  Full 256-bit EVM SUB spec composed from per-limb specs.
  30 instructions total (5 + 3×8 + 1 ADDI).
-/

import EvmAsm.Evm64.Arithmetic

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

/-- CodeReq for the 256-bit EVM SUB operation.
    30 instructions = 120 bytes. 4 per-limb SUB blocks + ADDI sp adjustment. -/
abbrev evm_sub_code (base : Addr) : CodeReq :=
  -- Limb 0 code (5 instructions: base+0..base+16)
  CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 0))
  (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 32))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x5 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SUB .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SD .x12 .x7 32))
  -- Limb 1 code (8 instructions: base+20..base+48)
  (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x7 .x12 8))
  (CodeReq.union (CodeReq.singleton (base + 24) (.LD .x6 .x12 40))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 32) (.SUB .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 36) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 40) (.SUB .x7 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 44) (.OR .x5 .x11 .x6))
  (CodeReq.union (CodeReq.singleton (base + 48) (.SD .x12 .x7 40))
  -- Limb 2 code (8 instructions: base+52..base+80)
  (CodeReq.union (CodeReq.singleton (base + 52) (.LD .x7 .x12 16))
  (CodeReq.union (CodeReq.singleton (base + 56) (.LD .x6 .x12 48))
  (CodeReq.union (CodeReq.singleton (base + 60) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 64) (.SUB .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 68) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 72) (.SUB .x7 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 76) (.OR .x5 .x11 .x6))
  (CodeReq.union (CodeReq.singleton (base + 80) (.SD .x12 .x7 48))
  -- Limb 3 code (8 instructions: base+84..base+112)
  (CodeReq.union (CodeReq.singleton (base + 84) (.LD .x7 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 88) (.LD .x6 .x12 56))
  (CodeReq.union (CodeReq.singleton (base + 92) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 96) (.SUB .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 100) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 104) (.SUB .x7 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 108) (.OR .x5 .x11 .x6))
  (CodeReq.union (CodeReq.singleton (base + 112) (.SD .x12 .x7 56))
  -- ADDI instruction
  (CodeReq.singleton (base + 116) (.ADDI .x12 .x12 32))))))))))))))))))))))))))))))

set_option maxHeartbeats 6400000 in
/-- Full 256-bit EVM SUB: composes 4 per-limb SUB specs + ADDI sp adjustment.
    30 instructions total. Pops 2 stack words (A at sp, B at sp+32),
    writes A - B to sp+32..sp+56, advances sp by 32.
    Borrow propagates through limbs via x5. -/
theorem evm_sub_spec (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (v7 v6 v5 v11 : Word)
    (hvalid : ValidMemRange sp 8) :
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let diff0 := a0 - b0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let result1 := temp1 - borrow0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let result2 := temp2 - borrow1
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult a3 b3 then (1 : Word) else 0
    let temp3 := a3 - b3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let result3 := temp3 - borrow2
    let borrow3 := borrow3a ||| borrow3b
    let code := evm_sub_code base
    cpsTriple base (base + 120) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ borrow3b) ** (.x5 ↦ᵣ borrow3) ** (.x11 ↦ᵣ borrow3a) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ diff0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) ** ((sp + 56) ↦ₘ result3)) := by
  intro borrow0; intro diff0
  intro borrow1a; intro temp1; intro borrow1b; intro result1; intro borrow1
  intro borrow2a; intro temp2; intro borrow2b; intro result2; intro borrow2
  intro borrow3a; intro temp3; intro borrow3b; intro result3; intro borrow3
  have L0 := sub_limb0_spec 0 32 sp a0 b0 v7 v6 v5 base (by validMem) (by validMem)
  have L1 := sub_limb_carry_spec 8 40 sp a1 b1 diff0 b0 borrow0 v11 (base + 20) (by validMem) (by validMem)
  have L2 := sub_limb_carry_spec 16 48 sp a2 b2 result1 borrow1b borrow1 borrow1a (base + 52) (by validMem) (by validMem)
  have L3 := sub_limb_carry_spec 24 56 sp a3 b3 result2 borrow2b borrow2 borrow2a (base + 84) (by validMem) (by validMem)
  have Laddi := addi_spec_gen_same .x12 sp 32 (base + 116) (by nofun)
  runBlock L0 L1 L2 L3 Laddi

end EvmAsm.Rv64
