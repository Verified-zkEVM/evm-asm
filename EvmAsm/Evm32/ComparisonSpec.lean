/-
  EvmAsm.Evm32.ComparisonSpec

  Full 256-bit EVM GT spec composed from per-limb LT specs (with swapped operands).
  GT(a, b) = LT(b, a): load b-limbs into x7 and a-limbs into x6, compute borrow(b < a).
  Final borrow = 1 iff b < a iff a > b.
  54 instructions total: 45 borrow + 9 store.
-/

import EvmAsm.Evm32.Comparison
import EvmAsm.Rv32.Tactics.XSimp
import EvmAsm.Rv32.Tactics.RunBlock

open EvmAsm.Tactics

namespace EvmAsm

-- ============================================================================
-- Helpers
-- ============================================================================

local macro "bv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]))

-- ============================================================================
-- Store phase helper: ADDI + 8 SW instructions
-- ============================================================================

abbrev lt_result_store_code (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ADDI .x12 .x12 32))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SW .x12 .x5 0))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SW .x12 .x0 4))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SW .x12 .x0 8))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SW .x12 .x0 12))
  (CodeReq.union (CodeReq.singleton (base + 20) (.SW .x12 .x0 16))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SW .x12 .x0 20))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SW .x12 .x0 24))
   (CodeReq.singleton (base + 32) (.SW .x12 .x0 28)))))))))

set_option maxHeartbeats 4800000 in
/-- Store phase spec for LT/GT: ADDI sp+32 + SW borrow + 7×SW 0.
    Takes sp → sp+32, stores borrow to mem[sp+32], zeros to mem[sp+36..sp+60].
    9 instructions = 36 bytes. -/
theorem lt_result_store_spec (sp : Addr)
    (borrow v7 v6 v11 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word) (base : Addr)
    -- Memory validity for sp+32..sp+60
    (hvalid : ValidMemRange (sp + 32) 8) :
    let code := lt_result_store_code base
    cpsTriple base (base + 36) code
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow) ** (.x11 ↦ᵣ v11) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow) ** (.x11 ↦ᵣ v11) **
       ((sp + 32) ↦ₘ borrow) ** ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
       ((sp + 48) ↦ₘ 0) ** ((sp + 52) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0) ** ((sp + 60) ↦ₘ 0)) := by
  runBlock

-- ============================================================================
-- Full 256-bit GT spec
-- ============================================================================

abbrev evm_gt_code (base : Addr) : CodeReq :=
  -- Limb 0 code (3 instr): LW b, LW a, SLTU
  CodeReq.union (CodeReq.singleton base (.LW .x7 .x12 32))
  (CodeReq.union (CodeReq.singleton (base + 4) (.LW .x6 .x12 0))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x5 .x7 .x6))
  -- Limb 1 code (6 instr)
  (CodeReq.union (CodeReq.singleton (base + 12) (.LW .x7 .x12 36))
  (CodeReq.union (CodeReq.singleton (base + 16) (.LW .x6 .x12 4))
  (CodeReq.union (CodeReq.singleton (base + 20) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SUB .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 32) (.OR .x5 .x11 .x6))
  -- Limb 2 code (6 instr)
  (CodeReq.union (CodeReq.singleton (base + 36) (.LW .x7 .x12 40))
  (CodeReq.union (CodeReq.singleton (base + 40) (.LW .x6 .x12 8))
  (CodeReq.union (CodeReq.singleton (base + 44) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 48) (.SUB .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 52) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 56) (.OR .x5 .x11 .x6))
  -- Limb 3 code (6 instr)
  (CodeReq.union (CodeReq.singleton (base + 60) (.LW .x7 .x12 44))
  (CodeReq.union (CodeReq.singleton (base + 64) (.LW .x6 .x12 12))
  (CodeReq.union (CodeReq.singleton (base + 68) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 72) (.SUB .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 76) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 80) (.OR .x5 .x11 .x6))
  -- Limb 4 code (6 instr)
  (CodeReq.union (CodeReq.singleton (base + 84) (.LW .x7 .x12 48))
  (CodeReq.union (CodeReq.singleton (base + 88) (.LW .x6 .x12 16))
  (CodeReq.union (CodeReq.singleton (base + 92) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 96) (.SUB .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 100) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 104) (.OR .x5 .x11 .x6))
  -- Limb 5 code (6 instr)
  (CodeReq.union (CodeReq.singleton (base + 108) (.LW .x7 .x12 52))
  (CodeReq.union (CodeReq.singleton (base + 112) (.LW .x6 .x12 20))
  (CodeReq.union (CodeReq.singleton (base + 116) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 120) (.SUB .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 124) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 128) (.OR .x5 .x11 .x6))
  -- Limb 6 code (6 instr)
  (CodeReq.union (CodeReq.singleton (base + 132) (.LW .x7 .x12 56))
  (CodeReq.union (CodeReq.singleton (base + 136) (.LW .x6 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 140) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 144) (.SUB .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 148) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 152) (.OR .x5 .x11 .x6))
  -- Limb 7 code (6 instr)
  (CodeReq.union (CodeReq.singleton (base + 156) (.LW .x7 .x12 60))
  (CodeReq.union (CodeReq.singleton (base + 160) (.LW .x6 .x12 28))
  (CodeReq.union (CodeReq.singleton (base + 164) (.SLTU .x11 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 168) (.SUB .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 172) (.SLTU .x6 .x7 .x5))
  (CodeReq.union (CodeReq.singleton (base + 176) (.OR .x5 .x11 .x6))
  -- Store phase code (9 instr)
   (lt_result_store_code (base + 180))))))))))))))))))))))))))))))))))))))))))))))

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 40000000 in
/-- Full 256-bit EVM GT: GT(a, b) = 1 iff a > b (unsigned).
    Computed as borrow chain of (b - a), same circuit as LT(b, a).
    Pops 2 stack words (A at sp+0..sp+28, B at sp+32..sp+60),
    writes result (0 or 1) to sp+32..sp+60, advances sp by 32.
    54 instructions = 216 bytes total. -/
theorem evm_gt_spec (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 v5 v11 : Word)
    -- Memory validity for all 16 stack cells
    (hvalid : ValidMemRange sp 16) :
    -- Borrow chain: b - a (GT direction)
    let borrow0 := if BitVec.ult b0 a0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult b1 a1 then (1 : Word) else 0
    let temp1 := b1 - a1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult b2 a2 then (1 : Word) else 0
    let temp2 := b2 - a2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult b3 a3 then (1 : Word) else 0
    let temp3 := b3 - a3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let borrow3 := borrow3a ||| borrow3b
    let borrow4a := if BitVec.ult b4 a4 then (1 : Word) else 0
    let temp4 := b4 - a4
    let borrow4b := if BitVec.ult temp4 borrow3 then (1 : Word) else 0
    let borrow4 := borrow4a ||| borrow4b
    let borrow5a := if BitVec.ult b5 a5 then (1 : Word) else 0
    let temp5 := b5 - a5
    let borrow5b := if BitVec.ult temp5 borrow4 then (1 : Word) else 0
    let borrow5 := borrow5a ||| borrow5b
    let borrow6a := if BitVec.ult b6 a6 then (1 : Word) else 0
    let temp6 := b6 - a6
    let borrow6b := if BitVec.ult temp6 borrow5 then (1 : Word) else 0
    let borrow6 := borrow6a ||| borrow6b
    let borrow7a := if BitVec.ult b7 a7 then (1 : Word) else 0
    let temp7 := b7 - a7
    let borrow7b := if BitVec.ult temp7 borrow6 then (1 : Word) else 0
    let borrow7 := borrow7a ||| borrow7b
    let code := evm_gt_code base
    cpsTriple base (base + 216) code
      -- Registers + memory
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
       -- Registers + memory (updated)
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (b7 - a7)) ** (.x6 ↦ᵣ borrow7b) **
       (.x5 ↦ᵣ borrow7) ** (.x11 ↦ᵣ borrow7a) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ borrow7) ** ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
       ((sp + 48) ↦ₘ 0) ** ((sp + 52) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0) ** ((sp + 60) ↦ₘ 0)) := by
  -- Borrow chain intermediate values
  let borrow0 := if BitVec.ult b0 a0 then (1 : Word) else 0
  let borrow1a := if BitVec.ult b1 a1 then (1 : Word) else 0
  let temp1 := b1 - a1
  let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
  let borrow1 := borrow1a ||| borrow1b
  let borrow2a := if BitVec.ult b2 a2 then (1 : Word) else 0
  let temp2 := b2 - a2
  let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
  let borrow2 := borrow2a ||| borrow2b
  let borrow3a := if BitVec.ult b3 a3 then (1 : Word) else 0
  let temp3 := b3 - a3
  let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
  let borrow3 := borrow3a ||| borrow3b
  let borrow4a := if BitVec.ult b4 a4 then (1 : Word) else 0
  let temp4 := b4 - a4
  let borrow4b := if BitVec.ult temp4 borrow3 then (1 : Word) else 0
  let borrow4 := borrow4a ||| borrow4b
  let borrow5a := if BitVec.ult b5 a5 then (1 : Word) else 0
  let temp5 := b5 - a5
  let borrow5b := if BitVec.ult temp5 borrow4 then (1 : Word) else 0
  let borrow5 := borrow5a ||| borrow5b
  let borrow6a := if BitVec.ult b6 a6 then (1 : Word) else 0
  let temp6 := b6 - a6
  let borrow6b := if BitVec.ult temp6 borrow5 then (1 : Word) else 0
  let borrow6 := borrow6a ||| borrow6b
  let borrow7a := if BitVec.ult b7 a7 then (1 : Word) else 0
  let temp7 := b7 - a7
  let borrow7b := if BitVec.ult temp7 borrow6 then (1 : Word) else 0
  let borrow7 := borrow7a ||| borrow7b
  -- Limb 0: 3 instructions (borrow only, GT direction: b loaded first)
  have L0 := lt_limb0_spec 32 0 sp b0 a0 v7 v6 v5 base
    (by validMem) (by validMem)
  -- Limb 1: 6 instructions
  have L1 := lt_limb_carry_spec 36 4 sp b1 a1 b0 a0 borrow0 v11
    (base + 12) (by validMem) (by validMem)
  -- Limb 2: 6 instructions
  have L2 := lt_limb_carry_spec 40 8 sp b2 a2 temp1 borrow1b borrow1 borrow1a
    (base + 36) (by validMem) (by validMem)
  -- Limb 3: 6 instructions
  have L3 := lt_limb_carry_spec 44 12 sp b3 a3 temp2 borrow2b borrow2 borrow2a
    (base + 60) (by validMem) (by validMem)
  -- Limb 4: 6 instructions
  have L4 := lt_limb_carry_spec 48 16 sp b4 a4 temp3 borrow3b borrow3 borrow3a
    (base + 84) (by validMem) (by validMem)
  -- Limb 5: 6 instructions
  have L5 := lt_limb_carry_spec 52 20 sp b5 a5 temp4 borrow4b borrow4 borrow4a
    (base + 108) (by validMem) (by validMem)
  -- Limb 6: 6 instructions
  have L6 := lt_limb_carry_spec 56 24 sp b6 a6 temp5 borrow5b borrow5 borrow5a
    (base + 132) (by validMem) (by validMem)
  -- Limb 7: 6 instructions
  have L7 := lt_limb_carry_spec 60 28 sp b7 a7 temp6 borrow6b borrow6 borrow6a
    (base + 156) (by validMem) (by validMem)
  -- Store phase: 9 instructions (ADDI + 8 SW)
  have hvalid2 : ValidMemRange (sp + 32) 8 := by
    have := hvalid.split (n1 := 8) (n2 := 8)
    exact this.2
  have L8 := lt_result_store_spec sp borrow7 temp7 borrow7b borrow7a
    b0 b1 b2 b3 b4 b5 b6 b7 (base + 180) hvalid2
  runBlock L0 L1 L2 L3 L4 L5 L6 L7 L8

-- ============================================================================
-- EQ: store+SLTIU phase
-- ============================================================================

abbrev eq_result_store_code (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.SLTIU .x7 .x7 1))
  (CodeReq.union (CodeReq.singleton (base + 4) (.ADDI .x12 .x12 32))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SW .x12 .x7 0))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SW .x12 .x0 4))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SW .x12 .x0 8))
  (CodeReq.union (CodeReq.singleton (base + 20) (.SW .x12 .x0 12))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SW .x12 .x0 16))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SW .x12 .x0 20))
  (CodeReq.union (CodeReq.singleton (base + 32) (.SW .x12 .x0 24))
   (CodeReq.singleton (base + 36) (.SW .x12 .x0 28))))))))))

set_option maxHeartbeats 6400000 in
/-- Store phase spec for EQ: SLTIU + ADDI sp+32 + SW eq_result + 7×SW 0.
    SLTIU converts accumulated XOR to boolean eq_result (1 iff all limbs equal).
    ADDI takes sp → sp+32. Stores eq_result to mem[sp+32], zeros to mem[sp+36..sp+60].
    10 instructions = 40 bytes. -/
theorem eq_result_store_spec (sp : Addr)
    (acc v6 v5 v11 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word) (base : Addr)
    -- Memory validity for sp+32..sp+60
    (hvalid : ValidMemRange (sp + 32) 8) :
    let _eq_result := if BitVec.ult acc (1 : Word) then (1 : Word) else 0
    let code := eq_result_store_code base
    cpsTriple base (base + 40) code
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ acc) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x7 ↦ᵣ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
       (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       ((sp + 32) ↦ₘ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
       ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
       ((sp + 48) ↦ₘ 0) ** ((sp + 52) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0) ** ((sp + 60) ↦ₘ 0)) := by
  runBlock

-- ============================================================================
-- Full 256-bit EQ spec
-- ============================================================================

abbrev evm_eq_code (base : Addr) : CodeReq :=
  -- Limb 0 code (3 instr)
  CodeReq.union (CodeReq.singleton base (.LW .x7 .x12 0))
  (CodeReq.union (CodeReq.singleton (base + 4) (.LW .x6 .x12 32))
  (CodeReq.union (CodeReq.singleton (base + 8) (.XOR .x7 .x7 .x6))
  -- Limb 1 code (4 instr)
  (CodeReq.union (CodeReq.singleton (base + 12) (.LW .x6 .x12 4))
  (CodeReq.union (CodeReq.singleton (base + 16) (.LW .x5 .x12 36))
  (CodeReq.union (CodeReq.singleton (base + 20) (.XOR .x6 .x6 .x5))
  (CodeReq.union (CodeReq.singleton (base + 24) (.OR .x7 .x7 .x6))
  -- Limb 2 code (4 instr)
  (CodeReq.union (CodeReq.singleton (base + 28) (.LW .x6 .x12 8))
  (CodeReq.union (CodeReq.singleton (base + 32) (.LW .x5 .x12 40))
  (CodeReq.union (CodeReq.singleton (base + 36) (.XOR .x6 .x6 .x5))
  (CodeReq.union (CodeReq.singleton (base + 40) (.OR .x7 .x7 .x6))
  -- Limb 3 code (4 instr)
  (CodeReq.union (CodeReq.singleton (base + 44) (.LW .x6 .x12 12))
  (CodeReq.union (CodeReq.singleton (base + 48) (.LW .x5 .x12 44))
  (CodeReq.union (CodeReq.singleton (base + 52) (.XOR .x6 .x6 .x5))
  (CodeReq.union (CodeReq.singleton (base + 56) (.OR .x7 .x7 .x6))
  -- Limb 4 code (4 instr)
  (CodeReq.union (CodeReq.singleton (base + 60) (.LW .x6 .x12 16))
  (CodeReq.union (CodeReq.singleton (base + 64) (.LW .x5 .x12 48))
  (CodeReq.union (CodeReq.singleton (base + 68) (.XOR .x6 .x6 .x5))
  (CodeReq.union (CodeReq.singleton (base + 72) (.OR .x7 .x7 .x6))
  -- Limb 5 code (4 instr)
  (CodeReq.union (CodeReq.singleton (base + 76) (.LW .x6 .x12 20))
  (CodeReq.union (CodeReq.singleton (base + 80) (.LW .x5 .x12 52))
  (CodeReq.union (CodeReq.singleton (base + 84) (.XOR .x6 .x6 .x5))
  (CodeReq.union (CodeReq.singleton (base + 88) (.OR .x7 .x7 .x6))
  -- Limb 6 code (4 instr)
  (CodeReq.union (CodeReq.singleton (base + 92) (.LW .x6 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 96) (.LW .x5 .x12 56))
  (CodeReq.union (CodeReq.singleton (base + 100) (.XOR .x6 .x6 .x5))
  (CodeReq.union (CodeReq.singleton (base + 104) (.OR .x7 .x7 .x6))
  -- Limb 7 code (4 instr)
  (CodeReq.union (CodeReq.singleton (base + 108) (.LW .x6 .x12 28))
  (CodeReq.union (CodeReq.singleton (base + 112) (.LW .x5 .x12 60))
  (CodeReq.union (CodeReq.singleton (base + 116) (.XOR .x6 .x6 .x5))
  (CodeReq.union (CodeReq.singleton (base + 120) (.OR .x7 .x7 .x6))
  -- Store phase code (10 instr)
   (eq_result_store_code (base + 124))))))))))))))))))))))))))))))))

set_option maxHeartbeats 12800000 in
/-- Full 256-bit EVM EQ: EQ(a, b) = 1 iff a == b (as 256-bit unsigned integers).
    Computed by XOR-ing each limb pair, OR-reducing, then SLTIU to boolean.
    Pops 2 stack words (A at sp+0..sp+28, B at sp+32..sp+60),
    writes result (0 or 1) to sp+32..sp+60, advances sp by 32.
    41 instructions = 164 bytes total. -/
theorem evm_eq_spec (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 v5 v11 : Word)
    -- Memory validity for all 16 stack cells
    (hvalid : ValidMemRange sp 16) :
    -- XOR-OR accumulation chain
    let acc0 := a0 ^^^ b0
    let acc1 := acc0 ||| (a1 ^^^ b1)
    let acc2 := acc1 ||| (a2 ^^^ b2)
    let acc3 := acc2 ||| (a3 ^^^ b3)
    let acc4 := acc3 ||| (a4 ^^^ b4)
    let acc5 := acc4 ||| (a5 ^^^ b5)
    let acc6 := acc5 ||| (a6 ^^^ b6)
    let acc7 := acc6 ||| (a7 ^^^ b7)
    let eq_result := if BitVec.ult acc7 (1 : Word) then (1 : Word) else 0
    let code := evm_eq_code base
    cpsTriple base (base + 164) code
      -- Registers + memory
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      -- Registers + memory (updated)
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x7 ↦ᵣ eq_result) ** (.x6 ↦ᵣ (a7 ^^^ b7)) ** (.x5 ↦ᵣ b7) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ eq_result) ** ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
       ((sp + 48) ↦ₘ 0) ** ((sp + 52) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0) ** ((sp + 60) ↦ₘ 0)) := by
  -- XOR-OR accumulation intermediate values
  let acc0 := a0 ^^^ b0
  let acc1 := acc0 ||| (a1 ^^^ b1)
  let acc2 := acc1 ||| (a2 ^^^ b2)
  let acc3 := acc2 ||| (a3 ^^^ b3)
  let acc4 := acc3 ||| (a4 ^^^ b4)
  let acc5 := acc4 ||| (a5 ^^^ b5)
  let acc6 := acc5 ||| (a6 ^^^ b6)
  let acc7 := acc6 ||| (a7 ^^^ b7)
  -- Limb 0: 3 instructions (LW, LW, XOR)
  have L0 := eq_limb0_spec 0 32 sp a0 b0 v7 v6 base
    (by validMem) (by validMem)
  -- Limb 1: 4 instructions (LW, LW, XOR, OR)
  have L1 := eq_or_limb_spec 4 36 sp a1 b1 b0 v5 acc0
    (base + 12) (by validMem) (by validMem)
  -- Limb 2: 4 instructions
  have L2 := eq_or_limb_spec 8 40 sp a2 b2 (a1 ^^^ b1) b1 acc1
    (base + 28) (by validMem) (by validMem)
  -- Limb 3: 4 instructions
  have L3 := eq_or_limb_spec 12 44 sp a3 b3 (a2 ^^^ b2) b2 acc2
    (base + 44) (by validMem) (by validMem)
  -- Limb 4: 4 instructions
  have L4 := eq_or_limb_spec 16 48 sp a4 b4 (a3 ^^^ b3) b3 acc3
    (base + 60) (by validMem) (by validMem)
  -- Limb 5: 4 instructions
  have L5 := eq_or_limb_spec 20 52 sp a5 b5 (a4 ^^^ b4) b4 acc4
    (base + 76) (by validMem) (by validMem)
  -- Limb 6: 4 instructions
  have L6 := eq_or_limb_spec 24 56 sp a6 b6 (a5 ^^^ b5) b5 acc5
    (base + 92) (by validMem) (by validMem)
  -- Limb 7: 4 instructions
  have L7 := eq_or_limb_spec 28 60 sp a7 b7 (a6 ^^^ b6) b6 acc6
    (base + 108) (by validMem) (by validMem)
  -- Store phase: 10 instructions (SLTIU + ADDI + 8 SW)
  have hvalid2 : ValidMemRange (sp + 32) 8 := by
    have := hvalid.split (n1 := 8) (n2 := 8)
    exact this.2
  have L8 := eq_result_store_spec sp acc7 (a7 ^^^ b7) b7 v11
    b0 b1 b2 b3 b4 b5 b6 b7 (base + 124) hvalid2
  runBlock L0 L1 L2 L3 L4 L5 L6 L7 L8

end EvmAsm
