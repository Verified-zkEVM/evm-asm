/-
  EvmAsm.Evm64.Gt

  Full 256-bit EVM GT spec composed from per-limb LT specs (with swapped operands).
  GT(a, b) = LT(b, a): load b-limbs into x7 and a-limbs into x6.
  26 instructions total (3 + 3×6 + 5 store).
-/

import EvmAsm.Evm64.Comparison

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

/-- CodeReq for the 256-bit EVM GT operation.
    26 instructions = 104 bytes. GT(a, b) = LT(b, a): load b-limbs first. -/
abbrev evm_gt_code (base : Addr) : CodeReq :=
  CodeReq.ofProg base evm_gt

set_option maxHeartbeats 6400000 in
/-- Full 256-bit EVM GT: GT(a, b) = 1 iff a > b (unsigned).
    Computed as borrow chain of (b - a), same circuit as LT(b, a).
    Pops 2 stack words (A at sp, B at sp+32),
    writes result to sp+32..sp+56, advances sp by 32.
    26 instructions = 104 bytes total. -/
theorem evm_gt_spec (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (v7 v6 v5 v11 : Word)
    (hvalid : ValidMemRange sp 8) :
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
    let code := evm_gt_code base
    cpsTriple base (base + 104) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ temp3) ** (.x6 ↦ᵣ borrow3b) **
       (.x5 ↦ᵣ borrow3) ** (.x11 ↦ᵣ borrow3a) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ borrow3) ** ((sp + 40) ↦ₘ 0) ** ((sp + 48) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0)) := by
  intro borrow0
  intro borrow1a; intro temp1; intro borrow1b; intro borrow1
  intro borrow2a; intro temp2; intro borrow2b; intro borrow2
  intro borrow3a; intro temp3; intro borrow3b; intro borrow3
  -- Per-limb borrow specs (GT swaps: b-limbs into x7, a-limbs into x6)
  have L0 := lt_limb0_spec 32 0 sp b0 a0 v7 v6 v5 base (by validMem) (by validMem)
  have L1 := lt_limb_carry_spec 40 8 sp b1 a1 b0 a0 borrow0 v11 (base + 12) (by validMem) (by validMem)
  have L2 := lt_limb_carry_spec 48 16 sp b2 a2 temp1 borrow1b borrow1 borrow1a (base + 36) (by validMem) (by validMem)
  have L3 := lt_limb_carry_spec 56 24 sp b3 a3 temp2 borrow2b borrow2 borrow2a (base + 60) (by validMem) (by validMem)
  -- Store phase
  have A := addi_spec_gen_same .x12 sp 32 (base + 84) (by nofun)
  simp only [signExtend12_32] at A
  have S0 := sd_spec_gen .x12 .x5 (sp + 32) borrow3 b0 0 (base + 88) (by validMem)
  have S1 := sd_x0_spec_gen .x12 (sp + 32) b1 8 (base + 92) (by validMem)
  have S2 := sd_x0_spec_gen .x12 (sp + 32) b2 16 (base + 96) (by validMem)
  have S3 := sd_x0_spec_gen .x12 (sp + 32) b3 24 (base + 100) (by validMem)
  runBlock L0 L1 L2 L3 A S0 S1 S2 S3

end EvmAsm.Rv64
