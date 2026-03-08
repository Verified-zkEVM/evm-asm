/-
  EvmAsm.Evm32.Xor

  Full 256-bit EVM XOR spec composed from per-limb specs.
-/

import EvmAsm.Evm32.Bitwise
import EvmAsm.Rv32.Tactics.LiftSpec

open EvmAsm.Tactics

namespace EvmAsm

local macro "bv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]))

-- ============================================================================
-- Full 256-bit XOR spec
-- ============================================================================

set_option maxHeartbeats 6400000 in
/-- Full 256-bit EVM XOR: composes 8 per-limb XOR specs + sp adjustment.
    33 instructions total. Pops 2 stack words (A at sp, B at sp+32),
    writes A ^^^ B to sp+32..sp+60, advances sp by 32. -/
theorem evm_xor_spec (sp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 : Word)
    (hvalid : ValidMemRange sp 16) :
    let code :=
      -- Limb 0 code
      (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
      ((base + 8) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
      -- Limb 1 code
      ((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
      ((base + 24) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
      -- Limb 2 code
      ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
      ((base + 40) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
      -- Limb 3 code
      ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
      ((base + 56) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
      -- Limb 4 code
      ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
      ((base + 72) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
      -- Limb 5 code
      ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
      ((base + 88) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
      -- Limb 6 code
      ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
      ((base + 104) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
      -- Limb 7 code
      ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
      ((base + 120) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60) **
      -- ADDI
      ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)
    cpsTriple base (base + 132)
      (code **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      (code **
       -- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a7 ^^^ b7)) ** (.x6 ↦ᵣ b7) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ (a0 ^^^ b0)) ** ((sp + 36) ↦ₘ (a1 ^^^ b1)) ** ((sp + 40) ↦ₘ (a2 ^^^ b2)) ** ((sp + 44) ↦ₘ (a3 ^^^ b3)) **
       ((sp + 48) ↦ₘ (a4 ^^^ b4)) ** ((sp + 52) ↦ₘ (a5 ^^^ b5)) ** ((sp + 56) ↦ₘ (a6 ^^^ b6)) ** ((sp + 60) ↦ₘ (a7 ^^^ b7))) := by
  -- Compose 8 per-limb XOR specs + ADDI via runBlock
  have L0 := xor_limb_spec 0 32 sp a0 b0 v7 v6 base (by validMem) (by validMem)
  have L1 := xor_limb_spec 4 36 sp a1 b1 (a0 ^^^ b0) b0 (base + 16) (by validMem) (by validMem)
  have L2 := xor_limb_spec 8 40 sp a2 b2 (a1 ^^^ b1) b1 (base + 32) (by validMem) (by validMem)
  have L3 := xor_limb_spec 12 44 sp a3 b3 (a2 ^^^ b2) b2 (base + 48) (by validMem) (by validMem)
  have L4 := xor_limb_spec 16 48 sp a4 b4 (a3 ^^^ b3) b3 (base + 64) (by validMem) (by validMem)
  have L5 := xor_limb_spec 20 52 sp a5 b5 (a4 ^^^ b4) b4 (base + 80) (by validMem) (by validMem)
  have L6 := xor_limb_spec 24 56 sp a6 b6 (a5 ^^^ b5) b5 (base + 96) (by validMem) (by validMem)
  have L7 := xor_limb_spec 28 60 sp a7 b7 (a6 ^^^ b6) b6 (base + 112) (by validMem) (by validMem)
  have Laddi := addi_spec_gen_same .x12 sp 32 (base + 128) (by nofun)
  runBlock L0 L1 L2 L3 L4 L5 L6 L7 Laddi

-- ============================================================================
-- Stack-level XOR spec
-- ============================================================================

set_option maxHeartbeats 6400000 in
/-- Stack-level 256-bit EVM XOR: operates on two EvmWords via evmWordIs. -/
theorem evm_xor_stack_spec (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word)
    (hvalid : ValidMemRange sp 16) :
    let code :=
      -- Limb 0 code
      (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .LW .x6 .x12 32) **
      ((base + 8) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SW .x12 .x7 32) **
      -- Limb 1 code
      ((base + 16) ↦ᵢ .LW .x7 .x12 4) ** ((base + 20) ↦ᵢ .LW .x6 .x12 36) **
      ((base + 24) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SW .x12 .x7 36) **
      -- Limb 2 code
      ((base + 32) ↦ᵢ .LW .x7 .x12 8) ** ((base + 36) ↦ᵢ .LW .x6 .x12 40) **
      ((base + 40) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SW .x12 .x7 40) **
      -- Limb 3 code
      ((base + 48) ↦ᵢ .LW .x7 .x12 12) ** ((base + 52) ↦ᵢ .LW .x6 .x12 44) **
      ((base + 56) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SW .x12 .x7 44) **
      -- Limb 4 code
      ((base + 64) ↦ᵢ .LW .x7 .x12 16) ** ((base + 68) ↦ᵢ .LW .x6 .x12 48) **
      ((base + 72) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 76) ↦ᵢ .SW .x12 .x7 48) **
      -- Limb 5 code
      ((base + 80) ↦ᵢ .LW .x7 .x12 20) ** ((base + 84) ↦ᵢ .LW .x6 .x12 52) **
      ((base + 88) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 92) ↦ᵢ .SW .x12 .x7 52) **
      -- Limb 6 code
      ((base + 96) ↦ᵢ .LW .x7 .x12 24) ** ((base + 100) ↦ᵢ .LW .x6 .x12 56) **
      ((base + 104) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 108) ↦ᵢ .SW .x12 .x7 56) **
      -- Limb 7 code
      ((base + 112) ↦ᵢ .LW .x7 .x12 28) ** ((base + 116) ↦ᵢ .LW .x6 .x12 60) **
      ((base + 120) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 124) ↦ᵢ .SW .x12 .x7 60) **
      -- ADDI
      ((base + 128) ↦ᵢ .ADDI .x12 .x12 32)
    cpsTriple base (base + 132)
      (code **
       -- Registers + stack words
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (code **
       -- Registers + stack words (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a.getLimb 7 ^^^ b.getLimb 7)) ** (.x6 ↦ᵣ b.getLimb 7) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a ^^^ b)) := by
  have h_main := evm_xor_spec sp base
    (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3)
    (a.getLimb 4) (a.getLimb 5) (a.getLimb 6) (a.getLimb 7)
    (b.getLimb 0) (b.getLimb 1) (b.getLimb 2) (b.getLimb 3)
    (b.getLimb 4) (b.getLimb 5) (b.getLimb 6) (b.getLimb 7)
    v7 v6 hvalid
  liftSpec h_main post_simp [EvmWord.getLimb_xor]

end EvmAsm
