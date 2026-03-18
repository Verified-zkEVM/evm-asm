/-
  EvmAsm.Evm64.And

  Full 256-bit EVM AND spec with ValidMemRange abstractions.
-/

import EvmAsm.Evm64.Bitwise

namespace EvmAsm.Rv64

-- ============================================================================
-- Full 256-bit AND spec
-- ============================================================================

/-- CodeReq for the 256-bit EVM AND operation.
    17 instructions = 68 bytes. 4 per-limb AND blocks + ADDI sp adjustment. -/
abbrev evm_and_code (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 0))
  (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 32))
  (CodeReq.union (CodeReq.singleton (base + 8) (.AND .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x7 32))
  (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x7 .x12 8))
  (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x6 .x12 40))
  (CodeReq.union (CodeReq.singleton (base + 24) (.AND .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SD .x12 .x7 40))
  (CodeReq.union (CodeReq.singleton (base + 32) (.LD .x7 .x12 16))
  (CodeReq.union (CodeReq.singleton (base + 36) (.LD .x6 .x12 48))
  (CodeReq.union (CodeReq.singleton (base + 40) (.AND .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 44) (.SD .x12 .x7 48))
  (CodeReq.union (CodeReq.singleton (base + 48) (.LD .x7 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 52) (.LD .x6 .x12 56))
  (CodeReq.union (CodeReq.singleton (base + 56) (.AND .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 60) (.SD .x12 .x7 56))
   (CodeReq.singleton (base + 64) (.ADDI .x12 .x12 32)))))))))))))))))

set_option maxHeartbeats 6400000 in
/-- Full 256-bit EVM AND: composes 4 per-limb AND specs + sp adjustment.
    17 instructions total. Pops 2 stack words (A at sp, B at sp+32),
    writes A &&& B to sp+32..sp+56, advances sp by 32. -/
theorem evm_and_spec (sp base : Addr)
    (a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code := evm_and_code base
    cpsTriple base (base + 68) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a3 &&& b3)) ** (.x6 ↦ᵣ b3) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ (a0 &&& b0)) ** ((sp + 40) ↦ₘ (a1 &&& b1)) ** ((sp + 48) ↦ₘ (a2 &&& b2)) ** ((sp + 56) ↦ₘ (a3 &&& b3))) := by
  have L0 := and_limb_spec 0 32 sp a0 b0 v7 v6 base (by validMem) (by validMem)
  have L1 := and_limb_spec 8 40 sp a1 b1 (a0 &&& b0) b0 (base + 16) (by validMem) (by validMem)
  have L2 := and_limb_spec 16 48 sp a2 b2 (a1 &&& b1) b1 (base + 32) (by validMem) (by validMem)
  have L3 := and_limb_spec 24 56 sp a3 b3 (a2 &&& b2) b2 (base + 48) (by validMem) (by validMem)
  have LADDI := addi_spec_gen_same .x12 sp 32 (base + 64) (by nofun)
  runBlock L0 L1 L2 L3 LADDI

-- ============================================================================
-- Stack-level AND spec
-- ============================================================================

set_option maxHeartbeats 6400000 in
/-- Stack-level 256-bit EVM AND: operates on two EvmWords via evmWordIs. -/
theorem evm_and_stack_spec (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code := evm_and_code base
    cpsTriple base (base + 68) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a.getLimb 3 &&& b.getLimb 3)) ** (.x6 ↦ᵣ b.getLimb 3) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a &&& b)) := by
  have h_main := evm_and_spec sp base
    (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3)
    (b.getLimb 0) (b.getLimb 1) (b.getLimb 2) (b.getLimb 3)
    v7 v6 hvalid
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      simp only [evmWordIs] at hp
      have : (sp : Addr) + 32 + 8 = sp + 40 := by bv_omega
      have : (sp : Addr) + 32 + 16 = sp + 48 := by bv_omega
      have : (sp : Addr) + 32 + 24 = sp + 56 := by bv_omega
      rw [‹sp + 32 + 8 = sp + 40›, ‹sp + 32 + 16 = sp + 48›, ‹sp + 32 + 24 = sp + 56›] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs, EvmWord.getLimb_and]
      have : (sp : Addr) + 32 + 8 = sp + 40 := by bv_omega
      have : (sp : Addr) + 32 + 16 = sp + 48 := by bv_omega
      have : (sp : Addr) + 32 + 24 = sp + 56 := by bv_omega
      rw [‹sp + 32 + 8 = sp + 40›, ‹sp + 32 + 16 = sp + 48›, ‹sp + 32 + 24 = sp + 56›]
      xperm_hyp hq)
    h_main

end EvmAsm.Rv64
