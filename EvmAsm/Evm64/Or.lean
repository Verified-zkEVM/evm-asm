/-
  EvmAsm.Evm64.Or

  Full 256-bit EVM OR spec with ValidMemRange abstractions.
-/

import EvmAsm.Evm64.Bitwise

namespace EvmAsm.Rv64

/-- CodeReq for the 256-bit EVM OR operation.
    17 instructions = 68 bytes. 4 per-limb OR blocks + ADDI sp adjustment. -/
abbrev evm_or_code (base : Addr) : CodeReq :=
  CodeReq.ofProg base evm_or

set_option maxHeartbeats 6400000 in
/-- Full 256-bit EVM OR: composes 4 per-limb OR specs + sp adjustment. -/
theorem evm_or_spec (sp base : Addr)
    (a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code := evm_or_code base
    cpsTriple base (base + 68) code
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a3 ||| b3)) ** (.x6 ↦ᵣ b3) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ (a0 ||| b0)) ** ((sp + 40) ↦ₘ (a1 ||| b1)) ** ((sp + 48) ↦ₘ (a2 ||| b2)) ** ((sp + 56) ↦ₘ (a3 ||| b3))) := by
  have L0 := or_limb_spec 0 32 sp a0 b0 v7 v6 base (by validMem) (by validMem)
  have L1 := or_limb_spec 8 40 sp a1 b1 (a0 ||| b0) b0 (base + 16) (by validMem) (by validMem)
  have L2 := or_limb_spec 16 48 sp a2 b2 (a1 ||| b1) b1 (base + 32) (by validMem) (by validMem)
  have L3 := or_limb_spec 24 56 sp a3 b3 (a2 ||| b2) b2 (base + 48) (by validMem) (by validMem)
  have LADDI := addi_spec_gen_same .x12 sp 32 (base + 64) (by nofun)
  runBlock L0 L1 L2 L3 LADDI

set_option maxHeartbeats 6400000 in
/-- Stack-level 256-bit EVM OR. -/
theorem evm_or_stack_spec (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code := evm_or_code base
    cpsTriple base (base + 68) code
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a.getLimb 3 ||| b.getLimb 3)) ** (.x6 ↦ᵣ b.getLimb 3) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a ||| b)) := by
  have h_main := evm_or_spec sp base
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
      simp only [evmWordIs, EvmWord.getLimb_or]
      have : (sp : Addr) + 32 + 8 = sp + 40 := by bv_omega
      have : (sp : Addr) + 32 + 16 = sp + 48 := by bv_omega
      have : (sp : Addr) + 32 + 24 = sp + 56 := by bv_omega
      rw [‹sp + 32 + 8 = sp + 40›, ‹sp + 32 + 16 = sp + 48›, ‹sp + 32 + 24 = sp + 56›]
      xperm_hyp hq)
    h_main

end EvmAsm.Rv64
