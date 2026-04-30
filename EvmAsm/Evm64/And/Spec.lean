/-
  EvmAsm.Evm64.And.Spec

  Full 256-bit EVM AND spec.
-/

-- `And.LimbSpec → And.Program → Stack → SpAddr`.
import EvmAsm.Evm64.And.LimbSpec
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Full 256-bit AND spec
-- ============================================================================

/-- CodeReq for the 256-bit EVM AND operation.
    17 instructions = 68 bytes. 4 per-limb AND blocks + ADDI sp adjustment. -/
abbrev evm_and_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_and

/-- Full 256-bit EVM AND: composes 4 per-limb AND specs + sp adjustment.
    17 instructions total. Pops 2 stack words (A at sp, B at sp+32),
    writes A &&& B to sp+32..sp+56, advances sp by 32. -/
theorem evm_and_spec_within (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 : Word) :
    let code := evm_and_code base
    cpsTripleWithin 17 base (base + 68) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a3 &&& b3)) ** (.x6 ↦ᵣ b3) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ (a0 &&& b0)) ** ((sp + 40) ↦ₘ (a1 &&& b1)) ** ((sp + 48) ↦ₘ (a2 &&& b2)) ** ((sp + 56) ↦ₘ (a3 &&& b3))) := by
  have L0 := and_limb_spec_within 0 32 sp a0 b0 v7 v6 base
  have L1 := and_limb_spec_within 8 40 sp a1 b1 (a0 &&& b0) b0 (base + 16)
  have L2 := and_limb_spec_within 16 48 sp a2 b2 (a1 &&& b1) b1 (base + 32)
  have L3 := and_limb_spec_within 24 56 sp a3 b3 (a2 &&& b2) b2 (base + 48)
  have LADDI := addi_spec_gen_same_within .x12 sp 32 (base + 64) (by nofun)
  runBlock L0 L1 L2 L3 LADDI


-- ============================================================================
-- Stack-level AND spec
-- ============================================================================

/-- Stack-level 256-bit EVM AND: operates on two EvmWords via evmWordIs. -/
theorem evm_and_stack_spec_within (sp base : Word)
    (a b : EvmWord) (v7 v6 : Word) :
    let code := evm_and_code base
    cpsTripleWithin 17 base (base + 68) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a.getLimbN 3 &&& b.getLimbN 3)) ** (.x6 ↦ᵣ b.getLimbN 3) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a &&& b)) := by
  have h_main := evm_and_spec_within sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v7 v6
  exact cpsTripleWithin_weaken
    (fun h hp => by
      simp only [evmWordIs] at hp
      rw [spAddr32_8, spAddr32_16, spAddr32_24] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs, EvmWord.getLimbN_and]
      rw [spAddr32_8, spAddr32_16, spAddr32_24]
      xperm_hyp hq)
    h_main


end EvmAsm.Evm64
