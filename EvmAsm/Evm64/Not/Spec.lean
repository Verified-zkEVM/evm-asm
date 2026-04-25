/-
  EvmAsm.Evm64.Not.Spec

  Full 256-bit EVM NOT spec composed from per-limb specs.
-/

import EvmAsm.Evm64.Not.LimbSpec
import EvmAsm.Rv64.Tactics.XSimp

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Full NOT spec
-- ============================================================================

/-- CodeReq for the 256-bit EVM NOT operation.
    12 instructions = 48 bytes. 4 per-limb XORI(-1) blocks. -/
abbrev evm_not_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_not

/-- Full 256-bit EVM NOT: composes 4 per-limb NOT specs.
    12 instructions total. Unary: complements each limb in-place, sp unchanged. -/
theorem evm_not_spec (sp base : Word)
    (a0 a1 a2 a3 : Word)
    (v7 : Word) :
    let c := signExtend12 (-1 : BitVec 12)
    let code := evm_not_code base
    cpsTriple base (base + 48) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a3 ^^^ c)) **
       (sp ↦ₘ (a0 ^^^ c)) ** ((sp + 8) ↦ₘ (a1 ^^^ c)) ** ((sp + 16) ↦ₘ (a2 ^^^ c)) ** ((sp + 24) ↦ₘ (a3 ^^^ c))) := by
  -- Compose 4 per-limb NOT specs via runBlock (manual mode with address normalization)
  have L0 := not_limb_spec 0 sp a0 v7 base
  have L1 := not_limb_spec 8 sp a1 (a0 ^^^ signExtend12 (-1 : BitVec 12)) (base + 12)
  have L2 := not_limb_spec 16 sp a2 (a1 ^^^ signExtend12 (-1 : BitVec 12)) (base + 24)
  have L3 := not_limb_spec 24 sp a3 (a2 ^^^ signExtend12 (-1 : BitVec 12)) (base + 36)
  runBlock L0 L1 L2 L3

-- ============================================================================
-- Stack-level NOT spec
-- ============================================================================

theorem signExtend12_neg1_eq_allOnes : signExtend12 (-1 : BitVec 12) = BitVec.allOnes 64 := by
  decide

/-- Stack-level 256-bit EVM NOT: complements an EvmWord in-place. -/
theorem evm_not_stack_spec (sp base : Word)
    (a : EvmWord) (v7 : Word) :
    let c := signExtend12 (-1 : BitVec 12)
    let code := evm_not_code base
    cpsTriple base (base + 48) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** evmWordIs sp a)
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a.getLimbN 3 ^^^ c)) ** evmWordIs sp (~~~a)) := by
  -- Helper: (~~~a).getLimbN k = a.getLimbN k ^^^ signExtend12 (-1)
  have not_limb_eq : ∀ (k : Nat), k < 4 →
      (~~~a).getLimbN k = a.getLimbN k ^^^ signExtend12 (-1 : BitVec 12) := by
    intro k hk
    rw [EvmWord.getLimbN_not hk, BitVec.not_def, BitVec.xor_comm, ← signExtend12_neg1_eq_allOnes]
  -- Apply evm_not_spec with individual limbs
  have h_main := evm_not_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    v7
  exact cpsTriple_weaken
    (fun h hp => by
      simp only [evmWordIs] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs, not_limb_eq 0 (by omega), not_limb_eq 1 (by omega),
                 not_limb_eq 2 (by omega), not_limb_eq 3 (by omega)]
      xperm_hyp hq)
    h_main

end EvmAsm.Evm64
