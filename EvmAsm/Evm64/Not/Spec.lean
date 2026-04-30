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
theorem evm_not_spec_within (sp base : Word)
    (a0 a1 a2 a3 : Word)
    (v7 : Word) :
    let c := signExtend12 (-1 : BitVec 12)
    let code := evm_not_code base
    cpsTripleWithin 12 base (base + 48) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a3 ^^^ c)) **
       (sp ↦ₘ (a0 ^^^ c)) ** ((sp + 8) ↦ₘ (a1 ^^^ c)) ** ((sp + 16) ↦ₘ (a2 ^^^ c)) ** ((sp + 24) ↦ₘ (a3 ^^^ c))) := by
  -- Compose 4 per-limb NOT specs via runBlock (manual mode with address normalization)
  have L0 := not_limb_spec_within 0 sp a0 v7 base
  have L1 := not_limb_spec_within 8 sp a1 (a0 ^^^ signExtend12 (-1 : BitVec 12)) (base + 12)
  have L2 := not_limb_spec_within 16 sp a2 (a1 ^^^ signExtend12 (-1 : BitVec 12)) (base + 24)
  have L3 := not_limb_spec_within 24 sp a3 (a2 ^^^ signExtend12 (-1 : BitVec 12)) (base + 36)
  runBlock L0 L1 L2 L3


-- ============================================================================
-- Stack-level NOT spec
-- ============================================================================


end EvmAsm.Evm64
