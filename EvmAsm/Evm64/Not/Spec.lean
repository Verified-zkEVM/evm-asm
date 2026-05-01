/-
  EvmAsm.Evm64.Not.Spec

  Full 256-bit EVM NOT spec composed from per-limb specs.
-/

import EvmAsm.Evm64.Not.LimbSpec
import EvmAsm.Evm64.Stack
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

/-- Bridge lemma: `signExtend12 (-1)` is `-1` as a 64-bit `Word`. -/
private theorem signExtend12_neg1_eq_neg1 :
    signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide

/-- Bridge lemma: a 64-bit XOR with `-1` is bitwise complement. -/
private theorem word_xor_neg1_eq_not (a : Word) :
    a ^^^ signExtend12 (-1 : BitVec 12) = ~~~ a := by
  rw [signExtend12_neg1_eq_neg1]; bv_decide

/-- Per-limb bridge: `(a.getLimbN k) ^^^ -1 = (~~~ a).getLimbN k` for `k < 4`. -/
private theorem getLimbN_xor_neg1 (a : EvmWord) {k : Nat} (hk : k < 4) :
    a.getLimbN k ^^^ signExtend12 (-1 : BitVec 12) = (~~~ a).getLimbN k := by
  rw [word_xor_neg1_eq_not, EvmWord.getLimbN_not hk]

/-- Stack-level 256-bit EVM NOT: operates on an EvmWord via evmWordIs.
    Unary: pops 1, pushes 1, sp unchanged. Result is bitwise complement. -/
theorem evm_not_stack_spec_within (sp base : Word)
    (a : EvmWord) (v7 : Word) :
    let code := evm_not_code base
    cpsTripleWithin 12 base (base + 48) code
      (-- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
       evmWordIs sp a)
      (-- Registers + memory (updated)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (~~~ a).getLimbN 3) **
       evmWordIs sp (~~~ a)) := by
  have h_main := evm_not_spec_within sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) v7
  exact cpsTripleWithin_weaken
    (fun h hp => by
      simp only [evmWordIs] at hp
      xperm_hyp hp)
    (fun h hq => by
      unfold evmWordIs
      simp only [
        getLimbN_xor_neg1 a (by decide : 0 < 4),
        getLimbN_xor_neg1 a (by decide : 1 < 4),
        getLimbN_xor_neg1 a (by decide : 2 < 4),
        getLimbN_xor_neg1 a (by decide : 3 < 4)] at hq
      xperm_hyp hq)
    h_main


end EvmAsm.Evm64
