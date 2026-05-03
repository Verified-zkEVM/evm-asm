/-
  EvmAsm.Evm64.Exp.Spec

  Top-level (semantic / stack-level) cpsTriple spec for `evm_exp`,
  bridging the limb-level loop composition to a single `evmWordIs`
  pre/post pair.

  Skeleton placeholder for GH #92 (beads slice evm-asm-cf2c). The actual
  `evm_exp_stack_spec` / `evm_exp_stack_spec_within` theorem lands in the
  semantic slice (evm-asm-6snn).
-/

import EvmAsm.Evm64.Exp.Compose.Base
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.Exp.Compose

/-- Stack-shaped bridge for the current EXP boundary mini-program.

    This is not the final `evm_exp_stack_spec_within`: the 256-iteration loop
    and multiplication scaffold are still pending. It packages the verified
    boundary composition as the first semantic bridge in this file: the
    prologue initializes the scratch accumulator to one, the epilogue writes
    that accumulator to the result slot at `evmSp + 32`, and the untouched
    first operand plus stack tail are framed through the program. -/
theorem exp_boundary_stack_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 : Word) (base : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    cpsTripleWithin 15 base (base + 60) (expBoundaryProgramCode base)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       evmWordIs evmSp baseWord **
       evmWordIs (evmSp + 32) exponentWord **
       evmStackIs (evmSp + 64) rest)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ (0 : Word)) **
       evmWordIs sp (1 : EvmWord) **
       evmWordIs evmSp baseWord **
       evmWordIs (evmSp + 32) (expResultWord
        ((0 : Word) + signExtend12 (1 : BitVec 12))
        (0 : Word) (0 : Word) (0 : Word)) **
       evmStackIs (evmSp + 64) rest) := by
  let frame : Assertion :=
    evmWordIs evmSp baseWord ** evmStackIs (evmSp + 64) rest
  have hBoundary := expBoundaryProgram_spec_within
    sp evmSp cOld tOld m0 m1 m2 m3
    (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
    (exponentWord.getLimbN 2) (exponentWord.getLimbN 3) base
  have hFramed := cpsTripleWithin_frameR frame (by pcFree) hBoundary
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [evmWordIs_sp32_limbs_eq evmSp exponentWord _ _ _ _
        rfl rfl rfl rfl] at hp
      rw [← show evmSp + signExtend12 (32 : BitVec 12) = evmSp + 32 from by
        rw [signExtend12_32]] at hp
      rw [← show evmSp + signExtend12 (40 : BitVec 12) = evmSp + 40 from by
        rw [signExtend12_40]] at hp
      rw [← show evmSp + signExtend12 (48 : BitVec 12) = evmSp + 48 from by
        rw [signExtend12_48]] at hp
      rw [← show evmSp + signExtend12 (56 : BitVec 12) = evmSp + 56 from by
        rw [signExtend12_56]] at hp
      dsimp [frame] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      rw [← exp_prologue_result_word_one sp]
      dsimp [frame] at hp ⊢
      xperm_hyp hp)
    hFramed

-- Placeholder: `evm_exp_stack_spec_within` lands in slice 6 (evm-asm-6snn).

end EvmAsm.Evm64
