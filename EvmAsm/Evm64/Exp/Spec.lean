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

/-- The boundary mini-program initializes the EXP accumulator to one, so the
    four output limbs assembled by the epilogue are exactly the EVM word `1`. -/
theorem exp_boundary_result_word_one :
    expResultWord
      ((0 : Word) + signExtend12 (1 : BitVec 12))
      (0 : Word) (0 : Word) (0 : Word) = (1 : EvmWord) := by
  unfold expResultWord EvmWord.fromLimbs
  rw [signExtend12_1]
  bv_decide

/-- Stack-shaped boundary bridge with the output slot exposed as the semantic
    EVM word `1`, rather than the raw four-limb epilogue assembly term. -/
theorem exp_boundary_result_one_stack_spec_within
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
       evmWordIs (evmSp + 32) (1 : EvmWord) **
       evmStackIs (evmSp + 64) rest) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      rw [exp_boundary_result_word_one] at hp
      exact hp)
    (exp_boundary_stack_spec_within sp evmSp cOld tOld m0 m1 m2 m3 base
      baseWord exponentWord rest)

/-- Boundary bridge with the produced one-word result folded into the visible
    stack tail. The old base operand cell is still framed explicitly because
    the boundary mini-program is only the prologue/epilogue skeleton, not the
    final EXP loop that consumes both operands semantically. -/
theorem exp_boundary_result_one_stack_tail_spec_within
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
       evmStackIs (evmSp + 32) ((1 : EvmWord) :: rest)) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      rw [evmStackIs_cons]
      rw [show (evmSp + 32 : Word) + 32 = evmSp + 64 from by bv_addr]
      xperm_hyp hp)
    (exp_boundary_result_one_stack_spec_within sp evmSp cOld tOld m0 m1 m2 m3 base
      baseWord exponentWord rest)

/-- Boundary bridge with the two input operands expressed as the ordinary EVM
    stack prefix. This is still a boundary-only theorem: it proves the
    prologue/epilogue skeleton's stack shape around the scratch accumulator,
    not the final exponentiation loop semantics. -/
theorem exp_boundary_result_one_full_stack_shape_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 : Word) (base : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    cpsTripleWithin 15 base (base + 60) (expBoundaryProgramCode base)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       evmStackIs evmSp (baseWord :: exponentWord :: rest))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ (0 : Word)) **
       evmWordIs sp (1 : EvmWord) **
       evmWordIs evmSp baseWord **
       evmStackIs (evmSp + 32) ((1 : EvmWord) :: rest)) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [evmStackIs_cons, evmStackIs_cons] at hp
      rw [show (evmSp + 32 : Word) + 32 = evmSp + 64 from by bv_addr] at hp
      xperm_hyp hp)
    (fun _ hp => hp)
    (exp_boundary_result_one_stack_tail_spec_within sp evmSp cOld tOld m0 m1 m2 m3 base
      baseWord exponentWord rest)

/-- Boundary bridge with both input and output operands expressed as ordinary
    EVM stack prefixes. The scratch accumulator at `sp` remains explicit,
    because the boundary mini-program writes it before the full EXP loop is
    available. -/
theorem exp_boundary_result_one_full_post_stack_shape_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 : Word) (base : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    cpsTripleWithin 15 base (base + 60) (expBoundaryProgramCode base)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       evmStackIs evmSp (baseWord :: exponentWord :: rest))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ (0 : Word)) **
       evmWordIs sp (1 : EvmWord) **
       evmStackIs evmSp (baseWord :: (1 : EvmWord) :: rest)) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      rw [evmStackIs_cons] at hp
      rw [evmStackIs_cons, evmStackIs_cons]
      rw [show (evmSp + 32 : Word) + 32 = evmSp + 64 from by bv_addr] at hp ⊢
      xperm_hyp hp)
    (exp_boundary_result_one_full_stack_shape_spec_within sp evmSp cOld tOld m0 m1 m2 m3 base
      baseWord exponentWord rest)

/-- The EXP boundary prologue initializes the loop counter to the semantic word
    value `256`; this lemma hides the raw ADDI/sign-extension spelling from
    stack-level consumers. -/
theorem exp_boundary_counter_256 :
    ((0 : Word) + signExtend12 (256 : BitVec 12)) = (256 : Word) := by
  unfold signExtend12
  bv_decide

/-- Boundary bridge with the stack-shaped postcondition and the loop counter
    exposed as the plain word `256`. -/
theorem exp_boundary_result_one_full_post_stack_shape_clean_counter_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 : Word) (base : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    cpsTripleWithin 15 base (base + 60) (expBoundaryProgramCode base)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       evmStackIs evmSp (baseWord :: exponentWord :: rest))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ (256 : Word)) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ (0 : Word)) **
       evmWordIs sp (1 : EvmWord) **
       evmStackIs evmSp (baseWord :: (1 : EvmWord) :: rest)) := by
  rw [← exp_boundary_counter_256]
  exact exp_boundary_result_one_full_post_stack_shape_spec_within
    sp evmSp cOld tOld m0 m1 m2 m3 base baseWord exponentWord rest

-- Placeholder: `evm_exp_stack_spec_within` lands in slice 6 (evm-asm-6snn).

end EvmAsm.Evm64
