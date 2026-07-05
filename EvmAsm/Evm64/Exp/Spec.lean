/-
  EvmAsm.Evm64.Exp.Spec

  Top-level (semantic / stack-level) cpsTriple spec for `evm_exp`,
  bridging the limb-level loop composition to a single `evmWordIs`
  pre/post pair.

  This file currently exposes stack-shaped boundary-program bridges that feed
  the semantic layer.  The final full-loop `evm_exp_stack_spec_within` belongs
  in `EvmAsm.Evm64.Exp.Semantic` once the 256-iteration composition is tied to
  `EvmWord.exp`.
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Evm64.Exp.Compose.Base
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedHeadroomFullLoop
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedHeadroomFramedLiveStackPost
import EvmAsm.Evm64.Exp.StackExecutionBridge
import EvmAsm.Evm64.EvmWordArith.Exp
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64

open EvmAsm.Rv64 (Assertion cpsTripleWithin cpsTripleWithin_frameR
  cpsTripleWithin_weaken regOwn signExtend12 signExtend12_0 signExtend12_1
  signExtend12_8 signExtend12_16 signExtend12_24 signExtend12_32
  signExtend12_40 signExtend12_48 signExtend12_56)
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
  decide

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
  rw [EvmAsm.Evm64.Exp.AddrNorm.exp_se12_256]
  bv_omega

/-- The EXP boundary epilogue advances the EVM stack pointer by one word. -/
theorem exp_boundary_stack_pointer_advance_32 (evmSp : Word) :
    evmSp + signExtend12 (32 : BitVec 12) = evmSp + 32 := by
  rw [signExtend12_32]

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

/-- Boundary bridge with the stack-shaped postcondition and register values
    exposed in their plain consumer-facing forms. -/
theorem exp_boundary_result_one_full_post_stack_shape_clean_regs_spec_within
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
       (.x12 ↦ᵣ (evmSp + 32)) **
       (.x5 ↦ᵣ (0 : Word)) **
       evmWordIs sp (1 : EvmWord) **
       evmStackIs evmSp (baseWord :: (1 : EvmWord) :: rest)) := by
  rw [← exp_boundary_stack_pointer_advance_32 evmSp]
  exact exp_boundary_result_one_full_post_stack_shape_clean_counter_spec_within
    sp evmSp cOld tOld m0 m1 m2 m3 base baseWord exponentWord rest

theorem exp_boundary_result_exp_zero_full_post_stack_shape_clean_regs_spec_within
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
       (.x12 ↦ᵣ (evmSp + 32)) **
       (.x5 ↦ᵣ (0 : Word)) **
       evmWordIs sp (1 : EvmWord) **
       evmStackIs evmSp (baseWord :: EvmWord.exp baseWord 0 :: rest)) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      rw [EvmWord.exp_zero_right baseWord]
      exact hp)
    (exp_boundary_result_one_full_post_stack_shape_clean_regs_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 base baseWord exponentWord rest)


/-- Headroom full-loop EXP surface with the input expressed as the ordinary
    two-operand EVM stack prefix. The post is still folded: it exposes the final
    live stack at `evmSp + 32` and preserves the consumed base cell plus the
    headroom/leftover frame for the final public wrapper cleanup. -/
theorem evm_exp_headroom_visible_stack_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
       ((evmSp + signExtend12 ((-128) : BitVec 12)) ↦ₘ h0) **
       ((evmSp + signExtend12 ((-120) : BitVec 12)) ↦ₘ h1) **
       ((evmSp + signExtend12 ((-112) : BitVec 12)) ↦ₘ h2) **
       ((evmSp + signExtend12 ((-104) : BitVec 12)) ↦ₘ h3) **
       ((evmSp + signExtend12 ((-96) : BitVec 12)) ↦ₘ h4) **
       ((evmSp + signExtend12 ((-88) : BitVec 12)) ↦ₘ h5) **
       ((evmSp + signExtend12 ((-80) : BitVec 12)) ↦ₘ h6) **
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ h7) **
       (.x18 ↦ᵣ v18) ** (.x1 ↦ᵣ vOld) **
       regOwn .x10 ** regOwn .x7 ** regOwn .x11 **
       evmWordIs (evmSp + signExtend12 ((-64) : BitVec 12)) dWord **
       evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) eWord **
       evmStackIs evmSp (baseWord :: exponentWord :: rest)))
      (EvmAsm.Evm64.Exp.Compose.expHeadroomFinalVisiblePost
        sp evmSp baseWord exponentWord rest) := by
  have h := EvmAsm.Evm64.Exp.Compose.exp_headroom_entry_to_final_visible_post
    sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
    (baseWord.getLimbN 0) (baseWord.getLimbN 1)
    (baseWord.getLimbN 2) (baseWord.getLimbN 3)
    (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
    (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
    h0 h1 h2 h3 h4 h5 h6 h7 base
    dWord eWord rest lookahead vOld v18 hbase
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [evmStackIs_cons, evmStackIs_cons] at hp
      rw [evmWordIs_sp_limbs_eq evmSp baseWord _ _ _ _ rfl rfl rfl rfl] at hp
      rw [evmWordIs_sp32_limbs_eq evmSp exponentWord _ _ _ _ rfl rfl rfl rfl] at hp
      rw [show (evmSp + 32 + 32 : Word) = evmSp + 64 from by bv_addr] at hp
      rw [EvmAsm.Evm64.Exp.Compose.expHeadroomLoopEntryBridgeFrame]
      simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24,
        signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56] at hp ⊢
      rw [show (evmSp + 0 : Word) = evmSp from by bv_omega]
      xperm_hyp hp)
    (fun _ hp => by
      rw [expResultWord_getLimbN_self baseWord,
        expResultWord_getLimbN_self exponentWord] at hp
      exact hp)
    h

/-- Headroom full-loop EXP surface with the loop-exit pure fact consumed into
    the final control resources. This is stronger than
    `evm_exp_headroom_visible_stack_spec_within`: the post exposes `x9` as the
    concrete zero word and no longer carries an existential loop counter. -/
theorem evm_exp_headroom_clean_visible_stack_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
       ((evmSp + signExtend12 ((-128) : BitVec 12)) ↦ₘ h0) **
       ((evmSp + signExtend12 ((-120) : BitVec 12)) ↦ₘ h1) **
       ((evmSp + signExtend12 ((-112) : BitVec 12)) ↦ₘ h2) **
       ((evmSp + signExtend12 ((-104) : BitVec 12)) ↦ₘ h3) **
       ((evmSp + signExtend12 ((-96) : BitVec 12)) ↦ₘ h4) **
       ((evmSp + signExtend12 ((-88) : BitVec 12)) ↦ₘ h5) **
       ((evmSp + signExtend12 ((-80) : BitVec 12)) ↦ₘ h6) **
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ h7) **
       (.x18 ↦ᵣ v18) ** (.x1 ↦ᵣ vOld) **
       regOwn .x10 ** regOwn .x7 ** regOwn .x11 **
       evmWordIs (evmSp + signExtend12 ((-64) : BitVec 12)) dWord **
       evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) eWord **
       evmStackIs evmSp (baseWord :: exponentWord :: rest)))
      (EvmAsm.Evm64.Exp.Compose.expHeadroomFinalCleanVisiblePost
        sp evmSp baseWord exponentWord rest) := by
  have h := EvmAsm.Evm64.Exp.Compose.exp_headroom_entry_to_final_clean_visible_post
    sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
    (baseWord.getLimbN 0) (baseWord.getLimbN 1)
    (baseWord.getLimbN 2) (baseWord.getLimbN 3)
    (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
    (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
    h0 h1 h2 h3 h4 h5 h6 h7 base
    dWord eWord rest lookahead vOld v18 hbase
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [evmStackIs_cons, evmStackIs_cons] at hp
      rw [evmWordIs_sp_limbs_eq evmSp baseWord _ _ _ _ rfl rfl rfl rfl] at hp
      rw [evmWordIs_sp32_limbs_eq evmSp exponentWord _ _ _ _ rfl rfl rfl rfl] at hp
      rw [show (evmSp + 32 + 32 : Word) = evmSp + 64 from by bv_addr] at hp
      rw [EvmAsm.Evm64.Exp.Compose.expHeadroomLoopEntryBridgeFrame]
      simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24,
        signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56] at hp ⊢
      rw [show (evmSp + 0 : Word) = evmSp from by bv_omega]
      xperm_hyp hp)
    (fun _ hp => by
      rw [expResultWord_getLimbN_self baseWord,
        expResultWord_getLimbN_self exponentWord] at hp
      exact hp)
    h

/-- Headroom full-loop EXP surface with the final post folded into stack-shaped
    assertions: the result scratch is `evmWordIs sp result`, and the consumed
    base cell plus live result tail are `evmStackIs evmSp (base :: result :: rest)`.
    The headroom/leftover frame remains explicit pending the public wrapper. -/
theorem evm_exp_headroom_clean_stack_visible_stack_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
       ((evmSp + signExtend12 ((-128) : BitVec 12)) ↦ₘ h0) **
       ((evmSp + signExtend12 ((-120) : BitVec 12)) ↦ₘ h1) **
       ((evmSp + signExtend12 ((-112) : BitVec 12)) ↦ₘ h2) **
       ((evmSp + signExtend12 ((-104) : BitVec 12)) ↦ₘ h3) **
       ((evmSp + signExtend12 ((-96) : BitVec 12)) ↦ₘ h4) **
       ((evmSp + signExtend12 ((-88) : BitVec 12)) ↦ₘ h5) **
       ((evmSp + signExtend12 ((-80) : BitVec 12)) ↦ₘ h6) **
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ h7) **
       (.x18 ↦ᵣ v18) ** (.x1 ↦ᵣ vOld) **
       regOwn .x10 ** regOwn .x7 ** regOwn .x11 **
       evmWordIs (evmSp + signExtend12 ((-64) : BitVec 12)) dWord **
       evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) eWord **
       evmStackIs evmSp (baseWord :: exponentWord :: rest)))
      (EvmAsm.Evm64.Exp.Compose.expHeadroomFinalCleanStackVisiblePost
        sp evmSp baseWord exponentWord rest) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp =>
      EvmAsm.Evm64.Exp.Compose.expHeadroomFinalCleanVisiblePost_to_cleanStackVisiblePost hp)
    (evm_exp_headroom_clean_visible_stack_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base
      baseWord exponentWord dWord eWord rest lookahead vOld v18 hbase)

@[irreducible]
def evmExpHeadroomPre
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord) : Assertion :=
  ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
   (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
   ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
   ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
   ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
   ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
   (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
   ((evmSp + signExtend12 ((-128) : BitVec 12)) ↦ₘ h0) **
   ((evmSp + signExtend12 ((-120) : BitVec 12)) ↦ₘ h1) **
   ((evmSp + signExtend12 ((-112) : BitVec 12)) ↦ₘ h2) **
   ((evmSp + signExtend12 ((-104) : BitVec 12)) ↦ₘ h3) **
   ((evmSp + signExtend12 ((-96) : BitVec 12)) ↦ₘ h4) **
   ((evmSp + signExtend12 ((-88) : BitVec 12)) ↦ₘ h5) **
   ((evmSp + signExtend12 ((-80) : BitVec 12)) ↦ₘ h6) **
   ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ h7) **
   (.x18 ↦ᵣ v18) ** (.x1 ↦ᵣ vOld) **
   regOwn .x10 ** regOwn .x7 ** regOwn .x11 **
   evmWordIs (evmSp + signExtend12 ((-64) : BitVec 12)) dWord **
   evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) eWord **
   evmStackIs evmSp (baseWord :: exponentWord :: rest))

theorem evmExpHeadroomPre_unfold
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord) :
    evmExpHeadroomPre sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
        h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld baseWord exponentWord dWord eWord rest =
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
       ((evmSp + signExtend12 ((-128) : BitVec 12)) ↦ₘ h0) **
       ((evmSp + signExtend12 ((-120) : BitVec 12)) ↦ₘ h1) **
       ((evmSp + signExtend12 ((-112) : BitVec 12)) ↦ₘ h2) **
       ((evmSp + signExtend12 ((-104) : BitVec 12)) ↦ₘ h3) **
       ((evmSp + signExtend12 ((-96) : BitVec 12)) ↦ₘ h4) **
       ((evmSp + signExtend12 ((-88) : BitVec 12)) ↦ₘ h5) **
       ((evmSp + signExtend12 ((-80) : BitVec 12)) ↦ₘ h6) **
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ h7) **
       (.x18 ↦ᵣ v18) ** (.x1 ↦ᵣ vOld) **
       regOwn .x10 ** regOwn .x7 ** regOwn .x11 **
       evmWordIs (evmSp + signExtend12 ((-64) : BitVec 12)) dWord **
       evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) eWord **
       evmStackIs evmSp (baseWord :: exponentWord :: rest))) := by
  delta evmExpHeadroomPre
  rfl

theorem evmExpHeadroomPre_pcFree
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord) :
    (evmExpHeadroomPre sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld baseWord exponentWord dWord eWord rest).pcFree := by
  rw [evmExpHeadroomPre_unfold]
  pcFree

instance pcFreeInst_evmExpHeadroomPre
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (evmExpHeadroomPre sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
        h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld baseWord exponentWord dWord eWord rest) :=
  ⟨evmExpHeadroomPre_pcFree sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
    h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld baseWord exponentWord dWord eWord rest⟩

structure EvmExpHeadroomPreWitness where
  cOld : Word
  tOld : Word
  c6Old : Word
  c16Old : Word
  c19Old : Word
  m0 : Word
  m1 : Word
  m2 : Word
  m3 : Word
  v6 : Word
  h0 : Word
  h1 : Word
  h2 : Word
  h3 : Word
  h4 : Word
  h5 : Word
  h6 : Word
  h7 : Word
  v18 : Word
  vOld : Word
  dWord : EvmWord
  eWord : EvmWord

@[irreducible]
def evmExpHeadroomExistentialPre
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion :=
  fun ps => ∃ w : EvmExpHeadroomPreWitness,
    evmExpHeadroomPre sp evmSp w.cOld w.tOld w.c6Old w.c16Old w.c19Old
      w.m0 w.m1 w.m2 w.m3 w.v6
      w.h0 w.h1 w.h2 w.h3 w.h4 w.h5 w.h6 w.h7 w.v18 w.vOld
      baseWord exponentWord w.dWord w.eWord rest ps

theorem evmExpHeadroomExistentialPre_unfold
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    evmExpHeadroomExistentialPre sp evmSp baseWord exponentWord rest =
      (fun ps => ∃ w : EvmExpHeadroomPreWitness,
        evmExpHeadroomPre sp evmSp w.cOld w.tOld w.c6Old w.c16Old w.c19Old
          w.m0 w.m1 w.m2 w.m3 w.v6
          w.h0 w.h1 w.h2 w.h3 w.h4 w.h5 w.h6 w.h7 w.v18 w.vOld
          baseWord exponentWord w.dWord w.eWord rest ps) := by
  delta evmExpHeadroomExistentialPre
  rfl

@[irreducible]
def evmExpHeadroomPublicStackPre
    (evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion :=
  fun ps => ∃ sp : Word,
    evmExpHeadroomExistentialPre sp evmSp baseWord exponentWord rest ps

theorem evmExpHeadroomPublicStackPre_unfold
    (evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    evmExpHeadroomPublicStackPre evmSp baseWord exponentWord rest =
      (fun ps => ∃ sp : Word,
        evmExpHeadroomExistentialPre sp evmSp baseWord exponentWord rest ps) := by
  delta evmExpHeadroomPublicStackPre
  rfl

@[irreducible]
def evmExpHeadroomPublicStackPost
    (evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion :=
  fun ps => ∃ sp : Word,
    EvmAsm.Evm64.Exp.Compose.expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost
      sp evmSp baseWord exponentWord rest ps

theorem evmExpHeadroomPublicStackPost_unfold
    (evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    evmExpHeadroomPublicStackPost evmSp baseWord exponentWord rest =
      (fun ps => ∃ sp : Word,
        EvmAsm.Evm64.Exp.Compose.expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost
          sp evmSp baseWord exponentWord rest ps) := by
  delta evmExpHeadroomPublicStackPost
  rfl

theorem evmExpHeadroomPublicStackPost_pcFree
    (evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    (evmExpHeadroomPublicStackPost evmSp baseWord exponentWord rest).pcFree := by
  intro ps h_post
  rw [evmExpHeadroomPublicStackPost_unfold] at h_post
  obtain ⟨sp, h_post⟩ := h_post
  exact EvmAsm.Evm64.Exp.Compose.expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost_pcFree
    sp evmSp baseWord exponentWord rest ps h_post

instance pcFreeInst_evmExpHeadroomPublicStackPost
    (evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree (evmExpHeadroomPublicStackPost evmSp baseWord exponentWord rest) :=
  ⟨evmExpHeadroomPublicStackPost_pcFree evmSp baseWord exponentWord rest⟩

@[irreducible]
def evmExpHeadroomPublicLeftoverFrame
    (evmSp : Word) : Assertion :=
  fun ps => ∃ sp : Word,
    EvmAsm.Evm64.Exp.Compose.expHeadroomFinalAllRegsOwnedLeftoverFrame sp evmSp ps

theorem evmExpHeadroomPublicLeftoverFrame_unfold
    (evmSp : Word) :
    evmExpHeadroomPublicLeftoverFrame evmSp =
      (fun ps => ∃ sp : Word,
        EvmAsm.Evm64.Exp.Compose.expHeadroomFinalAllRegsOwnedLeftoverFrame sp evmSp ps) := by
  delta evmExpHeadroomPublicLeftoverFrame
  rfl

theorem evmExpHeadroomPublicLeftoverFrame_pcFree
    (evmSp : Word) :
    (evmExpHeadroomPublicLeftoverFrame evmSp).pcFree := by
  intro ps h_frame
  rw [evmExpHeadroomPublicLeftoverFrame_unfold] at h_frame
  obtain ⟨sp, h_frame⟩ := h_frame
  exact EvmAsm.Evm64.Exp.Compose.expHeadroomFinalAllRegsOwnedLeftoverFrame_pcFree
    sp evmSp ps h_frame

instance pcFreeInst_evmExpHeadroomPublicLeftoverFrame
    (evmSp : Word) :
    Assertion.PCFree (evmExpHeadroomPublicLeftoverFrame evmSp) :=
  ⟨evmExpHeadroomPublicLeftoverFrame_pcFree evmSp⟩

@[irreducible]
def evmExpHeadroomVisibleResultStackPost
    (evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion :=
  (((.x12 ↦ᵣ (evmSp + 32)) **
    evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
    evmExpHeadroomPublicLeftoverFrame evmSp)

theorem evmExpHeadroomVisibleResultStackPost_unfold
    (evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    evmExpHeadroomVisibleResultStackPost evmSp baseWord exponentWord rest =
      ((((.x12 ↦ᵣ (evmSp + 32)) **
        evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
        evmExpHeadroomPublicLeftoverFrame evmSp)) := by
  delta evmExpHeadroomVisibleResultStackPost
  rfl

theorem evmExpHeadroomVisibleResultStackPost_pcFree
    (evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    (evmExpHeadroomVisibleResultStackPost evmSp baseWord exponentWord rest).pcFree := by
  rw [evmExpHeadroomVisibleResultStackPost_unfold]
  pcFree

instance pcFreeInst_evmExpHeadroomVisibleResultStackPost
    (evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree (evmExpHeadroomVisibleResultStackPost evmSp baseWord exponentWord rest) :=
  ⟨evmExpHeadroomVisibleResultStackPost_pcFree evmSp baseWord exponentWord rest⟩

@[irreducible]
def evmExpHeadroomRunStackPost
    (evmSp : Word)
    (out : ExpStackExecutionBridge.ExpStackResult) : Assertion :=
  (((.x12 ↦ᵣ (evmSp + 32)) **
    evmStackIs (evmSp + 32) (out.effects.stackWords ++ out.stack)) **
    evmExpHeadroomPublicLeftoverFrame evmSp)

theorem evmExpHeadroomRunStackPost_unfold
    (evmSp : Word)
    (out : ExpStackExecutionBridge.ExpStackResult) :
    evmExpHeadroomRunStackPost evmSp out =
      ((((.x12 ↦ᵣ (evmSp + 32)) **
        evmStackIs (evmSp + 32) (out.effects.stackWords ++ out.stack)) **
        evmExpHeadroomPublicLeftoverFrame evmSp)) := by
  delta evmExpHeadroomRunStackPost
  rfl

theorem evmExpHeadroomRunStackPost_pcFree
    (evmSp : Word)
    (out : ExpStackExecutionBridge.ExpStackResult) :
    (evmExpHeadroomRunStackPost evmSp out).pcFree := by
  rw [evmExpHeadroomRunStackPost_unfold]
  pcFree

instance pcFreeInst_evmExpHeadroomRunStackPost
    (evmSp : Word)
    (out : ExpStackExecutionBridge.ExpStackResult) :
    Assertion.PCFree (evmExpHeadroomRunStackPost evmSp out) :=
  ⟨evmExpHeadroomRunStackPost_pcFree evmSp out⟩

theorem evmExpHeadroomVisibleResultStackPost_eq_runStackPost
    (evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (out : ExpStackExecutionBridge.ExpStackResult)
    (h_run : ExpStackExecutionBridge.runExpStack?
        { stack := baseWord :: exponentWord :: rest } = some out) :
    evmExpHeadroomVisibleResultStackPost evmSp baseWord exponentWord rest =
      evmExpHeadroomRunStackPost evmSp out := by
  rw [ExpStackExecutionBridge.runExpStack?_semantic_cons] at h_run
  injection h_run with h_out
  subst h_out
  rw [evmExpHeadroomVisibleResultStackPost_unfold,
    evmExpHeadroomRunStackPost_unfold]
  rfl

theorem evmExpHeadroomRunStackPost_of_visibleResultStackPost
    {evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {out : ExpStackExecutionBridge.ExpStackResult} {ps : EvmAsm.Rv64.PartialState}
    (h_run : ExpStackExecutionBridge.runExpStack?
        { stack := baseWord :: exponentWord :: rest } = some out)
    (h_post : evmExpHeadroomVisibleResultStackPost evmSp baseWord exponentWord rest ps) :
    evmExpHeadroomRunStackPost evmSp out ps := by
  rw [← evmExpHeadroomVisibleResultStackPost_eq_runStackPost
    evmSp baseWord exponentWord rest out h_run]
  exact h_post

theorem evmExpHeadroomVisibleResultStackPost_to_runStackPost_self
    {evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : EvmAsm.Rv64.PartialState}
    (h_post : evmExpHeadroomVisibleResultStackPost evmSp baseWord exponentWord rest ps) :
    evmExpHeadroomRunStackPost evmSp
        { effects :=
            { stackWords := [EvmWord.exp baseWord exponentWord]
              dynamicGas := ExpArgs.expDynamicCostFromArgs
                (ExpArgs.expArgs baseWord exponentWord)
              totalGas := ExpArgs.expTotalGasFromArgs
                (ExpArgs.expArgs baseWord exponentWord) }
          stack := rest } ps := by
  exact evmExpHeadroomRunStackPost_of_visibleResultStackPost
    (ExpStackExecutionBridge.runExpStack?_semantic_cons baseWord exponentWord rest) h_post

theorem evmExpHeadroomPublicStackPost_to_visibleResultStackPost
    {evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : EvmAsm.Rv64.PartialState}
    (h : evmExpHeadroomPublicStackPost evmSp baseWord exponentWord rest ps) :
    evmExpHeadroomVisibleResultStackPost evmSp baseWord exponentWord rest ps := by
  rw [evmExpHeadroomPublicStackPost_unfold] at h
  obtain ⟨sp, h_post⟩ := h
  rw [EvmAsm.Evm64.Exp.Compose.expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost_unfold] at h_post
  rw [evmExpHeadroomVisibleResultStackPost_unfold, evmExpHeadroomPublicLeftoverFrame_unfold]
  exact EvmAsm.Rv64.sepConj_mono (fun _ h_stack => h_stack)
    (fun _ h_frame => ⟨sp, h_frame⟩) _ h_post

/-- Headroom full-loop EXP surface with the final live EVM stack rooted at the
    final stack pointer `evmSp + 32`, and the scratch result folded as
    `evmWordIs sp result`. The consumed base cell and headroom/leftover frame
    remain explicit pending the public wrapper cleanup. -/
theorem evm_exp_headroom_clean_live_stack_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
       ((evmSp + signExtend12 ((-128) : BitVec 12)) ↦ₘ h0) **
       ((evmSp + signExtend12 ((-120) : BitVec 12)) ↦ₘ h1) **
       ((evmSp + signExtend12 ((-112) : BitVec 12)) ↦ₘ h2) **
       ((evmSp + signExtend12 ((-104) : BitVec 12)) ↦ₘ h3) **
       ((evmSp + signExtend12 ((-96) : BitVec 12)) ↦ₘ h4) **
       ((evmSp + signExtend12 ((-88) : BitVec 12)) ↦ₘ h5) **
       ((evmSp + signExtend12 ((-80) : BitVec 12)) ↦ₘ h6) **
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ h7) **
       (.x18 ↦ᵣ v18) ** (.x1 ↦ᵣ vOld) **
       regOwn .x10 ** regOwn .x7 ** regOwn .x11 **
       evmWordIs (evmSp + signExtend12 ((-64) : BitVec 12)) dWord **
       evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) eWord **
       evmStackIs evmSp (baseWord :: exponentWord :: rest)))
      (EvmAsm.Evm64.Exp.Compose.expHeadroomFinalCleanLiveStackPost
        sp evmSp baseWord exponentWord rest) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp =>
      EvmAsm.Evm64.Exp.Compose.expHeadroomFinalCleanVisiblePost_to_cleanLiveStackPost hp)
    (evm_exp_headroom_clean_visible_stack_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base
      baseWord exponentWord dWord eWord rest lookahead vOld v18 hbase)

/-- Named-pre/named-post surface for the current headroom EXP full-loop
    theorem. The post exposes the final live stack at `evmSp + 32`; the
    consumed-base cell and headroom/leftover frame remain explicit. -/
theorem evm_exp_headroom_named_live_stack_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (evmExpHeadroomPre sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
        h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld baseWord exponentWord dWord eWord rest)
      (EvmAsm.Evm64.Exp.Compose.expHeadroomFinalCleanLiveStackPost
        sp evmSp baseWord exponentWord rest) := by
  rw [evmExpHeadroomPre_unfold]
  exact evm_exp_headroom_clean_live_stack_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
    h0 h1 h2 h3 h4 h5 h6 h7 base
    baseWord exponentWord dWord eWord rest lookahead vOld v18 hbase

/-- Named-pre EXP headroom theorem with the consumed base word weakened to
    ownership. This is closer to the public binary-op stack post: the live stack
    starts at `evmSp + 32`, and the old top word is merely owned below it. -/
theorem evm_exp_headroom_owned_base_live_stack_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (evmExpHeadroomPre sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
        h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld baseWord exponentWord dWord eWord rest)
      (EvmAsm.Evm64.Exp.Compose.expHeadroomFinalCleanOwnedBaseLiveStackPost
        sp evmSp baseWord exponentWord rest) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp =>
      EvmAsm.Evm64.Exp.Compose.expHeadroomFinalCleanLiveStackPost_to_ownedBasePost hp)
    (evm_exp_headroom_named_live_stack_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base
      baseWord exponentWord dWord eWord rest lookahead vOld v18 hbase)

/-- Named-pre EXP headroom theorem with the final live stack split from the
    remaining owned-base/scratch frame. This isolates the caller-visible stack
    transition at `evmSp + 32` while preserving all resources owned by the
    verified headroom loop. -/
theorem evm_exp_headroom_framed_live_stack_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (evmExpHeadroomPre sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
        h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld baseWord exponentWord dWord eWord rest)
      (EvmAsm.Evm64.Exp.Compose.expHeadroomFinalFramedLiveStackPost
        sp evmSp baseWord exponentWord rest) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp =>
      EvmAsm.Evm64.Exp.Compose.expHeadroomFinalCleanOwnedBaseLiveStackPost_to_framedLiveStackPost hp)
    (evm_exp_headroom_owned_base_live_stack_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base
      baseWord exponentWord dWord eWord rest lookahead vOld v18 hbase)

/-- Named-pre EXP headroom theorem with both consumed stack cells outside the
    final live stack weakened to ownership. The final live EVM stack remains
    isolated at `evmSp + 32`; the local RISC-V scratch result at `sp` is no
    longer value-constrained. -/
theorem evm_exp_headroom_owned_scratch_live_stack_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (evmExpHeadroomPre sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
        h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld baseWord exponentWord dWord eWord rest)
      (EvmAsm.Evm64.Exp.Compose.expHeadroomFinalOwnedScratchLiveStackPost
        sp evmSp baseWord exponentWord rest) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp =>
      EvmAsm.Evm64.Exp.Compose.expHeadroomFinalFramedLiveStackPost_to_ownedScratchLiveStackPost hp)
    (evm_exp_headroom_framed_live_stack_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base
      baseWord exponentWord dWord eWord rest lookahead vOld v18 hbase)

/-- Named-pre EXP headroom theorem with the visible final live stack isolated and
    every leftover headroom stack cell weakened to ownership. This keeps only
    the caller-visible result value constrained while preserving all resources
    returned by the verified headroom loop. -/
theorem evm_exp_headroom_owned_leftover_live_stack_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (evmExpHeadroomPre sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
        h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld baseWord exponentWord dWord eWord rest)
      (EvmAsm.Evm64.Exp.Compose.expHeadroomFinalOwnedLeftoverLiveStackPost
        sp evmSp baseWord exponentWord rest) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp =>
      EvmAsm.Evm64.Exp.Compose.expHeadroomFinalOwnedScratchLiveStackPost_to_ownedLeftoverLiveStackPost hp)
    (evm_exp_headroom_owned_scratch_live_stack_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base
      baseWord exponentWord dWord eWord rest lookahead vOld v18 hbase)

/-- Named-pre EXP headroom theorem with the loop counter register weakened to
    ownership in the leftover frame. The final live stack remains isolated at
    `evmSp + 32`, and the leftover headroom stack cells are owned abstractly. -/
theorem evm_exp_headroom_counter_owned_leftover_live_stack_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (evmExpHeadroomPre sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
        h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld baseWord exponentWord dWord eWord rest)
      (EvmAsm.Evm64.Exp.Compose.expHeadroomFinalCounterOwnedLeftoverLiveStackPost
        sp evmSp baseWord exponentWord rest) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp =>
      EvmAsm.Evm64.Exp.Compose.expHeadroomFinalOwnedLeftoverLiveStackPost_to_counterOwnedLeftoverLiveStackPost hp)
    (evm_exp_headroom_owned_leftover_live_stack_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base
      baseWord exponentWord dWord eWord rest lookahead vOld v18 hbase)

/-- Named-pre EXP headroom theorem with both leftover scratch registers currently
    exposed by the post (`x9` and `x5`) weakened to ownership. The final live
    stack remains isolated at `evmSp + 32`. -/
theorem evm_exp_headroom_scratch_regs_owned_leftover_live_stack_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (evmExpHeadroomPre sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
        h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld baseWord exponentWord dWord eWord rest)
      (EvmAsm.Evm64.Exp.Compose.expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost
        sp evmSp baseWord exponentWord rest) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp =>
      EvmAsm.Evm64.Exp.Compose.expHeadroomFinalCounterOwnedLeftoverLiveStackPost_to_scratchRegsOwnedLeftoverLiveStackPost hp)
    (evm_exp_headroom_counter_owned_leftover_live_stack_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base
      baseWord exponentWord dWord eWord rest lookahead vOld v18 hbase)


/-- Named-pre EXP headroom theorem with the leftover frame-pointer register
    weakened to ownership. The final live stack remains isolated at
    `evmSp + 32`. -/
theorem evm_exp_headroom_frame_regs_owned_leftover_live_stack_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (evmExpHeadroomPre sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
        h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld baseWord exponentWord dWord eWord rest)
      (EvmAsm.Evm64.Exp.Compose.expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost
        sp evmSp baseWord exponentWord rest) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp =>
      EvmAsm.Evm64.Exp.Compose.expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost_to_frameRegsOwnedLeftoverLiveStackPost hp)
    (evm_exp_headroom_scratch_regs_owned_leftover_live_stack_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base
      baseWord exponentWord dWord eWord rest lookahead vOld v18 hbase)

/-- Named-pre EXP headroom theorem with every leftover frame register in the
    current post weakened to ownership. The final live stack remains isolated at
    `evmSp + 32`. -/
theorem evm_exp_headroom_all_regs_owned_leftover_live_stack_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (evmExpHeadroomPre sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
        h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld baseWord exponentWord dWord eWord rest)
      (EvmAsm.Evm64.Exp.Compose.expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost
        sp evmSp baseWord exponentWord rest) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp =>
      EvmAsm.Evm64.Exp.Compose.expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost_to_allRegsOwnedLeftoverLiveStackPost hp)
    (evm_exp_headroom_frame_regs_owned_leftover_live_stack_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 base
      baseWord exponentWord dWord eWord rest lookahead vOld v18 hbase)

/-- EXP headroom theorem with old register/scratch values hidden behind an
    existential precondition. The visible precondition keeps only the scratch
    base pointer, EVM stack pointer, two operands, and stack tail explicit. -/
theorem evm_exp_headroom_existential_pre_all_regs_owned_leftover_live_stack_spec_within
    (sp evmSp base : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (evmExpHeadroomExistentialPre sp evmSp baseWord exponentWord rest)
      (EvmAsm.Evm64.Exp.Compose.expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost
        sp evmSp baseWord exponentWord rest) := by
  rw [evmExpHeadroomExistentialPre_unfold]
  refine EvmAsm.Evm64.Exp.Compose.cpsTripleWithin_exists_pre ?_
  intro w
  exact evm_exp_headroom_all_regs_owned_leftover_live_stack_spec_within
    sp evmSp w.cOld w.tOld w.c6Old w.c16Old w.c19Old w.m0 w.m1 w.m2 w.m3 w.v6
    w.h0 w.h1 w.h2 w.h3 w.h4 w.h5 w.h6 w.h7 base
    baseWord exponentWord w.dWord w.eWord rest (0 : Word) w.vOld w.v18 hbase

/-- EXP headroom theorem with public-shaped stack pre/post assertions: the
    visible arguments are the EVM stack pointer, two operands, and stack tail;
    the internal scratch base and old register/scratch values are existentially
    packaged. This still targets the verified headroom code surface rather than
    the final `evm_exp` opcode wrapper. -/
theorem evm_exp_headroom_public_stack_shape_spec_within
    (evmSp base : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (evmExpHeadroomPublicStackPre evmSp baseWord exponentWord rest)
      (evmExpHeadroomPublicStackPost evmSp baseWord exponentWord rest) := by
  rw [evmExpHeadroomPublicStackPre_unfold]
  refine EvmAsm.Evm64.Exp.Compose.cpsTripleWithin_exists_pre ?_
  intro sp
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      rw [evmExpHeadroomPublicStackPost_unfold]
      exact ⟨sp, hp⟩)
    (evm_exp_headroom_existential_pre_all_regs_owned_leftover_live_stack_spec_within
      sp evmSp base baseWord exponentWord rest hbase)

/-- EXP headroom public-shaped theorem with the ordinary entry-base alignment
    hypothesis. The internal proof still needs the loop-entry alignment fact at
    `base + 116`, derived here from the even entry address. -/
theorem evm_exp_headroom_public_stack_shape_base_aligned_spec_within
    (evmSp base : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (hbase : base &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (evmExpHeadroomPublicStackPre evmSp baseWord exponentWord rest)
      (evmExpHeadroomPublicStackPost evmSp baseWord exponentWord rest) := by
  have hbaseLoop : (base + 72 + 44 : Word) &&& 1 = 0 := by
    rw [show (base + 72 + 44 : Word) = base + (116 : Word) from by bv_omega]
    exact EvmAsm.Rv64.BitAux.word_add_even_and_one hbase (by decide)
  exact evm_exp_headroom_public_stack_shape_spec_within
    evmSp base baseWord exponentWord rest hbaseLoop

/-- Canonical partial EXP stack specification for the verified headroom code.
    This gives the current public-shaped stack pre/post surface a stable short
    name while the final `evm_exp` opcode wrapper remains pending. -/
theorem evm_exp_headroom_stack_spec_within
    (evmSp base : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (hbase : base &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (evmExpHeadroomPublicStackPre evmSp baseWord exponentWord rest)
      (evmExpHeadroomPublicStackPost evmSp baseWord exponentWord rest) := by
  exact evm_exp_headroom_public_stack_shape_base_aligned_spec_within
    evmSp base baseWord exponentWord rest hbase

-- The public `evm_exp_stack_spec_within` lives in `Exp/HeadroomProgramSpec.lean`
-- (it must sit beside the concrete appended-program abbrev it targets).

/-- Canonical partial EXP headroom specification with the semantic result stack
    exposed directly and only the leftover implementation frame hidden. This
    still targets the verified headroom code surface, not the final opcode
    wrapper. -/
theorem evm_exp_headroom_visible_result_stack_spec_within
    (evmSp base : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (hbase : base &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (EvmAsm.Evm64.Exp.Compose.evm_exp_headroom_canonical_appended_mul_code base)
      (evmExpHeadroomPublicStackPre evmSp baseWord exponentWord rest)
      (evmExpHeadroomVisibleResultStackPost evmSp baseWord exponentWord rest) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => evmExpHeadroomPublicStackPost_to_visibleResultStackPost hp)
    (evm_exp_headroom_stack_spec_within evmSp base baseWord exponentWord rest hbase)


end EvmAsm.Evm64
