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

-- Placeholder: `evm_exp_stack_spec_within` lands in slice 6 (evm-asm-6snn).

end EvmAsm.Evm64
