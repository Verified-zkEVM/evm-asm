/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryPrologueFixed

  Boundary-block prologue and pointer-advance helpers for the FIXED
  two-MUL saved-bit EXP code bundle (`evm_exp_msb_saved_bit_two_mul_fixed`).

  The fixed algorithm uses x19 as the callee-saved exponent cursor
  (initialized to `exponentWord.getLimbN 3`), x16 as the limb pointer,
  and x6 as the per-limb countdown counter, rather than leaving x5 = 1
  and ignoring the exponent entirely.

  GH #92, bead evm-asm-w5mk.
-/

import EvmAsm.Evm64.Exp.LimbSpec
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryPrologue

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

-- ============================================================================
-- Fixed loop entry state definition
-- ============================================================================

/-- The correct loop entry state for the fixed EXP algorithm, after
    `exp_prologue_fixed ;; exp_loop_pointer_advance` executes.

    Differences from `expTwoMulLoopEntryPost`:
    - x6 = 64 (per-limb counter, counting down from 64 bits per limb)
    - x16 = evmSp + 48 (limb pointer pre-advanced to second limb)
    - x19 = exponentWord.getLimbN 3 (exponent cursor, MSB limb loaded)
-/
@[irreducible]
def expTwoMulLoopEntryPostFixed
    (sp evmSp vOld v18 : Word) (baseWord exponentWord : EvmWord)
    (rest : List EvmWord) : Assertion :=
  (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x16 ↦ᵣ (evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))) **
      (.x19 ↦ᵣ exponentWord.getLimbN 3) **
      evmWordIs sp (1 : EvmWord)) **
     (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12)))) **
   evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
   expTwoMulScratchFrame vOld v18)

theorem expTwoMulLoopEntryPostFixed_unfold
    {sp evmSp vOld v18 : Word} {baseWord exponentWord : EvmWord}
    {rest : List EvmWord} :
    expTwoMulLoopEntryPostFixed sp evmSp vOld v18 baseWord exponentWord rest =
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
          (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
          (.x16 ↦ᵣ (evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))) **
          (.x19 ↦ᵣ exponentWord.getLimbN 3) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12)))) **
        evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       expTwoMulScratchFrame vOld v18) := by
  delta expTwoMulLoopEntryPostFixed; rfl

theorem expTwoMulLoopEntryPostFixed_unfold_scratch
    {sp evmSp vOld v18 : Word} {baseWord exponentWord : EvmWord}
    {rest : List EvmWord} :
    expTwoMulLoopEntryPostFixed sp evmSp vOld v18 baseWord exponentWord rest =
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
          (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
          (.x16 ↦ᵣ (evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))) **
          (.x19 ↦ᵣ exponentWord.getLimbN 3) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12)))) **
        evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       (regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18))) := by
  rw [expTwoMulLoopEntryPostFixed_unfold, expTwoMulScratchFrame_unfold]

/-- Fixed entry-post unfold that exposes the first two words below the EXP
    operands. This is the stack shape needed by the fixed iteration precondition
    after the prologue advances `x12` to `evmSp + 64`. -/
theorem expTwoMulLoopEntryPostFixed_unfold_rest2
    {sp evmSp vOld v18 : Word} {baseWord exponentWord dWord eWord : EvmWord}
    {rest : List EvmWord} :
    expTwoMulLoopEntryPostFixed sp evmSp vOld v18
        baseWord exponentWord (dWord :: eWord :: rest) =
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
          (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
          (.x16 ↦ᵣ (evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))) **
          (.x19 ↦ᵣ exponentWord.getLimbN 3) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12)))) **
        (evmWordIs evmSp baseWord **
         evmWordIs (evmSp + 32) exponentWord **
         evmWordIs (evmSp + 32 + 32) dWord **
         evmWordIs (evmSp + 32 + 32 + 32) eWord **
         evmStackIs (evmSp + 32 + 32 + 32 + 32) rest)) **
       (regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18))) := by
  rw [expTwoMulLoopEntryPostFixed_unfold_scratch]
  rfl

/-- Normalized-offset variant of `expTwoMulLoopEntryPostFixed_unfold_rest2`.
    The first rest word starts exactly at the advanced iteration stack pointer
    `evmSp + 64`. -/
theorem expTwoMulLoopEntryPostFixed_unfold_rest2_offsets
    {sp evmSp vOld v18 : Word} {baseWord exponentWord dWord eWord : EvmWord}
    {rest : List EvmWord} :
    expTwoMulLoopEntryPostFixed sp evmSp vOld v18
        baseWord exponentWord (dWord :: eWord :: rest) =
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
          (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
          (.x16 ↦ᵣ (evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))) **
          (.x19 ↦ᵣ exponentWord.getLimbN 3) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12)))) **
        (evmWordIs evmSp baseWord **
         evmWordIs (evmSp + 32) exponentWord **
         evmWordIs (evmSp + 64) dWord **
         evmWordIs (evmSp + 96) eWord **
         evmStackIs (evmSp + 128) rest)) **
       (regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18))) := by
  rw [expTwoMulLoopEntryPostFixed_unfold_rest2]
  simp only [BitVec.add_assoc,
    show (32 : Word) + 32 = 64 from by decide,
    show (64 : Word) + 32 = 96 from by decide,
    show (96 : Word) + 32 = 128 from by decide]

theorem expTwoMulLoopEntryPostFixed_pcFree
    {sp evmSp vOld v18 : Word} {baseWord exponentWord : EvmWord}
    {rest : List EvmWord} :
    (expTwoMulLoopEntryPostFixed sp evmSp vOld v18 baseWord exponentWord rest).pcFree := by
  rw [expTwoMulLoopEntryPostFixed_unfold]
  pcFree

instance pcFreeInst_expTwoMulLoopEntryPostFixed
    (sp evmSp vOld v18 : Word) (baseWord exponentWord : EvmWord)
    (rest : List EvmWord) :
    Assertion.PCFree (expTwoMulLoopEntryPostFixed sp evmSp vOld v18 baseWord exponentWord rest) :=
  ⟨expTwoMulLoopEntryPostFixed_pcFree⟩

-- ============================================================================
-- Code abbreviation for the fixed EXP program
-- ============================================================================

abbrev expMsbSavedBitTwoMulFixedCode (base : Word)
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : CodeReq :=
  CodeReq.ofProg base (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed
    squaringMulOff condMulOff skipOff backOff)

theorem expMsbSavedBitTwoMulFixedCode_prologue_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue_fixed) a = some i →
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  exact CodeReq.ofProg_mono_sub base base
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_prologue_fixed 0
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed EvmAsm.Rv64.seq
      unfold Program
      rfl)
    (by
      simp [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length,
        EvmAsm.Evm64.exp_prologue_fixed_length])
    (by simp [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length])

theorem expMsbSavedBitTwoMulFixedCode_pointer_advance_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 40) EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  exact CodeReq.ofProg_mono_sub base (base + 40)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_loop_pointer_advance 10
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed EvmAsm.Rv64.seq
      unfold Program
      rfl)
    (by
      simp [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length,
        EvmAsm.Evm64.exp_loop_pointer_advance_length])
    (by simp [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length])

theorem expMsbSavedBitTwoMulFixedCode_iter_body_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 44)
      (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
        squaringMulOff condMulOff skipOff backOff)) a = some i →
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  exact CodeReq.ofProg_mono_sub base (base + 44)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff) 11
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed EvmAsm.Rv64.seq
      unfold Program
      rfl)
    (by
      simp [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length,
        EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length])
    (by simp [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length])

theorem expMsbSavedBitTwoMulFixedCode_pointer_restore_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 296)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  exact CodeReq.ofProg_mono_sub base (base + 296)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_loop_pointer_restore 74
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed EvmAsm.Rv64.seq
      unfold Program
      rfl)
    (by
      simp [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length,
        EvmAsm.Evm64.exp_loop_pointer_restore_length])
    (by simp [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length])

theorem expMsbSavedBitTwoMulFixedCode_epilogue_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 300) EvmAsm.Evm64.exp_epilogue) a = some i →
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  exact CodeReq.ofProg_mono_sub base (base + 300)
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_epilogue 75
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed EvmAsm.Rv64.seq
      unfold Program
      rfl)
    (by
      simp [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length,
        EvmAsm.Evm64.exp_epilogue_length])
    (by simp [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length])

theorem expMsbSavedBitTwoMulFixedCode_block_subs {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue_fixed) a = some i →
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 40)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 44)
      (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
        squaringMulOff condMulOff skipOff backOff)) a = some i →
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 296)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 300) EvmAsm.Evm64.exp_epilogue)
      a = some i →
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) := by
  exact ⟨expMsbSavedBitTwoMulFixedCode_prologue_sub,
    expMsbSavedBitTwoMulFixedCode_pointer_advance_sub,
    expMsbSavedBitTwoMulFixedCode_iter_body_sub,
    expMsbSavedBitTwoMulFixedCode_pointer_restore_sub,
    expMsbSavedBitTwoMulFixedCode_epilogue_sub⟩

-- ============================================================================
-- Prologue + pointer-advance spec for the fixed code
-- ============================================================================

/-- The fixed prologue (10 instructions) lifted to the full fixed code,
    against a PRE that includes the exponent's MSB limb at evmSp+56. -/
private theorem exp_prologue_fixed_in_fixed_code_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 expLimb3 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 10 base (base + 40)
      (expMsbSavedBitTwoMulFixedCode base squaringMulOff condMulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ expLimb3))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       (.x12 ↦ᵣ evmSp) **
       (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
       (.x16 ↦ᵣ evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12)) **
       (.x19 ↦ᵣ expLimb3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ expLimb3)) :=
  cpsTripleWithin_extend_code
    (h := EvmAsm.Evm64.exp_prologue_fixed_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 expLimb3 base)
    (hmono := CodeReq.ofProg_mono_sub base base
      (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed
        squaringMulOff condMulOff skipOff backOff)
      EvmAsm.Evm64.exp_prologue_fixed 0
      (by bv_omega)
      (by unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed EvmAsm.Rv64.seq
              EvmAsm.Evm64.exp_prologue_fixed EvmAsm.Rv64.ADDI
              EvmAsm.Rv64.SD EvmAsm.Rv64.LD
              EvmAsm.Rv64.single
          rfl)
      (by simp [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length,
                EvmAsm.Evm64.exp_prologue_fixed_length])
      (by simp [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length]))

/-- The pointer-advance instruction lifted to the full fixed code. -/
private theorem exp_pointer_advance_fixed_in_fixed_code_spec_within
    (evmSp : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 1 (base + 40) (base + 44)
      (expMsbSavedBitTwoMulFixedCode base squaringMulOff condMulOff skipOff backOff)
      (.x12 ↦ᵣ evmSp)
      (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) := by
  have h := EvmAsm.Evm64.exp_loop_pointer_advance_spec_within evmSp (base + 40)
  have haddr : (base + 40 : Word) + 4 = base + 44 := by bv_addr
  rw [haddr] at h
  exact cpsTripleWithin_extend_code (h := h)
    (hmono := CodeReq.ofProg_mono_sub base (base + 40)
      (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed
        squaringMulOff condMulOff skipOff backOff)
      EvmAsm.Evm64.exp_loop_pointer_advance 10
      (by bv_omega)
      (by unfold EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed EvmAsm.Rv64.seq
              EvmAsm.Evm64.exp_prologue_fixed EvmAsm.Evm64.exp_loop_pointer_advance
              EvmAsm.Rv64.ADDI
              EvmAsm.Rv64.SD EvmAsm.Rv64.LD
              EvmAsm.Rv64.single
          rfl)
      (by simp [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length,
                EvmAsm.Evm64.exp_loop_pointer_advance_length])
      (by simp [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length]))

/-- The fixed EXP prologue followed by the pointer advance:
    proves that 11 instructions correctly initialize x19, x6, x16 for the
    fixed MSB-first exponent cursor from a raw precondition.

    The PRE includes the exponent's MSB limb explicitly at evmSp+56;
    the POST is the raw (pre-folded) accumulation from the specs.
    Callers wrap this in a further weaken to fold into `expTwoMulLoopEntryPostFixed`. -/
theorem exp_prologue_fixed_then_pointer_advance_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base expLimb3 : Word) :
    cpsTripleWithin (10 + 1) base (base + 44)
      (expMsbSavedBitTwoMulFixedCode base squaringMulOff condMulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ expLimb3) **
       expTwoMulScratchFrame vOld v18)
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
        (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
        (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
        (.x16 ↦ᵣ evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12)) **
        (.x19 ↦ᵣ expLimb3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ expLimb3)) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
       expTwoMulScratchFrame vOld v18) := by
  have hPrologue := exp_prologue_fixed_in_fixed_code_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 expLimb3
    squaringMulOff condMulOff skipOff backOff base
  have hPrologueF := cpsTripleWithin_frameR
    (expTwoMulScratchFrame vOld v18)
    (by pcFree) hPrologue
  have hAdvance := exp_pointer_advance_fixed_in_fixed_code_spec_within
    evmSp squaringMulOff condMulOff skipOff backOff base
  have hAdvanceF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
     (.x9 ↦ᵣ 0 + signExtend12 256) ** (.x5 ↦ᵣ 0 + signExtend12 1) **
     (.x20 ↦ᵣ 0 + signExtend12 64) **
     (.x16 ↦ᵣ evmSp + signExtend12 56 + signExtend12 (-8:BitVec 12)) **
     (.x19 ↦ᵣ expLimb3) **
     ((sp + signExtend12 0) ↦ₘ 0 + signExtend12 1) **
     ((sp + signExtend12 8) ↦ₘ 0) ** ((sp + signExtend12 16) ↦ₘ 0) **
     ((sp + signExtend12 24) ↦ₘ 0) **
     ((evmSp + signExtend12 56) ↦ₘ expLimb3) **
     expTwoMulScratchFrame vOld v18)
    (by pcFree) hAdvance
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hPrologueF hAdvanceF)

-- ============================================================================
-- Full-stack boundary prologue spec (with evmStackIs and expTwoMulLoopEntryPostFixed)
-- ============================================================================

/-- Full-stack combined prologue + pointer-advance spec for the fixed EXP algorithm.
    The PRE includes `evmStackIs evmSp (baseWord :: exponentWord :: rest)` and the
    POST is `expTwoMulLoopEntryPostFixed`, establishing the correct loop entry state
    with x19 = exponentWord.getLimbN 3, x6 = 64, x16 = evmSp+48.

    Proof: frame `exp_prologue_fixed_then_pointer_advance_spec_within` with all
    evmStackIs atoms except the MSB exponent limb (evmSp+56), then fold. -/
theorem exp_prologue_fixed_then_pointer_advance_full_stack_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin (10 + 1) base (base + 44)
      (expMsbSavedBitTwoMulFixedCode base squaringMulOff condMulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       expTwoMulScratchFrame vOld v18 **
       evmStackIs evmSp (baseWord :: exponentWord :: rest))
      (expTwoMulLoopEntryPostFixed sp evmSp vOld v18 baseWord exponentWord rest) := by
  -- Address identity: evmSp + signExtend12 56 = (evmSp+32) + 24
  have h56 : (evmSp + signExtend12 (56 : BitVec 12) : Word) =
             (evmSp + 32) + 24 := by rw [EvmAsm.Rv64.signExtend12_56]; bv_omega
  -- Frame the raw spec with remaining stack atoms (base word, exp limbs 0-2, rest)
  let expLimb3 := exponentWord.getLimbN 3
  have hRaw_framed := cpsTripleWithin_frameR
    ((evmSp ↦ₘ baseWord.getLimbN 0) **
     ((evmSp + 8) ↦ₘ baseWord.getLimbN 1) **
     ((evmSp + 16) ↦ₘ baseWord.getLimbN 2) **
     ((evmSp + 24) ↦ₘ baseWord.getLimbN 3) **
     (((evmSp + 32) + 0) ↦ₘ exponentWord.getLimbN 0) **
     (((evmSp + 32) + 8) ↦ₘ exponentWord.getLimbN 1) **
     (((evmSp + 32) + 16) ↦ₘ exponentWord.getLimbN 2) **
     evmStackIs (evmSp + 64) rest)
    (by pcFree)
    (exp_prologue_fixed_then_pointer_advance_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
      squaringMulOff condMulOff skipOff backOff base expLimb3)
  -- Key address identities
  have h64 : (evmSp + 32 + 32 : Word) = evmSp + 64 := by bv_addr
  have h32_0 : ((evmSp + 32) + 0 : Word) = evmSp + 32 := by bv_addr
  -- Register value normalizations needed for POST-weaken
  have hx9 : (0:Word) + signExtend12 (256:BitVec 12) = (256:Word) := by
    rw [EvmAsm.Evm64.Exp.AddrNorm.exp_se12_256]; bv_omega
  have hx5 : (0:Word) + signExtend12 (1:BitVec 12) = (1:Word) := by
    rw [EvmAsm.Rv64.signExtend12_1]; bv_omega
  -- Weaken: PRE uses evmStackIs, POST uses expTwoMulLoopEntryPostFixed
  exact cpsTripleWithin_weaken
    -- PRE-weaken: expand evmStackIs/evmWordIs → match hRaw_framed.PRE atoms
    (fun _ hp => by
      simp only [evmStackIs_cons, evmWordIs] at hp
      rw [h64] at hp  -- normalize hp: evmSp+32+32 → evmSp+64
      rw [h56, h32_0]  -- goal: evmSp+se56→evmSp+32+24; evmSp+32+0→evmSp+32
      -- inline expLimb3 let-binding for xperm matching
      simp only [show expLimb3 = exponentWord.getLimbN 3 from rfl]
      xperm_hyp hp)
    -- POST-weaken: fold atoms back into expTwoMulLoopEntryPostFixed
    (fun _ hp => by
      rw [expTwoMulLoopEntryPostFixed_unfold]
      -- Inline expLimb3 let-binding in hp and normalize exp.l0 address
      simp only [show expLimb3 = exponentWord.getLimbN 3 from rfl] at hp
      rw [h32_0] at hp
      -- Normalize goal: x9=256→0+se256, x5=1→0+se1 to match raw-spec hp forms
      rw [← hx9, ← hx5]
      -- Unfold evmWordIs sp 1 in goal BEFORE simp (must be before simp expands it wrong)
      rw [← exp_prologue_result_word_one sp]
      -- Expand evmStackIs/evmWordIs in goal (accumulator atoms already expanded)
      simp only [evmStackIs_cons, evmWordIs]
      -- Normalize goal addresses: evmSp+32+32→evmSp+64, evmSp+32+24→evmSp+se56
      rw [h64, ← h56]
      xperm_hyp hp)
    hRaw_framed

end EvmAsm.Evm64.Exp.Compose
