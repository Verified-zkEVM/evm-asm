import EvmAsm.Evm64.Exp.Compose.SavedBitFixedHeadroomCompose

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Word-folded epilogue block (instr idx 93, byte +372..408) lifted onto the
    headroom program. This keeps the result stack word folded for the final
    EXP wrapper composition. -/
theorem exp_headroom_epilogue_word_lifted
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 9 (base + 372) (base + 408)
      (evm_exp_headroom_code squaringMulOff condMulOff skipOff backOff base)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)) := by
  have h := exp_epilogue_word_spec_within sp evmSp tOld r0 r1 r2 r3
    d0 d1 d2 d3 (base + 372)
  rw [show (base + 372 + 36 : Word) = base + 408 from by bv_addr] at h
  refine cpsTripleWithin_extend_code ?_ h
  intro a i ha
  exact CodeReq.ofProg_mono_sub base (base + 372)
    (evm_exp_msb_saved_bit_two_mul_fixed_headroom
      squaringMulOff condMulOff skipOff backOff)
    exp_epilogue 93
    (by bv_omega)
    (by rfl)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    a i ha

/-- Canonical appended-code variant of `exp_headroom_epilogue_word_lifted`. -/
theorem exp_headroom_epilogue_word_canonical_appended
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base : Word) :
    cpsTripleWithin 9 (base + 372) (base + 408)
      (evm_exp_headroom_canonical_appended_mul_code base)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)) := by
  have h := exp_headroom_epilogue_word_lifted sp evmSp tOld r0 r1 r2 r3
    d0 d1 d2 d3 base
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff
  refine cpsTripleWithin_extend_code ?_ h
  intro a i ha
  exact CodeReq.union_mono_left a i ha

/-- Final headroom pointer advance followed by the folded epilogue, stated over
    the canonical appended-MUL code surface. The precondition is the loop-exit
    pointer coordinate (`evmSp - 64`) plus the live stack slot that the epilogue
    overwrites at `evmSp + 32`. -/
theorem exp_headroom_final_advance_then_epilogue_word_canonical_appended
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base : Word) :
    cpsTripleWithin (1 + 9) (base + 368) (base + 408)
      (evm_exp_headroom_canonical_appended_mul_code base)
      ((.x12 ↦ᵣ (evmSp + signExtend12 ((-64) : BitVec 12))) **
       ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)) := by
  let epilogueFrame : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
    ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
    ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
    ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
    ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
    ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
    ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
    ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
    ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)
  have hPtrBase := exp_headroom_ptr_restore_lifted
    (evmSp + signExtend12 ((-64) : BitVec 12)) base
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff
  have hPtrCanon :
      cpsTripleWithin 1 (base + 368) (base + 372)
        (evm_exp_headroom_canonical_appended_mul_code base)
        (.x12 ↦ᵣ (evmSp + signExtend12 ((-64) : BitVec 12)))
        (.x12 ↦ᵣ ((evmSp + signExtend12 ((-64) : BitVec 12)) +
          signExtend12 (64 : BitVec 12))) := by
    refine cpsTripleWithin_extend_code ?_ hPtrBase
    intro a i ha
    exact CodeReq.union_mono_left a i ha
  have hPtrFramed := cpsTripleWithin_frameR epilogueFrame (by
    dsimp [epilogueFrame]
    pcFree) hPtrCanon
  have hPtrFramed' :
      cpsTripleWithin 1 (base + 368) (base + 372)
        (evm_exp_headroom_canonical_appended_mul_code base)
        ((.x12 ↦ᵣ (evmSp + signExtend12 ((-64) : BitVec 12))) ** epilogueFrame)
        ((.x12 ↦ᵣ evmSp) ** epilogueFrame) := by
    rw [show ((evmSp + signExtend12 ((-64) : BitVec 12)) +
        signExtend12 (64 : BitVec 12) : Word) = evmSp from by
      rw [EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64, signExtend12_64]
      bv_omega] at hPtrFramed
    exact hPtrFramed
  have hEpilogue := exp_headroom_epilogue_word_canonical_appended
    sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base
  have hSeq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [epilogueFrame] at hp ⊢
      xperm_hyp hp)
    hPtrFramed' hEpilogue
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [epilogueFrame] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => hp)
    hSeq

/-- Headroom final block with loop-exit control and the caller stack tail framed
    around the folded epilogue. This is the live-stack-facing form needed after
    the fixed loop has produced the final accumulator in scratch. -/
theorem exp_headroom_final_advance_then_epilogue_full_post_stack_canonical_appended
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (base : Word) :
    let exitControl : Assertion := expTwoMulLoopExitControl iterCountNew exitCond
    let stackTail : Assertion := expTwoMulLoopExitStackTailFrame evmSp baseWord rest
    cpsTripleWithin (1 + 9) (base + 368) (base + 408)
      (evm_exp_headroom_canonical_appended_mul_code base)
      ((exitControl **
        ((.x12 ↦ᵣ (evmSp + signExtend12 ((-64) : BitVec 12))) **
         ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
          ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
          ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
          ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
          ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
          ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)))) **
       stackTail)
      (exitControl **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmStackIs evmSp (baseWord :: expResultWord r0 r1 r2 r3 :: rest))) := by
  intro exitControl stackTail
  have hBase := exp_headroom_final_advance_then_epilogue_word_canonical_appended
    sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base
  have hFramed := cpsTripleWithin_frameR (exitControl ** stackTail) (by
    dsimp [exitControl, stackTail]
    pcFree) hBase
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [exitControl, stackTail] at hp ⊢
      rw [expTwoMulLoopExitStackTailFrame_unfold] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      dsimp [exitControl, stackTail] at hp ⊢
      rw [expTwoMulLoopExitStackTailFrame_unfold] at hp
      rw [evmStackIs_cons, evmStackIs_cons]
      rw [show (evmSp + 32 : Word) + 32 = evmSp + 64 from by bv_addr]
      xcancel_struct hp)
    hFramed


@[irreducible]
def expHeadroomLoopExitFullStackPreFrame
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop) : Assertion :=
  expTwoMulLoopExitControl iterCountNew exitCond **
  ((.x12 ↦ᵣ (evmSp + signExtend12 ((-64) : BitVec 12))) **
   ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
    ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
    ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
    ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
    ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3))) **
  evmStackIs evmSp (baseWord :: expResultWord d0 d1 d2 d3 :: rest)

theorem expHeadroomLoopExitFullStackPreFrame_unfold
    {sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word}
    {baseWord : EvmWord} {rest : List EvmWord} {exitCond : Prop} :
    expHeadroomLoopExitFullStackPreFrame
      sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3
      baseWord rest exitCond =
      (expTwoMulLoopExitControl iterCountNew exitCond **
       ((.x12 ↦ᵣ (evmSp + signExtend12 ((-64) : BitVec 12))) **
        ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
         ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
         ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
         ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
         ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3))) **
       evmStackIs evmSp (baseWord :: expResultWord d0 d1 d2 d3 :: rest)) := by
  delta expHeadroomLoopExitFullStackPreFrame
  rfl

theorem expHeadroomLoopExitFullStackPreFrame_pcFree
    {sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word}
    {baseWord : EvmWord} {rest : List EvmWord} {exitCond : Prop} :
    (expHeadroomLoopExitFullStackPreFrame
      sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3
      baseWord rest exitCond).pcFree := by
  rw [expHeadroomLoopExitFullStackPreFrame_unfold]
  pcFree

instance pcFreeInst_expHeadroomLoopExitFullStackPreFrame
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop) :
    Assertion.PCFree
      (expHeadroomLoopExitFullStackPreFrame
        sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3
        baseWord rest exitCond) :=
  ⟨expHeadroomLoopExitFullStackPreFrame_pcFree⟩

@[irreducible]
def expHeadroomLoopExitFullStackPostFrame
    (sp evmSp iterCountNew r0 r1 r2 r3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop) : Assertion :=
  expTwoMulLoopExitControl iterCountNew exitCond **
  ((.x2 ↦ᵣ sp) **
   (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
   (.x5 ↦ᵣ r3) **
   ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
   ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
   ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
   ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
   evmStackIs evmSp (baseWord :: expResultWord r0 r1 r2 r3 :: rest))

theorem expHeadroomLoopExitFullStackPostFrame_unfold
    {sp evmSp iterCountNew r0 r1 r2 r3 : Word}
    {baseWord : EvmWord} {rest : List EvmWord} {exitCond : Prop} :
    expHeadroomLoopExitFullStackPostFrame
      sp evmSp iterCountNew r0 r1 r2 r3 baseWord rest exitCond =
      (expTwoMulLoopExitControl iterCountNew exitCond **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmStackIs evmSp (baseWord :: expResultWord r0 r1 r2 r3 :: rest))) := by
  delta expHeadroomLoopExitFullStackPostFrame
  rfl

theorem expHeadroomLoopExitFullStackPostFrame_pcFree
    {sp evmSp iterCountNew r0 r1 r2 r3 : Word}
    {baseWord : EvmWord} {rest : List EvmWord} {exitCond : Prop} :
    (expHeadroomLoopExitFullStackPostFrame
      sp evmSp iterCountNew r0 r1 r2 r3 baseWord rest exitCond).pcFree := by
  rw [expHeadroomLoopExitFullStackPostFrame_unfold]
  pcFree

instance pcFreeInst_expHeadroomLoopExitFullStackPostFrame
    (sp evmSp iterCountNew r0 r1 r2 r3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop) :
    Assertion.PCFree
      (expHeadroomLoopExitFullStackPostFrame
        sp evmSp iterCountNew r0 r1 r2 r3 baseWord rest exitCond) :=
  ⟨expHeadroomLoopExitFullStackPostFrame_pcFree⟩

/-- Folded headroom loop-exit frame followed by the final pointer advance and
    epilogue, over the canonical appended-MUL code. -/
theorem exp_headroom_loop_exit_full_stack_frame_then_final_epilogue_canonical_appended
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (base : Word) :
    cpsTripleWithin (1 + 9) (base + 368) (base + 408)
      (evm_exp_headroom_canonical_appended_mul_code base)
      (expHeadroomLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
        r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)
      (expHeadroomLoopExitFullStackPostFrame sp evmSp iterCountNew
        r0 r1 r2 r3 baseWord rest exitCond) := by
  have h := exp_headroom_final_advance_then_epilogue_full_post_stack_canonical_appended
    sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3
    baseWord rest exitCond base
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [expHeadroomLoopExitFullStackPreFrame_unfold] at hp
      rw [expTwoMulLoopExitStackTailFrame_unfold]
      rw [evmStackIs_cons] at hp
      rw [evmStackIs_cons] at hp
      rw [evmWordIs_sp32_limbs_eq evmSp (expResultWord d0 d1 d2 d3) d0 d1 d2 d3
        (expResultWord_getLimbN_0 d0 d1 d2 d3)
        (expResultWord_getLimbN_1 d0 d1 d2 d3)
        (expResultWord_getLimbN_2 d0 d1 d2 d3)
        (expResultWord_getLimbN_3 d0 d1 d2 d3)] at hp
      rw [← show evmSp + signExtend12 (32 : BitVec 12) = evmSp + 32 from by
        rw [signExtend12_32]] at hp
      rw [← show evmSp + signExtend12 (40 : BitVec 12) = evmSp + 40 from by
        rw [signExtend12_40]] at hp
      rw [← show evmSp + signExtend12 (48 : BitVec 12) = evmSp + 48 from by
        rw [signExtend12_48]] at hp
      rw [← show evmSp + signExtend12 (56 : BitVec 12) = evmSp + 56 from by
        rw [signExtend12_56]] at hp
      rw [show (evmSp + signExtend12 (32 : BitVec 12) + 32 : Word) = evmSp + 64 from by
        rw [signExtend12_32]
        bv_addr] at hp
      xperm_hyp hp)
    (fun _ hp => by
      rw [expHeadroomLoopExitFullStackPostFrame_unfold]
      xperm_hyp hp)
    h

/-- Entry prefix plus the fixed 256-step loop, with the explicit bridge frame
    folded into the first-iteration residual precondition. This is the main
    headroom body surface before the final epilogue writes the result back. -/
theorem exp_headroom_entry_to_final_loop_post
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193)) base (base + 72 + 296)
      (evm_exp_headroom_canonical_appended_mul_code base)
      ((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ b0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ b1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ b2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ b3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       ((evmSp + signExtend12 ((-128) : BitVec 12)) ↦ₘ h0) **
       ((evmSp + signExtend12 ((-120) : BitVec 12)) ↦ₘ h1) **
       ((evmSp + signExtend12 ((-112) : BitVec 12)) ↦ₘ h2) **
       ((evmSp + signExtend12 ((-104) : BitVec 12)) ↦ₘ h3) **
       ((evmSp + signExtend12 ((-96) : BitVec 12)) ↦ₘ h4) **
       ((evmSp + signExtend12 ((-88) : BitVec 12)) ↦ₘ h5) **
       ((evmSp + signExtend12 ((-80) : BitVec 12)) ↦ₘ h6) **
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ h7)) **
       expHeadroomLoopEntryBridgeFrame evmSp v18 vOld dWord eWord rest))
      (expFinalLoopFirstIterPost sp (evmSp + signExtend12 ((-128) : BitVec 12))
        (expResultWord b0 b1 b2 b3) (expResultWord e0 e1 e2 e3)
        (expResultWord b0 b1 b2 b3 :: expResultWord e0 e1 e2 e3 :: rest)) := by
  let bridgeFrame := expHeadroomLoopEntryBridgeFrame evmSp v18 vOld dWord eWord rest
  have hEntry :=
    exp_headroom_entry_to_loopadvance_canonical_appended_folded_framed
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base
      bridgeFrame (by
        dsimp [bridgeFrame]
        exact expHeadroomLoopEntryBridgeFrame_pcFree)
  have hLoop :=
    exp_headroom_loop_lifted_folded_canonical_appended
      sp (evmSp + signExtend12 ((-128) : BitVec 12)) base
      (expResultWord b0 b1 b2 b3) (expResultWord e0 e1 e2 e3)
      dWord eWord
      (expResultWord b0 b1 b2 b3 :: expResultWord e0 e1 e2 e3 :: rest)
      lookahead vOld v18 hbase
  rw [show (base + 72 + 44 : Word) = base + 116 from by bv_addr] at hLoop
  refine cpsTripleWithin_seq_perm_same_cr ?_ hEntry hLoop
  intro ps hps
  dsimp [bridgeFrame] at hps
  exact expHeadroomLoopEntryPost_to_firstIterPreWithResidual hps


@[irreducible]
def expHeadroomFinalLoopExtraFrame
    (evmSp : Word) (baseWord exponentWord scratchWord resultWord : EvmWord) : Assertion :=
  evmStackIs (evmSp + signExtend12 ((-128) : BitVec 12))
      [baseWord, exponentWord, scratchWord, resultWord] **
    (regOwn .x19 ** regOwn .x20 ** regOwn .x18 ** regOwn .x16 **
     regOwn .x1 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11)

theorem expHeadroomFinalLoopExtraFrame_unfold
    {evmSp : Word} {baseWord exponentWord scratchWord resultWord : EvmWord} :
    expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord resultWord =
      (evmStackIs (evmSp + signExtend12 ((-128) : BitVec 12))
          [baseWord, exponentWord, scratchWord, resultWord] **
        (regOwn .x19 ** regOwn .x20 ** regOwn .x18 ** regOwn .x16 **
         regOwn .x1 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11)) := by
  delta expHeadroomFinalLoopExtraFrame
  rfl

theorem expHeadroomFinalLoopExtraFrame_pcFree
    {evmSp : Word} {baseWord exponentWord scratchWord resultWord : EvmWord} :
    (expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord resultWord).pcFree := by
  rw [expHeadroomFinalLoopExtraFrame_unfold]
  pcFree

instance pcFreeInst_expHeadroomFinalLoopExtraFrame
    (evmSp : Word) (baseWord exponentWord scratchWord resultWord : EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord resultWord) :=
  ⟨expHeadroomFinalLoopExtraFrame_pcFree⟩

/-- Re-express the residual-loop folded post as the final headroom epilogue
    precondition plus the unused headroom scratch/leftover-register frame. -/
theorem expFinalLoopFirstIterPost_to_headroom_epilogue_pre
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h : (expFinalLoopFirstIterPost sp (evmSp + signExtend12 ((-128) : BitVec 12))
            baseWord exponentWord (baseWord :: exponentWord :: rest)) ps) :
    ∃ (icNew : Word) (scratchWord : EvmWord),
      (expHeadroomLoopExitFullStackPreFrame sp evmSp icNew
          ((EvmWord.exp baseWord exponentWord).getLimbN 3)
          ((EvmWord.exp baseWord exponentWord).getLimbN 0)
          ((EvmWord.exp baseWord exponentWord).getLimbN 1)
          ((EvmWord.exp baseWord exponentWord).getLimbN 2)
          ((EvmWord.exp baseWord exponentWord).getLimbN 3)
          (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
          (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
          baseWord rest (icNew = 0) **
       expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
          (EvmWord.exp baseWord exponentWord)) ps := by
  rw [expFinalLoopFirstIterPost_unfold] at h
  obtain ⟨psExit, psLive, h_disjoint, h_union, hExit, hLive⟩ := h
  unfold expExpFinalExitR at hExit
  obtain ⟨icNew, w0, w1, w2, w3, hExit⟩ := hExit
  refine ⟨icNew, expResultWord w0 w1 w2 w3, ?_⟩
  have hCombined :
      ((expTwoMulLoopExitFullStackPreFrame sp
          (((evmSp + signExtend12 ((-128) : BitVec 12)) +
              signExtend12 (64 : BitVec 12)) - 64)
          icNew
          ((EvmWord.exp baseWord exponentWord).getLimbN 3)
          ((EvmWord.exp baseWord exponentWord).getLimbN 0)
          ((EvmWord.exp baseWord exponentWord).getLimbN 1)
          ((EvmWord.exp baseWord exponentWord).getLimbN 2)
          ((EvmWord.exp baseWord exponentWord).getLimbN 3)
          (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
          (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
          (expResultWord (baseWord.getLimbN 0) (baseWord.getLimbN 1)
            (baseWord.getLimbN 2) (baseWord.getLimbN 3))
          [expResultWord w0 w1 w2 w3, EvmWord.exp baseWord exponentWord]
          (icNew = 0) **
        (regOwn .x19 ** regOwn .x20 ** regOwn .x18 ** regOwn .x16 **
         regOwn .x1 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11)) **
       evmStackIs ((evmSp + signExtend12 ((-128) : BitVec 12)) + 128)
          (baseWord :: exponentWord :: rest)) ps :=
    ⟨psExit, psLive, h_disjoint, h_union, hExit, hLive⟩
  rw [expHeadroomLoopExitFullStackPreFrame_unfold,
    expHeadroomFinalLoopExtraFrame_unfold]
  rw [expTwoMulLoopExitFullStackPreFrame_unfold] at hCombined
  rw [show (((evmSp + signExtend12 ((-128) : BitVec 12)) +
          signExtend12 (64 : BitVec 12)) - 64 : Word)
        = evmSp + signExtend12 ((-128) : BitVec 12) from by
        rw [show (signExtend12 ((-128) : BitVec 12) : Word) = 18446744073709551488 from by decide,
          show (signExtend12 (64 : BitVec 12) : Word) = 64 from by decide]
        bv_omega] at hCombined
  rw [show ((evmSp + signExtend12 ((-128) : BitVec 12)) +
          signExtend12 (64 : BitVec 12) : Word)
        = evmSp + signExtend12 ((-64) : BitVec 12) from by
        rw [show (signExtend12 ((-128) : BitVec 12) : Word) = 18446744073709551488 from by decide,
          show (signExtend12 (64 : BitVec 12) : Word) = 64 from by decide,
          show (signExtend12 ((-64) : BitVec 12) : Word) = 18446744073709551552 from by decide]
        bv_omega] at hCombined
  rw [show ((evmSp + signExtend12 ((-128) : BitVec 12)) + 128 : Word)
        = evmSp from by
        rw [show (signExtend12 ((-128) : BitVec 12) : Word) = 18446744073709551488 from by decide]
        bv_omega] at hCombined
  rw [expResultWord_getLimbN_self baseWord,
    expResultWord_getLimbN_self exponentWord] at hCombined
  rw [expResultWord_getLimbN_self exponentWord]
  xperm_hyp hCombined


@[irreducible]
def expHeadroomFinalEpilogueFramedPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  fun ps => ∃ (icNew : Word) (scratchWord : EvmWord),
    (expHeadroomLoopExitFullStackPostFrame sp evmSp icNew
        ((EvmWord.exp baseWord exponentWord).getLimbN 0)
        ((EvmWord.exp baseWord exponentWord).getLimbN 1)
        ((EvmWord.exp baseWord exponentWord).getLimbN 2)
        ((EvmWord.exp baseWord exponentWord).getLimbN 3)
        baseWord rest (icNew = 0) **
      expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
        (EvmWord.exp baseWord exponentWord)) ps

theorem expHeadroomFinalEpilogueFramedPost_unfold
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expHeadroomFinalEpilogueFramedPost sp evmSp baseWord exponentWord rest =
      (fun ps => ∃ (icNew : Word) (scratchWord : EvmWord),
        (expHeadroomLoopExitFullStackPostFrame sp evmSp icNew
            ((EvmWord.exp baseWord exponentWord).getLimbN 0)
            ((EvmWord.exp baseWord exponentWord).getLimbN 1)
            ((EvmWord.exp baseWord exponentWord).getLimbN 2)
            ((EvmWord.exp baseWord exponentWord).getLimbN 3)
            baseWord rest (icNew = 0) **
          expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
            (EvmWord.exp baseWord exponentWord)) ps) := by
  delta expHeadroomFinalEpilogueFramedPost
  rfl

/-- The folded residual-loop post followed by the final headroom pointer restore
    and epilogue, preserving unused headroom scratch/leftover-register resources. -/
theorem exp_headroom_final_loop_post_then_epilogue_framed
    (sp evmSp base : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    cpsTripleWithin (1 + 9) (base + 368) (base + 408)
      (evm_exp_headroom_canonical_appended_mul_code base)
      (expFinalLoopFirstIterPost sp (evmSp + signExtend12 ((-128) : BitVec 12))
        baseWord exponentWord (baseWord :: exponentWord :: rest))
      (expHeadroomFinalEpilogueFramedPost sp evmSp baseWord exponentWord rest) := by
  rw [expHeadroomFinalEpilogueFramedPost_unfold]
  refine cpsTripleWithin_weaken
    (fun _ hp => expFinalLoopFirstIterPost_to_headroom_epilogue_pre hp)
    (fun _ hp => hp)
    ?_
  refine cpsTripleWithin_exists_pre ?_
  intro icNew
  refine cpsTripleWithin_exists_pre ?_
  intro scratchWord
  have hEpi := exp_headroom_loop_exit_full_stack_frame_then_final_epilogue_canonical_appended
    sp evmSp icNew
    ((EvmWord.exp baseWord exponentWord).getLimbN 3)
    ((EvmWord.exp baseWord exponentWord).getLimbN 0)
    ((EvmWord.exp baseWord exponentWord).getLimbN 1)
    ((EvmWord.exp baseWord exponentWord).getLimbN 2)
    ((EvmWord.exp baseWord exponentWord).getLimbN 3)
    (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
    (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
    baseWord rest (icNew = 0) base
  have hFramed := cpsTripleWithin_frameR
    (expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
      (EvmWord.exp baseWord exponentWord))
    (by pcFree) hEpi
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => ⟨icNew, scratchWord, hp⟩)
    hFramed

/-- Entry prefix plus the fixed full loop and final epilogue, with the unused
    headroom scratch/leftover-register resources preserved in a folded post. -/
theorem exp_headroom_entry_to_final_epilogue_framed
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (evm_exp_headroom_canonical_appended_mul_code base)
      ((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ b0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ b1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ b2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ b3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       ((evmSp + signExtend12 ((-128) : BitVec 12)) ↦ₘ h0) **
       ((evmSp + signExtend12 ((-120) : BitVec 12)) ↦ₘ h1) **
       ((evmSp + signExtend12 ((-112) : BitVec 12)) ↦ₘ h2) **
       ((evmSp + signExtend12 ((-104) : BitVec 12)) ↦ₘ h3) **
       ((evmSp + signExtend12 ((-96) : BitVec 12)) ↦ₘ h4) **
       ((evmSp + signExtend12 ((-88) : BitVec 12)) ↦ₘ h5) **
       ((evmSp + signExtend12 ((-80) : BitVec 12)) ↦ₘ h6) **
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ h7)) **
       expHeadroomLoopEntryBridgeFrame evmSp v18 vOld dWord eWord rest))
      (expHeadroomFinalEpilogueFramedPost sp evmSp
        (expResultWord b0 b1 b2 b3) (expResultWord e0 e1 e2 e3) rest) := by
  have hLoop := exp_headroom_entry_to_final_loop_post
    sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
    b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base
    dWord eWord rest lookahead vOld v18 hbase
  have hEpi := exp_headroom_final_loop_post_then_epilogue_framed
    sp evmSp base (expResultWord b0 b1 b2 b3) (expResultWord e0 e1 e2 e3) rest
  rw [show (base + 368 : Word) = base + 72 + 296 from by bv_addr] at hEpi
  refine cpsTripleWithin_seq_perm_same_cr ?_ hLoop hEpi
  intro ps hp
  exact hp


@[irreducible]
def expHeadroomFinalVisiblePost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  fun ps => ∃ (icNew : Word) (scratchWord : EvmWord),
    (expTwoMulLoopExitControl icNew (icNew = 0) **
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
          ((EvmWord.exp baseWord exponentWord).getLimbN 0)) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ
          ((EvmWord.exp baseWord exponentWord).getLimbN 1)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ
          ((EvmWord.exp baseWord exponentWord).getLimbN 2)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ
          ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
       evmWordIs evmSp baseWord **
       evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
      expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
        (EvmWord.exp baseWord exponentWord)) ps

theorem expHeadroomFinalVisiblePost_unfold
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expHeadroomFinalVisiblePost sp evmSp baseWord exponentWord rest =
      (fun ps => ∃ (icNew : Word) (scratchWord : EvmWord),
        (expTwoMulLoopExitControl icNew (icNew = 0) **
          ((.x2 ↦ᵣ sp) **
           (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
           (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
           ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
              ((EvmWord.exp baseWord exponentWord).getLimbN 0)) **
           ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ
              ((EvmWord.exp baseWord exponentWord).getLimbN 1)) **
           ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ
              ((EvmWord.exp baseWord exponentWord).getLimbN 2)) **
           ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ
              ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
           evmWordIs evmSp baseWord **
           evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
          expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
            (EvmWord.exp baseWord exponentWord)) ps) := by
  delta expHeadroomFinalVisiblePost
  rfl

theorem expHeadroomFinalVisiblePost_pcFree
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    (expHeadroomFinalVisiblePost sp evmSp baseWord exponentWord rest).pcFree := by
  intro ps h_post
  rw [expHeadroomFinalVisiblePost_unfold] at h_post
  obtain ⟨icNew, scratchWord, h_post⟩ := h_post
  have hVisible :
      (((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
          ((EvmWord.exp baseWord exponentWord).getLimbN 0)) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ
          ((EvmWord.exp baseWord exponentWord).getLimbN 1)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ
          ((EvmWord.exp baseWord exponentWord).getLimbN 2)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ
          ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
       evmWordIs evmSp baseWord **
       evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)).pcFree) := by
    pcFree
  exact (pcFree_sepConj expTwoMulLoopExitControl_pcFree
    (pcFree_sepConj hVisible expHeadroomFinalLoopExtraFrame_pcFree)) ps h_post

instance pcFreeInst_expHeadroomFinalVisiblePost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalVisiblePost sp evmSp baseWord exponentWord rest) :=
  ⟨expHeadroomFinalVisiblePost_pcFree⟩


@[irreducible]
def expHeadroomFinalCleanVisiblePost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  fun ps => ∃ (scratchWord : EvmWord),
    (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
          ((EvmWord.exp baseWord exponentWord).getLimbN 0)) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ
          ((EvmWord.exp baseWord exponentWord).getLimbN 1)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ
          ((EvmWord.exp baseWord exponentWord).getLimbN 2)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ
          ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
       evmWordIs evmSp baseWord **
       evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
      expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
        (EvmWord.exp baseWord exponentWord)) ps

theorem expHeadroomFinalCleanVisiblePost_unfold
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expHeadroomFinalCleanVisiblePost sp evmSp baseWord exponentWord rest =
      (fun ps => ∃ (scratchWord : EvmWord),
        (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
          ((.x2 ↦ᵣ sp) **
           (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
           (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
           ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
              ((EvmWord.exp baseWord exponentWord).getLimbN 0)) **
           ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ
              ((EvmWord.exp baseWord exponentWord).getLimbN 1)) **
           ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ
              ((EvmWord.exp baseWord exponentWord).getLimbN 2)) **
           ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ
              ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
           evmWordIs evmSp baseWord **
           evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
          expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
            (EvmWord.exp baseWord exponentWord)) ps) := by
  delta expHeadroomFinalCleanVisiblePost
  rfl

theorem expHeadroomFinalCleanVisiblePost_pcFree
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    (expHeadroomFinalCleanVisiblePost sp evmSp baseWord exponentWord rest).pcFree := by
  intro ps h_post
  rw [expHeadroomFinalCleanVisiblePost_unfold] at h_post
  obtain ⟨scratchWord, h_post⟩ := h_post
  have hControl : (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))).pcFree) := by
    pcFree
  have hVisible :
      (((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
          ((EvmWord.exp baseWord exponentWord).getLimbN 0)) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ
          ((EvmWord.exp baseWord exponentWord).getLimbN 1)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ
          ((EvmWord.exp baseWord exponentWord).getLimbN 2)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ
          ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
       evmWordIs evmSp baseWord **
       evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)).pcFree) := by
    pcFree
  exact (pcFree_sepConj hControl
    (pcFree_sepConj hVisible expHeadroomFinalLoopExtraFrame_pcFree)) ps h_post

instance pcFreeInst_expHeadroomFinalCleanVisiblePost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalCleanVisiblePost sp evmSp baseWord exponentWord rest) :=
  ⟨expHeadroomFinalCleanVisiblePost_pcFree⟩

@[irreducible]
def expHeadroomFinalCleanStackVisiblePost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  fun ps => ∃ (scratchWord : EvmWord),
    (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
       evmWordIs sp (EvmWord.exp baseWord exponentWord) **
       evmStackIs evmSp (baseWord :: EvmWord.exp baseWord exponentWord :: rest)) **
      expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
        (EvmWord.exp baseWord exponentWord)) ps

theorem expHeadroomFinalCleanStackVisiblePost_unfold
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expHeadroomFinalCleanStackVisiblePost sp evmSp baseWord exponentWord rest =
      (fun ps => ∃ (scratchWord : EvmWord),
        (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
          ((.x2 ↦ᵣ sp) **
           (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
           (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
           evmWordIs sp (EvmWord.exp baseWord exponentWord) **
           evmStackIs evmSp (baseWord :: EvmWord.exp baseWord exponentWord :: rest)) **
          expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
            (EvmWord.exp baseWord exponentWord)) ps) := by
  delta expHeadroomFinalCleanStackVisiblePost
  rfl

theorem expHeadroomFinalCleanStackVisiblePost_pcFree
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    (expHeadroomFinalCleanStackVisiblePost sp evmSp baseWord exponentWord rest).pcFree := by
  intro ps h_post
  rw [expHeadroomFinalCleanStackVisiblePost_unfold] at h_post
  obtain ⟨scratchWord, h_post⟩ := h_post
  have hControl : (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))).pcFree) := by
    pcFree
  have hVisible :
      (((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
       evmWordIs sp (EvmWord.exp baseWord exponentWord) **
       evmStackIs evmSp (baseWord :: EvmWord.exp baseWord exponentWord :: rest)).pcFree) := by
    pcFree
  exact (pcFree_sepConj hControl
    (pcFree_sepConj hVisible expHeadroomFinalLoopExtraFrame_pcFree)) ps h_post

instance pcFreeInst_expHeadroomFinalCleanStackVisiblePost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalCleanStackVisiblePost sp evmSp baseWord exponentWord rest) :=
  ⟨expHeadroomFinalCleanStackVisiblePost_pcFree⟩

@[irreducible]
def expHeadroomFinalCleanLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  fun ps => ∃ (scratchWord : EvmWord),
    (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + 32)) **
       (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
       evmWordIs sp (EvmWord.exp baseWord exponentWord) **
       evmWordIs evmSp baseWord **
       evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
      expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
        (EvmWord.exp baseWord exponentWord)) ps

theorem expHeadroomFinalCleanLiveStackPost_unfold
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expHeadroomFinalCleanLiveStackPost sp evmSp baseWord exponentWord rest =
      (fun ps => ∃ (scratchWord : EvmWord),
        (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
          ((.x2 ↦ᵣ sp) **
           (.x12 ↦ᵣ (evmSp + 32)) **
           (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
           evmWordIs sp (EvmWord.exp baseWord exponentWord) **
           evmWordIs evmSp baseWord **
           evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
          expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
            (EvmWord.exp baseWord exponentWord)) ps) := by
  delta expHeadroomFinalCleanLiveStackPost
  rfl

theorem expHeadroomFinalCleanLiveStackPost_pcFree
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    (expHeadroomFinalCleanLiveStackPost sp evmSp baseWord exponentWord rest).pcFree := by
  intro ps h_post
  rw [expHeadroomFinalCleanLiveStackPost_unfold] at h_post
  obtain ⟨scratchWord, h_post⟩ := h_post
  have hControl : (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))).pcFree) := by
    pcFree
  have hVisible :
      (((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + 32)) **
       (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
       evmWordIs sp (EvmWord.exp baseWord exponentWord) **
       evmWordIs evmSp baseWord **
       evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)).pcFree) := by
    pcFree
  exact (pcFree_sepConj hControl
    (pcFree_sepConj hVisible expHeadroomFinalLoopExtraFrame_pcFree)) ps h_post

instance pcFreeInst_expHeadroomFinalCleanLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalCleanLiveStackPost sp evmSp baseWord exponentWord rest) :=
  ⟨expHeadroomFinalCleanLiveStackPost_pcFree⟩

@[irreducible]
def expHeadroomFinalCleanOwnedBaseLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  fun ps => ∃ (scratchWord : EvmWord),
    (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + 32)) **
       (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
       evmWordIs sp (EvmWord.exp baseWord exponentWord) **
       evmWordOwn evmSp **
       evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
      expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
        (EvmWord.exp baseWord exponentWord)) ps

theorem expHeadroomFinalCleanOwnedBaseLiveStackPost_unfold
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expHeadroomFinalCleanOwnedBaseLiveStackPost sp evmSp baseWord exponentWord rest =
      (fun ps => ∃ (scratchWord : EvmWord),
        (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
          ((.x2 ↦ᵣ sp) **
           (.x12 ↦ᵣ (evmSp + 32)) **
           (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
           evmWordIs sp (EvmWord.exp baseWord exponentWord) **
           evmWordOwn evmSp **
           evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
          expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
            (EvmWord.exp baseWord exponentWord)) ps) := by
  delta expHeadroomFinalCleanOwnedBaseLiveStackPost
  rfl

theorem expHeadroomFinalCleanOwnedBaseLiveStackPost_pcFree
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    (expHeadroomFinalCleanOwnedBaseLiveStackPost sp evmSp baseWord exponentWord rest).pcFree := by
  intro ps h_post
  rw [expHeadroomFinalCleanOwnedBaseLiveStackPost_unfold] at h_post
  obtain ⟨scratchWord, h_post⟩ := h_post
  have hControl : (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))).pcFree) := by
    pcFree
  have hVisible :
      (((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + 32)) **
       (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
       evmWordIs sp (EvmWord.exp baseWord exponentWord) **
       evmWordOwn evmSp **
       evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)).pcFree) := by
    pcFree
  exact (pcFree_sepConj hControl
    (pcFree_sepConj hVisible expHeadroomFinalLoopExtraFrame_pcFree)) ps h_post

instance pcFreeInst_expHeadroomFinalCleanOwnedBaseLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalCleanOwnedBaseLiveStackPost sp evmSp baseWord exponentWord rest) :=
  ⟨expHeadroomFinalCleanOwnedBaseLiveStackPost_pcFree⟩

private theorem expHeadroomCleanLiveVisible_to_ownedBase
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    ∀ ps,
      (((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + 32)) **
       (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
       evmWordIs sp (EvmWord.exp baseWord exponentWord) **
       evmWordIs evmSp baseWord **
       evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) ps) →
      (((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + 32)) **
       (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
       evmWordIs sp (EvmWord.exp baseWord exponentWord) **
       evmWordOwn evmSp **
       evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) ps) := by
  exact sepConj_mono (fun _ h => h)
    (sepConj_mono (fun _ h => h)
      (sepConj_mono (fun _ h => h)
        (sepConj_mono (fun _ h => h)
          (sepConj_mono (fun _ h => evmWordIs_to_evmWordOwn h) (fun _ h => h)))))

/-- Weaken the consumed base cell in the clean live-stack post to owned memory. -/
theorem expHeadroomFinalCleanLiveStackPost_to_ownedBasePost
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h : expHeadroomFinalCleanLiveStackPost sp evmSp baseWord exponentWord rest ps) :
    expHeadroomFinalCleanOwnedBaseLiveStackPost sp evmSp baseWord exponentWord rest ps := by
  rw [expHeadroomFinalCleanLiveStackPost_unfold] at h
  obtain ⟨scratchWord, h⟩ := h
  rw [expHeadroomFinalCleanOwnedBaseLiveStackPost_unfold]
  refine ⟨scratchWord, ?_⟩
  exact sepConj_mono (fun _ h_control => h_control)
    (sepConj_mono expHeadroomCleanLiveVisible_to_ownedBase (fun _ h_frame => h_frame)) _ h

/-- Fold the clean visible post's raw result limbs into `evmWordIs sp result`
    while keeping the actual final live stack rooted at `evmSp + 32`. -/
theorem expHeadroomFinalCleanVisiblePost_to_cleanLiveStackPost
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h : expHeadroomFinalCleanVisiblePost sp evmSp baseWord exponentWord rest ps) :
    expHeadroomFinalCleanLiveStackPost sp evmSp baseWord exponentWord rest ps := by
  rw [expHeadroomFinalCleanVisiblePost_unfold] at h
  obtain ⟨scratchWord, h⟩ := h
  rw [expHeadroomFinalCleanLiveStackPost_unfold]
  refine ⟨scratchWord, ?_⟩
  simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24,
    signExtend12_32] at h
  rw [show (sp + 0 : Word) = sp from by bv_omega] at h
  rw [evmWordIs_sp_limbs_eq_right sp (EvmWord.exp baseWord exponentWord)
    _ _ _ _ (evmWordIs evmSp baseWord **
      evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest))
    rfl rfl rfl rfl] at h
  xperm_hyp h

/-- Fold the clean visible post's raw result limbs and consumed-base cell into
    stack-shaped assertions. The leftover headroom/scratch frame remains
    explicit because it is still part of the current verified surface. -/
theorem expHeadroomFinalCleanVisiblePost_to_cleanStackVisiblePost
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h : expHeadroomFinalCleanVisiblePost sp evmSp baseWord exponentWord rest ps) :
    expHeadroomFinalCleanStackVisiblePost sp evmSp baseWord exponentWord rest ps := by
  rw [expHeadroomFinalCleanVisiblePost_unfold] at h
  obtain ⟨scratchWord, h⟩ := h
  rw [expHeadroomFinalCleanStackVisiblePost_unfold]
  refine ⟨scratchWord, ?_⟩
  simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24] at h
  rw [show (sp + 0 : Word) = sp from by bv_omega] at h
  rw [evmWordIs_sp_limbs_eq_right sp (EvmWord.exp baseWord exponentWord)
    _ _ _ _ (evmWordIs evmSp baseWord **
      evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest))
    rfl rfl rfl rfl] at h
  rw [evmStackIs_cons]
  xperm_hyp h


/-- Remove the loop-exit pure condition from the visible post, exposing the final
    loop counter register as the concrete zero word. -/
theorem expHeadroomFinalVisiblePost_to_cleanVisiblePost
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h : expHeadroomFinalVisiblePost sp evmSp baseWord exponentWord rest ps) :
    expHeadroomFinalCleanVisiblePost sp evmSp baseWord exponentWord rest ps := by
  rw [expHeadroomFinalVisiblePost_unfold] at h
  obtain ⟨icNew, scratchWord, h⟩ := h
  rw [expTwoMulLoopExitControl_unfold] at h
  have hFull := h
  obtain ⟨hControlState, _hRestState, _hDisjoint, _hUnion, hControl, _hRest⟩ := h
  obtain ⟨_hX9State, hControlTailState, _hControlDisjoint, _hControlUnion, _hX9, hControlTail⟩ := hControl
  have h_zero : icNew = 0 := ((sepConj_pure_right hControlTailState).1 hControlTail).2
  rw [h_zero] at hFull
  simp only [pure_true_eq_emp, sepConj_emp_right'] at hFull
  rw [expHeadroomFinalCleanVisiblePost_unfold]
  refine ⟨scratchWord, ?_⟩
  xperm_hyp hFull

/-- Expose the folded final framed post as a live-stack view at the final EVM
    stack pointer (`evmSp + 32`), with the consumed base word and unused
    headroom/leftover frame still explicit. -/
theorem expHeadroomFinalEpilogueFramedPost_to_visiblePost
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h : expHeadroomFinalEpilogueFramedPost sp evmSp baseWord exponentWord rest ps) :
    expHeadroomFinalVisiblePost sp evmSp baseWord exponentWord rest ps := by
  rw [expHeadroomFinalEpilogueFramedPost_unfold] at h
  obtain ⟨icNew, scratchWord, h⟩ := h
  rw [expHeadroomFinalVisiblePost_unfold]
  refine ⟨icNew, scratchWord, ?_⟩
  rw [expHeadroomLoopExitFullStackPostFrame_unfold] at h
  rw [evmStackIs_cons] at h
  rw [show (evmSp + 32 : Word) = evmSp + signExtend12 (32 : BitVec 12) from by
    rw [signExtend12_32]] at h
  rw [expResultWord_getLimbN_self (EvmWord.exp baseWord exponentWord)] at h
  rw [show (evmSp + 32 : Word) = evmSp + signExtend12 (32 : BitVec 12) from by
    rw [signExtend12_32]]
  xperm_hyp h

/-- Entry prefix plus fixed full loop and final epilogue, with the final live
    EVM stack exposed at `evmSp + 32`. -/
theorem exp_headroom_entry_to_final_visible_post
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (evm_exp_headroom_canonical_appended_mul_code base)
      ((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ b0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ b1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ b2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ b3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       ((evmSp + signExtend12 ((-128) : BitVec 12)) ↦ₘ h0) **
       ((evmSp + signExtend12 ((-120) : BitVec 12)) ↦ₘ h1) **
       ((evmSp + signExtend12 ((-112) : BitVec 12)) ↦ₘ h2) **
       ((evmSp + signExtend12 ((-104) : BitVec 12)) ↦ₘ h3) **
       ((evmSp + signExtend12 ((-96) : BitVec 12)) ↦ₘ h4) **
       ((evmSp + signExtend12 ((-88) : BitVec 12)) ↦ₘ h5) **
       ((evmSp + signExtend12 ((-80) : BitVec 12)) ↦ₘ h6) **
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ h7)) **
       expHeadroomLoopEntryBridgeFrame evmSp v18 vOld dWord eWord rest))
      (expHeadroomFinalVisiblePost sp evmSp
        (expResultWord b0 b1 b2 b3) (expResultWord e0 e1 e2 e3) rest) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => expHeadroomFinalEpilogueFramedPost_to_visiblePost hp)
    (exp_headroom_entry_to_final_epilogue_framed
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base
      dWord eWord rest lookahead vOld v18 hbase)

/-- Entry prefix plus fixed full loop and final epilogue, with the loop-exit
    pure fact consumed into concrete final control resources. -/
theorem exp_headroom_entry_to_final_clean_visible_post
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (evm_exp_headroom_canonical_appended_mul_code base)
      ((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ b0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ b1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ b2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ b3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       ((evmSp + signExtend12 ((-128) : BitVec 12)) ↦ₘ h0) **
       ((evmSp + signExtend12 ((-120) : BitVec 12)) ↦ₘ h1) **
       ((evmSp + signExtend12 ((-112) : BitVec 12)) ↦ₘ h2) **
       ((evmSp + signExtend12 ((-104) : BitVec 12)) ↦ₘ h3) **
       ((evmSp + signExtend12 ((-96) : BitVec 12)) ↦ₘ h4) **
       ((evmSp + signExtend12 ((-88) : BitVec 12)) ↦ₘ h5) **
       ((evmSp + signExtend12 ((-80) : BitVec 12)) ↦ₘ h6) **
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ h7)) **
       expHeadroomLoopEntryBridgeFrame evmSp v18 vOld dWord eWord rest))
      (expHeadroomFinalCleanVisiblePost sp evmSp
        (expResultWord b0 b1 b2 b3) (expResultWord e0 e1 e2 e3) rest) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => expHeadroomFinalVisiblePost_to_cleanVisiblePost hp)
    (exp_headroom_entry_to_final_visible_post
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base
      dWord eWord rest lookahead vOld v18 hbase)

/-- Entry prefix plus fixed full loop and final epilogue, with result scratch
    limbs and the consumed-base/result-tail cells folded into stack-shaped
    assertions. -/
theorem exp_headroom_entry_to_final_clean_stack_visible_post
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (evm_exp_headroom_canonical_appended_mul_code base)
      ((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ b0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ b1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ b2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ b3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       ((evmSp + signExtend12 ((-128) : BitVec 12)) ↦ₘ h0) **
       ((evmSp + signExtend12 ((-120) : BitVec 12)) ↦ₘ h1) **
       ((evmSp + signExtend12 ((-112) : BitVec 12)) ↦ₘ h2) **
       ((evmSp + signExtend12 ((-104) : BitVec 12)) ↦ₘ h3) **
       ((evmSp + signExtend12 ((-96) : BitVec 12)) ↦ₘ h4) **
       ((evmSp + signExtend12 ((-88) : BitVec 12)) ↦ₘ h5) **
       ((evmSp + signExtend12 ((-80) : BitVec 12)) ↦ₘ h6) **
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ h7)) **
       expHeadroomLoopEntryBridgeFrame evmSp v18 vOld dWord eWord rest))
      (expHeadroomFinalCleanStackVisiblePost sp evmSp
        (expResultWord b0 b1 b2 b3) (expResultWord e0 e1 e2 e3) rest) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => expHeadroomFinalCleanVisiblePost_to_cleanStackVisiblePost hp)
    (exp_headroom_entry_to_final_clean_visible_post
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base
      dWord eWord rest lookahead vOld v18 hbase)


end EvmAsm.Evm64.Exp.Compose
