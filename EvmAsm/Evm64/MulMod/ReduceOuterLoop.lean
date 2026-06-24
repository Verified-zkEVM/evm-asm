/-
  EvmAsm.Evm64.MulMod.ReduceOuterLoop

  Outer eight-limb loop of the MULMOD 512-bit reducer. This file lifts the
  inner 64-bit bit-loop spec into the enclosing `evm_mulmod_reduce512_loop`
  code (the inner step sits at byte offset 8), and (later) composes the outer
  loop body and its eight-limb induction.
-/

import EvmAsm.Evm64.MulMod.ReduceBitLoop
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- The inner reducer-step block sits at byte offset 8 within
    `evm_mulmod_reduce512_loop` (after `LD x17` and `ADDI x15`). -/
theorem evm_mulmod_reduce512_loop_inner_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_code (base + 8) a = some i →
      (CodeReq.ofProg base evm_mulmod_reduce512_loop) a = some i := by
  intro a i h
  unfold evm_mulmod_reduce512_inner_step_code at h
  refine CodeReq.ofProg_mono_subrange base
    [Instr.LD .x17 .x16 0, Instr.ADDI .x15 .x0 64]
    evm_mulmod_reduce512_inner_step
    [Instr.ADDI .x16 .x16 4088, Instr.ADDI .x18 .x18 4095,
      Instr.BNE .x18 .x0 (-272 : BitVec 13)]
    ?_ a i ?_
  · decide
  · exact h

/-- The inner 64-bit bit loop, lifted to the enclosing `reduce512_loop` code:
    it runs from byte offset 8 to byte offset 264 (where the pointer-advance
    instructions begin), folding the current product limb `w` into the
    remainder. -/
theorem evm_mulmod_reduce512_loop_bit_loop_spec_within
    (sp base w x19v x20v : Word) (r n : EvmWord) :
    cpsTripleWithin (64 * 64) (base + 8) (base + 8 + 256)
      (CodeReq.ofProg base evm_mulmod_reduce512_loop)
      (mulModReduceBitLoopPre sp w (BitVec.ofNat 64 64) x19v x20v r n)
      (mulModReduceBitLoopPost sp (mulModReduceStepN r n w 64) n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_loop_inner_code_sub base)
    (h := evm_mulmod_reduce512_bit_loop_spec_within sp (base + 8) w x19v x20v r n)

/-- Outer-loop body prefix: `LD x17, [x16]` loads the current product limb and
    `ADDI x15, x0, 64` arms the inner bit counter, advancing to the inner loop
    at byte offset 8. -/
theorem evm_mulmod_reduce512_loop_prefix_spec_within
    (base ptr oldX17 oldX15 limb : Word) :
    cpsTripleWithin 2 base (base + 8)
      (CodeReq.ofProg base evm_mulmod_reduce512_loop)
      ((.x16 ↦ᵣ ptr) ** (.x17 ↦ᵣ oldX17) ** (.x15 ↦ᵣ oldX15) ** (.x0 ↦ᵣ (0 : Word)) **
       ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limb))
      ((.x16 ↦ᵣ ptr) ** (.x17 ↦ᵣ limb) **
       (.x15 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
       ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limb)) := by
  have hLDsub : ∀ a i, CodeReq.singleton base (Instr.LD .x17 .x16 0) a = some i →
      (CodeReq.ofProg base evm_mulmod_reduce512_loop) a = some i := by
    rw [← CodeReq.ofProg_singleton]
    refine CodeReq.ofProg_mono_sub base base evm_mulmod_reduce512_loop
      [Instr.LD .x17 .x16 0] 0 ?_ ?_ ?_ ?_
    · rw [show BitVec.ofNat 64 (4 * 0) = (0 : Word) by decide]; bv_omega
    · rfl
    · decide
    · decide
  have hADDIsub : ∀ a i, CodeReq.singleton (base + 4) (Instr.ADDI .x15 .x0 64) a = some i →
      (CodeReq.ofProg base evm_mulmod_reduce512_loop) a = some i := by
    rw [← CodeReq.ofProg_singleton]
    refine CodeReq.ofProg_mono_sub base (base + 4) evm_mulmod_reduce512_loop
      [Instr.ADDI .x15 .x0 64] 1 ?_ ?_ ?_ ?_
    · rw [show BitVec.ofNat 64 (4 * 1) = (4 : Word) by decide]
    · rfl
    · decide
    · decide
  have hLD := cpsTripleWithin_extend_code (hmono := hLDsub)
    (h := ld_spec_gen_within .x17 .x16 ptr oldX17 limb (0 : BitVec 12) base (by nofun))
  have hADDI := cpsTripleWithin_extend_code (hmono := hADDIsub)
    (h := addi_spec_gen_within .x15 .x0 oldX15 (0 : Word) (64 : BitVec 12) (base + 4) (by decide))
  have hLDf := cpsTripleWithin_frameR ((.x15 ↦ᵣ oldX15) ** (.x0 ↦ᵣ (0 : Word))) (by pcFree) hLD
  have hADDIf := cpsTripleWithin_frameR
    ((.x16 ↦ᵣ ptr) ** (.x17 ↦ᵣ limb) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limb))
    (by pcFree) hADDI
  rw [show (base + 8 : Word) = base + 4 + 4 from by bv_omega]
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hLDf hADDIf)

/-- One outer-loop iteration up to the pointer-advance: load the product limb
    at `x16`, run the inner 64-bit bit loop, and land at byte offset 264 with
    that limb folded into the remainder (`mulModReduceStepN r n limb 64`). -/
theorem evm_mulmod_reduce512_loop_fold_one_limb_spec_within
    (sp base ptr oldX17 oldX15 x19v x20v limb : Word) (r n : EvmWord) :
    cpsTripleWithin (2 + 64 * 64) base (base + 8 + 256)
      (CodeReq.ofProg base evm_mulmod_reduce512_loop)
      ((.x12 ↦ᵣ sp) ** (.x16 ↦ᵣ ptr) ** (.x17 ↦ᵣ oldX17) ** (.x15 ↦ᵣ oldX15) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ x19v) ** (.x20 ↦ᵣ x20v) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
       ((sp + signExtend12 (224 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
       ((sp + signExtend12 (232 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
       ((sp + signExtend12 (240 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
       ((sp + signExtend12 (248 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3) **
       ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limb))
      (mulModReduceBitLoopPost sp (mulModReduceStepN r n limb 64) n **
       (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limb)) := by
  have hpf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x19 ↦ᵣ x19v) ** (.x20 ↦ᵣ x20v) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
     ((sp + signExtend12 (224 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
     ((sp + signExtend12 (232 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
     ((sp + signExtend12 (240 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
     ((sp + signExtend12 (248 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
     ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
     ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
     ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
     ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3))
    (by pcFree)
    (evm_mulmod_reduce512_loop_prefix_spec_within base ptr oldX17 oldX15 limb)
  have hif := cpsTripleWithin_frameR
    ((.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limb))
    (by pcFree)
    (evm_mulmod_reduce512_loop_bit_loop_spec_within sp base limb x19v x20v r n)
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_perm_same_cr
      (fun h hq => by
        rw [show (BitVec.ofNat 64 64) = (0 : Word) + signExtend12 (64 : BitVec 12) from by decide]
        unfold mulModReduceBitLoopPre bitLoopCommon
        xperm_hyp hq)
      hpf hif)

/-- The pointer-advance / loop-control suffix `[ADDI x16, ADDI x18, BNE]` sits at
    byte offset 264 (instruction index 66) within `evm_mulmod_reduce512_loop`. -/
theorem evm_mulmod_reduce512_loop_suffix_code_sub (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 264)
        [Instr.ADDI .x16 .x16 4088, Instr.ADDI .x18 .x18 4095,
          Instr.BNE .x18 .x0 (-272 : BitVec 13)]) a = some i →
      (CodeReq.ofProg base evm_mulmod_reduce512_loop) a = some i := by
  refine CodeReq.ofProg_mono_sub base (base + 264) evm_mulmod_reduce512_loop
    [Instr.ADDI .x16 .x16 4088, Instr.ADDI .x18 .x18 4095,
      Instr.BNE .x18 .x0 (-272 : BitVec 13)] 66 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 66) = (264 : Word) by decide]
  · rfl
  · rw [evm_mulmod_reduce512_loop_length]; decide
  · rw [evm_mulmod_reduce512_loop_length]; decide

/-- Single instruction `ADDI x16, x16, -8` at index 66 lives in `reduce512_loop`. -/
private theorem loop_addi16_code_sub (base : Word) :
    ∀ a i, CodeReq.singleton (base + 264) (Instr.ADDI .x16 .x16 4088) a = some i →
      (CodeReq.ofProg base evm_mulmod_reduce512_loop) a = some i := by
  rw [← CodeReq.ofProg_singleton]
  refine CodeReq.ofProg_mono_sub base (base + 264) evm_mulmod_reduce512_loop
    [Instr.ADDI .x16 .x16 4088] 66 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 66) = (264 : Word) by decide]
  · rfl
  · rw [evm_mulmod_reduce512_loop_length]; decide
  · rw [evm_mulmod_reduce512_loop_length]; decide

/-- Single instruction `ADDI x18, x18, -1` at index 67 lives in `reduce512_loop`. -/
private theorem loop_addi18_code_sub (base : Word) :
    ∀ a i, CodeReq.singleton (base + 268) (Instr.ADDI .x18 .x18 4095) a = some i →
      (CodeReq.ofProg base evm_mulmod_reduce512_loop) a = some i := by
  rw [← CodeReq.ofProg_singleton]
  refine CodeReq.ofProg_mono_sub base (base + 268) evm_mulmod_reduce512_loop
    [Instr.ADDI .x18 .x18 4095] 67 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 67) = (268 : Word) by decide]
  · rfl
  · rw [evm_mulmod_reduce512_loop_length]; decide
  · rw [evm_mulmod_reduce512_loop_length]; decide

/-- Outer-loop pointer/counter advance: `ADDI x16, x16, -8 ; ADDI x18, x18, -1`. -/
theorem evm_mulmod_reduce512_loop_advance_spec_within (base x16v x18v : Word) :
    cpsTripleWithin 2 (base + 264) (base + 272)
      (CodeReq.ofProg base evm_mulmod_reduce512_loop)
      ((.x16 ↦ᵣ x16v) ** (.x18 ↦ᵣ x18v))
      ((.x16 ↦ᵣ (x16v + signExtend12 (4088 : BitVec 12))) **
       (.x18 ↦ᵣ (x18v + signExtend12 (4095 : BitVec 12)))) := by
  have h16 := cpsTripleWithin_extend_code (hmono := loop_addi16_code_sub base)
    (h := addi_spec_gen_same_within .x16 x16v (4088 : BitVec 12) (base + 264) (by decide))
  have h18 := cpsTripleWithin_extend_code (hmono := loop_addi18_code_sub base)
    (h := addi_spec_gen_same_within .x18 x18v (4095 : BitVec 12) (base + 268) (by decide))
  have h16f := cpsTripleWithin_frameR ((.x18 ↦ᵣ x18v)) (by pcFree) h16
  have h18f := cpsTripleWithin_frameR
    ((.x16 ↦ᵣ (x16v + signExtend12 (4088 : BitVec 12)))) (by pcFree) h18
  rw [show (base + 264 + 4 : Word) = base + 268 from by bv_omega] at h16f
  rw [show (base + 272 : Word) = base + 268 + 4 from by bv_omega]
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h16f h18f)

/-- One outer-loop iteration through the pointer advance (everything but the
    final branch): load the limb, fold it into the remainder, then advance the
    limb pointer (`x16 -= 8`) and decrement the eight-limb counter (`x18`). -/
theorem evm_mulmod_reduce512_loop_fold_advance_spec_within
    (sp base ptr oldX17 oldX15 x19v x20v x18v limb : Word) (r n : EvmWord) :
    cpsTripleWithin (2 + 64 * 64 + 2) base (base + 272)
      (CodeReq.ofProg base evm_mulmod_reduce512_loop)
      ((.x12 ↦ᵣ sp) ** (.x16 ↦ᵣ ptr) ** (.x17 ↦ᵣ oldX17) ** (.x15 ↦ᵣ oldX15) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ x19v) ** (.x20 ↦ᵣ x20v) ** (.x18 ↦ᵣ x18v) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
       ((sp + signExtend12 (224 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
       ((sp + signExtend12 (232 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
       ((sp + signExtend12 (240 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
       ((sp + signExtend12 (248 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3) **
       ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limb))
      (mulModReduceBitLoopPost sp (mulModReduceStepN r n limb 64) n **
       (.x16 ↦ᵣ (ptr + signExtend12 (4088 : BitVec 12))) **
       (.x18 ↦ᵣ (x18v + signExtend12 (4095 : BitVec 12))) **
       ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limb)) := by
  have hfoldf := cpsTripleWithin_frameR ((.x18 ↦ᵣ x18v)) (by pcFree)
    (evm_mulmod_reduce512_loop_fold_one_limb_spec_within
      sp base ptr oldX17 oldX15 x19v x20v limb r n)
  have hadvf := cpsTripleWithin_frameR
    (mulModReduceBitLoopPost sp (mulModReduceStepN r n limb 64) n **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limb))
    (by unfold mulModReduceBitLoopPost mulModReduceCompareMem; pcFree)
    (evm_mulmod_reduce512_loop_advance_spec_within base ptr x18v)
  rw [show (base + 8 + 256 : Word) = base + 264 from by bv_omega] at hfoldf
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hfoldf hadvf)

/-- Outer-loop control `BNE x18, x0, -272` at byte offset 272: loops back to
    `base` while the eight-limb counter `x18` is nonzero, falls through to
    `base + 276` (the post-loop) when it reaches zero. -/
theorem evm_mulmod_reduce512_loop_branch_spec_within (base x18v : Word) :
    cpsBranchWithin 1 (base + 272)
      (CodeReq.ofProg base evm_mulmod_reduce512_loop)
      ((.x18 ↦ᵣ x18v) ** (.x0 ↦ᵣ (0 : Word)))
      base ((.x18 ↦ᵣ x18v) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜x18v ≠ (0 : Word)⌝)
      (base + 276) ((.x18 ↦ᵣ x18v) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜x18v = (0 : Word)⌝) := by
  have hsub : ∀ a i,
      CodeReq.singleton (base + 272) (Instr.BNE .x18 .x0 (-272 : BitVec 13)) a = some i →
      (CodeReq.ofProg base evm_mulmod_reduce512_loop) a = some i := by
    rw [← CodeReq.ofProg_singleton]
    refine CodeReq.ofProg_mono_sub base (base + 272) evm_mulmod_reduce512_loop
      [Instr.BNE .x18 .x0 (-272 : BitVec 13)] 68 ?_ ?_ ?_ ?_
    · rw [show BitVec.ofNat 64 (4 * 68) = (272 : Word) by decide]
    · rfl
    · rw [evm_mulmod_reduce512_loop_length]; decide
    · rw [evm_mulmod_reduce512_loop_length]; decide
  have hbne := bne_spec_gen_within .x18 .x0 (-272 : BitVec 13) x18v (0 : Word) (base + 272)
  have htaken : ((base + 272) + signExtend13 (-272 : BitVec 13) : Word) = base := by
    rw [show signExtend13 (-272 : BitVec 13) = (-272 : Word) from by decide]; bv_omega
  have hnt : ((base + 272) + 4 : Word) = base + 276 := by bv_omega
  rw [htaken, hnt] at hbne
  exact cpsBranchWithin_extend_code (hmono := hsub) (h := hbne)

/-- One full outer-loop body iteration as a two-exit branch: fold the current
    product limb, advance the pointer/counter, then branch on the eight-limb
    counter — loop back to `base` while `x18` stays nonzero, fall through to
    `base + 276` when it reaches zero. -/
theorem evm_mulmod_reduce512_loop_body_spec_within
    (sp base ptr oldX17 oldX15 x19v x20v x18v limb : Word) (r n : EvmWord) :
    cpsBranchWithin (2 + 64 * 64 + 2 + 1) base
      (CodeReq.ofProg base evm_mulmod_reduce512_loop)
      ((.x12 ↦ᵣ sp) ** (.x16 ↦ᵣ ptr) ** (.x17 ↦ᵣ oldX17) ** (.x15 ↦ᵣ oldX15) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ x19v) ** (.x20 ↦ᵣ x20v) ** (.x18 ↦ᵣ x18v) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
       ((sp + signExtend12 (224 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
       ((sp + signExtend12 (232 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
       ((sp + signExtend12 (240 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
       ((sp + signExtend12 (248 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3) **
       ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limb))
      base
      (mulModReduceBitLoopPost sp (mulModReduceStepN r n limb 64) n **
       (.x16 ↦ᵣ (ptr + signExtend12 (4088 : BitVec 12))) **
       (.x18 ↦ᵣ (x18v + signExtend12 (4095 : BitVec 12))) **
       ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limb) **
       ⌜x18v + signExtend12 (4095 : BitVec 12) ≠ (0 : Word)⌝)
      (base + 276)
      (mulModReduceBitLoopPost sp (mulModReduceStepN r n limb 64) n **
       (.x16 ↦ᵣ (ptr + signExtend12 (4088 : BitVec 12))) **
       (.x18 ↦ᵣ (x18v + signExtend12 (4095 : BitVec 12))) **
       ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limb) **
       ⌜x18v + signExtend12 (4095 : BitVec 12) = (0 : Word)⌝) := by
  have hbnef := cpsBranchWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x15 ↦ᵣ (0 : Word)) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
     regOwn .x17 ** regOwn .x19 ** regOwn .x20 **
     mulModReduceCompareMem sp (mulModReduceStepN r n limb 64) n **
     (.x16 ↦ᵣ (ptr + signExtend12 (4088 : BitVec 12))) **
     ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ limb))
    (by unfold mulModReduceCompareMem; pcFree)
    (evm_mulmod_reduce512_loop_branch_spec_within base
      (x18v + signExtend12 (4095 : BitVec 12)))
  exact cpsBranchWithin_weaken (fun _ hp => hp)
    (fun h hp => by unfold mulModReduceBitLoopPost; xperm_hyp hp)
    (fun h hp => by unfold mulModReduceBitLoopPost; xperm_hyp hp)
    (cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun h hp => by unfold mulModReduceBitLoopPost at hp; xperm_hyp hp)
      (evm_mulmod_reduce512_loop_fold_advance_spec_within
        sp base ptr oldX17 oldX15 x19v x20v x18v limb r n)
      hbnef)

end EvmAsm.Evm64
