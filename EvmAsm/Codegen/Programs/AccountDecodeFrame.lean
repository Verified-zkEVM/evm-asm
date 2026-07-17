/-
  The ABI frame blocks of `accountDecode_prog` (`Programs/State.lean`, PR-K27):

    * `adPrologue`  — instructions [0]-[13] (`AB → AB+56`): `addi sp,-64`, the
      seven callee-saved stores (`x1/x8/x9/x18/x19/x20/x21`), and the six `mv`
      shuffles copying the caller arguments `a0..a5` into the saved registers
      `s0..s5` (`x8/x9/x18/x19/x20/x21`).
    * `adEpilogue` — instructions [127]-[135] (`AB+508 → ra`): the seven
      register reloads, `addi sp,+64`, and the `ret`.

  Both reuse K20's 7-slot `listNthFrame` (identical layout).  The prologue is
  the `storeSeq`/`setupMoves` pattern of `RlpListNthItemSAsm.wrapperPrologue`;
  the epilogue mirrors `RlpListNthItemSAsm.epilogueOwned`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeSpec
import EvmAsm.Codegen.Programs.RlpListNthItemCallSAsm
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm (Saved savedVals listNthFrame savedFrame
  regsAt_listNthFrame frameSlotsSaved_listNthFrame)

set_option maxRecDepth 8000 in
/-- The six `mv` shuffles [8]-[13] (`AB+32 → AB+56`): copy the caller arguments
    `a0..a5` (in `x10..x15`) into the saved registers `s0..s5`
    (`x8/x9/x18/x19/x20/x21`).  The source argument registers are unchanged. -/
theorem adShuffle (a0 a1 a2 a3 a4 a5 os0 os1 os2 os3 os4 os5 : Word) :
    cpsTripleWithin 6 (AB + 32) (AB + 56) fullCode
      (((.x8 : Reg) ↦ᵣ os0) ** ((.x10 : Reg) ↦ᵣ a0) **
       ((.x9 : Reg) ↦ᵣ os1) ** ((.x11 : Reg) ↦ᵣ a1) **
       ((.x18 : Reg) ↦ᵣ os2) ** ((.x12 : Reg) ↦ᵣ a2) **
       ((.x19 : Reg) ↦ᵣ os3) ** ((.x13 : Reg) ↦ᵣ a3) **
       ((.x20 : Reg) ↦ᵣ os4) ** ((.x14 : Reg) ↦ᵣ a4) **
       ((.x21 : Reg) ↦ᵣ os5) ** ((.x15 : Reg) ↦ᵣ a5))
      (((.x8 : Reg) ↦ᵣ a0) ** ((.x10 : Reg) ↦ᵣ a0) **
       ((.x9 : Reg) ↦ᵣ a1) ** ((.x11 : Reg) ↦ᵣ a1) **
       ((.x18 : Reg) ↦ᵣ a2) ** ((.x12 : Reg) ↦ᵣ a2) **
       ((.x19 : Reg) ↦ᵣ a3) ** ((.x13 : Reg) ↦ᵣ a3) **
       ((.x20 : Reg) ↦ᵣ a4) ** ((.x14 : Reg) ↦ᵣ a4) **
       ((.x21 : Reg) ↦ᵣ a5) ** ((.x15 : Reg) ↦ᵣ a5)) := by
  have h8 := mv_spec_gen_within .x8 .x10 a0 os0 (AB + 32) (by decide)
  have h9 := mv_spec_gen_within .x9 .x11 a1 os1 (AB + 36) (by decide)
  have h10 := mv_spec_gen_within .x18 .x12 a2 os2 (AB + 40) (by decide)
  have h11 := mv_spec_gen_within .x19 .x13 a3 os3 (AB + 44) (by decide)
  have h12 := mv_spec_gen_within .x20 .x14 a4 os4 (AB + 48) (by decide)
  have h13 := mv_spec_gen_within .x21 .x15 a5 os5 (AB + 52) (by decide)
  have l8 := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 32) accountDecode_prog 8 (.MV .x8 .x10)
        (by bv_omega) (by rw [ad_length]; norm_num) rfl (by rw [ad_length]; norm_num)) h8)
  have l9 := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 36) accountDecode_prog 9 (.MV .x9 .x11)
        (by bv_omega) (by rw [ad_length]; norm_num) rfl (by rw [ad_length]; norm_num)) h9)
  have l10 := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 40) accountDecode_prog 10 (.MV .x18 .x12)
        (by bv_omega) (by rw [ad_length]; norm_num) rfl (by rw [ad_length]; norm_num)) h10)
  have l11 := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 44) accountDecode_prog 11 (.MV .x19 .x13)
        (by bv_omega) (by rw [ad_length]; norm_num) rfl (by rw [ad_length]; norm_num)) h11)
  have l12 := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 48) accountDecode_prog 12 (.MV .x20 .x14)
        (by bv_omega) (by rw [ad_length]; norm_num) rfl (by rw [ad_length]; norm_num)) h12)
  have l13 := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 52) accountDecode_prog 13 (.MV .x21 .x15)
        (by bv_omega) (by rw [ad_length]; norm_num) rfl (by rw [ad_length]; norm_num)) h13)
  have s8 := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ os1) ** ((.x11 : Reg) ↦ᵣ a1) ** ((.x18 : Reg) ↦ᵣ os2) **
     ((.x12 : Reg) ↦ᵣ a2) ** ((.x19 : Reg) ↦ᵣ os3) ** ((.x13 : Reg) ↦ᵣ a3) **
     ((.x20 : Reg) ↦ᵣ os4) ** ((.x14 : Reg) ↦ᵣ a4) ** ((.x21 : Reg) ↦ᵣ os5) **
     ((.x15 : Reg) ↦ᵣ a5)) (by pcf) l8
  have s9 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ a0) ** ((.x10 : Reg) ↦ᵣ a0) ** ((.x18 : Reg) ↦ᵣ os2) **
     ((.x12 : Reg) ↦ᵣ a2) ** ((.x19 : Reg) ↦ᵣ os3) ** ((.x13 : Reg) ↦ᵣ a3) **
     ((.x20 : Reg) ↦ᵣ os4) ** ((.x14 : Reg) ↦ᵣ a4) ** ((.x21 : Reg) ↦ᵣ os5) **
     ((.x15 : Reg) ↦ᵣ a5)) (by pcf) l9
  have s10 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ a0) ** ((.x10 : Reg) ↦ᵣ a0) ** ((.x9 : Reg) ↦ᵣ a1) **
     ((.x11 : Reg) ↦ᵣ a1) ** ((.x19 : Reg) ↦ᵣ os3) ** ((.x13 : Reg) ↦ᵣ a3) **
     ((.x20 : Reg) ↦ᵣ os4) ** ((.x14 : Reg) ↦ᵣ a4) ** ((.x21 : Reg) ↦ᵣ os5) **
     ((.x15 : Reg) ↦ᵣ a5)) (by pcf) l10
  have s11 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ a0) ** ((.x10 : Reg) ↦ᵣ a0) ** ((.x9 : Reg) ↦ᵣ a1) **
     ((.x11 : Reg) ↦ᵣ a1) ** ((.x18 : Reg) ↦ᵣ a2) ** ((.x12 : Reg) ↦ᵣ a2) **
     ((.x20 : Reg) ↦ᵣ os4) ** ((.x14 : Reg) ↦ᵣ a4) ** ((.x21 : Reg) ↦ᵣ os5) **
     ((.x15 : Reg) ↦ᵣ a5)) (by pcf) l11
  have s12 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ a0) ** ((.x10 : Reg) ↦ᵣ a0) ** ((.x9 : Reg) ↦ᵣ a1) **
     ((.x11 : Reg) ↦ᵣ a1) ** ((.x18 : Reg) ↦ᵣ a2) ** ((.x12 : Reg) ↦ᵣ a2) **
     ((.x19 : Reg) ↦ᵣ a3) ** ((.x13 : Reg) ↦ᵣ a3) ** ((.x21 : Reg) ↦ᵣ os5) **
     ((.x15 : Reg) ↦ᵣ a5)) (by pcf) l12
  have s13 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ a0) ** ((.x10 : Reg) ↦ᵣ a0) ** ((.x9 : Reg) ↦ᵣ a1) **
     ((.x11 : Reg) ↦ᵣ a1) ** ((.x18 : Reg) ↦ᵣ a2) ** ((.x12 : Reg) ↦ᵣ a2) **
     ((.x19 : Reg) ↦ᵣ a3) ** ((.x13 : Reg) ↦ᵣ a3) ** ((.x20 : Reg) ↦ᵣ a4) **
     ((.x14 : Reg) ↦ᵣ a4)) (by pcf) l13
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s8 s9
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 s10
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 s11
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3 s12
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c4 s13
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c5

#print axioms adShuffle

set_option maxRecDepth 8000 in
/-- The ABI prologue [0]-[13] (`AB → AB+56`): `addi sp,-64`, save the seven
    callee-saved registers into their frame slots (`saved` holds their entry
    values), then shuffle the arguments `a0..a5` into `s0..s5`.  `x1` (the
    caller return) is untouched by the shuffle and left live for the epilogue's
    `ret`; the arguments remain live in `x10..x15`. -/
theorem adPrologue (sp0 newSp callerRa a0 a1 a2 a3 a4 a5 os0 os1 os2 os3 os4 os5 : Word)
    (hnewSp : newSp = sp0 + signExtend12 (-64 : BitVec 12)) :
    let saved : Saved :=
      { ra := callerRa, s0 := os0, s1 := os1, s2 := os2, s3 := os3, s4 := os4,
        s5 := os5 }
    cpsTripleWithin 14 AB (AB + 56) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt listNthFrame (savedVals saved) **
        frameSlotsOwn listNthFrame newSp **
        (((.x10 : Reg) ↦ᵣ a0) ** ((.x11 : Reg) ↦ᵣ a1) ** ((.x12 : Reg) ↦ᵣ a2) **
         ((.x13 : Reg) ↦ᵣ a3) ** ((.x14 : Reg) ↦ᵣ a4) ** ((.x15 : Reg) ↦ᵣ a5)))
      (((.x2 : Reg) ↦ᵣ newSp) ** ((.x1 : Reg) ↦ᵣ callerRa) **
       ((.x8 : Reg) ↦ᵣ a0) ** ((.x9 : Reg) ↦ᵣ a1) ** ((.x18 : Reg) ↦ᵣ a2) **
       ((.x19 : Reg) ↦ᵣ a3) ** ((.x20 : Reg) ↦ᵣ a4) ** ((.x21 : Reg) ↦ᵣ a5) **
       ((.x10 : Reg) ↦ᵣ a0) ** ((.x11 : Reg) ↦ᵣ a1) ** ((.x12 : Reg) ↦ᵣ a2) **
       ((.x13 : Reg) ↦ᵣ a3) ** ((.x14 : Reg) ↦ᵣ a4) ** ((.x15 : Reg) ↦ᵣ a5) **
       savedFrame newSp saved) := by
  intro saved
  -- [0] addi sp, sp, -64
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-64 : BitVec 12) AB (by decide)
  rw [← hnewSp] at ha0
  have ha := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB AB accountDecode_prog 0 (.ADDI .x2 .x2 (-64 : BitVec 12))
        rfl (by rw [ad_length]; norm_num) rfl (by rw [ad_length]; norm_num)) ha0)
  have haF := cpsTripleWithin_frameR
    (regsAt listNthFrame (savedVals saved) ** frameSlotsOwn listNthFrame newSp **
      (((.x10 : Reg) ↦ᵣ a0) ** ((.x11 : Reg) ↦ᵣ a1) ** ((.x12 : Reg) ↦ᵣ a2) **
       ((.x13 : Reg) ↦ᵣ a3) ** ((.x14 : Reg) ↦ᵣ a4) ** ((.x15 : Reg) ↦ᵣ a5)))
    (by pcf) ha
  -- [1]-[7] store the seven callee-saved registers
  have hs0 := storeSeq_spec listNthFrame newSp (savedVals saved) (AB + 4) (by decide)
  have hstoreMono : ∀ a i,
      CodeReq.ofProg (AB + 4) (storeProg listNthFrame) a = some i → fullCode a = some i := by
    intro a i hmem
    exact ad_mono a i (CodeReq.ofProg_mono_sub AB (AB + 4) accountDecode_prog
      (storeProg listNthFrame) 1 (by bv_omega) (by rfl)
      (by rw [ad_length]; simp [listNthFrame])
      (by rw [ad_length]; norm_num) a i hmem)
  have hs := cpsTripleWithin_extend_code hstoreMono hs0
  rw [show AB + 4 + BitVec.ofNat 64 (4 * listNthFrame.length) = AB + 32 from by
    simp [listNthFrame]; bv_omega] at hs
  rw [frameSlotsSaved_listNthFrame] at hs
  have hsF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ a0) ** ((.x11 : Reg) ↦ᵣ a1) ** ((.x12 : Reg) ↦ᵣ a2) **
     ((.x13 : Reg) ↦ᵣ a3) ** ((.x14 : Reg) ↦ᵣ a4) ** ((.x15 : Reg) ↦ᵣ a5))
    (by pcf) hs
  -- [8]-[13] shuffle a0..a5 into s0..s5
  have hsh := adShuffle a0 a1 a2 a3 a4 a5 os0 os1 os2 os3 os4 os5
  have hshF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ callerRa) ** ((.x2 : Reg) ↦ᵣ newSp) ** savedFrame newSp saved)
    (by unfold savedFrame; pcf) hsh
  -- Compose [0] ;; [1-7] ;; [8-13].
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) haF hsF
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_listNthFrame] at hp
    xperm_hyp hp) c1 hshF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c2

#print axioms adPrologue

set_option maxRecDepth 8000 in
/-- The ABI epilogue [127]-[135] (`AB+508 → saved.ra`): reload the seven
    callee-saved registers from their (untouched) frame slots, restore
    `sp := sp0`, and `ret`.  Generic over an arbitrary framed result `F`
    (which carries the already-set `a0` status).  Mirrors `epilogueOwned`. -/
theorem adEpilogue (sp0 newSp : Word) (saved : Saved)
    (F : Assertion) (hF : F.pcFree)
    (hnewSp : newSp = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin 9 (AB + 508) saved.ra fullCode
      (((.x2 ↦ᵣ newSp) ** regsOwnAt listNthFrame **
        savedFrame newSp saved) ** F)
      (((.x2 ↦ᵣ sp0) ** regsAt listNthFrame (savedVals saved) **
        savedFrame newSp saved) ** F) := by
  have hl0 := loadSeq_spec_own listNthFrame newSp (savedVals saved)
    (AB + 508) (by decide) (by decide)
  have hlMono : ∀ a i,
      CodeReq.ofProg (AB + 508) (loadProg listNthFrame) a = some i → fullCode a = some i := by
    intro a i hmem
    exact ad_mono a i (CodeReq.ofProg_mono_sub AB (AB + 508) accountDecode_prog
      (loadProg listNthFrame) 127 (by bv_omega) (by rfl)
      (by rw [ad_length]; simp [listNthFrame])
      (by rw [ad_length]; norm_num) a i hmem)
  have hl := cpsTripleWithin_extend_code hlMono hl0
  rw [show AB + 508 + BitVec.ofNat 64 (4 * listNthFrame.length) = AB + 536 from by
    simp [listNthFrame]; bv_omega] at hl
  rw [frameSlotsSaved_listNthFrame] at hl
  have hlF := cpsTripleWithin_frameR F hF hl
  have hd0 := addi_spec_gen_same_within .x2 newSp (64 : BitVec 12) (AB + 536)
    (by decide)
  rw [show newSp + signExtend12 (64 : BitVec 12) = sp0 from by
    rw [hnewSp]
    exact sext_frameRestore sp0 (-64 : BitVec 12) (64 : BitVec 12) (by decide)] at hd0
  have hd := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 536) accountDecode_prog 134
        (.ADDI .x2 .x2 (64 : BitVec 12)) (by bv_omega)
        (by rw [ad_length]; norm_num) rfl (by rw [ad_length]; norm_num)) hd0)
  have hdF := cpsTripleWithin_frameR
    (regsAt listNthFrame (savedVals saved) ** savedFrame newSp saved ** F)
    (by unfold savedFrame; pcf; assumption) hd
  have hr0 := EvmAsm.Evm64.ret_spec_within' (AB + 540) saved.ra
  rw [hret] at hr0
  have hr := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 540) accountDecode_prog 135
        (.JALR .x0 .x1 (0 : BitVec 12)) (by bv_omega)
        (by rw [ad_length]; norm_num) rfl (by rw [ad_length]; norm_num)) hr0)
  have hrF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ sp0) **
      (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
      (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
      (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) **
      savedFrame newSp saved) ** F) (by
        unfold savedFrame
        pcf
        assumption) hr
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlF hdF
  have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_listNthFrame] at hp
    xperm_hyp hp) h12 hrF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hp => by
    rw [regsAt_listNthFrame]
    xperm_hyp hp) h123

#print axioms adEpilogue

end EvmAsm.Codegen.AccountDecodeSpec
