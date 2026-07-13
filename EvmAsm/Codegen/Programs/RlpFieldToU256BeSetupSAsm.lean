import EvmAsm.Codegen.Programs.RlpFieldToU256BeSAsm
import EvmAsm.Rv64.SAsm.SelectedRead

namespace EvmAsm.Codegen.RlpFieldToU256BeSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

abbrev Saved := EvmAsm.Codegen.RlpFieldToU64SAsm.Saved
abbrev frame := EvmAsm.Codegen.RlpFieldToU64SAsm.frame
abbrev savedVals := EvmAsm.Codegen.RlpFieldToU64SAsm.savedVals
abbrev savedFrame := EvmAsm.Codegen.RlpFieldToU64SAsm.savedFrame

theorem regsAt_frame (saved : Saved) :
    regsAt frame (savedVals saved) =
      ((.x1 ↦ᵣ saved.ra) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1)) :=
  EvmAsm.Codegen.RlpFieldToU64SAsm.regsAt_frame saved

theorem frameSlotsSaved_frame (newSp : Word) (saved : Saved) :
    frameSlotsSaved frame newSp (savedVals saved) = savedFrame newSp saved :=
  EvmAsm.Codegen.RlpFieldToU64SAsm.frameSlotsSaved_frame newSp saved

/-- Allocate K35's 32-byte frame and save `ra/s0/s1` (instructions 0--3). -/
theorem setupPrologue
    (sp0 newSp : Word) (saved : Saved) (F : Assertion)
    (hnewSp : newSp = sp0 + signExtend12 (-32 : BitVec 12)) (hF : F.pcFree) :
    cpsTripleWithin 4 B (B + 16) code
      ((.x2 ↦ᵣ sp0) ** regsAt frame (savedVals saved) **
       frameSlotsOwn frame newSp ** F)
      ((.x2 ↦ᵣ newSp) ** regsAt frame (savedVals saved) **
       savedFrame newSp saved ** F) := by
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-32 : BitVec 12) B (by decide)
  rw [← hnewSp] at ha0
  have ha := cpsTripleWithin_extend_code (cr' := code) (fun a i hi =>
    wrapperCode_mono a i (CodeReq.ofProg_mem_at B B rlpFieldToU256Be_prog 0
      (.ADDI .x2 .x2 (-32 : BitVec 12)) rfl (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide) a i hi)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt frame (savedVals saved) ** frameSlotsOwn frame newSp ** F)
    (pcFree_sepConj (pcFree_regsAt _ _)
      (pcFree_sepConj (pcFree_frameSlotsOwn _ _) hF)) ha
  have hs0 := storeSeq_spec frame newSp (savedVals saved) (B + 4) (by decide)
  have hs := cpsTripleWithin_extend_code (cr' := code) (fun a i hi =>
    wrapperCode_mono a i (CodeReq.ofProg_mono_sub B (B + 4)
      rlpFieldToU256Be_prog (storeProg frame) 1 (by bv_omega) (by rfl)
      (by rw [program_length]; change 1 + 3 ≤ 44; decide)
      (by rw [program_length]; decide) a i hi)) hs0
  rw [show B + 4 + BitVec.ofNat 64 (4 * frame.length) = B + 16 from by
    rw [show frame.length = 3 by decide]; bv_omega] at hs
  have hsF := cpsTripleWithin_frameR F hF hs
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    haF hsF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hp => by rw [frameSlotsSaved_frame] at hp; xperm_hyp hp) hseq

#print axioms setupPrologue

/-- Save the input/output pointers (instructions 4--5). -/
theorem setupMoves
    (listBase outputPtr old8 old9 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (B + 16) (B + 24) code
      (((.x8 ↦ᵣ old8) ** (.x9 ↦ᵣ old9) ** (.x10 ↦ᵣ listBase) **
       (.x13 ↦ᵣ outputPtr)) ** F)
      (((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outputPtr) **
       (.x10 ↦ᵣ listBase) ** (.x13 ↦ᵣ outputPtr)) ** F) := by
  have h0 := mv_spec_gen_within .x8 .x10 listBase old8 (B + 16) (by decide)
  have h0' := cpsTripleWithin_extend_code (cr' := code) (fun a i hi =>
    wrapperCode_mono a i (CodeReq.ofProg_mem_at B (B + 16)
      rlpFieldToU256Be_prog 4 (.MV .x8 .x10) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide) a i hi)) h0
  have h1 := mv_spec_gen_within .x9 .x13 outputPtr old9 (B + 20) (by decide)
  have h1' := cpsTripleWithin_extend_code (cr' := code) (fun a i hi =>
    wrapperCode_mono a i (CodeReq.ofProg_mem_at B (B + 20)
      rlpFieldToU256Be_prog 5 (.MV .x9 .x13) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide) a i hi)) h1
  have h0F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ old9) ** (.x13 ↦ᵣ outputPtr)) (by pcf) h0'
  have h1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ listBase)) (by pcf) h1'
  have hs := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_frameR F hF
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp) hs)

#print axioms setupMoves

private theorem getByteAt_dword0 (j : Nat) (hj : j < 8) :
    getByteAt (dwordBytes (0 : Word)) j = 0 := by
  have hd : dwordBytes (0 : Word) = List.replicate 8 (0 : BitVec 8) := by decide
  unfold getByteAt
  rw [hd, dif_pos (by simp; omega), List.getElem_replicate]

private theorem getElem_eq_getByteAt (l : List (BitVec 8)) (i : Nat)
    (h : i < l.length) : l[i] = getByteAt l i := by
  unfold getByteAt
  rw [dif_pos h]

theorem zeroFold (l : List (BitVec 8)) (hl : l.length = 32) :
    setBytes (setBytes (setBytes (setBytes l 0 (dwordBytes 0)) 8 (dwordBytes 0))
        16 (dwordBytes 0)) 24 (dwordBytes 0) =
      List.replicate 32 (0 : BitVec 8) := by
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 _
    have hi : i < 32 := by simpa [hl] using h1
    have g24 : 24 + (dwordBytes (0 : Word)).length ≤
        (setBytes (setBytes (setBytes l 0 (dwordBytes 0)) 8 (dwordBytes 0))
          16 (dwordBytes 0)).length := by simp [hl]
    have g16 : 16 + (dwordBytes (0 : Word)).length ≤
        (setBytes (setBytes l 0 (dwordBytes 0)) 8 (dwordBytes 0)).length := by
      simp [hl]
    have g8 : 8 + (dwordBytes (0 : Word)).length ≤
        (setBytes l 0 (dwordBytes 0)).length := by simp [hl]
    have g0 : (dwordBytes (0 : Word)).length ≤ l.length := by simp [hl]
    rw [getElem_eq_getByteAt _ _ h1, List.getElem_replicate,
      getByteAt_setBytes _ _ _ _ g24, getByteAt_setBytes _ _ _ _ g16,
      getByteAt_setBytes _ _ _ _ g8, getByteAt_setBytes _ _ _ _ g0]
    simp only [length_dwordBytes]
    by_cases c24 : 24 ≤ i ∧ i < 32
    · rw [if_pos c24, getByteAt_dword0 _ (by omega)]
    · rw [if_neg c24]
      by_cases c16 : 16 ≤ i ∧ i < 24
      · rw [if_pos c16, getByteAt_dword0 _ (by omega)]
      · rw [if_neg c16]
        by_cases c8 : 8 ≤ i ∧ i < 16
        · rw [if_pos c8, getByteAt_dword0 _ (by omega)]
        · rw [if_neg c8, if_pos (by omega), getByteAt_dword0 _ (by omega)]

/-- Four emitted stores zero the complete 32-byte output window (6--9). -/
theorem zeroOutput (outputPtr : Word) (orig : List (BitVec 8))
    (hlen : orig.length = 32) :
    cpsTripleWithin 4 (B + 24) (B + 40) code
      ((.x9 ↦ᵣ outputPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion outputPtr orig)
      ((.x9 ↦ᵣ outputPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion outputPtr (List.replicate 32 0)) := by
  let b0 := setBytes orig 0 (dwordBytes (0 : Word))
  let b1 := setBytes b0 8 (dwordBytes (0 : Word))
  let b2 := setBytes b1 16 (dwordBytes (0 : Word))
  let b3 := setBytes b2 24 (dwordBytes (0 : Word))
  have hs (q : Nat) (bs : List (BitVec 8)) (hbs : bs.length = 32)
      (hq : q < 4) : cpsTripleWithin 1 (B + 24 + BitVec.ofNat 64 (4 * q))
        (B + 24 + BitVec.ofNat 64 (4 * (q + 1))) code
        ((.x9 ↦ᵣ outputPtr) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion outputPtr bs)
        ((.x9 ↦ᵣ outputPtr) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion outputPtr (setBytes bs (8 * q) (dwordBytes 0))) := by
    have h0 := bytesRegion_sd_within .x9 .x0 outputPtr (0 : Word)
      (B + 24 + BitVec.ofNat 64 (4 * q)) bs q (by rw [hbs]; omega) (by omega)
    rw [show B + 24 + BitVec.ofNat 64 (4 * q) + 4 =
        B + 24 + BitVec.ofNat 64 (4 * (q + 1)) from by bv_omega] at h0
    exact cpsTripleWithin_extend_code (fun a i hi => wrapperCode_mono a i
      (CodeReq.ofProg_mem_at B (B + 24 + BitVec.ofNat 64 (4 * q))
        rlpFieldToU256Be_prog (6 + q)
        (.SD .x9 .x0 (BitVec.ofNat 12 (8 * q))) (by bv_omega)
        (by rw [program_length]; omega) (by interval_cases q <;> rfl)
        (by rw [program_length]; omega) a i hi)) h0
  have h0 := hs 0 orig hlen (by omega)
  have h1 := hs 1 b0 (by unfold b0; simp [hlen]) (by omega)
  have h2 := hs 2 b1 (by unfold b1 b0; simp [hlen]) (by omega)
  have h3 := hs 3 b2 (by unfold b2 b1 b0; simp [hlen]) (by omega)
  have h01 := cpsTripleWithin_seq_same_cr h0 h1
  have h012 := cpsTripleWithin_seq_same_cr h01 h2
  have h0123 := cpsTripleWithin_seq_same_cr h012 h3
  unfold b3 b2 b1 b0 at *
  rw [zeroFold orig hlen] at h0123
  simpa using h0123

#print axioms zeroOutput

end EvmAsm.Codegen.RlpFieldToU256BeSAsm
