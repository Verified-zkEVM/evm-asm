/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedHeadroomFramedLiveStackPost

  Framed live-stack post surface for the verified fixed-headroom EXP loop.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedHeadroomFullLoop

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expHeadroomFinalOwnedBaseFrame
    (sp evmSp : Word) (baseWord exponentWord scratchWord : EvmWord) : Assertion :=
  ((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
    ((.x2 ↦ᵣ sp) **
     (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
     evmWordIs sp (EvmWord.exp baseWord exponentWord) **
     evmWordOwn evmSp) **
    expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
      (EvmWord.exp baseWord exponentWord)

theorem expHeadroomFinalOwnedBaseFrame_unfold
    {sp evmSp : Word} {baseWord exponentWord scratchWord : EvmWord} :
    expHeadroomFinalOwnedBaseFrame sp evmSp baseWord exponentWord scratchWord =
      (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x2 ↦ᵣ sp) **
         (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
         evmWordIs sp (EvmWord.exp baseWord exponentWord) **
         evmWordOwn evmSp) **
        expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
          (EvmWord.exp baseWord exponentWord)) := by
  delta expHeadroomFinalOwnedBaseFrame
  rfl

theorem expHeadroomFinalOwnedBaseFrame_pcFree
    {sp evmSp : Word} {baseWord exponentWord scratchWord : EvmWord} :
    (expHeadroomFinalOwnedBaseFrame sp evmSp baseWord exponentWord scratchWord).pcFree := by
  rw [expHeadroomFinalOwnedBaseFrame_unfold]
  pcFree

instance pcFreeInst_expHeadroomFinalOwnedBaseFrame
    (sp evmSp : Word) (baseWord exponentWord scratchWord : EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalOwnedBaseFrame sp evmSp baseWord exponentWord scratchWord) :=
  ⟨expHeadroomFinalOwnedBaseFrame_pcFree⟩

@[irreducible]
def expHeadroomFinalFramedLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  fun ps => ∃ (scratchWord : EvmWord),
    (((.x12 ↦ᵣ (evmSp + 32)) **
      evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
      expHeadroomFinalOwnedBaseFrame sp evmSp baseWord exponentWord scratchWord) ps

theorem expHeadroomFinalFramedLiveStackPost_unfold
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expHeadroomFinalFramedLiveStackPost sp evmSp baseWord exponentWord rest =
      (fun ps => ∃ (scratchWord : EvmWord),
        (((.x12 ↦ᵣ (evmSp + 32)) **
          evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
          expHeadroomFinalOwnedBaseFrame sp evmSp baseWord exponentWord scratchWord) ps) := by
  delta expHeadroomFinalFramedLiveStackPost
  rfl

theorem expHeadroomFinalFramedLiveStackPost_pcFree
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    (expHeadroomFinalFramedLiveStackPost sp evmSp baseWord exponentWord rest).pcFree := by
  intro ps h_post
  rw [expHeadroomFinalFramedLiveStackPost_unfold] at h_post
  obtain ⟨scratchWord, h_post⟩ := h_post
  have hVisible : (((.x12 ↦ᵣ (evmSp + 32)) **
      evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)).pcFree) := by
    pcFree
  exact (pcFree_sepConj hVisible expHeadroomFinalOwnedBaseFrame_pcFree) ps h_post

instance pcFreeInst_expHeadroomFinalFramedLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalFramedLiveStackPost sp evmSp baseWord exponentWord rest) :=
  ⟨expHeadroomFinalFramedLiveStackPost_pcFree⟩

@[irreducible]
def expHeadroomFinalOwnedScratchFrame
    (sp evmSp : Word) (baseWord exponentWord scratchWord : EvmWord) : Assertion :=
  ((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
    ((.x2 ↦ᵣ sp) **
     (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
     evmWordOwn sp **
     evmWordOwn evmSp) **
    expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
      (EvmWord.exp baseWord exponentWord)

theorem expHeadroomFinalOwnedScratchFrame_unfold
    {sp evmSp : Word} {baseWord exponentWord scratchWord : EvmWord} :
    expHeadroomFinalOwnedScratchFrame sp evmSp baseWord exponentWord scratchWord =
      (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x2 ↦ᵣ sp) **
         (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
         evmWordOwn sp **
         evmWordOwn evmSp) **
        expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
          (EvmWord.exp baseWord exponentWord)) := by
  delta expHeadroomFinalOwnedScratchFrame
  rfl

theorem expHeadroomFinalOwnedScratchFrame_pcFree
    {sp evmSp : Word} {baseWord exponentWord scratchWord : EvmWord} :
    (expHeadroomFinalOwnedScratchFrame sp evmSp baseWord exponentWord scratchWord).pcFree := by
  rw [expHeadroomFinalOwnedScratchFrame_unfold]
  pcFree

instance pcFreeInst_expHeadroomFinalOwnedScratchFrame
    (sp evmSp : Word) (baseWord exponentWord scratchWord : EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalOwnedScratchFrame sp evmSp baseWord exponentWord scratchWord) :=
  ⟨expHeadroomFinalOwnedScratchFrame_pcFree⟩

@[irreducible]
def expHeadroomFinalOwnedScratchLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  fun ps => ∃ (scratchWord : EvmWord),
    (((.x12 ↦ᵣ (evmSp + 32)) **
      evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
      expHeadroomFinalOwnedScratchFrame sp evmSp baseWord exponentWord scratchWord) ps

theorem expHeadroomFinalOwnedScratchLiveStackPost_unfold
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expHeadroomFinalOwnedScratchLiveStackPost sp evmSp baseWord exponentWord rest =
      (fun ps => ∃ (scratchWord : EvmWord),
        (((.x12 ↦ᵣ (evmSp + 32)) **
          evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
          expHeadroomFinalOwnedScratchFrame sp evmSp baseWord exponentWord scratchWord) ps) := by
  delta expHeadroomFinalOwnedScratchLiveStackPost
  rfl

theorem expHeadroomFinalOwnedScratchLiveStackPost_pcFree
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    (expHeadroomFinalOwnedScratchLiveStackPost sp evmSp baseWord exponentWord rest).pcFree := by
  intro ps h_post
  rw [expHeadroomFinalOwnedScratchLiveStackPost_unfold] at h_post
  obtain ⟨scratchWord, h_post⟩ := h_post
  have hVisible : (((.x12 ↦ᵣ (evmSp + 32)) **
      evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)).pcFree) := by
    pcFree
  exact (pcFree_sepConj hVisible expHeadroomFinalOwnedScratchFrame_pcFree) ps h_post

instance pcFreeInst_expHeadroomFinalOwnedScratchLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalOwnedScratchLiveStackPost sp evmSp baseWord exponentWord rest) :=
  ⟨expHeadroomFinalOwnedScratchLiveStackPost_pcFree⟩

@[irreducible]
def expHeadroomFinalOwnedLoopExtraFrame
    (evmSp : Word) : Assertion :=
  (evmWordOwn (evmSp + signExtend12 ((-128) : BitVec 12)) **
    evmWordOwn (evmSp + signExtend12 ((-96) : BitVec 12)) **
    evmWordOwn (evmSp + signExtend12 ((-64) : BitVec 12)) **
    evmWordOwn (evmSp + signExtend12 ((-32) : BitVec 12))) **
    (regOwn .x19 ** regOwn .x20 ** regOwn .x18 ** regOwn .x16 **
     regOwn .x1 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11)

theorem expHeadroomFinalOwnedLoopExtraFrame_unfold
    (evmSp : Word) :
    expHeadroomFinalOwnedLoopExtraFrame evmSp =
      ((evmWordOwn (evmSp + signExtend12 ((-128) : BitVec 12)) **
        evmWordOwn (evmSp + signExtend12 ((-96) : BitVec 12)) **
        evmWordOwn (evmSp + signExtend12 ((-64) : BitVec 12)) **
        evmWordOwn (evmSp + signExtend12 ((-32) : BitVec 12))) **
        (regOwn .x19 ** regOwn .x20 ** regOwn .x18 ** regOwn .x16 **
         regOwn .x1 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11)) := by
  delta expHeadroomFinalOwnedLoopExtraFrame
  rfl

theorem expHeadroomFinalOwnedLoopExtraFrame_pcFree
    (evmSp : Word) :
    (expHeadroomFinalOwnedLoopExtraFrame evmSp).pcFree := by
  rw [expHeadroomFinalOwnedLoopExtraFrame_unfold]
  pcFree

instance pcFreeInst_expHeadroomFinalOwnedLoopExtraFrame
    (evmSp : Word) :
    Assertion.PCFree (expHeadroomFinalOwnedLoopExtraFrame evmSp) :=
  ⟨expHeadroomFinalOwnedLoopExtraFrame_pcFree evmSp⟩

@[irreducible]
def expHeadroomFinalOwnedLeftoverFrame
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) : Assertion :=
  ((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
    ((.x2 ↦ᵣ sp) **
     (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
     evmWordOwn sp **
     evmWordOwn evmSp) **
    expHeadroomFinalOwnedLoopExtraFrame evmSp

theorem expHeadroomFinalOwnedLeftoverFrame_unfold
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) :
    expHeadroomFinalOwnedLeftoverFrame sp evmSp baseWord exponentWord =
      (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x2 ↦ᵣ sp) **
         (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
         evmWordOwn sp **
         evmWordOwn evmSp) **
        expHeadroomFinalOwnedLoopExtraFrame evmSp) := by
  delta expHeadroomFinalOwnedLeftoverFrame
  rfl

theorem expHeadroomFinalOwnedLeftoverFrame_pcFree
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) :
    (expHeadroomFinalOwnedLeftoverFrame sp evmSp baseWord exponentWord).pcFree := by
  rw [expHeadroomFinalOwnedLeftoverFrame_unfold]
  pcFree

instance pcFreeInst_expHeadroomFinalOwnedLeftoverFrame
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalOwnedLeftoverFrame sp evmSp baseWord exponentWord) :=
  ⟨expHeadroomFinalOwnedLeftoverFrame_pcFree sp evmSp baseWord exponentWord⟩

@[irreducible]
def expHeadroomFinalOwnedLeftoverLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion :=
  (((.x12 ↦ᵣ (evmSp + 32)) **
    evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
    expHeadroomFinalOwnedLeftoverFrame sp evmSp baseWord exponentWord)

theorem expHeadroomFinalOwnedLeftoverLiveStackPost_unfold
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    expHeadroomFinalOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest =
      ((((.x12 ↦ᵣ (evmSp + 32)) **
        evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
        expHeadroomFinalOwnedLeftoverFrame sp evmSp baseWord exponentWord)) := by
  delta expHeadroomFinalOwnedLeftoverLiveStackPost
  rfl

theorem expHeadroomFinalOwnedLeftoverLiveStackPost_pcFree
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    (expHeadroomFinalOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest).pcFree := by
  rw [expHeadroomFinalOwnedLeftoverLiveStackPost_unfold]
  pcFree

instance pcFreeInst_expHeadroomFinalOwnedLeftoverLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest) :=
  ⟨expHeadroomFinalOwnedLeftoverLiveStackPost_pcFree sp evmSp baseWord exponentWord rest⟩

private theorem expHeadroomFinalOwnedBaseFrame_to_ownedScratchFrame
    {sp evmSp : Word} {baseWord exponentWord scratchWord : EvmWord} {ps : PartialState}
    (h : expHeadroomFinalOwnedBaseFrame sp evmSp baseWord exponentWord scratchWord ps) :
    expHeadroomFinalOwnedScratchFrame sp evmSp baseWord exponentWord scratchWord ps := by
  rw [expHeadroomFinalOwnedBaseFrame_unfold] at h
  rw [expHeadroomFinalOwnedScratchFrame_unfold]
  exact sepConj_mono (fun _ h => h)
    (sepConj_mono
      (sepConj_mono (fun _ h => h)
        (sepConj_mono (fun _ h => h)
          (sepConj_mono (fun _ h => evmWordIs_to_evmWordOwn h) (fun _ h => h))))
      (fun _ h => h)) _ h

theorem expHeadroomFinalFramedLiveStackPost_to_ownedScratchLiveStackPost
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h : expHeadroomFinalFramedLiveStackPost sp evmSp baseWord exponentWord rest ps) :
    expHeadroomFinalOwnedScratchLiveStackPost sp evmSp baseWord exponentWord rest ps := by
  rw [expHeadroomFinalFramedLiveStackPost_unfold] at h
  obtain ⟨scratchWord, h⟩ := h
  rw [expHeadroomFinalOwnedScratchLiveStackPost_unfold]
  refine ⟨scratchWord, ?_⟩
  exact sepConj_mono (fun _ h => h)
    (fun _ h_frame => expHeadroomFinalOwnedBaseFrame_to_ownedScratchFrame h_frame) _ h


private theorem expHeadroomFinalLoopExtraFrame_to_ownedLoopExtraFrame
    {evmSp : Word} {baseWord exponentWord scratchWord resultWord : EvmWord}
    {ps : PartialState}
    (h :
      expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
        resultWord ps) :
    expHeadroomFinalOwnedLoopExtraFrame evmSp ps := by
  rw [expHeadroomFinalLoopExtraFrame_unfold] at h
  rw [expHeadroomFinalOwnedLoopExtraFrame_unfold]
  rw [evmStackIs_cons, evmStackIs_cons, evmStackIs_cons, evmStackIs_cons,
    evmStackIs_nil] at h
  simp only [sepConj_emp_right'] at h
  rw [show (evmSp + signExtend12 ((-128) : BitVec 12) + 32 : Word) =
      evmSp + signExtend12 ((-96) : BitVec 12) from by
        rw [show (signExtend12 ((-128) : BitVec 12) : Word) =
            18446744073709551488 from by decide,
          show (signExtend12 ((-96) : BitVec 12) : Word) =
            18446744073709551520 from by decide]
        bv_omega] at h
  rw [show (evmSp + signExtend12 ((-96) : BitVec 12) + 32 : Word) =
      evmSp + signExtend12 ((-64) : BitVec 12) from by
        rw [show (signExtend12 ((-96) : BitVec 12) : Word) =
            18446744073709551520 from by decide,
          EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64]
        bv_omega] at h
  rw [show (evmSp + signExtend12 ((-64) : BitVec 12) + 32 : Word) =
      evmSp + signExtend12 ((-32) : BitVec 12) from by
        rw [EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
          EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg32]
        bv_omega] at h
  exact sepConj_mono
    (sepConj_mono (fun _ h => evmWordIs_to_evmWordOwn h)
      (sepConj_mono (fun _ h => evmWordIs_to_evmWordOwn h)
        (sepConj_mono (fun _ h => evmWordIs_to_evmWordOwn h)
          (fun _ h => evmWordIs_to_evmWordOwn h))))
    (fun _ h_regs => h_regs) _ h

private theorem expHeadroomFinalOwnedScratchFrame_to_ownedLeftoverFrame
    {sp evmSp : Word} {baseWord exponentWord scratchWord : EvmWord}
    {ps : PartialState}
    (h :
      expHeadroomFinalOwnedScratchFrame sp evmSp baseWord exponentWord scratchWord
        ps) :
    expHeadroomFinalOwnedLeftoverFrame sp evmSp baseWord exponentWord ps := by
  rw [expHeadroomFinalOwnedScratchFrame_unfold] at h
  rw [expHeadroomFinalOwnedLeftoverFrame_unfold]
  exact sepConj_mono (fun _ h => h)
    (sepConj_mono (fun _ h => h)
      (fun _ h_frame => expHeadroomFinalLoopExtraFrame_to_ownedLoopExtraFrame h_frame)) _ h

theorem expHeadroomFinalOwnedScratchLiveStackPost_to_ownedLeftoverLiveStackPost
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h :
      expHeadroomFinalOwnedScratchLiveStackPost sp evmSp baseWord exponentWord rest
        ps) :
    expHeadroomFinalOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest
        ps := by
  rw [expHeadroomFinalOwnedScratchLiveStackPost_unfold] at h
  obtain ⟨scratchWord, h⟩ := h
  rw [expHeadroomFinalOwnedLeftoverLiveStackPost_unfold]
  exact sepConj_mono (fun _ h => h)
    (fun _ h_frame => expHeadroomFinalOwnedScratchFrame_to_ownedLeftoverFrame h_frame) _ h


theorem expHeadroomFinalCleanOwnedBaseLiveStackPost_to_framedLiveStackPost
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h : expHeadroomFinalCleanOwnedBaseLiveStackPost sp evmSp baseWord exponentWord rest ps) :
    expHeadroomFinalFramedLiveStackPost sp evmSp baseWord exponentWord rest ps := by
  rw [expHeadroomFinalCleanOwnedBaseLiveStackPost_unfold] at h
  obtain ⟨scratchWord, h⟩ := h
  rw [expHeadroomFinalFramedLiveStackPost_unfold]
  refine ⟨scratchWord, ?_⟩
  rw [expHeadroomFinalOwnedBaseFrame_unfold]
  xperm_hyp h


end EvmAsm.Evm64.Exp.Compose
