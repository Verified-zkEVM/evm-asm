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
