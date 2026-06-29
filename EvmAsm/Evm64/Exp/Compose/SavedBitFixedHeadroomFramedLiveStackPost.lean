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
