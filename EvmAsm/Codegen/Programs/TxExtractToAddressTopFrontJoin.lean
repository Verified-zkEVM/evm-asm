/-
  Bridge front AfterSave post into MidJoin AfterSave pre (midOwned).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontWalkInit
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontWalkInitLong
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidJoin
import EvmAsm.Codegen.Programs.TxExtractToAddressTopTypeBranch
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (extractToBufOwn)
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)

/-- walkFrameAmbient ≡ midOwned with s7 = s.s7. -/
theorem walkFrame_to_midOwned
    (spC : Word) (s : ExtractSaved) (toBuf isCreationPtr : Word) :
    ∀ h, walkFrameAmbient spC s toBuf isCreationPtr h →
      midOwned spC s toBuf isCreationPtr s.s7 h := by
  intro h hp
  simp only [walkFrameAmbient, midOwned, joinStackAmbient, extractToBufOwn] at hp ⊢
  xperm_hyp hp

/-- extractAfterSavePost → afterSaveFrameTy ** x20 ** regOwn x5 ** x0. -/
theorem afterSave_to_midJoinCore
    (txBase lenW typeW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) :
    ∀ h, extractAfterSavePost txBase lenW typeW innerW cursor endPtr txBytes h →
      (afterSaveFrameTy txBase lenW typeW innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ typeW) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word))) h := by
  intro h hp
  simp only [extractAfterSavePost, walkInitAmbient, walkInitRest,
    afterSaveFrameTy] at hp ⊢
  xperm_hyp hp

/-- frontAfterSavePost → MidJoin AfterSave pre (∃ cursor,end). -/
theorem frontAfterSave_to_midJoinPre
    (spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8)) :
    ∀ h, frontAfterSavePost spC s txBase lenW toBuf isCreationPtr txBytes h →
      ∃ cursor endPtr : Word,
        (afterSaveFrameTy txBase lenW
            (teerTxTypeDispatch txBytes).2.1
            (teerTxTypeDispatch txBytes).2.2
            cursor endPtr txBytes **
          (.x20 ↦ᵣ (teerTxTypeDispatch txBytes).2.1) **
          regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
          midOwned spC s toBuf isCreationPtr s.s7) h := by
  intro h hp
  simp only [frontAfterSavePost] at hp
  obtain ⟨cursor, endPtr, hpair⟩ := hp
  obtain ⟨h1, h2, hd, hu, hW, hAS⟩ := hpair
  have hM := walkFrame_to_midOwned spC s toBuf isCreationPtr h1 hW
  have hC := afterSave_to_midJoinCore txBase lenW
    (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2
    cursor endPtr txBytes h2 hAS
  have hnest :
      ((afterSaveFrameTy txBase lenW
          (teerTxTypeDispatch txBytes).2.1
          (teerTxTypeDispatch txBytes).2.2
          cursor endPtr txBytes **
        (.x20 ↦ᵣ (teerTxTypeDispatch txBytes).2.1) **
        regOwn .x5 ** (.x0 ↦ᵣ (0 : Word))) **
      midOwned spC s toBuf isCreationPtr s.s7) h :=
    ⟨h2, h1, hd.symm,
      by rw [PartialState.union_comm_of_disjoint hd.symm, hu],
      hC, hM⟩
  refine ⟨cursor, endPtr, ?_⟩
  xperm_hyp hnest

/-- Concrete short AfterSave → MidJoin pre at shortWalkCursor/End (no ∃). -/
theorem frontAfterSavePostShort_to_midJoinPre
    (spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8)) :
    ∀ h, frontAfterSavePostShort spC s txBase lenW toBuf isCreationPtr txBytes h →
      (afterSaveFrameTy txBase lenW
          (teerTxTypeDispatch txBytes).2.1
          (teerTxTypeDispatch txBytes).2.2
          (shortWalkCursor txBase (teerTxTypeDispatch txBytes).2.2.toNat)
          (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
            (teerTxTypeDispatch txBytes).2.2.toNat)
          txBytes **
        (.x20 ↦ᵣ (teerTxTypeDispatch txBytes).2.1) **
        regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s.s7) h := by
  intro h hp
  simp only [frontAfterSavePostShort] at hp
  obtain ⟨h1, h2, hd, hu, hW, hAS⟩ := hp
  have hM := walkFrame_to_midOwned spC s toBuf isCreationPtr h1 hW
  have hC := afterSave_to_midJoinCore txBase lenW
    (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2
    (shortWalkCursor txBase (teerTxTypeDispatch txBytes).2.2.toNat)
    (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
      (teerTxTypeDispatch txBytes).2.2.toNat)
    txBytes h2 hAS
  have hnest :
      ((afterSaveFrameTy txBase lenW
          (teerTxTypeDispatch txBytes).2.1
          (teerTxTypeDispatch txBytes).2.2
          (shortWalkCursor txBase (teerTxTypeDispatch txBytes).2.2.toNat)
          (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
            (teerTxTypeDispatch txBytes).2.2.toNat)
          txBytes **
        (.x20 ↦ᵣ (teerTxTypeDispatch txBytes).2.1) **
        regOwn .x5 ** (.x0 ↦ᵣ (0 : Word))) **
      midOwned spC s toBuf isCreationPtr s.s7) h :=
    ⟨h2, h1, hd.symm,
      by rw [PartialState.union_comm_of_disjoint hd.symm, hu],
      hC, hM⟩
  xperm_hyp hnest

#print axioms walkFrame_to_midOwned
#print axioms afterSave_to_midJoinCore
#print axioms frontAfterSave_to_midJoinPre
#print axioms frontAfterSavePostShort_to_midJoinPre

/-- Concrete long AfterSave → MidJoin pre at longWalkCursor/End (no ∃). -/
theorem frontAfterSavePostLong_to_midJoinPre
    (spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
    (hoff : (teerTxTypeDispatch txBytes).2.2.toNat < txBytes.length) :
    ∀ h, frontAfterSavePostLong spC s txBase lenW toBuf isCreationPtr txBytes hoff h →
      (afterSaveFrameTy txBase lenW
          (teerTxTypeDispatch txBytes).2.1
          (teerTxTypeDispatch txBytes).2.2
          (longWalkCursor txBase txBytes
            (teerTxTypeDispatch txBytes).2.2.toNat hoff)
          (longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
            (teerTxTypeDispatch txBytes).2.2.toNat)
          txBytes **
        (.x20 ↦ᵣ (teerTxTypeDispatch txBytes).2.1) **
        regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s.s7) h := by
  intro h hp
  simp only [frontAfterSavePostLong] at hp
  obtain ⟨h1, h2, hd, hu, hW, hAS⟩ := hp
  have hM := walkFrame_to_midOwned spC s toBuf isCreationPtr h1 hW
  have hC := afterSave_to_midJoinCore txBase lenW
    (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2
    (longWalkCursor txBase txBytes
      (teerTxTypeDispatch txBytes).2.2.toNat hoff)
    (longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
      (teerTxTypeDispatch txBytes).2.2.toNat)
    txBytes h2 hAS
  have hnest :
      ((afterSaveFrameTy txBase lenW
          (teerTxTypeDispatch txBytes).2.1
          (teerTxTypeDispatch txBytes).2.2
          (longWalkCursor txBase txBytes
            (teerTxTypeDispatch txBytes).2.2.toNat hoff)
          (longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
            (teerTxTypeDispatch txBytes).2.2.toNat)
          txBytes **
        (.x20 ↦ᵣ (teerTxTypeDispatch txBytes).2.1) **
        regOwn .x5 ** (.x0 ↦ᵣ (0 : Word))) **
      midOwned spC s toBuf isCreationPtr s.s7) h :=
    ⟨h2, h1, hd.symm,
      by rw [PartialState.union_comm_of_disjoint hd.symm, hu],
      hC, hM⟩
  xperm_hyp hnest

#print axioms frontAfterSavePostLong_to_midJoinPre

end EvmAsm.Codegen.TxExtractToAddressSpec
