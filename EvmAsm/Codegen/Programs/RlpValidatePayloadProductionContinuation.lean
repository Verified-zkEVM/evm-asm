/-
  End-to-end production continuation for `rlp_validate_payload`.

  The theorem in this file is conditional on a direct-JAL production decoder
  triple.  It composes the linked wrapper prefix, call, status dispatch and
  all return arms; it does not identify that premise with the retired offline
  `ValidateFuel` family.
-/

import EvmAsm.Codegen.Programs.RlpValidatePayloadProductionAdapter

namespace EvmAsm.Codegen.RlpValidatePayloadProductionAdapter

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.RecDecode

def productionSimpleExitRest
    (listBase listEnd : Word) (inputBytes frameBytes : List (BitVec 8)) : Assertion :=
  ((.x11 ↦ᵣ listEnd) ** (regOwn .x12 ** regOwn .x15 ** regOwn .x16) **
    productionItemsRest listBase Frame inputBytes frameBytes)

theorem productionSimpleExitRest_pcFree
    (listBase listEnd : Word) (inputBytes frameBytes : List (BitVec 8)) :
    (productionSimpleExitRest listBase listEnd inputBytes frameBytes).pcFree := by
  unfold productionSimpleExitRest
  repeat' apply pcFree_sepConj
  all_goals first
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact bytesRegion_pcFree _ _

set_option maxRecDepth 8000 in
theorem rlp_validate_payload_production_full_spec_within
    {cr calleeCode : CodeReq} {n : Nat}
    (sp old13 raVal listBase listEnd status : Word)
    (inputBytes frameBytes : List (BitVec 8))
    (hdisj : (CodeReq.singleton CallPC
      (.JAL .x1 itemsJalOff)).Disjoint calleeCode)
    (hcallerDisj : wrapperCode.Disjoint calleeCode)
    (hcode : ∀ a i, (wrapperCode.union calleeCode) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n Items RetPC calleeCode
      (((.x1 ↦ᵣ RetPC) **
        productionItemsPre listBase listEnd Frame inputBytes frameBytes))
      (((.x1 ↦ᵣ RetPC) **
        productionItemsPost listBase Frame status inputBytes frameBytes))) :
    cpsTripleWithin (7 + ((1 + n) + 12)) (V + 12)
      (raVal &&& ~~~(1 : Word)) cr
      (((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listEnd)) **
        productionEntryFrame sp old13 raVal listBase inputBytes frameBytes)
      (productionExitPost sp old13 raVal listBase listEnd status
        inputBytes frameBytes) := by
  let allCode := wrapperCode.union calleeCode
  have hwrap : ∀ a i, wrapperCode a = some i → allCode a = some i := by
    intro a i h
    exact CodeReq.union_mono_left a i h
  have hprefix0 := rlp_validate_payload_production_entry_prefix_spec_within
    sp old13 raVal listBase listEnd inputBytes frameBytes
  have hprefix := cpsNBranchWithin_extend_code hwrap hprefix0
  have hcall0 := rlp_validate_payload_items_call_post_spec_within
    (cr := allCode) (calleeCode := calleeCode) (n := n)
    (listBase := listBase) (listEnd := listEnd) (framePtr := Frame)
    (oldRa := raVal) (inputBytes := inputBytes) (frameBytes := frameBytes)
    (post := productionItemsPost listBase Frame status inputBytes frameBytes)
    (F := productionCallFrame sp old13 raVal)
    (productionCallFrame_pcFree sp old13 raVal) hdisj hcallerDisj
    (by intro a i h; exact h) hcallee
  have hcallPre : ∀ h,
      (productionItemsPre listBase listEnd Frame inputBytes frameBytes **
        productionEntrySavedFrame sp old13 raVal) h →
      (((.x1 ↦ᵣ raVal) **
        productionItemsPre listBase listEnd Frame inputBytes frameBytes) **
        productionCallFrame sp old13 raVal) h := by
    intro h hp
    dsimp [productionEntrySavedFrame, productionCallFrame] at hp ⊢
    xperm_hyp hp
  have hcallPost : ∀ h,
      ((((.x1 ↦ᵣ RetPC) **
          productionItemsPost listBase Frame status inputBytes frameBytes) **
        productionCallFrame sp old13 raVal) h) →
      (((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x2 ↦ᵣ sp) ** (.x1 ↦ᵣ RetPC) ** (.x13 ↦ᵣ Frame) **
          (memIs sp raVal) ** (memIs (sp + 8) old13)) **
        productionStatusRest listBase inputBytes frameBytes) h := by
    intro h hp
    dsimp [productionItemsPost, productionCallFrame,
      productionStatusRest] at hp ⊢
    xperm_hyp hp
  have hcall := cpsTripleWithin_weaken hcallPre hcallPost hcall0

  have hstatus0 := rlp_validate_payload_production_status_tails_spec_within
    sp old13 raVal status
  have hstatus1 := cpsNBranchWithin_extend_code hwrap hstatus0
  have hstatus := cpsNBranchWithin_frameR
    (productionStatusRest_pcFree listBase inputBytes frameBytes) hstatus1

  have hsucc0 : cpsTripleWithin 0 (raVal &&& ~~~(1 : Word))
      (raVal &&& ~~~(1 : Word)) CodeReq.empty
      (((.x10 ↦ᵣ status) ** (.x2 ↦ᵣ (sp + 32)) ** (.x1 ↦ᵣ raVal) **
        (.x13 ↦ᵣ old13) ** (.x0 ↦ᵣ (0 : Word)) ** (memIs sp raVal) **
        (memIs (sp + 8) old13)) ** pure (status = 0) **
        productionStatusRest listBase inputBytes frameBytes)
      (productionExitPost sp old13 raVal listBase listEnd status
        inputBytes frameBytes) := by
    apply cpsTripleWithin_refl
    intro h hp
    simp only [productionExitPost]
    right; right; left
    drop_pure hp
    dsimp [productionNonemptyExitPost, productionStatusRest] at hp ⊢
    xperm_hyp hp
  have hsucc0' : cpsTripleWithin 0 (raVal &&& ~~~(1 : Word))
      (raVal &&& ~~~(1 : Word)) CodeReq.empty
      (((((.x10 ↦ᵣ status) ** (.x2 ↦ᵣ (sp + 32)) ** (.x1 ↦ᵣ raVal) **
          (.x13 ↦ᵣ old13) ** (.x0 ↦ᵣ (0 : Word)) ** (memIs sp raVal) **
          (memIs (sp + 8) old13)) ** pure (status = 0)) **
        productionStatusRest listBase inputBytes frameBytes))
      (productionExitPost sp old13 raVal listBase listEnd status
        inputBytes frameBytes) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [sepConj_assoc'] at hp ⊢
        exact hp)
      (fun _ hp => hp) hsucc0
  have hsucc := cpsTripleWithin_extend_code (cr' := allCode)
    (by intro a i h; simp [CodeReq.empty] at h) hsucc0'
  have hsucc3 := cpsTripleWithin_mono_nSteps (show 0 ≤ 3 by omega) hsucc

  have hfailAt72Base : cpsTripleWithin 3 (V + 72)
      (raVal &&& ~~~(1 : Word)) wrapperCode
      (((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ (7 : Word)) ** (.x1 ↦ᵣ (V + 44)) **
          (.x13 ↦ᵣ Frame) ** (.x0 ↦ᵣ (0 : Word)) ** (memIs sp raVal) **
          (memIs (sp + 8) old13)))
      (((.x2 ↦ᵣ (sp + 32)) ** (.x10 ↦ᵣ (7 : Word)) ** (.x1 ↦ᵣ raVal) **
          (.x13 ↦ᵣ Frame) ** (.x0 ↦ᵣ (0 : Word)) ** (memIs sp raVal) **
          (memIs (sp + 8) old13))) := by
    have h2 := ld_spec_gen_within .x1 .x2 sp (V + 44) raVal
      (0 : BitVec 12) (V + 72) (by decide)
    have h3 := addi_spec_gen_same_within .x2 sp (32 : BitVec 12)
      (V + 76) (by decide)
    have h4 := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (V + 80)
    runBlock h2 h3 h4
  have hfailAt72Framed := cpsTripleWithin_frameR
    (pure (status ≠ 0) ** productionStatusRest listBase inputBytes frameBytes)
    (pcFree_sepConj pcFree_pure
      (productionStatusRest_pcFree listBase inputBytes frameBytes))
    hfailAt72Base
  have hfailAt72' := cpsTripleWithin_extend_code hwrap hfailAt72Framed
  have hfailAt72 : cpsTripleWithin 3 (V + 72)
      (raVal &&& ~~~(1 : Word)) allCode
      ((((((.x2 ↦ᵣ sp) ** (.x10 ↦ᵣ (7 : Word)) **
          (.x1 ↦ᵣ (V + 44)) ** (.x13 ↦ᵣ Frame) **
          (.x0 ↦ᵣ (0 : Word)) ** (memIs sp raVal) **
          (memIs (sp + 8) old13)) ** pure (status ≠ 0)) **
        productionStatusRest listBase inputBytes frameBytes)))
      (productionExitPost sp old13 raVal listBase listEnd status
        inputBytes frameBytes) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [sepConj_assoc'] at hp ⊢
        exact hp)
      (fun _ hp => by
        simp only [productionExitPost]
        right; right; right
        drop_pure hp
        dsimp [productionNonemptyExitPost, productionStatusRest] at hp ⊢
        xperm_hyp hp) hfailAt72'
  have hstatusToFinal := cpsNBranchWithin_merge (nSteps2 := 3) hstatus (by
    intro ex hmem
    simp only [List.map, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h
    · subst ex
      exact hsucc3
    · subst ex
      exact hfailAt72)
  have hcall' : cpsTripleWithin (1 + n) CallPC (V + 44) allCode
      (productionItemsPre listBase listEnd Frame inputBytes frameBytes **
        productionEntrySavedFrame sp old13 raVal)
      (((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x2 ↦ᵣ sp) ** (.x1 ↦ᵣ (V + 44)) ** (.x13 ↦ᵣ Frame) **
          (memIs sp raVal) ** (memIs (sp + 8) old13)) **
        productionStatusRest listBase inputBytes frameBytes) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hq => by
        simp only [RetPC, sepConj_assoc'] at hq ⊢
        xperm_hyp hq) hcall
  have hstatusToFinal' : cpsTripleWithin (7 + 3) (V + 44)
      (raVal &&& ~~~(1 : Word)) allCode
      (((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x2 ↦ᵣ sp) ** (.x1 ↦ᵣ (V + 44)) ** (.x13 ↦ᵣ Frame) **
          (memIs sp raVal) ** (memIs (sp + 8) old13)) **
        productionStatusRest listBase inputBytes frameBytes)
      (productionExitPost sp old13 raVal listBase listEnd status
        inputBytes frameBytes) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [sepConj_assoc'] at hp ⊢
        exact hp)
      (fun _ hp => hp) hstatusToFinal
  have hvalid := cpsTripleWithin_seq_same_cr hcall' hstatusToFinal'

  have hsimpleRest := productionSimpleExitRest_pcFree
    listBase listEnd inputBytes frameBytes
  have hempty0 := rlp_validate_payload_production_empty_tail_spec_within
    sp old13 raVal raVal listBase
    (productionSimpleExitRest listBase listEnd inputBytes frameBytes) hsimpleRest
  have hempty1 := cpsTripleWithin_extend_code hwrap hempty0
  have hempty : cpsTripleWithin 6 (V + 56) (raVal &&& ~~~(1 : Word)) allCode
      (((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listEnd) **
        pure (listBase = listEnd)) **
        productionEntryFrame sp old13 raVal listBase inputBytes frameBytes)
      (productionExitPost sp old13 raVal listBase listEnd status
        inputBytes frameBytes) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        drop_pure hp
        dsimp [productionEntryFrame, productionEntrySavedFrame,
          productionSimpleExitRest, productionItemsRest] at hp ⊢
        xperm_hyp hp)
      (fun _ hp => by
        simp only [productionExitPost]
        left
        dsimp [productionSimpleExitPost, productionSimpleExitRest,
          productionItemsRest] at hp ⊢
        xperm_hyp hp) hempty1
  have hearly0 := rlp_validate_payload_production_early_failure_tail_spec_within
    sp old13 raVal raVal listBase
    (productionSimpleExitRest listBase listEnd inputBytes frameBytes) hsimpleRest
  have hearly1 := cpsTripleWithin_extend_code hwrap hearly0
  have hearly : cpsTripleWithin 5 (V + 64) (raVal &&& ~~~(1 : Word)) allCode
      (((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listEnd)) **
        (pure (¬ BitVec.ult listBase listEnd) **
          (pure (listBase ≠ listEnd) **
            productionEntryFrame sp old13 raVal listBase inputBytes frameBytes)))
      (productionExitPost sp old13 raVal listBase listEnd status
        inputBytes frameBytes) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        drop_pure hp
        dsimp [productionEntryFrame, productionEntrySavedFrame,
          productionSimpleExitRest, productionItemsRest] at hp ⊢
        xperm_hyp hp)
      (fun _ hp => by
        simp only [productionExitPost]
        right; left
        dsimp [productionSimpleExitPost, productionSimpleExitRest,
          productionItemsRest] at hp ⊢
        xperm_hyp hp) hearly1
  have hemptyN := cpsTripleWithin_mono_nSteps (show 6 ≤ 1 + n + 10 by omega)
    hempty
  have hearlyN := cpsTripleWithin_mono_nSteps (show 5 ≤ 1 + n + 10 by omega)
    hearly
  have hfull := cpsNBranchWithin_merge (nSteps2 := 1 + n + 10) hprefix (by
    intro ex hmem
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hemptyN
    · exact hearlyN
    · exact hvalid)
  have hfull' := cpsTripleWithin_mono_nSteps
    (show 7 + (1 + n + 10) ≤ 7 + ((1 + n) + 12) by omega) hfull
  exact cpsTripleWithin_extend_code (by
    intro a i h
    exact hcode a i (by simpa [allCode] using h)) hfull'

#print axioms rlp_validate_payload_production_full_spec_within

end EvmAsm.Codegen.RlpValidatePayloadProductionAdapter
