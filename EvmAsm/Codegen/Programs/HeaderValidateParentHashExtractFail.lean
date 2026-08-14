/-
  EvmAsm.Codegen.Programs.HeaderValidateParentHashExtractFail

  Extract-fail residual + adapter for `header_validate_parent_hash`
  (status = 1). Same namespace as `HeaderValidateParentHashSpec`.
-/

import EvmAsm.Codegen.Programs.HeaderValidateParentHashSpec

namespace EvmAsm.Codegen.HeaderValidateParentHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_frameSlotsSaved _ _ _)

set_option maxRecDepth 8000 in
/-- Extract-fail residual: prologue+headers ;; beq fall ;; status-1. Cost `19+nH`. -/
theorem hvphExtractFail_spec_within
    (nH : Nat) (sp0 spC ret thisPtr thisLen parentPtr parentLen statusHdr : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes claimedBytes claimedOut : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (h_nz : statusHdr ≠ (0 : Word))
    (h_headers : headersCallPremise nH (H + 40) statusHdr thisPtr thisLen
      thisBytes claimedBytes claimedOut
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes)) :
    cpsTripleWithin (19 + nH) H ret fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt hvphFrame (hvphFrameVals ret vals) **
        frameSlotsOwn hvphFrame spC **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
        claimedOwn claimedBytes **
        bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        bytesRegion parentPtr parentBytes **
        hvphFailG thisPtr thisBytes claimedOut parentLen) := by
  have hph := hvphPrologueHeaders nH sp0 spC ret thisPtr thisLen parentPtr parentLen
    statusHdr vals thisBytes parentBytes claimedBytes claimedOut hspC h_headers
  have hphW : cpsTripleWithin (9 + (1 + nH)) H (H + 40) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt hvphFrame (hvphFrameVals ret vals) **
        frameSlotsOwn hvphFrame spC **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
        claimedOwn claimedBytes **
        bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ statusHdr) ** (.x0 ↦ᵣ (0 : Word)) **
        claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
        regOwn .x11 ** regOwn .x12 **
        headersCallFrameCore spC ret parentPtr parentLen vals parentBytes) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      unfold headersCallFrame at hq
      unfold headersCallFrameCore
      xperm_hyp hq) hph
  have hbeq := hvphBeqExtractFailFramed spC ret parentPtr parentLen statusHdr vals
    thisPtr thisBytes claimedOut parentBytes h_nz
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hphW hbeq
  have hvals' :
      regsAt hvphFrame (hvphPostHeadersVals parentPtr parentLen vals) =
        ((.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
          (.x18 ↦ᵣ vals .x18)) := by
    simp [hvphPostHeadersVals, hvphFrame, regsAt, sepConj_emp_right']
  have hepi0 := hvphStatus1Exit sp0 spC statusHdr (hvphFrameVals ret vals)
    (hvphPostHeadersVals parentPtr parentLen vals)
    (bytesRegion parentPtr parentBytes **
      hvphFailG thisPtr thisBytes claimedOut parentLen)
    (by refine pcFree_sepConj (bytesRegion_pcFree _ _)
          (hvphFailG_pcFree thisPtr thisBytes claimedOut parentLen))
    hspC (by simpa [hvphFrameVals] using hret)
  have hepi := cpsTripleWithin_extend_code hvph_mono hepi0
  have hepiW : cpsTripleWithin 8 (H + 44) ret fullCode
      ((.x10 ↦ᵣ statusHdr) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x13 ↦ᵣ parentLen) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        bytesRegion parentPtr parentBytes **
        claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        regOwn .x11 ** regOwn .x12)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        bytesRegion parentPtr parentBytes **
        hvphFailG thisPtr thisBytes claimedOut parentLen) :=
    cpsTripleWithin_weaken (fun _ hp => by
      rw [hvals']
      unfold hvphFailG claimedOwn
      xperm_hyp hp) (fun _ hq => by
      simp [hvphFrameVals] at hq ⊢
      xperm_hyp hq) hepi
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold headersCallFrameCore at hp
    xperm_hyp hp) h01 hepiW
  have hn : (9 + (1 + nH)) + 1 + 8 = 19 + nH := by omega
  rw [← hn]
  exact h012


/-! ## Adapter-shaped extract-fail (`status = 1`). Cost `19+nH`. -/

/-- Extract-fail residual → `hvphPost ** claimedOwn`. -/
theorem hvphExtractFail_post_to_adapter
    (sp0 spC ret thisPtr parentPtr parentLen : Word) (vals : Reg → Word)
    (thisBytes parentBytes claimedOut : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12)) :
    ∀ s,
      ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        bytesRegion parentPtr parentBytes **
        hvphFailG thisPtr thisBytes claimedOut parentLen) s →
      (hvphPost sp0 thisPtr parentPtr ret (1 : Word) vals thisBytes parentBytes **
        claimedOwn claimedOut) s := by
  intro s hq
  unfold hvphFailG at hq
  have hqTrail :
      ((((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
          (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
          frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
          bytesRegion parentPtr parentBytes **
          claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word))) **
        (.x13 ↦ᵣ parentLen))) s := by
    xperm_hyp hq
  have hqOwn :
      ((((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
          (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
          frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
          bytesRegion parentPtr parentBytes **
          claimedOwn claimedOut ** bytesRegion thisPtr thisBytes **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          regOwn .x11 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word))) **
        regOwn .x13)) s :=
    sepConj_mono_right (regIs_to_regOwn .x13 parentLen) s hqTrail
  unfold hvphPost
  simp only [regsAt_hvphSavedFrame, hspC] at hqOwn ⊢
  xperm_hyp hqOwn

set_option maxRecDepth 8000 in
/-- Extract-fail path in adapter shape. Cost `19+nH`. -/
theorem header_validate_parent_hash_extract_fail_spec_within
    (nH : Nat) (sp0 spC ret thisPtr thisLen parentPtr parentLen statusHdr : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes claimedBytes claimedOut : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret)
    (h_nz : statusHdr ≠ (0 : Word))
    (h_headers : headersCallPremise nH (H + 40) statusHdr thisPtr thisLen
      thisBytes claimedBytes claimedOut
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes)) :
    cpsTripleWithin (19 + nH) H ret fullCode
      ((.x1 ↦ᵣ ret) **
        hvphPre sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes **
        claimedOwn claimedBytes)
      (hvphPost sp0 thisPtr parentPtr ret (1 : Word) vals thisBytes parentBytes **
        claimedOwn claimedOut) := by
  have hfail := hvphExtractFail_spec_within nH sp0 spC ret thisPtr thisLen
    parentPtr parentLen statusHdr vals thisBytes parentBytes claimedBytes claimedOut
    hspC hret h_nz h_headers
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hfail
  · unfold hvphPre at hp
    simp only [regsAt_hvphFrame_of_vals, hspC] at hp ⊢
    xperm_hyp hp
  · exact hvphExtractFail_post_to_adapter sp0 spC ret thisPtr parentPtr parentLen
      vals thisBytes parentBytes claimedOut hspC s hq

end EvmAsm.Codegen.HeaderValidateParentHashSpec
