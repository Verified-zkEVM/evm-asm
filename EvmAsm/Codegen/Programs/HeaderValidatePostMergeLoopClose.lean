import EvmAsm.Codegen.Programs.HeaderValidatePostMergeLoopBody

/-!
  K67 loop ok-path arms (successor to `HeaderValidatePostMergeLoopBody.lean`,
  which is at the 1500-line cap): the per-exit lemmas for the walk-status
  dispatch and the ok-path guards, composed with the status tails.
-/

namespace EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

/-- The walk-status dispatch at [17] (K + 68): when the walk outcome carries a
    nonzero status in `x11`, the BNE takes to the status-4 tail site
    [157] = K + 628.  Cost 1. -/
theorem k67LoopFail
    (sp0 spC base omConst cursor endPtr statusW iW v8 v9 v21 v5 v6 v7 v28 v29 v30 v31 : Word)
    (bytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-48 : BitVec 12))
    (hne : statusW ≠ (0 : Word)) :
    cpsTripleWithin 1 (K + 68) (K + 628) fullCode
      ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ statusW) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) **
        (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
      ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ statusW) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) **
        (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) := by
  have hbne := bne_spec_gen_within .x11 .x0 (560 : BitVec 13) statusW (0 : Word) (K + 68)
  rw [show (K + 68 : Word) + 4 = K + 72 from by bv_omega,
    show (K + 68 : Word) + signExtend13 (560 : BitVec 13) = K + 628 from by
      rw [show signExtend13 (560 : BitVec 13) = (560 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 68) k67Prog 17 (.BNE .x11 .x0 (560 : BitVec 13))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) hbne
  have htake0 := cpsBranchWithin_takenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      first
        | exact absurd ((sepConj_pure_right _).1 hBP).2 hne
        | exact hne ((sepConj_pure_right _).1 hBP).2)
  have htake := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ cursor) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) **
      (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      frameSlotsOwn k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) **
      bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact pcFree_memOwn
        | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsOwn _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp)
    htake0
  exact cpsTripleWithin_extend_code k67_mono
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) htake)

end EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec
