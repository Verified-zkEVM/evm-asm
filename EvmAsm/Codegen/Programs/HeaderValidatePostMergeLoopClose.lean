import EvmAsm.Codegen.Programs.HeaderValidatePostMergeLoopBody
import EvmAsm.Rv64.SAsm.MeasureLoop

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
    (svals : Reg → Word)
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
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
      ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ statusW) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) **
        (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
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
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
    (by
      repeat' first
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact pcFree_memOwn
        | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp)
    htake0
  exact cpsTripleWithin_extend_code k67_mono
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) htake)

/-! ## Epilogue: slot restore, deallocate, return -/

set_option maxRecDepth 4000 in
/-- Instructions 158-165: reload `ra`/`x8`/`x9`/`x18`/`x19`/`x20` from the
    48-byte frame, deallocate (`ADDI sp, 48`), and return to `ret`.  The
    frame slots stay owned (loose `\u21a6\u2098` atoms) so the straight-line
    `runBlock` chains; the status in `x10` and the pass-through `x21` ride
    through untouched. -/
theorem k67Epilogue
    (sp0 spC base omConst ret v8 v9 v18 v19 v20 v21 o1 o8 o9 o18 o19 o20 status : Word)
    (bytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-48 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret) :
    cpsTripleWithin (7 + 1) (K + 632) ret fullCode
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ status) ** (.x21 ↦ᵣ v21) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) ** ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ status) ** (.x21 ↦ᵣ v21) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) ** ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) := by
  rw [show signExtend12 (-48 : BitVec 12) = (-48 : Word) from by decide] at hspC
  have h158 : cpsTripleWithin 1 (K + 632) (K + 632 + 4) (CodeReq.singleton (K + 632) (.LD .x1 .x2 (0 : BitVec 12))) ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** ((spC + signExtend12 (0 : BitVec 12)) ↦ₘ ret)) ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ ret) ** ((spC + signExtend12 (0 : BitVec 12)) ↦ₘ ret)) := ld_spec_gen_within .x1 .x2 spC o1 ret (0 : BitVec 12) (K + 632) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show spC + (0 : Word) = spC from by bv_omega] at h158
  have h159 : cpsTripleWithin 1 (K + 636) (K + 636 + 4) (CodeReq.singleton (K + 636) (.LD .x8 .x2 (8 : BitVec 12))) ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ o8) ** ((spC + signExtend12 (8 : BitVec 12)) ↦ₘ v8)) ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ v8) ** ((spC + signExtend12 (8 : BitVec 12)) ↦ₘ v8)) := ld_spec_gen_within .x8 .x2 spC o8 v8 (8 : BitVec 12) (K + 636) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show spC + (8 : Word) = spC + 8 from by bv_omega] at h159
  have h160 : cpsTripleWithin 1 (K + 640) (K + 640 + 4) (CodeReq.singleton (K + 640) (.LD .x9 .x2 (16 : BitVec 12))) ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ o9) ** ((spC + signExtend12 (16 : BitVec 12)) ↦ₘ v9)) ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ v9) ** ((spC + signExtend12 (16 : BitVec 12)) ↦ₘ v9)) := ld_spec_gen_within .x9 .x2 spC o9 v9 (16 : BitVec 12) (K + 640) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show spC + (16 : Word) = spC + 16 from by bv_omega] at h160
  have h161 : cpsTripleWithin 1 (K + 644) (K + 644 + 4) (CodeReq.singleton (K + 644) (.LD .x18 .x2 (24 : BitVec 12))) ((.x2 ↦ᵣ spC) ** (.x18 ↦ᵣ o18) ** ((spC + signExtend12 (24 : BitVec 12)) ↦ₘ v18)) ((.x2 ↦ᵣ spC) ** (.x18 ↦ᵣ v18) ** ((spC + signExtend12 (24 : BitVec 12)) ↦ₘ v18)) := ld_spec_gen_within .x18 .x2 spC o18 v18 (24 : BitVec 12) (K + 644) (by decide)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show spC + (24 : Word) = spC + 24 from by bv_omega] at h161
  have h162 : cpsTripleWithin 1 (K + 648) (K + 648 + 4) (CodeReq.singleton (K + 648) (.LD .x19 .x2 (32 : BitVec 12))) ((.x2 ↦ᵣ spC) ** (.x19 ↦ᵣ o19) ** ((spC + signExtend12 (32 : BitVec 12)) ↦ₘ v19)) ((.x2 ↦ᵣ spC) ** (.x19 ↦ᵣ v19) ** ((spC + signExtend12 (32 : BitVec 12)) ↦ₘ v19)) := ld_spec_gen_within .x19 .x2 spC o19 v19 (32 : BitVec 12) (K + 648) (by decide)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
    show spC + (32 : Word) = spC + 32 from by bv_omega] at h162
  have h163 : cpsTripleWithin 1 (K + 652) (K + 652 + 4) (CodeReq.singleton (K + 652) (.LD .x20 .x2 (40 : BitVec 12))) ((.x2 ↦ᵣ spC) ** (.x20 ↦ᵣ o20) ** ((spC + signExtend12 (40 : BitVec 12)) ↦ₘ v20)) ((.x2 ↦ᵣ spC) ** (.x20 ↦ᵣ v20) ** ((spC + signExtend12 (40 : BitVec 12)) ↦ₘ v20)) := ld_spec_gen_within .x20 .x2 spC o20 v20 (40 : BitVec 12) (K + 652) (by decide)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide,
    show spC + (40 : Word) = spC + 40 from by bv_omega] at h163
  have h164 : cpsTripleWithin 1 (K + 656) (K + 656 + 4)
      (CodeReq.singleton (K + 656) (.ADDI .x2 .x2 (48 : BitVec 12)))
      (.x2 ↦ᵣ spC) (.x2 ↦ᵣ (spC + signExtend12 (48 : BitVec 12))) := 
    addi_spec_gen_same_within .x2 spC (48 : BitVec 12) (K + 656) (by decide)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide,
    show spC + (48 : Word) = sp0 from by bv_omega] at h164
  have h158C := cpsTripleWithin_extend_code (CodeReq.ofProg_mem_at K (K + 632) k67Prog 158 (.LD .x1 .x2 (0 : BitVec 12)) (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h158
  have h159C := cpsTripleWithin_extend_code (CodeReq.ofProg_mem_at K (K + 636) k67Prog 159 (.LD .x8 .x2 (8 : BitVec 12)) (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h159
  have h160C := cpsTripleWithin_extend_code (CodeReq.ofProg_mem_at K (K + 640) k67Prog 160 (.LD .x9 .x2 (16 : BitVec 12)) (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h160
  have h161C := cpsTripleWithin_extend_code (CodeReq.ofProg_mem_at K (K + 644) k67Prog 161 (.LD .x18 .x2 (24 : BitVec 12)) (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h161
  have h162C := cpsTripleWithin_extend_code (CodeReq.ofProg_mem_at K (K + 648) k67Prog 162 (.LD .x19 .x2 (32 : BitVec 12)) (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h162
  have h163C := cpsTripleWithin_extend_code (CodeReq.ofProg_mem_at K (K + 652) k67Prog 163 (.LD .x20 .x2 (40 : BitVec 12)) (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h163
  have h164C := cpsTripleWithin_extend_code (CodeReq.ofProg_mem_at K (K + 656) k67Prog 164
    (.ADDI .x2 .x2 (48 : BitVec 12)) (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
    (by rw [k67_length]; decide)) h164
  have hblk : cpsTripleWithin 7 (K + 632) (K + 660) k67Code
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ status) ** (.x21 ↦ᵣ v21) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) ** ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ status) ** (.x21 ↦ᵣ v21) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) ** ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) := by
    runBlock h158C h159C h160C h161C h162C h163C h164C
  have hjalr := EvmAsm.Evm64.ret_spec_within' (K + 660) ret
  rw [hret] at hjalr
  have hjalrC := cpsTripleWithin_extend_code (CodeReq.ofProg_mem_at K (K + 660) k67Prog 165
    (.JALR .x0 .x1 (0 : BitVec 12)) (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
    (by rw [k67_length]; decide)) hjalr
  have hjalrF := cpsTripleWithin_frameR ((.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ status) ** (.x21 ↦ᵣ v21) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) ** ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
    (by repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp) hjalrC
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblk hjalrF
  exact cpsTripleWithin_extend_code k67_mono
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hall)

/-! ## Status tails (instructions 149-157): set status and jump to the epilogue -/
/-- Status-0 tail: LI x10, 0 then JAL x0 into the epilogue. -/
theorem k67StatusTail0
    (sp0 spC base omConst ret v8 v9 v18 v19 v20 v21 o1 o8 o9 o18 o19 o20 old10 : Word)
    (bytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-48 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret) :
    cpsTripleWithin 2 (K + 596) (K + 632) fullCode
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ old10) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) := by
  have hLI : cpsTripleWithin 1 (K + 596) (K + 596 + 4)
      (CodeReq.singleton (K + 596) (.LI .x10 (0 : Word)))
      (.x10 ↦ᵣ old10) (.x10 ↦ᵣ (0 : Word)) :=
    li_spec_gen_within .x10 old10 (0 : Word) (K + 596) (by decide)
  have hLIC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 596) k67Prog 149 (.LI .x10 (0 : Word))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) hLI
  have hG : ((.x2 ↦ᵣ spC) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
    repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_memOwn
        | exact pcFree_regOwn | apply pcFree_sepConj
        | exact pcFree_frameSlotsOwn _ _ | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _ | exact pcFree_emp
  have hLIF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG hLIC
  have hJAL := jal_x0_spec_gen_within (32 : BitVec 21) (K + 600)
  rw [show K + 600 + signExtend21 (32 : BitVec 21) = K + 632 from by
      rw [show signExtend21 (32 : BitVec 21) = (32 : Word) from by decide]; bv_omega] at hJAL
  have hJALC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 600) k67Prog 150 (.JAL .x0 (32 : BitVec 21))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) hJAL
  have hG2 : (((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))).pcFree := by
    repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_memOwn
        | exact pcFree_regOwn | apply pcFree_sepConj
        | exact pcFree_frameSlotsOwn _ _ | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _ | exact pcFree_emp
  have hJALF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))) hG2 hJALC
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun s hp => by
      apply (sepConj_emp_left s).mpr
      first
        | exact hp
        | xperm_hyp hp) hLIF hJALF
  exact cpsTripleWithin_extend_code k67_mono
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun s hq => by
      rw [sepConj_emp_left] at hq
      first
        | exact hq
        | xperm_hyp hq) hseq)


/-- Status-1 tail: LI x10, 1 then JAL x0 into the epilogue. -/
theorem k67StatusTail1
    (sp0 spC base omConst ret v8 v9 v18 v19 v20 v21 o1 o8 o9 o18 o19 o20 old10 : Word)
    (bytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-48 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret) :
    cpsTripleWithin 2 (K + 604) (K + 632) fullCode
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ old10) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ (1 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) := by
  have hLI : cpsTripleWithin 1 (K + 604) (K + 604 + 4)
      (CodeReq.singleton (K + 604) (.LI .x10 (1 : Word)))
      (.x10 ↦ᵣ old10) (.x10 ↦ᵣ (1 : Word)) :=
    li_spec_gen_within .x10 old10 (1 : Word) (K + 604) (by decide)
  have hLIC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 604) k67Prog 151 (.LI .x10 (1 : Word))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) hLI
  have hG : ((.x2 ↦ᵣ spC) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
    repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_memOwn
        | exact pcFree_regOwn | apply pcFree_sepConj
        | exact pcFree_frameSlotsOwn _ _ | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _ | exact pcFree_emp
  have hLIF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG hLIC
  have hJAL := jal_x0_spec_gen_within (24 : BitVec 21) (K + 608)
  rw [show K + 608 + signExtend21 (24 : BitVec 21) = K + 632 from by
      rw [show signExtend21 (24 : BitVec 21) = (24 : Word) from by decide]; bv_omega] at hJAL
  have hJALC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 608) k67Prog 152 (.JAL .x0 (24 : BitVec 21))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) hJAL
  have hG2 : (((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ (1 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))).pcFree := by
    repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_memOwn
        | exact pcFree_regOwn | apply pcFree_sepConj
        | exact pcFree_frameSlotsOwn _ _ | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _ | exact pcFree_emp
  have hJALF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ (1 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))) hG2 hJALC
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun s hp => by
      apply (sepConj_emp_left s).mpr
      first
        | exact hp
        | xperm_hyp hp) hLIF hJALF
  exact cpsTripleWithin_extend_code k67_mono
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun s hq => by
      rw [sepConj_emp_left] at hq
      first
        | exact hq
        | xperm_hyp hq) hseq)


/-- Status-2 tail: LI x10, 2 then JAL x0 into the epilogue. -/
theorem k67StatusTail2
    (sp0 spC base omConst ret v8 v9 v18 v19 v20 v21 o1 o8 o9 o18 o19 o20 old10 : Word)
    (bytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-48 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret) :
    cpsTripleWithin 2 (K + 612) (K + 632) fullCode
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ old10) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ (2 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) := by
  have hLI : cpsTripleWithin 1 (K + 612) (K + 612 + 4)
      (CodeReq.singleton (K + 612) (.LI .x10 (2 : Word)))
      (.x10 ↦ᵣ old10) (.x10 ↦ᵣ (2 : Word)) :=
    li_spec_gen_within .x10 old10 (2 : Word) (K + 612) (by decide)
  have hLIC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 612) k67Prog 153 (.LI .x10 (2 : Word))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) hLI
  have hG : ((.x2 ↦ᵣ spC) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
    repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_memOwn
        | exact pcFree_regOwn | apply pcFree_sepConj
        | exact pcFree_frameSlotsOwn _ _ | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _ | exact pcFree_emp
  have hLIF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG hLIC
  have hJAL := jal_x0_spec_gen_within (16 : BitVec 21) (K + 616)
  rw [show K + 616 + signExtend21 (16 : BitVec 21) = K + 632 from by
      rw [show signExtend21 (16 : BitVec 21) = (16 : Word) from by decide]; bv_omega] at hJAL
  have hJALC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 616) k67Prog 154 (.JAL .x0 (16 : BitVec 21))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) hJAL
  have hG2 : (((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ (2 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))).pcFree := by
    repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_memOwn
        | exact pcFree_regOwn | apply pcFree_sepConj
        | exact pcFree_frameSlotsOwn _ _ | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _ | exact pcFree_emp
  have hJALF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ (2 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))) hG2 hJALC
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun s hp => by
      apply (sepConj_emp_left s).mpr
      first
        | exact hp
        | xperm_hyp hp) hLIF hJALF
  exact cpsTripleWithin_extend_code k67_mono
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun s hq => by
      rw [sepConj_emp_left] at hq
      first
        | exact hq
        | xperm_hyp hq) hseq)


/-- Status-3 tail: LI x10, 3 then JAL x0 into the epilogue. -/
theorem k67StatusTail3
    (sp0 spC base omConst ret v8 v9 v18 v19 v20 v21 o1 o8 o9 o18 o19 o20 old10 : Word)
    (bytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-48 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret) :
    cpsTripleWithin 2 (K + 620) (K + 632) fullCode
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ old10) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ (3 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) := by
  have hLI : cpsTripleWithin 1 (K + 620) (K + 620 + 4)
      (CodeReq.singleton (K + 620) (.LI .x10 (3 : Word)))
      (.x10 ↦ᵣ old10) (.x10 ↦ᵣ (3 : Word)) :=
    li_spec_gen_within .x10 old10 (3 : Word) (K + 620) (by decide)
  have hLIC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 620) k67Prog 155 (.LI .x10 (3 : Word))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) hLI
  have hG : ((.x2 ↦ᵣ spC) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
    repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_memOwn
        | exact pcFree_regOwn | apply pcFree_sepConj
        | exact pcFree_frameSlotsOwn _ _ | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _ | exact pcFree_emp
  have hLIF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG hLIC
  have hJAL := jal_x0_spec_gen_within (8 : BitVec 21) (K + 624)
  rw [show K + 624 + signExtend21 (8 : BitVec 21) = K + 632 from by
      rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]; bv_omega] at hJAL
  have hJALC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 624) k67Prog 156 (.JAL .x0 (8 : BitVec 21))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) hJAL
  have hG2 : (((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ (3 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))).pcFree := by
    repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_memOwn
        | exact pcFree_regOwn | apply pcFree_sepConj
        | exact pcFree_frameSlotsOwn _ _ | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _ | exact pcFree_emp
  have hJALF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ (3 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))) hG2 hJALC
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun s hp => by
      apply (sepConj_emp_left s).mpr
      first
        | exact hp
        | xperm_hyp hp) hLIF hJALF
  exact cpsTripleWithin_extend_code k67_mono
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun s hq => by
      rw [sepConj_emp_left] at hq
      first
        | exact hq
        | xperm_hyp hq) hseq)


/-- Status-4 tail: LI x10, 4 then fall through into the epilogue. -/
theorem k67StatusTail4
    (sp0 spC base omConst ret v8 v9 v18 v19 v20 v21 o1 o8 o9 o18 o19 o20 old10 : Word)
    (bytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-48 : BitVec 12))
    (hret : ret &&& ~~~(1 : Word) = ret) :
    cpsTripleWithin 1 (K + 628) (K + 632) fullCode
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ old10) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
      ((.x2 ↦ᵣ spC) ** (.x10 ↦ᵣ (4 : Word)) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) := by
  have hLI : cpsTripleWithin 1 (K + 628) (K + 628 + 4)
      (CodeReq.singleton (K + 628) (.LI .x10 (4 : Word)))
      (.x10 ↦ᵣ old10) (.x10 ↦ᵣ (4 : Word)) :=
    li_spec_gen_within .x10 old10 (4 : Word) (K + 628) (by decide)
  have hLIC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 628) k67Prog 157 (.LI .x10 (4 : Word))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) hLI
  have hG : ((.x2 ↦ᵣ spC) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
    repeat' first
        | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_memOwn
        | exact pcFree_regOwn | apply pcFree_sepConj
        | exact pcFree_frameSlotsOwn _ _ | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _ | exact pcFree_emp
  have hLIF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x21 ↦ᵣ v21) **
        (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ ret) ** ((spC + 8) ↦ₘ v8) ** ((spC + 16) ↦ₘ v9) **
        ((spC + 24) ↦ₘ v18) ** ((spC + 32) ↦ₘ v19) ** ((spC + 40) ↦ₘ v20) **
        bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG hLIC
  exact cpsTripleWithin_extend_code k67_mono
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hLIF)

/-! ## Loop ok-path: i=7 difficulty arm -/

set_option maxRecDepth 4000 in
/-! ## Loop ok-path: difficulty arm (i = 7) -/
set_option maxRecDepth 4000 in
/-- `k67LoopDiff`: at the ok-path with `x20 = 7`, the difficulty guard fires:
    skip the i=1 capture, match the i=7 guard, and dispatch on `len ≠ 0` to
    the status-1 tail entry (K+604).  Exits at K+604; the status tail and
    epilogue are composed at the top level. -/
theorem k67LoopDiff
    (sp0 base omConst cursor endPtr lenW iW next v21 v6 v7 v28 v29 v30 v31 o8 o9 v5 : Word)
    (bytes : List (BitVec 8)) (svals : Reg → Word)
    (hi7 : iW = (7 : Word))
    (hne : lenW ≠ (0 : Word)) :
    cpsTripleWithin 5 (K + 72) (K + 604) fullCode
    ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) ** regOwn .x13 ** regOwn .x14)
    ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) ** regOwn .x13 ** regOwn .x14) := by
  -- [18] LI x5, 1
  have h18 : cpsTripleWithin 1 (K + 72) (K + 76)
      (CodeReq.singleton (K + 72) (.LI .x5 (1 : Word)))
      ((.x5 ↦ᵣ v5)) ((.x5 ↦ᵣ (1 : Word))) :=
    li_spec_gen_within .x5 v5 (1 : Word) (K + 72) (by decide)
  have h18C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at K (K + 72) k67Prog 18 (.LI .x5 (1 : Word))
        (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
        (by rw [k67_length]; decide)) h18
  have hG18 : ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) ** regOwn .x13 ** regOwn .x14).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_regOwn | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _ | exact pcFree_memOwn
        | exact bytesRegion_pcFree _ _ | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp
  have h18F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) ** regOwn .x13 ** regOwn .x14) hG18 h18C
  -- [19] BNE x20, x5, +12 (taken: 7 ≠ 1)
  have h19 := bne_spec_gen_within .x20 .x5 (12 : BitVec 13) iW (1 : Word) (K + 76)
  rw [show (K + 76 + 4 : Word) = K + 80 from by bv_omega,
    show (K + 76) + signExtend13 (12 : BitVec 13) = K + 88 from by
      rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega] at h19
  have h19C := cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at K (K + 76) k67Prog 19 (.BNE .x20 .x5 (12 : BitVec 13))
        (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
        (by rw [k67_length]; decide)) h19

  have h19t0 := cpsBranchWithin_takenStripPure2 h19C
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hBP).2 (by rw [hi7]; decide))
  have hG19 : ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) ** regOwn .x13 ** regOwn .x14).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_regOwn | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _ | exact pcFree_memOwn
        | exact bytesRegion_pcFree _ _ | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp
  have h19t := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) ** regOwn .x13 ** regOwn .x14) hG19 h19t0

  have hA := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h18F h19t
  -- [22] LI x5, 7
  have h22 : cpsTripleWithin 1 (K + 88) (K + 92)
      (CodeReq.singleton (K + 88) (.LI .x5 (7 : Word)))
      ((.x5 ↦ᵣ (1 : Word))) ((.x5 ↦ᵣ (7 : Word))) :=
    li_spec_gen_within .x5 (1 : Word) (7 : Word) (K + 88) (by decide)
  have h22C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at K (K + 88) k67Prog 22 (.LI .x5 (7 : Word))
        (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
        (by rw [k67_length]; decide)) h22
  have hG22 : ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) ** regOwn .x13 ** regOwn .x14).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_regOwn | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _ | exact pcFree_memOwn
        | exact bytesRegion_pcFree _ _ | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp
  have h22F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) ** regOwn .x13 ** regOwn .x14) hG22 h22C

  have hB := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hA h22F
  -- [23] BNE x20, x5, +8 (not taken: iW = 7 = x5)
  have h23 := bne_spec_gen_within .x20 .x5 (8 : BitVec 13) iW (7 : Word) (K + 92)
  rw [show (K + 92 + 4 : Word) = K + 96 from by bv_omega,
    show (K + 92) + signExtend13 (8 : BitVec 13) = K + 100 from by
      rw [show signExtend13 (8 : BitVec 13) = (8 : Word) from by decide]; bv_omega] at h23
  have h23C := cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at K (K + 92) k67Prog 23 (.BNE .x20 .x5 (8 : BitVec 13))
        (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
        (by rw [k67_length]; decide)) h23

  have h23n0 := cpsBranchWithin_ntakenStripPure2 h23C
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      rw [hi7] at hBP
      exact ((sepConj_pure_right _).1 hBP).2 rfl)
  have hG23 : ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) ** regOwn .x13 ** regOwn .x14).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_regOwn | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _ | exact pcFree_memOwn
        | exact bytesRegion_pcFree _ _ | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp
  have h23n := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) ** regOwn .x13 ** regOwn .x14) hG23 h23n0

  have hC := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hB h23n
  -- [24] BNE x12, x0, +508 (taken: len ≠ 0)
  have h24 := bne_spec_gen_within .x12 .x0 (508 : BitVec 13) lenW (0 : Word) (K + 96)
  rw [show (K + 96 + 4 : Word) = K + 100 from by bv_omega,
    show (K + 96) + signExtend13 (508 : BitVec 13) = K + 604 from by
      rw [show signExtend13 (508 : BitVec 13) = (508 : Word) from by decide]; bv_omega] at h24
  have h24C := cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at K (K + 96) k67Prog 24 (.BNE .x12 .x0 (508 : BitVec 13))
        (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
        (by rw [k67_length]; decide)) h24

  have h24t0 := cpsBranchWithin_takenStripPure2 h24C
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hBP).2 hne)
  have hG24 : ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) ** regOwn .x13 ** regOwn .x14).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_regOwn | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _ | exact pcFree_memOwn
        | exact bytesRegion_pcFree _ _ | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp
  have h24t := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)) ** regOwn .x13 ** regOwn .x14) hG24 h24t0

  have hD := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hC h24t
  exact cpsTripleWithin_extend_code k67_mono
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hD)


/-! ## Loop continue arms (back-edge K+72 -> K+56) -/

set_option maxRecDepth 4000 in
/-- `k67LoopContO`: the ok-path for `i ≀ (1, 7)` — both guard BNEs taken (skip
    capture and difficulty), cursor advanced into `x18`, index incremented,
    back-edge taken.  The loop walks fields ASCENDING 0..14 with a strictly
    advancing cursor; no read-then-write aliasing within an iteration. -/
theorem k67LoopContO (sp0 base omConst cursor endPtr lenW iW next v21 v5 v6 v7 v8 v9 v28 v29 v30 v31 : Word)
    (bytes : List (BitVec 8)) (svals : Reg → Word)
    (hio1 : iW ≠ (1 : Word)) (hio7 : iW ≠ (7 : Word)) (hi14 : iW ≠ (14 : Word)) :
    cpsTripleWithin 8 (K + 72) (K + 56) fullCode
      ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
      ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (15 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (iW + (1 : Word))) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) := by
  have h1514 : (iW + (1 : Word)) ≠ (15 : Word) := by bv_omega
  -- [18] LI x5,1
  have h18 : cpsTripleWithin 1 (K + 72) (K + 76)
      (CodeReq.singleton (K + 72) (.LI .x5 (1 : Word)))
      ((.x5 ↦ᵣ v5)) ((.x5 ↦ᵣ (1 : Word))) :=
    li_spec_gen_within .x5 v5 (1 : Word) (K + 72) (by decide)
  have h18C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 72) k67Prog 18 (.LI .x5 (1 : Word))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h18
  have hG18 : ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h18F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG18 h18C

  -- [19] BNE x20,x5,12 TAKEN (iW <> 1) -> K+88
  have h19 := bne_spec_gen_within .x20 .x5 (12 : BitVec 13) iW (1 : Word) (K + 76)
  rw [show (K + 76 + 4 : Word) = K + 80 from by bv_omega,
    show (K + 76 + signExtend13 (12 : BitVec 13)) = K + 88 from by
      rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega] at h19
  have h19C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 76) k67Prog 19 (.BNE .x20 .x5 (12 : BitVec 13))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h19
  have h19t := cpsBranchWithin_takenStripPure2 h19C
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      first
        | exact absurd ((sepConj_pure_right _).1 hBP).2 hio1
        | exact hio1 ((sepConj_pure_right _).1 hBP).2)
  have hG19 : ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h19tF := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG19 h19t

  have hA := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h18F h19tF
  -- [22] LI x5,7
  have h22 : cpsTripleWithin 1 (K + 88) (K + 92)
      (CodeReq.singleton (K + 88) (.LI .x5 (7 : Word)))
      ((.x5 ↦ᵣ (1 : Word))) ((.x5 ↦ᵣ (7 : Word))) :=
    li_spec_gen_within .x5 (1 : Word) (7 : Word) (K + 88) (by decide)
  have h22C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 88) k67Prog 22 (.LI .x5 (7 : Word))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h22
  have hG22 : ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h22F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG22 h22C

  have hB := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hA h22F
  -- [23] BNE x20,x5,8 TAKEN (iW <> 7) -> K+100
  have h23 := bne_spec_gen_within .x20 .x5 (8 : BitVec 13) iW (7 : Word) (K + 92)
  rw [show (K + 92 + 4 : Word) = K + 96 from by bv_omega,
    show (K + 92 + signExtend13 (8 : BitVec 13)) = K + 100 from by
      rw [show signExtend13 (8 : BitVec 13) = (8 : Word) from by decide]; bv_omega] at h23
  have h23C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 92) k67Prog 23 (.BNE .x20 .x5 (8 : BitVec 13))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h23
  have h23t := cpsBranchWithin_takenStripPure2 h23C
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      first
        | exact absurd ((sepConj_pure_right _).1 hBP).2 hio7
        | exact hio7 ((sepConj_pure_right _).1 hBP).2)
  have hG23 : ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h23tF := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG23 h23t

  have hC := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hB h23tF
  -- [25] MV x18,x10
  have h25 : cpsTripleWithin 1 (K + 100) (K + 104)
      (CodeReq.singleton (K + 100) (.MV .x18 .x10))
      ((.x10 ↦ᵣ next) ** (.x18 ↦ᵣ cursor)) ((.x10 ↦ᵣ next) ** (.x18 ↦ᵣ next)) :=
    mv_spec_gen_within .x18 .x10 next cursor (K + 100) (by decide)
  have h25C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 100) k67Prog 25 (.MV .x18 .x10)
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h25
  have hG25 : ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h25F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG25 h25C

  have hD := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hC h25F
  -- [26] ADDI x20,x20,1
  have h26 : cpsTripleWithin 1 (K + 104) (K + 108)
      (CodeReq.singleton (K + 104) (.ADDI .x20 .x20 (1 : BitVec 12)))
      ((.x20 ↦ᵣ iW)) ((.x20 ↦ᵣ iW + signExtend12 (1 : BitVec 12))) :=
    addi_spec_gen_same_within .x20 iW (1 : BitVec 12) (K + 104) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at h26
  have h26C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 104) k67Prog 26 (.ADDI .x20 .x20 (1 : BitVec 12))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h26
  have hG26 : ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h26F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG26 h26C

  have hE := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hD h26F
  -- [27] LI x5,15
  have h27 : cpsTripleWithin 1 (K + 108) (K + 112)
      (CodeReq.singleton (K + 108) (.LI .x5 (15 : Word)))
      ((.x5 ↦ᵣ (7 : Word))) ((.x5 ↦ᵣ (15 : Word))) :=
    li_spec_gen_within .x5 (7 : Word) (15 : Word) (K + 108) (by decide)
  have h27C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 108) k67Prog 27 (.LI .x5 (15 : Word))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h27
  have hG27 : ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (iW + (1 : Word))) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h27F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (iW + (1 : Word))) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG27 h27C

  have hF := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hE h27F
  -- [28] BNE x20,x5,-56 TAKEN (iW+1 <> 15) -> K+56
  have h28 := bne_spec_gen_within .x20 .x5 (-56 : BitVec 13) (iW + (1 : Word)) (15 : Word) (K + 112)
  rw [show (K + 112 + 4 : Word) = K + 116 from by bv_omega,
    show (K + 112 + signExtend13 (-56 : BitVec 13)) = K + 56 from by
      rw [show signExtend13 (-56 : BitVec 13) = (-56 : Word) from by decide]; bv_omega] at h28
  have h28C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 112) k67Prog 28 (.BNE .x20 .x5 (-56 : BitVec 13))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h28
  have h28t := cpsBranchWithin_takenStripPure2 h28C
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      first
        | exact absurd ((sepConj_pure_right _).1 hBP).2 h1514
        | exact h1514 ((sepConj_pure_right _).1 hBP).2)
  have hG28 : ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h28tF := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG28 h28t

  have hG2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hF h28tF
  exact cpsTripleWithin_extend_code k67_mono
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hG2)


/-! ## Loop continue arm for i = 1 (capture) -/

set_option maxRecDepth 4000 in
/-- `k67LoopCont1`: the ok-path for `i = 1` — the first guard BNE falls through
    (iW = 1), the ommers capture MVs fire (`x8 := next`, `x9 := lenW`), the
    second guard BNE is taken (1 <> 7, difficulty check skipped), cursor
    advanced into `x18`, index incremented, back-edge taken. -/
theorem k67LoopCont1 (sp0 base omConst cursor endPtr lenW iW next v21 v5 v6 v7 v8 v9 v28 v29 v30 v31 : Word)
    (bytes : List (BitVec 8)) (svals : Reg → Word)
    (hi1 : iW = (1 : Word)) :
    cpsTripleWithin 10 (K + 72) (K + 56) fullCode
      ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
      ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (15 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ next) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (iW + (1 : Word))) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) := by
  have hi1o7 : iW ≠ (7 : Word) := by rw [hi1]; decide
  have h1514 : (iW + (1 : Word)) ≠ (15 : Word) := by rw [hi1]; decide
  -- [18] LI x5,1
  have h18 : cpsTripleWithin 1 (K + 72) (K + 76)
      (CodeReq.singleton (K + 72) (.LI .x5 (1 : Word)))
      ((.x5 ↦ᵣ v5)) ((.x5 ↦ᵣ (1 : Word))) :=
    li_spec_gen_within .x5 v5 (1 : Word) (K + 72) (by decide)
  have h18C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 72) k67Prog 18 (.LI .x5 (1 : Word))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h18
  have hG18 : ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h18F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG18 h18C
  -- [19] BNE x20,x5,12 NTAKEN (iW = 1) -> K+80
  have h19 := bne_spec_gen_within .x20 .x5 (12 : BitVec 13) iW (1 : Word) (K + 76)
  rw [show (K + 76 + 4 : Word) = K + 80 from by bv_omega,
    show (K + 76 + signExtend13 (12 : BitVec 13)) = K + 88 from by
      rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega] at h19
  have h19C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 76) k67Prog 19 (.BNE .x20 .x5 (12 : BitVec 13))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h19
  have h19n := cpsBranchWithin_ntakenStripPure2 h19C
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      rw [hi1] at hBP
      exact ((sepConj_pure_right _).1 hBP).2 rfl)
  have hG19 : ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h19nF := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG19 h19n
  have hA := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h18F h19nF
  -- [20] MV x8,x10 (capture: x8 := next)
  have h20 : cpsTripleWithin 1 (K + 80) (K + 84)
      (CodeReq.singleton (K + 80) (.MV .x8 .x10))
      ((.x10 ↦ᵣ next) ** (.x8 ↦ᵣ v8)) ((.x10 ↦ᵣ next) ** (.x8 ↦ᵣ next)) :=
    mv_spec_gen_within .x8 .x10 next v8 (K + 80) (by decide)
  have h20C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 80) k67Prog 20 (.MV .x8 .x10)
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h20
  have hG20 : ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h20F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG20 h20C
  have hB := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hA h20F
  -- [21] MV x9,x12 (capture: x9 := lenW)
  have h21 : cpsTripleWithin 1 (K + 84) (K + 88)
      (CodeReq.singleton (K + 84) (.MV .x9 .x12))
      ((.x12 ↦ᵣ lenW) ** (.x9 ↦ᵣ v9)) ((.x12 ↦ᵣ lenW) ** (.x9 ↦ᵣ lenW)) :=
    mv_spec_gen_within .x9 .x12 lenW v9 (K + 84) (by decide)
  have h21C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 84) k67Prog 21 (.MV .x9 .x12)
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h21
  have hG21 : ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ next) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h21F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ next) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG21 h21C
  have hC := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hB h21F
  -- [22] LI x5,7
  have h22 : cpsTripleWithin 1 (K + 88) (K + 92)
      (CodeReq.singleton (K + 88) (.LI .x5 (7 : Word)))
      ((.x5 ↦ᵣ (1 : Word))) ((.x5 ↦ᵣ (7 : Word))) :=
    li_spec_gen_within .x5 (1 : Word) (7 : Word) (K + 88) (by decide)
  have h22C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 88) k67Prog 22 (.LI .x5 (7 : Word))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h22
  have hG22 : ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ next) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h22F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ next) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG22 h22C
  have hD := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hC h22F
  -- [23] BNE x20,x5,8 TAKEN (iW = 1 ≠ 7) -> K+100
  have h23 := bne_spec_gen_within .x20 .x5 (8 : BitVec 13) iW (7 : Word) (K + 92)
  rw [show (K + 92 + 4 : Word) = K + 96 from by bv_omega,
    show (K + 92 + signExtend13 (8 : BitVec 13)) = K + 100 from by
      rw [show signExtend13 (8 : BitVec 13) = (8 : Word) from by decide]; bv_omega] at h23
  have h23C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 92) k67Prog 23 (.BNE .x20 .x5 (8 : BitVec 13))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h23
  have h23t := cpsBranchWithin_takenStripPure2 h23C
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      first
        | exact absurd ((sepConj_pure_right _).1 hBP).2 hi1o7
        | exact hi1o7 ((sepConj_pure_right _).1 hBP).2)
  have hG23 : ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ next) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h23tF := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ next) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG23 h23t
  have hE := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hD h23tF
  -- [25] MV x18,x10
  have h25 : cpsTripleWithin 1 (K + 100) (K + 104)
      (CodeReq.singleton (K + 100) (.MV .x18 .x10))
      ((.x10 ↦ᵣ next) ** (.x18 ↦ᵣ cursor)) ((.x10 ↦ᵣ next) ** (.x18 ↦ᵣ next)) :=
    mv_spec_gen_within .x18 .x10 next cursor (K + 100) (by decide)
  have h25C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 100) k67Prog 25 (.MV .x18 .x10)
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h25
  have hG25 : ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ next) ** (.x9 ↦ᵣ lenW) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h25F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ next) ** (.x9 ↦ᵣ lenW) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG25 h25C
  have hF := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hE h25F
  -- [26] ADDI x20,x20,1
  have h26 : cpsTripleWithin 1 (K + 104) (K + 108)
      (CodeReq.singleton (K + 104) (.ADDI .x20 .x20 (1 : BitVec 12)))
      ((.x20 ↦ᵣ iW)) ((.x20 ↦ᵣ iW + signExtend12 (1 : BitVec 12))) :=
    addi_spec_gen_same_within .x20 iW (1 : BitVec 12) (K + 104) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at h26
  have h26C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 104) k67Prog 26 (.ADDI .x20 .x20 (1 : BitVec 12))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h26
  have hG26 : ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ next) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h26F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ next) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG26 h26C
  have hG := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hF h26F
  -- [27] LI x5,15
  have h27 : cpsTripleWithin 1 (K + 108) (K + 112)
      (CodeReq.singleton (K + 108) (.LI .x5 (15 : Word)))
      ((.x5 ↦ᵣ (7 : Word))) ((.x5 ↦ᵣ (15 : Word))) :=
    li_spec_gen_within .x5 (7 : Word) (15 : Word) (K + 108) (by decide)
  have h27C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 108) k67Prog 27 (.LI .x5 (15 : Word))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h27
  have hG27 : ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ next) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (iW + (1 : Word))) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h27F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ next) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (iW + (1 : Word))) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG27 h27C
  have hH := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hG h27F
  -- [28] BNE x20,x5,-56 TAKEN (iW+1 = 2 ≠ 15) -> K+56
  have h28 := bne_spec_gen_within .x20 .x5 (-56 : BitVec 13) (iW + (1 : Word)) (15 : Word) (K + 112)
  rw [show (K + 112 + 4 : Word) = K + 116 from by bv_omega,
    show (K + 112 + signExtend13 (-56 : BitVec 13)) = K + 56 from by
      rw [show signExtend13 (-56 : BitVec 13) = (-56 : Word) from by decide]; bv_omega] at h28
  have h28C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 112) k67Prog 28 (.BNE .x20 .x5 (-56 : BitVec 13))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h28
  have h28t := cpsBranchWithin_takenStripPure2 h28C
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      first
        | exact absurd ((sepConj_pure_right _).1 hBP).2 h1514
        | exact h1514 ((sepConj_pure_right _).1 hBP).2)
  have hG28 : ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ next) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
      repeat' first
        | exact pcFree_regIs | exact pcFree_memIs
        | exact pcFree_memOwn | exact pcFree_regOwn
        | apply pcFree_sepConj
        | exact pcFree_frameSlotsSaved _ _ _
        | exact bytesRegion_pcFree _ _
        | exact bytesRegionAux_pcFree _ _ _
        | exact pcFree_emp

  have h28tF := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ next) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ endPtr) ** (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals ** bytesRegion base bytes ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG28 h28t
  have hI := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hH h28tF
  exact cpsTripleWithin_extend_code k67_mono
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hI)

/-! ## Loop-continue arm: i = 7 with zero content length -/
set_option maxRecDepth 4000 in
/-- Iteration `i = 7` (difficulty field) whose decoded content length is
    zero: both guards skip their special paths (`i != 1` jumps over the
    ommers capture; `i = 7` falls through the difficulty check because
    `x12 = lenW = 0`), then the shared advance and back-edge run. -/
theorem k67LoopCont7 (sp0 base omConst cursor endPtr lenW iW next v21 v5 v6 v7 v8 v9
      v28 v29 v30 v31 : Word) (bytes : List (BitVec 8)) (svals : Reg → Word)
    (hi7 : iW = (7 : Word)) (hlen0 : lenW = (0 : Word)) :
    cpsTripleWithin 9 (K + 72) (K + 56) fullCode
      ((.x1 ↦ᵣ (K + 68))
      ** (.x5 ↦ᵣ v5)
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ cursor)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x20 ↦ᵣ iW)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
      ((.x1 ↦ᵣ (K + 68))
      ** (.x5 ↦ᵣ (15 : Word))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ next)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x20 ↦ᵣ (iW + (1 : Word)))
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) := by
  have hi7o1 : iW ≠ (1 : Word) := by rw [hi7]; decide
  have h1514 : (iW + (1 : Word)) ≠ (15 : Word) := by rw [hi7]; decide
  have h18 : cpsTripleWithin 1 (K + 72) (K + 76)
      (CodeReq.singleton (K + 72) (.LI .x5 (1 : Word)))
      ((.x5 ↦ᵣ v5)) ((.x5 ↦ᵣ (1 : Word))) :=
    li_spec_gen_within .x5 v5 (1 : Word) (K + 72) (by decide)
  have h18C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 72) k67Prog 18 (.LI .x5 (1 : Word))
      (by unfold K; bv_omega)
      (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h18

  have hG18 : ((.x1 ↦ᵣ (K + 68))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ cursor)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x20 ↦ᵣ iW)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree :=
    by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp

  have h18F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (K + 68))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ cursor)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x20 ↦ᵣ iW)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
    hG18 h18C

  have h19 := bne_spec_gen_within .x20 .x5 (12 : BitVec 13) iW (1 : Word) (K + 76)
  rw [show (K + 76 + 4 : Word) = K + 80 from by bv_omega,
    show (K + 76) + signExtend13 (12 : BitVec 13) = K + 88 from by
      rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega] at h19
  have h19C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 76) k67Prog 19 (.BNE .x20 .x5 (12 : BitVec 13))
      (by unfold K; bv_omega)
      (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h19

  have h19t := cpsBranchWithin_takenStripPure2 h19C
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      first
        | exact absurd ((sepConj_pure_right _).1 hBP).2 hi7o1
        | exact hi7o1 ((sepConj_pure_right _).1 hBP).2)
  have hG19 : ((.x1 ↦ᵣ (K + 68))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ cursor)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree :=
    by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp

  have h19tF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (K + 68))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ cursor)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
    hG19 h19t

  have h22 : cpsTripleWithin 1 (K + 88) (K + 92)
      (CodeReq.singleton (K + 88) (.LI .x5 (7 : Word)))
      ((.x5 ↦ᵣ (1 : Word))) ((.x5 ↦ᵣ (7 : Word))) :=
    li_spec_gen_within .x5 (1 : Word) (7 : Word) (K + 88) (by decide)
  have h22C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 88) k67Prog 22 (.LI .x5 (7 : Word))
      (by unfold K; bv_omega)
      (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h22

  have hG22 : ((.x1 ↦ᵣ (K + 68))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ cursor)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x20 ↦ᵣ iW)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree :=
    by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp

  have h22F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (K + 68))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ cursor)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x20 ↦ᵣ iW)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
    hG22 h22C

  have h23 := bne_spec_gen_within .x20 .x5 (8 : BitVec 13) iW (7 : Word) (K + 92)
  rw [show (K + 92 + 4 : Word) = K + 96 from by bv_omega,
    show (K + 92) + signExtend13 (8 : BitVec 13) = K + 100 from by
      rw [show signExtend13 (8 : BitVec 13) = (8 : Word) from by decide]; bv_omega] at h23
  have h23C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 92) k67Prog 23 (.BNE .x20 .x5 (8 : BitVec 13))
      (by unfold K; bv_omega)
      (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h23

  have h23n := cpsBranchWithin_ntakenStripPure2 h23C
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      rw [hi7] at hBP
      exact ((sepConj_pure_right _).1 hBP).2 rfl)
  have hG23 : ((.x1 ↦ᵣ (K + 68))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ cursor)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree :=
    by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp

  have h23nF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (K + 68))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ cursor)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
    hG23 h23n

  have h24 := bne_spec_gen_within .x12 .x0 (508 : BitVec 13) lenW (0 : Word) (K + 96)
  rw [show (K + 96 + 4 : Word) = K + 100 from by bv_omega,
    show (K + 96) + signExtend13 (508 : BitVec 13) = K + 604 from by
      rw [show signExtend13 (508 : BitVec 13) = (508 : Word) from by decide]; bv_omega] at h24
  have h24C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 96) k67Prog 24 (.BNE .x12 .x0 (508 : BitVec 13))
      (by unfold K; bv_omega)
      (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h24

  have h24n := cpsBranchWithin_ntakenStripPure2 h24C
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      rw [hlen0] at hBP
      exact ((sepConj_pure_right _).1 hBP).2 rfl)
  have hG24 : ((.x1 ↦ᵣ (K + 68))
      ** (.x5 ↦ᵣ (7 : Word))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ cursor)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x20 ↦ᵣ iW)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree :=
    by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp

  have h24nF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (K + 68))
      ** (.x5 ↦ᵣ (7 : Word))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ cursor)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x20 ↦ᵣ iW)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
    hG24 h24n

  have h25 : cpsTripleWithin 1 (K + 100) (K + 104)
      (CodeReq.singleton (K + 100) (.MV .x18 .x10))
      ((.x10 ↦ᵣ next) ** (.x18 ↦ᵣ cursor)) ((.x10 ↦ᵣ next) ** (.x18 ↦ᵣ next)) :=
    mv_spec_gen_within .x18 .x10 next cursor (K + 100) (by decide)
  have h25C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 100) k67Prog 25 (.MV .x18 .x10)
      (by unfold K; bv_omega)
      (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h25

  have hG25 : ((.x1 ↦ᵣ (K + 68))
      ** (.x5 ↦ᵣ (7 : Word))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x20 ↦ᵣ iW)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree :=
    by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp

  have h25F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (K + 68))
      ** (.x5 ↦ᵣ (7 : Word))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x20 ↦ᵣ iW)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
    hG25 h25C

  have h26 : cpsTripleWithin 1 (K + 104) (K + 108)
      (CodeReq.singleton (K + 104) (.ADDI .x20 .x20 (1 : BitVec 12)))
      ((.x20 ↦ᵣ iW)) ((.x20 ↦ᵣ (iW + signExtend12 (1 : BitVec 12)))) :=
    addi_spec_gen_same_within .x20 iW (1 : BitVec 12) (K + 104) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at h26
  have h26C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 104) k67Prog 26 (.ADDI .x20 .x20 (1 : BitVec 12))
      (by unfold K; bv_omega)
      (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h26

  have hG26 : ((.x1 ↦ᵣ (K + 68))
      ** (.x5 ↦ᵣ (7 : Word))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ next)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree :=
    by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp

  have h26F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (K + 68))
      ** (.x5 ↦ᵣ (7 : Word))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ next)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
    hG26 h26C

  have h27 : cpsTripleWithin 1 (K + 108) (K + 112)
      (CodeReq.singleton (K + 108) (.LI .x5 (15 : Word)))
      ((.x5 ↦ᵣ (7 : Word))) ((.x5 ↦ᵣ (15 : Word))) :=
    li_spec_gen_within .x5 (7 : Word) (15 : Word) (K + 108) (by decide)
  have h27C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 108) k67Prog 27 (.LI .x5 (15 : Word))
      (by unfold K; bv_omega)
      (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h27

  have hG27 : ((.x1 ↦ᵣ (K + 68))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ next)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x20 ↦ᵣ (iW + (1 : Word)))
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree :=
    by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp

  have h27F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (K + 68))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ next)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x20 ↦ᵣ (iW + (1 : Word)))
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
    hG27 h27C

  have h28 := bne_spec_gen_within .x20 .x5 (-56 : BitVec 13)
    (iW + (1 : Word)) (15 : Word) (K + 112)
  rw [show (K + 112 + 4 : Word) = K + 116 from by bv_omega,
    show (K + 112) + signExtend13 (-56 : BitVec 13) = K + 56 from by
      rw [show signExtend13 (-56 : BitVec 13) = (-56 : Word) from by decide]; bv_omega] at h28
  have h28C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 112) k67Prog 28 (.BNE .x20 .x5 (-56 : BitVec 13))
      (by unfold K; bv_omega)
      (by rw [k67_length]; decide) rfl
      (by rw [k67_length]; decide)) h28

  have h28t := cpsBranchWithin_takenStripPure2 h28C
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      first
        | exact absurd ((sepConj_pure_right _).1 hBP).2 h1514
        | exact h1514 ((sepConj_pure_right _).1 hBP).2)
  have hG28 : ((.x1 ↦ᵣ (K + 68))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ next)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree :=
    by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp

  have h28tF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (K + 68))
      ** (.x6 ↦ᵣ v6)
      ** (.x7 ↦ᵣ v7)
      ** (.x10 ↦ᵣ next)
      ** (.x11 ↦ᵣ (0 : Word))
      ** (.x12 ↦ᵣ lenW)
      ** (.x8 ↦ᵣ v8)
      ** (.x9 ↦ᵣ v9)
      ** (.x18 ↦ᵣ next)
      ** (.x19 ↦ᵣ endPtr)
      ** (.x21 ↦ᵣ v21)
      ** (.x28 ↦ᵣ v28)
      ** (.x29 ↦ᵣ v29)
      ** (.x30 ↦ᵣ v30)
      ** (.x31 ↦ᵣ v31)
      ** regOwn .x13 ** regOwn .x14
      ** (.x0 ↦ᵣ (0 : Word))
      ** frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals
      ** bytesRegion base bytes
      ** bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
    hG28 h28t

  have hA := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h18F h19tF
  have hB := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hA h22F
  have hC := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hB h23nF
  have hD := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hC h24nF
  have hE := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hD h25F
  have hF := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hE h26F
  have hG2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hF h27F
  have hH := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hG2 h28tF
  exact cpsTripleWithin_extend_code k67_mono
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hH)
set_option maxRecDepth 4000 in
/-- Loop-exit arm (i = 14): both guards skip, index advances to 15,
    back-edge BNE falls through to the nonce tail entry at K+116.
    Traversal-order note: the walk visits fields ASCENDING 0..14 with a
    strictly advancing cursor; no read-then-write aliasing per iteration. -/
theorem k67LoopExit (sp0 base omConst cursor endPtr lenW iW next v21 v5 v6 v7 v8 v9 v28 v29 v30 v31 : Word)
    (bytes : List (BitVec 8)) (svals : Reg → Word)
    (hi14eq : iW = (14 : Word)) :
    cpsTripleWithin 8 (K + 72) (K + 116) fullCode
      ((.x1 ↦ᵣ (K + 68)) **
      (.x5 ↦ᵣ v5) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ cursor) **
      (.x19 ↦ᵣ endPtr) **
      (.x20 ↦ᵣ iW) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8)))
      ((.x1 ↦ᵣ (K + 68)) **
      (.x5 ↦ᵣ (15 : Word)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ next) **
      (.x19 ↦ᵣ endPtr) **
      (.x20 ↦ᵣ (iW + (1 : Word))) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) := by
  have hi14o1 : iW ≠ (1 : Word) := by rw [hi14eq]; decide
  have hi14o7 : iW ≠ (7 : Word) := by rw [hi14eq]; decide
  have h15eq : (iW + (1 : Word)) = (15 : Word) := by rw [hi14eq]; decide
  have h18 : cpsTripleWithin 1 (K + 72) (K + 76) (CodeReq.singleton (K + 72) (.LI .x5 (1 : Word)))
      ((.x5 ↦ᵣ v5)) ((.x5 ↦ᵣ (1 : Word))) := li_spec_gen_within .x5 v5 (1 : Word) (K + 72) (by decide)
  have h18C := cpsTripleWithin_extend_code (CodeReq.ofProg_mem_at K (K + 72) k67Prog 18 (.LI .x5 (1 : Word))
    (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h18
  have hG18 : ((.x1 ↦ᵣ (K + 68)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ cursor) **
      (.x19 ↦ᵣ endPtr) **
      (.x20 ↦ᵣ iW) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp
  have h18F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ cursor) **
      (.x19 ↦ᵣ endPtr) **
      (.x20 ↦ᵣ iW) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG18 h18C
  have h19 := bne_spec_gen_within .x20 .x5 (12 : BitVec 13) iW (1 : Word) (K + 76)
  rw [show (K + 76 + 4 : Word) = K + 80 from by bv_omega,
    show (K + 76) + signExtend13 (12 : BitVec 13) = K + 88 from by
      rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega] at h19
  have h19C := cpsBranchWithin_extend_code (CodeReq.ofProg_mem_at K (K + 76) k67Prog 19 (.BNE .x20 .x5 (12 : BitVec 13))
    (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h19
  have h19t := cpsBranchWithin_takenStripPure2 h19C (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hBP⟩ := hQf
    first
      | exact absurd ((sepConj_pure_right _).1 hBP).2 hi14o1
      | exact hi14o1 ((sepConj_pure_right _).1 hBP).2)
  have hG19 : ((.x1 ↦ᵣ (K + 68)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ cursor) **
      (.x19 ↦ᵣ endPtr) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp
  have h19tF := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ cursor) **
      (.x19 ↦ᵣ endPtr) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG19 h19t
  have h22 : cpsTripleWithin 1 (K + 88) (K + 92) (CodeReq.singleton (K + 88) (.LI .x5 (7 : Word)))
      ((.x5 ↦ᵣ (1 : Word))) ((.x5 ↦ᵣ (7 : Word))) := li_spec_gen_within .x5 (1 : Word) (7 : Word) (K + 88) (by decide)
  have h22C := cpsTripleWithin_extend_code (CodeReq.ofProg_mem_at K (K + 88) k67Prog 22 (.LI .x5 (7 : Word))
    (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h22
  have hG22 : ((.x1 ↦ᵣ (K + 68)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ cursor) **
      (.x19 ↦ᵣ endPtr) **
      (.x20 ↦ᵣ iW) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp
  have h22F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ cursor) **
      (.x19 ↦ᵣ endPtr) **
      (.x20 ↦ᵣ iW) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG22 h22C
  have h23 := bne_spec_gen_within .x20 .x5 (8 : BitVec 13) iW (7 : Word) (K + 92)
  rw [show (K + 92 + 4 : Word) = K + 96 from by bv_omega,
    show (K + 92) + signExtend13 (8 : BitVec 13) = K + 100 from by
      rw [show signExtend13 (8 : BitVec 13) = (8 : Word) from by decide]; bv_omega] at h23
  have h23C := cpsBranchWithin_extend_code (CodeReq.ofProg_mem_at K (K + 92) k67Prog 23 (.BNE .x20 .x5 (8 : BitVec 13))
    (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h23
  have h23t := cpsBranchWithin_takenStripPure2 h23C (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hBP⟩ := hQf
    first
      | exact absurd ((sepConj_pure_right _).1 hBP).2 hi14o7
      | exact hi14o7 ((sepConj_pure_right _).1 hBP).2)
  have hG23 : ((.x1 ↦ᵣ (K + 68)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ cursor) **
      (.x19 ↦ᵣ endPtr) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp
  have h23tF := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ cursor) **
      (.x19 ↦ᵣ endPtr) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG23 h23t
  have h25 : cpsTripleWithin 1 (K + 100) (K + 104) (CodeReq.singleton (K + 100) (.MV .x18 .x10))
      ((.x10 ↦ᵣ next) ** (.x18 ↦ᵣ cursor)) ((.x10 ↦ᵣ next) ** (.x18 ↦ᵣ next)) :=
    mv_spec_gen_within .x18 .x10 next cursor (K + 100) (by decide)
  have h25C := cpsTripleWithin_extend_code (CodeReq.ofProg_mem_at K (K + 100) k67Prog 25 (.MV .x18 .x10)
    (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h25
  have hG25 : ((.x1 ↦ᵣ (K + 68)) **
      (.x5 ↦ᵣ (7 : Word)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x19 ↦ᵣ endPtr) **
      (.x20 ↦ᵣ iW) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp
  have h25F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) **
      (.x5 ↦ᵣ (7 : Word)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x19 ↦ᵣ endPtr) **
      (.x20 ↦ᵣ iW) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG25 h25C
  have h26 : cpsTripleWithin 1 (K + 104) (K + 108) (CodeReq.singleton (K + 104) (.ADDI .x20 .x20 (1 : BitVec 12)))
      ((.x20 ↦ᵣ iW)) ((.x20 ↦ᵣ (iW + signExtend12 (1 : BitVec 12)))) :=
    addi_spec_gen_same_within .x20 iW (1 : BitVec 12) (K + 104) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at h26
  have h26C := cpsTripleWithin_extend_code (CodeReq.ofProg_mem_at K (K + 104) k67Prog 26 (.ADDI .x20 .x20 (1 : BitVec 12))
    (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h26
  have hG26 : ((.x1 ↦ᵣ (K + 68)) **
      (.x5 ↦ᵣ (7 : Word)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ next) **
      (.x19 ↦ᵣ endPtr) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp
  have h26F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) **
      (.x5 ↦ᵣ (7 : Word)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ next) **
      (.x19 ↦ᵣ endPtr) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG26 h26C
  have h27 : cpsTripleWithin 1 (K + 108) (K + 112) (CodeReq.singleton (K + 108) (.LI .x5 (15 : Word)))
      ((.x5 ↦ᵣ (7 : Word))) ((.x5 ↦ᵣ (15 : Word))) := li_spec_gen_within .x5 (7 : Word) (15 : Word) (K + 108) (by decide)
  have h27C := cpsTripleWithin_extend_code (CodeReq.ofProg_mem_at K (K + 108) k67Prog 27 (.LI .x5 (15 : Word))
    (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h27
  have hG27 : ((.x1 ↦ᵣ (K + 68)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ next) **
      (.x19 ↦ᵣ endPtr) **
      (.x20 ↦ᵣ (iW + (1 : Word))) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp
  have h27F := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ next) **
      (.x19 ↦ᵣ endPtr) **
      (.x20 ↦ᵣ (iW + (1 : Word))) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG27 h27C
  have h28 := bne_spec_gen_within .x20 .x5 (-56 : BitVec 13) (iW + (1 : Word)) (15 : Word) (K + 112)
  rw [show (K + 112 + 4 : Word) = K + 116 from by bv_omega,
    show (K + 112) + signExtend13 (-56 : BitVec 13) = K + 56 from by
      rw [show signExtend13 (-56 : BitVec 13) = (-56 : Word) from by decide]; bv_omega] at h28
  have h28C := cpsBranchWithin_extend_code (CodeReq.ofProg_mem_at K (K + 112) k67Prog 28 (.BNE .x20 .x5 (-56 : BitVec 13))
    (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) h28
  have h28n := cpsBranchWithin_ntakenStripPure2 h28C (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hBP⟩ := hQf
    rw [h15eq] at hBP
    exact ((sepConj_pure_right _).1 hBP).2 rfl)
  have hG28 : ((.x1 ↦ᵣ (K + 68)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ next) **
      (.x19 ↦ᵣ endPtr) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))).pcFree := by
    repeat' first
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_regOwn
      | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
      | exact pcFree_emp
  have h28nF := cpsTripleWithin_frameR ((.x1 ↦ᵣ (K + 68)) **
      (.x6 ↦ᵣ v6) **
      (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ next) **
      (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ lenW) **
      (.x8 ↦ᵣ v8) **
      (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ next) **
      (.x19 ↦ᵣ endPtr) **
      (.x21 ↦ᵣ v21) **
      (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes **
      bytesRegion omConst (List.replicate 32 (0 : BitVec 8))) hG28 h28n
  have hA := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h18F h19tF
  have hB := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hA h22F
  have hC := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hB h23tF
  have hD := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hC h25F
  have hE := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hD h26F
  have hF := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hE h27F
  have hG2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hF h28nF
  exact cpsTripleWithin_extend_code k67_mono
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hG2)
end EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec
