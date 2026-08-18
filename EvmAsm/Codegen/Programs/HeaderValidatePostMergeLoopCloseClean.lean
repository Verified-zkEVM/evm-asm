import EvmAsm.Codegen.Programs.HeaderValidatePostMergeLoopClose

namespace EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

/-! Clean-station continuations split from `HeaderValidatePostMergeLoopClose`:
    the zero-length difficulty arm and the i=14 clean loop exit. -/

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
