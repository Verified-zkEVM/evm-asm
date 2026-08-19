/-
  K67 `header_validate_post_merge` — final assembly: stations → tails →
  epilogue → the adapter-shaped whole-routine `cpsTripleWithin`.

  `k67ToStations` (HeaderValidatePostMergeTop.lean) delivers control at the six
  stations with the semantic posts.  This file continues each station through
  its status tail (`k67StatusTail0..4`, 2 steps) and the shared epilogue
  (`k67Epilogue`, 8 steps) to the return address, collapsing to a single
  Hoare triple via `cpsNBranchWithin_merge`.  The final post is the five-way
  disjunction of `postMergeCalleePost` at statuses 0/1/2/3/4 (status 4 covers
  both the walker-failure and the init-failure stations), which is exactly the
  shape `validate_header_post_merge_call_spec_within`
  (ValidateHeaderPostMergeCorrespondence.lean) consumes.
-/
import EvmAsm.Codegen.Programs.HeaderValidatePostMergeTop
import EvmAsm.Codegen.RegionMap

namespace EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpWalkNextStrictFuel
open EvmAsm.Codegen.RlpListNthItemSAsm

/-! ## Helpers: pin→own conversion and frame unfoldings -/

/-- Nine-pin analogue of `k67Pins10_to_regOwns`, converting the tail-destined
    pin chain (x5, x6, x7, x11, x12, x28, x29, x30, x31) to `regOwn`s. -/
theorem k67Pins9_to_regOwns :
    ∀ (v5 v6 v7 v11 v12 v28 v29 v30 v31 : Word) h,
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
        (.x12 ↦ᵣ v12) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31)) h →
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) h := by
  intro v5 v6 v7 v11 v12 v28 v29 v30 v31 h hp
  obtain ⟨g0, g8, d0, u0, h5, hp⟩ := hp
  obtain ⟨g1, g7, d1, u1, h6, hp⟩ := hp
  obtain ⟨g2, g6, d2, u2, h7, hp⟩ := hp
  obtain ⟨g3, g5, d3, u3, h11, hp⟩ := hp
  obtain ⟨g4, g4', d4, u4, h12, hp⟩ := hp
  obtain ⟨g5', g3', d5, u5, h28, hp⟩ := hp
  obtain ⟨g6', g2', d6, u6, h29, hp⟩ := hp
  obtain ⟨g7', g1', d7, u7, h30, h31⟩ := hp
  exact ⟨g0, g8, d0, u0, ⟨v5, h5⟩,
    g1, g7, d1, u1, ⟨v6, h6⟩,
    g2, g6, d2, u2, ⟨v7, h7⟩,
    g3, g5, d3, u3, ⟨v11, h11⟩,
    g4, g4', d4, u4, ⟨v12, h12⟩,
    g5', g3', d5, u5, ⟨v28, h28⟩,
    g6', g2', d6, u6, ⟨v29, h29⟩,
    g7', g1', d7, u7, ⟨v30, h30⟩, ⟨v31, h31⟩⟩

/-- Three-pin variant for the init-failure station (x10, x11, x12 → owns). -/
theorem k67Pins101112_to_regOwns :
    ∀ (v10 v11 v12 : Word) h,
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12)) h →
      (regOwn .x10 ** regOwn .x11 ** regOwn .x12) h := by
  intro v10 v11 v12 h hp
  obtain ⟨g0, g1, d0, u0, h10, hp⟩ := hp
  obtain ⟨g1', g2, d1, u1, h11, h12⟩ := hp
  exact ⟨g0, g1, d0, u0, ⟨v10, h10⟩, g1', g2, d1, u1, ⟨v11, h11⟩, ⟨v12, h12⟩⟩

/-- The station-carried frame, unfolded to the six `memIs` conjuncts the status
    tails and the epilogue expect (with the saved-value function computed). -/
theorem k67FrameSaved_unfold (spC Ret : Word) (vals : Reg → Word) :
    frameSlotsSaved k67Frame spC
        (k67PrologueVals Ret (vals .x8) (vals .x9) (vals .x18) (vals .x19)
          (vals .x20)) =
      ((spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ (vals .x8)) **
        ((spC + 16) ↦ₘ (vals .x9)) ** ((spC + 24) ↦ₘ (vals .x18)) **
        ((spC + 32) ↦ₘ (vals .x19)) ** ((spC + 40) ↦ₘ (vals .x20))) := by
  simp only [k67Frame, frameSlotsSaved_cons, frameSlotsSaved_nil,
    k67PrologueVals, sepConj_emp_right']
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
    show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]
  rw [show spC + 0 = spC from by bv_omega]

/-- The adapter's saved-frame assertion, unfolded the same way (the two value
    functions agree on the six frame registers). -/
theorem k67PostMergeFrameSaved_unfold (spC Ret : Word) (vals : Reg → Word) :
    frameSlotsSaved ValidateHeaderPostMergeCorrespondence.postMergeFrame spC
        (ValidateHeaderPostMergeCorrespondence.postMergeFrameVals Ret vals) =
      ((spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ (vals .x8)) **
        ((spC + 16) ↦ₘ (vals .x9)) ** ((spC + 24) ↦ₘ (vals .x18)) **
        ((spC + 32) ↦ₘ (vals .x19)) ** ((spC + 40) ↦ₘ (vals .x20))) := by
  have hx8 : ¬ (Reg.x8 = Reg.x1) := by decide
  have hx9 : ¬ (Reg.x9 = Reg.x1) := by decide
  have hx18 : ¬ (Reg.x18 = Reg.x1) := by decide
  have hx19 : ¬ (Reg.x19 = Reg.x1) := by decide
  have hx20 : ¬ (Reg.x20 = Reg.x1) := by decide
  simp only [ValidateHeaderPostMergeCorrespondence.postMergeFrame,
    frameSlotsSaved_cons, frameSlotsSaved_nil,
    ValidateHeaderPostMergeCorrespondence.postMergeFrameVals,
    sepConj_emp_right', if_true, hx8, hx9, hx18, hx19, hx20,
    if_false]
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
    show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]
  rw [show spC + 0 = spC from by bv_omega]

/-- The adapter's saved-register assertion, unfolded to the four pins. -/
theorem k67RegsAtSaved_unfold (vals : Reg → Word) :
    regsAt ValidateHeaderPostMergeCorrespondence.postMergeSavedFrame vals =
      ((.x8 ↦ᵣ (vals .x8)) ** (.x9 ↦ᵣ (vals .x9)) ** (.x18 ↦ᵣ (vals .x18)) **
        (.x19 ↦ᵣ (vals .x19))) := by
  simp only [ValidateHeaderPostMergeCorrespondence.postMergeSavedFrame,
    regsAt_cons, regsAt_nil, sepConj_emp_right']

/-- The adapter's frame ownership, unfolded to the six `memOwn` conjuncts. -/
theorem k67FrameOwn_unfold (spC : Word) :
    frameSlotsOwn ValidateHeaderPostMergeCorrespondence.postMergeFrame spC =
      (memOwn spC ** memOwn (spC + 8) ** memOwn (spC + 16) ** memOwn (spC + 24) **
        memOwn (spC + 32) ** memOwn (spC + 40)) := by
  simp only [ValidateHeaderPostMergeCorrespondence.postMergeFrame,
    frameSlotsOwn_cons, frameSlotsOwn_nil, sepConj_emp_right']
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
    show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]
  rw [show spC + 0 = spC from by bv_omega]

/-- The five-way return post: the adapter's `postMergeCalleePost` at each
    status code. -/
def k67PostRet (sp0 header : Word) (Ret s5 : Word) (vals : Reg → Word)
    (bytes : List (BitVec 8)) : Assertion := fun h =>
  (ValidateHeaderPostMergeCorrespondence.postMergeCalleePost sp0 header
      (vals .x20) s5 Ret (0 : Word) vals bytes) h ∨
  (ValidateHeaderPostMergeCorrespondence.postMergeCalleePost sp0 header
      (vals .x20) s5 Ret (1 : Word) vals bytes) h ∨
  (ValidateHeaderPostMergeCorrespondence.postMergeCalleePost sp0 header
      (vals .x20) s5 Ret (2 : Word) vals bytes) h ∨
  (ValidateHeaderPostMergeCorrespondence.postMergeCalleePost sp0 header
      (vals .x20) s5 Ret (3 : Word) vals bytes) h ∨
  (ValidateHeaderPostMergeCorrespondence.postMergeCalleePost sp0 header
      (vals .x20) s5 Ret (4 : Word) vals bytes) h

/-- Two-pin conversion for the init-failure station (x11/x12 are the only
    pins needing `regOwn` in the tail pre there). -/
theorem k67Pins1112_to_regOwns :
    ∀ (v11 v12 : Word) h,
      ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12)) h →
      (regOwn .x11 ** regOwn .x12) h := by
  intro v11 v12 h hp
  obtain ⟨g0, g1, d0, u0, h11, h12⟩ := hp
  exact ⟨g0, g1, d0, u0, ⟨v11, h11⟩, ⟨v12, h12⟩⟩

/-! ## §3  Six-station merge: `K`-entry to `Ret` -/

/-- The whole routine from its entry `K` to the caller return address `Ret`:
    the six stations of `k67ToStations` are each continued through their
    status stub (`k67StatusTail0..4`) and the register-restore epilogue
    (`k67Epilogue`), landing in the `k67PostRet` disjunctive post with the
    status code matching the station. -/
theorem k67ToRet (sp0 header : Word) (bytes : List (BitVec 8))
    (Ret s5 : Word) (vals : Reg → Word)
    (v12 v5 v6 v7 v28 v29 v30 v31 : Word)
    (hsalign : header.toNat % 8 = 0)
    (hoff : 0 < bytes.length)
    (hover9 : header.toNat + bytes.length + 9 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (header + BitVec.ofNat 64 k) = true)
    (hll_len : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ¬ BitVec.ult
        ((header + BitVec.ofNat 64 0) + BitVec.ofNat 64 bytes.length)
        ((header + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      0 + 1 + ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤
        bytes.length)
    (hll_over : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ¬ BitVec.ult
        ((header + BitVec.ofNat 64 0) + BitVec.ofNat 64 bytes.length)
        ((header + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      header.toNat +
        (0 + 1 + ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤
        2 ^ 64)
    (hll_valid : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ¬ BitVec.ult
        ((header + BitVec.ofNat 64 0) + BitVec.ofNat 64 bytes.length)
        ((header + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      ∀ k, k < ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
        isValidByteAccess (header + BitVec.ofNat 64 (0 + 1 + k)) = true)
    (hret : Ret &&& ~~~(1 : Word) = Ret) :
    cpsTripleWithin
      (((10 + (1 + 81) + (1 + 2)) + 101 * (2 * bytes.length + 1) + 124) + 10)
      K Ret fullCode
      ((.x1 ↦ᵣ Ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ (vals .x8)) **
        (.x9 ↦ᵣ (vals .x9)) ** (.x18 ↦ᵣ (vals .x18)) **
        (.x19 ↦ᵣ (vals .x19)) ** (.x20 ↦ᵣ (vals .x20)) ** (.x21 ↦ᵣ s5) **
        (.x10 ↦ᵣ header) ** (.x11 ↦ᵣ BitVec.ofNat 64 bytes.length) **
        (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion header bytes **
        bytesRegion ((GuestAddrs.empty_ommers_hash : Word)) (k67OmBytes) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12)) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 8) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 16) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 24) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 32) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 40))
      (k67PostRet sp0 header Ret s5 vals bytes) :=
  cpsNBranchWithin_merge
    (k67ToStations sp0 header bytes Ret (vals .x8) (vals .x9) (vals .x18)
      (vals .x19) (vals .x20) s5 v12 v5 v6 v7 v28 v29 v30 v31 hsalign hoff
      hover9 hvalid hll_len hll_over hll_valid)
    (by
      intro ex hex
      simp only [List.mem_cons] at hex
      rcases hex with hex | hex | hex | hex | hex | hex | hnil
      · -- clean run: status 0
        subst hex
        apply cpsTripleWithin_exists_pre_gen; intro _startOff
        apply cpsTripleWithin_exists_pre_gen; intro next14
        apply cpsTripleWithin_exists_pre_gen; intro len14
        apply cpsTripleWithin_exists_pre_gen; intro n1
        apply cpsTripleWithin_exists_pre_gen; intro l1
        apply cpsTripleWithin_exists_pre_gen; intro v29
        apply cpsTripleWithin_exists_pre_gen; intro v30
        apply cpsTripleWithin_exists_pre_gen; intro v31
        have htail := k67StatusTail0 (sp0 + signExtend12 (-48 : BitVec 12))
          header ((GuestAddrs.empty_ommers_hash : Word)) Ret (vals .x8)
          (vals .x9) (vals .x18) (vals .x19) (vals .x20) s5 (K + 68)
          (header + BitVec.ofNat 64 (n1 - header).toNat)
          (BitVec.ofNat 64 l1.toNat) next14
          (header + BitVec.ofNat 64 bytes.length) (15 : Word) next14 bytes
        have hep := k67Epilogue sp0 (sp0 + signExtend12 (-48 : BitVec 12))
          header ((GuestAddrs.empty_ommers_hash : Word)) Ret (vals .x8)
          (vals .x9) (vals .x18) (vals .x19) (vals .x20) s5 (K + 68)
          (header + BitVec.ofNat 64 (n1 - header).toNat)
          (BitVec.ofNat 64 l1.toNat) next14
          (header + BitVec.ofNat 64 bytes.length) (15 : Word) (0 : Word)
          bytes rfl hret
        have hseq := cpsTripleWithin_seq_perm_same_cr
          (fun _ hp => by xperm_hyp hp) htail hep
        have hseqM := cpsTripleWithin_mono_nSteps
          (show 2 + (7 + 1) ≤ 10 from by omega) hseq
        refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hseqM
        · unfold k67QOk at hp
          obtain ⟨hq, -⟩ := (sepConj_pure_right _).1 hp
          rw [k67FrameSaved_unfold (sp0 + signExtend12 (-48 : BitVec 12))
            Ret vals] at hq
          have hP : (((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
              (.x10 ↦ᵣ next14) ** (.x21 ↦ᵣ s5) ** (.x1 ↦ᵣ (K + 68)) **
              (.x8 ↦ᵣ (header + BitVec.ofNat 64 (n1 - header).toNat)) **
              (.x9 ↦ᵣ BitVec.ofNat 64 l1.toNat) ** (.x18 ↦ᵣ next14) **
              (.x19 ↦ᵣ (header + BitVec.ofNat 64 bytes.length)) **
              (.x20 ↦ᵣ (15 : Word)) ** regOwn .x13 ** regOwn .x14 **
              (.x0 ↦ᵣ (0 : Word)) **
              ((sp0 + signExtend12 (-48 : BitVec 12)) ↦ₘ Ret) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 8) ↦ₘ (vals .x8)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 16) ↦ₘ (vals .x9)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 24) ↦ₘ (vals .x18)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 32) ↦ₘ (vals .x19)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 40) ↦ₘ (vals .x20)) **
              bytesRegion header bytes **
              bytesRegion ((GuestAddrs.empty_ommers_hash : Word))
                (k67OmBytes)) **
              ((.x5 ↦ᵣ ((GuestAddrs.empty_ommers_hash : Word))) **
                (.x6 ↦ᵣ ((header + BitVec.ofNat 64 (n1 - header).toNat) -
                  BitVec.ofNat 64 l1.toNat)) **
                (.x7 ↦ᵣ ((k67OmBytes.getD 31 (0 : BitVec 8)).zeroExtend 64)) **
                (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
                (.x28 ↦ᵣ ((k67OmBytes.getD 31 (0 : BitVec 8)).zeroExtend
                  64)) **
                (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))) h := by
            xperm_hyp hq
          have hC := sepConj_mono_right
            (k67Pins9_to_regOwns ((GuestAddrs.empty_ommers_hash : Word))
              ((header + BitVec.ofNat 64 (n1 - header).toNat) -
                BitVec.ofNat 64 l1.toNat)
              ((k67OmBytes.getD 31 (0 : BitVec 8)).zeroExtend 64) (0 : Word)
              len14 ((k67OmBytes.getD 31 (0 : BitVec 8)).zeroExtend 64)
              v29 v30 v31) h hP
          xperm_hyp hC
        · unfold k67PostRet
          refine Or.inl ?_
          unfold ValidateHeaderPostMergeCorrespondence.postMergeCalleePost
          rw [k67PostMergeFrameSaved_unfold
            (sp0 + signExtend12 (-48 : BitVec 12)) Ret vals,
            k67RegsAtSaved_unfold vals]
          xperm_hyp hq
      · -- ommers mismatch: status 3
        subst hex
        apply cpsTripleWithin_exists_pre_gen; intro _startOff
        apply cpsTripleWithin_exists_pre_gen; intro next14
        apply cpsTripleWithin_exists_pre_gen; intro len14
        apply cpsTripleWithin_exists_pre_gen; intro n1
        apply cpsTripleWithin_exists_pre_gen; intro l1
        apply cpsTripleWithin_exists_pre_gen; intro v29
        apply cpsTripleWithin_exists_pre_gen; intro v30
        apply cpsTripleWithin_exists_pre_gen; intro v31
        have htail := k67StatusTail3 (sp0 + signExtend12 (-48 : BitVec 12))
          header ((GuestAddrs.empty_ommers_hash : Word)) Ret (vals .x8)
          (vals .x9) (vals .x18) (vals .x19) (vals .x20) s5 (K + 68)
          (header + BitVec.ofNat 64 (n1 - header).toNat)
          (BitVec.ofNat 64 l1.toNat) next14
          (header + BitVec.ofNat 64 bytes.length) (15 : Word) next14 bytes
        have hep := k67Epilogue sp0 (sp0 + signExtend12 (-48 : BitVec 12))
          header ((GuestAddrs.empty_ommers_hash : Word)) Ret (vals .x8)
          (vals .x9) (vals .x18) (vals .x19) (vals .x20) s5 (K + 68)
          (header + BitVec.ofNat 64 (n1 - header).toNat)
          (BitVec.ofNat 64 l1.toNat) next14
          (header + BitVec.ofNat 64 bytes.length) (15 : Word) (3 : Word)
          bytes rfl hret
        have hseq := cpsTripleWithin_seq_perm_same_cr
          (fun _ hp => by xperm_hyp hp) htail hep
        have hseqM := cpsTripleWithin_mono_nSteps
          (show 2 + (7 + 1) ≤ 10 from by omega) hseq
        refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hseqM
        · unfold k67QOmmersFail at hp
          obtain ⟨v5o, v6o, v7o, v28o, hp⟩ := hp
          obtain ⟨hq, -⟩ := (sepConj_pure_right _).1 hp
          rw [k67FrameSaved_unfold (sp0 + signExtend12 (-48 : BitVec 12))
            Ret vals] at hq
          have hP : (((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
              (.x10 ↦ᵣ next14) ** (.x21 ↦ᵣ s5) ** (.x1 ↦ᵣ (K + 68)) **
              (.x8 ↦ᵣ (header + BitVec.ofNat 64 (n1 - header).toNat)) **
              (.x9 ↦ᵣ BitVec.ofNat 64 l1.toNat) ** (.x18 ↦ᵣ next14) **
              (.x19 ↦ᵣ (header + BitVec.ofNat 64 bytes.length)) **
              (.x20 ↦ᵣ (15 : Word)) ** regOwn .x13 ** regOwn .x14 **
              (.x0 ↦ᵣ (0 : Word)) **
              ((sp0 + signExtend12 (-48 : BitVec 12)) ↦ₘ Ret) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 8) ↦ₘ (vals .x8)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 16) ↦ₘ (vals .x9)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 24) ↦ₘ (vals .x18)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 32) ↦ₘ (vals .x19)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 40) ↦ₘ (vals .x20)) **
              bytesRegion header bytes **
              bytesRegion ((GuestAddrs.empty_ommers_hash : Word))
                (k67OmBytes)) **
              ((.x5 ↦ᵣ v5o) ** (.x6 ↦ᵣ v6o) ** (.x7 ↦ᵣ v7o) **
                (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
                (.x28 ↦ᵣ v28o) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
                (.x31 ↦ᵣ v31))) h := by
            xperm_hyp hq
          have hC := sepConj_mono_right
            (k67Pins9_to_regOwns v5o v6o v7o (0 : Word) len14 v28o v29 v30
              v31) h hP
          xperm_hyp hC
        · unfold k67PostRet
          refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
          unfold ValidateHeaderPostMergeCorrespondence.postMergeCalleePost
          rw [k67PostMergeFrameSaved_unfold
            (sp0 + signExtend12 (-48 : BitVec 12)) Ret vals,
            k67RegsAtSaved_unfold vals]
          xperm_hyp hq
      · -- nonce violation: status 2
        subst hex
        apply cpsTripleWithin_exists_pre_gen; intro _startOff
        apply cpsTripleWithin_exists_pre_gen; intro next14
        apply cpsTripleWithin_exists_pre_gen; intro len14
        apply cpsTripleWithin_exists_pre_gen; intro n1
        apply cpsTripleWithin_exists_pre_gen; intro l1
        apply cpsTripleWithin_exists_pre_gen; intro v28
        apply cpsTripleWithin_exists_pre_gen; intro v29
        apply cpsTripleWithin_exists_pre_gen; intro v30
        apply cpsTripleWithin_exists_pre_gen; intro v31
        have htail := k67StatusTail2 (sp0 + signExtend12 (-48 : BitVec 12))
          header ((GuestAddrs.empty_ommers_hash : Word)) Ret (vals .x8)
          (vals .x9) (vals .x18) (vals .x19) (vals .x20) s5 (K + 68)
          (header + BitVec.ofNat 64 (n1 - header).toNat)
          (BitVec.ofNat 64 l1.toNat) next14
          (header + BitVec.ofNat 64 bytes.length) (15 : Word) next14 bytes
        have hep := k67Epilogue sp0 (sp0 + signExtend12 (-48 : BitVec 12))
          header ((GuestAddrs.empty_ommers_hash : Word)) Ret (vals .x8)
          (vals .x9) (vals .x18) (vals .x19) (vals .x20) s5 (K + 68)
          (header + BitVec.ofNat 64 (n1 - header).toNat)
          (BitVec.ofNat 64 l1.toNat) next14
          (header + BitVec.ofNat 64 bytes.length) (15 : Word) (2 : Word)
          bytes rfl hret
        have hseq := cpsTripleWithin_seq_perm_same_cr
          (fun _ hp => by xperm_hyp hp) htail hep
        have hseqM := cpsTripleWithin_mono_nSteps
          (show 2 + (7 + 1) ≤ 10 from by omega) hseq
        refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hseqM
        · unfold k67QNonceFail at hp
          obtain ⟨v5o, v6o, v7o, hp⟩ := hp
          obtain ⟨hq, -⟩ := (sepConj_pure_right _).1 hp
          rw [k67FrameSaved_unfold (sp0 + signExtend12 (-48 : BitVec 12))
            Ret vals] at hq
          have hP : (((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
              (.x10 ↦ᵣ next14) ** (.x21 ↦ᵣ s5) ** (.x1 ↦ᵣ (K + 68)) **
              (.x8 ↦ᵣ (header + BitVec.ofNat 64 (n1 - header).toNat)) **
              (.x9 ↦ᵣ BitVec.ofNat 64 l1.toNat) ** (.x18 ↦ᵣ next14) **
              (.x19 ↦ᵣ (header + BitVec.ofNat 64 bytes.length)) **
              (.x20 ↦ᵣ (15 : Word)) ** regOwn .x13 ** regOwn .x14 **
              (.x0 ↦ᵣ (0 : Word)) **
              ((sp0 + signExtend12 (-48 : BitVec 12)) ↦ₘ Ret) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 8) ↦ₘ (vals .x8)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 16) ↦ₘ (vals .x9)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 24) ↦ₘ (vals .x18)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 32) ↦ₘ (vals .x19)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 40) ↦ₘ (vals .x20)) **
              bytesRegion header bytes **
              bytesRegion ((GuestAddrs.empty_ommers_hash : Word))
                (k67OmBytes)) **
              ((.x5 ↦ᵣ v5o) ** (.x6 ↦ᵣ v6o) ** (.x7 ↦ᵣ v7o) **
                (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
                (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
                (.x31 ↦ᵣ v31))) h := by
            xperm_hyp hq
          have hC := sepConj_mono_right
            (k67Pins9_to_regOwns v5o v6o v7o (0 : Word) len14 v28 v29 v30
              v31) h hP
          xperm_hyp hC
        · unfold k67PostRet
          refine Or.inr (Or.inr (Or.inl ?_))
          unfold ValidateHeaderPostMergeCorrespondence.postMergeCalleePost
          rw [k67PostMergeFrameSaved_unfold
            (sp0 + signExtend12 (-48 : BitVec 12)) Ret vals,
            k67RegsAtSaved_unfold vals]
          xperm_hyp hq
      · -- init failure: status 4
        subst hex
        apply cpsTripleWithin_exists_pre_gen; intro v10
        apply cpsTripleWithin_exists_pre_gen; intro v11
        apply cpsTripleWithin_exists_pre_gen; intro v12f
        have htail := k67StatusTail4 (sp0 + signExtend12 (-48 : BitVec 12))
          header ((GuestAddrs.empty_ommers_hash : Word)) Ret (vals .x8)
          (vals .x9) (vals .x18) (vals .x19) (vals .x20) s5 (K + 44)
          header (BitVec.ofNat 64 bytes.length) (vals .x18) (vals .x19)
          (0 : Word) v10 bytes
        have hep := k67Epilogue sp0 (sp0 + signExtend12 (-48 : BitVec 12))
          header ((GuestAddrs.empty_ommers_hash : Word)) Ret (vals .x8)
          (vals .x9) (vals .x18) (vals .x19) (vals .x20) s5 (K + 44)
          header (BitVec.ofNat 64 bytes.length) (vals .x18) (vals .x19)
          (0 : Word) (4 : Word) bytes rfl hret
        have hseq := cpsTripleWithin_seq_perm_same_cr
          (fun _ hp => by xperm_hyp hp) htail hep
        have hseqM := cpsTripleWithin_mono_nSteps
          (show 1 + (7 + 1) ≤ 10 from by omega) hseq
        refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hseqM
        · obtain ⟨hq, -⟩ := (sepConj_pure_right _).1 hp
          rw [k67FrameSaved_unfold (sp0 + signExtend12 (-48 : BitVec 12))
            Ret vals] at hq
          have hP : (((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
              (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ s5) ** (.x1 ↦ᵣ (K + 44)) **
              (.x8 ↦ᵣ header) **
              (.x9 ↦ᵣ BitVec.ofNat 64 bytes.length) **
              (.x18 ↦ᵣ (vals .x18)) ** (.x19 ↦ᵣ (vals .x19)) **
              (.x20 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 **
              regOwn .x7 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
              regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) **
              ((sp0 + signExtend12 (-48 : BitVec 12)) ↦ₘ Ret) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 8) ↦ₘ (vals .x8)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 16) ↦ₘ (vals .x9)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 24) ↦ₘ (vals .x18)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 32) ↦ₘ (vals .x19)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 40) ↦ₘ (vals .x20)) **
              bytesRegion header bytes **
              bytesRegion ((GuestAddrs.empty_ommers_hash : Word))
                (k67OmBytes)) **
              ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12f))) h := by
            xperm_hyp hq
          have hC := sepConj_mono_right (k67Pins1112_to_regOwns v11 v12f)
            h hP
          xperm_hyp hC
        · unfold k67PostRet
          refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
          unfold ValidateHeaderPostMergeCorrespondence.postMergeCalleePost
          rw [k67PostMergeFrameSaved_unfold
            (sp0 + signExtend12 (-48 : BitVec 12)) Ret vals,
            k67RegsAtSaved_unfold vals]
          xperm_hyp hq
      · -- difficulty nonzero: status 1
        subst hex
        apply cpsTripleWithin_exists_pre_gen; intro _startOff
        apply cpsTripleWithin_exists_pre_gen; intro cur
        apply cpsTripleWithin_exists_pre_gen; intro omEnd
        apply cpsTripleWithin_exists_pre_gen; intro omLen
        apply cpsTripleWithin_exists_pre_gen; intro next7
        apply cpsTripleWithin_exists_pre_gen; intro len7
        apply cpsTripleWithin_exists_pre_gen; intro n1
        apply cpsTripleWithin_exists_pre_gen; intro l1
        apply cpsTripleWithin_exists_pre_gen; intro v6
        apply cpsTripleWithin_exists_pre_gen; intro v7
        apply cpsTripleWithin_exists_pre_gen; intro v28d
        apply cpsTripleWithin_exists_pre_gen; intro v29d
        apply cpsTripleWithin_exists_pre_gen; intro v30d
        apply cpsTripleWithin_exists_pre_gen; intro v31d
        have htail := k67StatusTail1 (sp0 + signExtend12 (-48 : BitVec 12))
          header ((GuestAddrs.empty_ommers_hash : Word)) Ret (vals .x8)
          (vals .x9) (vals .x18) (vals .x19) (vals .x20) s5 (K + 68)
          (header + BitVec.ofNat 64 omEnd) (BitVec.ofNat 64 omLen)
          (header + BitVec.ofNat 64 cur)
          (header + BitVec.ofNat 64 bytes.length) (7 : Word) next7 bytes
        have hep := k67Epilogue sp0 (sp0 + signExtend12 (-48 : BitVec 12))
          header ((GuestAddrs.empty_ommers_hash : Word)) Ret (vals .x8)
          (vals .x9) (vals .x18) (vals .x19) (vals .x20) s5 (K + 68)
          (header + BitVec.ofNat 64 omEnd) (BitVec.ofNat 64 omLen)
          (header + BitVec.ofNat 64 cur)
          (header + BitVec.ofNat 64 bytes.length) (7 : Word) (1 : Word)
          bytes rfl hret
        have hseq := cpsTripleWithin_seq_perm_same_cr
          (fun _ hp => by xperm_hyp hp) htail hep
        have hseqM := cpsTripleWithin_mono_nSteps
          (show 2 + (7 + 1) ≤ 10 from by omega) hseq
        refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hseqM
        · obtain ⟨hq, -⟩ := (sepConj_pure_right _).1 hp
          rw [k67FrameSaved_unfold (sp0 + signExtend12 (-48 : BitVec 12))
            Ret vals] at hq
          have hP : (((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
              (.x10 ↦ᵣ next7) ** (.x21 ↦ᵣ s5) ** (.x1 ↦ᵣ (K + 68)) **
              (.x8 ↦ᵣ (header + BitVec.ofNat 64 omEnd)) **
              (.x9 ↦ᵣ BitVec.ofNat 64 omLen) **
              (.x18 ↦ᵣ (header + BitVec.ofNat 64 cur)) **
              (.x19 ↦ᵣ (header + BitVec.ofNat 64 bytes.length)) **
              (.x20 ↦ᵣ (7 : Word)) ** regOwn .x13 ** regOwn .x14 **
              (.x0 ↦ᵣ (0 : Word)) **
              ((sp0 + signExtend12 (-48 : BitVec 12)) ↦ₘ Ret) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 8) ↦ₘ (vals .x8)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 16) ↦ₘ (vals .x9)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 24) ↦ₘ (vals .x18)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 32) ↦ₘ (vals .x19)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 40) ↦ₘ (vals .x20)) **
              bytesRegion header bytes **
              bytesRegion ((GuestAddrs.empty_ommers_hash : Word))
                (k67OmBytes)) **
              ((.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
                (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len7) **
                (.x28 ↦ᵣ v28d) ** (.x29 ↦ᵣ v29d) ** (.x30 ↦ᵣ v30d) **
                (.x31 ↦ᵣ v31d))) h := by
            xperm_hyp hq
          have hC := sepConj_mono_right
            (k67Pins9_to_regOwns (7 : Word) v6 v7 (0 : Word) len7 v28d v29d
              v30d v31d) h hP
          xperm_hyp hC
        · unfold k67PostRet
          refine Or.inr (Or.inl ?_)
          unfold ValidateHeaderPostMergeCorrespondence.postMergeCalleePost
          rw [k67PostMergeFrameSaved_unfold
            (sp0 + signExtend12 (-48 : BitVec 12)) Ret vals,
            k67RegsAtSaved_unfold vals]
          xperm_hyp hq
      · -- walk failure: status 4
        subst hex
        apply cpsTripleWithin_exists_pre_gen; intro _startOff
        apply cpsTripleWithin_exists_pre_gen; intro ifail
        apply cpsTripleWithin_exists_pre_gen; intro cur
        apply cpsTripleWithin_exists_pre_gen; intro statusW
        apply cpsTripleWithin_exists_pre_gen; intro v8f
        apply cpsTripleWithin_exists_pre_gen; intro v9f
        apply cpsTripleWithin_exists_pre_gen; intro v5f
        apply cpsTripleWithin_exists_pre_gen; intro v6f
        apply cpsTripleWithin_exists_pre_gen; intro v7f
        apply cpsTripleWithin_exists_pre_gen; intro v28f
        apply cpsTripleWithin_exists_pre_gen; intro v29f
        apply cpsTripleWithin_exists_pre_gen; intro v30f
        apply cpsTripleWithin_exists_pre_gen; intro v31f
        have htail := k67StatusTail4 (sp0 + signExtend12 (-48 : BitVec 12))
          header ((GuestAddrs.empty_ommers_hash : Word)) Ret (vals .x8)
          (vals .x9) (vals .x18) (vals .x19) (vals .x20) s5 (K + 68) v8f v9f
          (header + BitVec.ofNat 64 cur)
          (header + BitVec.ofNat 64 bytes.length)
          (BitVec.ofNat 64 ifail) (header + BitVec.ofNat 64 cur) bytes
        have hep := k67Epilogue sp0 (sp0 + signExtend12 (-48 : BitVec 12))
          header ((GuestAddrs.empty_ommers_hash : Word)) Ret (vals .x8)
          (vals .x9) (vals .x18) (vals .x19) (vals .x20) s5 (K + 68) v8f v9f
          (header + BitVec.ofNat 64 cur)
          (header + BitVec.ofNat 64 bytes.length)
          (BitVec.ofNat 64 ifail) (4 : Word) bytes rfl hret
        have hseq := cpsTripleWithin_seq_perm_same_cr
          (fun _ hp => by xperm_hyp hp) htail hep
        have hseqM := cpsTripleWithin_mono_nSteps
          (show 1 + (7 + 1) ≤ 10 from by omega) hseq
        refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hseqM
        · obtain ⟨hq, -⟩ := (sepConj_pure_right _).1 hp
          rw [k67FrameSaved_unfold (sp0 + signExtend12 (-48 : BitVec 12))
            Ret vals] at hq
          have hP : (((.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
              (.x10 ↦ᵣ (header + BitVec.ofNat 64 cur)) ** (.x21 ↦ᵣ s5) **
              (.x1 ↦ᵣ (K + 68)) **
              (.x8 ↦ᵣ v8f) ** (.x9 ↦ᵣ v9f) **
              (.x18 ↦ᵣ (header + BitVec.ofNat 64 cur)) **
              (.x19 ↦ᵣ (header + BitVec.ofNat 64 bytes.length)) **
              (.x20 ↦ᵣ BitVec.ofNat 64 ifail) ** regOwn .x13 ** regOwn .x14 **
              (.x0 ↦ᵣ (0 : Word)) **
              ((sp0 + signExtend12 (-48 : BitVec 12)) ↦ₘ Ret) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 8) ↦ₘ (vals .x8)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 16) ↦ₘ (vals .x9)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 24) ↦ₘ (vals .x18)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 32) ↦ₘ (vals .x19)) **
              ((sp0 + signExtend12 (-48 : BitVec 12) + 40) ↦ₘ (vals .x20)) **
              bytesRegion header bytes **
              bytesRegion ((GuestAddrs.empty_ommers_hash : Word))
                (k67OmBytes)) **
              ((.x5 ↦ᵣ v5f) ** (.x6 ↦ᵣ v6f) ** (.x7 ↦ᵣ v7f) **
                (.x11 ↦ᵣ statusW) ** (.x12 ↦ᵣ (0 : Word)) **
                (.x28 ↦ᵣ v28f) ** (.x29 ↦ᵣ v29f) ** (.x30 ↦ᵣ v30f) **
                (.x31 ↦ᵣ v31f))) h := by
            xperm_hyp hq
          have hC := sepConj_mono_right
            (k67Pins9_to_regOwns v5f v6f v7f statusW (0 : Word) v28f v29f
              v30f v31f) h hP
          xperm_hyp hC
        · unfold k67PostRet
          refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
          unfold ValidateHeaderPostMergeCorrespondence.postMergeCalleePost
          rw [k67PostMergeFrameSaved_unfold
            (sp0 + signExtend12 (-48 : BitVec 12)) Ret vals,
            k67RegsAtSaved_unfold vals]
          xperm_hyp hq
      · simp at hnil)

/-! ## §4  The whole-routine triple in adapter shape -/

/-- The whole-routine `header_validate_post_merge` triple in the adapter's
    exact shape: from the `postMergeEntryRest` entry state (plus return address
    `Ret` in `x1`), control returns to `Ret` within the given step bound with
    `k67PostRet` — the five-way disjunction of `postMergeCalleePost` states at
    statuses 0 (ok), 1 (difficulty nonzero), 2 (nonce malformed), 3 (ommers
    mismatch) and 4 (RLP parse failure). -/
theorem header_validate_post_merge_spec_within
    (sp0 header : Word) (bytes : List (BitVec 8))
    (Ret s5 : Word) (vals : Reg → Word)
    (hsalign : header.toNat % 8 = 0)
    (hoff : 0 < bytes.length)
    (hover9 : header.toNat + bytes.length + 9 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (header + BitVec.ofNat 64 k) = true)
    (hll_len : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ¬ BitVec.ult
        ((header + BitVec.ofNat 64 0) + BitVec.ofNat 64 bytes.length)
        ((header + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      0 + 1 + ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤
        bytes.length)
    (hll_over : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ¬ BitVec.ult
        ((header + BitVec.ofNat 64 0) + BitVec.ofNat 64 bytes.length)
        ((header + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      header.toNat +
        (0 + 1 + ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤
        2 ^ 64)
    (hll_valid : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ¬ BitVec.ult
        ((header + BitVec.ofNat 64 0) + BitVec.ofNat 64 bytes.length)
        ((header + BitVec.ofNat 64 0) +
          (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            signExtend12 (1 : BitVec 12))) = true →
      ∀ k, k < ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
        isValidByteAccess (header + BitVec.ofNat 64 (0 + 1 + k)) = true)
    (hret : Ret &&& ~~~(1 : Word) = Ret) :
    cpsTripleWithin (((10 + (1 + 81) + (1 + 2)) + 101 * (2 * bytes.length + 1)
        + 124) + 10) K Ret fullCode
      ((.x1 ↦ᵣ Ret) **
        ValidateHeaderPostMergeCorrespondence.postMergeEntryRest sp0 header
          (BitVec.ofNat 64 bytes.length) (vals .x20) s5 vals bytes)
      (k67PostRet sp0 header Ret s5 vals bytes) := by
  have hinner : cpsNBranchWithin
      (10 + (1 + 81) + (1 + 2) + 101 * (2 * bytes.length + 1) + 124 + 10)
      K fullCode
      (((.x1 ↦ᵣ Ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ (vals .x8)) **
        (.x9 ↦ᵣ (vals .x9)) ** (.x18 ↦ᵣ (vals .x18)) ** (.x19 ↦ᵣ (vals .x19)) **
        (.x20 ↦ᵣ (vals .x20)) ** (.x21 ↦ᵣ s5) ** (.x10 ↦ᵣ header) **
        (.x11 ↦ᵣ BitVec.ofNat 64 bytes.length) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion header bytes **
        bytesRegion ((GuestAddrs.empty_ommers_hash : Word)) (k67OmBytes) **
        regOwn .x14 **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12)) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 8) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 16) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 24) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 32) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 40)) **
        regOwn .x12 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x13)
      [(Ret, k67PostRet sp0 header Ret s5 vals bytes)] := by
    refine cpsNBranchWithin_of_forall_regIs_to_regOwn9 (r1 := .x12)
      (r2 := .x5) (r3 := .x6) (r4 := .x7) (r5 := .x28) (r6 := .x29)
      (r7 := .x30) (r8 := .x31) (r9 := .x13) ?_
    intro v12 v5 v6 v7 v28 v29 v30 v31 v13
    refine cpsNBranchWithin_weaken_pre
      (P := ((.x1 ↦ᵣ Ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ (vals .x8)) **
        (.x9 ↦ᵣ (vals .x9)) ** (.x18 ↦ᵣ (vals .x18)) ** (.x19 ↦ᵣ (vals .x19)) **
        (.x20 ↦ᵣ (vals .x20)) ** (.x21 ↦ᵣ s5) ** (.x10 ↦ᵣ header) **
        (.x11 ↦ᵣ BitVec.ofNat 64 bytes.length) ** (.x12 ↦ᵣ v12) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** regOwn .x13 **
        regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion header bytes **
        bytesRegion ((GuestAddrs.empty_ommers_hash : Word)) (k67OmBytes) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12)) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 8) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 16) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 24) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 32) **
        memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 40)))
      (fun h hp => by
        have hP : (((.x1 ↦ᵣ Ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ (vals .x8)) **
            (.x9 ↦ᵣ (vals .x9)) ** (.x18 ↦ᵣ (vals .x18)) **
            (.x19 ↦ᵣ (vals .x19)) ** (.x20 ↦ᵣ (vals .x20)) ** (.x21 ↦ᵣ s5) **
            (.x10 ↦ᵣ header) ** (.x11 ↦ᵣ BitVec.ofNat 64 bytes.length) **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion header bytes **
            bytesRegion ((GuestAddrs.empty_ommers_hash : Word)) (k67OmBytes) **
            memOwn (sp0 + signExtend12 (-48 : BitVec 12)) **
            memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 8) **
            memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 16) **
            memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 24) **
            memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 32) **
            memOwn (sp0 + signExtend12 (-48 : BitVec 12) + 40) **
            regOwn .x14 ** (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
            (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
            (.x31 ↦ᵣ v31)) ** ((.x13 ↦ᵣ v13))) h := by xperm_hyp hp
        have hconv := sepConj_mono_right (regIs_implies_regOwn .x13) h hP
        xperm_hyp hconv) ?_
    exact cpsTripleWithin_as_cpsNBranchWithin
      (k67ToRet sp0 header bytes Ret s5 vals v12 v5 v6 v7 v28 v29 v30 v31
        hsalign hoff hover9 hvalid hll_len hll_over hll_valid hret)
  refine cpsNBranchWithin_as_cpsTripleWithin ?_
  exact cpsNBranchWithin_weaken_pre (fun h hp => by
    unfold ValidateHeaderPostMergeCorrespondence.postMergeEntryRest at hp
    rw [k67FrameOwn_unfold (sp0 + signExtend12 (-48 : BitVec 12)),
      k67RegsAtSaved_unfold vals] at hp
    xperm_hyp hp) hinner

/-! ## §4  Non-vacuity: a concrete inhabitant of the full premise set -/

/-- The whole-routine theorem's premise set is inhabited: at the concrete
    instantiation with the header at the input-region base, a one-byte
    short-list prefix `[0xc0]`, a literal stack pointer and a trivial frame map,
    every static premise holds and the entry assertion is satisfiable
    (pcFree + pairwise-disjoint ranges).  The header/`.data` disjointness is a
    layout fact, decided here by the symbolic region pins (never a premise on
    the triple). -/
theorem header_validate_post_merge_spec_within_inhabitable :
    ∃ (sp0 Ret s5 : Word) (vals : Reg → Word),
      ((RegionMap.inputRegion.base : Word)).toNat % 8 = 0 ∧
      0 < ([(0xc0 : BitVec 8)] : List (BitVec 8)).length ∧
      ((RegionMap.inputRegion.base : Word)).toNat +
        ([(0xc0 : BitVec 8)] : List (BitVec 8)).length + 9 < 2 ^ 64 ∧
      (∀ k, k < ([(0xc0 : BitVec 8)] : List (BitVec 8)).length →
        isValidByteAccess ((RegionMap.inputRegion.base : Word) +
          BitVec.ofNat 64 k) = true) ∧
      (¬ BitVec.ult (([(0xc0 : BitVec 8)][0]'(by decide)).zeroExtend 64)
          (0xf8 : Word) = true →
        ¬ BitVec.ult
          (((RegionMap.inputRegion.base : Word) + BitVec.ofNat 64 0) +
            BitVec.ofNat 64 ([(0xc0 : BitVec 8)] : List (BitVec 8)).length)
          (((RegionMap.inputRegion.base : Word) + BitVec.ofNat 64 0) +
            ((([(0xc0 : BitVec 8)][0]'(by decide)).zeroExtend 64 -
              (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true →
        0 + 1 + (([(0xc0 : BitVec 8)][0]'(by decide)).zeroExtend 64 -
          (0xf7 : Word)).toNat ≤
          ([(0xc0 : BitVec 8)] : List (BitVec 8)).length) ∧
      (¬ BitVec.ult (([(0xc0 : BitVec 8)][0]'(by decide)).zeroExtend 64)
          (0xf8 : Word) = true →
        ¬ BitVec.ult
          (((RegionMap.inputRegion.base : Word) + BitVec.ofNat 64 0) +
            BitVec.ofNat 64 ([(0xc0 : BitVec 8)] : List (BitVec 8)).length)
          (((RegionMap.inputRegion.base : Word) + BitVec.ofNat 64 0) +
            ((([(0xc0 : BitVec 8)][0]'(by decide)).zeroExtend 64 -
              (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true →
        ((RegionMap.inputRegion.base : Word)).toNat +
          (0 + 1 + (([(0xc0 : BitVec 8)][0]'(by decide)).zeroExtend 64 -
            (0xf7 : Word)).toNat) ≤ 2 ^ 64) ∧
      (¬ BitVec.ult (([(0xc0 : BitVec 8)][0]'(by decide)).zeroExtend 64)
          (0xf8 : Word) = true →
        ¬ BitVec.ult
          (((RegionMap.inputRegion.base : Word) + BitVec.ofNat 64 0) +
            BitVec.ofNat 64 ([(0xc0 : BitVec 8)] : List (BitVec 8)).length)
          (((RegionMap.inputRegion.base : Word) + BitVec.ofNat 64 0) +
            ((([(0xc0 : BitVec 8)][0]'(by decide)).zeroExtend 64 -
              (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true →
        ∀ k, k < (([(0xc0 : BitVec 8)][0]'(by decide)).zeroExtend 64 -
            (0xf7 : Word)).toNat →
          isValidByteAccess ((RegionMap.inputRegion.base : Word) +
            BitVec.ofNat 64 (0 + 1 + k)) = true) ∧
      (Ret &&& ~~~(1 : Word) = Ret) ∧
      (((.x1 ↦ᵣ Ret) **
          ValidateHeaderPostMergeCorrespondence.postMergeEntryRest sp0
            (RegionMap.inputRegion.base : Word) (BitVec.ofNat 64 1)
            (vals .x20) s5 vals [(0xc0 : BitVec 8)]).pcFree) ∧
      -- layout facts: the input header window, the `.data` constant window
      -- and the stack slots are pairwise disjoint (by the symbolic pins)
      ((RegionMap.inputRegion.base + 1 ≤ GuestAddrs.empty_ommers_hash ∨
          GuestAddrs.empty_ommers_hash + 32 ≤ RegionMap.inputRegion.base)) ∧
      (sp0.toNat + 2 ^ 64 - 48 ≤ 2 ^ 64 →
        (sp0.toNat + 2 ^ 64 - 48) % 2 ^ 64 + 48 ≤ RegionMap.inputRegion.base ∨
          RegionMap.inputRegion.base + 1 ≤
            (sp0.toNat + 2 ^ 64 - 48) % 2 ^ 64) ∧
      ((sp0.toNat + 2 ^ 64 - 48) % 2 ^ 64 + 48 ≤
          GuestAddrs.empty_ommers_hash ∨
        GuestAddrs.empty_ommers_hash + 32 ≤
          (sp0.toNat + 2 ^ 64 - 48) % 2 ^ 64) := by
  refine ⟨(0x10000 : Word), (0x100 : Word), (0 : Word), (fun _ => 0), ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RegionMap.inputRegion
    decide
  · decide
  · unfold RegionMap.inputRegion
    decide
  · intro k hk
    rw [show ([(0xc0 : BitVec 8)] : List (BitVec 8)).length = 1 from by decide]
      at hk
    interval_cases k
    rw [show (RegionMap.inputRegion.base : Word) + BitVec.ofNat 64 0 =
        (RegionMap.inputRegion.base : Word) from by bv_omega]
    unfold RegionMap.inputRegion
    decide
  · intro h1 _; exact absurd h1 (by decide)
  · intro h1 _; exact absurd h1 (by decide)
  · intro h1 _; exact absurd h1 (by decide)
  · decide
  · unfold ValidateHeaderPostMergeCorrespondence.postMergeEntryRest
    rw [k67FrameOwn_unfold ((0x10000 : Word) + signExtend12 (-48 : BitVec 12)),
      k67RegsAtSaved_unfold (fun _ => 0)]
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_memOwn | apply pcFree_sepConj
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _
      | exact bytesRegionAux_pcFree _ _ _
  · unfold RegionMap.inputRegion
    unfold GuestAddrs.empty_ommers_hash
    decide
  · intro _
    unfold RegionMap.inputRegion
    decide
  · unfold GuestAddrs.empty_ommers_hash; decide
