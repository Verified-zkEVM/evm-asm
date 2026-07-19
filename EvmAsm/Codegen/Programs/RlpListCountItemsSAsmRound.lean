import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmNext

namespace EvmAsm.Codegen.RlpListCountItemsSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm

/-- The six concrete WalkNext exits collapsed to the semantic distinction the
    count loop needs. -/
def normalizedNext (listBase endPtr : Word) (bytes : List (BitVec 8))
    (off : Nat) : Assertion := fun h =>
  rlpWalkNextOk (listBase + BitVec.ofNat 64 off) endPtr bytes off h ∨
  ∃ status : Word,
    (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
      (.x12 ↦ᵣ (0 : Word))) **
     ⌜status ≠ 0 ∧
       WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr⌝) h

theorem failureRegs_mono (listBase endPtr : Word) (bytes : List (BitVec 8))
    (off : Nat) (status : Word) (P : Prop)
    (h_status : status ≠ 0)
    (h_imp : P → WalkFailure bytes off
      (listBase + BitVec.ofNat 64 off) endPtr) : ∀ h,
      (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
        (.x12 ↦ᵣ (0 : Word)) ** ⌜P⌝) h) →
      ((((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
        (.x12 ↦ᵣ (0 : Word))) **
        ⌜status ≠ 0 ∧ WalkFailure bytes off
          (listBase + BitVec.ofNat 64 off) endPtr⌝) h) := by
  intro h hp
  obtain ⟨h1, h2, hd, hu, h10, hp⟩ := hp
  obtain ⟨h3, h4, hd2, hu2, h11, hp⟩ := hp
  obtain ⟨h12, hP⟩ := (sepConj_pure_right h4).1 hp
  exact (sepConj_pure_right h).2
    ⟨⟨h1, h2, hd, hu, h10, ⟨h3, h4, hd2, hu2, h11, h12⟩⟩,
      h_status, h_imp hP⟩

theorem nextOutcome_to_normalized (listBase endPtr : Word)
    (bytes : List (BitVec 8)) (off : Nat) : ∀ h,
    nextOutcome listBase endPtr bytes off h →
      normalizedNext listBase endPtr bytes off h := by
  intro h h_out
  unfold nextOutcome at h_out
  unfold normalizedNext
  rcases h_out with hs | h2 | h3 | h4 | h5 | h6
  · exact Or.inl hs
  · exact Or.inr ⟨2, failureRegs_mono listBase endPtr bytes off 2 _ (by decide) Or.inl h h2⟩
  · exact Or.inr ⟨3, failureRegs_mono listBase endPtr bytes off 3 _ (by decide) Or.inr h h3⟩
  · exact Or.inr ⟨4, failureRegs_mono listBase endPtr bytes off 4 _ (by decide) Or.inr h h4⟩
  · exact Or.inr ⟨5, failureRegs_mono listBase endPtr bytes off 5 _ (by decide) Or.inr h h5⟩
  · exact Or.inr ⟨6, failureRegs_mono listBase endPtr bytes off 6 _ (by decide) Or.inr h h6⟩

theorem nextCallNormalized (listBase endPtr : Word) (bytes : List (BitVec 8))
    (off listLen : Nat) (v5 v6 v7 v11 v12 v28 v29 v30 v31 oldRa : Word)
    (F : Assertion) (h_F : F.pcFree)
    (h_align : listBase.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_valid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_off : off ≤ listLen) :
    cpsTripleWithin 89 (B + 52) (B + 60) code
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ v11) **
       (.x12 ↦ᵣ v12) ** (.x18 ↦ᵣ endPtr) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** (.x1 ↦ᵣ oldRa) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** F)
      ((nextCommon listBase bytes **
        normalizedNext listBase endPtr bytes off) **
       ((.x18 ↦ᵣ endPtr) ** F)) := by
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp =>
    sepConj_mono_left (sepConj_mono_right
      (nextOutcome_to_normalized listBase endPtr bytes off)) h hp)
    (nextCallBlock listBase endPtr bytes off listLen v5 v6 v7 v11 v12 v28 v29
      v30 v31 oldRa F h_F h_align h_slack h_over h_valid h_off)

def selected (newSp listBase outPtr oldCount : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ endPtr : Word, ∃ count : Nat,
    ∃ v5 v6 v7 v11 v12 v28 v29 v30 v31 raW : Word,
    (((.x18 ↦ᵣ endPtr) ** stableRest newSp listBase outPtr oldCount saved **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) ** (.x1 ↦ᵣ raW) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase bytes **
      (.x10 ↦ᵣ endPtr) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (.x19 ↦ᵣ BitVec.ofNat 64 count)) **
     ⌜Success bytes listBase listLen count ∧ count < 2 ^ 64⌝) h

theorem dispatchDone (newSp listBase outPtr endPtr oldCount : Word)
    (saved : Saved) (bytes : List (BitVec 8))
    (listLen cursorOff count : Nat)
    (v5 v6 v7 v11 v12 v28 v29 v30 v31 raW : Word)
    (h_inv : LoopInvariant bytes listBase listLen cursorOff endPtr count off
      (listBase + BitVec.ofNat 64 off))
    (h_done : listBase + BitVec.ofNat 64 off = endPtr)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_slack : listLen + 9 ≤ bytes.length) :
    cpsTripleWithin 1 (B + 48) (B + 72) code
      ((.x18 ↦ᵣ endPtr) ** stableRest newSp listBase outPtr oldCount saved **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** (.x1 ↦ᵣ raW) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes **
       (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ v11) **
       (.x12 ↦ᵣ v12) ** (.x19 ↦ᵣ BitVec.ofNat 64 count))
      (selected newSp listBase outPtr oldCount saved bytes listLen) := by
  let F : Assertion :=
    ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (.x19 ↦ᵣ BitVec.ofNat 64 count) **
      (stableRest newSp listBase outPtr oldCount saved **
       ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) ** (.x1 ↦ᵣ raW) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase bytes)))
  have hs := headerDone endPtr F (by dsimp [F]; pcf)
  have h_success := h_inv.toSuccess h_done (by omega)
  have h_count := h_inv.h_count
  have h_off := h_inv.h_off
  exact cpsTripleWithin_weaken (fun _ hp => by
    rw [h_done] at hp
    unfold F
    xperm_hyp hp)
    (fun h hp => by
      unfold selected
      refine ⟨endPtr, count, v5, v6, v7, v11, v12, v28, v29, v30, v31, raW, ?_⟩
      refine (sepConj_pure_right h).2 ⟨?_, h_success, ?_⟩
      · unfold F at hp
        xperm_hyp hp
      · omega) hs

theorem dispatchFailure (newSp listBase outPtr endPtr oldCount status : Word)
    (saved : Saved) (bytes : List (BitVec 8))
    (listLen cursorOff count off : Nat)
    (h_inv : LoopInvariant bytes listBase listLen cursorOff endPtr count off
      (listBase + BitVec.ofNat 64 off))
    (h_status : status ≠ 0)
    (h_inside : BitVec.ult (listBase + BitVec.ofNat 64 off) endPtr = true)
    (h_walk : WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr) :
    cpsTripleWithin 1 (B + 60) (B + 84) code
      ((nextCommon listBase bytes **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
         (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ (0 : Word)))) **
       ((.x18 ↦ᵣ endPtr) **
        (stableRest newSp listBase outPtr oldCount saved **
         (.x19 ↦ᵣ BitVec.ofNat 64 count))))
      (rejected newSp listBase outPtr oldCount saved bytes listLen) := by
  let F : Assertion :=
    ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x12 ↦ᵣ (0 : Word)) **
     (.x18 ↦ᵣ endPtr) ** stableRest newSp listBase outPtr oldCount saved **
     (.x19 ↦ᵣ BitVec.ofNat 64 count) **
     (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (B + 60)) **
      bytesRegion listBase bytes))
  have ht := statusReject status F (by dsimp [F]; pcf) h_status
  have h_failure := h_inv.toFailure h_inside h_walk
  exact cpsTripleWithin_weaken (fun _ hp => by
    unfold nextCommon at hp
    unfold F
    xperm_hyp hp) (fun h hp => by
    unfold rejected
    refine ⟨status, listBase + BitVec.ofNat 64 off, status, 0, endPtr,
      BitVec.ofNat 64 count, B + 60, ?_⟩
    refine (sepConj_pure_right h).2 ⟨?_, h_status, h_failure⟩
    unfold F stableRest at hp
    unfold stableRest
    xperm_hyp hp) ht

theorem dispatchSuccess (newSp listBase outPtr endPtr oldCount next len : Word)
    (saved : Saved) (bytes : List (BitVec 8))
    (listLen cursorOff count off j : Nat)
    (h_j : j = remaining listLen off)
    (h_inv : LoopInvariant bytes listBase listLen cursorOff endPtr count off
      (listBase + BitVec.ofNat 64 off))
    (h_item : rlpItemDecode bytes off (listBase + BitVec.ofNat 64 off)
      endPtr next len)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_slack : listLen + 9 ≤ bytes.length) :
    cpsTripleWithin 3 (B + 60) (B + 48) code
      ((nextCommon listBase bytes **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len))) **
       ((.x18 ↦ᵣ endPtr) **
        (stableRest newSp listBase outPtr oldCount saved **
         (.x19 ↦ᵣ BitVec.ofNat 64 count))))
      (fun h => ∃ j', j' < j ∧
        loopInv newSp listBase outPtr endPtr oldCount saved bytes listLen
          cursorOff j' h) := by
  let F : Assertion :=
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x18 ↦ᵣ endPtr) **
     stableRest newSp listBase outPtr oldCount saved **
     (.x19 ↦ᵣ BitVec.ofNat 64 count) **
     (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (B + 60)) **
      bytesRegion listBase bytes))
  have hs := statusOk F (by dsimp [F]; pcf)
  let G : Assertion :=
    ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
     (.x18 ↦ᵣ endPtr) ** stableRest newSp listBase outPtr oldCount saved **
     (.x0 ↦ᵣ (0 : Word)) **
     (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (B + 60)) **
      bytesRegion listBase bytes))
  have hi := incrementBack count G (by dsimp [G]; pcf)
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold F at hp
    unfold G
    xperm_hyp hp) hs hi
  have h_step := h_inv.step h_item (by omega)
  let newOff := (next - listBase).toNat
  have h_next : next = listBase + BitVec.ofNat 64 newOff := h_step.1.h_cursor
  have h_inv' : LoopInvariant bytes listBase listLen cursorOff endPtr
      (count + 1) newOff (listBase + BitVec.ofNat 64 newOff) := by
    rw [← h_next]
    exact h_step.1
  exact cpsTripleWithin_weaken (fun _ hp => by
    unfold nextCommon at hp
    unfold F
    xperm_hyp hp) (fun h hp => by
    refine ⟨remaining listLen newOff, ?_, ?_⟩
    · rw [h_j]
      exact h_step.2
    · unfold loopInv
      refine ⟨count + 1, newOff, 0, len, B + 60, ?_⟩
      refine (sepConj_pure_right h).2 ⟨?_, rfl, h_inv'⟩
      unfold G at hp
      unfold loopFrame
      rw [h_next] at hp
      xperm_hyp hp) hc

theorem cpsNBranchWithin_pre_or {n : Nat} {entry : Word} {cr : CodeReq}
    {P1 P2 : Assertion} {exits : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n entry cr P1 exits)
    (h2 : cpsNBranchWithin n entry cr P2 exits) :
    cpsNBranchWithin n entry cr (fun h => P1 h ∨ P2 h) exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, ha, hb, hd, hu, hor, hRb⟩ := hPR
  rcases hor with hP | hP
  · exact h1 R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc
  · exact h2 R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc

theorem afterCall (newSp listBase outPtr endPtr oldCount : Word)
    (saved : Saved) (bytes : List (BitVec 8))
    (listLen cursorOff count off j : Nat)
    (h_j : j = remaining listLen off)
    (h_inv : LoopInvariant bytes listBase listLen cursorOff endPtr count off
      (listBase + BitVec.ofNat 64 off))
    (h_inside : BitVec.ult (listBase + BitVec.ofNat 64 off) endPtr = true)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_slack : listLen + 9 ≤ bytes.length) :
    cpsNBranchWithin 3 (B + 60) code
      ((nextCommon listBase bytes **
        normalizedNext listBase endPtr bytes off) **
       ((.x18 ↦ᵣ endPtr) **
        (stableRest newSp listBase outPtr oldCount saved **
         (.x19 ↦ᵣ BitVec.ofNat 64 count))))
      [(B + 72, selected newSp listBase outPtr oldCount saved bytes listLen),
       (B + 84, rejected newSp listBase outPtr oldCount saved bytes listLen),
       (B + 48, fun h => ∃ j', j' < j ∧
         loopInv newSp listBase outPtr endPtr oldCount saved bytes listLen
           cursorOff j' h)] := by
  let successPre : Assertion := fun h => ∃ next len,
    (((nextCommon listBase bytes **
       ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len))) **
      ((.x18 ↦ᵣ endPtr) **
       (stableRest newSp listBase outPtr oldCount saved **
        (.x19 ↦ᵣ BitVec.ofNat 64 count)))) **
     ⌜rlpItemDecode bytes off (listBase + BitVec.ofNat 64 off)
       endPtr next len⌝) h
  let failPre : Assertion := fun h => ∃ status,
    (((nextCommon listBase bytes **
       ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
        (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ (0 : Word)))) **
      ((.x18 ↦ᵣ endPtr) **
       (stableRest newSp listBase outPtr oldCount saved **
        (.x19 ↦ᵣ BitVec.ofNat 64 count)))) **
     ⌜status ≠ 0 ∧ WalkFailure bytes off
       (listBase + BitVec.ofNat 64 off) endPtr⌝) h
  have hs : cpsNBranchWithin 3 (B + 60) code successPre
      [(B + 72, selected newSp listBase outPtr oldCount saved bytes listLen),
       (B + 84, rejected newSp listBase outPtr oldCount saved bytes listLen),
       (B + 48, fun h => ∃ j', j' < j ∧
         loopInv newSp listBase outPtr endPtr oldCount saved bytes listLen
           cursorOff j' h)] := by
    unfold successPre
    refine cpsNBranchWithin_exists_pre (fun next => ?_)
    refine cpsNBranchWithin_exists_pre (fun len => ?_)
    refine cpsNBranchWithin_pure_pre (fun h_item => ?_)
    exact cpsNBranchWithin_of_triple (by simp)
      (dispatchSuccess newSp listBase outPtr endPtr oldCount next len saved bytes
        listLen cursorOff count off j h_j h_inv h_item h_over h_slack)
  have hf : cpsNBranchWithin 3 (B + 60) code failPre
      [(B + 72, selected newSp listBase outPtr oldCount saved bytes listLen),
       (B + 84, rejected newSp listBase outPtr oldCount saved bytes listLen),
       (B + 48, fun h => ∃ j', j' < j ∧
         loopInv newSp listBase outPtr endPtr oldCount saved bytes listLen
           cursorOff j' h)] := by
    unfold failPre
    refine cpsNBranchWithin_exists_pre (fun status => ?_)
    refine cpsNBranchWithin_pure_pre (fun hpure => ?_)
    exact cpsNBranchWithin_mono_nSteps (by omega)
      (cpsNBranchWithin_of_triple (by simp)
        (dispatchFailure newSp listBase outPtr endPtr oldCount status saved bytes
          listLen cursorOff count off h_inv hpure.1 h_inside hpure.2))
  have harms := cpsNBranchWithin_pre_or hs hf
  exact cpsNBranchWithin_weaken_pre (fun h hp => by
    unfold normalizedNext at hp
    unfold successPre failPre
    obtain ⟨h1, h2, hd, hu, hleft, hstable⟩ := hp
    obtain ⟨h3, h4, hd2, hu2, hcommon, hout⟩ := hleft
    rcases hout with hout | hout
    · refine Or.inl ?_
      obtain ⟨next, len, hok⟩ := hout
      refine ⟨next, len, ?_⟩
      obtain ⟨h5, h6, hd3, hu3, h10, hrest⟩ := hok
      obtain ⟨h7, h8, hd4, hu4, h11, hrest⟩ := hrest
      obtain ⟨h12, h_item⟩ := (sepConj_pure_right h8).1 hrest
      refine (sepConj_pure_right h).2 ⟨?_, h_item⟩
      exact ⟨h1, h2, hd, hu,
        ⟨h3, h4, hd2, hu2, hcommon,
          ⟨h5, h6, hd3, hu3, h10,
            ⟨h7, h8, hd4, hu4, h11, h12⟩⟩⟩, hstable⟩
    · refine Or.inr ?_
      obtain ⟨status, hfail⟩ := hout
      refine ⟨status, ?_⟩
      have hall := sepConj_mono_left
        (sepConj_mono_right (fun _ hp0 => hp0)) h
        ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, hfail⟩, hstable⟩
      xperm_hyp hall) harms

theorem loopRound (newSp listBase outPtr endPtr oldCount : Word)
    (saved : Saved) (bytes : List (BitVec 8))
    (listLen cursorOff j : Nat)
    (h_align : listBase.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_valid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsNBranchWithin 93 (B + 48) code
      (loopInv newSp listBase outPtr endPtr oldCount saved bytes listLen
        cursorOff j)
      [(B + 72, selected newSp listBase outPtr oldCount saved bytes listLen),
       (B + 84, rejected newSp listBase outPtr oldCount saved bytes listLen),
       (B + 48, fun h => ∃ j', j' < j ∧
         loopInv newSp listBase outPtr endPtr oldCount saved bytes listLen
           cursorOff j' h)] := by
  unfold loopInv
  refine cpsNBranchWithin_exists_pre (fun count => ?_)
  refine cpsNBranchWithin_exists_pre (fun off => ?_)
  refine cpsNBranchWithin_exists_pre (fun v11 => ?_)
  refine cpsNBranchWithin_exists_pre (fun v12 => ?_)
  refine cpsNBranchWithin_exists_pre (fun raW => ?_)
  refine cpsNBranchWithin_pure_pre (fun hfacts => ?_)
  obtain ⟨h_j, h_inv⟩ := hfacts
  let P : Assertion :=
    (((stableRest newSp listBase outPtr oldCount saved **
      ((.x18 ↦ᵣ endPtr) **
       (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
       (.x19 ↦ᵣ BitVec.ofNat 64 count) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes)) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1) **
     regOwn .x11)
  refine cpsNBranchWithin_weaken_pre (P := P) (fun h hp => by
    unfold loopFrame at hp
    unfold P
    let Rest : Assertion :=
      stableRest newSp listBase outPtr oldCount saved **
      (.x18 ↦ᵣ endPtr) **
      (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
      (.x19 ↦ᵣ BitVec.ofNat 64 count) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase bytes ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
    have hpGrouped : ((((.x12 ↦ᵣ v12) ** (.x1 ↦ᵣ raW) **
        (.x11 ↦ᵣ v11)) ** Rest) h) := by
      unfold Rest
      xperm_hyp hp
    have hpOwn := sepConj_mono
      (sepConj_mono (regIs_implies_regOwn .x12)
        (sepConj_mono (regIs_implies_regOwn .x1)
          (regIs_implies_regOwn .x11)))
      (fun _ x => x) h hpGrouped
    unfold Rest at hpOwn
    xperm_hyp hpOwn) ?_
  unfold P
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn (fun v11 => ?_)
  let P9 : Assertion :=
    (stableRest newSp listBase outPtr oldCount saved **
      ((.x18 ↦ᵣ endPtr) **
       (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
       (.x19 ↦ᵣ BitVec.ofNat 64 count) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes)) ** (.x11 ↦ᵣ v11)
  refine cpsNBranchWithin_weaken_pre
    (P := P9 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1)
    (fun h hp => by unfold P9; xperm_hyp hp) ?_
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn9
    (fun v5 v6 v7 v12 v28 v29 v30 v31 raW => ?_)
  by_cases h_done : listBase + BitVec.ofNat 64 off = endPtr
  · exact cpsNBranchWithin_mono_nSteps (by omega)
      (cpsNBranchWithin_of_triple (by simp)
        (cpsTripleWithin_weaken (fun _ hp => by
          unfold P9 stableRest at hp
          unfold stableRest
          xperm_hyp hp) (fun _ hp => hp)
          (dispatchDone newSp listBase outPtr endPtr oldCount saved bytes listLen
            cursorOff count v5 v6 v7 v11 v12 v28 v29 v30 v31 raW h_inv h_done
            h_over h_slack)))
  · let Fh : Assertion :=
      ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x19 ↦ᵣ BitVec.ofNat 64 count) **
       stableRest newSp listBase outPtr oldCount saved **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** (.x1 ↦ᵣ raW) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes)
    have hh := headerContinue (listBase + BitVec.ofNat 64 off) endPtr Fh
      (by dsimp [Fh]; pcf) h_done
    let Fc : Assertion :=
      stableRest newSp listBase outPtr oldCount saved **
        (.x19 ↦ᵣ BitVec.ofNat 64 count)
    have hcall := nextCallNormalized listBase endPtr bytes off listLen
      v5 v6 v7 v11 v12 v28 v29 v30 v31 raW Fc (by dsimp [Fc]; pcf)
      h_align h_slack h_over h_valid h_inv.h_off
    have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      unfold Fh at hp
      unfold Fc
      xperm_hyp hp) hh hcall
    have h_inside : BitVec.ult (listBase + BitVec.ofNat 64 off) endPtr = true := by
      -- Not done (cursor ≠ end) + off ≤ listLen + end = base+listLen ⇒ ult
      have h_end : endPtr = listBase + BitVec.ofNat 64 listLen := h_inv.h_list.end_eq
      have h_off := h_inv.h_off
      have h_ne : listBase + BitVec.ofNat 64 off ≠
          listBase + BitVec.ofNat 64 listLen := by simpa [h_end] using h_done
      have h_off_ne : off ≠ listLen := by
        intro heq; apply h_ne; simp [heq]
      have h_lt : off < listLen := Nat.lt_of_le_of_ne h_off h_off_ne
      have h_base_off : listBase.toNat + off < 2 ^ 64 := by
        have := h_over; omega
      have h_base_len : listBase.toNat + listLen < 2 ^ 64 := by
        have := h_over; omega
      rw [h_end]
      have h1 : (listBase + BitVec.ofNat 64 off).toNat = listBase.toNat + off := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off < 2^64),
          Nat.mod_eq_of_lt h_base_off]
      have h2 : (listBase + BitVec.ofNat 64 listLen).toNat = listBase.toNat + listLen := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : listLen < 2^64),
          Nat.mod_eq_of_lt h_base_len]
      rw [BitVec.ult_eq_decide, decide_eq_true_iff, h1, h2]
      omega
    have hcont := afterCall newSp listBase outPtr endPtr oldCount saved bytes
      listLen cursorOff count off j h_j h_inv h_inside h_over h_slack
    have hseq := cpsTripleWithin_seq_cpsNBranchWithin_same_cr hc hcont
    exact cpsNBranchWithin_mono_nSteps (by omega)
      (cpsNBranchWithin_weaken_pre (fun _ hp => by
        unfold P9 at hp
        unfold Fh
        xperm_hyp hp) hseq)

theorem strictCountLoop (newSp listBase outPtr endPtr oldCount : Word)
    (saved : Saved) (bytes : List (BitVec 8))
    (listLen cursorOff j : Nat)
    (h_align : listBase.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_valid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsNBranchWithin (93 * (j + 1)) (B + 48) code
      (loopInv newSp listBase outPtr endPtr oldCount saved bytes listLen
        cursorOff j)
      [(B + 72, selected newSp listBase outPtr oldCount saved bytes listLen),
       (B + 84, rejected newSp listBase outPtr oldCount saved bytes listLen)] :=
  measureTwoExitLoop_spec 93
    (loopInv newSp listBase outPtr endPtr oldCount saved bytes listLen cursorOff)
    (fun j' => loopRound newSp listBase outPtr endPtr oldCount saved bytes
      listLen cursorOff j' h_align h_slack h_over h_valid) j

theorem scanFromInit (newSp listBase outPtr oldCount : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen : Nat)
    (h_align : listBase.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_valid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsNBranchWithin (93 * (listLen + 1)) (B + 48) code
      (initLoopPost newSp listBase outPtr oldCount saved bytes listLen)
      [(B + 72, selected newSp listBase outPtr oldCount saved bytes listLen),
       (B + 84, rejected newSp listBase outPtr oldCount saved bytes listLen)] := by
  unfold initLoopPost
  refine cpsNBranchWithin_exists_pre (fun cursorOff => ?_)
  refine cpsNBranchWithin_exists_pre (fun endPtr => ?_)
  have hloop := strictCountLoop newSp listBase outPtr endPtr oldCount saved bytes
    listLen cursorOff (remaining listLen cursorOff) h_align h_slack h_over h_valid
  exact cpsNBranchWithin_mono_nSteps (by
    unfold remaining
    omega) hloop


end EvmAsm.Codegen.RlpListCountItemsSAsm
