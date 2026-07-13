import EvmAsm.Codegen.Programs.RlpFieldToU256BeOutcomeSAsm

namespace EvmAsm.Codegen.RlpFieldToU256BeSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

theorem restoreTailExact
    (spOuter newSp v1 v8 v9 : Word) (outer : Saved)
    (F : Assertion) (hF : F.pcFree)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hret : outer.ra &&& ~~~(1 : Word) = outer.ra) :
    cpsTripleWithin 5 (B + 156) outer.ra code
      (((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) **
        (.x9 ↦ᵣ v9) ** savedFrame newSp outer) ** F)
      (((.x2 ↦ᵣ spOuter) ** regsAt frame (savedVals outer) **
        savedFrame newSp outer) ** F) := by
  have ht := restoreTail spOuter newSp outer F hF hnewSp hret
  exact cpsTripleWithin_weaken (fun h hp => by
      let R : Assertion :=
        (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9)
      let FrameExact : Assertion :=
        ((.x2 ↦ᵣ newSp) ** R) ** savedFrame newSp outer
      let FrameOwn : Assertion :=
        ((.x2 ↦ᵣ newSp) ** regsOwnAt frame) ** savedFrame newSp outer
      have hp0 : ((FrameExact ** F) h) := by
        unfold FrameExact R
        xperm_hyp hp
      have himpl : ∀ h', FrameExact h' → FrameOwn h' := by
        intro h' hf
        obtain ⟨g1, g2, gd, gu, hleft, hsaved⟩ := hf
        obtain ⟨ha, hb, hd, hu, hsp, hr⟩ := hleft
        have hro : regsOwnAt frame hb :=
          EvmAsm.Codegen.RlpFieldToU64SAsm.frameRegs_implies_owned v8 v9 hb
            (sepConj_mono_left (regIs_implies_regOwn .x1) hb hr)
        unfold FrameOwn
        exact ⟨g1, g2, gd, gu, ⟨ha, hb, hd, hu, hsp, hro⟩, hsaved⟩
      have hp1 := sepConj_mono_left himpl h hp0
      unfold FrameOwn at hp1
      xperm_hyp hp1)
    (fun _ hp => hp) ht

#print axioms restoreTailExact

def successPayload (newSp listBase outputPtr offset len v11 v12 : Word)
    (saved : ListSaved) (bytes : List (BitVec 8))
    (listLen index : Nat) : Assertion :=
  (((.x5 ↦ᵣ offsetCell) ** (.x6 ↦ᵣ (0 : Word)) ** regOwn .x7 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) **
    (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
    (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
    (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** stackFree newSp 8 **
    (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x31 **
    bytesRegion listBase bytes **
    bytesRegion outputPtr (rightAligned32 bytes offset len)) **
    ⌜Result bytes listBase listLen index 0
      (rightAligned32 bytes offset len)⌝)

def successReturned
    (spOuter newSp listBase outputPtr : Word) (outer : Saved)
    (saved : ListSaved) (bytes : List (BitVec 8))
    (listLen index : Nat) : Assertion := fun h => ∃ offset len v11 v12,
  ((((.x2 ↦ᵣ spOuter) ** regsAt frame (savedVals outer) **
      savedFrame newSp outer) **
    successPayload newSp listBase outputPtr offset len v11 v12 saved bytes
      listLen index) h)

theorem restoreSuccess
    (spOuter newSp listBase outputPtr : Word) (outer : Saved)
    (saved : ListSaved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hret : outer.ra &&& ~~~(1 : Word) = outer.ra) :
    cpsTripleWithin 5 (B + 156) outer.ra code
      (((.x1 ↦ᵣ (B + 60)) **
        successOutcome newSp listBase outputPtr saved bytes listLen index) **
        savedFrame newSp outer)
      (successReturned spOuter newSp listBase outputPtr outer saved bytes
        listLen index) := by
  unfold successOutcome
  refine cpsTripleWithin_weaken (P := fun h => ∃ offset len v11 v12,
      (((.x1 ↦ᵣ (B + 60)) **
        (((.x5 ↦ᵣ offsetCell) ** (.x6 ↦ᵣ (0 : Word)) ** regOwn .x7 **
          (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outputPtr) ** regOwn .x28 **
          regOwn .x29 ** regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) **
          (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
          copyCarry newSp saved v11 v12 ** bytesRegion listBase bytes **
          bytesRegion outputPtr (rightAligned32 bytes offset len)) **
          ⌜Result bytes listBase listLen index 0
            (rightAligned32 bytes offset len)⌝)) **
        savedFrame newSp outer) h) (fun h hp => by
      obtain ⟨g1, g2, gd, gu, hmain, hsf⟩ := hp
      obtain ⟨ha, hb, hd, hu, hra, houtcome⟩ := hmain
      obtain ⟨offset, len, v11, v12, hcase⟩ := houtcome
      exact ⟨offset, len, v11, v12, g1, g2, gd, gu,
        ⟨ha, hb, hd, hu, hra, hcase⟩, hsf⟩) (fun _ hp => hp) ?_
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun offset => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun len => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v11 => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v12 => ?_)
  let F := successPayload newSp listBase outputPtr offset len v11 v12 saved bytes
    listLen index
  have ht := restoreTailExact spOuter newSp (B + 60) listBase outputPtr outer F
    (by unfold F successPayload; pcf) hnewSp hret
  refine cpsTripleWithin_weaken (fun h hp => by
      unfold copyCarry at hp
      dsimp only [F] at ⊢
      unfold successPayload
      xperm_pure hp) (fun h hp => ?_) ht
  unfold successReturned
  exact ⟨offset, len, v11, v12, hp⟩

#print axioms restoreSuccess

def tooLongPayload (newSp listBase outputPtr offset len v11 v12 : Word)
    (saved : ListSaved) (bytes : List (BitVec 8))
    (listLen index : Nat) : Assertion :=
  (((.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) **
    (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
    (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
    (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** stackFree newSp 8 **
    (.x10 ↦ᵣ (2 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x31 **
    bytesRegion listBase bytes ** bytesRegion outputPtr (List.replicate 32 0)) **
    ⌜Result bytes listBase listLen index 2 (List.replicate 32 0)⌝)

def tooLongReturned
    (spOuter newSp listBase outputPtr : Word) (outer : Saved)
    (saved : ListSaved) (bytes : List (BitVec 8))
    (listLen index : Nat) : Assertion := fun h => ∃ offset len v11 v12,
  ((((.x2 ↦ᵣ spOuter) ** regsAt frame (savedVals outer) **
      savedFrame newSp outer) **
    tooLongPayload newSp listBase outputPtr offset len v11 v12 saved bytes
      listLen index) h)

theorem restoreTooLong
    (spOuter newSp listBase outputPtr : Word) (outer : Saved)
    (saved : ListSaved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (hs1 : saved.s1 = outputPtr)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hret : outer.ra &&& ~~~(1 : Word) = outer.ra) :
    cpsTripleWithin 5 (B + 156) outer.ra code
      (((.x1 ↦ᵣ (B + 60)) **
        tooLongOutcome newSp listBase outputPtr saved bytes listLen index) **
        savedFrame newSp outer)
      (tooLongReturned spOuter newSp listBase outputPtr outer saved bytes
        listLen index) := by
  unfold tooLongOutcome
  refine cpsTripleWithin_weaken (P := fun h => ∃ offset len v11 v12,
      (((.x1 ↦ᵣ (B + 60)) **
        (((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
          (.x5 ↦ᵣ lengthCell) ** (.x8 ↦ᵣ listBase) ** regOwn .x28 **
          regOwn .x29 ** (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
          statusCarry newSp listBase saved bytes v11 v12 2 **
          bytesRegion outputPtr (List.replicate 32 0)) **
          ⌜Result bytes listBase listLen index 2 (List.replicate 32 0)⌝)) **
        savedFrame newSp outer) h) (fun h hp => by
      obtain ⟨g1, g2, gd, gu, hmain, hsf⟩ := hp
      obtain ⟨ha, hb, hd, hu, hra, houtcome⟩ := hmain
      obtain ⟨offset, len, v11, v12, hcase⟩ := houtcome
      exact ⟨offset, len, v11, v12, g1, g2, gd, gu,
        ⟨ha, hb, hd, hu, hra, hcase⟩, hsf⟩) (fun _ hp => hp) ?_
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun offset => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun len => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v11 => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v12 => ?_)
  let F := tooLongPayload newSp listBase outputPtr offset len v11 v12 saved bytes
    listLen index
  have ht := restoreTailExact spOuter newSp (B + 60) listBase outputPtr outer F
    (by unfold F tooLongPayload; pcf) hnewSp hret
  refine cpsTripleWithin_weaken (fun h hp => by
      unfold statusCarry at hp
      rw [hs1] at hp
      dsimp only [F] at ⊢
      unfold tooLongPayload
      xperm_pure hp) (fun h hp => ?_) ht
  unfold tooLongReturned
  exact ⟨offset, len, v11, v12, hp⟩

#print axioms restoreTooLong

def failurePayload (newSp listBase outputPtr oldOffset oldLen v11 v12 : Word)
    (saved : ListSaved) (bytes : List (BitVec 8))
    (listLen index : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) **
    (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen) **
    (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
    (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** stackFree newSp 8 **
    (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x31 **
    bytesRegion listBase bytes ** bytesRegion outputPtr (List.replicate 32 0)) **
    ⌜Result bytes listBase listLen index 1 (List.replicate 32 0)⌝)

def failureReturned
    (spOuter newSp listBase outputPtr oldOffset oldLen : Word) (outer : Saved)
    (saved : ListSaved) (bytes : List (BitVec 8))
    (listLen index : Nat) : Assertion := fun h => ∃ v11 v12,
  ((((.x2 ↦ᵣ spOuter) ** regsAt frame (savedVals outer) **
      savedFrame newSp outer) **
    failurePayload newSp listBase outputPtr oldOffset oldLen v11 v12 saved bytes
      listLen index) h)

theorem restoreFailure
    (spOuter newSp listBase outputPtr oldOffset oldLen : Word) (outer : Saved)
    (saved : ListSaved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (hs0 : saved.s0 = listBase) (hs1 : saved.s1 = outputPtr)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hret : outer.ra &&& ~~~(1 : Word) = outer.ra) :
    cpsTripleWithin 5 (B + 156) outer.ra code
      (((.x1 ↦ᵣ (B + 60)) **
        failureOutcome newSp listBase outputPtr oldOffset oldLen saved bytes
          listLen index) ** savedFrame newSp outer)
      (failureReturned spOuter newSp listBase outputPtr oldOffset oldLen outer
        saved bytes listLen index) := by
  unfold failureOutcome
  refine cpsTripleWithin_weaken (P := fun h => ∃ v11 v12,
      (((.x1 ↦ᵣ (B + 60)) **
        (((listCallCore newSp listBase offsetCell lengthCell saved bytes 1
          oldOffset oldLen v11 v12) **
          bytesRegion outputPtr (List.replicate 32 0)) **
          ⌜Result bytes listBase listLen index 1 (List.replicate 32 0)⌝)) **
        savedFrame newSp outer) h) (fun h hp => by
      obtain ⟨g1, g2, gd, gu, hmain, hsf⟩ := hp
      obtain ⟨ha, hb, hd, hu, hra, houtcome⟩ := hmain
      obtain ⟨v11, v12, hcase⟩ := houtcome
      exact ⟨v11, v12, g1, g2, gd, gu,
        ⟨ha, hb, hd, hu, hra, hcase⟩, hsf⟩) (fun _ hp => hp) ?_
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v11 => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v12 => ?_)
  let F := failurePayload newSp listBase outputPtr oldOffset oldLen v11 v12 saved
    bytes listLen index
  have ht := restoreTailExact spOuter newSp (B + 60) listBase outputPtr outer F
    (by unfold F failurePayload; pcf) hnewSp hret
  refine cpsTripleWithin_weaken (fun h hp => by
      simp only [listCallCore,
        EvmAsm.Codegen.RlpFieldToU64SAsm.listCallCore,
        EvmAsm.Codegen.RlpFieldToU64SAsm.listCallRest,
        EvmAsm.Codegen.RlpFieldToU64SAsm.listSavedRegs,
        EvmAsm.Codegen.RlpFieldToU64SAsm.listOtherSaved] at hp
      rw [hs0, hs1] at hp
      dsimp only [F] at ⊢
      unfold failurePayload
      xperm_pure hp) (fun h hp => ?_) ht
  unfold failureReturned
  exact ⟨v11, v12, hp⟩

#print axioms restoreFailure

def returnedOutcome
    (spOuter newSp listBase outputPtr oldOffset oldLen : Word) (outer : Saved)
    (saved : ListSaved) (bytes : List (BitVec 8))
    (listLen index : Nat) : Assertion := fun h =>
  successReturned spOuter newSp listBase outputPtr outer saved bytes listLen
    index h ∨
  tooLongReturned spOuter newSp listBase outputPtr outer saved bytes listLen
    index h ∨
  failureReturned spOuter newSp listBase outputPtr oldOffset oldLen outer saved
    bytes listLen index h

theorem restoreJoined
    (spOuter newSp listBase outputPtr oldOffset oldLen : Word) (outer : Saved)
    (saved : ListSaved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (hs0 : saved.s0 = listBase) (hs1 : saved.s1 = outputPtr)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hret : outer.ra &&& ~~~(1 : Word) = outer.ra) :
    cpsTripleWithin 5 (B + 156) outer.ra code
      (((.x1 ↦ᵣ (B + 60)) **
        joinedOutcome newSp listBase outputPtr oldOffset oldLen saved bytes
          listLen index) ** savedFrame newSp outer)
      (returnedOutcome spOuter newSp listBase outputPtr oldOffset oldLen outer
        saved bytes listLen index) := by
  have hs := cpsTripleWithin_weaken
    (Q' := returnedOutcome spOuter newSp listBase outputPtr oldOffset oldLen outer
      saved bytes listLen index) (fun _ hp => hp)
    (fun h hp => by unfold returnedOutcome; exact Or.inl hp)
    (restoreSuccess spOuter newSp listBase outputPtr outer saved bytes listLen
      index hnewSp hret)
  have ht := cpsTripleWithin_weaken
    (Q' := returnedOutcome spOuter newSp listBase outputPtr oldOffset oldLen outer
      saved bytes listLen index) (fun _ hp => hp)
    (fun h hp => by unfold returnedOutcome; exact Or.inr (Or.inl hp))
    (restoreTooLong spOuter newSp listBase outputPtr outer saved bytes listLen
      index hs1 hnewSp hret)
  have hf := cpsTripleWithin_weaken
    (Q' := returnedOutcome spOuter newSp listBase outputPtr oldOffset oldLen outer
      saved bytes listLen index) (fun _ hp => hp)
    (fun h hp => by unfold returnedOutcome; exact Or.inr (Or.inr hp))
    (restoreFailure spOuter newSp listBase outputPtr oldOffset oldLen outer saved
      bytes listLen index hs0 hs1 hnewSp hret)
  have hor := cpsTripleWithin_pre_or hs (cpsTripleWithin_pre_or ht hf)
  exact cpsTripleWithin_weaken (fun h hp => by
      obtain ⟨g1, g2, gd, gu, hmain, hsf⟩ := hp
      obtain ⟨ha, hb, hd, hu, hra, hj⟩ := hmain
      unfold joinedOutcome at hj
      rcases hj with hs | ht | hf
      · exact Or.inl ⟨g1, g2, gd, gu, ⟨ha, hb, hd, hu, hra, hs⟩, hsf⟩
      · exact Or.inr (Or.inl
          ⟨g1, g2, gd, gu, ⟨ha, hb, hd, hu, hra, ht⟩, hsf⟩)
      · exact Or.inr (Or.inr
          ⟨g1, g2, gd, gu, ⟨ha, hb, hd, hu, hra, hf⟩, hsf⟩))
    (fun _ hp => hp) hor

#print axioms restoreJoined

end EvmAsm.Codegen.RlpFieldToU256BeSAsm
