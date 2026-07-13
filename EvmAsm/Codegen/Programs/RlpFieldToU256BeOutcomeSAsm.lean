import EvmAsm.Codegen.Programs.RlpFieldToU256BeComposeSAsm

namespace EvmAsm.Codegen.RlpFieldToU256BeSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

def successOutcome (sp0 listBase outputPtr : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (((.x5 ↦ᵣ offsetCell) ** (.x6 ↦ᵣ (0 : Word)) ** regOwn .x7 **
      (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outputPtr) ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) **
      (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
      copyCarry sp0 saved v11 v12 ** bytesRegion listBase bytes **
      bytesRegion outputPtr (rightAligned32 bytes offset len)) **
      ⌜Result bytes listBase listLen index 0
        (rightAligned32 bytes offset len)⌝) h

theorem successDoneToOutcome
    (sp0 listBase outputPtr : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsTripleWithin 2 (B + 136) (B + 156) code
      (successDone sp0 listBase outputPtr saved bytes listLen index)
      (successOutcome sp0 listBase outputPtr saved bytes listLen index) := by
  unfold successDone
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun offset => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun len => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v11 => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v12 => ?_)
  let H : Assertion :=
    (.x5 ↦ᵣ offsetCell) ** (.x6 ↦ᵣ (0 : Word)) ** regOwn .x7 **
    (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outputPtr) ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) **
    (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
    copyCarry sp0 saved v11 v12 ** bytesRegion listBase bytes **
    bytesRegion outputPtr (rightAligned32 bytes offset len)
  refine cpsTripleWithin_weaken (fun h hp => by
      obtain ⟨hstate, hsem⟩ := (sepConj_pure_right h).1 hp
      exact (sepConj_pure_left h).2 ⟨hsem, hstate⟩)
    (fun _ hp => hp) (cpsTripleWithin_pure_pre
      (P := ListSuccess bytes listBase listLen index offset len ∧ len.toNat ≤ 32)
      (H := H) (fun hsem => ?_))
  let F : Assertion :=
    (.x5 ↦ᵣ offsetCell) ** (.x6 ↦ᵣ (0 : Word)) ** regOwn .x7 **
    (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outputPtr) ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) **
    (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
    (.x2 ↦ᵣ sp0) ** (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
    (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** stackFree sp0 8 **
    (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
    regOwn .x31 ** bytesRegion listBase bytes **
    bytesRegion outputPtr (rightAligned32 bytes offset len)
  have ht := successStatusTail (0 : Word) F (by unfold F; pcf)
  refine cpsTripleWithin_weaken (fun h hp => by
      dsimp only [H, copyCarry] at hp
      dsimp only [F] at ⊢
      xperm_hyp hp) (fun h hp => ?_) ht
  unfold successOutcome
  refine ⟨offset, len, v11, v12, ?_⟩
  apply (sepConj_pure_right h).2
  refine ⟨(by
    dsimp only [F] at hp
    unfold copyCarry
    xperm_hyp hp), ?_⟩
  exact .success offset len hsem.1 hsem.2

#print axioms successDoneToOutcome

def statusCarry (sp0 listBase : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (v11 v12 status : Word) : Assertion :=
  (.x2 ↦ᵣ sp0) ** (.x9 ↦ᵣ saved.s1) **
  (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
  (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** stackFree sp0 8 **
  (.x10 ↦ᵣ status) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
  regOwn .x13 ** regOwn .x14 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes

def tooLongOutcome (sp0 listBase outputPtr : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
      (.x5 ↦ᵣ lengthCell) ** (.x8 ↦ᵣ listBase) ** regOwn .x28 **
      regOwn .x29 ** (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
      statusCarry sp0 listBase saved bytes v11 v12 2 **
      bytesRegion outputPtr (List.replicate 32 0)) **
      ⌜Result bytes listBase listLen index 2 (List.replicate 32 0)⌝) h

theorem tooLongToOutcome
    (sp0 listBase outputPtr : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsTripleWithin 2 (B + 144) (B + 156) code
      ((lengthTooLong sp0 listBase saved bytes listLen index) **
        bytesRegion outputPtr (List.replicate 32 0))
      (tooLongOutcome sp0 listBase outputPtr saved bytes listLen index) := by
  refine cpsTripleWithin_weaken (P := fun h => ∃ offset len v11 v12,
      (((((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
        lengthRest sp0 listBase offset len saved bytes listLen index v11 v12) **
        ⌜32 < len.toNat⌝) **
        bytesRegion outputPtr (List.replicate 32 0)) h)) (fun h hp => by
      obtain ⟨g1, g2, gd, gu, hleft, hout⟩ := hp
      unfold lengthTooLong at hleft
      obtain ⟨offset, len, v11, v12, hcase⟩ := hleft
      exact ⟨offset, len, v11, v12, g1, g2, gd, gu, hcase, hout⟩)
    (fun _ hp => hp) ?_
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun offset => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun len => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v11 => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v12 => ?_)
  let H : Assertion :=
    (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
    (.x5 ↦ᵣ lengthCell) ** (.x8 ↦ᵣ listBase) ** regOwn .x28 **
    regOwn .x29 ** (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
    selectedPathCarry sp0 listBase saved bytes v11 v12 **
    bytesRegion outputPtr (List.replicate 32 0)
  refine cpsTripleWithin_weaken (fun h hp => by
      extract_pure_deep hp
      obtain ⟨hlong, hp⟩ := hp
      unfold lengthRest at hp
      extract_pure_deep hp
      obtain ⟨h_ok, hp⟩ := hp
      apply (sepConj_pure_left h).2
      exact ⟨⟨h_ok, hlong⟩, (by unfold H; xperm_hyp hp)⟩)
    (fun _ hp => hp) (cpsTripleWithin_pure_pre
      (P := ListSuccess bytes listBase listLen index offset len ∧ 32 < len.toNat)
      (H := H) (fun hsem => ?_))
  let F : Assertion :=
    (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
    (.x5 ↦ᵣ lengthCell) ** (.x8 ↦ᵣ listBase) ** regOwn .x28 **
    regOwn .x29 ** (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
    (.x2 ↦ᵣ sp0) ** (.x9 ↦ᵣ saved.s1) **
    (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
    (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** stackFree sp0 8 **
    (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion listBase bytes **
    bytesRegion outputPtr (List.replicate 32 0)
  have ht := tooLongStatusTail (0 : Word) F (by unfold F; pcf)
  refine cpsTripleWithin_weaken (fun h hp => by
      dsimp only [H] at hp
      unfold selectedPathCarry at hp
      dsimp only [F] at ⊢
      xperm_hyp hp) (fun h hp => ?_) ht
  unfold tooLongOutcome
  refine ⟨offset, len, v11, v12, ?_⟩
  apply (sepConj_pure_right h).2
  refine ⟨(by
    dsimp only [F] at hp
    unfold statusCarry
    xperm_hyp hp), ?_⟩
  exact .tooLong offset len hsem.1 hsem.2

#print axioms tooLongToOutcome

def failureOutcome (sp0 listBase outputPtr oldOffset oldLen : Word)
    (saved : ListSaved) (bytes : List (BitVec 8))
    (listLen index : Nat) : Assertion :=
  fun h => ∃ v11 v12,
    (((listCallCore sp0 listBase offsetCell lengthCell saved bytes 1 oldOffset
        oldLen v11 v12) ** bytesRegion outputPtr (List.replicate 32 0)) **
      ⌜Result bytes listBase listLen index 1 (List.replicate 32 0)⌝) h

theorem failureToOutcome
    (sp0 listBase outputPtr oldOffset oldLen : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsTripleWithin 1 (B + 152) (B + 156) code
      ((listFailed sp0 listBase offsetCell lengthCell oldOffset oldLen saved
          bytes listLen index) ** bytesRegion outputPtr (List.replicate 32 0))
      (failureOutcome sp0 listBase outputPtr oldOffset oldLen saved bytes
        listLen index) := by
  refine cpsTripleWithin_weaken (P := fun h => ∃ v11 v12,
      (((listCallCore sp0 listBase offsetCell lengthCell saved bytes 1 oldOffset
        oldLen v11 v12 **
        ⌜ListFailure bytes listBase listLen index⌝) **
        bytesRegion outputPtr (List.replicate 32 0)) h)) (fun h hp => by
      obtain ⟨g1, g2, gd, gu, hleft, hout⟩ := hp
      unfold listFailed EvmAsm.Codegen.RlpFieldToU64SAsm.listFailed at hleft
      obtain ⟨v11, v12, hcase⟩ := hleft
      exact ⟨v11, v12, g1, g2, gd, gu, hcase, hout⟩)
    (fun _ hp => hp) ?_
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v11 => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v12 => ?_)
  let H : Assertion :=
    (((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      listCallRest sp0 listBase offsetCell lengthCell saved bytes oldOffset oldLen
        v11 v12) ** bytesRegion outputPtr (List.replicate 32 0))
  refine cpsTripleWithin_weaken (fun h hp => by
      obtain ⟨g1, g2, gd, gu, hcase, hout⟩ := hp
      obtain ⟨hstate, h_fail⟩ := (sepConj_pure_right g1).1 hcase
      apply (sepConj_pure_left h).2
      exact ⟨h_fail, g1, g2, gd, gu, hstate, hout⟩)
    (fun _ hp => hp) (cpsTripleWithin_pure_pre
      (P := ListFailure bytes listBase listLen index) (H := H)
      (fun h_fail => ?_))
  let F : Assertion :=
    (.x0 ↦ᵣ (0 : Word)) **
    listCallRest sp0 listBase offsetCell lengthCell saved bytes oldOffset oldLen
      v11 v12 ** bytesRegion outputPtr (List.replicate 32 0)
  have ht := failureStatusTail (1 : Word) F (by unfold F; pcf)
  refine cpsTripleWithin_weaken (fun h hp => by
      dsimp only [H] at hp
      dsimp only [F] at ⊢
      xperm_hyp hp) (fun h hp => ?_) ht
  unfold failureOutcome
  refine ⟨v11, v12, ?_⟩
  apply (sepConj_pure_right h).2
  refine ⟨(by
    dsimp only [F] at hp
    change ((((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      listCallRest sp0 listBase offsetCell lengthCell saved bytes oldOffset oldLen
        v11 v12) ** bytesRegion outputPtr (List.replicate 32 0)) h)
    xperm_hyp hp), ?_⟩
  exact .listFailure h_fail

#print axioms failureToOutcome

def joinedOutcome (sp0 listBase outputPtr oldOffset oldLen : Word)
    (saved : ListSaved) (bytes : List (BitVec 8))
    (listLen index : Nat) : Assertion := fun h =>
  successOutcome sp0 listBase outputPtr saved bytes listLen index h ∨
  tooLongOutcome sp0 listBase outputPtr saved bytes listLen index h ∨
  failureOutcome sp0 listBase outputPtr oldOffset oldLen saved bytes listLen
    index h

theorem selectedToJoined
    (sp0 listBase outputPtr oldOffset oldLen : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hs0 : saved.s0 = listBase) (hs1 : saved.s1 = outputPtr)
    (hsalign : listBase.toNat % 8 = 0)
    (hoalign : outputPtr.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hoover : outputPtr.toNat + 32 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (houtvalid : ∀ k, k < 32 →
      isValidByteAccess (outputPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (4 + 1 + (6 + (7 * 32 + 1) + 2))
      (B + 64) (B + 156) code
      ((listSelected sp0 listBase offsetCell lengthCell saved bytes listLen
          index) ** bytesRegion outputPtr (List.replicate 32 0))
      (joinedOutcome sp0 listBase outputPtr oldOffset oldLen saved bytes
        listLen index) := by
  have hl0 := selectedLength sp0 listBase saved bytes listLen index hs0
  have hl := cpsTripleWithin_frameR
    (bytesRegion outputPtr (List.replicate 32 0)) (by pcf) hl0
  have hb0 := lengthBranch sp0 listBase saved bytes listLen index
  have hb := cpsBranchWithin_frameR
    (bytesRegion outputPtr (List.replicate 32 0)) (by pcf) hb0
  have hf0 := fitToSuccessDone sp0 listBase outputPtr saved bytes listLen index
    hs1 hsalign hoalign hslack hover hoover hvalid houtvalid
  have hf1 := cpsTripleWithin_seq_same_cr hf0
    (successDoneToOutcome sp0 listBase outputPtr saved bytes listLen index)
  have hf := cpsTripleWithin_weaken
    (Q' := joinedOutcome sp0 listBase outputPtr oldOffset oldLen saved bytes
      listLen index) (fun _ hp => hp)
    (fun _ hp => by unfold joinedOutcome; exact Or.inl hp) hf1
  have ht0 := tooLongToOutcome sp0 listBase outputPtr saved bytes listLen index
  have ht1 := cpsTripleWithin_mono_nSteps
    (nSteps' := 6 + (7 * 32 + 1) + 2) (by decide) ht0
  have ht := cpsTripleWithin_weaken
    (Q' := joinedOutcome sp0 listBase outputPtr oldOffset oldLen saved bytes
      listLen index) (fun _ hp => hp)
    (fun _ hp => by unfold joinedOutcome; exact Or.inr (Or.inl hp)) ht1
  have hm := cpsBranchWithin_merge_same_cr hb ht hf
  simpa only [Nat.add_assoc] using
    cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hl hm

#print axioms selectedToJoined

theorem listDispatchToJoined
    (sp0 listBase outputPtr oldOffset oldLen : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hs0 : saved.s0 = listBase) (hs1 : saved.s1 = outputPtr)
    (hsalign : listBase.toNat % 8 = 0)
    (hoalign : outputPtr.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hoover : outputPtr.toNat + 32 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (houtvalid : ∀ k, k < 32 →
      isValidByteAccess (outputPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + (4 + 1 + (6 + (7 * 32 + 1) + 2)))
      (B + 60) (B + 156) code
      ((listCallResult sp0 listBase offsetCell lengthCell oldOffset oldLen saved
          bytes listLen index) ** bytesRegion outputPtr (List.replicate 32 0))
      (joinedOutcome sp0 listBase outputPtr oldOffset oldLen saved bytes
        listLen index) := by
  have hb0 := listResultBranch sp0 listBase offsetCell lengthCell oldOffset oldLen
    saved bytes listLen index
  have hb := cpsBranchWithin_frameR
    (bytesRegion outputPtr (List.replicate 32 0)) (by pcf) hb0
  have hs0' := selectedToJoined sp0 listBase outputPtr oldOffset oldLen saved
    bytes listLen index hs0 hs1 hsalign hoalign hslack hover hoover hvalid
    houtvalid
  have hs := hs0'
  have hf0 := failureToOutcome sp0 listBase outputPtr oldOffset oldLen saved
    bytes listLen index
  have hf1 := cpsTripleWithin_mono_nSteps
    (nSteps' := 4 + 1 + (6 + (7 * 32 + 1) + 2)) (by decide) hf0
  have hf := cpsTripleWithin_weaken
    (Q' := joinedOutcome sp0 listBase outputPtr oldOffset oldLen saved bytes
      listLen index) (fun _ hp => hp)
    (fun _ hp => by unfold joinedOutcome; exact Or.inr (Or.inr hp)) hf1
  have hm := cpsBranchWithin_merge_same_cr hb hf hs
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => hp) hm

#print axioms listDispatchToJoined

end EvmAsm.Codegen.RlpFieldToU256BeSAsm
