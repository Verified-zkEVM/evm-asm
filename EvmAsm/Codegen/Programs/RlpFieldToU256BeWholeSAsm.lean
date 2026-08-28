import EvmAsm.Codegen.Programs.RlpFieldToU256BeRestoreSAsm

namespace EvmAsm.Codegen.RlpFieldToU256BeSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

theorem dispatchAndRestore
    (spOuter newSp listBase outputPtr oldOffset oldLen : Word) (outer : Saved)
    (saved : ListSaved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (hs0 : saved.s0 = listBase) (hs1 : saved.s1 = outputPtr)
    (hsalign : listBase.toNat % 8 = 0)
    (hoalign : outputPtr.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hoover : outputPtr.toNat + 32 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (houtvalid : ∀ k, k < 32 →
      isValidByteAccess (outputPtr + BitVec.ofNat 64 k) = true)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hret : outer.ra &&& ~~~(1 : Word) = outer.ra) :
    cpsTripleWithin ((1 + (4 + 1 + (6 + (7 * 32 + 1) + 2))) + 5)
      (B + 60) outer.ra code
      ((((.x1 ↦ᵣ (B + 60)) **
        listCallResult newSp listBase offsetCell lengthCell oldOffset oldLen saved
          bytes listLen index) ** bytesRegion outputPtr (List.replicate 32 0)) **
        savedFrame newSp outer)
      (returnedOutcome spOuter newSp listBase outputPtr oldOffset oldLen outer
        saved bytes listLen index) := by
  have hd0 := listDispatchToJoined newSp listBase outputPtr oldOffset oldLen saved
    bytes listLen index hs0 hs1 hsalign hoalign hslack hover hoover hvalid
    houtvalid
  have hd := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (B + 60)) ** savedFrame newSp outer)
    (by unfold savedFrame; pcf) hd0
  have hd' := cpsTripleWithin_weaken
    (P' := ((((.x1 ↦ᵣ (B + 60)) **
      listCallResult newSp listBase offsetCell lengthCell oldOffset oldLen saved
        bytes listLen index) ** bytesRegion outputPtr (List.replicate 32 0)) **
      savedFrame newSp outer))
    (Q' := (((.x1 ↦ᵣ (B + 60)) **
      joinedOutcome newSp listBase outputPtr oldOffset oldLen saved bytes listLen
        index) ** savedFrame newSp outer)) (fun h hp => by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp)
    (fun h hp => by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp) hd
  have hr := restoreJoined spOuter newSp listBase outputPtr oldOffset oldLen outer
    saved bytes listLen index hs0 hs1 hnewSp hret
  exact cpsTripleWithin_seq_same_cr hd' hr

@[irreducible] def wholeRest
    (listBase listLenW indexW outputPtr oldOffset oldLen old14 : Word)
    (s2 s3 s4 s5 : Word) (bytes output : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
  (.x13 ↦ᵣ outputPtr) ** (.x14 ↦ᵣ old14) ** regOwn .x5 ** regOwn .x6 **
  regOwn .x7 ** (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
  (.x21 ↦ᵣ s5) ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
  regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
  bytesRegion outputPtr output ** (offsetCell ↦ₘ oldOffset) **
  (lengthCell ↦ₘ oldLen)

theorem setupAndCall
    (spOuter newSp listBase listLenW indexW outputPtr oldOffset oldLen old14 : Word)
    (outer : Saved) (s2 s3 s4 s5 : Word)
    (bytes output : List (BitVec 8)) (listLen index : Nat)
    (houtput : output.length = 32)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index) (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let saved : ListSaved :=
      { ra := B + 60, s0 := listBase, s1 := outputPtr, s2 := s2, s3 := s3,
        s4 := s4, s5 := s5 }
    let callSteps := 1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
    cpsTripleWithin (4 + (2 + (4 + (4 + callSteps)))) B (B + 60) code
      ((.x2 ↦ᵣ spOuter) ** regsAt frame (savedVals outer) **
        frameSlotsOwn frame newSp ** stackFree newSp 8 **
        wholeRest listBase listLenW indexW outputPtr oldOffset oldLen old14
          s2 s3 s4 s5 bytes output)
      ((((.x1 ↦ᵣ (B + 60)) **
        listCallResult newSp listBase offsetCell lengthCell oldOffset oldLen saved
          bytes listLen index) ** bytesRegion outputPtr (List.replicate 32 0)) **
        savedFrame newSp outer) := by
  dsimp
  let saved : ListSaved :=
    { ra := B + 60, s0 := listBase, s1 := outputPtr, s2 := s2, s3 := s3,
      s4 := s4, s5 := s5 }
  let F0 : Assertion := stackFree newSp 8 **
    wholeRest listBase listLenW indexW outputPtr oldOffset oldLen old14
      s2 s3 s4 s5 bytes output
  have hp := setupPrologue spOuter newSp outer F0 hnewSp (by
    unfold F0 wholeRest; pcf)
  let F1 : Assertion :=
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ outer.ra) ** savedFrame newSp outer **
    stackFree newSp 8 ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
    (.x14 ↦ᵣ old14) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
    bytesRegion outputPtr output ** (offsetCell ↦ₘ oldOffset) **
    (lengthCell ↦ₘ oldLen)
  have hm := setupMoves listBase outputPtr outer.s0 outer.s1 F1
    (by unfold F1 savedFrame; pcf)
  have hpm := cpsTripleWithin_seq_perm_same_cr (fun h hp' => by
    rw [regsAt_frame] at hp'
    unfold F0 wholeRest F1 at *
    xperm_hyp hp') hp hm
  let F2 : Assertion :=
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ outer.ra) ** (.x8 ↦ᵣ listBase) **
    savedFrame newSp outer ** stackFree newSp 8 ** (.x10 ↦ᵣ listBase) **
    (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) ** (.x13 ↦ᵣ outputPtr) **
    (.x14 ↦ᵣ old14) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    bytesRegion listBase bytes ** (offsetCell ↦ₘ oldOffset) **
    (lengthCell ↦ₘ oldLen)
  have hz0 := zeroOutput outputPtr output houtput
  have hz := cpsTripleWithin_frameR F2 (by unfold F2 savedFrame; pcf) hz0
  have hpmz := cpsTripleWithin_seq_perm_same_cr (fun h hp' => by
    unfold F1 F2 at *
    xperm_hyp hp') hpm hz
  let F3 : Assertion :=
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ outer.ra) ** (.x8 ↦ᵣ listBase) **
    (.x9 ↦ᵣ outputPtr) ** savedFrame newSp outer ** stackFree newSp 8 **
    (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x18 ↦ᵣ s2) **
    (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion listBase bytes ** bytesRegion outputPtr (List.replicate 32 0) **
    (offsetCell ↦ₘ oldOffset) ** (lengthCell ↦ₘ oldLen)
  have hg := setupGlobals outputPtr old14 F3 (by unfold F3 savedFrame; pcf)
  have hpmzg := cpsTripleWithin_seq_perm_same_cr (fun h hp' => by
    unfold F2 F3 at *
    xperm_hyp hp') hpmz hg
  have hc0 := callListNth newSp listBase listLenW indexW offsetCell lengthCell
    oldOffset oldLen outer.ra listBase outputPtr s2 s3 s4 s5 bytes listLen index
    hlistLenW hindexW hindex hsalign hslack hover hvalid
  have hc := cpsTripleWithin_frameR
    (bytesRegion outputPtr (List.replicate 32 0) ** savedFrame newSp outer)
    (by unfold savedFrame; pcf) hc0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun h hp' => by
    simp only [F3, EvmAsm.Codegen.RlpFieldToU64SAsm.listSavedRegs,
      EvmAsm.Codegen.RlpFieldToU64SAsm.listOtherSaved,
      EvmAsm.Codegen.RlpListNthItemSAsm.entryRest] at hp' ⊢
    xperm_hyp hp') hpmzg hc
  have hall' := cpsTripleWithin_weaken
    (P' := ((.x2 ↦ᵣ spOuter) ** regsAt frame (savedVals outer) **
      frameSlotsOwn frame newSp ** stackFree newSp 8 **
      wholeRest listBase listLenW indexW outputPtr oldOffset oldLen old14
        s2 s3 s4 s5 bytes output))
    (Q' := ((((.x1 ↦ᵣ (B + 60)) **
      listCallResult newSp listBase offsetCell lengthCell oldOffset oldLen saved
        bytes listLen index) ** bytesRegion outputPtr (List.replicate 32 0)) **
      savedFrame newSp outer)) (fun h hp' => by
      dsimp only [F0] at ⊢
      xperm_hyp hp') (fun h hp' => by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp') hall
  simp only [Nat.add_assoc] at hall' ⊢
  exact hall'

theorem rlpFieldToU256Be_spec_within
    (spOuter newSp listBase listLenW indexW outputPtr oldOffset oldLen old14 : Word)
    (outer : Saved) (s2 s3 s4 s5 : Word)
    (bytes output : List (BitVec 8)) (listLen index : Nat)
    (houtput : output.length = 32)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index) (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hoalign : outputPtr.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hoover : outputPtr.toNat + 32 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (houtvalid : ∀ k, k < 32 →
      isValidByteAccess (outputPtr + BitVec.ofNat 64 k) = true)
    (hret : outer.ra &&& ~~~(1 : Word) = outer.ra) :
    let saved : ListSaved :=
      { ra := B + 60, s0 := listBase, s1 := outputPtr, s2 := s2, s3 := s3,
        s4 := s4, s5 := s5 }
    let callSteps := 1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
    let tailSteps := (1 + (4 + 1 + (6 + (7 * 32 + 1) + 2))) + 5
    cpsTripleWithin ((4 + (2 + (4 + (4 + callSteps)))) + tailSteps)
      B outer.ra code
      ((.x2 ↦ᵣ spOuter) ** regsAt frame (savedVals outer) **
        frameSlotsOwn frame newSp ** stackFree newSp 8 **
        wholeRest listBase listLenW indexW outputPtr oldOffset oldLen old14
          s2 s3 s4 s5 bytes output)
      (returnedOutcome spOuter newSp listBase outputPtr oldOffset oldLen outer
        saved bytes listLen index) := by
  dsimp
  let saved : ListSaved :=
    { ra := B + 60, s0 := listBase, s1 := outputPtr, s2 := s2, s3 := s3,
      s4 := s4, s5 := s5 }
  have hs := setupAndCall spOuter newSp listBase listLenW indexW outputPtr
    oldOffset oldLen old14 outer s2 s3 s4 s5 bytes output listLen index
    houtput hnewSp hlistLenW hindexW hindex hsalign hslack hover hvalid
  have ht := dispatchAndRestore spOuter newSp listBase outputPtr oldOffset oldLen
    outer saved bytes listLen index (by rfl) (by rfl) hsalign hoalign hslack
    hover hoover hvalid houtvalid hnewSp hret
  exact cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hs ht

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

/-! A flat caller view of the strict K35 wrapper.

`rlpFieldToU256Be_spec_within` keeps the caller link in `regsAt frame`.
Cross-call users need that link as a standalone atom, while retaining the
same K20 result, output bytes, scratch cells, and saved frame.  These
assertions are a structural projection only; no semantic case is weakened.
-/

def flatPre
    (spOuter newSp listBase listLenW indexW outputPtr oldOffset oldLen old14 : Word)
    (outer : Saved) (s2 s3 s4 s5 : Word) (bytes output : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spOuter) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
  frameSlotsOwn frame newSp ** stackFree newSp 8 **
  wholeRest listBase listLenW indexW outputPtr oldOffset oldLen old14
    s2 s3 s4 s5 bytes output

def flatSuccessReturned
    (spOuter newSp listBase outputPtr : Word) (outer : Saved)
    (saved : ListSaved) (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (((.x2 ↦ᵣ spOuter) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
      savedFrame newSp outer) **
      successPayload newSp listBase outputPtr offset len v11 v12 saved bytes
        listLen index) h

def flatTooLongReturned
    (spOuter newSp listBase outputPtr : Word) (outer : Saved)
    (saved : ListSaved) (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (((.x2 ↦ᵣ spOuter) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
      savedFrame newSp outer) **
      tooLongPayload newSp listBase outputPtr offset len v11 v12 saved bytes
        listLen index) h

def flatFailureReturned
    (spOuter newSp listBase outputPtr oldOffset oldLen : Word) (outer : Saved)
    (saved : ListSaved) (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ v11 v12,
    (((.x2 ↦ᵣ spOuter) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
      savedFrame newSp outer) **
      failurePayload newSp listBase outputPtr oldOffset oldLen v11 v12 saved bytes
        listLen index) h

def flatPost
    (spOuter newSp listBase outputPtr oldOffset oldLen : Word) (outer : Saved)
    (saved : ListSaved) (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h =>
    flatSuccessReturned spOuter newSp listBase outputPtr outer saved bytes listLen index h ∨
    flatTooLongReturned spOuter newSp listBase outputPtr outer saved bytes listLen index h ∨
    flatFailureReturned spOuter newSp listBase outputPtr oldOffset oldLen outer saved
      bytes listLen index h

-- The adapter reuses K35's emitted wrapper unchanged.
#guard rlpFieldToU256Be_prog.length = 44

theorem rlpFieldToU256Be_flat_spec_within
    (spOuter newSp listBase listLenW indexW outputPtr oldOffset oldLen old14 : Word)
    (outer : Saved) (s2 s3 s4 s5 : Word)
    (bytes output : List (BitVec 8)) (listLen index : Nat)
    (houtput : output.length = 32)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index) (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hoalign : outputPtr.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hoover : outputPtr.toNat + 32 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (houtvalid : ∀ k, k < 32 →
      isValidByteAccess (outputPtr + BitVec.ofNat 64 k) = true)
    (hret : outer.ra &&& ~~~(1 : Word) = outer.ra) :
    let saved : ListSaved :=
      { ra := B + 60, s0 := listBase, s1 := outputPtr, s2 := s2, s3 := s3,
        s4 := s4, s5 := s5 }
    let callSteps := 1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
    let tailSteps := (1 + (4 + 1 + (6 + (7 * 32 + 1) + 2))) + 5
    cpsTripleWithin ((4 + (2 + (4 + (4 + callSteps)))) + tailSteps)
      B outer.ra code
      ((.x1 ↦ᵣ outer.ra) **
       flatPre spOuter newSp listBase listLenW indexW outputPtr oldOffset oldLen old14
         outer s2 s3 s4 s5 bytes output)
      ((.x1 ↦ᵣ outer.ra) **
       flatPost spOuter newSp listBase outputPtr oldOffset oldLen outer saved bytes listLen
         index) := by
  dsimp
  let saved : ListSaved :=
    { ra := B + 60, s0 := listBase, s1 := outputPtr, s2 := s2, s3 := s3,
      s4 := s4, s5 := s5 }
  have hwhole := rlpFieldToU256Be_spec_within spOuter newSp listBase listLenW indexW
    outputPtr oldOffset oldLen old14 outer s2 s3 s4 s5 bytes output listLen index
    houtput hnewSp hlistLenW hindexW hindex hsalign hoalign hslack hover hoover hvalid
    houtvalid hret
  refine cpsTripleWithin_weaken
    (P' := ((.x1 ↦ᵣ outer.ra) **
      flatPre spOuter newSp listBase listLenW indexW outputPtr oldOffset oldLen old14
        outer s2 s3 s4 s5 bytes output))
    (Q' := ((.x1 ↦ᵣ outer.ra) **
      flatPost spOuter newSp listBase outputPtr oldOffset oldLen outer saved bytes listLen
        index))
    (fun h hp => ?_) (fun h hq => ?_) hwhole
  · unfold flatPre at hp
    rw [regsAt_frame]
    xperm_hyp hp
  · unfold returnedOutcome at hq
    rcases hq with hs | ht | hf
    · unfold successReturned at hs
      rw [regsAt_frame] at hs
      obtain ⟨offset, len, v11, v12, hs⟩ := hs
      have hflat : ((.x1 ↦ᵣ outer.ra) **
          flatSuccessReturned spOuter newSp listBase outputPtr outer saved bytes listLen
            index) h := by
        have hfixed : ((.x1 ↦ᵣ outer.ra) **
            (((.x2 ↦ᵣ spOuter) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
              savedFrame newSp outer) **
             successPayload newSp listBase outputPtr offset len v11 v12 saved bytes
               listLen index)) h := by
          xperm_hyp hs
        exact sepConj_mono_right
          (fun _ hp => ⟨offset, len, v11, v12, hp⟩) h hfixed
      exact sepConj_mono_right (fun _ hp => Or.inl hp) h hflat
    · unfold tooLongReturned at ht
      rw [regsAt_frame] at ht
      obtain ⟨offset, len, v11, v12, ht⟩ := ht
      have hflat : ((.x1 ↦ᵣ outer.ra) **
          flatTooLongReturned spOuter newSp listBase outputPtr outer saved bytes listLen
            index) h := by
        have hfixed : ((.x1 ↦ᵣ outer.ra) **
            (((.x2 ↦ᵣ spOuter) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
              savedFrame newSp outer) **
             tooLongPayload newSp listBase outputPtr offset len v11 v12 saved bytes
               listLen index)) h := by
          xperm_hyp ht
        exact sepConj_mono_right
          (fun _ hp => ⟨offset, len, v11, v12, hp⟩) h hfixed
      exact sepConj_mono_right (fun _ hp => Or.inr (Or.inl hp)) h hflat
    · unfold failureReturned at hf
      rw [regsAt_frame] at hf
      obtain ⟨v11, v12, hf⟩ := hf
      have hflat : ((.x1 ↦ᵣ outer.ra) **
          flatFailureReturned spOuter newSp listBase outputPtr oldOffset oldLen outer
            saved bytes listLen index) h := by
        have hfixed : ((.x1 ↦ᵣ outer.ra) **
            (((.x2 ↦ᵣ spOuter) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
              savedFrame newSp outer) **
             failurePayload newSp listBase outputPtr oldOffset oldLen v11 v12 saved bytes
               listLen index)) h := by
          xperm_hyp hf
        exact sepConj_mono_right
          (fun _ hp => ⟨v11, v12, hp⟩) h hfixed
      exact sepConj_mono_right (fun _ hp => Or.inr (Or.inr hp)) h hflat

end EvmAsm.Codegen.RlpFieldToU256BeSAsm
