import EvmAsm.Codegen.Programs.RlpFieldToU64FinishSAsm

namespace EvmAsm.Codegen.RlpFieldToU64SAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

theorem allJoinedResult_to_restoreReady
    (newSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : ∀ h,
    (allJoinedResult newSp listBase oldOffset oldLen saved bytes listLen index **
      savedFrame newSp outer) h →
    allRestoreReady newSp newSp listBase oldOffset oldLen outer saved bytes
      listLen index h := by
  intro h hp
  obtain ⟨h1, h2, hd, hu, hj, hsf⟩ := hp
  unfold allJoinedResult at hj
  unfold allRestoreReady
  rcases hj with hs | hf
  · left
    exact joinedResult_to_restoreReady newSp newSp listBase outer saved bytes
      listLen index h ⟨h1, h2, hd, hu, hs, hsf⟩
  · right
    exact failureResult_to_restoreReady newSp newSp listBase oldOffset oldLen outer
      saved bytes listLen index h ⟨h1, h2, hd, hu, hf, hsf⟩


theorem dispatchAndRestore
    (spOuter newSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hs0 : saved.s0 = listBase)
    (hsalign : listBase.toNat % 8 = 0)
    (hbytes : listLen ≤ bytes.length)
    (hnowrap : listBase.toNat + listLen + 9 < 2 ^ 64)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnz : 0 < bytes.length)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hret : outer.ra &&& ~~~(1 : Word) = outer.ra) :
    let tailSteps := (7 + (1 + (7 * bytes.length + 11))) + 5
    cpsTripleWithin ((1 + tailSteps) + 5) (B + 48) outer.ra code
      ((((.x1 ↦ᵣ (B + 48)) **
        listCallResult newSp listBase offsetCell lengthCell oldOffset oldLen saved
          bytes listLen index) ** (saved.s1 ↦ₘ (0 : Word))) **
        savedFrame newSp outer)
      (allReturned spOuter newSp listBase oldOffset oldLen outer saved bytes
        listLen index) := by
  dsimp
  have hd0 := listDispatchToJoin newSp listBase oldOffset oldLen saved bytes
    listLen index hs0 hsalign hbytes hnowrap hover hvalid hnz
  have hd := cpsTripleWithin_frameR (savedFrame newSp outer)
    (by unfold savedFrame; pcf) hd0
  have hd' := cpsTripleWithin_weaken (fun _ hp => hp)
    (allJoinedResult_to_restoreReady newSp listBase oldOffset oldLen outer saved
      bytes listLen index) hd
  have hr := restoreAll spOuter newSp listBase oldOffset oldLen outer saved bytes
    listLen index hnewSp hret
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hd' hr


@[irreducible] def wholeRest
    (listBase listLenW indexW outputPtr oldOut oldOffset oldLen old14 : Word)
    (s2 s3 s4 s5 : Word) (bytes : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
  (.x13 ↦ᵣ outputPtr) ** (.x14 ↦ᵣ old14) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
  (outputPtr ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) **
  (lengthCell ↦ₘ oldLen)

theorem prologueAndMoves
    (spOuter newSp listBase listLenW indexW outputPtr oldOut oldOffset oldLen old14 : Word)
    (outer : Saved) (s2 s3 s4 s5 : Word) (bytes : List (BitVec 8))
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12)) :
    cpsTripleWithin 7 B (B + 28) code
      ((.x2 ↦ᵣ spOuter) ** regsAt frame (savedVals outer) **
       frameSlotsOwn frame newSp ** stackFree newSp 8 **
       wholeRest listBase listLenW indexW outputPtr oldOut oldOffset oldLen old14
         s2 s3 s4 s5 bytes)
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ outer.ra) ** (.x8 ↦ᵣ listBase) **
       (.x9 ↦ᵣ outputPtr) ** savedFrame newSp outer **
       stackFree newSp 8 **
       wholeRest listBase listLenW indexW outputPtr 0 oldOffset oldLen old14
         s2 s3 s4 s5 bytes) := by
  have hp := setupPrologue spOuter newSp outer
    (stackFree newSp 8 **
      wholeRest listBase listLenW indexW outputPtr oldOut oldOffset oldLen old14
        s2 s3 s4 s5 bytes) hnewSp (by unfold wholeRest; pcf)
  let F : Assertion :=
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ outer.ra) ** savedFrame newSp outer **
    stackFree newSp 8 **
    (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) ** (.x14 ↦ᵣ old14) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x18 ↦ᵣ s2) **
    (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    bytesRegion listBase bytes ** (offsetCell ↦ₘ oldOffset) **
    (lengthCell ↦ₘ oldLen)
  have hm := setupMovesZero listBase outputPtr oldOut outer.s0 outer.s1 F
    (by unfold F savedFrame; pcf)
  have hpm := cpsTripleWithin_seq_perm_same_cr (fun h hp' => by
    rw [regsAt_frame] at hp'
    unfold wholeRest F at *
    xperm_hyp hp') hp hm
  exact cpsTripleWithin_weaken (fun _ hp' => hp') (fun h hp' => by
    unfold wholeRest F at *
    xperm_hyp hp') hpm


theorem setupAndCall
    (spOuter newSp listBase listLenW indexW outputPtr oldOut oldOffset oldLen old14 : Word)
    (outer : Saved) (s2 s3 s4 s5 : Word) (bytes : List (BitVec 8))
    (listLen index : Nat)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index) (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hbytes : listLen ≤ bytes.length)
    (hnowrap : listBase.toNat + listLen + 9 < 2 ^ 64)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnz : 0 < bytes.length) :
    let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := B + 48, s0 := listBase, s1 := outputPtr, s2 := s2, s3 := s3,
        s4 := s4, s5 := s5 }
    cpsTripleWithin
      (7 + 4 + (1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)))
      B (B + 48) code
      ((.x2 ↦ᵣ spOuter) ** regsAt frame (savedVals outer) **
       frameSlotsOwn frame newSp ** stackFree newSp 8 **
       wholeRest listBase listLenW indexW outputPtr oldOut oldOffset oldLen old14
         s2 s3 s4 s5 bytes)
      ((((.x1 ↦ᵣ (B + 48)) **
        listCallResult newSp listBase offsetCell lengthCell oldOffset oldLen saved
          bytes listLen index) ** (outputPtr ↦ₘ (0 : Word))) **
        savedFrame newSp outer) := by
  dsimp
  let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
    { ra := B + 48, s0 := listBase, s1 := outputPtr, s2 := s2, s3 := s3,
      s4 := s4, s5 := s5 }
  have hpm := prologueAndMoves spOuter newSp listBase listLenW indexW outputPtr
    oldOut oldOffset oldLen old14 outer s2 s3 s4 s5 bytes hnewSp
  let FG : Assertion :=
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ outer.ra) ** (.x8 ↦ᵣ listBase) **
    (.x9 ↦ᵣ outputPtr) ** savedFrame newSp outer ** stackFree newSp 8 **
    (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x18 ↦ᵣ s2) **
    (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
    (outputPtr ↦ₘ (0 : Word)) ** (offsetCell ↦ₘ oldOffset) **
    (lengthCell ↦ₘ oldLen)
  have hg := setupGlobals outputPtr old14 FG (by unfold FG savedFrame; pcf)
  have hpg := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    unfold wholeRest FG at *
    xperm_hyp hp) hpm hg
  have hc0 := callListNth newSp listBase listLenW indexW offsetCell lengthCell
    oldOffset oldLen outer.ra listBase outputPtr s2 s3 s4 s5 bytes listLen index
    hlistLenW hindexW hindex hsalign hbytes hnowrap hover hvalid hnz
  have hc := cpsTripleWithin_frameR
    ((outputPtr ↦ₘ (0 : Word)) ** savedFrame newSp outer)
    (by unfold savedFrame; pcf) hc0
  have hpgc := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    unfold FG listSavedRegs listOtherSaved
      EvmAsm.Codegen.RlpListNthItemSAsm.entryRest at *
    xperm_hyp hp) hpg hc
  have hpost : ∀ h,
      ((((.x1 ↦ᵣ (B + 48)) **
          listCallResult newSp listBase offsetCell lengthCell oldOffset oldLen
            saved bytes listLen index) **
        (outputPtr ↦ₘ (0 : Word)) ** savedFrame newSp outer) h) →
      (((((.x1 ↦ᵣ (B + 48)) **
          listCallResult newSp listBase offsetCell lengthCell oldOffset oldLen
            saved bytes listLen index) **
        (outputPtr ↦ₘ (0 : Word))) ** savedFrame newSp outer) h) := by
    intro h hp
    exact (sepConj_assoc h).mpr hp
  have hpgc' := cpsTripleWithin_weaken (fun _ hp => hp) hpost hpgc
  simpa only [show 7 + 4 = 11 by decide] using hpgc'


theorem rlpFieldToU64_spec_within
    (spOuter newSp listBase listLenW indexW outputPtr oldOut oldOffset oldLen old14 : Word)
    (outer : Saved) (s2 s3 s4 s5 : Word) (bytes : List (BitVec 8))
    (listLen index : Nat)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index) (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hbytes : listLen ≤ bytes.length)
    (hnowrap : listBase.toNat + listLen + 9 < 2 ^ 64)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnz : 0 < bytes.length)
    (hret : outer.ra &&& ~~~(1 : Word) = outer.ra) :
    let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := B + 48, s0 := listBase, s1 := outputPtr, s2 := s2, s3 := s3,
        s4 := s4, s5 := s5 }
    let callSteps := 1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
    let tailSteps := (7 + (1 + (7 * bytes.length + 11))) + 5
    cpsTripleWithin ((7 + 4 + callSteps) + ((1 + tailSteps) + 5))
      B outer.ra code
      ((.x2 ↦ᵣ spOuter) ** regsAt frame (savedVals outer) **
       frameSlotsOwn frame newSp ** stackFree newSp 8 **
       wholeRest listBase listLenW indexW outputPtr oldOut oldOffset oldLen old14
         s2 s3 s4 s5 bytes)
      (allReturned spOuter newSp listBase oldOffset oldLen outer saved bytes
        listLen index) := by
  dsimp
  let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
    { ra := B + 48, s0 := listBase, s1 := outputPtr, s2 := s2, s3 := s3,
      s4 := s4, s5 := s5 }
  have hs := setupAndCall spOuter newSp listBase listLenW indexW outputPtr oldOut
    oldOffset oldLen old14 outer s2 s3 s4 s5 bytes listLen index hnewSp
    hlistLenW hindexW hindex hsalign hbytes hnowrap hover hvalid hnz
  have ht := dispatchAndRestore spOuter newSp listBase oldOffset oldLen outer
    saved bytes listLen index (by rfl) hsalign hbytes hnowrap hover hvalid hnz hnewSp hret
  exact cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hs ht


end EvmAsm.Codegen.RlpFieldToU64SAsm
