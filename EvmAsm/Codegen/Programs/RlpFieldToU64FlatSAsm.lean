import EvmAsm.Codegen.Programs.RlpFieldToU64WholeSAsm

namespace EvmAsm.Codegen.RlpFieldToU64SAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

/-! A call-site view of the strict K34 wrapper.

`rlpFieldToU64_spec_within` is the whole K34 theorem: its frame assertion
bundles the saved `ra/s0/s1` registers in `regsAt frame`, and its result uses
the corresponding bundled frame again.  Cross-call callers need the link
register as a separate atom so that `callWithin_spec` can replace it with the
JAL return address.  These assertions are only a structural projection of
that theorem; the semantic `Result` relation and all scratch/output facts are
unchanged.
-/

def flatPre
    (spOuter newSp listBase listLenW indexW outputPtr oldOut oldOffset oldLen old14 : Word)
    (outer : Saved) (s2 s3 s4 s5 : Word) (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spOuter) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
  frameSlotsOwn frame newSp ** stackFree newSp 8 **
  wholeRest listBase listLenW indexW outputPtr oldOut oldOffset oldLen old14
    s2 s3 s4 s5 bytes

def flatSuccessReturned
    (spOuter newSp listBase : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v12 x5 scalarStatus wrapperStatus outputValue,
    (((.x2 ↦ᵣ spOuter) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
      savedFrame newSp outer) **
      successPayload newSp listBase offset len v12 x5 scalarStatus wrapperStatus
        outputValue saved bytes listLen index) h

def flatFailureReturned
    (spOuter newSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ v11 v12,
    (((.x2 ↦ᵣ spOuter) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
      savedFrame newSp outer) **
      failurePayload newSp listBase oldOffset oldLen v11 v12 saved bytes
        listLen index) h

def flatPost
    (spOuter newSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h =>
    flatSuccessReturned spOuter newSp listBase outer saved bytes listLen index h ∨
    flatFailureReturned spOuter newSp listBase oldOffset oldLen outer saved bytes
      listLen index h

-- This adapter reuses K34's emitted program unchanged.
#guard rlpFieldToU64_prog.length = 37

theorem rlpFieldToU64_flat_spec_within
    (spOuter newSp listBase listLenW indexW outputPtr oldOut oldOffset oldLen old14 : Word)
    (outer : Saved) (s2 s3 s4 s5 : Word) (bytes : List (BitVec 8))
    (listLen index : Nat)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index) (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hret : outer.ra &&& ~~~(1 : Word) = outer.ra) :
    let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := B + 48, s0 := listBase, s1 := outputPtr, s2 := s2, s3 := s3,
        s4 := s4, s5 := s5 }
    let callSteps := 1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
    let tailSteps := (7 + (1 + (7 * bytes.length + 11))) + 5
    cpsTripleWithin ((7 + 4 + callSteps) + ((1 + tailSteps) + 5)) B outer.ra code
      ((.x1 ↦ᵣ outer.ra) **
       flatPre spOuter newSp listBase listLenW indexW outputPtr oldOut oldOffset
         oldLen old14 outer s2 s3 s4 s5 bytes)
      ((.x1 ↦ᵣ outer.ra) **
       flatPost spOuter newSp listBase oldOffset oldLen outer saved bytes listLen
         index) := by
  dsimp
  let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
    { ra := B + 48, s0 := listBase, s1 := outputPtr, s2 := s2, s3 := s3,
      s4 := s4, s5 := s5 }
  have hwhole := rlpFieldToU64_spec_within spOuter newSp listBase listLenW
    indexW outputPtr oldOut oldOffset oldLen old14 outer s2 s3 s4 s5 bytes
    listLen index hnewSp hlistLenW hindexW hindex hsalign hslack hover hvalid hret
  refine cpsTripleWithin_weaken
    (P' := ((.x1 ↦ᵣ outer.ra) **
      flatPre spOuter newSp listBase listLenW indexW outputPtr oldOut oldOffset
        oldLen old14 outer s2 s3 s4 s5 bytes))
    (Q' := ((.x1 ↦ᵣ outer.ra) **
      flatPost spOuter newSp listBase oldOffset oldLen outer saved bytes listLen
        index))
    (fun h hp => ?_) (fun h hq => ?_) hwhole
  · unfold flatPre at hp
    rw [regsAt_frame]
    xperm_hyp hp
  · unfold allReturned at hq
    rcases hq with hs | hf
    ·
      unfold successReturned at hs
      rw [regsAt_frame] at hs
      obtain ⟨offset, len, v12, x5, scalarStatus, wrapperStatus, outputValue,
        hs⟩ := hs
      have hflat : ((.x1 ↦ᵣ outer.ra) **
          flatSuccessReturned spOuter newSp listBase outer saved bytes listLen
            index) h := by
        have hfixed : ((.x1 ↦ᵣ outer.ra) **
            (((.x2 ↦ᵣ spOuter) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
              savedFrame newSp outer) **
             successPayload newSp listBase offset len v12 x5 scalarStatus
               wrapperStatus outputValue saved bytes listLen index)) h := by
          xperm_hyp hs
        exact sepConj_mono_right
          (fun _ hp => ⟨offset, len, v12, x5, scalarStatus, wrapperStatus,
            outputValue, hp⟩) h hfixed
      unfold flatPost
      exact sepConj_mono_right (fun _ hp => Or.inl hp) h hflat
    ·
      unfold failureReturned at hf
      rw [regsAt_frame] at hf
      obtain ⟨v11, v12, hf⟩ := hf
      have hflat : ((.x1 ↦ᵣ outer.ra) **
          flatFailureReturned spOuter newSp listBase oldOffset oldLen outer saved
            bytes listLen index) h := by
        have hfixed : ((.x1 ↦ᵣ outer.ra) **
            (((.x2 ↦ᵣ spOuter) ** (.x8 ↦ᵣ outer.s0) ** (.x9 ↦ᵣ outer.s1) **
              savedFrame newSp outer) **
             failurePayload newSp listBase oldOffset oldLen v11 v12 saved bytes
               listLen index)) h := by
          xperm_hyp hf
        exact sepConj_mono_right
          (fun _ hp => ⟨v11, v12, hp⟩) h hfixed
      unfold flatPost
      exact sepConj_mono_right (fun _ hp => Or.inr hp) h hflat


end EvmAsm.Codegen.RlpFieldToU64SAsm
