/-
  Call-compatible K20 contract.

  This is the reusable adapter for callers which invoke the strict
  `rlp_list_nth_item` routine from an ABI-frame body.  The callee's saved `ra`
  cell is exposed separately, so `callWithin_spec` can link the call without
  duplicating the register assertion.  The semantic `Result` relation from
  `RlpListNthItemSAsm` is kept intact.
-/

import EvmAsm.Codegen.Programs.RlpListNthItemSAsm
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.RlpListNthItemSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

#guard rlpListNthItem_prog.length = 194

def savedRegTail (saved : Saved) : Assertion :=
  ((.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
   (.x19 ↦ᵣ saved.s3) ** (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5))

theorem regsAt_factor (saved : Saved) :
    regsAt listNthFrame (savedVals saved) =
      ((.x1 ↦ᵣ saved.ra) ** savedRegTail saved) := by
  rw [regsAt_listNthFrame]
  rfl

def callEntryRest (sp0 listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) : Assertion :=
  ((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail saved **
   entryRest listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen bytes)

def callReturnResult (sp0 listBase _indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ status offset len v11 v12,
    ((((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** savedRegTail saved) **
      ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
       (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len))) **
      ⌜Result bytes listBase listLen index oldOffset oldLen status offset len⌝) h

theorem callEntryRest_pcFree (sp0 listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) :
    (callEntryRest sp0 listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen saved bytes).pcFree := by
  unfold callEntryRest savedRegTail
  pcf

/-! The K20 flat post, with its saved `ra` assertion factored out. -/
theorem flatReturnResult_to_callReturn
    (sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (h : PartialState) :
    flatReturnResult sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen saved
      bytes listLen index h →
      ((.x1 ↦ᵣ saved.ra) **
       callReturnResult sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen saved bytes listLen index) h := by
  intro hp
  unfold flatReturnResult at hp
  obtain ⟨status, offset, len, v11, v12, hcore⟩ := hp
  unfold callReturnResult
  have hintro5 : ∀ {A : Assertion}
      {B : Word → Word → Word → Word → Word → Assertion},
      (∃ status offset len v11 v12,
        (A ** B status offset len v11 v12) h) →
      (A ** (fun h' => ∃ status offset len v11 v12,
        B status offset len v11 v12 h')) h := by
    intro A B hx
    obtain ⟨status, offset, len, v11, v12, hx⟩ := hx
    rcases hx with ⟨h1, h2, hd, hu, hA, hB⟩
    exact ⟨h1, h2, hd, hu, hA, ⟨status, offset, len, v11, v12, hB⟩⟩
  refine hintro5 ⟨status, offset, len, v11, v12, ?_⟩
  rw [regsAt_factor] at hcore
  xperm_hyp hcore

/-! A single K20 call, framed by an arbitrary caller-owned assertion.  The
    caller supplies code-containment facts for the call instruction and the
    callee body; this keeps the theorem independent of any particular caller
    layout while exposing the exact status/offset/length `Result`. -/
theorem rlpListNthItem_call_spec_within
    {cr : CodeReq} (callerPC calleeEntry vOld sp0 listBase listLenW indexW offsetPtr lenPtr
      oldOffset oldLen : Word) (offset : BitVec 21) (F : Assertion) (hF : F.pcFree)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hret : (callerPC + 4) &&& ~~~(1 : Word) = callerPC + 4)
    (htarget : callerPC + signExtend21 offset = calleeEntry)
    (hentry : calleeEntry = B)
    (hmem : ∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i → cr a = some i)
    (hcalleeMem : ∀ a i, code a = some i → cr a = some i)
    :
    cpsTripleWithin (1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)) callerPC (callerPC + 4) cr
      (((.x1 ↦ᵣ vOld) ** callEntryRest sp0 listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen
        { saved with ra := callerPC + 4 } bytes) ** F)
      (((.x1 ↦ᵣ (callerPC + 4)) ** callReturnResult sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen
        { saved with ra := callerPC + 4 } bytes listLen index) ** F) := by
  let calleeSaved : Saved := { saved with ra := callerPC + 4 }
  have hk := rlpListNthItem_flat_spec_within sp0 listBase listLenW indexW offsetPtr lenPtr
    oldOffset oldLen calleeSaved bytes listLen index hlistLenW hindexW hindex hsalign hslack hover
    hvalid hret
  have hk' := cpsTripleWithin_extend_code hcalleeMem hk
  have hk'' : cpsTripleWithin
      ((12 + ((85 + 93 * (index + 2)) + 6)) + 9) calleeEntry (callerPC + 4) cr
      (((.x1 ↦ᵣ (callerPC + 4)) ** callEntryRest sp0 listBase listLenW indexW offsetPtr lenPtr
        oldOffset oldLen calleeSaved bytes))
      (((.x1 ↦ᵣ (callerPC + 4)) ** callReturnResult sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen
        calleeSaved bytes listLen index)) := by
    rw [hentry]
    have hpre' : cpsTripleWithin
        ((12 + ((85 + 93 * (index + 2)) + 6)) + 9) B calleeSaved.ra cr
        (((.x1 ↦ᵣ (callerPC + 4)) ** callEntryRest sp0 listBase listLenW indexW offsetPtr lenPtr
          oldOffset oldLen calleeSaved bytes))
        (flatReturnResult sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen calleeSaved bytes listLen index) :=
      cpsTripleWithin_weaken
        (P := ((.x2 ↦ᵣ sp0) ** regsAt listNthFrame (savedVals calleeSaved) **
          stackFree sp0 8 ** entryRest listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen bytes))
        (P' := ((.x1 ↦ᵣ (callerPC + 4)) ** callEntryRest sp0 listBase listLenW indexW offsetPtr lenPtr
          oldOffset oldLen calleeSaved bytes))
        (Q := flatReturnResult sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen calleeSaved bytes listLen index)
        (Q' := flatReturnResult sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen calleeSaved bytes listLen index)
        (fun _ hp => by
          unfold callEntryRest at hp
          rw [regsAt_factor]
          xperm_hyp hp) (fun _ hp => hp) hk'
    have hpost' : cpsTripleWithin
        ((12 + ((85 + 93 * (index + 2)) + 6)) + 9) B calleeSaved.ra cr
        (((.x1 ↦ᵣ (callerPC + 4)) ** callEntryRest sp0 listBase listLenW indexW offsetPtr lenPtr
          oldOffset oldLen calleeSaved bytes))
        (((.x1 ↦ᵣ (callerPC + 4)) ** callReturnResult sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen
          calleeSaved bytes listLen index)) :=
      cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hp => flatReturnResult_to_callReturn sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen
        calleeSaved bytes listLen index h hp)
      hpre'
    simpa [calleeSaved] using hpost'
  have hcall := callWithin_spec callerPC calleeEntry vOld offset
    ((12 + ((85 + 93 * (index + 2)) + 6)) + 9) htarget hmem
    (callEntryRest_pcFree sp0 listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen
      calleeSaved bytes) hk''
  exact cpsTripleWithin_frameR F hF hcall

#print axioms rlpListNthItem_call_spec_within

end EvmAsm.Codegen.RlpListNthItemSAsm
