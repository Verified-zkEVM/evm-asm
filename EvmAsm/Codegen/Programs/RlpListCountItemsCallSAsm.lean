/-
  Call-compatible adapter for strict `rlp_list_count_items`.

  Mirrors `RlpListNthItemCallSAsm`: factors saved `ra` so `callWithin_spec`
  can link a JAL without duplicating the register assertion. Used by
  `mpt_node_kind` (#11799 dep).
-/

import EvmAsm.Codegen.Programs.RlpListCountItemsFlatSAsm
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.RlpListCountItemsSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

def savedRegTail (saved : Saved) : Assertion :=
  ((.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) ** (.x18 ↦ᵣ saved.s2) **
   (.x19 ↦ᵣ saved.s3))

theorem regsAt_factor (saved : Saved) :
    regsAt countFrame (savedVals saved) =
      ((.x1 ↦ᵣ saved.ra) ** savedRegTail saved) := by
  rw [regsAt_countFrame]
  rfl

def callEntryRest (sp0 listBase listLenW outPtr oldCount : Word)
    (saved : Saved) (bytes : List (BitVec 8)) : Assertion :=
  ((.x2 ↦ᵣ sp0) ** stackFree sp0 6 ** savedRegTail saved **
   entryRest listBase listLenW outPtr oldCount bytes)

def callReturnResult (sp0 listBase outPtr : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ status result v11 v12 : Word,
    ((((.x2 ↦ᵣ sp0) ** stackFree sp0 6 ** savedRegTail saved) **
      ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
       regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** (outPtr ↦ₘ result))) **
      ⌜Result bytes listBase listLen status result⌝) h

theorem callEntryRest_pcFree (sp0 listBase listLenW outPtr oldCount : Word)
    (saved : Saved) (bytes : List (BitVec 8)) :
    (callEntryRest sp0 listBase listLenW outPtr oldCount saved bytes).pcFree := by
  unfold callEntryRest savedRegTail entryRest
  pcf

theorem flatReturnResult_to_callReturn
    (sp0 listBase outPtr : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) (h : PartialState) :
    flatResult sp0 listBase outPtr saved bytes listLen h →
      ((.x1 ↦ᵣ saved.ra) **
       callReturnResult sp0 listBase outPtr saved bytes listLen) h := by
  intro hp
  unfold flatResult at hp
  obtain ⟨status, result, v11, v12, hcore⟩ := hp
  unfold callReturnResult
  have hintro4 : ∀ {A : Assertion} {B : Word → Word → Word → Word → Assertion},
      (∃ status result v11 v12, (A ** B status result v11 v12) h) →
      (A ** (fun h' => ∃ status result v11 v12,
        B status result v11 v12 h')) h := by
    intro A B hx
    obtain ⟨status, result, v11, v12, hx⟩ := hx
    rcases hx with ⟨h1, h2, hd, hu, hA, hB⟩
    exact ⟨h1, h2, hd, hu, hA, ⟨status, result, v11, v12, hB⟩⟩
  refine hintro4 ⟨status, result, v11, v12, ?_⟩
  rw [regsAt_factor] at hcore
  xperm_hyp hcore

/-- Single K47 call framed by arbitrary caller-owned `F`. -/
theorem rlpListCountItems_call_spec_within
    {cr : CodeReq} (callerPC calleeEntry vOld sp0 listBase listLenW outPtr
      oldCount : Word) (offset : BitVec 21) (F : Assertion) (hF : F.pcFree)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen : Nat)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hret : (callerPC + 4) &&& ~~~(1 : Word) = callerPC + 4)
    (htarget : callerPC + signExtend21 offset = calleeEntry)
    (hentry : calleeEntry = B)
    (hmem : ∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i → cr a = some i)
    (hcalleeMem : ∀ a i, code a = some i → cr a = some i) :
    cpsTripleWithin (1 + (8 + (85 + (93 * (listLen + 1) + 3) + 7)))
      callerPC (callerPC + 4) cr
      (((.x1 ↦ᵣ vOld) ** callEntryRest sp0 listBase listLenW outPtr oldCount
        { saved with ra := callerPC + 4 } bytes) ** F)
      (((.x1 ↦ᵣ (callerPC + 4)) ** callReturnResult sp0 listBase outPtr
        { saved with ra := callerPC + 4 } bytes listLen) ** F) := by
  let calleeSaved : Saved := { saved with ra := callerPC + 4 }
  have hnewSp : sp0 + signExtend12 (-48 : BitVec 12) =
      sp0 + signExtend12 (-48 : BitVec 12) := rfl
  have hk := rlpListCountItems_flat_spec_within sp0
    (sp0 + signExtend12 (-48 : BitVec 12)) listBase listLenW outPtr oldCount
    calleeSaved bytes listLen hlistLenW hsalign hslack hover hvalid rfl hret
  have hk' := cpsTripleWithin_extend_code hcalleeMem hk
  have hk'' : cpsTripleWithin
      (8 + (85 + (93 * (listLen + 1) + 3) + 7)) calleeEntry (callerPC + 4) cr
      (((.x1 ↦ᵣ (callerPC + 4)) ** callEntryRest sp0 listBase listLenW outPtr
        oldCount calleeSaved bytes))
      (((.x1 ↦ᵣ (callerPC + 4)) ** callReturnResult sp0 listBase outPtr
        calleeSaved bytes listLen)) := by
    rw [hentry]
    have hpre' : cpsTripleWithin
        (8 + (85 + (93 * (listLen + 1) + 3) + 7)) B calleeSaved.ra cr
        (((.x1 ↦ᵣ (callerPC + 4)) ** callEntryRest sp0 listBase listLenW outPtr
          oldCount calleeSaved bytes))
        (flatResult sp0 listBase outPtr calleeSaved bytes listLen) :=
      cpsTripleWithin_weaken
        (P := ((.x2 ↦ᵣ sp0) ** regsAt countFrame (savedVals calleeSaved) **
          stackFree sp0 6 ** entryRest listBase listLenW outPtr oldCount bytes))
        (P' := ((.x1 ↦ᵣ (callerPC + 4)) ** callEntryRest sp0 listBase listLenW
          outPtr oldCount calleeSaved bytes))
        (Q := flatResult sp0 listBase outPtr calleeSaved bytes listLen)
        (Q' := flatResult sp0 listBase outPtr calleeSaved bytes listLen)
        (fun _ hp => by
          unfold callEntryRest at hp
          rw [regsAt_factor]
          xperm_hyp hp) (fun _ hp => hp) hk'
    have hpost' : cpsTripleWithin
        (8 + (85 + (93 * (listLen + 1) + 3) + 7)) B calleeSaved.ra cr
        (((.x1 ↦ᵣ (callerPC + 4)) ** callEntryRest sp0 listBase listLenW outPtr
          oldCount calleeSaved bytes))
        (((.x1 ↦ᵣ (callerPC + 4)) ** callReturnResult sp0 listBase outPtr
          calleeSaved bytes listLen)) :=
      cpsTripleWithin_weaken (fun _ hp => hp)
        (fun h hp => flatReturnResult_to_callReturn sp0 listBase outPtr
          calleeSaved bytes listLen h hp) hpre'
    simpa [calleeSaved] using hpost'
  have hcall := callWithin_spec callerPC calleeEntry vOld offset
    (8 + (85 + (93 * (listLen + 1) + 3) + 7)) htarget hmem
    (callEntryRest_pcFree sp0 listBase listLenW outPtr oldCount calleeSaved bytes)
    hk''
  exact cpsTripleWithin_frameR F hF hcall

end EvmAsm.Codegen.RlpListCountItemsSAsm
