/-
  Branch arm: la child BSS (#11799).

  After `branchNthSetup` (pc 60): a0=node a1=len a2=nibble.
  Idx 60-63: la x13,mw_child_offset; la x14,mw_child_length
-/

import EvmAsm.Codegen.Programs.MptWalkBranchNibble
import EvmAsm.Codegen.Programs.RlpListNthItemCallSAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.MptNodeKindSpec
open EvmAsm.Codegen.RlpListNthItemSAsm

/-! ## la bridges (Codegen.laHi ↔ Rv64.laHi) -/

private theorem la_child_off_hi :
    laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 240) =
      EvmAsm.Rv64.laHi (pc 60) MwChildOff := by
  unfold pc walkB MwChildOff EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_child_off_lo :
    laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 240) =
      EvmAsm.Rv64.laLo (pc 60) MwChildOff := by
  unfold pc walkB MwChildOff EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_child_off_range : laInRange (pc 60) MwChildOff := by
  unfold pc walkB MwChildOff laInRange; decide

private theorem la_child_len_hi :
    laHi GuestAddrs.mw_child_length (GuestAddrs.mpt_walk + 248) =
      EvmAsm.Rv64.laHi (pc 62) MwChildLen := by
  unfold pc walkB MwChildLen EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_child_len_lo :
    laLo GuestAddrs.mw_child_length (GuestAddrs.mpt_walk + 248) =
      EvmAsm.Rv64.laLo (pc 62) MwChildLen := by
  unfold pc walkB MwChildLen EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_child_len_range : laInRange (pc 62) MwChildLen := by
  unfold pc walkB MwChildLen laInRange; decide

private theorem nth_jal_target :
    pc 64 + signExtend21
      (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 256)) =
      NthB := by
  unfold pc walkB NthB jalOff signExtend21; decide

private theorem nth_ret_even :
    (pc 64 + 4) &&& ~~~(1 : Word) = pc 64 + 4 := by
  unfold pc walkB; decide

/-- Stable ambient through la (no x13/x14). -/
private def laRest (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) (nibbleW : Word) : Assertion :=
  (.x1 ↦ᵣ (kindCallPc + 4)) **
  (.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x12 ↦ᵣ nibbleW) **
  (.x0 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ (pathPtr + (0 : Word))) **
  (.x6 ↦ᵣ nibbleW) **
  regOwn .x7 **
  (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) **
  (.x20 ↦ᵣ valOutPtr) ** (.x21 ↦ᵣ valOutLen) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
    0 countW offW lenW **
  dispatchAmb newSp ws ks nodeBase nodeLenW **
  bytesRegion pathPtr pathBytes

private theorem laRest_pcFree (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) (nibbleW : Word) :
    (laRest newSp ws ks nodeBase nodeLenW bytes listLen
      oldCount oldOff oldLen countW offW lenW
      pathPtr pathLenW valOutPtr valOutLen pathBytes nibbleW).pcFree := by
  unfold laRest
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact kindPayload_pcFree _ _ _ _ _ _ _ _ _ _ _
    | exact dispatchAmb_pcFree _ _ _ _ _
    | exact bytesRegion_pcFree _ _ | apply pcFree_sepConj

/-- After both las. -/
def branchAfterLa (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) (nibbleW : Word) : Assertion :=
  (.x13 ↦ᵣ MwChildOff) ** (.x14 ↦ᵣ MwChildLen) **
  laRest newSp ws ks nodeBase nodeLenW bytes listLen
    oldCount oldOff oldLen countW offW lenW
    pathPtr pathLenW valOutPtr valOutLen pathBytes nibbleW

/-! la x13 then la x14 (pc60→pc64). -/
set_option maxRecDepth 8000 in
theorem branch_child_la
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) (nibbleW : Word) :
    cpsTripleWithin 4 (pc 60) (pc 64) fullCode
      (branchNthSetup newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen countW offW lenW
        pathPtr pathLenW valOutPtr valOutLen pathBytes nibbleW)
      (branchAfterLa newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen countW offW lenW
        pathPtr pathLenW valOutPtr valOutLen pathBytes nibbleW) := by
  let R := laRest newSp ws ks nodeBase nodeLenW bytes listLen
    oldCount oldOff oldLen countW offW lenW
    pathPtr pathLenW valOutPtr valOutLen pathBytes nibbleW
  have hR : R.pcFree :=
    laRest_pcFree newSp ws ks nodeBase nodeLenW bytes listLen
      oldCount oldOff oldLen countW offW lenW
      pathPtr pathLenW valOutPtr valOutLen pathBytes nibbleW
  -- la x13 under own x13 ** own x14 ** R
  have hla0core : ∀ v13,
      cpsTripleWithin 2 (pc 60) (pc 62) fullCode
        (((.x13 ↦ᵣ v13) ** regOwn .x14) ** R)
        (((.x13 ↦ᵣ MwChildOff) ** regOwn .x14) ** R) := by
    intro v13
    have hla := la_materialize_within (cr := fullCode) .x13 v13 (pc 60) MwChildOff
      (by decide) la_child_off_range
      (walkMem (pc 60) 60
        (.AUIPC .x13 (EvmAsm.Rv64.laHi (pc 60) MwChildOff))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_child_off_hi]; rfl))
      (by
        intro a i hs
        have hs' : CodeReq.singleton (pc 61)
            (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 60) MwChildOff)) a = some i := by
          simpa [pc_succ 60] using hs
        exact walkMem (pc 61) 61
          (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 60) MwChildOff))
          (by decide) (by unfold pc walkB; decide)
          (by rw [← la_child_off_lo]; rfl) a i hs')
    rw [show pc 60 + 8 = pc 62 from by unfold pc; bv_omega] at hla
    have hFr := cpsTripleWithin_frameR (regOwn .x14 ** R)
      (by exact pcFree_sepConj (by exact pcFree_regOwn) hR) hla
    refine cpsTripleWithin_weaken ?_ ?_ hFr
    · intro h hp; xperm_chunked hp
    · intro h hq; xperm_chunked hq
  have hla0 :
      cpsTripleWithin 2 (pc 60) (pc 62) fullCode
        ((regOwn .x14 ** R) ** regOwn .x13)
        (((.x13 ↦ᵣ MwChildOff) ** regOwn .x14) ** R) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x13) ?_
    intro v13
    refine cpsTripleWithin_weaken ?_ ?_ (hla0core v13)
    · intro h hp; xperm_chunked hp
    · intro h hq; exact hq
  -- la x14 under own x14 ** (x13 ** R)
  have hla1core : ∀ v14,
      cpsTripleWithin 2 (pc 62) (pc 64) fullCode
        (((.x14 ↦ᵣ v14) ** (.x13 ↦ᵣ MwChildOff)) ** R)
        (((.x14 ↦ᵣ MwChildLen) ** (.x13 ↦ᵣ MwChildOff)) ** R) := by
    intro v14
    have hla := la_materialize_within (cr := fullCode) .x14 v14 (pc 62) MwChildLen
      (by decide) la_child_len_range
      (walkMem (pc 62) 62
        (.AUIPC .x14 (EvmAsm.Rv64.laHi (pc 62) MwChildLen))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_child_len_hi]; rfl))
      (by
        intro a i hs
        have hs' : CodeReq.singleton (pc 63)
            (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 62) MwChildLen)) a = some i := by
          simpa [pc_succ 62] using hs
        exact walkMem (pc 63) 63
          (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 62) MwChildLen))
          (by decide) (by unfold pc walkB; decide)
          (by rw [← la_child_len_lo]; rfl) a i hs')
    rw [show pc 62 + 8 = pc 64 from by unfold pc; bv_omega] at hla
    have hFr := cpsTripleWithin_frameR ((.x13 ↦ᵣ MwChildOff) ** R)
      (by exact pcFree_sepConj (by exact pcFree_regIs) hR) hla
    refine cpsTripleWithin_weaken ?_ ?_ hFr
    · intro h hp; xperm_chunked hp
    · intro h hq; xperm_chunked hq
  have hla1 :
      cpsTripleWithin 2 (pc 62) (pc 64) fullCode
        (((.x13 ↦ᵣ MwChildOff) ** R) ** regOwn .x14)
        (((.x14 ↦ᵣ MwChildLen) ** (.x13 ↦ᵣ MwChildOff)) ** R) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x14) ?_
    intro v14
    refine cpsTripleWithin_weaken ?_ ?_ (hla1core v14)
    · intro h hp; xperm_chunked hp
    · intro h hq; exact hq
  -- Mid after hla0: (x13 ** own14) ** R  → need (x13 ** R) ** own14 for hla1
  have hla0' :
      cpsTripleWithin 2 (pc 60) (pc 62) fullCode
        ((regOwn .x14 ** R) ** regOwn .x13)
        (((.x13 ↦ᵣ MwChildOff) ** R) ** regOwn .x14) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hla0
    · intro h hq
      xperm_chunked hq
  have c01 := cpsTripleWithin_seq_same_cr hla0' hla1
  refine cpsTripleWithin_weaken ?_ ?_ c01
  · intro h hp
    -- branchNthSetup = own13 ** own14 ** R  (up to xperm)
    simp only [branchNthSetup, laRest, R, dispatchAmb, kindCallFrame,
      kindSavedRegTail, kindPayload] at hp ⊢
    xperm_chunked hp
  · intro h hq
    simp only [branchAfterLa, laRest, R] at hq ⊢
    xperm_chunked hq

/-! ## nth callWithin at pc 64

  Guest: `jal rlp_list_nth_item` with a0=node a1=len a2=nibble a3/a4=child BSS.
  Saves x8/x9/x18-21 into nth frame; restores on return.

  Residual: child content dispatch (empty / hash-32 / inlined) is the next
  hop arm — inlined sub-32 EXCLUDED BY GATE on #11799 domain.
-/

/-- Frame through nth: walk/kind frame slots + x22-24 + Mnk BSS + path + Result.
    Node bytes + child BSS + stackFree8 + saved path regs go into callEntryRest. -/
def branchNthCallFrame (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (pathBytes : List (BitVec 8))
    (pathPtr : Word) (countW offW lenW : Word)
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (bytes : List (BitVec 8)) : Assertion :=
  frameSlotsSaved kindFrame (newSp + signExtend12 (-32 : BitVec 12))
    (kindSavedVals ks) **
  walkSavedFrame newSp ws **
  (.x22 ↦ᵣ (0 : Word)) ** (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) **
  (MnkCount ↦ₘ countW) ** (MnkPathOff ↦ₘ offW) ** (MnkPathLen ↦ₘ lenW) **
  bytesRegion pathPtr pathBytes **
  ⌜MptNodeKindResult bytes nodeBase listLen oldCount oldOff oldLen 0⌝

theorem branchNthCallFrame_pcFree (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (pathBytes : List (BitVec 8))
    (pathPtr : Word) (countW offW lenW : Word)
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (bytes : List (BitVec 8)) :
    (branchNthCallFrame newSp ws ks nodeBase nodeLenW pathBytes pathPtr
      countW offW lenW listLen oldCount oldOff oldLen bytes).pcFree := by
  unfold branchNthCallFrame walkSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact pcFree_frameSlotsSaved _ _ _
    | exact bytesRegion_pcFree _ _ | exact pcFree_pure
    | apply pcFree_sepConj

/-! Nth call at walk pc64. Pre is already in callEntryRest shape
    (caller reshapes from branchAfterLa + child BSS cells). -/
set_option maxRecDepth 8000 in
theorem branch_nth_call_spec_within
    (newSp nodeBase nodeLenW nibbleW childOldOff childOldLen : Word)
    (nSaved : Saved) (bytes : List (BitVec 8)) (listLen nibble : Nat)
    (F : Assertion) (hF : F.pcFree)
    (hlistLenW : nodeLenW = BitVec.ofNat 64 listLen)
    (hnibbleW : nibbleW = BitVec.ofNat 64 nibble)
    (hnibble : nibble < 2 ^ 64)
    (hsalign : nodeBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : nodeBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (nodeBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin
      (1 + ((12 + ((85 + 93 * (nibble + 2)) + 6)) + 9))
      (pc 64) (pc 65) fullCode
      (((.x1 ↦ᵣ (kindCallPc + 4)) **
        callEntryRest newSp nodeBase nodeLenW nibbleW MwChildOff MwChildLen
          childOldOff childOldLen { nSaved with ra := pc 65 } bytes) ** F)
      (((.x1 ↦ᵣ (pc 65)) **
        callReturnResult newSp nodeBase nibbleW MwChildOff MwChildLen
          childOldOff childOldLen { nSaved with ra := pc 65 } bytes
          listLen nibble) ** F) := by
  have hmem : ∀ a i,
      CodeReq.singleton (pc 64)
          (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
            (GuestAddrs.mpt_walk + 256))) a = some i →
        fullCode a = some i :=
    walkMem (pc 64) 64
      (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
        (GuestAddrs.mpt_walk + 256)))
      (by decide) (by unfold pc walkB; decide) rfl
  have h := rlpListNthItem_call_spec_within (cr := fullCode)
    (callerPC := pc 64) (calleeEntry := NthB) (kindCallPc + 4)
    newSp nodeBase nodeLenW nibbleW MwChildOff MwChildLen
    childOldOff childOldLen
    (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 256))
    F hF nSaved bytes listLen nibble
    hlistLenW hnibbleW hnibble hsalign hslack hover hvalid nth_ret_even
    nth_jal_target rfl hmem nthCalleeMem
  have hpc : pc 64 + 4 = pc 65 := pc_succ 64
  simpa [hpc] using h

/-- Drop concrete x5/x6 after la into owns (entryRest needs owns).
    `**` is right-assoc: `x5 ** x6 ** R`. -/
private theorem drop_x5_x6_owns
    (v5 v6 : Word) (R : Assertion) :
    ∀ h, ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** R) h →
      (regOwn .x5 ** regOwn .x6 ** R) h := by
  intro h hp
  have hx5 := regIs_implies_regOwn (r := .x5) (v := v5)
  have hx6 := regIs_implies_regOwn (r := .x6) (v := v6)
  exact (sepConj_mono hx5 (sepConj_mono hx6 (fun _ hq => hq))) h hp

/-- Reshape `branchAfterLa ** child BSS` into nth call pre. -/
theorem branchAfterLa_to_nth_call_pre
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen childOldOff childOldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) (nibbleW : Word) :
    ∀ h,
      (branchAfterLa newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen countW offW lenW
        pathPtr pathLenW valOutPtr valOutLen pathBytes nibbleW **
       (MwChildOff ↦ₘ childOldOff) ** (MwChildLen ↦ₘ childOldLen)) h →
      (((.x1 ↦ᵣ (kindCallPc + 4)) **
        callEntryRest newSp nodeBase nodeLenW nibbleW MwChildOff MwChildLen
          childOldOff childOldLen
          { ra := pc 65, s0 := ks.s0, s1 := ks.s1, s2 := pathPtr,
            s3 := pathLenW, s4 := valOutPtr, s5 := valOutLen }
          bytes) **
       branchNthCallFrame newSp ws ks nodeBase nodeLenW pathBytes pathPtr
         countW offW lenW listLen oldCount oldOff oldLen bytes) h := by
  intro h hp
  -- Front x5/x6 (right-assoc), drop to owns, then xperm into call shape.
  have hp1 :
      ((.x5 ↦ᵣ (pathPtr + (0 : Word))) ** (.x6 ↦ᵣ nibbleW) **
       ((.x13 ↦ᵣ MwChildOff) ** (.x14 ↦ᵣ MwChildLen) **
        (.x1 ↦ᵣ (kindCallPc + 4)) **
        (.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x12 ↦ᵣ nibbleW) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x7 **
        (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) **
        (.x20 ↦ᵣ valOutPtr) ** (.x21 ↦ᵣ valOutLen) **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
          0 countW offW lenW **
        dispatchAmb newSp ws ks nodeBase nodeLenW **
        bytesRegion pathPtr pathBytes **
        (MwChildOff ↦ₘ childOldOff) ** (MwChildLen ↦ₘ childOldLen))) h := by
    simp only [branchAfterLa, laRest] at hp
    xperm_chunked hp
  have hp2 := drop_x5_x6_owns (pathPtr + (0 : Word)) nibbleW _ _ hp1
  -- Expand payload/dispatch and xperm into callEntryRest ** frame
  simp only [kindPayload, dispatchAmb, kindCallFrame, kindSavedRegTail,
    callEntryRest, savedRegTail, entryRest, branchNthCallFrame] at hp2 ⊢
  xperm_chunked hp2

end EvmAsm.Codegen.MptWalkSpec
