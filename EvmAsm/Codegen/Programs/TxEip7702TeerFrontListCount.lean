/-
  Teer front packaging: AtListCount → AfterAuthLoopLi under nested stackFree spC 6.

  * TeerListCountAssumed discharged classical-3 via teerListCountOkToLoad
    (Call_ok+BNE+LD) under ListCountResultSpecialize (walk-fail uniqueness residual).
  * TeerListCountAuthLoopAssumed discharged classical-3 via OkToLoad +
    AuthLoopStartShort_ownTemps (nested free framed).
  * Empty-auth: Success count=0 → s7=0; LI s8=0 at AfterAuthLoopLi.

  Bridge residual (AuthContent applied post → Assumed prest):
  1. nested `stackFree spC 6` outside TeerAssumed 20 — use `stackFree26_split`
     when caller provides 26-dword entry budget
  2. `bytesRegion listBase listBytes` vs full `bytesRegion regionBase bs`
     (unaligned RLP contentOff; bytesRegion_append needs 8∣prefix)
  3. peel `memOwn AuthCountAddr` → `AuthCountAddr ↦ₘ oldCount`
  4. FrontToAuthLoopAssumed empty post still needs epi-shaped ExitPre weaken
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerListCount
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopStart
import EvmAsm.Codegen.Programs.TxEip7702TeerSpec
import EvmAsm.Codegen.Programs.TxEip7702TeerScratchZero
import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmBase
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.RlpListCountItemsSAsm

/-- Steps: list_count ok+load + AuthLoopStartShort. -/
def nListCountAuthLoopStart (listLen : Nat) : Nat :=
  nListCountOkToLoad listLen + nAuthLoopStartShort

/-- After list_count load + AuthLoopStart short: s7=countW, s8=0, cursors saved. -/
def teerListCountAuthLoopPost (spC listBase outPtr s0 s1 s2 s3 countW : Word)
    (bytes : List (BitVec 8)) (listOff : Nat) (listLenW : Word) :
    Assertion :=
  teerAuthLoopStartBodyPost listBase listLenW bytes listOff **
    ((.x2 ↦ᵣ spC) **
      ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3)) **
      stackFree spC 6 **
      (.x23 ↦ᵣ countW) ** (outPtr ↦ₘ countW))

/-- Named hyp: AtListCount → AfterAuthLoopLi under nested free + short WI guards.
    Prest: OkToLoad prest framed with s5/s6/v24 (callee-saved through list_count).
    Discharged classical-3 via OkToLoad + AuthLoopStartShort_ownTemps. -/
structure TeerListCountAuthLoopAssumed (cr : CodeReq) where
  run :
    ∀ (spC newSp listBase listLenW outPtr oldCount s0 s1 s2 s3 countW : Word)
      (bytes : List (BitVec 8)) (listLen count listOff : Nat)
      (old1 s7Old v24 : Word)
      (hoff : listOff < bytes.length),
      listLenW = BitVec.ofNat 64 listLen →
      listBase.toNat % 8 = 0 →
      listLen + 9 ≤ bytes.length →
      listBase.toNat + bytes.length < 2 ^ 64 →
      (∀ k, k < bytes.length →
        isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) →
      newSp = spC + signExtend12 (-48 : BitVec 12) →
      (LinkListCount &&& ~~~(1 : Word)) = LinkListCount →
      countW = BitVec.ofNat 64 count →
      count < 2 ^ 64 →
      Success bytes listBase listLen count →
      ListCountResultSpecialize bytes listBase listLen count countW →
      outPtr = AuthCountAddr →
      listLenW ≠ (0 : Word) →
      listBase.toNat + listOff < 2 ^ 64 →
      isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true →
      ¬ BitVec.ult ((bytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
      BitVec.ult ((bytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
      (listBase + BitVec.ofNat 64 listOff) +
          (((bytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
            signExtend12 (1 : BitVec 12)) =
        (listBase + BitVec.ofNat 64 listOff) + listLenW →
      cpsTripleWithin (nListCountAuthLoopStart listLen) AtListCount AfterAuthLoopLi cr
        ((.x1 ↦ᵣ old1) ** (.x23 ↦ᵣ s7Old) **
          (.x24 ↦ᵣ v24) **
          (.x21 ↦ᵣ listBase + BitVec.ofNat 64 listOff) **
          (.x22 ↦ᵣ listLenW) **
          teerListCountCalleeP spC listBase listLenW outPtr oldCount s0 s1 s2 s3
            bytes)
        (teerListCountAuthLoopPost spC listBase outPtr s0 s1 s2 s3 countW bytes
          listOff listLenW)

/-- Ambient frame around list_count+AuthLoopStart (regs/stack not in CalleeP). -/
def teerListCountAuthLoopAmbient
    (spVal spC balPtr chainIdW baiW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal cursorV endW s11 : Word) : Assertion :=
  (.x20 ↦ᵣ chainIdW) ** (.x25 ↦ᵣ endW) **
    (.x26 ↦ᵣ (0 : Word)) ** (.x27 ↦ᵣ s11) **
    (.x15 ↦ᵣ baiW) **
    frameSlotsSaved teerFrame spC (teerSavedVals s) **
    (BitVec.ofNat 64 GuestAddrs.teer_type ↦ₘ (4 : Word)) **
    (BitVec.ofNat 64 GuestAddrs.teer_inner_off ↦ₘ innerVal) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x16 **
    stackFree spVal 6 **
    bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
    -- scratch without auth_count (peeled to memIs in CalleeP)
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_rolled_back) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_count) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_regular_refund) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_wouldbe_state) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_wouldbe_regular) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr) **
    (.x24 ↦ᵣ cursorV)

local macro "pcf" : tactic => `(tactic|
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp
    | exact pcFree_pure
    | exact pcFree_frameSlotsSaved
    | exact pcFree_stackFree _ _
    | exact bytesRegion_pcFree _ _
    | exact frameSlotsSaved_pcFree _ _ _)

private theorem pcFree_teerListCountAuthLoopAmbient
    (spVal spC balPtr chainIdW baiW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal cursorV endW s11 : Word) :
    (teerListCountAuthLoopAmbient spVal spC balPtr chainIdW baiW s regionBase bs
      balBytes innerVal cursorV endW s11).pcFree := by
  unfold teerListCountAuthLoopAmbient
  pcf

set_option maxRecDepth 8000 in
/-- Frame Assumed under ambient: mid-segment AtListCount → AfterAuthLoopLi. -/
theorem teerListCountAuthLoop_framed
    (asm : TeerListCountAuthLoopAssumed teerLinkedCount)
    (spVal spC newSp listBase listLenW outPtr oldCount s0 s1 s2 s3 countW : Word)
    (bytes : List (BitVec 8)) (listLen count listOff : Nat)
    (old1 s7Old v24 : Word)
    (hoff : listOff < bytes.length)
    (balPtr chainIdW baiW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal cursorV endW s11 : Word)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnewSp : newSp = spC + signExtend12 (-48 : BitVec 12))
    (hret : (LinkListCount &&& ~~~(1 : Word)) = LinkListCount)
    (hcountW : countW = BitVec.ofNat 64 count)
    (hcount : count < 2 ^ 64)
    (hsuccess : Success bytes listBase listLen count)
    (hspe : ListCountResultSpecialize bytes listBase listLen count countW)
    (hout : outPtr = AuthCountAddr)
    (hlen : listLenW ≠ (0 : Word))
    (hoverOff : listBase.toNat + listOff < 2 ^ 64)
    (hvalidOff : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (h_ge : ¬ BitVec.ult ((bytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (listBase + BitVec.ofNat 64 listOff) +
        (((bytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (listBase + BitVec.ofNat 64 listOff) + listLenW) :
    cpsTripleWithin (nListCountAuthLoopStart listLen) AtListCount AfterAuthLoopLi
      teerLinkedCount
      (((.x1 ↦ᵣ old1) ** (.x23 ↦ᵣ s7Old) **
          (.x24 ↦ᵣ v24) **
          (.x21 ↦ᵣ listBase + BitVec.ofNat 64 listOff) **
          (.x22 ↦ᵣ listLenW) **
          teerListCountCalleeP spC listBase listLenW outPtr oldCount s0 s1 s2 s3
            bytes) **
        teerListCountAuthLoopAmbient spVal spC balPtr chainIdW
          baiW s regionBase bs balBytes innerVal cursorV endW s11)
      ((teerListCountAuthLoopPost spC listBase outPtr s0 s1 s2 s3 countW bytes
          listOff listLenW) **
        teerListCountAuthLoopAmbient spVal spC balPtr chainIdW
          baiW s regionBase bs balBytes innerVal cursorV endW s11) := by
  have hcore := asm.run spC newSp listBase listLenW outPtr oldCount s0 s1 s2 s3
    countW bytes listLen count listOff old1 s7Old v24 hoff
    hlistLenW hsalign hslack hover hvalid hnewSp hret hcountW hcount hsuccess hspe
    hout hlen hoverOff hvalidOff h_ge h_hi h_exact
  have hpcf := pcFree_teerListCountAuthLoopAmbient spVal spC balPtr
    chainIdW baiW s regionBase bs balBytes innerVal cursorV endW s11
  exact cpsTripleWithin_frameR
    (teerListCountAuthLoopAmbient spVal spC balPtr chainIdW
      baiW s regionBase bs balBytes innerVal cursorV endW s11)
    hpcf hcore

/-- Empty-auth specialization: count=0, listOff=0 (content setup). -/
theorem teerListCountAuthLoop_framed_empty
    (asm : TeerListCountAuthLoopAssumed teerLinkedCount)
    (spVal spC newSp listBase listLenW outPtr oldCount s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (old1 s7Old v24 : Word)
    (hoff : (0 : Nat) < bytes.length)
    (balPtr chainIdW baiW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal cursorV endW s11 : Word)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnewSp : newSp = spC + signExtend12 (-48 : BitVec 12))
    (hret : (LinkListCount &&& ~~~(1 : Word)) = LinkListCount)
    (hsuccess : Success bytes listBase listLen 0)
    (hspe : ListCountResultSpecialize bytes listBase listLen 0 (0 : Word))
    (hout : outPtr = AuthCountAddr)
    (hlen : listLenW ≠ (0 : Word))
    (hoverOff : listBase.toNat + 0 < 2 ^ 64)
    (hvalidOff : isValidByteAccess (listBase + BitVec.ofNat 64 0) = true)
    (h_ge : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (listBase + BitVec.ofNat 64 0) +
        (((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (listBase + BitVec.ofNat 64 0) + listLenW) :
    cpsTripleWithin (nListCountAuthLoopStart listLen) AtListCount AfterAuthLoopLi
      teerLinkedCount
      (((.x1 ↦ᵣ old1) ** (.x23 ↦ᵣ s7Old) **
          (.x24 ↦ᵣ v24) **
          (.x21 ↦ᵣ listBase) **
          (.x22 ↦ᵣ listLenW) **
          teerListCountCalleeP spC listBase listLenW outPtr oldCount s0 s1 s2 s3
            bytes) **
        teerListCountAuthLoopAmbient spVal spC balPtr chainIdW
          baiW s regionBase bs balBytes innerVal cursorV endW s11)
      ((teerListCountAuthLoopPost spC listBase outPtr s0 s1 s2 s3 (0 : Word) bytes
          0 listLenW) **
        teerListCountAuthLoopAmbient spVal spC balPtr chainIdW
          baiW s regionBase bs balBytes innerVal cursorV endW s11) := by
  have hbase :
      listBase + BitVec.ofNat 64 0 = listBase := by
    apply BitVec.eq_of_toNat_eq
    simp
  simpa [hbase] using
    teerListCountAuthLoop_framed asm spVal spC newSp listBase listLenW outPtr
      oldCount s0 s1 s2 s3 (0 : Word) bytes listLen 0 0 old1 s7Old v24 hoff
      balPtr chainIdW baiW s regionBase bs balBytes
      innerVal cursorV endW s11 hlistLenW hsalign hslack hover hvalid hnewSp hret
      (rfl : (0 : Word) = BitVec.ofNat 64 0) (by omega : (0 : Nat) < 2 ^ 64)
      hsuccess hspe hout hlen hoverOff hvalidOff h_ge h_hi h_exact

#print axioms teerListCountAuthLoop_framed
#print axioms teerListCountAuthLoop_framed_empty

set_option maxRecDepth 8000 in
/-- Discharge AuthLoop Assumed: OkToLoad framed + AuthLoopStart ownTemps framed. -/
def teerListCountAuthLoopAssumed_teerLinked :
    TeerListCountAuthLoopAssumed teerLinkedCount where
  run := fun spC newSp listBase listLenW outPtr oldCount s0 s1 s2 s3 countW
      bytes listLen count listOff old1 s7Old v24 hoff
      hlistLenW hsalign hslack hover hvalid hnewSp hret hcountW hcount
      hsuccess hspe hout hlen hoverOff hvalidOff h_ge h_hi h_exact => by
    -- OkToLoad framed with s5/s6/v24
    have hok := teerListCountOkToLoad spC newSp listBase listLenW outPtr oldCount
      s0 s1 s2 s3 countW bytes listLen count old1 s7Old hlistLenW hsalign hslack
      hover hvalid hnewSp hret hcountW hcount hsuccess hspe hout
    have hokF := cpsTripleWithin_frameR
      ((.x21 ↦ᵣ listBase + BitVec.ofNat 64 listOff) **
        (.x22 ↦ᵣ listLenW) ** (.x24 ↦ᵣ v24)) (by pcf) hok
    -- AuthLoopStart ownTemps: after load, x10=0, x5=AuthCountAddr
    have hst := teerAuthLoopStartShort_ownTemps listBase listLenW AuthCountAddr
      (0 : Word) bytes listOff LinkListCount
      (listBase + BitVec.ofNat 64 listOff) listLenW v24
      rfl rfl hsalign hoff hoverOff hvalidOff hlen h_ge h_hi h_exact
    -- Frame Start with stack/s-regs/s7/out from LoadPost
    have hstF := cpsTripleWithin_frameR
      ((.x2 ↦ᵣ spC) **
        ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3)) **
        stackFree spC 6 **
        (.x23 ↦ᵣ countW) ** (outPtr ↦ₘ countW)) (by
          subst hout; pcf) hst
    -- Bridge LoadPost**cursors → Start prest ** stack frame
    have hokW : cpsTripleWithin (nListCountOkToLoad listLen) AtListCount
        AfterAuthCountLoad teerLinkedCount
        ((.x1 ↦ᵣ old1) ** (.x23 ↦ᵣ s7Old) **
          (.x24 ↦ᵣ v24) **
          (.x21 ↦ᵣ listBase + BitVec.ofNat 64 listOff) **
          (.x22 ↦ᵣ listLenW) **
          teerListCountCalleeP spC listBase listLenW outPtr oldCount s0 s1 s2 s3
            bytes)
        (teerAuthLoopStartBodyCore listBase listLenW bytes listOff LinkListCount
            (0 : Word) AuthCountAddr
            (listBase + BitVec.ofNat 64 listOff) listLenW v24 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x2 ↦ᵣ spC) **
            ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3)) **
            stackFree spC 6 **
            (.x23 ↦ᵣ countW) ** (outPtr ↦ₘ countW))) := by
      refine cpsTripleWithin_weaken (fun _ hp => by
          -- prest: (x1**x23**CalleeP)**cursors → x1**x23**x24**x21**x22**CalleeP
          xperm_hyp hp) (fun s hq => ?_) hokF
      -- LoadPost ** cursors → BodyCore ** regOwns ** stack
      unfold teerListCountLoadPost at hq
      unfold teerAuthLoopStartBodyCore
      subst hout
      xperm_hyp hq
    have hstW : cpsTripleWithin nAuthLoopStartShort AfterAuthCountLoad
        AfterAuthLoopLi teerLinkedCount
        (teerAuthLoopStartBodyCore listBase listLenW bytes listOff LinkListCount
            (0 : Word) AuthCountAddr
            (listBase + BitVec.ofNat 64 listOff) listLenW v24 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x2 ↦ᵣ spC) **
            ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3)) **
            stackFree spC 6 **
            (.x23 ↦ᵣ countW) ** (outPtr ↦ₘ countW)))
        (teerListCountAuthLoopPost spC listBase outPtr s0 s1 s2 s3 countW bytes
          listOff listLenW) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun s hq => ?_)
        hstF
      -- AuthLoopPost := BodyPost ** stack = frameR post
      unfold teerListCountAuthLoopPost
      exact hq
    have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hokW hstW
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      hseq

#print axioms teerListCountAuthLoopAssumed_teerLinked


end EvmAsm.Codegen.TxEip7702TeerSpec
