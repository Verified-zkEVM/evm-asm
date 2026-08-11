/-
  Call-compatible adapter for `hp_decode_nibbles_spec` (#11799).

  Factors saved `ra` out of `regsAt hdnFrame` so `callWithin_spec` can link
  the call without duplicating the register assertion. Consumes the existing
  whole-routine triple — does NOT rebuild the machine.
-/

import EvmAsm.Codegen.Programs.HpDecodeNibblesSAsmPaths
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.HpDecodeNibblesSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

/-- Canonical guest entry PC. -/
abbrev HpB : Word := BitVec.ofNat 64 GuestAddrs.hp_decode_nibbles

/-- Saved-register tail of `hdnFrame` without ra (x8/x9/x18/x19/x20). -/
def hdnSavedTailDesc : FrameDesc :=
  [(.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40)]

def hdnSavedTail (vals : Reg → Word) : Assertion :=
  regsAt hdnSavedTailDesc vals

theorem regsAt_hdnFrame_factor (vals : Reg → Word) :
    regsAt hdnFrame vals =
      ((.x1 ↦ᵣ vals .x1) ** hdnSavedTail vals) := by
  simp only [hdnFrame, hdnSavedTail, hdnSavedTailDesc, regsAt_cons]

/-- Call entry: sp + frame slots own + saved tail + caller pre (no outer x1). -/
def hdnCallEntry (sp0 : Word) (vals : Reg → Word)
    (src dst cnt isl : Word) (srcBytes bufOrig : List (BitVec 8))
    (v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl : Word) : Assertion :=
  (.x2 ↦ᵣ sp0) **
  frameSlotsOwn hdnFrame (sp0 + signExtend12 (-48 : BitVec 12)) **
  hdnSavedTail vals **
  hdnCallerPre src dst cnt isl srcBytes bufOrig
    v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl

/-- Call return: sp + frame slots saved + saved tail + caller post (no outer x1). -/
def hdnCallReturn (sp0 : Word) (vals : Reg → Word)
    (src dst cnt isl : Word) (srcBytes bufOrig : List (BitVec 8))
    (oldCnt oldIsl : Word) : Assertion :=
  (.x2 ↦ᵣ sp0) **
  frameSlotsSaved hdnFrame (sp0 + signExtend12 (-48 : BitVec 12)) vals **
  hdnSavedTail vals **
  hdnCallerPost src dst cnt isl srcBytes bufOrig oldCnt oldIsl

theorem hdnCallEntry_pcFree (sp0 : Word) (vals : Reg → Word)
    (src dst cnt isl : Word) (srcBytes bufOrig : List (BitVec 8))
    (v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl : Word) :
    (hdnCallEntry sp0 vals src dst cnt isl srcBytes bufOrig
      v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl).pcFree := by
  unfold hdnCallEntry
  refine pcFree_sepConj pcFree_regIs ?_
  refine pcFree_sepConj (pcFree_frameSlotsOwn _ _) ?_
  refine pcFree_sepConj (pcFree_regsAt _ _) ?pre
  exact pcFree_hdnCallerPre src dst cnt isl srcBytes bufOrig
    v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl

/-- Fuel of the existing whole-routine triple (body depends on src length). -/
def hdnFuel (srcLen : Nat) : Nat :=
  1 + hdnFrame.length + (30 + 11 * srcLen) + hdnFrame.length + 1 + 1

/-- One `hp_decode_nibbles` call framed by arbitrary caller-owned `F`.
    Requires `vals .x1 = callerPC + 4` (link) and the ABI hyps of the
    existing whole-routine triple. -/
theorem hp_decode_nibbles_call_spec_within
    {cr : CodeReq} (callerPC calleeEntry vOld sp0 : Word)
    (vals : Reg → Word)
    (src dst cnt isl : Word) (srcBytes bufOrig : List (BitVec 8))
    (v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl : Word)
    (offset : BitVec 21) (F : Assertion) (hF : F.pcFree)
    (hret : vals .x1 = callerPC + 4)
    (halignRet : (callerPC + 4 &&& ~~~(1 : Word)) = callerPC + 4)
    (hsalign : src.toNat % 8 = 0)
    (hsover : src.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ j, j < srcBytes.length →
      isValidByteAccess (src + BitVec.ofNat 64 j) = true)
    (hbuf : hdnC0 srcBytes + 2 * (srcBytes.length - 1) ≤ bufOrig.length)
    (hdalign : dst.toNat % 8 = 0)
    (hdover : dst.toNat + bufOrig.length < 2 ^ 64)
    (hdvalid : ∀ j, j < bufOrig.length →
      isValidByteAccess (dst + BitVec.ofNat 64 j) = true)
    (htarget : callerPC + signExtend21 offset = calleeEntry)
    (hentry : calleeEntry = HpB)
    (hmem : ∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i →
      cr a = some i)
    (hcalleeMem : ∀ a i, hdnCr HpB a = some i → cr a = some i) :
    cpsTripleWithin (1 + hdnFuel srcBytes.length) callerPC (callerPC + 4) cr
      (((.x1 ↦ᵣ vOld) ** hdnCallEntry sp0 vals src dst cnt isl srcBytes bufOrig
        v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl) ** F)
      (((.x1 ↦ᵣ (callerPC + 4)) ** hdnCallReturn sp0 vals src dst cnt isl
        srcBytes bufOrig oldCnt oldIsl) ** F) := by
  have hk0 := hp_decode_nibbles_spec HpB sp0 (callerPC + 4) vals
    src dst cnt isl srcBytes bufOrig
    v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl
    hret halignRet hsalign hsover hsvalid hbuf hdalign hdover hdvalid
  have hk := cpsTripleWithin_extend_code hcalleeMem hk0
  have hk' : cpsTripleWithin (hdnFuel srcBytes.length) HpB (callerPC + 4) cr
      ((.x1 ↦ᵣ (callerPC + 4)) ** hdnCallEntry sp0 vals src dst cnt isl
        srcBytes bufOrig v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl)
      ((.x1 ↦ᵣ (callerPC + 4)) ** hdnCallReturn sp0 vals src dst cnt isl
        srcBytes bufOrig oldCnt oldIsl) := by
    have hk1 : cpsTripleWithin (hdnFuel srcBytes.length) HpB (callerPC + 4) cr
        ((.x2 ↦ᵣ sp0) ** regsAt hdnFrame vals **
         frameSlotsOwn hdnFrame (sp0 + signExtend12 (-48 : BitVec 12)) **
         hdnCallerPre src dst cnt isl srcBytes bufOrig
           v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl)
        ((.x2 ↦ᵣ sp0) ** regsAt hdnFrame vals **
         frameSlotsSaved hdnFrame (sp0 + signExtend12 (-48 : BitVec 12)) vals **
         hdnCallerPost src dst cnt isl srcBytes bufOrig oldCnt oldIsl) := by
      simpa [hdnFuel] using hk
    refine cpsTripleWithin_weaken ?pre ?post hk1
    · intro h hp
      -- want flat; have (x1 ** hdnCallEntry)
      simp only [hdnCallEntry] at hp
      rw [regsAt_hdnFrame_factor, hret]
      xperm_hyp hp
    · intro h hq
      -- have flat; want (x1 ** hdnCallReturn)
      simp only [hdnCallReturn]
      rw [regsAt_hdnFrame_factor, hret] at hq
      xperm_hyp hq
  have hk'' : cpsTripleWithin (hdnFuel srcBytes.length) calleeEntry (callerPC + 4) cr
      ((.x1 ↦ᵣ (callerPC + 4)) ** hdnCallEntry sp0 vals src dst cnt isl
        srcBytes bufOrig v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl)
      ((.x1 ↦ᵣ (callerPC + 4)) ** hdnCallReturn sp0 vals src dst cnt isl
        srcBytes bufOrig oldCnt oldIsl) := by
    rw [hentry]; exact hk'
  have hcall := callWithin_spec callerPC calleeEntry vOld offset
    (hdnFuel srcBytes.length) htarget hmem
    (hdnCallEntry_pcFree sp0 vals src dst cnt isl srcBytes bufOrig
      v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl) hk''
  exact cpsTripleWithin_frameR F hF hcall

end EvmAsm.Codegen.HpDecodeNibblesSAsm
