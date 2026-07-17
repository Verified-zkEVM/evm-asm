/-
  One-iter glue (through bal=0 EndSpan→LoopInv) for block_verdict_tx_state_gas_array (a4gbr).
  Split for Codegen/Programs 1500-line file-size guard.
-/

import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayLoopBalNez
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayEpilogue

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel
open EvmAsm.Codegen.SgLoadU32leSAsm (leU32)
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec (wordArray)

/-! ## StartBgv post → SpanChecks pre (unpack bgvScratch, reassemble payload) -/

private theorem startBgv_post_to_spanPre
    (spC txBase outBase balBase chainIdW nW iW startW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) :
    ∀ h,
      (((.x1 ↦ᵣ LinkLoopBgv1) **
          (.x10 ↦ᵣ startW) **
          regOwns bgvScratch **
          bytesRegion txBase txBlob **
          loopBgvFrameAfterMv spC txBase outBase balBase chainIdW nW iW csaved
            txBlob outVals balBytes balEnabled startW) h) →
      (((.x1 ↦ᵣ LinkLoopBgv1) **
          (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
          (.x22 ↦ᵣ startW) ** regOwn .x23 **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
          (.x10 ↦ᵣ startW) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          savedFrame spC csaved **
          stackFree spC nCalleeStackDwords **
          payload txBase outBase balBase txBlob outVals balBytes balEnabled **
          (.x0 ↦ᵣ (0 : Word))) h) := by
  intro h hp
  unfold loopBgvFrameAfterMv at hp
  simp only [bgvScratch, regOwns_cons, regOwns_nil, sepConj_emp_right'] at hp
  unfold payload
  xperm_hyp hp

/-! ## LoopInv peels for StartBgv pre -/

private def loopInvNoX10 (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (i : Nat) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) **
  regOwn .x1 ** regOwn .x22 ** regOwn .x23 ** regOwn .x27 **
  savedFrame spC csaved **
  stackFree spC nCalleeStackDwords **
  payload txBase outBase balBase txBlob outVals balBytes balEnabled **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

private theorem loopInv_to_noX10
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (i : Nat) :
    ∀ h, (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals
        balBytes balEnabled i) h →
      ((loopInvNoX10 spC txBase outBase balBase chainIdW nW csaved txBlob outVals
          balBytes balEnabled i ** regOwn .x10) h) := by
  intro h hp
  unfold LoopInv scratchRegs at hp
  unfold loopInvNoX10
  xperm_hyp hp

private def loopInvNoX10X5 (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (i : Nat)
    (old10 : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) **
  regOwn .x1 ** regOwn .x22 ** regOwn .x23 ** regOwn .x27 **
  savedFrame spC csaved **
  stackFree spC nCalleeStackDwords **
  payload txBase outBase balBase txBlob outVals balBytes balEnabled **
  (.x10 ↦ᵣ old10) **
  regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

private theorem noX10_to_noX5
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (i : Nat)
    (old10 : Word) :
    ∀ h, ((loopInvNoX10 spC txBase outBase balBase chainIdW nW csaved txBlob
          outVals balBytes balEnabled i ** (.x10 ↦ᵣ old10)) h) →
      ((loopInvNoX10X5 spC txBase outBase balBase chainIdW nW csaved txBlob
          outVals balBytes balEnabled i old10 ** regOwn .x5) h) := by
  intro h hp
  unfold loopInvNoX10 at hp
  unfold loopInvNoX10X5
  xperm_hyp hp

private def loopInvNoX10X5X1 (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (i : Nat)
    (old10 old5 : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) **
  regOwn .x22 ** regOwn .x23 ** regOwn .x27 **
  savedFrame spC csaved **
  stackFree spC nCalleeStackDwords **
  payload txBase outBase balBase txBlob outVals balBytes balEnabled **
  (.x10 ↦ᵣ old10) ** (.x5 ↦ᵣ old5) **
  regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

private theorem noX5_to_noX1
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (i : Nat)
    (old10 old5 : Word) :
    ∀ h, ((loopInvNoX10X5 spC txBase outBase balBase chainIdW nW csaved txBlob
          outVals balBytes balEnabled i old10 ** (.x5 ↦ᵣ old5)) h) →
      ((loopInvNoX10X5X1 spC txBase outBase balBase chainIdW nW csaved txBlob
          outVals balBytes balEnabled i old10 old5 ** regOwn .x1) h) := by
  intro h hp
  unfold loopInvNoX10X5 at hp
  unfold loopInvNoX10X5X1
  xperm_hyp hp

private theorem noX1_to_startBgvPre
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (i : Nat)
    (old10 old5 old1 : Word) :
    ∀ h, ((loopInvNoX10X5X1 spC txBase outBase balBase chainIdW nW csaved txBlob
          outVals balBytes balEnabled i old10 old5 ** (.x1 ↦ᵣ old1)) h) →
      (((.x8 ↦ᵣ txBase) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
          (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ old10) **
          setupFrame spC txBase outBase balBase chainIdW nW csaved
            txBlob outVals balBytes balEnabled old1) h) := by
  intro h hp
  unfold loopInvNoX10X5X1 at hp
  unfold setupFrame
  xperm_hyp hp

set_option maxRecDepth 8000 in
/-- From `LoopInv` at body entry: peel owned x1/x5/x10 and run `bvtIterStartBgv`. -/
theorem bvtIterStartBgv_fromInv
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (n i : Nat)
    (hbgv : BgvOffsetAssumed fullCode)
    (hok : IterOk txBlob n i)
    (htxAlign : txBase.toNat % 8 = 0) :
    let iW := BitVec.ofNat 64 i
    let startW := leU32 txBlob (4 * i)
    cpsTripleWithin (2 + (1 + nBgvSteps) + 1) LoopBody AfterStartBgv fullCode
      (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals
        balBytes balEnabled i)
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x10 ↦ᵣ startW) **
        regOwns bgvScratch **
        bytesRegion txBase txBlob **
        loopBgvFrameAfterMv spC txBase outBase balBase chainIdW nW iW csaved
          txBlob outVals balBytes balEnabled startW) := by
  intro iW startW
  refine cpsTripleWithin_weaken
    (fun h hp => loopInv_to_noX10 spC txBase outBase balBase chainIdW nW
      csaved txBlob outVals balBytes balEnabled i h hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10) (fun old10 => ?_)
  refine cpsTripleWithin_weaken
    (fun h hp => noX10_to_noX5 spC txBase outBase balBase chainIdW nW
      csaved txBlob outVals balBytes balEnabled i old10 h hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5) (fun old5 => ?_)
  refine cpsTripleWithin_weaken
    (fun h hp => noX5_to_noX1 spC txBase outBase balBase chainIdW nW
      csaved txBlob outVals balBytes balEnabled i old10 old5 h hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x1) (fun old1 => ?_)
  have h0 := bvtIterStartBgv spC txBase outBase balBase chainIdW nW csaved
    txBlob outVals balBytes balEnabled n i old1 old5 old10 hbgv hok htxAlign
  exact cpsTripleWithin_weaken
    (fun h hp => noX1_to_startBgvPre spC txBase outBase balBase chainIdW nW
      csaved txBlob outVals balBytes balEnabled i old10 old5 old1 h hp)
    (fun _ hq => by xperm_hyp hq) h0

set_option maxRecDepth 8000 in
/-- Body entry through span checks: `LoopBody` → `AfterSpanChecks`. -/
theorem bvtIterThroughSpan
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (n i : Nat)
    (hbgv : BgvOffsetAssumed fullCode)
    (hok : IterOk txBlob n i)
    (htxAlign : txBase.toNat % 8 = 0)
    (hnW : nW = BitVec.ofNat 64 n) :
    let iW := BitVec.ofNat 64 i
    let startW := leU32 txBlob (4 * i)
    let tableW := BitVec.ofNat 64 (4 * n)
    cpsTripleWithin
      ((2 + (1 + nBgvSteps) + 1) + 3) LoopBody AfterSpanChecks fullCode
      (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals
        balBytes balEnabled i)
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x10 ↦ᵣ startW) **
        (.x5 ↦ᵣ tableW) ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word))) := by
  intro iW startW tableW
  have hstart := bvtIterStartBgv_fromInv spC txBase outBase balBase chainIdW nW
    csaved txBlob outVals balBytes balEnabled n i hbgv hok htxAlign
  have hspan0 := bvtIterSpanChecks spC txBase outBase balBase chainIdW nW csaved
    txBlob outVals balBytes balEnabled n i startW hok hnW rfl
  have hspan := cpsTripleWithin_extend_code bvt_mono hspan0
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hp => startBgv_post_to_spanPre spC txBase outBase balBase chainIdW nW
      iW startW csaved txBlob outVals balBytes balEnabled h hp)
    hstart hspan

/-! ## End-offset path (last vs next) from AfterSpanChecks -/

/-- Common post after end path: `x5` is owned (last weakens concrete; next from bgvScratch).
    `x10` holds a path-dependent value (last: startW; next: endW). -/
private def afterEndRegs (spC txBase outBase balBase chainIdW nW iW
    startW endW lenW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool)
    (link x10v : Word) : Assertion :=
  (.x1 ↦ᵣ link) **
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
  (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
  regOwn .x5 ** (.x10 ↦ᵣ x10v) **
  regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  savedFrame spC csaved **
  stackFree spC nCalleeStackDwords **
  payload txBase outBase balBase txBlob outVals balBytes balEnabled **
  (.x0 ↦ᵣ (0 : Word))

/-- EndLast post → afterEndRegs (weaken concrete x5 to regOwn). -/
private theorem endLast_post_to_afterEnd
    (spC txBase outBase balBase chainIdW nW iW startW lenW ip1W : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) :
    ∀ h,
      (((.x1 ↦ᵣ LinkLoopBgv1) **
          (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
          (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ lenW) **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
          (.x10 ↦ᵣ startW) **
          (.x5 ↦ᵣ ip1W) ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          savedFrame spC csaved **
          stackFree spC nCalleeStackDwords **
          payload txBase outBase balBase txBlob outVals balBytes balEnabled **
          (.x0 ↦ᵣ (0 : Word))) h) →
      (afterEndRegs spC txBase outBase balBase chainIdW nW iW startW lenW lenW
        csaved txBlob outVals balBytes balEnabled LinkLoopBgv1 startW) h := by
  intro h hp
  -- Pull x5 leftmost, weaken regIs→regOwn, reassemble into afterEndRegs.
  have hp1 :
      (((.x5 ↦ᵣ ip1W) **
          ((.x1 ↦ᵣ LinkLoopBgv1) **
            (.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ lenW) **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            (.x10 ↦ᵣ startW) **
            regOwn .x6 ** regOwn .x7 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
            regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            savedFrame spC csaved **
            stackFree spC nCalleeStackDwords **
            payload txBase outBase balBase txBlob outVals balBytes balEnabled **
            (.x0 ↦ᵣ (0 : Word)))) h) := by
    xperm_hyp hp
  have hp2 :=
    sepConj_mono (regIs_to_regOwn .x5 ip1W) (fun _ hh => hh) h hp1
  unfold afterEndRegs
  xperm_hyp hp2

/-- EndNext post (peeled) → afterEndRegs (unpack bgvScratch, reassemble payload).
    `x5` stays owned inside bgvScratch. -/
private theorem endNext_post_to_afterEnd
    (spC txBase outBase balBase chainIdW nW iW startW endW lenW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) :
    ∀ h,
      (((.x1 ↦ᵣ LinkLoopBgv2) **
          (.x10 ↦ᵣ endW) ** regOwns bgvScratch **
          bytesRegion txBase txBlob **
          (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
          (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
          savedFrame spC csaved **
          stackFree spC nCalleeStackDwords **
          wordArray outBase outVals **
          (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
          (.x0 ↦ᵣ (0 : Word))) h) →
      (afterEndRegs spC txBase outBase balBase chainIdW nW iW startW endW lenW
        csaved txBlob outVals balBytes balEnabled LinkLoopBgv2 endW) h := by
  intro h hp
  unfold afterEndRegs payload
  simp only [bgvScratch, regOwns_cons, regOwns_nil, sepConj_emp_right'] at hp
  xperm_hyp hp

/-- Span post with regOwn x6 rightmost (for EndNext peel). -/
private def spanPostNoX6 (spC txBase outBase balBase chainIdW nW iW
    startW tableW lenW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) : Assertion :=
  (.x1 ↦ᵣ LinkLoopBgv1) **
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
  (.x22 ↦ᵣ startW) ** regOwn .x23 **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
  (.x10 ↦ᵣ startW) **
  (.x5 ↦ᵣ tableW) ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  savedFrame spC csaved **
  stackFree spC nCalleeStackDwords **
  payload txBase outBase balBase txBlob outVals balBytes balEnabled **
  (.x0 ↦ᵣ (0 : Word))

private theorem span_to_noX6
    (spC txBase outBase balBase chainIdW nW iW startW tableW lenW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) :
    ∀ h,
      (((.x1 ↦ᵣ LinkLoopBgv1) **
          (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
          (.x22 ↦ᵣ startW) ** regOwn .x23 **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
          (.x10 ↦ᵣ startW) **
          (.x5 ↦ᵣ tableW) ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          savedFrame spC csaved **
          stackFree spC nCalleeStackDwords **
          payload txBase outBase balBase txBlob outVals balBytes balEnabled **
          (.x0 ↦ᵣ (0 : Word))) h) →
      ((spanPostNoX6 spC txBase outBase balBase chainIdW nW iW startW tableW
          lenW csaved txBlob outVals balBytes balEnabled ** regOwn .x6) h) := by
  intro h hp
  unfold spanPostNoX6
  xperm_hyp hp

private theorem noX6_to_endNextPre
    (spC txBase outBase balBase chainIdW nW iW startW tableW lenW old6 : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) :
    ∀ h,
      ((spanPostNoX6 spC txBase outBase balBase chainIdW nW iW startW tableW
          lenW csaved txBlob outVals balBytes balEnabled ** (.x6 ↦ᵣ old6)) h) →
      (((.x1 ↦ᵣ LinkLoopBgv1) **
          (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
          (.x22 ↦ᵣ startW) ** regOwn .x23 **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
          (.x10 ↦ᵣ startW) **
          (.x5 ↦ᵣ tableW) ** (.x6 ↦ᵣ old6) ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          savedFrame spC csaved **
          stackFree spC nCalleeStackDwords **
          payload txBase outBase balBase txBlob outVals balBytes balEnabled **
          (.x0 ↦ᵣ (0 : Word))) h) := by
  intro h hp
  unfold spanPostNoX6 at hp
  xperm_hyp hp

set_option maxRecDepth 8000 in
/-- Last-tx end path: AfterSpanChecks → AfterEndOffset with end=body_len. -/
theorem bvtIterEndLast_fromSpan
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (n i : Nat)
    (startW tableW : Word)
    (hok : IterOk txBlob n i)
    (hLast : i + 1 = n)
    (hnW : nW = BitVec.ofNat 64 n)
    (hStart : startW = leU32 txBlob (4 * i))
    (htab : tableW = BitVec.ofNat 64 (4 * n)) :
    let iW := BitVec.ofNat 64 i
    let lenW := BitVec.ofNat 64 txBlob.length
    cpsTripleWithin 3 AfterSpanChecks AfterEndOffset bvtCode
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x10 ↦ᵣ startW) **
        (.x5 ↦ᵣ tableW) ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word)))
      (afterEndRegs spC txBase outBase balBase chainIdW nW iW startW lenW lenW
        csaved txBlob outVals balBytes balEnabled LinkLoopBgv1 startW) := by
  intro iW lenW
  have h0 := bvtIterEndLast spC txBase outBase balBase chainIdW nW csaved
    txBlob outVals balBytes balEnabled n i startW tableW hok hLast hnW hStart htab
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => endLast_post_to_afterEnd spC txBase outBase balBase chainIdW nW
      iW startW lenW (BitVec.ofNat 64 (i + 1)) csaved txBlob outVals balBytes
      balEnabled h hq) h0

set_option maxRecDepth 8000 in
/-- Non-last end path under BgvOffsetAssumed: AfterSpanChecks → AfterEndOffset. -/
theorem bvtIterEndNext_fromSpan
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (n i : Nat)
    (startW tableW : Word)
    (hbgv : BgvOffsetAssumed fullCode)
    (hok : IterOk txBlob n i)
    (hNext : i + 1 ≠ n)
    (hnW : nW = BitVec.ofNat 64 n)
    (hStart : startW = leU32 txBlob (4 * i))
    (htab : tableW = BitVec.ofNat 64 (4 * n))
    (htxAlign : txBase.toNat % 8 = 0) :
    let iW := BitVec.ofNat 64 i
    let endW := leU32 txBlob (4 * (i + 1))
    let lenW := BitVec.ofNat 64 txBlob.length
    cpsTripleWithin (2 + 2 + (1 + nBgvSteps) + 2) AfterSpanChecks AfterEndOffset
      fullCode
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x10 ↦ᵣ startW) **
        (.x5 ↦ᵣ tableW) ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word)))
      (afterEndRegs spC txBase outBase balBase chainIdW nW iW startW endW lenW
        csaved txBlob outVals balBytes balEnabled LinkLoopBgv2 endW) := by
  intro iW endW lenW
  refine cpsTripleWithin_weaken
    (fun h hp => span_to_noX6 spC txBase outBase balBase chainIdW nW iW startW
      tableW lenW csaved txBlob outVals balBytes balEnabled h hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6) (fun old6 => ?_)
  have h0 := bvtIterEndNext spC txBase outBase balBase chainIdW nW csaved
    txBlob outVals balBytes balEnabled n i startW tableW old6 startW
    hbgv hok hNext hnW hStart htab htxAlign
  exact cpsTripleWithin_weaken
    (fun h hp => noX6_to_endNextPre spC txBase outBase balBase chainIdW nW iW
      startW tableW lenW old6 csaved txBlob outVals balBytes balEnabled h hp)
    (fun h hq => endNext_post_to_afterEnd spC txBase outBase balBase chainIdW nW
      iW startW endW lenW csaved txBlob outVals balBytes balEnabled h hq) h0

/-- Unified end path: cases on last vs next. Step bound is max of both. -/
def nEndPathSteps : Nat := 2 + 2 + (1 + nBgvSteps) + 2  -- covers next; last is 3 ≤ this

set_option maxRecDepth 8000 in
/-- AfterSpanChecks → AfterEndOffset under IterOk (both last/next). -/
theorem bvtIterThroughEnd
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (n i : Nat)
    (startW tableW : Word)
    (hbgv : BgvOffsetAssumed fullCode)
    (hok : IterOk txBlob n i)
    (hnW : nW = BitVec.ofNat 64 n)
    (hStart : startW = leU32 txBlob (4 * i))
    (htab : tableW = BitVec.ofNat 64 (4 * n))
    (htxAlign : txBase.toNat % 8 = 0) :
    let iW := BitVec.ofNat 64 i
    let endW := hok.endW
    let lenW := BitVec.ofNat 64 txBlob.length
    let link := if i + 1 = n then LinkLoopBgv1 else LinkLoopBgv2
    let x10v := if i + 1 = n then startW else endW
    cpsTripleWithin nEndPathSteps AfterSpanChecks AfterEndOffset fullCode
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x10 ↦ᵣ startW) **
        (.x5 ↦ᵣ tableW) ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word)))
      (afterEndRegs spC txBase outBase balBase chainIdW nW iW startW endW lenW
        csaved txBlob outVals balBytes balEnabled link x10v) := by
  intro iW endW lenW link x10v
  by_cases hLast : i + 1 = n
  · have h0 := bvtIterEndLast_fromSpan spC txBase outBase balBase chainIdW nW
      csaved txBlob outVals balBytes balEnabled n i startW tableW hok hLast hnW
      hStart htab
    have h0C := cpsTripleWithin_extend_code bvt_mono h0
    have hmono := cpsTripleWithin_mono_nSteps
      (nSteps := 3) (nSteps' := nEndPathSteps)
      (by simp only [nEndPathSteps, nBgvSteps]; omega) h0C
    -- Goal post uses `endW`/`link`/`x10v`; last path pins them to lenW/Link1/startW.
    have hend : endW = lenW := by
      change hok.endW = BitVec.ofNat 64 txBlob.length
      rw [hok.hEnd, if_pos hLast]
    have hlink : link = LinkLoopBgv1 := by
      change (if i + 1 = n then LinkLoopBgv1 else LinkLoopBgv2) = LinkLoopBgv1
      rw [if_pos hLast]
    have hx10 : x10v = startW := by
      change (if i + 1 = n then startW else endW) = startW
      rw [if_pos hLast]
    -- hmono already has concrete last-path post; rewrite goal only.
    simpa only [hend, hlink, hx10] using hmono
  · have h0 := bvtIterEndNext_fromSpan spC txBase outBase balBase chainIdW nW
      csaved txBlob outVals balBytes balEnabled n i startW tableW hbgv hok hLast
      hnW hStart htab htxAlign
    have hend : endW = leU32 txBlob (4 * (i + 1)) := by
      change hok.endW = leU32 txBlob (4 * (i + 1))
      rw [hok.hEnd, if_neg hLast]
    have hlink : link = LinkLoopBgv2 := by
      change (if i + 1 = n then LinkLoopBgv1 else LinkLoopBgv2) = LinkLoopBgv2
      rw [if_neg hLast]
    have hx10 : x10v = endW := by
      change (if i + 1 = n then startW else endW) = endW
      rw [if_neg hLast]
    -- h0 has endW := leU32 ...; goal has endW := hok.endW. Align via hend.
    simpa only [nEndPathSteps, hend, hlink, hx10] using h0

/-! ## EndSpanSetup from afterEndRegs + FromIntrinsic join -/

/-- `w = ofNat w.toNat` (Word identity). -/
theorem word_eq_ofNat_toNat (w : Word) :
    w = BitVec.ofNat 64 w.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt w.isLt).symm

/-- `a - b = ofNat (a.toNat - b.toNat)` when `b.toNat ≤ a.toNat`. -/
theorem word_sub_toNat (a b : Word) (hle : b.toNat ≤ a.toNat) :
    a - b = BitVec.ofNat 64 (a.toNat - b.toNat) := by
  have ha : a = BitVec.ofNat 64 a.toNat := word_eq_ofNat_toNat a
  have hb : b = BitVec.ofNat 64 b.toNat := word_eq_ofNat_toNat b
  rw [ha, hb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have _ha : a.toNat < 2 ^ 64 := a.isLt
  have _hb : b.toNat < 2 ^ 64 := b.isLt
  omega

/-- Core of afterEnd with x1 owned; trailing owns x5/x12/x11 for of_forall3. -/
private def afterEndCore (spC txBase outBase balBase chainIdW nW iW
    startW endW lenW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (x10v : Word) : Assertion :=
  regOwn .x1 **
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
  (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
  (.x10 ↦ᵣ x10v) **
  regOwn .x6 ** regOwn .x7 **
  regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  savedFrame spC csaved **
  stackFree spC nCalleeStackDwords **
  payload txBase outBase balBase txBlob outVals balBytes balEnabled **
  (.x0 ↦ᵣ (0 : Word))

/-- afterEnd with regOwn x1 and trailing owned x5/x12/x11 (right-assoc). -/
private def afterEndOwnRa (spC txBase outBase balBase chainIdW nW iW
    startW endW lenW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (x10v : Word) : Assertion :=
  afterEndCore spC txBase outBase balBase chainIdW nW iW startW endW lenW
    csaved txBlob outVals balBytes balEnabled x10v **
  regOwn .x5 ** regOwn .x12 ** regOwn .x11

private theorem afterEnd_to_ownRa
    (spC txBase outBase balBase chainIdW nW iW startW endW lenW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (link x10v : Word) :
    ∀ h, (afterEndRegs spC txBase outBase balBase chainIdW nW iW startW endW
        lenW csaved txBlob outVals balBytes balEnabled link x10v) h →
      (afterEndOwnRa spC txBase outBase balBase chainIdW nW iW startW endW
        lenW csaved txBlob outVals balBytes balEnabled x10v) h := by
  intro h hp
  unfold afterEndRegs at hp
  have hp1 :
      (((.x1 ↦ᵣ link) **
          ((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            (.x10 ↦ᵣ x10v) **
            regOwn .x6 ** regOwn .x7 **
            regOwn .x13 **
            regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            savedFrame spC csaved **
            stackFree spC nCalleeStackDwords **
            payload txBase outBase balBase txBlob outVals balBytes balEnabled **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x5 ** regOwn .x12 ** regOwn .x11)) h) := by
    xperm_hyp hp
  have hp2 := sepConj_mono (regIs_to_regOwn .x1 link) (fun _ hh => hh) h hp1
  unfold afterEndOwnRa afterEndCore
  xperm_hyp hp2

/-- Introduce THREE trailing owned registers (right-assoc `**` chain). -/
private theorem of_forall3
    {nSteps : Nat} {entry exit_ : Word} {r1 r2 r3 : Reg}
    {P Q : Assertion} {cr : CodeReq}
    (h : ∀ v1 v2 v3, cpsTripleWithin nSteps entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3)) Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, ⟨v3, hv3⟩⟩ := hO2
  exact h v1 v2 v3 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1, g4, g5, d3, u3, hv2, hv3⟩, hRb⟩ hpc

private theorem core_vals_to_endSpanPre
    (spC txBase outBase balBase chainIdW nW iW startW endW lenW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool)
    (x10v old5 old12 old11 : Word) :
    ∀ h, ((afterEndCore spC txBase outBase balBase chainIdW nW iW startW endW
          lenW csaved txBlob outVals balBytes balEnabled x10v **
        (.x5 ↦ᵣ old5) ** (.x12 ↦ᵣ old12) ** (.x11 ↦ᵣ old11)) h) →
      (((.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
          (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
          (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
          regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          savedFrame spC csaved **
          stackFree spC nCalleeStackDwords **
          payload txBase outBase balBase txBlob outVals balBytes balEnabled **
          (.x0 ↦ᵣ (0 : Word))) h) := by
  intro h hp
  unfold afterEndCore at hp
  xperm_hyp hp

set_option maxRecDepth 8000 in
/-- AfterEndOffset → AfterEndSpan via EndSpanSetup peels. -/
theorem bvtIterEndSpanSetup_fromEnd
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (n i : Nat)
    (startW endW link x10v : Word)
    (hok : IterOk txBlob n i)
    (hStart : startW = hok.startW)
    (hEnd : endW = hok.endW)
    (hi61 : i < 2 ^ 61) :
    let iW := BitVec.ofNat 64 i
    let lenW := BitVec.ofNat 64 txBlob.length
    let txPtr := txBase + startW
    let txLenW := endW - startW
    let outPtr := outBase + BitVec.ofNat 64 (8 * i)
    cpsTripleWithin 6 AfterEndOffset AfterEndSpan bvtCode
      (afterEndRegs spC txBase outBase balBase chainIdW nW iW startW endW lenW
        csaved txBlob outVals balBytes balEnabled link x10v)
      ((.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
        (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
        regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word))) := by
  intro iW lenW txPtr txLenW outPtr
  refine cpsTripleWithin_weaken
    (fun h hp => afterEnd_to_ownRa spC txBase outBase balBase chainIdW nW iW
      startW endW lenW csaved txBlob outVals balBytes balEnabled link x10v h hp)
    (fun _ hq => hq) ?_
  unfold afterEndOwnRa
  refine of_forall3 (r1 := .x5) (r2 := .x12) (r3 := .x11) (fun old5 old12 old11 => ?_)
  have h0 := bvtIterEndSpanSetup spC txBase outBase balBase chainIdW nW csaved
    txBlob outVals balBytes balEnabled n i startW endW old5 x10v old11 old12
    hok hStart hEnd hi61
  exact cpsTripleWithin_weaken
    (fun h hp => core_vals_to_endSpanPre spC txBase outBase balBase chainIdW nW
      iW startW endW lenW csaved txBlob outVals balBytes balEnabled x10v
      old5 old12 old11 h hp)
    (fun _ hq => by xperm_hyp hq) h0

/-! ## EndSpan → FromIntrinsic (bal=0) + LoopInv post reshape

    Specialized to balEnabled=false for the first one-iter path. bal≠0 is
    parallel once this reshape pattern is stable. -/

/-- EndSpan post (concrete x1, bal=0) → FromIntrinsic bal=0 pre. -/
private theorem endSpan_to_fromIntr_bal0
    (spC txBase outBase chainIdW nW iW startW endW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8))
    (txPtr txLenW outPtr old1 : Word) (i : Nat) :
    ∀ h, (((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
            (.x24 ↦ᵣ (0 : Word)) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
            (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
            (.x1 ↦ᵣ old1) ** regOwn .x6 ** regOwn .x7 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            savedFrame spC csaved **
            stackFree spC nCalleeStackDwords **
            payload txBase outBase (0 : Word) txBlob outVals balBytes false **
            (.x0 ↦ᵣ (0 : Word))) h) →
      (((.x1 ↦ᵣ old1) **
          (.x2 ↦ᵣ spC) ** stackFree spC nCalleeStackDwords **
          (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
          bytesRegion txBase txBlob **
          wordArray outBase outVals **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          loopIntrinsicFrame spC txBase outBase (0 : Word) chainIdW nW iW
            startW endW (BitVec.ofNat 64 txBlob.length) csaved balBytes
            false) h) := by
  intro h hp
  have hp1 :
      (((.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
          ((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
            (.x24 ↦ᵣ (0 : Word)) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
            (.x1 ↦ᵣ old1) ** regOwn .x6 ** regOwn .x7 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            savedFrame spC csaved **
            stackFree spC nCalleeStackDwords **
            payload txBase outBase (0 : Word) txBlob outVals balBytes false **
            (.x0 ↦ᵣ (0 : Word)))) h) := by
    xperm_hyp hp
  have hp2 := sepConj_mono (regIs_to_regOwn .x5 (BitVec.ofNat 64 (8 * i)))
    (fun _ hh => hh) h hp1
  simp only [payload, loopIntrinsicFrame, Bool.false_eq_true, ↓reduceIte] at hp2 ⊢
  xperm_hyp hp2

set_option maxRecDepth 8000 in
/-- bal=0 FromIntrinsic post → LoopInv (i+1). -/
private theorem bal0Post_to_loopInv
    (spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (i : Nat) (startW endW : Word) :
    ∀ h, (((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
            (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x24 ↦ᵣ (0 : Word)) **
            (.x1 ↦ᵣ LinkIntrinsic) **
            (.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) **
            (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
            (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            savedFrame spC csaved **
            stackFree spC nCalleeStackDwords **
            bytesRegion txBase txBlob **
            wordArray outBase outVals **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
            regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) h) →
      (LoopInv spC txBase outBase (0 : Word) chainIdW nW csaved txBlob outVals
        balBytes false (i + 1)) h := by
  intro h hp
  have step (r : Reg) (v : Word) (P : Assertion) :
      ∀ h', ((r ↦ᵣ v) ** P) h' → (regOwn r ** P) h' :=
    fun h' hp' => sepConj_mono (regIs_to_regOwn r v) (fun _ hh => hh) h' hp'
  have hp1 :
      (((.x1 ↦ᵣ LinkIntrinsic) ** (.x10 ↦ᵣ (0 : Word)) **
          (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
            (.x0 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ (0 : Word)) **
            (.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
            (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            savedFrame spC csaved **
            stackFree spC nCalleeStackDwords **
            bytesRegion txBase txBlob ** wordArray outBase outVals **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
            regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) h) := by
    xperm_hyp hp
  have hp2 := step .x1 LinkIntrinsic _ h hp1
  have hp3 :
      (((.x10 ↦ᵣ (0 : Word)) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          (regOwn .x1 **
            ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
              (.x0 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ (0 : Word)) **
              (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
              (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
              (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
              (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
              savedFrame spC csaved **
              stackFree spC nCalleeStackDwords **
              bytesRegion txBase txBlob ** wordArray outBase outVals **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
              regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31))) h) := by
    xperm_hyp hp2
  have hp4 := step .x10 (0 : Word) _ h hp3
  have hp5 :
      (((.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          (regOwn .x10 ** regOwn .x1 **
            ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
              (.x0 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ (0 : Word)) **
              (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
              (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
              (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
              (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
              savedFrame spC csaved **
              stackFree spC nCalleeStackDwords **
              bytesRegion txBase txBlob ** wordArray outBase outVals **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
              regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31))) h) := by
    xperm_hyp hp4
  have hp6 := step .x22 startW _ h hp5
  have hp7 :
      (((.x23 ↦ᵣ endW) **
          (regOwn .x22 ** regOwn .x10 ** regOwn .x1 **
            ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
              (.x0 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ (0 : Word)) **
              (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
              (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
              (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
              (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
              savedFrame spC csaved **
              stackFree spC nCalleeStackDwords **
              bytesRegion txBase txBlob ** wordArray outBase outVals **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
              regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31))) h) := by
    xperm_hyp hp6
  have hp8 := step .x23 endW _ h hp7
  -- Name the tail so we can inject emp via ← sepConj_emp_left'.
  let R : Assertion :=
    regOwn .x23 ** regOwn .x22 ** regOwn .x10 ** regOwn .x1 **
      ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        bytesRegion txBase txBlob **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
  have hp9 : (wordArray outBase outVals ** R) h := by
    dsimp only [R]; xperm_hyp hp8
  have hp10 : (wordArray outBase outVals ** (empAssertion ** R)) h := by
    rwa [← sepConj_emp_left' R] at hp9
  -- Expand goal without deep simp on LoopInv body.
  unfold LoopInv payload scratchRegs
  simp only [Bool.false_eq_true, ↓reduceIte]
  dsimp only [R] at hp10
  xperm_hyp hp10

/-- EndSpan post with regOwn x1 pulled rightmost (for of_forall). -/
private def endSpanOwnRa (spC txBase outBase chainIdW nW iW startW endW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (txPtr txLenW outPtr : Word) (i : Nat)
    : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
  (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
  (.x24 ↦ᵣ (0 : Word)) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
  (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
  (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
  regOwn .x6 ** regOwn .x7 **
  regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  savedFrame spC csaved **
  stackFree spC nCalleeStackDwords **
  payload txBase outBase (0 : Word) txBlob outVals balBytes false **
  (.x0 ↦ᵣ (0 : Word))

private theorem endSpan_to_ownRa
    (spC txBase outBase chainIdW nW iW startW endW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (txPtr txLenW outPtr : Word) (i : Nat) :
    ∀ h, (((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
            (.x24 ↦ᵣ (0 : Word)) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
            (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
            regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            savedFrame spC csaved **
            stackFree spC nCalleeStackDwords **
            payload txBase outBase (0 : Word) txBlob outVals balBytes false **
            (.x0 ↦ᵣ (0 : Word))) h) →
      ((endSpanOwnRa spC txBase outBase chainIdW nW iW startW endW csaved
          txBlob outVals balBytes txPtr txLenW outPtr i ** regOwn .x1) h) := by
  intro h hp
  unfold endSpanOwnRa
  xperm_hyp hp

private theorem ownRa_vals_to_endSpan
    (spC txBase outBase chainIdW nW iW startW endW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (txPtr txLenW outPtr old1 : Word) (i : Nat) :
    ∀ h, ((endSpanOwnRa spC txBase outBase chainIdW nW iW startW endW csaved
            txBlob outVals balBytes txPtr txLenW outPtr i ** (.x1 ↦ᵣ old1)) h) →
      (((.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
          (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          (.x24 ↦ᵣ (0 : Word)) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
          (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
          (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
          (.x1 ↦ᵣ old1) ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          savedFrame spC csaved **
          stackFree spC nCalleeStackDwords **
          payload txBase outBase (0 : Word) txBlob outVals balBytes false **
          (.x0 ↦ᵣ (0 : Word))) h) := by
  intro h hp
  unfold endSpanOwnRa at hp
  xperm_hyp hp

set_option maxRecDepth 8000 in
/-- AfterEndSpan → LoopGuard (i+1) on bal=0 under IntrinsicAssumed. -/
theorem bvtIterBal0_fromEndSpan
    (hintr : IntrinsicAssumed fullCode)
    (spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8))
    (i off len : Nat) (startW endW : Word)
    (hentry : hintr.entry = (GuestAddrs.tx_intrinsic_state_gas : Word))
    (hret : (LinkIntrinsic &&& ~~~(1 : Word)) = LinkIntrinsic)
    (hstart : startW = BitVec.ofNat 64 off)
    (hlen : off + len ≤ txBlob.length)
    (htxLen : endW - startW = BitVec.ofNat 64 len)
    (hi : i < outVals.length)
    (hcell : outVals[i] = pureIntrinsicStateGasSuccess) :
    let iW := BitVec.ofNat 64 i
    let bodyLenW := BitVec.ofNat 64 txBlob.length
    let txPtr := txBase + startW
    let txLenW := endW - startW
    let outPtr := outBase + BitVec.ofNat 64 (8 * i)
    cpsTripleWithin ((1 + nIntrinsicSteps) + 4) AfterEndSpan LoopGuard fullCode
      ((.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ (0 : Word)) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
        (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
        regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        payload txBase outBase (0 : Word) txBlob outVals balBytes false **
        (.x0 ↦ᵣ (0 : Word)))
      (LoopInv spC txBase outBase (0 : Word) chainIdW nW csaved txBlob outVals
        balBytes false (i + 1)) := by
  intro iW bodyLenW txPtr txLenW outPtr
  refine cpsTripleWithin_weaken
    (fun h hp => endSpan_to_ownRa spC txBase outBase chainIdW nW iW startW endW
      csaved txBlob outVals balBytes txPtr txLenW outPtr i h hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x1) (fun old1 => ?_)
  have hcore := bvtIterBal0FromIntrinsic hintr spC txBase outBase chainIdW nW
    csaved txBlob outVals balBytes i off len startW endW old1
    hentry hret hstart hlen htxLen hi hcell
  refine cpsTripleWithin_weaken
    (fun h hp => by
      have hp1 := ownRa_vals_to_endSpan spC txBase outBase chainIdW nW iW
        startW endW csaved txBlob outVals balBytes txPtr txLenW outPtr old1 i h hp
      exact endSpan_to_fromIntr_bal0 spC txBase outBase chainIdW nW iW
        startW endW csaved txBlob outVals balBytes txPtr txLenW outPtr
        old1 i h hp1)
    (fun h hq => bal0Post_to_loopInv spC txBase outBase chainIdW nW csaved
      txBlob outVals balBytes i startW endW h hq) hcore

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
