/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledOneHitWrap

  #12036 — **call-site adapter for the enable=1 HIT arm.**

  `witness_lookup_by_hash_spec_within_enabled_one_hit` (fuel 402, #12690) is a
  whole-routine `cpsTripleWithin` in `abiFrame` shape. A caller cannot consume
  it directly: the residual the three `mpt_walk` sites need is a `callWithin`
  over one `jal`, with the callee's two frames folded into the caller-visible
  `stackFree sp0 16`. This module supplies exactly that adapter, mirroring
  `wlhCallWithin_enabled_empty` / `wlCallWithinShapeEn` (#12183) one domain
  over.

  ## Domain (SAY SO) — `widx_count = 1` only

  Everything the fuel-402 top requires: `widx_enabled = 1`, the registered
  section pointer AND length equal to `a0`/`a1` (both free but matched),
  `widx_count = 1`, and the sole `widx_records` record's 32-byte hash equal to
  the target (`coverHitHash`). This is the **`widx_count = 1`** hit domain, NOT
  the general binary-search hit path: arbitrary `widx_count` remains open, and
  so does the linear scan with `zkvm_keccak256` (both unreached here).

  ⇒ Consequently `wlCallWithinShapeHitEn` is a `widx_count = 1` residual. It is
  NOT `MptWalkResidualChain.wlCallWithinShapeHit`, whose ambient is the
  enable=0 walk shape (`stackFree sp0 8`, six-cell `wlTelemetry`, no index
  cells and no `widx_records` bytes) and which therefore cannot be established
  from this arm at all. See the module docstring of `MptWalkWlEnabledHit`.
-/

import EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledOneHit
import EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledWrap
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Codegen.WitnessLookupByHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec
  (WidxCountLoc WidxRecordsBase indexedFrame)
open EvmAsm.Codegen.WitnessLookupByHashIndexedEmpty (IndexedSaved indexedSavedVals)
open EvmAsm.Codegen.WitnessLookupByHashIndexedOneHit
  (hitOffAddr hitLenAddr hitOffW hitLenW hitCells hitHashBytes coverHitHash)

set_option maxRecDepth 8000

/-- Caller-visible argument ambient of the `enable = 1` hit arm: exactly
    `wlhHitCallerPre` with the nested indexed frame (`wlhEnNestedStack`)
    removed — at a call site that frame is folded into `stackFree sp0 16`
    together with the routine's own frame. -/
def wlhHitArgs (v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 : Word)
    (nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
  wlhHitAregs secPtr secLen hashPtr outOff outLen **
  wlhHitCells secPtr secLen nCalls nIdx nMiss nLin nLast nMax nLinMiss **
  ((.x7 : Reg) ↦ᵣ w7) ** ((.x15 : Reg) ↦ᵣ w15) **
  ((.x16 : Reg) ↦ᵣ w16) ** ((.x17 : Reg) ↦ᵣ w17) **
  ((.x28 : Reg) ↦ᵣ w28) ** ((.x29 : Reg) ↦ᵣ w29) **
  ((.x30 : Reg) ↦ᵣ w30) ** ((.x31 : Reg) ↦ᵣ w31) **
  (IdxHitLoc ↦ₘ nHit) **
  hitHashBytes hashPtr ** hitCells outOff outLen offOld lenOld

theorem wlhHitArgs_pcFree
    (v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 : Word)
    (nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss : Word) :
    (wlhHitArgs v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
      w7 w15 w16 w17 w28 w29 w30 w31
      nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss).pcFree := by
  unfold wlhHitArgs wlhHitAregs wlhHitCells hitHashBytes hitCells
  repeat' first
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj

private theorem regsAt_wlhFrame_hitw (vals : Reg → Word) :
    regsAt wlhFrame vals =
      (((.x1 : Reg) ↦ᵣ vals .x1) ** ((.x8 : Reg) ↦ᵣ vals .x8) **
        ((.x9 : Reg) ↦ᵣ vals .x9) ** ((.x18 : Reg) ↦ᵣ vals .x18) **
        ((.x19 : Reg) ↦ᵣ vals .x19) ** ((.x20 : Reg) ↦ᵣ vals .x20) **
        ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22)) := by
  simp [wlhFrame, regsAt, sepConj_emp_right']

/-- **Call-site discharge, `enable = 1` hit at `widx_count = 1`.** Fuel 1+402.

    Instantiates `callWithin_spec` against
    `witness_lookup_by_hash_spec_within_enabled_one_hit`. The free stack is
    `stackFree sp0 16` (this routine's frame 8 + the nested indexed frame 8 —
    SAY SO), and `cr` must contain `enableFullCode` (`hcode`; walk `fullCode`
    does after #12152).

    Pattern mirrors `wlhCallWithin_enabled_empty`. The four extra hypotheses
    (`halignH`/`hovH`/`hvalidR`/`hvalidH`) are the callee's, carried verbatim:
    the target hash buffer is dword-aligned, does not wrap, and both the
    32-byte record and the 32-byte target are byte-accessible. -/
theorem wlhCallWithin_enabled_one_hit (cr : CodeReq) (callerPC vOld sp0 : Word)
    (offset : BitVec 21) (vals : Reg → Word) (F : Assertion)
    (v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 : Word)
    (nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss : Word)
    (hF : F.pcFree)
    (hvals : vals .x1 = callerPC + 4)
    (halign : ((callerPC + 4) &&& ~~~(1 : Word)) = callerPC + 4)
    (htarget : callerPC + signExtend21 offset = wlhB)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true)
    (hmem : ∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i →
      cr a = some i)
    (hcode : ∀ a i, enableFullCode a = some i → cr a = some i) :
    let newSp := sp0 + signExtend12 (-64 : BitVec 12)
    let retCall : Word := (wlhB + 164 : Word) + 4
    cpsTripleWithin (1 + 402) callerPC (callerPC + 4) cr
      ((((.x1 : Reg) ↦ᵣ vOld) ** ((.x2 : Reg) ↦ᵣ sp0) ** stackFree sp0 16 **
        wlhSregs vals **
        wlhHitArgs v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
          w7 w15 w16 w17 w28 w29 w30 w31
          nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss) ** F)
      ((((.x1 : Reg) ↦ᵣ (callerPC + 4)) ** ((.x2 : Reg) ↦ᵣ sp0) **
        frameSlotsSaved wlhFrame newSp vals **
        wlhSregs vals **
        wlhHitCallerPost newSp retCall
          (wlhHitIdxSaved (vals .x1) secPtr secLen hashPtr outOff outLen
            (vals .x21) (vals .x22))
          hashPtr outOff outLen secPtr secLen
          (nCalls + 1) (nIdx + 1) nHit nMiss nLin nLast nMax nLinMiss) ** F) := by
  intro newSp retCall
  have hbase := cpsTripleWithin_extend_code hcode
    (witness_lookup_by_hash_spec_within_enabled_one_hit sp0 (callerPC + 4) vals
      v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
      w7 w15 w16 w17 w28 w29 w30 w31
      nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss
      hvals (by simpa using halign) halignH hovH hvalidR hvalidH)
  have hbase' : cpsTripleWithin 402 wlhB (callerPC + 4) cr
      (((.x2 : Reg) ↦ᵣ sp0) **
        (((.x1 : Reg) ↦ᵣ (callerPC + 4)) ** wlhSregs vals) **
        stackFree sp0 16 **
        wlhHitArgs v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
          w7 w15 w16 w17 w28 w29 w30 w31
          nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss)
      (((.x2 : Reg) ↦ᵣ sp0) **
        (((.x1 : Reg) ↦ᵣ (callerPC + 4)) ** wlhSregs vals) **
        frameSlotsSaved wlhFrame newSp vals **
        wlhHitCallerPost newSp retCall
          (wlhHitIdxSaved (vals .x1) secPtr secLen hashPtr outOff outLen
            (vals .x21) (vals .x22))
          hashPtr outOff outLen secPtr secLen
          (nCalls + 1) (nIdx + 1) nHit nMiss nLin nLast nMax nLinMiss) := by
    refine cpsTripleWithin_weaken (fun h hp => ?pre) (fun h hq => ?post) hbase
    case pre =>
      have heq := stackFree16_eq_nested_parent sp0
      have hp1 :
          (((.x2 : Reg) ↦ᵣ sp0) **
            (((.x1 : Reg) ↦ᵣ (callerPC + 4)) ** wlhSregs vals) **
            (frameSlotsOwn indexedFrame
                (newSp + signExtend12 (-64 : BitVec 12)) **
              frameSlotsOwn wlhFrame newSp) **
            wlhHitArgs v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
              w7 w15 w16 w17 w28 w29 w30 w31
              nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss) h := by
        simpa [newSp, heq] using hp
      rw [regsAt_wlhFrame_hitw]
      simp only [hvals]
      dsimp [wlhHitCallerPre, wlhEnNestedStack, wlhHitAregs, wlhHitCells,
        wlhHitArgs, wlhSregs, newSp] at hp1 ⊢
      xperm_chunked hp1
    case post =>
      rw [regsAt_wlhFrame_hitw] at hq
      simp only [hvals] at hq
      dsimp [wlhSregs, wlhHitCallerPost, wlhHitIdxSaved, indexedSavedVals,
        newSp, retCall] at hq ⊢
      xperm_chunked hq
  have hPfree : ((((.x2 : Reg) ↦ᵣ sp0) ** stackFree sp0 16 ** wlhSregs vals **
      wlhHitArgs v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
        w7 w15 w16 w17 w28 w29 w30 w31
        nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss) ** F).pcFree := by
    refine pcFree_sepConj ?_ hF
    refine pcFree_sepConj pcFree_regIs (pcFree_sepConj (pcFree_stackFree _ _) ?_)
    refine pcFree_sepConj ?_ (wlhHitArgs_pcFree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _)
    unfold wlhSregs
    repeat' first
      | exact pcFree_regIs
      | apply pcFree_sepConj
  have hcallee : cpsTripleWithin 402 wlhB (callerPC + 4) cr
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
        ((((.x2 : Reg) ↦ᵣ sp0) ** stackFree sp0 16 ** wlhSregs vals **
          wlhHitArgs v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
            w7 w15 w16 w17 w28 w29 w30 w31
            nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss) ** F))
      (((.x1 : Reg) ↦ᵣ (callerPC + 4)) **
        ((((.x2 : Reg) ↦ᵣ sp0) **
          frameSlotsSaved wlhFrame newSp vals **
          wlhSregs vals **
          wlhHitCallerPost newSp retCall
            (wlhHitIdxSaved (vals .x1) secPtr secLen hashPtr outOff outLen
              (vals .x21) (vals .x22))
            hashPtr outOff outLen secPtr secLen
            (nCalls + 1) (nIdx + 1) nHit nMiss nLin nLast nMax nLinMiss) ** F)) := by
    have hfr := cpsTripleWithin_frameR F hF hbase'
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hfr
    · dsimp [wlhSregs] at hp ⊢
      xperm_hyp hp
    · dsimp [wlhSregs] at hq ⊢
      xperm_hyp hq
  have hcall := callWithin_spec callerPC wlhB vOld offset 402 htarget hmem hPfree
    hcallee
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hcall

/-- Residual shape for the `enable = 1` **hit** walk sites at `widx_count = 1`:
    the `callWithin` ambient of `wlhCallWithin_enabled_one_hit`.

    Pre:  `(x1 ** x2 ** stackFree sp0 16 ** sregs ** HitArgs) ** F`
    Post: `(x1 ** x2 ** parent Saved ** sregs ** HitCallerPost) ** F`

    SAY SO: `stackFree sp0 16`, and `widx_count = 1` (inside `wlhHitCells`) —
    this is the sole-record hit domain, not the general binary search. -/
def wlCallWithinShapeHitEn (cr : CodeReq) (callerPC vOld sp0 : Word)
    (vals : Reg → Word)
    (v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 : Word)
    (nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss : Word)
    (offset : BitVec 21) (F : Assertion) : Prop :=
  let newSp := sp0 + signExtend12 (-64 : BitVec 12)
  let retCall : Word := (wlhB + 164 : Word) + 4
  F.pcFree ∧
  vals .x1 = callerPC + 4 ∧
  ((callerPC + 4) &&& ~~~(1 : Word)) = callerPC + 4 ∧
  callerPC + signExtend21 offset = wlhB ∧
  (∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i →
    cr a = some i) ∧
  cpsTripleWithin (1 + 402) callerPC (callerPC + 4) cr
    ((((.x1 : Reg) ↦ᵣ vOld) ** ((.x2 : Reg) ↦ᵣ sp0) ** stackFree sp0 16 **
      wlhSregs vals **
      wlhHitArgs v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
        w7 w15 w16 w17 w28 w29 w30 w31
        nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss) ** F)
    ((((.x1 : Reg) ↦ᵣ (callerPC + 4)) ** ((.x2 : Reg) ↦ᵣ sp0) **
      frameSlotsSaved wlhFrame newSp vals **
      wlhSregs vals **
      wlhHitCallerPost newSp retCall
        (wlhHitIdxSaved (vals .x1) secPtr secLen hashPtr outOff outLen
          (vals .x21) (vals .x22))
        hashPtr outOff outLen secPtr secLen
        (nCalls + 1) (nIdx + 1) nHit nMiss nLin nLast nMax nLinMiss) ** F)

/-- Discharge the hit residual from the `callWithin` under
    `enableFullCode ⊆ cr`. `widx_count = 1` domain — SAY SO. -/
theorem wlCallWithinShapeHitEn_of_callWithin (cr : CodeReq)
    (callerPC vOld sp0 : Word)
    (offset : BitVec 21) (vals : Reg → Word) (F : Assertion)
    (v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld : Word)
    (w7 w15 w16 w17 w28 w29 w30 w31 : Word)
    (nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss : Word)
    (hF : F.pcFree)
    (hvals : vals .x1 = callerPC + 4)
    (halign : ((callerPC + 4) &&& ~~~(1 : Word)) = callerPC + 4)
    (htarget : callerPC + signExtend21 offset = wlhB)
    (halignH : hashPtr.toNat % 8 = 0)
    (hovH : hashPtr.toNat + 32 < 2 ^ 64)
    (hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true)
    (hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hashPtr + BitVec.ofNat 64 k) = true)
    (hmem : ∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i →
      cr a = some i)
    (hcode : ∀ a i, enableFullCode a = some i → cr a = some i) :
    wlCallWithinShapeHitEn cr callerPC vOld sp0 vals
      v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
      w7 w15 w16 w17 w28 w29 w30 w31
      nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss offset F := by
  refine ⟨hF, hvals, halign, htarget, hmem, ?_⟩
  exact wlhCallWithin_enabled_one_hit cr callerPC vOld sp0 offset vals F
    v5 v6 secPtr secLen hashPtr outOff outLen offOld lenOld
    w7 w15 w16 w17 w28 w29 w30 w31
    nCalls nIdx nHit nMiss nLin nLast nMax nLinMiss
    hF hvals halign htarget halignH hovH hvalidR hvalidH hmem hcode

end EvmAsm.Codegen.WitnessLookupByHashSpec
