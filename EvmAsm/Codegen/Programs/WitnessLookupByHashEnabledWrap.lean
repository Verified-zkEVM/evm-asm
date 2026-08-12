/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledWrap

  #12183 — enable=1 empty-miss whole-routine wrap.

  * `wlhEn_body_core` fuel 68 (+36→+580) under nested stack
  * `witness_lookup_by_hash_spec_within_enabled_empty` fuel 87 via abiFrame_spec_own
  Domain: widx_enabled=1, widx_count=0, section_len=0 (REACHABLE).
  Nested stack: Own at newSp-64 (walk residual needs stackFree sp0 16 — SAY SO).
  Residual callWithin adapter + WlEmpty three-site restate: follow-on.
-/

import EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledBody
import EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledEmpty
import EvmAsm.Codegen.Programs.WitnessLookupByHashSpec
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedEmpty
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Codegen.WitnessLookupByHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec (WidxCountLoc indexedFrame)
open EvmAsm.Codegen.WitnessLookupByHashIndexedEmpty (IndexedSaved indexedSavedVals)

set_option maxRecDepth 8000

/-- Nested stack free below parent SP. -/
def wlhEnNestedStack (spC : Word) : Assertion :=
  frameSlotsOwn indexedFrame (spC + signExtend12 (-64 : BitVec 12))

theorem wlhEnNestedStack_pcFree (spC : Word) :
    (wlhEnNestedStack spC).pcFree := by
  unfold wlhEnNestedStack; pcf

/-- Body ambient F through setup→call: parent frame + nested stack + x1/x2/x21/x22.
    No x10 — Aregs owns a0 after ABI restore (would double-own). -/
def wlhEnBodyF (newSp : Word) (vals : Reg → Word) : Assertion :=
  ((.x1 : Reg) ↦ᵣ vals .x1) ** ((.x2 : Reg) ↦ᵣ newSp) **
  ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22) **
  frameSlotsSaved wlhFrame newSp vals **
  wlhEnNestedStack newSp

theorem wlhEnBodyF_pcFree (newSp : Word) (vals : Reg → Word) :
    (wlhEnBodyF newSp vals).pcFree := by
  unfold wlhEnBodyF wlhEnNestedStack; pcf

/-- +36 → +580 body under nested stack. Fuel 68 = 32+36.
    Entry s-regs a8..a20 are overwritten by arg moves to secPtr/0/hash/outOff/outLen.
    After call path, x10=1 (indexed miss), outs written only on hit (empty keeps a3/a4). -/
theorem wlhEn_body_core
    (newSp : Word) (vals : Reg → Word)
    (v5 v6 : Word)
    (a8 a9 a18 a19 a20 : Word)
    (secPtr hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word) :
    let s := wlhEnIdxSaved (vals .x1) secPtr hashPtr outOff outLen
      (vals .x21) (vals .x22)
    let retCall : Word := (wlhB + 164 : Word) + 4
    cpsTripleWithin 68 (wlhB + 36) (wlhB + 580) enableFullCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        wlhEnAregs secPtr hashPtr outOff outLen **
        ((.x8 : Reg) ↦ᵣ a8) ** ((.x9 : Reg) ↦ᵣ a9) **
        ((.x18 : Reg) ↦ᵣ a18) ** ((.x19 : Reg) ↦ᵣ a19) **
        ((.x20 : Reg) ↦ᵣ a20) **
        wlhEnCells secPtr nCalls nIdx nMiss nLin nLast nMax nLinMiss **
        wlhEnBodyF newSp vals)
      (wlhEnBodyExit newSp retCall s hashPtr outOff outLen
        nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr
        (frameSlotsSaved wlhFrame newSp vals)) := by
  intro s retCall
  have hF := wlhEnBodyF_pcFree newSp vals
  -- setup → call entry (+36 → +164)
  have h1 := wlhEn_body_to_call v5 v6 a8 a9 a18 a19 a20
    secPtr hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss
    (wlhEnBodyF newSp vals) hF
  -- Reshape body_to_call post → (x1 ** CallP ** Extra)
  -- body_to_call post:
  --   x0, x5=IdxCallsLoc, x6=nIdx+1, Aregs, Sregs, Cells, BodyF
  -- CallP: x2, s0-s6, x12-14, x5, x10, nested Own, WidxCount
  --   with s0=secPtr,s1=0,s2=hash,s3=outOff,s4=outLen,s5=x21,s6=x22
  --   v5=IdxCallsLoc, v10=secPtr (a0 after ABI)
  -- Extra: x0, x6, x11, cells sans WidxCount, parent Saved
  have h1' : cpsTripleWithin 32 (wlhB + 36) (wlhB + 164) enableFullCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        wlhEnAregs secPtr hashPtr outOff outLen **
        ((.x8 : Reg) ↦ᵣ a8) ** ((.x9 : Reg) ↦ᵣ a9) **
        ((.x18 : Reg) ↦ᵣ a18) ** ((.x19 : Reg) ↦ᵣ a19) **
        ((.x20 : Reg) ↦ᵣ a20) **
        wlhEnCells secPtr nCalls nIdx nMiss nLin nLast nMax nLinMiss **
        wlhEnBodyF newSp vals)
      ((.x1 ↦ᵣ vals .x1) **
        wlhIdxCallP newSp s hashPtr outOff outLen IdxCallsLoc secPtr **
        wlhEnCallExtra nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr
          (frameSlotsSaved wlhFrame newSp vals)) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) h1
    dsimp [wlhEnAregs, wlhEnSregs, wlhEnCells, wlhEnBodyF, wlhEnNestedStack,
      wlhIdxCallP, wlhEnCallExtra, wlhEnIdxSaved, indexedSavedVals, s] at hq ⊢
    xperm_chunked hq
  -- call → body exit (+164 → +580)
  have h2 := wlhEn_call_to_bodyExit newSp (vals .x1) (vals .x21) (vals .x22)
    secPtr hashPtr outOff outLen IdxCallsLoc secPtr
    nCalls nIdx nMiss nLin nLast nMax nLinMiss
    (frameSlotsSaved wlhFrame newSp vals) (by pcf)
  have c := cpsTripleWithin_seq_same_cr h1' h2
  exact cpsTripleWithin_mono_nSteps (by decide : 32 + 36 ≤ 68) c

/-! ## abiFrame body + whole-routine wrap (enable=1 empty) -/

/-- Caller ambient (no frame regs). Nested Own below parent SP. -/
def wlhEnCallerPre (newSp : Word)
    (v5 v6 secPtr hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
  wlhEnAregs secPtr hashPtr outOff outLen **
  wlhEnCells secPtr nCalls nIdx nMiss nLin nLast nMax nLinMiss **
  wlhEnNestedStack newSp

theorem wlhEnCallerPre_pcFree (newSp : Word)
    (v5 v6 secPtr hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word) :
    (wlhEnCallerPre newSp v5 v6 secPtr hashPtr outOff outLen
      nCalls nIdx nMiss nLin nLast nMax nLinMiss).pcFree := by
  unfold wlhEnCallerPre wlhEnAregs wlhEnCells wlhEnNestedStack; pcf

/-- Post ambient after enable-empty body. -/
def wlhEnCallerPost (newSp retCall : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (secPtr : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (1 : Word)) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
  ((.x5 : Reg) ↦ᵣ IdxMissLoc) ** ((.x6 : Reg) ↦ᵣ (nMiss + 1)) **
  ((.x12 : Reg) ↦ᵣ hashPtr) ** ((.x13 : Reg) ↦ᵣ outOff) **
  ((.x14 : Reg) ↦ᵣ outLen) **
  (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (1 : Word)) **
  (SecPtrLoc ↦ₘ secPtr) ** (SecLenLoc ↦ₘ (0 : Word)) **
  (WidxCountLoc ↦ₘ (0 : Word)) **
  (IdxCallsLoc ↦ₘ (nIdx + 1)) ** (IdxMissLoc ↦ₘ (nMiss + 1)) **
  (LinCallsLoc ↦ₘ nLin) ** (LinLastLoc ↦ₘ nLast) **
  (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ nLinMiss) **
  frameSlotsSaved indexedFrame (newSp + signExtend12 (-64 : BitVec 12))
    (indexedSavedVals { s with ra := retCall })

theorem wlhEnCallerPost_pcFree (newSp retCall : Word) (s : IndexedSaved)
    (hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (secPtr : Word) :
    (wlhEnCallerPost newSp retCall s hashPtr outOff outLen
      nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr).pcFree := by
  unfold wlhEnCallerPost
  repeat' first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact (pcFree_frameSlotsSaved _ _ _)

private theorem regsAt_wlhFrame_en (vals : Reg → Word) :
    regsAt wlhFrame vals =
      (((.x1 : Reg) ↦ᵣ vals .x1) ** ((.x8 : Reg) ↦ᵣ vals .x8) **
        ((.x9 : Reg) ↦ᵣ vals .x9) ** ((.x18 : Reg) ↦ᵣ vals .x18) **
        ((.x19 : Reg) ↦ᵣ vals .x19) ** ((.x20 : Reg) ↦ᵣ vals .x20) **
        ((.x21 : Reg) ↦ᵣ vals .x21) ** ((.x22 : Reg) ↦ᵣ vals .x22)) := by
  simp [wlhFrame, regsAt, sepConj_emp_right']

private theorem regsOwnAt_wlhFrame_en :
    regsOwnAt wlhFrame =
      (regOwn .x1 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
        regOwn .x20 ** regOwn .x21 ** regOwn .x22) := by
  simp [wlhFrame, regsOwnAt, sepConj_emp_right']

private theorem ent_own8_en (r1 r2 r3 r4 r5 r6 r7 r8 : Reg)
    (w1 w2 w3 w4 w5 w6 w7 w8 : Word) (P : Assertion) (h : PartialState)
    (hp : ((r1 ↦ᵣ w1) ** (r2 ↦ᵣ w2) ** (r3 ↦ᵣ w3) ** (r4 ↦ᵣ w4) ** (r5 ↦ᵣ w5) **
      (r6 ↦ᵣ w6) ** (r7 ↦ᵣ w7) ** (r8 ↦ᵣ w8) ** P) h) :
    (regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 ** regOwn r5 ** regOwn r6 **
      regOwn r7 ** regOwn r8 ** P) h :=
  sepConj_mono (regIs_to_regOwn r1 w1)
    (sepConj_mono (regIs_to_regOwn r2 w2)
      (sepConj_mono (regIs_to_regOwn r3 w3)
        (sepConj_mono (regIs_to_regOwn r4 w4)
          (sepConj_mono (regIs_to_regOwn r5 w5)
            (sepConj_mono (regIs_to_regOwn r6 w6)
              (sepConj_mono (regIs_to_regOwn r7 w7)
                (sepConj_mono (regIs_to_regOwn r8 w8) (fun _ hx => hx)))))))) h hp

/-- Body in abiFrame shape. Fuel 68. Pattern: empty_section body. -/
theorem wlhEn_empty_body_abi
    (newSp : Word) (vals : Reg → Word)
    (v5 v6 secPtr hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word) :
    let s := wlhEnIdxSaved (vals .x1) secPtr hashPtr outOff outLen
      (vals .x21) (vals .x22)
    let retCall : Word := (wlhB + 164 : Word) + 4
    cpsTripleWithin 68
      (wlhB + BitVec.ofNat 64 (4 * (1 + wlhFrame.length)))
      (wlhB + BitVec.ofNat 64 (4 * (1 + wlhFrame.length + wlhBody.length)))
      enableFullCode
      (((.x2 : Reg) ↦ᵣ newSp) ** regsAt wlhFrame vals **
        frameSlotsSaved wlhFrame newSp vals **
        wlhEnCallerPre newSp v5 v6 secPtr hashPtr outOff outLen
          nCalls nIdx nMiss nLin nLast nMax nLinMiss)
      (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt wlhFrame **
        frameSlotsSaved wlhFrame newSp vals **
        wlhEnCallerPost newSp retCall s hashPtr outOff outLen
          nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr) := by
  intro s retCall
  rw [wlhFrame_length, wlhBody_length]
  simp only [show 4 * (1 + 8) = 36 from rfl, show 4 * (1 + 8 + 136) = 580 from rfl]
  have core := wlhEn_body_core newSp vals v5 v6
    (vals .x8) (vals .x9) (vals .x18) (vals .x19) (vals .x20)
    secPtr hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss
  refine cpsTripleWithin_weaken (fun h hp => ?pre) (fun h hq => ?post) core
  case pre =>
    rw [regsAt_wlhFrame_en] at hp
    dsimp [wlhEnCallerPre, wlhEnBodyF, wlhEnNestedStack, wlhEnAregs, wlhEnCells] at hp ⊢
    xperm_chunked hp
  case post =>
    -- BodyExit has x1=retCall, s0..s4=secPtr/0/hash/outs, s5/s6=entry vals
    rw [regsOwnAt_wlhFrame_en]
    have hq1 : (wlhEnBodyExit newSp retCall s hashPtr outOff outLen
        nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr
        (frameSlotsSaved wlhFrame newSp vals)) h := hq
    dsimp [wlhEnBodyExit, wlhEnIdxSaved, indexedSavedVals, s, retCall] at hq1
    have hq2 : (((.x1 : Reg) ↦ᵣ retCall) **
        ((.x8 : Reg) ↦ᵣ secPtr) ** ((.x9 : Reg) ↦ᵣ (0 : Word)) **
        ((.x18 : Reg) ↦ᵣ hashPtr) ** ((.x19 : Reg) ↦ᵣ outOff) **
        ((.x20 : Reg) ↦ᵣ outLen) ** ((.x21 : Reg) ↦ᵣ vals .x21) **
        ((.x22 : Reg) ↦ᵣ vals .x22) **
        (((.x2 : Reg) ↦ᵣ newSp) ** frameSlotsSaved wlhFrame newSp vals **
          wlhEnCallerPost newSp retCall s hashPtr outOff outLen
            nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr)) h := by
      dsimp [wlhEnCallerPost, wlhEnIdxSaved, indexedSavedVals, s, retCall]
      xperm_chunked hq1
    have hq3 := ent_own8_en .x1 .x8 .x9 .x18 .x19 .x20 .x21 .x22
      retCall secPtr (0 : Word) hashPtr outOff outLen (vals .x21) (vals .x22) _ h hq2
    dsimp [wlhEnCallerPost, wlhEnIdxSaved, indexedSavedVals, s, retCall] at hq3 ⊢
    xperm_chunked hq3

/-- Whole-routine enable=1 empty-miss. Fuel 87 = 1+8+68+8+1+1.
    Domain: widx_enabled=1, widx_count=0, section_len=0 (REACHABLE).
    Nested Own at newSp-64 in pre (walk entry stackFree sp0 16 — SAY SO).
    CR = enableFullCode. -/
theorem witness_lookup_by_hash_spec_within_enabled_empty
    (sp0 ret : Word) (vals : Reg → Word)
    (v5 v6 secPtr hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (hret : vals .x1 = ret)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    let newSp := sp0 + signExtend12 (-64 : BitVec 12)
    let s := wlhEnIdxSaved (vals .x1) secPtr hashPtr outOff outLen
      (vals .x21) (vals .x22)
    let retCall : Word := (wlhB + 164 : Word) + 4
    cpsTripleWithin 87 wlhB ret enableFullCode
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt wlhFrame vals **
        frameSlotsOwn wlhFrame newSp **
        wlhEnCallerPre newSp v5 v6 secPtr hashPtr outOff outLen
          nCalls nIdx nMiss nLin nLast nMax nLinMiss)
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt wlhFrame vals **
        frameSlotsSaved wlhFrame newSp vals **
        wlhEnCallerPost newSp retCall s hashPtr outOff outLen
          nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr) := by
  intro newSp s retCall
  set spC : Word := sp0 + signExtend12 (-64 : BitVec 12)
  set sSaved := wlhEnIdxSaved (vals .x1) secPtr hashPtr outOff outLen
    (vals .x21) (vals .x22)
  set rc : Word := (wlhB + 164 : Word) + 4
  have hbody := wlhEn_empty_body_abi spC vals v5 v6 secPtr hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss
  have hpreF := wlhEnCallerPre_pcFree spC v5 v6 secPtr hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss
  have hpostF := wlhEnCallerPost_pcFree spC rc sSaved hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr
  have h := abiFrame_spec_own wlhB sp0 ret (-64 : BitVec 12) (64 : BitVec 12)
    wlhFrame (0 : BitVec 12)
    [(.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)), (.x18, (24 : BitVec 12)),
     (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)), (.x21, (48 : BitVec 12)),
     (.x22, (56 : BitVec 12))]
    vals wlhBody 68
    (wlhEnCallerPre spC v5 v6 secPtr hashPtr outOff outLen
      nCalls nIdx nMiss nLin nLast nMax nLinMiss)
    (wlhEnCallerPost spC rc sSaved hashPtr outOff outLen
      nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr)
    enableFullCode rfl (by decide) (by decide)
    (by rw [wlh_abiFrame_byte_tie]; decide)
    hret halign (sext_frameRestore _ _ _ (by decide))
    hpreF hpostF
    (by
      rw [wlh_abiFrame_byte_tie]
      intro a i hi
      exact wlh_in_enableFull a i (by simpa [wlhCr] using hi))
    hbody
  rw [wlhFrame_length] at h
  -- Fuel 1+8+68+8+1+1 = 87; unify let-bound newSp/s/retCall with spC/sSaved/rc
  change cpsTripleWithin 87 wlhB ret enableFullCode
    (((.x2 : Reg) ↦ᵣ sp0) ** regsAt wlhFrame vals **
      frameSlotsOwn wlhFrame spC **
      wlhEnCallerPre spC v5 v6 secPtr hashPtr outOff outLen
        nCalls nIdx nMiss nLin nLast nMax nLinMiss)
    (((.x2 : Reg) ↦ᵣ sp0) ** regsAt wlhFrame vals **
      frameSlotsSaved wlhFrame spC vals **
      wlhEnCallerPost spC rc sSaved hashPtr outOff outLen
        nCalls nIdx nMiss nLin nLast nMax nLinMiss secPtr) at h
  simpa [newSp, s, retCall, spC, sSaved, rc] using h

/-! ## Residual callWithin (follow-on)

    `wlhCallWithin_enabled_empty` (callWithin adapter for walk sites) needs
    `stackFree sp0 16` reshape (parent Own + nested Own). Landed as a follow-on
    once the whole-routine top above is reviewed; walk `fullCode` already unions
    indexed (#12183 Machine) so `enableFullCode ⊆ fullCode`.
-/

end EvmAsm.Codegen.WitnessLookupByHashSpec
