/-
  Empty-section discharge of the three `mpt_walk` → `witness_lookup_by_hash`
  call sites against the **generic** `wlCallWithinShape` (#12144 ambient repair).

  ## Domain (SAY SO)

  Only `section_len = 0` and `widx_enabled = 0` (guaranteed miss, `a0 = 1`).
  Hit residual remains a DEPENDENCY.

  ## Acceptance

  Establishes `wlCallWithinShape fullCode …` via `wlhCallWithin_empty_section`
  + holds reshape. Generic residual is usable, not merely reworded.
-/

import EvmAsm.Codegen.Programs.MptWalkWlCall
import EvmAsm.Codegen.Programs.WitnessLookupByHashSpec
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.WitnessLookupByHashSpec

set_option maxRecDepth 8000

private abbrev rootOff : BitVec 21 :=
  jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 140)
private abbrev branchOff : BitVec 21 :=
  jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 404)
private abbrev extOff : BitVec 21 :=
  jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 840)

private theorem root_jal_mem :
    ∀ a i, CodeReq.singleton (pc 35) (.JAL .x1 rootOff) a = some i →
      fullCode a = some i :=
  walkMem (pc 35) 35 (.JAL .x1 rootOff)
    (by rw [program_length]; omega)
    (by unfold pc walkB; decide)
    (by decide)

private theorem branch_jal_mem :
    ∀ a i, CodeReq.singleton (pc 101) (.JAL .x1 branchOff) a = some i →
      fullCode a = some i :=
  walkMem (pc 101) 101 (.JAL .x1 branchOff)
    (by rw [program_length]; omega)
    (by unfold pc walkB; decide)
    (by decide)

private theorem ext_jal_mem :
    ∀ a i, CodeReq.singleton (pc 210) (.JAL .x1 extOff) a = some i →
      fullCode a = some i :=
  walkMem (pc 210) 210 (.JAL .x1 extOff)
    (by rw [program_length]; omega)
    (by unfold pc walkB; decide)
    (by decide)

private theorem root_ret_align :
    ((pc 35 + 4) &&& ~~~(1 : Word)) = pc 35 + 4 := by
  unfold pc walkB; decide

private theorem branch_ret_align :
    ((pc 101 + 4) &&& ~~~(1 : Word)) = pc 101 + 4 := by
  unfold pc walkB; decide

private theorem ext_ret_align :
    ((pc 210 + 4) &&& ~~~(1 : Word)) = pc 210 + 4 := by
  unfold pc walkB; decide

private theorem root_target :
    pc 35 + signExtend21 rootOff = wlhB := by
  unfold pc walkB wlhB rootOff; decide

private theorem branch_target :
    pc 101 + signExtend21 branchOff = wlhB := by
  unfold pc walkB wlhB branchOff; decide

private theorem ext_target :
    pc 210 + signExtend21 extOff = wlhB := by
  unfold pc walkB wlhB extOff; decide

private theorem wlhCr_eq_machine :
    WitnessLookupByHashSpec.wlhCr = MptWalkSpec.wlhCr := by
  unfold WitnessLookupByHashSpec.wlhCr MptWalkSpec.wlhCr
    WitnessLookupByHashSpec.wlhB MptWalkSpec.WlhB
  rfl

private theorem wlh_code_in_full :
    ∀ a i, WitnessLookupByHashSpec.wlhCr a = some i → fullCode a = some i := by
  intro a i hi
  rw [wlhCr_eq_machine] at hi
  exact wlhCalleeMem a i hi

/-- Cell names coincide (Spec `CallsLoc` vs residual `WlCallsLoc`). -/
private theorem cells_eq :
    CallsLoc = WlCallsLoc ∧ WidxEnLoc = WlWidxEnLoc ∧
    LinCallsLoc = WlLinCallsLoc ∧ LinLastLoc = WlLinLastLoc ∧
    LinMaxLoc = WlLinMaxLoc ∧ LinMissLoc = WlLinMissLoc := by
  unfold CallsLoc WidxEnLoc LinCallsLoc LinLastLoc LinMaxLoc LinMissLoc
    WlCallsLoc WlWidxEnLoc WlLinCallsLoc WlLinLastLoc WlLinMaxLoc WlLinMissLoc
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- Shared frame F: callee-saved s-regs + pass-through owns + user ambient. -/
def wlEmptyFrame (vals : Reg → Word) (F : Assertion) : Assertion :=
  wlhSregs vals **
  regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** F

theorem wlEmptyFrame_pcFree (vals : Reg → Word) {F : Assertion} (hF : F.pcFree) :
    (wlEmptyFrame vals F).pcFree := by
  unfold wlEmptyFrame wlhSregs
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact hF | apply pcFree_sepConj

/-- Machine frame: bytes + out + pass-through owns + user F. -/
private def wlEmptyMachF (secPtr hashPtr : Word)
    (secBytes hashBytes : List (BitVec 8))
    (oldOff oldLen : Word) (F : Assertion) : Assertion :=
  bytesRegion secPtr secBytes ** bytesRegion hashPtr hashBytes **
  (MwLookupOff ↦ₘ oldOff) ** (MwLookupLen ↦ₘ oldLen) **
  regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** F

private theorem wlEmptyMachF_pcFree (secPtr hashPtr : Word)
    (secBytes hashBytes : List (BitVec 8))
    (oldOff oldLen : Word) {F : Assertion} (hF : F.pcFree) :
    (wlEmptyMachF secPtr hashPtr secBytes hashBytes oldOff oldLen F).pcFree := by
  unfold wlEmptyMachF
  repeat' first
    | exact bytesRegion_pcFree _ _ | exact pcFree_memIs | exact pcFree_regOwn
    | exact hF | apply pcFree_sepConj


/-- frameSlotsSaved → stackFree via Own intermediate (8 slots + emp). -/
private theorem frameSlotsSaved_to_stackFree (sp : Word) (vals : Reg → Word) :
    ∀ h, frameSlotsSaved wlhFrame (sp + signExtend12 (-64 : BitVec 12)) vals h →
      stackFree sp 8 h := by
  intro h hs
  have hown : frameSlotsOwn wlhFrame (sp + signExtend12 (-64 : BitVec 12)) h := by
    simp only [frameSlotsSaved, frameSlotsOwn, wlhFrame] at hs ⊢
    -- 8 memIs→memOwn + emp id
    exact (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (fun _ hx => hx))))))))) h hs
  exact (stackFree8_eq_frameSlotsOwn sp).symm ▸ hown

private def machFocusPre (vOld newSp : Word) (vals : Reg → Word)
    (v5 v6 secPtr hashPtr nCalls nLin nLast nMax nMiss : Word) : Assertion :=
  (.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ newSp) ** stackFree newSp 8 **
  wlhSregs vals **
  wlhArgs v5 v6 secPtr hashPtr MwLookupOff MwLookupLen
    nCalls nLin nLast nMax nMiss

private def machFocusPostSf (callerPC newSp : Word) (vals : Reg → Word)
    (hashPtr nCalls nLin nMax nMiss : Word) : Assertion :=
  (.x1 ↦ᵣ (callerPC + 4)) ** (.x2 ↦ᵣ newSp) ** stackFree newSp 8 **
  wlhSregs vals **
  wlhMissOut hashPtr MwLookupOff MwLookupLen nCalls nLin nMax nMiss

/-- Pre reshape: ((x1 ** entry) ** frame) → (machFocusPre ** machF). -/
private theorem pre_generic_to_machine
    (vOld newSp : Word) (vals : Reg → Word)
    (v5 v6 secPtr hashPtr : Word)
    (secBytes hashBytes : List (BitVec 8))
    (oldOff oldLen nCalls nLin nLast nMax nMiss : Word)
    (F0 : Assertion) (h : PartialState)
    (hp : (((.x1 ↦ᵣ vOld) **
        wlCallEntry newSp secPtr (0 : Word) hashPtr oldOff oldLen
          secBytes hashBytes v5 v6
          nCalls nLin nLast nMax nMiss (0 : Word)) **
        wlEmptyFrame vals F0) h) :
    ((machFocusPre vOld newSp vals v5 v6 secPtr hashPtr
        nCalls nLin nLast nMax nMiss) **
      wlEmptyMachF secPtr hashPtr secBytes hashBytes oldOff oldLen F0) h := by
  obtain ⟨eqC, eqW, eqLC, eqLL, eqLM, eqLMi⟩ := cells_eq
  simp only [machFocusPre, wlCallEntry, wlTelemetry, wlEmptyFrame, wlhArgs, wlhSregs,
    wlEmptyMachF, eqC, eqW, eqLC, eqLL, eqLM, eqLMi] at hp ⊢
  xperm_chunked hp


/-- Everything in post except the six concrete temps we drop to owns. -/
private def postDropRest (callerPC newSp : Word) (vals : Reg → Word)
    (hashPtr nCalls nLin nMax nMiss : Word)
    (secPtr : Word) (secBytes hashBytes : List (BitVec 8))
    (oldOff oldLen : Word) (F0 : Assertion) : Assertion :=
  (.x1 ↦ᵣ (callerPC + 4)) ** (.x2 ↦ᵣ newSp) ** stackFree newSp 8 **
  wlhSregs vals ** (.x0 ↦ᵣ (0 : Word)) **
  (.x10 ↦ᵣ (1 : Word)) **
  (CallsLoc ↦ₘ (nCalls + 1)) ** (WidxEnLoc ↦ₘ (0 : Word)) **
  (LinCallsLoc ↦ₘ (nLin + 1)) ** (LinLastLoc ↦ₘ (0 : Word)) **
  (LinMaxLoc ↦ₘ nMax) ** (LinMissLoc ↦ₘ (nMiss + 1)) **
  bytesRegion secPtr secBytes ** bytesRegion hashPtr hashBytes **
  (MwLookupOff ↦ₘ oldOff) ** (MwLookupLen ↦ₘ oldLen) **
  regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** F0

/-- Post reshape after Saved→Free: drop concrete temps to owns. -/
private theorem post_drop_temps
    (callerPC newSp : Word) (vals : Reg → Word)
    (hashPtr : Word) (nCalls nLin nMax nMiss : Word)
    (secPtr : Word) (secBytes hashBytes : List (BitVec 8))
    (oldOff oldLen : Word) (F0 : Assertion) (h : PartialState)
    (hq : ((machFocusPostSf callerPC newSp vals hashPtr nCalls nLin nMax nMiss) **
      wlEmptyMachF secPtr hashPtr secBytes hashBytes oldOff oldLen F0) h) :
    (((.x1 ↦ᵣ (callerPC + 4)) **
        wlCallReturn newSp secPtr hashPtr secBytes hashBytes
          (1 : Word) oldOff oldLen
          (nCalls + 1) (nLin + 1) (0 : Word) nMax (nMiss + 1) (0 : Word)) **
      wlEmptyFrame vals F0) h := by
  obtain ⟨eqC, eqW, eqLC, eqLL, eqLM, eqLMi⟩ := cells_eq
  have hx5 := regIs_implies_regOwn (r := .x5) (v := LinMissLoc)
  have hx6 := regIs_implies_regOwn (r := .x6) (v := nMiss + 1)
  have hx11 := regIs_implies_regOwn (r := .x11) (v := (0 : Word))
  have hx12 := regIs_implies_regOwn (r := .x12) (v := hashPtr)
  have hx13 := regIs_implies_regOwn (r := .x13) (v := MwLookupOff)
  have hx14 := regIs_implies_regOwn (r := .x14) (v := MwLookupLen)
  let rest := postDropRest callerPC newSp vals hashPtr nCalls nLin nMax nMiss
    secPtr secBytes hashBytes oldOff oldLen F0
  -- Front six temps ** rest
  have hq1 :
      ((.x5 ↦ᵣ LinMissLoc) ** (.x6 ↦ᵣ (nMiss + 1)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ hashPtr) **
        (.x13 ↦ᵣ MwLookupOff) ** (.x14 ↦ᵣ MwLookupLen) ** rest) h := by
    simp only [machFocusPostSf, wlhMissOut, wlhSregs, wlEmptyMachF, rest,
      postDropRest, eqC, eqW, eqLC, eqLL, eqLM, eqLMi] at hq ⊢
    xperm_chunked hq
  have hq2 :=
    (sepConj_mono hx5
      (sepConj_mono hx6
      (sepConj_mono hx11
      (sepConj_mono hx12
      (sepConj_mono hx13
      (sepConj_mono hx14
        (fun _ hx => hx))))))) h hq1
  -- owns ** rest → ((x1 ** Return) ** Frame)
  simp only [rest, postDropRest, wlCallReturn, wlTelemetry, wlEmptyFrame, wlhSregs,
    eqC, eqW, eqLC, eqLL, eqLM, eqLMi] at hq2 ⊢
  xperm_chunked hq2

private theorem wl_empty_establishes_shape_at
    (callerPC : Word) (offset : BitVec 21) (vOld newSp : Word)
    (vals : Reg → Word) (F0 : Assertion)
    (v5 v6 secPtr hashPtr : Word)
    (secBytes hashBytes : List (BitVec 8))
    (oldOff oldLen nCalls nLin nLast nMax nMiss : Word)
    (hF0 : F0.pcFree)
    (hvals : vals .x1 = callerPC + 4)
    (halign : ((callerPC + 4) &&& ~~~(1 : Word)) = callerPC + 4)
    (htarget : callerPC + signExtend21 offset = wlhB)
    (hmem : ∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i →
      fullCode a = some i) :
    wlCallWithinShape fullCode callerPC vOld newSp
      secPtr (0 : Word) hashPtr oldOff oldLen secBytes hashBytes
      v5 v6
      nCalls nLin nLast nMax nMiss (0 : Word)
      offset 52
      (wlEmptyFrame vals F0) := by
  refine ⟨wlEmptyFrame_pcFree vals hF0, halign, htarget, hmem, ?htrip⟩
  let machF := wlEmptyMachF secPtr hashPtr secBytes hashBytes oldOff oldLen F0
  have hmach := wlhCallWithin_empty_section fullCode callerPC vOld newSp offset
    vals machF v5 v6 secPtr hashPtr MwLookupOff MwLookupLen
    nCalls nLin nLast nMax nMiss
    (wlEmptyMachF_pcFree _ _ _ _ _ _ hF0) hvals halign htarget hmem wlh_code_in_full
  refine cpsTripleWithin_weaken ?pre ?post hmach
  · intro h hp
    exact pre_generic_to_machine vOld newSp vals v5 v6 secPtr hashPtr
      secBytes hashBytes oldOff oldLen nCalls nLin nLast nMax nMiss F0 h hp
  · intro h hq
    -- Front Saved, convert to stackFree, rebuild focusSf ** machF
    have hqFront :
        ((frameSlotsSaved wlhFrame
            (newSp + signExtend12 (-64 : BitVec 12)) vals) **
          ((.x1 ↦ᵣ (callerPC + 4)) ** (.x2 ↦ᵣ newSp) **
            wlhSregs vals **
            wlhMissOut hashPtr MwLookupOff MwLookupLen nCalls nLin nMax nMiss **
            machF)) h := by
      xperm_chunked hq
    have hqFreeFront :=
      (sepConj_mono (frameSlotsSaved_to_stackFree newSp vals)
        (fun _ hx => hx)) h hqFront
    have hqSf :
        ((machFocusPostSf callerPC newSp vals hashPtr nCalls nLin nMax nMiss) **
          machF) h := by
      simp only [machFocusPostSf] at hqFreeFront ⊢
      xperm_chunked hqFreeFront
    have hqRet := post_drop_temps callerPC newSp vals hashPtr nCalls nLin nMax nMiss
      secPtr secBytes hashBytes oldOff oldLen F0 h hqSf
    refine (sepConj_mono
      (sepConj_mono (fun _ hx => hx)
        (fun (h' : PartialState)
            (hr : wlCallReturn newSp secPtr hashPtr secBytes hashBytes
              (1 : Word) oldOff oldLen
              (nCalls + 1) (nLin + 1) (0 : Word) nMax (nMiss + 1) (0 : Word) h') =>
          show wlCallReturnEx newSp secPtr hashPtr secBytes hashBytes h' from
            ⟨(1 : Word), oldOff, oldLen,
              nCalls + 1, nLin + 1, (0 : Word), nMax, nMiss + 1, (0 : Word), hr⟩))
      (fun _ hx => hx)) h hqRet

/-! ## Public site lemmas -/

theorem root_wl_empty_establishes_shape
    (newSp vOld : Word) (vals : Reg → Word) (F0 : Assertion)
    (v5 v6 secPtr hashPtr : Word)
    (secBytes hashBytes : List (BitVec 8))
    (oldOff oldLen nCalls nLin nLast nMax nMiss : Word)
    (hF0 : F0.pcFree)
    (hvals : vals .x1 = pc 35 + 4) :
    wlCallWithinShape fullCode (pc 35) vOld newSp
      secPtr (0 : Word) hashPtr oldOff oldLen secBytes hashBytes
      v5 v6
      nCalls nLin nLast nMax nMiss (0 : Word)
      rootOff 52
      (wlEmptyFrame vals F0) :=
  wl_empty_establishes_shape_at (pc 35) rootOff vOld newSp vals F0
    v5 v6 secPtr hashPtr secBytes hashBytes oldOff oldLen
    nCalls nLin nLast nMax nMiss hF0 hvals root_ret_align root_target root_jal_mem

theorem branch_wl_empty_establishes_shape
    (newSp vOld : Word) (vals : Reg → Word) (F0 : Assertion)
    (v5 v6 secPtr hashPtr : Word)
    (secBytes hashBytes : List (BitVec 8))
    (oldOff oldLen nCalls nLin nLast nMax nMiss : Word)
    (hF0 : F0.pcFree)
    (hvals : vals .x1 = pc 101 + 4) :
    wlCallWithinShape fullCode (pc 101) vOld newSp
      secPtr (0 : Word) hashPtr oldOff oldLen secBytes hashBytes
      v5 v6
      nCalls nLin nLast nMax nMiss (0 : Word)
      branchOff 52
      (wlEmptyFrame vals F0) :=
  wl_empty_establishes_shape_at (pc 101) branchOff vOld newSp vals F0
    v5 v6 secPtr hashPtr secBytes hashBytes oldOff oldLen
    nCalls nLin nLast nMax nMiss hF0 hvals branch_ret_align branch_target branch_jal_mem

theorem ext_wl_empty_establishes_shape
    (newSp vOld : Word) (vals : Reg → Word) (F0 : Assertion)
    (v5 v6 secPtr hashPtr : Word)
    (secBytes hashBytes : List (BitVec 8))
    (oldOff oldLen nCalls nLin nLast nMax nMiss : Word)
    (hF0 : F0.pcFree)
    (hvals : vals .x1 = pc 210 + 4) :
    wlCallWithinShape fullCode (pc 210) vOld newSp
      secPtr (0 : Word) hashPtr oldOff oldLen secBytes hashBytes
      v5 v6
      nCalls nLin nLast nMax nMiss (0 : Word)
      extOff 52
      (wlEmptyFrame vals F0) :=
  wl_empty_establishes_shape_at (pc 210) extOff vOld newSp vals F0
    v5 v6 secPtr hashPtr secBytes hashBytes oldOff oldLen
    nCalls nLin nLast nMax nMiss hF0 hvals ext_ret_align ext_target ext_jal_mem

end EvmAsm.Codegen.MptWalkSpec
