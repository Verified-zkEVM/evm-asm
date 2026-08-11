/-
  Residual `h_wl` callWithin chains (#11799).

  Compose residual wl call (HIT) → hop glue → kind ABI at the three sites
  (root pc35, branch pc101, ext pc210).

  Hit-specialized residual `wlCallWithinShapeHit` is a DEPENDENCY discharge:
  obtain from `wlCallWithinShape` by casing `wlCallReturnEx` and taking the
  status=0 arm with matching off/len. Miss arms stay at whole-routine cases.

  Residual = DEPENDENCY not domain gate (coord 2026-08-11).
-/

import EvmAsm.Codegen.Programs.MptWalkRootHopGlue
import EvmAsm.Codegen.Programs.MptWalkBranchHopGlue
import EvmAsm.Codegen.Programs.MptWalkWlCall
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-- Hit-specialized residual shape: status=0, concrete off/len.
    Discharge from `wlCallWithinShape` by casing Ex return. -/
def wlCallWithinShapeHit (cr : CodeReq) (callerPC vOld sp0 secPtr secLenW hashPtr
    oldOff oldLen nodeOff nodeLen : Word)
    (secBytes hashBytes : List (BitVec 8))
    (offset : BitVec 21) (fuel : Nat) (F : Assertion) : Prop :=
  F.pcFree ∧
  (callerPC + 4 &&& ~~~(1 : Word)) = callerPC + 4 ∧
  callerPC + signExtend21 offset = WlB ∧
  (∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i →
    cr a = some i) ∧
  cpsTripleWithin (1 + fuel) callerPC (callerPC + 4) cr
    (((.x1 ↦ᵣ vOld) ** wlCallEntry sp0 secPtr secLenW hashPtr oldOff oldLen
      secBytes hashBytes) ** F)
    (((.x1 ↦ᵣ (callerPC + 4)) **
      wlHitReturn sp0 secPtr hashPtr nodeOff nodeLen secBytes hashBytes) ** F)

/-! ## Root residual chain -/

/-- Ambient through root residual: path/out + owns for hop + wit regs. -/
def rootWlSiteExtra (witBase witLen pathPtr pathLenW valOut valOutLen : Word)
    (F : Assertion) : Assertion :=
  (.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) **
  (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) **
  (.x20 ↦ᵣ valOut) ** (.x21 ↦ᵣ valOutLen) **
  regOwn .x22 ** regOwn .x23 ** regOwn .x24 ** F

theorem rootWlSiteExtra_pcFree
    (witBase witLen pathPtr pathLenW valOut valOutLen : Word)
    (F : Assertion) (hF : F.pcFree) :
    (rootWlSiteExtra witBase witLen pathPtr pathLenW valOut valOutLen F).pcFree := by
  unfold rootWlSiteExtra
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact hF | apply pcFree_sepConj

/-- Hop ambient after call-post reshape (no x8 — that sits outside F in hop pre). -/
def rootHopAmb (newSp : Word) (ws : WalkSaved)
    (witLen pathPtr pathLenW valOut valOutLen : Word) (F : Assertion) : Assertion :=
  walkSavedFrame newSp ws **
  (.x9 ↦ᵣ witLen) **
  (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) **
  (.x20 ↦ᵣ valOut) ** (.x21 ↦ᵣ valOutLen) ** F

theorem rootHopAmb_pcFree
    (newSp : Word) (ws : WalkSaved)
    (witLen pathPtr pathLenW valOut valOutLen : Word)
    (F : Assertion) (hF : F.pcFree) :
    (rootHopAmb newSp ws witLen pathPtr pathLenW valOut valOutLen F).pcFree := by
  unfold rootHopAmb walkSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact hF | apply pcFree_sepConj

/-- Root hit chain: residual hit @pc35 → kind ABI @pc47.
    Fuel = 1 + wlFuel + 11.
    Call post `((x1**Hit)**Site)` reshaped holds-level into hop pre. -/
theorem root_wl_hit_chain
    (newSp : Word) (ws : WalkSaved)
    (witBase witLen : Word)
    (secBytes hashBytes : List (BitVec 8))
    (pathPtr pathLenW valOut valOutLen oldOff oldLen nodeOff nodeLen raVal : Word)
    (wlFuel : Nat) (F : Assertion) (hF : F.pcFree)
    (h_wl : wlCallWithinShapeHit fullCode (pc 35) raVal newSp
      witBase witLen MwLookupHash oldOff oldLen nodeOff nodeLen
      secBytes hashBytes
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 140))
      wlFuel
      (wlSiteFrame newSp ws
        (rootWlSiteExtra witBase witLen pathPtr pathLenW valOut valOutLen F))) :
    cpsTripleWithin (1 + wlFuel + 11) (pc 35) (pc 47) fullCode
      (((.x1 ↦ᵣ raVal) **
        wlCallEntry newSp witBase witLen MwLookupHash oldOff oldLen
          secBytes hashBytes) **
        wlSiteFrame newSp ws
          (rootWlSiteExtra witBase witLen pathPtr pathLenW valOut valOutLen F))
      ((.x1 ↦ᵣ (pc 36)) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
       rootKindEntry witBase nodeOff nodeLen
         ((.x2 ↦ᵣ newSp) ** stackFree newSp 8 ** rootHopResidualExtraOwns **
          bytesRegion witBase secBytes ** bytesRegion MwLookupHash hashBytes **
          rootHopAmb newSp ws witLen pathPtr pathLenW valOut valOutLen F)) := by
  rcases h_wl with ⟨_hFs, _hret, _htarget, _hmem, hcall⟩
  have hpc : pc 35 + 4 = pc 36 := pc_succ 35
  -- Residual call with exit PC rewritten to pc 36.
  have hcall' : cpsTripleWithin (1 + wlFuel) (pc 35) (pc 36) fullCode
      (((.x1 ↦ᵣ raVal) **
        wlCallEntry newSp witBase witLen MwLookupHash oldOff oldLen
          secBytes hashBytes) **
        wlSiteFrame newSp ws
          (rootWlSiteExtra witBase witLen pathPtr pathLenW valOut valOutLen F))
      (((.x1 ↦ᵣ (pc 36)) **
        wlHitReturn newSp witBase MwLookupHash nodeOff nodeLen
          secBytes hashBytes) **
        wlSiteFrame newSp ws
          (rootWlSiteExtra witBase witLen pathPtr pathLenW valOut valOutLen F)) := by
    simpa [hpc] using hcall
  -- Hop glue at exact hop-pre / hop-post shapes.
  have hhop := root_wl_hit_to_kind newSp witBase witBase nodeOff nodeLen
    secBytes hashBytes
    (rootHopAmb newSp ws witLen pathPtr pathLenW valOut valOutLen F)
    (rootHopAmb_pcFree newSp ws witLen pathPtr pathLenW valOut valOutLen F hF)
  -- Reshape call-post → hop-pre (holds-level).
  have hhop' : cpsTripleWithin 11 (pc 36) (pc 47) fullCode
      (((.x1 ↦ᵣ (pc 36)) **
        wlHitReturn newSp witBase MwLookupHash nodeOff nodeLen
          secBytes hashBytes) **
        wlSiteFrame newSp ws
          (rootWlSiteExtra witBase witLen pathPtr pathLenW valOut valOutLen F))
      ((.x1 ↦ᵣ (pc 36)) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
       rootKindEntry witBase nodeOff nodeLen
         ((.x2 ↦ᵣ newSp) ** stackFree newSp 8 ** rootHopResidualExtraOwns **
          bytesRegion witBase secBytes ** bytesRegion MwLookupHash hashBytes **
          rootHopAmb newSp ws witLen pathPtr pathLenW valOut valOutLen F)) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [wlSiteFrame, rootWlSiteExtra, rootHopAmb, wlHitReturn,
          wlCallReturn, walkSavedFrame] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        simp only [rootKindEntry, rootHopResidualExtraOwns, rootHopAmb,
          walkSavedFrame] at hq ⊢
        xperm_chunked hq)
      hhop
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hcall' hhop'

/-! ## Branch residual chain -/

/-- Ambient through branch residual: path pos + owns for hop. -/
def branchWlSiteExtra (witBase pathPtr pathLenW pathPos : Word)
    (F : Assertion) : Assertion :=
  (.x8 ↦ᵣ witBase) **
  (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pathPos) **
  regOwn .x23 ** regOwn .x24 ** F

theorem branchWlSiteExtra_pcFree
    (witBase pathPtr pathLenW pathPos : Word)
    (F : Assertion) (hF : F.pcFree) :
    (branchWlSiteExtra witBase pathPtr pathLenW pathPos F).pcFree := by
  unfold branchWlSiteExtra
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact hF | apply pcFree_sepConj

/-- Hop ambient after call-post reshape for branch/ext. -/
def branchHopAmb (newSp : Word) (ws : WalkSaved) (witLen : Word)
    (F : Assertion) : Assertion :=
  walkSavedFrame newSp ws ** (.x9 ↦ᵣ witLen) ** F

theorem branchHopAmb_pcFree
    (newSp : Word) (ws : WalkSaved) (witLen : Word)
    (F : Assertion) (hF : F.pcFree) :
    (branchHopAmb newSp ws witLen F).pcFree := by
  unfold branchHopAmb walkSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact hF | apply pcFree_sepConj

/-- Branch hit chain: residual hit @pc101 → kind ABI @pc47. -/
theorem branch_wl_hit_chain
    (newSp : Word) (ws : WalkSaved)
    (witBase witLen : Word)
    (secBytes hashBytes : List (BitVec 8))
    (pathPtr pathLenW pathPos oldOff oldLen nodeOff nodeLen raVal : Word)
    (wlFuel : Nat) (F : Assertion) (hF : F.pcFree)
    (h_wl : wlCallWithinShapeHit fullCode (pc 101) raVal newSp
      witBase witLen MwLookupHash oldOff oldLen nodeOff nodeLen
      secBytes hashBytes
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 404))
      wlFuel
      (wlSiteFrame newSp ws
        (branchWlSiteExtra witBase pathPtr pathLenW pathPos
          ((.x9 ↦ᵣ witLen) ** F)))) :
    cpsTripleWithin (1 + wlFuel + 11) (pc 101) (pc 47) fullCode
      (((.x1 ↦ᵣ raVal) **
        wlCallEntry newSp witBase witLen MwLookupHash oldOff oldLen
          secBytes hashBytes) **
        wlSiteFrame newSp ws
          (branchWlSiteExtra witBase pathPtr pathLenW pathPos
            ((.x9 ↦ᵣ witLen) ** F)))
      ((.x1 ↦ᵣ (pc 102)) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
       branchHopKindEntry witBase nodeOff nodeLen
         ((.x2 ↦ᵣ newSp) ** stackFree newSp 8 ** hopResidualExtraOwns **
          bytesRegion witBase secBytes ** bytesRegion MwLookupHash hashBytes **
          hopPathFrame pathPtr pathLenW pathPos
            (branchHopAmb newSp ws witLen F))) := by
  rcases h_wl with ⟨_hFs, _hret, _htarget, _hmem, hcall⟩
  have hpc : pc 101 + 4 = pc 102 := pc_succ 101
  have hcall' : cpsTripleWithin (1 + wlFuel) (pc 101) (pc 102) fullCode
      (((.x1 ↦ᵣ raVal) **
        wlCallEntry newSp witBase witLen MwLookupHash oldOff oldLen
          secBytes hashBytes) **
        wlSiteFrame newSp ws
          (branchWlSiteExtra witBase pathPtr pathLenW pathPos
            ((.x9 ↦ᵣ witLen) ** F)))
      (((.x1 ↦ᵣ (pc 102)) **
        wlHitReturn newSp witBase MwLookupHash nodeOff nodeLen
          secBytes hashBytes) **
        wlSiteFrame newSp ws
          (branchWlSiteExtra witBase pathPtr pathLenW pathPos
            ((.x9 ↦ᵣ witLen) ** F))) := by
    simpa [hpc] using hcall
  have hhop := branch_wl_hit_to_kind newSp witBase witBase nodeOff nodeLen
    pathPtr pathLenW pathPos secBytes hashBytes
    (branchHopAmb newSp ws witLen F)
    (branchHopAmb_pcFree newSp ws witLen F hF)
  have hhop' : cpsTripleWithin 11 (pc 102) (pc 47) fullCode
      (((.x1 ↦ᵣ (pc 102)) **
        wlHitReturn newSp witBase MwLookupHash nodeOff nodeLen
          secBytes hashBytes) **
        wlSiteFrame newSp ws
          (branchWlSiteExtra witBase pathPtr pathLenW pathPos
            ((.x9 ↦ᵣ witLen) ** F)))
      ((.x1 ↦ᵣ (pc 102)) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
       branchHopKindEntry witBase nodeOff nodeLen
         ((.x2 ↦ᵣ newSp) ** stackFree newSp 8 ** hopResidualExtraOwns **
          bytesRegion witBase secBytes ** bytesRegion MwLookupHash hashBytes **
          hopPathFrame pathPtr pathLenW pathPos
            (branchHopAmb newSp ws witLen F))) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [wlSiteFrame, branchWlSiteExtra, branchHopAmb, hopPathFrame,
          wlHitReturn, wlCallReturn, walkSavedFrame] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        simp only [branchHopKindEntry, hopResidualExtraOwns, hopPathFrame,
          branchHopAmb, walkSavedFrame] at hq ⊢
        xperm_chunked hq)
      hhop
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hcall' hhop'

/-- Ext hit chain: residual hit @pc210 → kind ABI @pc47. -/
theorem ext_wl_hit_chain
    (newSp : Word) (ws : WalkSaved)
    (witBase witLen : Word)
    (secBytes hashBytes : List (BitVec 8))
    (pathPtr pathLenW pathPos oldOff oldLen nodeOff nodeLen raVal : Word)
    (wlFuel : Nat) (F : Assertion) (hF : F.pcFree)
    (h_wl : wlCallWithinShapeHit fullCode (pc 210) raVal newSp
      witBase witLen MwLookupHash oldOff oldLen nodeOff nodeLen
      secBytes hashBytes
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 840))
      wlFuel
      (wlSiteFrame newSp ws
        (branchWlSiteExtra witBase pathPtr pathLenW pathPos
          ((.x9 ↦ᵣ witLen) ** F)))) :
    cpsTripleWithin (1 + wlFuel + 11) (pc 210) (pc 47) fullCode
      (((.x1 ↦ᵣ raVal) **
        wlCallEntry newSp witBase witLen MwLookupHash oldOff oldLen
          secBytes hashBytes) **
        wlSiteFrame newSp ws
          (branchWlSiteExtra witBase pathPtr pathLenW pathPos
            ((.x9 ↦ᵣ witLen) ** F)))
      ((.x1 ↦ᵣ (pc 211)) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
       branchHopKindEntry witBase nodeOff nodeLen
         ((.x2 ↦ᵣ newSp) ** stackFree newSp 8 ** hopResidualExtraOwns **
          bytesRegion witBase secBytes ** bytesRegion MwLookupHash hashBytes **
          hopPathFrame pathPtr pathLenW pathPos
            (branchHopAmb newSp ws witLen F))) := by
  rcases h_wl with ⟨_hFs, _hret, _htarget, _hmem, hcall⟩
  have hpc : pc 210 + 4 = pc 211 := pc_succ 210
  have hcall' : cpsTripleWithin (1 + wlFuel) (pc 210) (pc 211) fullCode
      (((.x1 ↦ᵣ raVal) **
        wlCallEntry newSp witBase witLen MwLookupHash oldOff oldLen
          secBytes hashBytes) **
        wlSiteFrame newSp ws
          (branchWlSiteExtra witBase pathPtr pathLenW pathPos
            ((.x9 ↦ᵣ witLen) ** F)))
      (((.x1 ↦ᵣ (pc 211)) **
        wlHitReturn newSp witBase MwLookupHash nodeOff nodeLen
          secBytes hashBytes) **
        wlSiteFrame newSp ws
          (branchWlSiteExtra witBase pathPtr pathLenW pathPos
            ((.x9 ↦ᵣ witLen) ** F))) := by
    simpa [hpc] using hcall
  have hhop := ext_wl_hit_to_kind newSp witBase witBase nodeOff nodeLen
    pathPtr pathLenW pathPos secBytes hashBytes
    (branchHopAmb newSp ws witLen F)
    (branchHopAmb_pcFree newSp ws witLen F hF)
  have hhop' : cpsTripleWithin 11 (pc 211) (pc 47) fullCode
      (((.x1 ↦ᵣ (pc 211)) **
        wlHitReturn newSp witBase MwLookupHash nodeOff nodeLen
          secBytes hashBytes) **
        wlSiteFrame newSp ws
          (branchWlSiteExtra witBase pathPtr pathLenW pathPos
            ((.x9 ↦ᵣ witLen) ** F)))
      ((.x1 ↦ᵣ (pc 211)) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
       branchHopKindEntry witBase nodeOff nodeLen
         ((.x2 ↦ᵣ newSp) ** stackFree newSp 8 ** hopResidualExtraOwns **
          bytesRegion witBase secBytes ** bytesRegion MwLookupHash hashBytes **
          hopPathFrame pathPtr pathLenW pathPos
            (branchHopAmb newSp ws witLen F))) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [wlSiteFrame, branchWlSiteExtra, branchHopAmb, hopPathFrame,
          wlHitReturn, wlCallReturn, walkSavedFrame] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        simp only [branchHopKindEntry, hopResidualExtraOwns, hopPathFrame,
          branchHopAmb, walkSavedFrame] at hq ⊢
        xperm_chunked hq)
      hhop
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hcall' hhop'

end EvmAsm.Codegen.MptWalkSpec
