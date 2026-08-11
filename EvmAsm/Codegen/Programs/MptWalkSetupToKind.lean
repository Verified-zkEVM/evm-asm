/-
  Setup wl ABI → residual hit chain → kind ABI (#11799).

  Composes `setup_wl_abi` (pc27→35) with `root_wl_hit_chain` (pc35→47)
  under hit-specialized residual `h_wl : wlCallWithinShapeHit`.
-/

import EvmAsm.Codegen.Programs.MptWalkSetupBody
import EvmAsm.Codegen.Programs.MptWalkResidualChain
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-- Ambient under setup_wl_abi that becomes the residual site frame + entry. -/
def setupWlAmb (newSp : Word) (ws : WalkSaved)
    (witBase pathPtr pathLenW valOut valOutLen oldOff oldLen raVal : Word)
    (secBytes hashBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ newSp) ** stackFree newSp 8 **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion witBase secBytes ** bytesRegion MwLookupHash hashBytes **
  (MwLookupOff ↦ₘ oldOff) ** (MwLookupLen ↦ₘ oldLen) **
  walkSavedFrame newSp ws **
  (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) **
  (.x20 ↦ᵣ valOut) ** (.x21 ↦ᵣ valOutLen) **
  regOwn .x22 ** regOwn .x23 ** regOwn .x24 ** F

theorem setupWlAmb_pcFree
    (newSp : Word) (ws : WalkSaved)
    (witBase pathPtr pathLenW valOut valOutLen oldOff oldLen raVal : Word)
    (secBytes hashBytes : List (BitVec 8)) (F : Assertion) (hF : F.pcFree) :
    (setupWlAmb newSp ws witBase pathPtr pathLenW valOut valOutLen
      oldOff oldLen raVal secBytes hashBytes F).pcFree := by
  unfold setupWlAmb walkSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
    | exact hF | apply pcFree_sepConj

/-- setup_wl_abi framed under setupWlAmb. Fuel 8. -/
theorem setup_wl_abi_framed
    (newSp : Word) (ws : WalkSaved)
    (v10 v11 v12 v13 v14 witBase witLen pathPtr pathLenW valOut valOutLen
      oldOff oldLen raVal : Word)
    (secBytes hashBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (pc 27) (pc 35) fullCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) **
       setupWlAmb newSp ws witBase pathPtr pathLenW valOut valOutLen
         oldOff oldLen raVal secBytes hashBytes F)
      ((.x10 ↦ᵣ witBase) ** (.x11 ↦ᵣ witLen) ** (.x12 ↦ᵣ MwLookupHash) **
       (.x13 ↦ᵣ MwLookupOff) ** (.x14 ↦ᵣ MwLookupLen) **
       (.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) **
       setupWlAmb newSp ws witBase pathPtr pathLenW valOut valOutLen
         oldOff oldLen raVal secBytes hashBytes F) := by
  have h := setup_wl_abi v10 v11 v12 v13 v14 witBase witLen
    (setupWlAmb newSp ws witBase pathPtr pathLenW valOut valOutLen
      oldOff oldLen raVal secBytes hashBytes F)
    (setupWlAmb_pcFree newSp ws witBase pathPtr pathLenW valOut valOutLen
      oldOff oldLen raVal secBytes hashBytes F hF)
  exact h

/-- Reshape setup_wl_abi post → residual chain pre. -/
theorem setup_post_to_chain_pre
    (newSp : Word) (ws : WalkSaved)
    (witBase witLen pathPtr pathLenW valOut valOutLen oldOff oldLen raVal : Word)
    (secBytes hashBytes : List (BitVec 8)) (F : Assertion)
    (h : PartialState)
    (hp : ((.x10 ↦ᵣ witBase) ** (.x11 ↦ᵣ witLen) ** (.x12 ↦ᵣ MwLookupHash) **
      (.x13 ↦ᵣ MwLookupOff) ** (.x14 ↦ᵣ MwLookupLen) **
      (.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) **
      setupWlAmb newSp ws witBase pathPtr pathLenW valOut valOutLen
        oldOff oldLen raVal secBytes hashBytes F) h) :
    (((.x1 ↦ᵣ raVal) **
      wlCallEntry newSp witBase witLen MwLookupHash oldOff oldLen
        secBytes hashBytes) **
      wlSiteFrame newSp ws
        (rootWlSiteExtra witBase witLen pathPtr pathLenW valOut valOutLen F)) h := by
  simp only [setupWlAmb, wlCallEntry, wlSiteFrame, rootWlSiteExtra,
    walkSavedFrame] at hp ⊢
  xperm_chunked hp

/-- Setup wl ABI → residual hit → kind ABI. Fuel 8 + (1 + wlFuel + 11). -/
theorem setup_wl_to_kind
    (newSp : Word) (ws : WalkSaved)
    (v10 v11 v12 v13 v14 witBase witLen : Word)
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
    cpsTripleWithin (8 + (1 + wlFuel + 11)) (pc 27) (pc 47) fullCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) **
       setupWlAmb newSp ws witBase pathPtr pathLenW valOut valOutLen
         oldOff oldLen raVal secBytes hashBytes F)
      ((.x1 ↦ᵣ (pc 36)) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
       rootKindEntry witBase nodeOff nodeLen
         ((.x2 ↦ᵣ newSp) ** stackFree newSp 8 ** rootHopResidualExtraOwns **
          bytesRegion witBase secBytes ** bytesRegion MwLookupHash hashBytes **
          rootHopAmb newSp ws witLen pathPtr pathLenW valOut valOutLen F)) := by
  have hsetup := setup_wl_abi_framed newSp ws v10 v11 v12 v13 v14 witBase witLen
    pathPtr pathLenW valOut valOutLen oldOff oldLen raVal secBytes hashBytes F hF
  have hchain := root_wl_hit_chain newSp ws witBase witLen secBytes hashBytes
    pathPtr pathLenW valOut valOutLen oldOff oldLen nodeOff nodeLen raVal
    wlFuel F hF h_wl
  have hchain' := cpsTripleWithin_weaken
    (fun h hp => setup_post_to_chain_pre newSp ws witBase witLen pathPtr pathLenW
      valOut valOutLen oldOff oldLen raVal secBytes hashBytes F h hp)
    (fun _ hq => hq)
    hchain
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hsetup hchain'

end EvmAsm.Codegen.MptWalkSpec
