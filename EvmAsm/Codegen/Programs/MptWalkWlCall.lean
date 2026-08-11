/-
  Residual `witness_lookup_by_hash` callWithin discharge (#11799).

  Does NOT prove the callee. Takes `h_wl : wlCallWithinShape ...` and
  frames it at each walk JAL site (root pc35, branch hop pc101).
  Ext hop pc210 is the same shape when needed.

  Retires when `witness_lookup_by_hash_spec_within` lands and supplies
  the residual hyp via callWithin against that triple.
-/

import EvmAsm.Codegen.Programs.MptWalkResiduals
import EvmAsm.Codegen.Programs.MptWalkSetupBody
import EvmAsm.Codegen.Programs.MptWalkBranchHash
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

private theorem root_wl_jal_target :
    pc 35 + signExtend21
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 140)) =
      WlB := by
  unfold pc walkB WlB; decide

private theorem root_wl_ret_even :
    ((pc 35 + 4) &&& ~~~(1 : Word)) = pc 35 + 4 := by
  unfold pc walkB; decide

private theorem branch_wl_jal_target :
    pc 101 + signExtend21
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 404)) =
      WlB := by
  unfold pc walkB WlB; decide

private theorem branch_wl_ret_even :
    ((pc 101 + 4) &&& ~~~(1 : Word)) = pc 101 + 4 := by
  unfold pc walkB; decide

/-- Walk ambient framed through a residual wl call.
    Does NOT include x0/sp/stackFree — those live in `wlCallEntry` /
    `wlCallReturn` (avoid double-own under sep). -/
def wlSiteFrame (newSp : Word) (ws : WalkSaved)
    (extra : Assertion) : Assertion :=
  walkSavedFrame newSp ws ** extra

theorem wlSiteFrame_pcFree (newSp : Word) (ws : WalkSaved)
    (extra : Assertion) (hE : extra.pcFree) :
    (wlSiteFrame newSp ws extra).pcFree := by
  unfold wlSiteFrame walkSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact hE | apply pcFree_sepConj

/-! ## Root site pc35 -/

/-- Root residual call: discharge via `h_wl`.
    Pre ABI matches `setup_wl_abi` post (a0=sec, a1=len, a2=hash, a3/a4=out). -/
theorem root_wl_call_residual
    (newSp : Word) (ws : WalkSaved)
    (secPtr secLenW : Word)
    (secBytes hashBytes : List (BitVec 8))
    (oldOff oldLen raVal : Word)
    (fuel : Nat) (Fextra : Assertion)
    (h_wl : wlCallWithinShape fullCode (pc 35) raVal newSp
      secPtr secLenW MwLookupHash oldOff oldLen secBytes hashBytes
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 140))
      fuel
      (wlSiteFrame newSp ws Fextra)) :
    cpsTripleWithin (1 + fuel) (pc 35) (pc 35 + 4) fullCode
      (((.x1 ↦ᵣ raVal) **
        wlCallEntry newSp secPtr secLenW MwLookupHash oldOff oldLen
          secBytes hashBytes) **
        wlSiteFrame newSp ws Fextra)
      (((.x1 ↦ᵣ (pc 35 + 4)) **
        wlCallReturnEx newSp secPtr MwLookupHash secBytes hashBytes) **
        wlSiteFrame newSp ws Fextra) := by
  rcases h_wl with ⟨_hF, _hret, _htarget, _hmem, htrip⟩
  exact htrip

/-! ## Branch hop site pc101 -/

theorem branch_wl_call_residual
    (newSp : Word) (ws : WalkSaved)
    (secPtr secLenW : Word)
    (secBytes hashBytes : List (BitVec 8))
    (oldOff oldLen raVal : Word)
    (fuel : Nat) (Fextra : Assertion)
    (h_wl : wlCallWithinShape fullCode (pc 101) raVal newSp
      secPtr secLenW MwLookupHash oldOff oldLen secBytes hashBytes
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 404))
      fuel
      (wlSiteFrame newSp ws Fextra)) :
    cpsTripleWithin (1 + fuel) (pc 101) (pc 101 + 4) fullCode
      (((.x1 ↦ᵣ raVal) **
        wlCallEntry newSp secPtr secLenW MwLookupHash oldOff oldLen
          secBytes hashBytes) **
        wlSiteFrame newSp ws Fextra)
      (((.x1 ↦ᵣ (pc 101 + 4)) **
        wlCallReturnEx newSp secPtr MwLookupHash secBytes hashBytes) **
        wlSiteFrame newSp ws Fextra) := by
  rcases h_wl with ⟨_hF, _hret, _htarget, _hmem, htrip⟩
  exact htrip

/-! ## Ext hop site pc210 -/

private theorem ext_wl_jal_target :
    pc 210 + signExtend21
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 840)) =
      WlB := by
  unfold pc walkB WlB; decide

private theorem ext_wl_ret_even :
    ((pc 210 + 4) &&& ~~~(1 : Word)) = pc 210 + 4 := by
  unfold pc walkB; decide

theorem ext_wl_call_residual
    (newSp : Word) (ws : WalkSaved)
    (secPtr secLenW : Word)
    (secBytes hashBytes : List (BitVec 8))
    (oldOff oldLen raVal : Word)
    (fuel : Nat) (Fextra : Assertion)
    (h_wl : wlCallWithinShape fullCode (pc 210) raVal newSp
      secPtr secLenW MwLookupHash oldOff oldLen secBytes hashBytes
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 840))
      fuel
      (wlSiteFrame newSp ws Fextra)) :
    cpsTripleWithin (1 + fuel) (pc 210) (pc 210 + 4) fullCode
      (((.x1 ↦ᵣ raVal) **
        wlCallEntry newSp secPtr secLenW MwLookupHash oldOff oldLen
          secBytes hashBytes) **
        wlSiteFrame newSp ws Fextra)
      (((.x1 ↦ᵣ (pc 210 + 4)) **
        wlCallReturnEx newSp secPtr MwLookupHash secBytes hashBytes) **
        wlSiteFrame newSp ws Fextra) := by
  rcases h_wl with ⟨_hF, _hret, _htarget, _hmem, htrip⟩
  exact htrip

end EvmAsm.Codegen.MptWalkSpec
