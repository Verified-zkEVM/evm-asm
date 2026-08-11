/-
  Glue residual `witness_lookup` hit post → hop → kind ABI (#11799).

  Residual `wlCallReturn` owns x5/x6/x7/x11-14/x28-31 but not x23/x24.
  Hop needs hopScratchOwns = own x5/x6/x11/x23/x24; so ambient supplies
  own x23/x24 (unpinned across residual).
-/

import EvmAsm.Codegen.Programs.MptWalkExtHop
import EvmAsm.Codegen.Programs.MptWalkResiduals
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-- Path ambient preserved across hop. -/
def hopPathFrame (pathPtr pathLenW pathPos : Word) (F : Assertion) : Assertion :=
  (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pathPos) ** F

/-- Residual owns not in hopScratchOwns. -/
def hopResidualExtraOwns : Assertion :=
  regOwn .x7 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

/-- From residual hit post at pc102 through hop to kind ABI at pc47. Fuel 11.
    Requires ambient own x23/x24 (residual does not pin them). -/
theorem branch_wl_hit_to_kind
    (sp0 secPtr witBase nodeOff nodeLen pathPtr pathLenW pathPos : Word)
    (secBytes hashBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 11 (pc 102) (pc 47) fullCode
      ((.x1 ↦ᵣ (pc 102)) **
       wlHitReturn sp0 secPtr MwLookupHash nodeOff nodeLen secBytes hashBytes **
       regOwn .x23 ** regOwn .x24 **
       (.x8 ↦ᵣ witBase) **
       hopPathFrame pathPtr pathLenW pathPos F)
      ((.x1 ↦ᵣ (pc 102)) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
       branchHopKindEntry witBase nodeOff nodeLen
         ((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** hopResidualExtraOwns **
          bytesRegion secPtr secBytes ** bytesRegion MwLookupHash hashBytes **
          hopPathFrame pathPtr pathLenW pathPos F)) := by
  have hhop := branch_after_lookup_ok_to_kind nodeOff nodeLen witBase
    ((.x1 ↦ᵣ (pc 102)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
     hopResidualExtraOwns **
     bytesRegion secPtr secBytes ** bytesRegion MwLookupHash hashBytes **
     hopPathFrame pathPtr pathLenW pathPos F)
    (by
      unfold hopPathFrame hopResidualExtraOwns
      repeat' first
        | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
        | exact hF | apply pcFree_sepConj)
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [wlHitReturn, wlCallReturn, hopPathFrame, hopScratchOwns,
        hopResidualExtraOwns] at hp ⊢
      xperm_chunked hp)
    (fun _ hq => by
      simp only [hopPathFrame, hopResidualExtraOwns, branchHopKindEntry] at hq ⊢
      xperm_chunked hq)
    hhop

/-- Ext hop hit → kind. -/
theorem ext_wl_hit_to_kind
    (sp0 secPtr witBase nodeOff nodeLen pathPtr pathLenW pathPos : Word)
    (secBytes hashBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 11 (pc 211) (pc 47) fullCode
      ((.x1 ↦ᵣ (pc 211)) **
       wlHitReturn sp0 secPtr MwLookupHash nodeOff nodeLen secBytes hashBytes **
       regOwn .x23 ** regOwn .x24 **
       (.x8 ↦ᵣ witBase) **
       hopPathFrame pathPtr pathLenW pathPos F)
      ((.x1 ↦ᵣ (pc 211)) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
       branchHopKindEntry witBase nodeOff nodeLen
         ((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** hopResidualExtraOwns **
          bytesRegion secPtr secBytes ** bytesRegion MwLookupHash hashBytes **
          hopPathFrame pathPtr pathLenW pathPos F)) := by
  have hhop := ext_after_lookup_ok_to_kind nodeOff nodeLen witBase
    ((.x1 ↦ᵣ (pc 211)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
     hopResidualExtraOwns **
     bytesRegion secPtr secBytes ** bytesRegion MwLookupHash hashBytes **
     hopPathFrame pathPtr pathLenW pathPos F)
    (by
      unfold hopPathFrame hopResidualExtraOwns
      repeat' first
        | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
        | exact hF | apply pcFree_sepConj)
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [wlHitReturn, wlCallReturn, hopPathFrame, hopScratchOwns,
        hopResidualExtraOwns] at hp ⊢
      xperm_chunked hp)
    (fun _ hq => by
      simp only [hopPathFrame, hopResidualExtraOwns, branchHopKindEntry] at hq ⊢
      xperm_chunked hq)
    hhop

end EvmAsm.Codegen.MptWalkSpec
