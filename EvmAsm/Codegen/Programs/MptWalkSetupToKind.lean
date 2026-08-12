/-
  Setup wl ABI framing (#11799 / #12144 half-2).

  `setup_wl_abi_framed` prepares the residual entry ambient (telemetry +
  hop extras). Full `setup_wl_to_kind` compose (ABI-temp drop vs hop own
  x12–14) is deferred — acceptance for #12144 half-2 is empty-section
  discharge of generic `wlCallWithinShape`, not the setup→kind path.
-/

import EvmAsm.Codegen.Programs.MptWalkSetupBody
import EvmAsm.Codegen.Programs.MptWalkResidualChain
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-- Ambient under setup_wl_abi carrying telemetry + hop residual owns. -/
def setupWlAmb (newSp : Word) (ws : WalkSaved)
    (witBase pathPtr pathLenW valOut valOutLen oldOff oldLen raVal : Word)
    (secBytes hashBytes : List (BitVec 8))
    (nCalls nLin nLast nMax nMiss widxEn : Word) (F : Assertion) : Assertion :=
  (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ newSp) ** stackFree newSp 8 **
  (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)) **
  bytesRegion witBase secBytes ** bytesRegion MwLookupHash hashBytes **
  (MwLookupOff ↦ₘ oldOff) ** (MwLookupLen ↦ₘ oldLen) **
  wlTelemetry nCalls nLin nLast nMax nMiss widxEn **
  walkSavedFrame newSp ws **
  (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) **
  (.x20 ↦ᵣ valOut) ** (.x21 ↦ᵣ valOutLen) **
  rootHopResidualExtraOwns **
  regOwn .x22 ** regOwn .x23 ** regOwn .x24 ** F

theorem setupWlAmb_pcFree
    (newSp : Word) (ws : WalkSaved)
    (witBase pathPtr pathLenW valOut valOutLen oldOff oldLen raVal : Word)
    (secBytes hashBytes : List (BitVec 8))
    (nCalls nLin nLast nMax nMiss widxEn : Word)
    (F : Assertion) (hF : F.pcFree) :
    (setupWlAmb newSp ws witBase pathPtr pathLenW valOut valOutLen
      oldOff oldLen raVal secBytes hashBytes
      nCalls nLin nLast nMax nMiss widxEn F).pcFree := by
  unfold setupWlAmb walkSavedFrame wlTelemetry rootHopResidualExtraOwns
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
    (nCalls nLin nLast nMax nMiss widxEn : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (pc 27) (pc 35) fullCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) **
       setupWlAmb newSp ws witBase pathPtr pathLenW valOut valOutLen
         oldOff oldLen raVal secBytes hashBytes
         nCalls nLin nLast nMax nMiss widxEn F)
      ((.x10 ↦ᵣ witBase) ** (.x11 ↦ᵣ witLen) ** (.x12 ↦ᵣ MwLookupHash) **
       (.x13 ↦ᵣ MwLookupOff) ** (.x14 ↦ᵣ MwLookupLen) **
       (.x8 ↦ᵣ witBase) ** (.x9 ↦ᵣ witLen) **
       setupWlAmb newSp ws witBase pathPtr pathLenW valOut valOutLen
         oldOff oldLen raVal secBytes hashBytes
         nCalls nLin nLast nMax nMiss widxEn F) := by
  exact setup_wl_abi v10 v11 v12 v13 v14 witBase witLen
    (setupWlAmb newSp ws witBase pathPtr pathLenW valOut valOutLen
      oldOff oldLen raVal secBytes hashBytes
      nCalls nLin nLast nMax nMiss widxEn F)
    (setupWlAmb_pcFree newSp ws witBase pathPtr pathLenW valOut valOutLen
      oldOff oldLen raVal secBytes hashBytes
      nCalls nLin nLast nMax nMiss widxEn F hF)

end EvmAsm.Codegen.MptWalkSpec
