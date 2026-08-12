/-
  Glue residual root `witness_lookup` hit post → RootResolve → kind ABI (#11799).

  Residual `wlCallReturn` owns x5/x6/x7/x11-14/x28-31 but not x22/x23/x24.
  Root hop needs those owned (unpinned across residual) plus x8=witBase.
-/

import EvmAsm.Codegen.Programs.MptWalkRootResolve
import EvmAsm.Codegen.Programs.MptWalkResiduals
import EvmAsm.Codegen.Programs.MptWalkBranchHop
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-- Scratch owns for root hop (residual + ambient x22/x23/x24). -/
def rootHopScratchOwns : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x11 **
  regOwn .x22 ** regOwn .x23 ** regOwn .x24

theorem rootHopScratchOwns_pcFree : rootHopScratchOwns.pcFree := by
  unfold rootHopScratchOwns
  repeat' first | exact pcFree_regOwn | apply pcFree_sepConj

/-- Peel six trailing owns into rootHopScratchOwns. -/
theorem of_forall_rootHopScratch
    {n : Nat} {entry exit : Word} {cr : CodeReq} {P Q : Assertion}
    (h : ∀ v5 v6 v11 v22 v23 v24 : Word,
      cpsTripleWithin n entry exit cr
        ((((((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) ** (.x11 ↦ᵣ v11)) **
          (.x22 ↦ᵣ v22)) ** (.x23 ↦ᵣ v23)) ** (.x24 ↦ᵣ v24)) Q) :
    cpsTripleWithin n entry exit cr (P ** rootHopScratchOwns) Q := by
  unfold rootHopScratchOwns
  have h1 : ∀ v5 v6 v11 v22 v23,
      cpsTripleWithin n entry exit cr
        ((((((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) ** (.x11 ↦ᵣ v11)) **
          (.x22 ↦ᵣ v22)) ** (.x23 ↦ᵣ v23)) ** regOwn .x24) Q :=
    fun v5 v6 v11 v22 v23 =>
      cpsTripleWithin_of_forall_regIs_to_regOwn (fun v24 => h v5 v6 v11 v22 v23 v24)
  have h2 : ∀ v5 v6 v11 v22,
      cpsTripleWithin n entry exit cr
        (((((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) ** (.x11 ↦ᵣ v11)) **
          (.x22 ↦ᵣ v22)) ** regOwn .x23 ** regOwn .x24) Q := by
    intro v5 v6 v11 v22
    have hy : ∀ v23,
        cpsTripleWithin n entry exit cr
          ((((((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) ** (.x11 ↦ᵣ v11)) **
            (.x22 ↦ᵣ v22)) ** regOwn .x24) ** (.x23 ↦ᵣ v23)) Q :=
      fun v23 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
          (h1 v5 v6 v11 v22 v23)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn hy)
  have h3 : ∀ v5 v6 v11,
      cpsTripleWithin n entry exit cr
        ((((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) ** (.x11 ↦ᵣ v11)) **
          regOwn .x22 ** regOwn .x23 ** regOwn .x24) Q := by
    intro v5 v6 v11
    have hy : ∀ v22,
        cpsTripleWithin n entry exit cr
          (((((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) ** (.x11 ↦ᵣ v11)) **
            regOwn .x23 ** regOwn .x24) ** (.x22 ↦ᵣ v22)) Q :=
      fun v22 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
          (h2 v5 v6 v11 v22)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn hy)
  have h4 : ∀ v5 v6,
      cpsTripleWithin n entry exit cr
        (((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) **
          regOwn .x11 ** regOwn .x22 ** regOwn .x23 ** regOwn .x24) Q := by
    intro v5 v6
    have hy : ∀ v11,
        cpsTripleWithin n entry exit cr
          ((((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) **
            regOwn .x22 ** regOwn .x23 ** regOwn .x24) ** (.x11 ↦ᵣ v11)) Q :=
      fun v11 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
          (h3 v5 v6 v11)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn hy)
  have h5 : ∀ v5,
      cpsTripleWithin n entry exit cr
        ((P ** (.x5 ↦ᵣ v5)) **
          regOwn .x6 ** regOwn .x11 ** regOwn .x22 ** regOwn .x23 **
          regOwn .x24) Q := by
    intro v5
    have hy : ∀ v6,
        cpsTripleWithin n entry exit cr
          (((P ** (.x5 ↦ᵣ v5)) **
            regOwn .x11 ** regOwn .x22 ** regOwn .x23 ** regOwn .x24) **
            (.x6 ↦ᵣ v6)) Q :=
      fun v6 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
          (h4 v5 v6)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn hy)
  have h6 :
      cpsTripleWithin n entry exit cr
        (P ** regOwn .x5 ** regOwn .x6 ** regOwn .x11 ** regOwn .x22 **
          regOwn .x23 ** regOwn .x24) Q := by
    have hy : ∀ v5,
        cpsTripleWithin n entry exit cr
          ((P ** regOwn .x6 ** regOwn .x11 ** regOwn .x22 ** regOwn .x23 **
            regOwn .x24) ** (.x5 ↦ᵣ v5)) Q :=
      fun v5 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
          (h5 v5)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn hy)
  exact h6

/-- Pass-through owns NOT in wlCallReturn (return already owns x5/x6/x11–14). -/
def rootHopResidualExtraOwns : Assertion :=
  regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

/-- From residual hit post at pc36 through root resolve to kind ABI at pc47.
    Fuel 11. Ambient supplies rootHopResidualExtraOwns (x7/x28–31) + own x22/x23/x24.
    Return already owns x5/x6/x11–14. -/
theorem root_wl_hit_to_kind
    (sp0 secPtr witBase nodeOff nodeLen : Word)
    (secBytes hashBytes : List (BitVec 8))
    (nCalls nLin nLast nMax nMiss widxEn : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 11 (pc 36) (pc 47) fullCode
      ((.x1 ↦ᵣ (pc 36)) **
       wlHitReturn sp0 secPtr MwLookupHash nodeOff nodeLen secBytes hashBytes
         nCalls nLin nLast nMax nMiss widxEn **
       rootHopResidualExtraOwns **
       regOwn .x22 ** regOwn .x23 ** regOwn .x24 **
       (.x8 ↦ᵣ witBase) ** F)
      ((.x1 ↦ᵣ (pc 36)) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
       rootKindEntry witBase nodeOff nodeLen
         ((.x2 ↦ᵣ sp0) ** stackFree sp0 8 ** rootHopResidualExtraOwns **
          regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          bytesRegion secPtr secBytes ** bytesRegion MwLookupHash hashBytes **
          wlTelemetry nCalls nLin nLast nMax nMiss widxEn ** F)) := by
  have hown : cpsTripleWithin 11 (pc 36) (pc 47) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       rootHopScratchOwns **
       (.x8 ↦ᵣ witBase) **
       (MwLookupOff ↦ₘ nodeOff) ** (MwLookupLen ↦ₘ nodeLen) **
       ((.x1 ↦ᵣ (pc 36)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
        rootHopResidualExtraOwns **
        regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        bytesRegion secPtr secBytes ** bytesRegion MwLookupHash hashBytes ** wlTelemetry nCalls nLin nLast nMax nMiss widxEn ** F))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
       rootKindEntry witBase nodeOff nodeLen
         ((.x1 ↦ᵣ (pc 36)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
          rootHopResidualExtraOwns **
          regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          bytesRegion secPtr secBytes ** bytesRegion MwLookupHash hashBytes **
          wlTelemetry nCalls nLin nLast nMax nMiss widxEn ** F)) := by
    let P : Assertion :=
      (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x8 ↦ᵣ witBase) **
      (MwLookupOff ↦ₘ nodeOff) ** (MwLookupLen ↦ₘ nodeLen) **
      ((.x1 ↦ᵣ (pc 36)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
       rootHopResidualExtraOwns **
       regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
       bytesRegion secPtr secBytes ** bytesRegion MwLookupHash hashBytes ** wlTelemetry nCalls nLin nLast nMax nMiss widxEn ** F)
    let Q : Assertion :=
      (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
      rootKindEntry witBase nodeOff nodeLen
        ((.x1 ↦ᵣ (pc 36)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
         rootHopResidualExtraOwns **
         regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
         bytesRegion secPtr secBytes ** bytesRegion MwLookupHash hashBytes ** wlTelemetry nCalls nLin nLast nMax nMiss widxEn ** F)
    have hconc : ∀ v5 v6 v11 v22 v23 v24 : Word,
        cpsTripleWithin 11 (pc 36) (pc 47) fullCode
          ((((((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) ** (.x11 ↦ᵣ v11)) **
            (.x22 ↦ᵣ v22)) ** (.x23 ↦ᵣ v23)) ** (.x24 ↦ᵣ v24)) Q := by
      intro v5 v6 v11 v22 v23 v24
      have h := root_after_lookup_ok_to_kind v5 v6 v11 v22 v23 v24 nodeOff nodeLen
        witBase
        ((.x1 ↦ᵣ (pc 36)) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
         rootHopResidualExtraOwns **
         regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
         bytesRegion secPtr secBytes ** bytesRegion MwLookupHash hashBytes ** wlTelemetry nCalls nLin nLast nMax nMiss widxEn ** F)
        (by
          unfold rootHopResidualExtraOwns wlTelemetry
          repeat' first
            | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
            | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
            | exact hF | apply pcFree_sepConj)
      exact cpsTripleWithin_weaken
        (fun _ hp => by simp only [P] at hp ⊢; xperm_chunked hp)
        (fun _ hq => by simp only [Q, rootKindEntry] at hq ⊢; xperm_chunked hq) h
    have hpeel := of_forall_rootHopScratch hconc
    exact cpsTripleWithin_weaken
      (fun _ hp => by simp only [P, rootHopScratchOwns] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [Q] at hq ⊢; exact hq) hpeel
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [wlHitReturn, wlCallReturn, rootHopScratchOwns,
        rootHopResidualExtraOwns, wlTelemetry] at hp ⊢
      xperm_chunked hp)
    (fun _ hq => by
      simp only [rootKindEntry, rootHopResidualExtraOwns, wlTelemetry] at hq ⊢
      xperm_chunked hq)
    hown

end EvmAsm.Codegen.MptWalkSpec
