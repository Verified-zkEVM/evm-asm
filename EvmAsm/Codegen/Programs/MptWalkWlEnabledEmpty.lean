/-
  MptWalkWlEnabledEmpty — enable=1 empty-miss residual discharge at walk sites.

  PRODUCTION empty-miss residual (`wlCallWithinShapeEn`) is the ambient of
  `wlhCallWithin_enabled_empty` (fuel 1+87, stackFree 16). Three walk sites
  (root pc35, branch pc101, ext pc210) establish it under walk `fullCode`
  (which already unions enableFullCode via Machine).

  Domain: widx_enabled=1, widx_count=0, section_len=0 — REACHABLE (build empty
  section succeeds with enable=1). Hit residual still DEPENDENCY.

  LEGACY enable=0: MptWalkWlEmpty (linear empty_section) kept for the
  pre-index path; not used at production walk ambient after #12183.
-/
import EvmAsm.Codegen.Programs.MptWalkMachine
import EvmAsm.Codegen.Programs.MptWalkResiduals
import EvmAsm.Codegen.Programs.WitnessLookupByHashEnabledWrap
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Codegen
open EvmAsm.Codegen.WitnessLookupByHashSpec
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec
open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

set_option maxRecDepth 8000

private theorem root_en_jal_target :
    pc 35 + signExtend21
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 140)) =
      WlB := by
  unfold pc walkB WlB; decide

private theorem branch_en_jal_target :
    pc 101 + signExtend21
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 404)) =
      WlB := by
  unfold pc walkB WlB; decide

private theorem ext_en_jal_target :
    pc 210 + signExtend21
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 840)) =
      WlB := by
  unfold pc walkB WlB; decide

/-- Thin apply of `wlCallWithinShapeEn_of_callWithin` +
    `enableFull_in_walk_fullCode` at an arbitrary walk JAL site. -/
theorem wl_enabled_empty_establishes_shape_at
    (callPc : Word) (offset : BitVec 21)
    (vOld sp0 : Word) (vals : Reg → Word) (F : Assertion)
    (v5 v6 secPtr hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (hF : F.pcFree)
    (hvals : vals .x1 = callPc + 4)
    (halign : ((callPc + 4) &&& ~~~(1 : Word)) = callPc + 4)
    (htarget : callPc + signExtend21 offset = WlB)
    (hmem : ∀ a i, CodeReq.singleton callPc (.JAL .x1 offset) a = some i →
      fullCode a = some i) :
    wlCallWithinShapeEn fullCode callPc vOld sp0 vals
      v5 v6 secPtr hashPtr outOff outLen
      nCalls nIdx nMiss nLin nLast nMax nLinMiss offset F := by
  refine wlCallWithinShapeEn_of_callWithin fullCode callPc vOld sp0 offset vals F
    v5 v6 secPtr hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss
    hF hvals (by simpa using halign) htarget hmem ?hcode
  intro a i ha
  exact enableFull_in_walk_fullCode a i ha

theorem root_wl_enabled_empty_establishes_shape
    (vOld sp0 : Word) (vals : Reg → Word) (F : Assertion)
    (v5 v6 secPtr hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (hF : F.pcFree)
    (hvals : vals .x1 = pc 35 + 4)
    (halign : ((pc 35 + 4) &&& ~~~(1 : Word)) = pc 35 + 4) :
    wlCallWithinShapeEn fullCode (pc 35) vOld sp0 vals
      v5 v6 secPtr hashPtr outOff outLen
      nCalls nIdx nMiss nLin nLast nMax nLinMiss
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 140)) F := by
  refine wl_enabled_empty_establishes_shape_at (pc 35)
    (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 140))
    vOld sp0 vals F v5 v6 secPtr hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss hF hvals
    (by simpa using halign) root_en_jal_target ?hm
  intro a i ha
  exact walkMem (pc 35) 35
    (.JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 140)))
    (by decide) (by unfold pc walkB; decide) (by decide) a i ha

theorem branch_wl_enabled_empty_establishes_shape
    (vOld sp0 : Word) (vals : Reg → Word) (F : Assertion)
    (v5 v6 secPtr hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (hF : F.pcFree)
    (hvals : vals .x1 = pc 101 + 4)
    (halign : ((pc 101 + 4) &&& ~~~(1 : Word)) = pc 101 + 4) :
    wlCallWithinShapeEn fullCode (pc 101) vOld sp0 vals
      v5 v6 secPtr hashPtr outOff outLen
      nCalls nIdx nMiss nLin nLast nMax nLinMiss
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 404)) F := by
  refine wl_enabled_empty_establishes_shape_at (pc 101)
    (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 404))
    vOld sp0 vals F v5 v6 secPtr hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss hF hvals
    (by simpa using halign) branch_en_jal_target ?hm
  intro a i ha
  exact walkMem (pc 101) 101
    (.JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 404)))
    (by decide) (by unfold pc walkB; decide) (by decide) a i ha

theorem ext_wl_enabled_empty_establishes_shape
    (vOld sp0 : Word) (vals : Reg → Word) (F : Assertion)
    (v5 v6 secPtr hashPtr outOff outLen : Word)
    (nCalls nIdx nMiss nLin nLast nMax nLinMiss : Word)
    (hF : F.pcFree)
    (hvals : vals .x1 = pc 210 + 4)
    (halign : ((pc 210 + 4) &&& ~~~(1 : Word)) = pc 210 + 4) :
    wlCallWithinShapeEn fullCode (pc 210) vOld sp0 vals
      v5 v6 secPtr hashPtr outOff outLen
      nCalls nIdx nMiss nLin nLast nMax nLinMiss
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 840)) F := by
  refine wl_enabled_empty_establishes_shape_at (pc 210)
    (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 840))
    vOld sp0 vals F v5 v6 secPtr hashPtr outOff outLen
    nCalls nIdx nMiss nLin nLast nMax nLinMiss hF hvals
    (by simpa using halign) ext_en_jal_target ?hm
  intro a i ha
  exact walkMem (pc 210) 210
    (.JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 840)))
    (by decide) (by unfold pc walkB; decide) (by decide) a i ha

end EvmAsm.Codegen.MptWalkSpec
