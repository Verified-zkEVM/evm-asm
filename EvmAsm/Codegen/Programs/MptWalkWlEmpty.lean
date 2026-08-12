/-
  Empty-section discharge of the three `mpt_walk` → `witness_lookup_by_hash`
  call sites (#12144).

  ## Domain (SAY SO)

  The only whole-routine machine triple available today is
  `witness_lookup_by_hash_spec_within_empty_section`:
  `section_len = 0` and `widx_enabled = 0` (guaranteed miss, `a0 = 1`).
  These three lemmas therefore establish callWithin **only on that domain**.

  Hit residual (`wlCallWithinShapeHit` / hop chains) remains a DEPENDENCY
  until a hit-domain triple lands — not silently absorbed into this gate.

  ## What was fixed

  1. `fullCode` now includes `wlhCr` (`MptWalkMachine.wlhCalleeMem`) —
     Blocker 1 of `WitnessLookupByHashSpec` is gone.
  2. Ambient carries the six telemetry cells via `wlhArgs`/`wlhMissOut` —
     Blocker 2 repaired at these sites (same shape as
     `wlhCallWithin_empty_section`).

  Each lemma **proves** the callWithin by applying the machine triple;
  it does not take an unsatisfiable free `h_wl`.

  ## Consumers

  `root_wl_call_empty_section` is referenced from Spec/docs. Branch/ext twins
  are staged for the same obligation inventory (same shape, different PC);
  existence-without-use is intentional staging, not a second vacuous residual.
  Vacuous `*_wl_call_residual` lemmas deleted from MptWalkWlCall (#12152 fix).
-/

import EvmAsm.Codegen.Programs.MptWalkWlCall
import EvmAsm.Codegen.Programs.WitnessLookupByHashSpec
import EvmAsm.Codegen.GuestAddrs

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

/-- `wlhCr` (Spec) and `wlhCr` (Machine) agree — both `ofProg` of the same
    linked program — so `wlhCalleeMem` discharges Spec's `hcode`. -/
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

/-! ## Three sites — empty-section miss via machine triple -/

/-- Root site pc35 (`mpt_walk+140`): empty-section miss. -/
theorem root_wl_call_empty_section
    (newSp vOld : Word) (vals : Reg → Word) (F : Assertion)
    (v5 v6 secPtr hashPtr outOffP outLenP
      nCalls nLin nLast nMax nMiss : Word)
    (hF : F.pcFree)
    (hvals : vals .x1 = pc 35 + 4) :
    cpsTripleWithin (1 + 52) (pc 35) (pc 35 + 4) fullCode
      ((((.x1 : Reg) ↦ᵣ vOld) ** ((.x2 : Reg) ↦ᵣ newSp) ** stackFree newSp 8 **
        wlhSregs vals **
        wlhArgs v5 v6 secPtr hashPtr outOffP outLenP
          nCalls nLin nLast nMax nMiss) ** F)
      ((((.x1 : Reg) ↦ᵣ (pc 35 + 4)) ** ((.x2 : Reg) ↦ᵣ newSp) **
        frameSlotsSaved wlhFrame (newSp + signExtend12 (-64 : BitVec 12)) vals **
        wlhSregs vals **
        wlhMissOut hashPtr outOffP outLenP nCalls nLin nMax nMiss) ** F) :=
  wlhCallWithin_empty_section fullCode (pc 35) vOld newSp rootOff vals F
    v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss
    hF hvals root_ret_align root_target root_jal_mem wlh_code_in_full

/-- Branch hop site pc101 (`mpt_walk+404`): empty-section miss. -/
theorem branch_wl_call_empty_section
    (newSp vOld : Word) (vals : Reg → Word) (F : Assertion)
    (v5 v6 secPtr hashPtr outOffP outLenP
      nCalls nLin nLast nMax nMiss : Word)
    (hF : F.pcFree)
    (hvals : vals .x1 = pc 101 + 4) :
    cpsTripleWithin (1 + 52) (pc 101) (pc 101 + 4) fullCode
      ((((.x1 : Reg) ↦ᵣ vOld) ** ((.x2 : Reg) ↦ᵣ newSp) ** stackFree newSp 8 **
        wlhSregs vals **
        wlhArgs v5 v6 secPtr hashPtr outOffP outLenP
          nCalls nLin nLast nMax nMiss) ** F)
      ((((.x1 : Reg) ↦ᵣ (pc 101 + 4)) ** ((.x2 : Reg) ↦ᵣ newSp) **
        frameSlotsSaved wlhFrame (newSp + signExtend12 (-64 : BitVec 12)) vals **
        wlhSregs vals **
        wlhMissOut hashPtr outOffP outLenP nCalls nLin nMax nMiss) ** F) :=
  wlhCallWithin_empty_section fullCode (pc 101) vOld newSp branchOff vals F
    v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss
    hF hvals branch_ret_align branch_target branch_jal_mem wlh_code_in_full

/-- Ext hop site pc210 (`mpt_walk+840`): empty-section miss. -/
theorem ext_wl_call_empty_section
    (newSp vOld : Word) (vals : Reg → Word) (F : Assertion)
    (v5 v6 secPtr hashPtr outOffP outLenP
      nCalls nLin nLast nMax nMiss : Word)
    (hF : F.pcFree)
    (hvals : vals .x1 = pc 210 + 4) :
    cpsTripleWithin (1 + 52) (pc 210) (pc 210 + 4) fullCode
      ((((.x1 : Reg) ↦ᵣ vOld) ** ((.x2 : Reg) ↦ᵣ newSp) ** stackFree newSp 8 **
        wlhSregs vals **
        wlhArgs v5 v6 secPtr hashPtr outOffP outLenP
          nCalls nLin nLast nMax nMiss) ** F)
      ((((.x1 : Reg) ↦ᵣ (pc 210 + 4)) ** ((.x2 : Reg) ↦ᵣ newSp) **
        frameSlotsSaved wlhFrame (newSp + signExtend12 (-64 : BitVec 12)) vals **
        wlhSregs vals **
        wlhMissOut hashPtr outOffP outLenP nCalls nLin nMax nMiss) ** F) :=
  wlhCallWithin_empty_section fullCode (pc 210) vOld newSp extOff vals F
    v5 v6 secPtr hashPtr outOffP outLenP nCalls nLin nLast nMax nMiss
    hF hvals ext_ret_align ext_target ext_jal_mem wlh_code_in_full

end EvmAsm.Codegen.MptWalkSpec
