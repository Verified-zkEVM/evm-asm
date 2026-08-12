/-
  Walk → `witness_lookup_by_hash` call-site helpers (#11799 / #12144).

  ## What lives where

  * **Empty-section miss (legacy enable=0):** `MptWalkWlEmpty` —
    `root_wl_call_empty_section` / `branch_wl_call_empty_section` /
    `ext_wl_call_empty_section` via `witness_lookup_by_hash_spec_within_empty_section`.
    Domain: `section_len = 0`, `widx_enabled = 0` — production-UNREACHABLE after
    successful `witness_index_build` (#12183). Kept as legacy until enable=1
    whole-routine wrap lands.

  * **Enable=1 empty path (in progress, #12183):** nested callWithin
    `wlhIndexedEmptyCall_spec` (#12209) + body compose `wlhEn_body_core` fuel 68
    (`WitnessLookupByHashEnabled{Body,Wrap}`). Whole-routine abiFrame wrap and
    residual restate onto enable=1 still open. Nested stack needs Own at
    newSp-64 (walk entry stackFree sp0 16 — SAY SO).

  * **Hit residual (DEPENDENCY):** `MptWalkResidualChain.wlCallWithinShapeHit`
    and the `*_wl_hit_chain` lemmas. Still unsatisfiable until a hit-domain
    machine triple lands. Not the generic miss residual.

  ## Retired (#12144 follow-up)

  `root_wl_call_residual` / `branch_wl_call_residual` / `ext_wl_call_residual`
  took free `h_wl : wlCallWithinShape fullCode …` with `wlCallEntry` omitting
  telemetry (Blocker 2 unrepaired) — vacuous compile-only progress. Deleted;
  no external consumers. Do not reintroduce that shape without repairing
  the entry ambient to carry `wlhArgs`/`wlhMissOut` (or a hit-domain triple).
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
    Does NOT include x0/sp/stackFree — those live in the call entry/return
    ambient (avoid double-own under sep). -/
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

private theorem ext_wl_jal_target :
    pc 210 + signExtend21
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 840)) =
      WlB := by
  unfold pc walkB WlB; decide

private theorem ext_wl_ret_even :
    ((pc 210 + 4) &&& ~~~(1 : Word)) = pc 210 + 4 := by
  unfold pc walkB; decide

end EvmAsm.Codegen.MptWalkSpec
