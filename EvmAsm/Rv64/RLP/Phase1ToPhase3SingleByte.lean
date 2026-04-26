/-
  EvmAsm.Rv64.RLP.Phase1ToPhase3SingleByte

  EL.3 Phase 1 → Phase 3 composition for the e1 (single-byte) exit.

  Composes:
    * `rlp_phase1_step_taken_spec` at threshold `k = 0x80` — the first
      cascade step assumed taken (caller has `BitVec.ult v5 0x80`).
    * `rlp_phase3_single_byte_spec` at the e1 target — materializes
      `length = 1` in `x11`.

  Result: a single `cpsTriple` from the Phase 1 base (where the
  classifier starts) through the e1 target to the e1 exit
  (`target + 4`), under the disjointness assumption that the Phase 1
  step code at `[base, base+8)` does not overlap the Phase 3
  single-byte program at `target`.
-/

import EvmAsm.Rv64.RLP.Phase1
import EvmAsm.Rv64.RLP.Phase3SingleByte

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Spec
-- ============================================================================

/-- `cpsTriple` for the e1 path: Phase 1 first cascade step (taken)
    composed with Phase 3 single-byte length emitter.

    Pre-state: standard Phase 1 entry plus an arbitrary `x11` slot to be
    overwritten by Phase 3.

    Post-state: `x11 = 1`, `x10 = 0x80` (cascade-step constant
    residue), `x5` and `x0` unchanged.

    The two `htarget` and `hd` hypotheses tie the e1 target to the
    Phase 1 cascade step's BLTU offset and to the Phase 1 step code's
    disjointness with Phase 3 single-byte's code, respectively. -/
theorem rlp_phase1_e1_then_single_byte_spec
    (v5 v10 v11Old : Word)
    (offset : BitVec 13)
    (base target : Word)
    (htarget : (base + 4) + signExtend13 offset = target)
    (hv5 : BitVec.ult v5 ((0 : Word) + signExtend12 0x80))
    (hd  : (rlp_phase1_step_code 0x80 offset base).Disjoint
            (CodeReq.ofProg target rlp_phase3_single_byte_prog)) :
    cpsTriple base (target + 4)
      ((rlp_phase1_step_code 0x80 offset base).union
         (CodeReq.ofProg target rlp_phase3_single_byte_prog))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0x80 : BitVec 12))) **
        (.x11 ↦ᵣ (1 : Word))) := by
  -- Step 1: Phase 1 cascade step at k = 0x80, taken path.
  have ph1 := rlp_phase1_step_taken_spec v5 v10 0x80 offset base target htarget hv5
  -- Frame Phase 1 with `x11`.
  have ph1' : cpsTriple base target
      (rlp_phase1_step_code 0x80 offset base)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0x80 : BitVec 12))) **
        (.x11 ↦ᵣ v11Old)) :=
    cpsTriple_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTriple_frameR (.x11 ↦ᵣ v11Old) (by pcFree) ph1)
  -- Step 2: Phase 3 single-byte length emitter at target.
  have ph3 := rlp_phase3_single_byte_spec v11Old target
  -- Frame Phase 3 with `x5` and `x10`.
  have ph3' : cpsTriple target (target + 4)
      (CodeReq.ofProg target rlp_phase3_single_byte_prog)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0x80 : BitVec 12))) **
        (.x11 ↦ᵣ v11Old))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0x80 : BitVec 12))) **
        (.x11 ↦ᵣ (1 : Word))) :=
    cpsTriple_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTriple_frameR
        ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0x80 : BitVec 12))))
        (by pcFree) ph3)
  exact cpsTriple_seq hd ph1' ph3'

end EvmAsm.Rv64.RLP
