/-
  EvmAsm.Rv64.RLP.Phase1ToPhase3SingleByte

  EL.3 Phase 1 → Phase 3 composition for the e1 (single-byte) exit.

  Composes:
    * `rlp_phase1_step_taken_spec` at threshold `k = 0x80` — the first
      cascade step assumed taken (caller has `BitVec.ult v5 0x80`).
    * `rlp_phase3_single_byte_spec` at the e1 target — materializes
      `length = 1` in `x11`.

  Result: a single `cpsTripleWithin` from the Phase 1 base (where the
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

/-- `cpsTripleWithin` for the e1 path: Phase 1 first cascade step (taken)
    composed with Phase 3 single-byte length emitter.

    Pre-state: standard Phase 1 entry plus an arbitrary `x11` slot to be
    overwritten by Phase 3.

    Post-state: `x11 = 1`, `x10 = 0x80` (cascade-step constant
    residue), `x5` and `x0` unchanged.

    The two `htarget` and `hd` hypotheses tie the e1 target to the
    Phase 1 cascade step's BLTU offset and to the Phase 1 step code's
    disjointness with Phase 3 single-byte's code, respectively. -/
theorem rlp_phase1_e1_then_single_byte_spec_within
    (v5 v10 v11Old : Word)
    (offset : BitVec 13)
    (base target : Word)
    (htarget : (base + 4) + signExtend13 offset = target)
    (hv5 : BitVec.ult v5 ((0 : Word) + signExtend12 0x80))
    (hd  : (rlp_phase1_step_code 0x80 offset base).Disjoint
            (CodeReq.ofProg target rlp_phase3_single_byte_prog)) :
    cpsTripleWithin 3 base (target + 4)
      ((rlp_phase1_step_code 0x80 offset base).union
         (CodeReq.ofProg target rlp_phase3_single_byte_prog))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0x80 : BitVec 12))) **
        (.x11 ↦ᵣ (1 : Word))) := by
  -- Step 1: Phase 1 cascade step at k = 0x80, taken path.
  have ph1 := rlp_phase1_step_taken_spec_within v5 v10 0x80 offset base target htarget hv5
  -- Frame Phase 1 with `x11`.
  have ph1' : cpsTripleWithin 2 base target
      (rlp_phase1_step_code 0x80 offset base)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0x80 : BitVec 12))) **
        (.x11 ↦ᵣ v11Old)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x11 ↦ᵣ v11Old) (by pcFree) ph1)
  -- Step 2: Phase 3 single-byte length emitter at target.
  have ph3 := rlp_phase3_single_byte_spec_within v11Old target
  -- Frame Phase 3 with `x5` and `x10`.
  have ph3' : cpsTripleWithin 1 target (target + 4)
      (CodeReq.ofProg target rlp_phase3_single_byte_prog)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0x80 : BitVec 12))) **
        (.x11 ↦ᵣ v11Old))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0x80 : BitVec 12))) **
        (.x11 ↦ᵣ (1 : Word))) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0x80 : BitVec 12))))
        (by pcFree) ph3)
  exact cpsTripleWithin_seq hd ph1' ph3'

theorem rlp_phase1_e1_then_single_byte_spec_at_0x42_within
    (v10 v11Old : Word)
    (offset : BitVec 13)
    (base target : Word)
    (htarget : (base + 4) + signExtend13 offset = target)
    (hd  : (rlp_phase1_step_code 0x80 offset base).Disjoint
            (CodeReq.ofProg target rlp_phase3_single_byte_prog)) :
    cpsTripleWithin 3 base (target + 4)
      ((rlp_phase1_step_code 0x80 offset base).union
         (CodeReq.ofProg target rlp_phase3_single_byte_prog))
      ((.x5 ↦ᵣ (0x42 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old))
      ((.x5 ↦ᵣ (0x42 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0x80 : BitVec 12))) **
        (.x11 ↦ᵣ (1 : Word))) :=
  rlp_phase1_e1_then_single_byte_spec_within
    (0x42 : Word) v10 v11Old offset base target htarget
    (by decide) hd

/-- Specialization at `v5 = 0x00` (the smallest canonical single-byte
    payload). The dispatch hypothesis `BitVec.ult 0 0x80` is discharged
    internally via `decide`. -/
theorem rlp_phase1_e1_then_single_byte_spec_at_0x00_within
    (v10 v11Old : Word)
    (offset : BitVec 13)
    (base target : Word)
    (htarget : (base + 4) + signExtend13 offset = target)
    (hd  : (rlp_phase1_step_code 0x80 offset base).Disjoint
            (CodeReq.ofProg target rlp_phase3_single_byte_prog)) :
    cpsTripleWithin 3 base (target + 4)
      ((rlp_phase1_step_code 0x80 offset base).union
         (CodeReq.ofProg target rlp_phase3_single_byte_prog))
      ((.x5 ↦ᵣ (0x00 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old))
      ((.x5 ↦ᵣ (0x00 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0x80 : BitVec 12))) **
        (.x11 ↦ᵣ (1 : Word))) :=
  rlp_phase1_e1_then_single_byte_spec_within
    (0x00 : Word) v10 v11Old offset base target htarget
    (by decide) hd

/-- Specialization at `v5 = 0x7F` (the largest canonical single-byte
    payload, just below the short-string threshold). The dispatch
    hypothesis `BitVec.ult 0x7F 0x80` is discharged internally via
    `decide`. -/
theorem rlp_phase1_e1_then_single_byte_spec_at_0x7F_within
    (v10 v11Old : Word)
    (offset : BitVec 13)
    (base target : Word)
    (htarget : (base + 4) + signExtend13 offset = target)
    (hd  : (rlp_phase1_step_code 0x80 offset base).Disjoint
            (CodeReq.ofProg target rlp_phase3_single_byte_prog)) :
    cpsTripleWithin 3 base (target + 4)
      ((rlp_phase1_step_code 0x80 offset base).union
         (CodeReq.ofProg target rlp_phase3_single_byte_prog))
      ((.x5 ↦ᵣ (0x7F : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old))
      ((.x5 ↦ᵣ (0x7F : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0x80 : BitVec 12))) **
        (.x11 ↦ᵣ (1 : Word))) :=
  rlp_phase1_e1_then_single_byte_spec_within
    (0x7F : Word) v10 v11Old offset base target htarget
    (by decide) hd

end EvmAsm.Rv64.RLP
