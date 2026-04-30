/-
  EvmAsm.Rv64.RLP.Phase1StepToPhase3ShortString

  EL.3 single-cascade-step → Phase 3 short-string composition.

  Composes:
    * `rlp_phase1_step_taken_spec` at threshold `k = 0xB8` — a cascade
      step assumed taken (caller has `BitVec.ult v5 0xB8`).
    * `rlp_phase3_short_string_spec` at the step's target — emits the
      payload length and advances the data pointer.

  Caller obligations are split:
    * Reaching this cascade step implies the caller has already
      established `¬ BitVec.ult v5 0x80` (i.e., `v5 ≥ 0x80`); that
      precondition is needed for the short-string interpretation but
      is *not* required by the spec produced here. The result is
      well-typed for any `v5 < 0xB8`.
    * The caller is responsible for the disjointness of the cascade
      step code at `[step_base, step_base+8)` from the Phase 3
      short-string program at `[target, target+8)`.

  Mirrors `rlp_phase1_e1_then_single_byte_spec` (#1352) but for the
  e2 (short-string) exit instead of e1.
-/

import EvmAsm.Rv64.RLP.Phase1
import EvmAsm.Rv64.RLP.Phase3ShortString

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Spec
-- ============================================================================

/-- `cpsTripleWithin` chaining a Phase 1 cascade step (taken at threshold
    `0xB8`) with the Phase 3 short-string flat-decode emitter.

    Pre-state: standard Phase 1 entry plus an `x11` slot to be
    overwritten by the length, and an `x13` slot (the data pointer)
    that the short-string program advances by 1.

    Post-state: `x11 = v5 + signExtend12 (-0x80)` (payload length),
    `x13 = v13 + 1` (data pointer past the prefix byte), `x10 = 0xB8`
    (cascade-step constant residue), `x5` and `x0` preserved. -/
theorem rlp_phase1_step_then_short_string_spec_within
    (v5 v10 v11Old v13 : Word)
    (offset : BitVec 13)
    (step_base target : Word)
    (htarget : (step_base + 4) + signExtend13 offset = target)
    (hv5 : BitVec.ult v5 ((0 : Word) + signExtend12 0xB8))
    (hd  : (rlp_phase1_step_code 0xB8 offset step_base).Disjoint
            (CodeReq.ofProg target rlp_phase3_short_string_prog)) :
    cpsTripleWithin 4 step_base (target + 8)
      ((rlp_phase1_step_code 0xB8 offset step_base).union
         (CodeReq.ofProg target rlp_phase3_short_string_prog))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (v5 + signExtend12 (-(0x80 : BitVec 12)))) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) := by
  -- Step 1: Phase 1 cascade step at k = 0xB8, taken path.
  have ph1 := rlp_phase1_step_taken_spec_within v5 v10 0xB8 offset step_base target
    htarget hv5
  -- Frame Phase 1 with `x11` and `x13`.
  have ph1' : cpsTripleWithin 2 step_base target
      (rlp_phase1_step_code 0xB8 offset step_base)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13)) (by pcFree) ph1)
  -- Step 2: Phase 3 short-string at target.
  have ph3 := rlp_phase3_short_string_spec_within v5 v11Old v13 target
  -- Frame Phase 3 with `x0` and `x10`.
  have ph3' : cpsTripleWithin 2 target (target + 8)
      (CodeReq.ofProg target rlp_phase3_short_string_prog)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (v5 + signExtend12 (-(0x80 : BitVec 12)))) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))))
        (by pcFree) ph3)
  exact cpsTripleWithin_seq hd ph1' ph3'

end EvmAsm.Rv64.RLP
