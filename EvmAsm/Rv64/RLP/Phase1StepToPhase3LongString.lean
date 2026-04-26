/-
  EvmAsm.Rv64.RLP.Phase1StepToPhase3LongString

  EL.3 single-cascade-step → Phase 3 long-string composition.

  Composes:
    * `rlp_phase1_step_taken_spec` at threshold `k = 0xC0` — a cascade
      step assumed taken (caller has `BitVec.ult v5 0xC0`).
    * `rlp_phase3_long_string_spec` at the step's target — seeds the
      Phase 2 long-form loop pre-state (lenLen counter, length
      accumulator, data pointer).

  Caller obligations are split:
    * Reaching this cascade step implies the caller has already
      established `¬ BitVec.ult v5 0xB8` (i.e., `v5 ≥ 0xB8`); that
      precondition is needed for the long-string interpretation but is
      *not* required by the spec produced here.
    * The caller is responsible for the disjointness of the cascade
      step code at `[step_base, step_base+8)` from the Phase 3
      long-string program at `[target, target+12)`.

  Mirrors `rlp_phase1_e1_then_single_byte_spec` (#1352) and
  `rlp_phase1_step_then_short_string_spec` (#1354) but for the e3
  (long-string) exit.
-/

import EvmAsm.Rv64.RLP.Phase1
import EvmAsm.Rv64.RLP.Phase3LongString

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Spec
-- ============================================================================

/-- `cpsTriple` chaining a Phase 1 cascade step (taken at threshold
    `0xC0`) with the Phase 3 long-string entry block.

    Pre-state: standard Phase 1 entry plus `x11`/`x13`/`x14` slots
    that the long-string entry will overwrite (length accumulator,
    data pointer, length-of-length counter).

    Post-state: `x14 = v5 + signExtend12 (-0xB7)` (length-of-length
    counter), `x11 = 0` (cleared length accumulator),
    `x13 = v13 + 1` (data pointer past prefix), `x10 = 0xC0`
    (cascade-step constant residue), `x5` and `x0` preserved. -/
theorem rlp_phase1_step_then_long_string_spec
    (v5 v10 v11Old v13 v14Old : Word)
    (offset : BitVec 13)
    (step_base target : Word)
    (htarget : (step_base + 4) + signExtend13 offset = target)
    (hv5 : BitVec.ult v5 ((0 : Word) + signExtend12 0xC0))
    (hd  : (rlp_phase1_step_code 0xC0 offset step_base).Disjoint
            (CodeReq.ofProg target rlp_phase3_long_string_prog)) :
    cpsTriple step_base (target + 12)
      ((rlp_phase1_step_code 0xC0 offset step_base).union
         (CodeReq.ofProg target rlp_phase3_long_string_prog))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (v5 + signExtend12 (-(0xB7 : BitVec 12))))) := by
  -- Step 1: Phase 1 cascade step at k = 0xC0, taken path.
  have ph1 := rlp_phase1_step_taken_spec v5 v10 0xC0 offset step_base target
    htarget hv5
  -- Frame Phase 1 with `x11`, `x13`, `x14`.
  have ph1' : cpsTriple step_base target
      (rlp_phase1_step_code 0xC0 offset step_base)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old)) :=
    cpsTriple_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTriple_frameR
        ((.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
        (by pcFree) ph1)
  -- Step 2: Phase 3 long-string entry at target.
  have ph3 := rlp_phase3_long_string_spec v5 v11Old v13 v14Old target
  -- Frame Phase 3 with `x10`.
  have ph3' : cpsTriple target (target + 12)
      (CodeReq.ofProg target rlp_phase3_long_string_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (v5 + signExtend12 (-(0xB7 : BitVec 12))))) :=
    cpsTriple_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTriple_frameR
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12)))
        (by pcFree) ph3)
  exact cpsTriple_seq hd ph1' ph3'

end EvmAsm.Rv64.RLP
