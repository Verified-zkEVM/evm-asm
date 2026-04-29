/-
  EvmAsm.Rv64.RLP.Phase1E3FullPath

  EL.3 full Phase 1 → Phase 3 e3 (long-string) chain.

  Composes:
    * `rlp_phase1_cascade_prefix_e3_spec` — Phase 1 cascade steps 1, 2
      (both fall-through) and step 3 (taken at `0xC0`), reaching
      `e3_target`.
    * `rlp_phase3_long_string_spec` at `e3_target` — seeds the Phase 2
      long-form loop pre-state (lenLen counter, length accumulator,
      data pointer).

  Result: a single `cpsTriple base (e3_target + 12)` witnessing that
  whenever `v5 ∈ [0xB8, 0xC0)`, executing the Phase 1 cascade from
  `base` traverses the e3 path then immediately seeds the long-form
  length loop.

  Mirrors `rlp_phase1_e2_full_path_spec` (#1360) for the e3 exit.
-/

import EvmAsm.Rv64.RLP.Phase1CascadePrefixE3
import EvmAsm.Rv64.RLP.Phase1Disjoint
import EvmAsm.Rv64.RLP.Phase3LongString

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Spec
-- ============================================================================

/-- `cpsTriple base (e3_target + 12)` for the full Phase 1 e3
    (long-string) path: cascade prefix to `e3_target`, then Phase 3
    long-string entry.

    Post-state: `x14 = v5 + signExtend12 (-0xB7)` (length-of-length
    counter), `x11 = 0` (cleared length accumulator), `x13 = v13 + 1`
    (data pointer past prefix), `x10 = 0xC0` (cascade-step constant
    residue), `x5` and `x0` preserved — the canonical pre-loop state
    for the Phase 2 long-form length loop. -/
theorem rlp_phase1_e3_full_path_spec
    (v5 v10 v11Old v13 v14Old : Word)
    (off1 off2 off3 : BitVec 13) (base e3_target : Word)
    (htarget : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (hv5_lo  : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0x80 : BitVec 12)))
    (hv5_mid : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xB8 : BitVec 12)))
    (hv5_hi  : BitVec.ult v5 ((0 : Word) + signExtend12 (0xC0 : BitVec 12)))
    (hd12 : (rlp_phase1_step_code 0x80 off1 base).Disjoint
              (rlp_phase1_step_code 0xB8 off2 (base + 8)))
    (hd13 : (rlp_phase1_step_code 0x80 off1 base).Disjoint
              (rlp_phase1_step_code 0xC0 off3 (base + 16)))
    (hd23 : (rlp_phase1_step_code 0xB8 off2 (base + 8)).Disjoint
              (rlp_phase1_step_code 0xC0 off3 (base + 16)))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))).Disjoint
        (CodeReq.ofProg e3_target rlp_phase3_long_string_prog)) :
    cpsTriple base (e3_target + 12)
      (((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (v5 + signExtend12 (-(0xB7 : BitVec 12))))) := by
  -- Step 1: cascade prefix (steps 1+2 ntaken + step 3 taken) reaches e3_target.
  have prefix_ := rlp_phase1_cascade_prefix_e3_spec v5 v10 off1 off2 off3 base
    e3_target htarget hv5_lo hv5_mid hv5_hi hd12 hd13 hd23
  -- Frame the prefix with `x11`, `x13`, `x14`.
  have prefix' : cpsTriple base e3_target
      ((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))
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
        (by pcFree) prefix_)
  -- Step 2: Phase 3 long-string entry at e3_target.
  have ph3 := rlp_phase3_long_string_spec v5 v11Old v13 v14Old e3_target
  -- Frame Phase 3 with `x10`.
  have ph3' : cpsTriple e3_target (e3_target + 12)
      (CodeReq.ofProg e3_target rlp_phase3_long_string_prog)
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
  exact cpsTriple_seq hd_phase3 prefix' ph3'

/-- Convenience variant of `rlp_phase1_e3_full_path_spec` that
    discharges the three pairwise cascade-step disjointness
    obligations (`hd12`, `hd13`, `hd23`) internally via the
    `rlp_phase1_step_code_disjoint_*` helpers. The caller still
    supplies the Phase 1↔Phase 3 disjointness `hd_phase3` since
    `e3_target` is not derivable from `base`. -/
theorem rlp_phase1_e3_full_path_spec'
    (v5 v10 v11Old v13 v14Old : Word)
    (off1 off2 off3 : BitVec 13) (base e3_target : Word)
    (htarget : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (hv5_lo  : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0x80 : BitVec 12)))
    (hv5_mid : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xB8 : BitVec 12)))
    (hv5_hi  : BitVec.ult v5 ((0 : Word) + signExtend12 (0xC0 : BitVec 12)))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))).Disjoint
        (CodeReq.ofProg e3_target rlp_phase3_long_string_prog)) :
    cpsTriple base (e3_target + 12)
      (((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (v5 + signExtend12 (-(0xB7 : BitVec 12))))) :=
  rlp_phase1_e3_full_path_spec v5 v10 v11Old v13 v14Old off1 off2 off3 base
    e3_target htarget hv5_lo hv5_mid hv5_hi
    (rlp_phase1_step_code_disjoint_8 0x80 0xB8 off1 off2 base)
    (rlp_phase1_step_code_disjoint_16 0x80 0xC0 off1 off3 base)
    (rlp_phase1_step_code_disjoint_8_at_8 0xB8 0xC0 off2 off3 base)
    hd_phase3

end EvmAsm.Rv64.RLP
