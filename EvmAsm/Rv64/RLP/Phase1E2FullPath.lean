/-
  EvmAsm.Rv64.RLP.Phase1E2FullPath

  EL.3 full Phase 1 → Phase 3 e2 (short-string) chain.

  Composes:
    * `rlp_phase1_cascade_prefix_e2_spec` — Phase 1 cascade steps 1
      (not taken) and 2 (taken) reaching `e2_target`.
    * `rlp_phase3_short_string_spec` at `e2_target` — emits the
      payload length in `x11` and advances the data pointer in `x13`.

  Result: a single `cpsTriple base (e2_target + 8)` witnessing that
  whenever `v5 ∈ [0x80, 0xB8)`, executing the Phase 1 cascade from
  `base` runs through the e2 fall-through-then-taken path, then
  immediately into the Phase 3 short-string emitter.
-/

import EvmAsm.Rv64.RLP.Phase1CascadePrefixE2
import EvmAsm.Rv64.RLP.Phase1Disjoint
import EvmAsm.Rv64.RLP.Phase3ShortString

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Spec
-- ============================================================================

/-- `cpsTriple base (e2_target + 8)` for the full Phase 1 e2
    (short-string) path: cascade prefix to `e2_target`, then Phase 3
    short-string emit.

    Post-state: `x11 = v5 - 0x80` (payload length), `x13 = v13 + 1`
    (data pointer past prefix), `x10 = 0xB8` (cascade-step constant
    residue from the second step), `x5` and `x0` preserved. -/
theorem rlp_phase1_e2_full_path_spec
    (v5 v10 v11Old v13 : Word)
    (off1 off2 : BitVec 13) (base e2_target : Word)
    (htarget : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (hv5_lo : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0x80 : BitVec 12)))
    (hv5_hi : BitVec.ult v5 ((0 : Word) + signExtend12 (0xB8 : BitVec 12)))
    (hd_steps : (rlp_phase1_step_code 0x80 off1 base).Disjoint
                  (rlp_phase1_step_code 0xB8 off2 (base + 8)))
    (hd_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)) :
    cpsTriple base (e2_target + 8)
      (((rlp_phase1_step_code 0x80 off1 base).union
          (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
         (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (v5 + signExtend12 (-(0x80 : BitVec 12)))) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) := by
  -- Step 1: cascade prefix (steps 1 ntaken + 2 taken) reaches e2_target.
  have prefix_ := rlp_phase1_cascade_prefix_e2_spec v5 v10 off1 off2 base
    e2_target htarget hv5_lo hv5_hi hd_steps
  -- Frame the prefix with `x11` and `x13`.
  have prefix' : cpsTriple base e2_target
      ((rlp_phase1_step_code 0x80 off1 base).union
         (rlp_phase1_step_code 0xB8 off2 (base + 8)))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13)) :=
    cpsTriple_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTriple_frameR
        ((.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13)) (by pcFree) prefix_)
  -- Step 2: Phase 3 short-string at e2_target.
  have ph3 := rlp_phase3_short_string_spec v5 v11Old v13 e2_target
  -- Frame Phase 3 with `x0` and `x10`.
  have ph3' : cpsTriple e2_target (e2_target + 8)
      (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (v5 + signExtend12 (-(0x80 : BitVec 12)))) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) :=
    cpsTriple_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTriple_frameR
        ((.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))))
        (by pcFree) ph3)
  exact cpsTriple_seq hd_phase3 prefix' ph3'

/-- Convenience variant of `rlp_phase1_e2_full_path_spec` that
    discharges the cascade-step disjointness obligation internally
    via `rlp_phase1_step_code_disjoint_8`. The caller still has to
    supply the Phase 1↔Phase 3 disjointness `hd_phase3` since
    `e2_target` is not derivable from `base`. -/
theorem rlp_phase1_e2_full_path_spec'
    (v5 v10 v11Old v13 : Word)
    (off1 off2 : BitVec 13) (base e2_target : Word)
    (htarget : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (hv5_lo : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0x80 : BitVec 12)))
    (hv5_hi : BitVec.ult v5 ((0 : Word) + signExtend12 (0xB8 : BitVec 12)))
    (hd_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)) :
    cpsTriple base (e2_target + 8)
      (((rlp_phase1_step_code 0x80 off1 base).union
          (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
         (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (v5 + signExtend12 (-(0x80 : BitVec 12)))) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) :=
  rlp_phase1_e2_full_path_spec v5 v10 v11Old v13 off1 off2 base e2_target
    htarget hv5_lo hv5_hi
    (rlp_phase1_step_code_disjoint_8 0x80 0xB8 off1 off2 base)
    hd_phase3

end EvmAsm.Rv64.RLP
