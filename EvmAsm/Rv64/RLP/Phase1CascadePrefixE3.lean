/-
  EvmAsm.Rv64.RLP.Phase1CascadePrefixE3

  EL.3 Phase 1 cascade prefix for the e3 (long-string) path.

  Composes:
    * `rlp_phase1_step_ntaken_spec` at `(base, k = 0x80)` — first
      cascade step assumed *not* taken (caller has `¬ ult v5 0x80`).
    * `rlp_phase1_step_ntaken_spec` at `(base + 8, k = 0xB8)` —
      second cascade step also not taken (caller has `¬ ult v5 0xB8`).
    * `rlp_phase1_step_taken_spec` at `(base + 16, k = 0xC0)` —
      third cascade step assumed taken (caller has `ult v5 0xC0`).

  Result: a single `cpsTriple` from the Phase 1 entry `base` to the
  e3 target, witnessing that the cascade traverses the first three
  steps along the e3 path under all three dispatch hypotheses.

  Mirrors `rlp_phase1_cascade_prefix_e2_spec` (#1358) but for the e3
  exit. Final composition with `rlp_phase3_long_string_prog` will
  yield the complete Phase 1 entry → Phase 3 long-string seed chain.
-/

import EvmAsm.Rv64.RLP.Phase1
import EvmAsm.Rv64.RLP.Phase1Disjoint

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Spec
-- ============================================================================

/-- `cpsTriple base e3_target` for the Phase 1 cascade prefix on the
    e3 (long-string) path: cascade steps 1, 2 fall through, step 3
    takes its branch.

    `kVal3 = (0 : Word) + signExtend12 0xC0` is the residue left in
    `x10` by the third cascade step. -/
theorem rlp_phase1_cascade_prefix_e3_spec (v5 v10 : Word)
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
              (rlp_phase1_step_code 0xC0 off3 (base + 16))) :
    let kVal3 := (0 : Word) + signExtend12 (0xC0 : BitVec 12)
    cpsTriple base e3_target
      ((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ kVal3)) := by
  -- Step 1: not taken at k = 0x80, fall through to base + 8.
  have step1 := rlp_phase1_step_ntaken_spec v5 v10 0x80 off1 base
    ((base + 4) + signExtend13 off1) rfl hv5_lo
  -- Step 2: not taken at k = 0xB8, fall through to base + 16.
  have step2 := rlp_phase1_step_ntaken_spec v5
    ((0 : Word) + signExtend12 (0x80 : BitVec 12)) 0xB8 off2 (base + 8)
    ((base + 8 + 4) + signExtend13 off2) rfl hv5_mid
  rw [show (base + 8 : Word) + 8 = base + 16 from by bv_omega] at step2
  -- Step 3: taken at k = 0xC0, lands at e3_target.
  have step3 := rlp_phase1_step_taken_spec v5
    ((0 : Word) + signExtend12 (0xB8 : BitVec 12)) 0xC0 off3 (base + 16)
    e3_target htarget hv5_hi
  -- Compose step 2 ; step 3.
  have step23 := cpsTriple_seq hd23 step2 step3
  -- Compose step 1 ; (step 2 ; step 3).
  have hd1_23 : (rlp_phase1_step_code 0x80 off1 base).Disjoint
      ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
        (rlp_phase1_step_code 0xC0 off3 (base + 16))) :=
    CodeReq.Disjoint.union_right hd12 hd13
  exact cpsTriple_seq hd1_23 step1 step23

/-- Convenience variant of `rlp_phase1_cascade_prefix_e3_spec` that
    discharges all three pairwise cascade-step disjointness obligations
    internally via the `rlp_phase1_step_code_disjoint_*` helpers
    (#1364). The user only supplies the dispatch hypotheses on `v5`
    and the `htarget` PC equation. -/
theorem rlp_phase1_cascade_prefix_e3_spec' (v5 v10 : Word)
    (off1 off2 off3 : BitVec 13) (base e3_target : Word)
    (htarget : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (hv5_lo  : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0x80 : BitVec 12)))
    (hv5_mid : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xB8 : BitVec 12)))
    (hv5_hi  : BitVec.ult v5 ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) :
    let kVal3 := (0 : Word) + signExtend12 (0xC0 : BitVec 12)
    cpsTriple base e3_target
      ((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ kVal3)) :=
  rlp_phase1_cascade_prefix_e3_spec v5 v10 off1 off2 off3 base e3_target
    htarget hv5_lo hv5_mid hv5_hi
    (rlp_phase1_step_code_disjoint_8 0x80 0xB8 off1 off2 base)
    (rlp_phase1_step_code_disjoint_16 0x80 0xC0 off1 off3 base)
    (by
      have h := rlp_phase1_step_code_disjoint_8 0xB8 0xC0 off2 off3 (base + 8)
      rw [show (base + 8 : Word) + 8 = base + 16 from by bv_omega] at h; exact h)

end EvmAsm.Rv64.RLP
