/-
  EvmAsm.Rv64.RLP.Phase1CascadePrefixE2

  EL.3 Phase 1 cascade prefix for the e2 (short-string) path.

  Composes:
    * `rlp_phase1_step_ntaken_spec` at `(base, k = 0x80)` — first
      cascade step assumed *not* taken (caller has `¬ ult v5 0x80`).
    * `rlp_phase1_step_taken_spec` at `(base + 8, k = 0xB8)` — second
      cascade step assumed taken (caller has `ult v5 0xB8`).

  Result: a single `cpsTriple` from the Phase 1 entry `base` to the
  e2 target, witnessing that the cascade traverses the first two steps
  along the e2 path under both dispatch hypotheses.

  This is the cascade-prefix portion of the full e2 path; appending
  `rlp_phase3_short_string_prog` at the e2 target yields the complete
  Phase 1 entry → Phase 3 short-string emit chain.
-/

import EvmAsm.Rv64.RLP.Phase1

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Spec
-- ============================================================================

/-- `cpsTriple base e2_target` for the Phase 1 cascade prefix on the
    e2 (short-string) path: first cascade step at `base` (k = 0x80,
    not taken), then second cascade step at `base + 8` (k = 0xB8,
    taken).

    `kVal2 = (0 : Word) + signExtend12 0xB8` is the residue left in
    `x10` by the second cascade step. -/
theorem rlp_phase1_cascade_prefix_e2_spec (v5 v10 : Word)
    (off1 off2 : BitVec 13) (base e2_target : Word)
    (htarget : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (hv5_lo : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0x80 : BitVec 12)))
    (hv5_hi : BitVec.ult v5 ((0 : Word) + signExtend12 (0xB8 : BitVec 12)))
    (hd : (rlp_phase1_step_code 0x80 off1 base).Disjoint
            (rlp_phase1_step_code 0xB8 off2 (base + 8))) :
    let kVal2 := (0 : Word) + signExtend12 (0xB8 : BitVec 12)
    cpsTriple base e2_target
      ((rlp_phase1_step_code 0x80 off1 base).union
         (rlp_phase1_step_code 0xB8 off2 (base + 8)))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ kVal2)) := by
  -- Step 1: not-taken at k = 0x80, e1 target = (base+4) + off1
  -- (irrelevant; the spec lands at base + 8 regardless).
  have step1 := rlp_phase1_step_ntaken_spec v5 v10 0x80 off1 base
    ((base + 4) + signExtend13 off1) rfl hv5_lo
  -- Step 2: taken at k = 0xB8, e2 target = (base+8+4) + off2 = e2_target
  have step2 := rlp_phase1_step_taken_spec v5
    ((0 : Word) + signExtend12 (0x80 : BitVec 12)) 0xB8 off2
    (base + 8) e2_target htarget hv5_hi
  exact cpsTriple_seq hd step1 step2

end EvmAsm.Rv64.RLP
