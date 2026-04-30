/-
  EvmAsm.Rv64.RLP.Phase1CascadePrefixE5

  EL.3 Phase 1 cascade prefix for the e5 (long-list / fall-through) path.

  Composes:
    * `rlp_phase1_step_ntaken_spec` at `(base, k = 0x80)` — step 1
      not taken (`¬ ult v5 0x80`).
    * `rlp_phase1_step_ntaken_spec` at `(base + 8, k = 0xB8)` — step
      2 not taken (`¬ ult v5 0xB8`).
    * `rlp_phase1_step_ntaken_spec` at `(base + 16, k = 0xC0)` — step
      3 not taken (`¬ ult v5 0xC0`).
    * `rlp_phase1_step_ntaken_spec` at `(base + 24, k = 0xF8)` — step
      4 not taken (`¬ ult v5 0xF8`).

  Result: a single `cpsTripleWithin base (base + 32)` witnessing that under
  the four fall-through hypotheses (`v5 ≥ 0xF8`), the cascade falls
  all the way through to the long-list / fall-through PC.

  Mirrors `rlp_phase1_cascade_prefix_e4_spec` (#1362) but with the
  fourth step also fall-through.
-/

import EvmAsm.Rv64.RLP.Phase1
import EvmAsm.Rv64.RLP.Phase1Disjoint

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Spec
-- ============================================================================

/-- `cpsTripleWithin base (base + 32)` for the Phase 1 cascade prefix on the
    e5 (long-list / fall-through) path: all four cascade steps fall
    through.

    `kVal4 = (0 : Word) + signExtend12 0xF8` is the residue left in
    `x10` by the fourth (final) cascade step. The exit PC `base + 32`
    is the long-list dispatch target in the Yellow Paper layout. -/
theorem rlp_phase1_cascade_prefix_e5_spec_within (v5 v10 : Word)
    (off1 off2 off3 off4 : BitVec 13) (base : Word)
    (hv5_lo  : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0x80 : BitVec 12)))
    (hv5_2   : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xB8 : BitVec 12)))
    (hv5_3   : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xC0 : BitVec 12)))
    (hv5_hi  : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xF8 : BitVec 12)))
    (hd12 : (rlp_phase1_step_code 0x80 off1 base).Disjoint
              (rlp_phase1_step_code 0xB8 off2 (base + 8)))
    (hd13 : (rlp_phase1_step_code 0x80 off1 base).Disjoint
              (rlp_phase1_step_code 0xC0 off3 (base + 16)))
    (hd14 : (rlp_phase1_step_code 0x80 off1 base).Disjoint
              (rlp_phase1_step_code 0xF8 off4 (base + 24)))
    (hd23 : (rlp_phase1_step_code 0xB8 off2 (base + 8)).Disjoint
              (rlp_phase1_step_code 0xC0 off3 (base + 16)))
    (hd24 : (rlp_phase1_step_code 0xB8 off2 (base + 8)).Disjoint
              (rlp_phase1_step_code 0xF8 off4 (base + 24)))
    (hd34 : (rlp_phase1_step_code 0xC0 off3 (base + 16)).Disjoint
              (rlp_phase1_step_code 0xF8 off4 (base + 24))) :
    let kVal4 := (0 : Word) + signExtend12 (0xF8 : BitVec 12)
    cpsTripleWithin 8 base (base + 32)
      ((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ kVal4)) := by
  -- Step 1: not taken at k = 0x80, fall through to base + 8.
  have step1 := rlp_phase1_step_ntaken_spec_within v5 v10 0x80 off1 base
    ((base + 4) + signExtend13 off1) rfl hv5_lo
  -- Step 2: not taken at k = 0xB8, fall through to base + 16.
  have step2 := rlp_phase1_step_ntaken_spec_within v5
    ((0 : Word) + signExtend12 (0x80 : BitVec 12)) 0xB8 off2 (base + 8)
    ((base + 8 + 4) + signExtend13 off2) rfl hv5_2
  rw [show (base + 8 : Word) + 8 = base + 16 from by bv_omega] at step2
  -- Step 3: not taken at k = 0xC0, fall through to base + 24.
  have step3 := rlp_phase1_step_ntaken_spec_within v5
    ((0 : Word) + signExtend12 (0xB8 : BitVec 12)) 0xC0 off3 (base + 16)
    ((base + 16 + 4) + signExtend13 off3) rfl hv5_3
  rw [show (base + 16 : Word) + 8 = base + 24 from by bv_omega] at step3
  -- Step 4: not taken at k = 0xF8, fall through to base + 32.
  have step4 := rlp_phase1_step_ntaken_spec_within v5
    ((0 : Word) + signExtend12 (0xC0 : BitVec 12)) 0xF8 off4 (base + 24)
    ((base + 24 + 4) + signExtend13 off4) rfl hv5_hi
  rw [show (base + 24 : Word) + 8 = base + 32 from by bv_omega] at step4
  -- Compose step 3 ; step 4.
  have step34 := cpsTripleWithin_seq hd34 step3 step4
  -- Compose step 2 ; (step 3 ; step 4).
  have hd2_34 : (rlp_phase1_step_code 0xB8 off2 (base + 8)).Disjoint
      ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
        (rlp_phase1_step_code 0xF8 off4 (base + 24))) :=
    CodeReq.Disjoint.union_right hd23 hd24
  have step234 := cpsTripleWithin_seq hd2_34 step2 step34
  -- Compose step 1 ; (step 2 ; step 3 ; step 4).
  have hd1_234 : (rlp_phase1_step_code 0x80 off1 base).Disjoint
      ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
        ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
          (rlp_phase1_step_code 0xF8 off4 (base + 24)))) :=
    CodeReq.Disjoint.union_right hd12
      (CodeReq.Disjoint.union_right hd13 hd14)
  exact cpsTripleWithin_seq hd1_234 step1 step234

theorem rlp_phase1_cascade_prefix_e5_spec'_within (v5 v10 : Word)
    (off1 off2 off3 off4 : BitVec 13) (base : Word)
    (hv5_lo  : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0x80 : BitVec 12)))
    (hv5_2   : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xB8 : BitVec 12)))
    (hv5_3   : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xC0 : BitVec 12)))
    (hv5_hi  : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) :
    let kVal4 := (0 : Word) + signExtend12 (0xF8 : BitVec 12)
    cpsTripleWithin 8 base (base + 32)
      ((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ kVal4)) :=
  rlp_phase1_cascade_prefix_e5_spec_within v5 v10 off1 off2 off3 off4 base
    hv5_lo hv5_2 hv5_3 hv5_hi
    (rlp_phase1_step_code_disjoint_8 0x80 0xB8 off1 off2 base)
    (rlp_phase1_step_code_disjoint_16 0x80 0xC0 off1 off3 base)
    (rlp_phase1_step_code_disjoint_24 0x80 0xF8 off1 off4 base)
    (rlp_phase1_step_code_disjoint_8_at_8 0xB8 0xC0 off2 off3 base)
    (rlp_phase1_step_code_disjoint_16_at_8 0xB8 0xF8 off2 off4 base)
    (rlp_phase1_step_code_disjoint_8_at_16 0xC0 0xF8 off3 off4 base)

end EvmAsm.Rv64.RLP
