/-
  EvmAsm.Rv64.RLP.Phase1Disjoint

  Public disjointness helpers for Phase 1 cascade-step `CodeReq`s.

  The Phase 1 classifier program is a chain of four cascade steps,
  each occupying eight bytes. Composing them requires disjointness
  between the various pairs. The proof obligations fall into three
  shapes (8 / 16 / 24 byte gaps), each of which holds for any
  threshold/offset by `bv_omega` on the addresses.

  These public helpers re-export the corresponding `step_code_Disjoint_{8,16,24}`
  helpers from `Phase1.lean` so downstream consumers (cascade-prefix
  specs, full-path specs) have a single public entry point and do
  not need to re-prove the same `bv_omega` shape inline at every
  call site.
-/

import EvmAsm.Rv64.RLP.Phase1

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

-- ============================================================================
-- Pairwise step-code disjointness (8 / 16 / 24 byte gaps)
-- ============================================================================

/-- Two cascade-step `CodeReq`s at bases 8 bytes apart are disjoint. -/
theorem rlp_phase1_step_code_disjoint_8
    (k1 k2 : BitVec 12) (off1 off2 : BitVec 13) (base : Word) :
    (rlp_phase1_step_code k1 off1 base).Disjoint
      (rlp_phase1_step_code k2 off2 (base + 8)) :=
  step_code_Disjoint_8 k1 k2 off1 off2 base

/-- Two cascade-step `CodeReq`s at bases 16 bytes apart are disjoint. -/
theorem rlp_phase1_step_code_disjoint_16
    (k1 k2 : BitVec 12) (off1 off2 : BitVec 13) (base : Word) :
    (rlp_phase1_step_code k1 off1 base).Disjoint
      (rlp_phase1_step_code k2 off2 (base + 16)) :=
  step_code_Disjoint_16 k1 k2 off1 off2 base

/-- Two cascade-step `CodeReq`s at bases 24 bytes apart are disjoint. -/
theorem rlp_phase1_step_code_disjoint_24
    (k1 k2 : BitVec 12) (off1 off2 : BitVec 13) (base : Word) :
    (rlp_phase1_step_code k1 off1 base).Disjoint
      (rlp_phase1_step_code k2 off2 (base + 24)) :=
  step_code_Disjoint_24 k1 k2 off1 off2 base

-- ============================================================================
-- Pairwise step-code disjointness at shifted bases
-- ============================================================================

/-- Step at `base + 8` disjoint from step at `base + 16`.
    Address-normalized variant of `rlp_phase1_step_code_disjoint_8`. -/
theorem rlp_phase1_step_code_disjoint_8_at_8
    (k1 k2 : BitVec 12) (off1 off2 : BitVec 13) (base : Word) :
    (rlp_phase1_step_code k1 off1 (base + 8)).Disjoint
      (rlp_phase1_step_code k2 off2 (base + 16)) := by
  have h := rlp_phase1_step_code_disjoint_8 k1 k2 off1 off2 (base + 8)
  rwa [show (base + 8 : Word) + 8 = base + 16 from by bv_omega] at h

/-- Step at `base + 8` disjoint from step at `base + 24`.
    Address-normalized variant of `rlp_phase1_step_code_disjoint_16`. -/
theorem rlp_phase1_step_code_disjoint_16_at_8
    (k1 k2 : BitVec 12) (off1 off2 : BitVec 13) (base : Word) :
    (rlp_phase1_step_code k1 off1 (base + 8)).Disjoint
      (rlp_phase1_step_code k2 off2 (base + 24)) := by
  have h := rlp_phase1_step_code_disjoint_16 k1 k2 off1 off2 (base + 8)
  rwa [show (base + 8 : Word) + 16 = base + 24 from by bv_omega] at h

/-- Step at `base + 16` disjoint from step at `base + 24`.
    Address-normalized variant of `rlp_phase1_step_code_disjoint_8`. -/
theorem rlp_phase1_step_code_disjoint_8_at_16
    (k1 k2 : BitVec 12) (off1 off2 : BitVec 13) (base : Word) :
    (rlp_phase1_step_code k1 off1 (base + 16)).Disjoint
      (rlp_phase1_step_code k2 off2 (base + 24)) := by
  have h := rlp_phase1_step_code_disjoint_8 k1 k2 off1 off2 (base + 16)
  rwa [show (base + 16 : Word) + 8 = base + 24 from by bv_omega] at h

end EvmAsm.Rv64.RLP
