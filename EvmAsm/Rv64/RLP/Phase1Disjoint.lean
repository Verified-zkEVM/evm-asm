/-
  EvmAsm.Rv64.RLP.Phase1Disjoint

  Public disjointness helpers for Phase 1 cascade-step `CodeReq`s.

  The Phase 1 classifier program is a chain of four cascade steps,
  each occupying eight bytes. Composing them requires disjointness
  between the various pairs. The proof obligations fall into three
  shapes (8 / 16 / 24 byte gaps), each of which holds for any
  threshold/offset by `bv_omega` on the addresses.

  These public helpers give downstream consumers (cascade-prefix
  specs, full-path specs) a single re-exported entry point so they
  do not need to either:
    * reach into `Phase1.lean`'s `private` `step_code_Disjoint_{8,16,24}`
      helpers, or
    * re-prove the same `bv_omega` shape inline at every call site.
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
  CodeReq.Disjoint.union_left
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega)))
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega)))

/-- Two cascade-step `CodeReq`s at bases 16 bytes apart are disjoint. -/
theorem rlp_phase1_step_code_disjoint_16
    (k1 k2 : BitVec 12) (off1 off2 : BitVec 13) (base : Word) :
    (rlp_phase1_step_code k1 off1 base).Disjoint
      (rlp_phase1_step_code k2 off2 (base + 16)) :=
  CodeReq.Disjoint.union_left
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega)))
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega)))

/-- Two cascade-step `CodeReq`s at bases 24 bytes apart are disjoint. -/
theorem rlp_phase1_step_code_disjoint_24
    (k1 k2 : BitVec 12) (off1 off2 : BitVec 13) (base : Word) :
    (rlp_phase1_step_code k1 off1 base).Disjoint
      (rlp_phase1_step_code k2 off2 (base + 24)) :=
  CodeReq.Disjoint.union_left
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega)))
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega)))

end EvmAsm.Rv64.RLP
