/-
  EvmAsm.Evm64.EvmWordArith.AddbackPinning

  Branch-pinning infrastructure for the n=4 max+addback BEQ stack spec
  (Phase F of issue #61). Builds up to a proof that the algorithm's
  normalized runtime carry matches the semantic branch (single vs
  double addback) indicated by the un-normalized hypothesis `hsem`.

  See `memory/project_branch_pinning_detailed_plan.md` for the full
  6-step plan. This file starts with Step 1.
-/

import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

-- ============================================================================
-- Step 1: un-normalized Euclidean equation under max-trial single-addback
-- ============================================================================

/-- Under the un-normalized single-addback semantic hypothesis (mulsub borrow
    `c3 = 1` + first-addback carry = 1) with max trial quotient
    `signExtend12 4095 = 2^64 - 1`, the Euclidean equation holds:
    `val256(a) = (2^64 - 2) * val256(b) + val256(ab_un)`.

    Thin specialization of `mulsub_addback_val256_combined` to `q = signExtend12 4095`.
    Used by the branch-pinning proof (Step 5c of the plan) to derive a
    contradiction with the algorithm's normalized runtime carry = 0 branch.

    The `u4_new` argument is unused by the claim (the low-4 outputs of
    `addbackN4` are u4-independent per `addbackN4_fst4_u4_indep`); it's kept
    as an explicit parameter so callers can pass whatever shape their
    algorithm-level `ab` uses without an extra bridging rewrite. -/
theorem n4_max_addback_un_val256_euclidean
    (a0 a1 a2 a3 b0 b1 b2 b3 u4_new : Word)
    (hc3 : (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 1)
    (hcarry : addbackN4_carry
      (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).1
      (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.1
      (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
      (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1
      b0 b1 b2 b3 = 1) :
    let ms := mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0 b1 b2 b3
    val256 a0 a1 a2 a3 =
      (2 ^ 64 - 2) * val256 b0 b1 b2 b3 +
      val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 := by
  intro ms ab
  have hq_pos : (signExtend12 (4095 : BitVec 12) : Word).toNat ≥ 1 := by decide
  have h := mulsub_addback_val256_combined (signExtend12 4095) u4_new
    hc3 hcarry hq_pos
  simp only [] at h
  have hq_toNat : (signExtend12 (4095 : BitVec 12) : Word).toNat = 2 ^ 64 - 1 := by decide
  rw [hq_toNat] at h
  -- h : val256 a = (2^64 - 1 - 1) * val256 b + val256 ab — reduces definitionally.
  exact h

end EvmAsm.Evm64
