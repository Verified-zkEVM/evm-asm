/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2

  Replacement for PR #1154 (closed). Proves the call-skip exact lower bound
  `val256(a)/val256(b) ≤ (div128Quot u4 u3 b3').toNat` under shift_nz + hcall
  + hskip, via a **GLOBAL Phase 1+2 compensation argument** instead of the
  per-phase tight bounds that PR #1154 attempted.

  Background (why per-phase fails): see
  `memory/project_knuth_b_lower_large_rhatc.md`. The overall Knuth bound
  `qHat ≥ q_true_full` holds only because Phase 2 compensates Phase 1
  undershoots — a global, not per-phase, property.

  ## Decomposition plan

  The top theorem `div128Quot_call_skip_ge_val256_div_v2` composes two
  sub-lemmas (§A and §B). Each is further decomposed into smaller
  sub-sub-lemmas (A1–A4 and B1–B3) with individual sorrys.

  - §A: **core Knuth-B lower** at 128/64.
      `(u4*2^64 + u3) / b3' ≤ (div128Quot u4 u3 b3').toNat`

  - §B: **val256 → 128/64 bridge** (normalization).
      `val256(a)/val256(b) ≤ (u4*2^64 + u3) / b3'`

  Each sub-section below lists its sub-lemmas with statement, dependency,
  and estimated effort. Iterate through these in follow-up iterations.

  ## §A sub-lemmas (core, ~500 lines total)

  - **A1** `div128Quot_qHat_times_b3_le_u_plus_two_b3`:
       `qHat.toNat * b3'.toNat ≤ u4*2^64 + u3 + 2*b3'` (Knuth-B UPPER form).
       Derived from Phase 1b post + Phase 2b post + small correction.
       ~100 lines. **This is the Knuth-B UPPER bound** (qHat ≤ q_true + 2).
       NOT the target — just useful context.

  - **A2** `div128Quot_qHat_plus_one_times_b3_gt_u`:
       `(qHat.toNat + 1) * b3'.toNat > u4*2^64 + u3` (the LOWER bound in
       divisibility form). Divide by b3' to get q_true ≤ qHat.
       **This is the hard core.** ~300 lines.

       Proof sketch: by contradiction. Suppose `(qHat+1)*b3' ≤ u4*2^64+u3`.
       Then some "uncovered" mass of at least b3' exists in u_total beyond
       what qHat accounts for. Trace through Phase 1 + Phase 2 to derive
       either a contradiction with the algorithm's invariants, or show
       that a false alarm would have been caught.

  - **A3** `div128Quot_toNat_decomp_lt_pow32`:
       `qHat.toNat = (q1'.toNat % 2^32) * 2^32 + q0'.toNat` when q0' < 2^32.
       Already exists as `div128Quot_toNat_eq` (Div128FinalAssembly.lean:641).
       No new code needed; just cite.

  - **A4** `div128Quot_ge_q_true_normalized` (the §A target):
       `(u4*2^64 + u3) / b3' ≤ qHat.toNat`.
       Trivial from A2 via `Nat.div_lt_iff_lt_mul`. ~5 lines.

  ## §B sub-lemmas (bridge, ~100 lines total)

  - **B1** `val256_eq_u_total_via_shift`:
       `val256(a_norm) + u4 * 2^256 = val256(a) * 2^shift`
       (normalization preserves value modulo the u4 overflow term).
       Already exists as `u_val256_eq_scaled_with_overflow`. No new code.

  - **B2** `val256_b_norm_eq_b_scaled`:
       `val256(b_norm) = val256(b) * 2^shift`.
       Already exists as `b3_prime_val256_eq_scaled`. No new code.

  - **B3** `val256_ratio_le_u_total_div_b3_prime`:
       `val256(a) / val256(b) ≤ (u4*2^64 + u3) / b3'`.

       Proof: use B1 + B2 to rewrite val256(a)/val256(b) = (val256(a)*2^shift)
       / (val256(b)*2^shift) = val256(a_norm) / val256(b_norm) [if u4 = 0]
       or analogous with u4-overflow. Then truncate to the top-3 Word window.
       ~50 lines.

  - **B4** `q_true_triple_bridge_to_val256_norm` (the §B target):
       Wrapper around B3 with the explicit let-chain that matches the
       main theorem's statement shape. ~30 lines.
-/

import EvmAsm.Evm64.EvmWordArith.Div128CallSkipClose

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

-- =============================================================================
-- §A — Core Knuth-B lower bound (128/64 level)
-- =============================================================================

/-- **A1**: Knuth-B upper form. `qHat * b3' ≤ u + 2*b3'`.
    (UPPER direction of Knuth-B; not the target but useful reference.)

    **TODO**: ~100 lines via Phase 1b euclidean + Phase 2b euclidean. -/
theorem div128Quot_qHat_times_b3_le_u_plus_two_b3
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat) :
    (div128Quot u4 u3 b3').toNat * b3'.toNat ≤
      u4.toNat * 2^64 + u3.toNat + 2 * b3'.toNat := by
  sorry

/-- **A2**: Knuth-B lower form (divisibility). `(qHat + 1) * b3' > u`.
    This is the deep core — Phase 1+2 compensation argument.

    **TODO**: ~300 lines. Strategy (tentative):
    1. Case on Phase 1 false alarm: if Phase 1 is tight, Phase 2 closes directly.
    2. Under Phase 1 false alarm (q1' = q_true_1 - 1), un21 after Phase 1 is
       larger by b3' than the tight case. Phase 2 on this larger un21 yields
       a q0' that is 2^32 bigger than the tight-Phase-1 q0' would be.
    3. Final halfword combine `(q1' << 32) | q0'` absorbs the 2^32 overshoot:
       the "extra" 2^32 from q0' conceptually moves into the q1' column,
       making qHat match what tight-Phase-1 would produce.

    Need careful tracking of modular arithmetic in the halfword combine. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  sorry

/-- **A4** (the §A target, derived from A2 via Nat.div). -/
theorem div128Quot_ge_q_true_normalized
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat) :
    (u4.toNat * 2^64 + u3.toNat) / b3'.toNat ≤
      (div128Quot u4 u3 b3').toNat := by
  have hb3'_pos : 0 < b3'.toNat := by
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_core := div128Quot_qHat_plus_one_times_b3_gt_u u4 u3 b3' hb3'_ge hu4_lt_b3'
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hb3'_pos).mpr h_core)

-- =============================================================================
-- §B — Bridge from val256 to 128/64 (normalization)
-- =============================================================================

/-- **B3**: val256 ratio bound under normalization.
    `val256(a) / val256(b) ≤ (u4*2^64 + u3) / b3'`.

    **TODO**: ~50 lines via val256 decomposition + shift arithmetic.
    Uses existing `u_val256_eq_scaled_with_overflow` and
    `b3_prime_val256_eq_scaled` (both on main). -/
theorem val256_ratio_le_u_total_div_b3_prime
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hb3nz : b3 ≠ 0) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat := by
  sorry

/-- **B4** (the §B target, wrapper form). -/
theorem q_true_triple_bridge_to_val256_norm
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hb3nz : b3 ≠ 0) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat :=
  val256_ratio_le_u_total_div_b3_prime a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz hb3nz

-- =============================================================================
-- Main theorem: composition
-- =============================================================================

/-- **Call-skip exact lower bound** (the target of PR #1154 replacement).
    Under shift_nz + hcall + hskip + hbnz,
    `val256(a) / val256(b) ≤ (div128Quot u4 u3 b3').toNat`. -/
theorem div128Quot_call_skip_ge_val256_div_v2
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3)
    (_hskip : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (div128Quot u4 u3 b3').toNat := by
  intro shift antiShift b3' u4 u3
  -- Step 1: Bridge to the normalized 128/64 quotient (§B).
  have h_bridge := q_true_triple_bridge_to_val256_norm a0 a1 a2 a3 b0 b1 b2 b3
    hshift_nz hb3nz
  simp only [] at h_bridge
  -- Step 2: Core Knuth-B lower bound (§A).
  have h_b3'_ge : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 b3 b2 hb3nz _
  have h_u4_lt_b3' : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_core := div128Quot_ge_q_true_normalized u4 u3 b3' h_b3'_ge h_u4_lt_b3'
  -- Step 3: Transitivity.
  exact Nat.le_trans h_bridge h_core

end EvmAsm.Evm64
