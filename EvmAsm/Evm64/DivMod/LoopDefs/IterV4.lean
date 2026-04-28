/-
  EvmAsm.Evm64.DivMod.LoopDefs.IterV4

  Fully-corrected div128 trial quotient `div128Quot_v4` — Knuth's
  classical Algorithm D with up to 2 D3 corrections in BOTH the
  high-half (Phase-1b) and low-half (Phase-2) trial divisions.

  Bug history (v1, v2 deprecated; v3 removed in this PR):
  - `div128Quot` (v1): only 1 D3 correction in Phase-1b. Buggy on
    inputs where Knuth's classical D3 loop needs 2 iterations.
  - `div128Quot_v2`: added a 2nd Phase-1b correction, but the 1st
    correction had a truncation bug (no `rhatc >> 32 = 0` guard).
  - (v3 was a half-step that fixed Phase-1b but kept 1-correction
    Phase-2; obsolete since `phase2_no_wrap_lo` sub-case b was proven
    FALSE under 1-correction Phase-2.)
  - `div128Quot_v4` (this file): full 2-correction in both phases.
    With Knuth's full classical 2-correction loop, the output
    `qHat = q*_full` exactly — no per-phase overshoot.

  Why v4 matters:
  - `phase2_no_wrap_lo_under_runtime` was sorry'd in v2/v3 because
    Phase-2 overshoot of 1 made the no-wrap claim false. With v4,
    q0'' = q*_phase2 exactly, so `phase2_no_wrap_lo` holds universally.
  - The chain `_no_wrap_under_call_addback_beq_untruncated` →
    `_le_val256_div_plus_two_untruncated` becomes provable.
  - `addback_carry_partition_v2_{zero,nonzero}_case` (deleted in
    PR #1393) can be re-derived for v4.

  Migration path: replace consumers of `div128Quot_v2` with
  `div128Quot_v4`. The actual RISC-V program needs the corresponding
  ~6 instructions added for the Phase-2 2nd D3 correction.

  Issue #1337 algorithm fix migration / Issue #61 stack spec closure.
-/

import EvmAsm.Evm64.DivMod.LoopDefs.Iter

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **FULLY CORRECTED v4** trial quotient. Mirrors Knuth's classical
    Algorithm D Step D3 with up to 2 correction iterations in BOTH the
    high-half (Phase-1b) and low-half (Phase-2) trial divisions.

    With 2 D3 iterations in each phase, the output `qHat = q*_full =
    ⌊(uHi*2^64+uLo)/vTop⌋` exactly — no per-phase overshoot.

    Each correction is delegated to `div128Quot_phase2b_q0'` (which has
    the `rhat' < 2^32` guard built in), so all corrections are idempotent
    on inputs where the trial quotient is already correct. -/
def div128Quot_v4 (uHi uLo vTop : Word) : Word :=
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := uLo >>> (32 : BitVec 6).toNat
  let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  -- Phase 1b: 1st D3 correction (same as v3 — guarded helper).
  let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
  let rhat' :=
    if rhatc >>> (32 : BitVec 6).toNat = 0 then
      let qDlo := q1c * dLo
      let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
      if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    else rhatc
  -- Phase 1b: 2nd D3 correction (same as v3).
  let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
  let rhat'' :=
    if rhat' >>> (32 : BitVec 6).toNat = 0 then
      let qDlo2 := q1' * dLo
      let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
      if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
    else rhat'
  -- Phase 2 setup with q1''/rhat''.
  let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1'' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  -- Phase 2: 1st D3 correction (same as v3).
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
  -- Phase 2: 2nd D3 correction — NEW in v4. Mirror of Phase-1b's
  -- 2nd correction. Closes Knuth's classical 2-correction guarantee.
  let rhat2' :=
    if rhat2c >>> (32 : BitVec 6).toNat = 0 then
      let qDlo2 := q0c * dLo
      let rhatUn0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
      if BitVec.ult rhatUn0 qDlo2 then rhat2c + dHi else rhat2c
    else rhat2c
  let q0'' := div128Quot_phase2b_q0' q0' rhat2' dLo div_un0
  (q1'' <<< (32 : BitVec 6).toNat) ||| q0''

/-- Idempotency of `div128Quot_phase2b_q0'` when its inner BLTU doesn't
    fire on q's mul. If the outer guard `rhat >>> 32 = 0` fails OR the
    inner BLTU `(rhat << 32) | divUn < q * dLo` fails, the helper
    returns its input `q` unchanged.

    A small reusable algebraic identity, useful any time we need to
    show a `phase2b_q0'` call is a no-op (e.g. when the algorithm has
    already converged at a given correction step). -/
theorem div128Quot_phase2b_q0'_eq_self_of_no_bltu
    (q rhat dLo divUn : Word)
    (h : ¬ (rhat >>> (32 : BitVec 6).toNat = 0 ∧
        BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| divUn) (q * dLo))) :
    div128Quot_phase2b_q0' q rhat dLo divUn = q := by
  unfold div128Quot_phase2b_q0'
  by_cases h_guard : rhat >>> (32 : BitVec 6).toNat = 0
  · simp only [h_guard, if_true]
    have h_bltu : ¬ BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| divUn) (q * dLo) :=
      fun hb => h ⟨h_guard, hb⟩
    simp only [Bool.not_eq_true] at h_bltu
    rw [h_bltu]
    rfl
  · simp only [h_guard, if_false]

end EvmAsm.Evm64
