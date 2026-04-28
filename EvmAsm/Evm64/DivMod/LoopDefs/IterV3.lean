/-
  EvmAsm.Evm64.DivMod.LoopDefs.IterV3

  Fixed div128 trial quotient `div128Quot_v3` — closes the truncation
  bug in `div128Quot_v2` (where the Phase-1b 1st D3 correction lacked a
  `rhatc >> 32 = 0` guard).

  Bug witness in `div128Quot_v2`: on `(uHi=2^64-2^32+1, uLo=0, vTop=2^64-1)`,
  the algorithm undershoots the true quotient by `2^32`. See
  `SpecCallAddbackBeq/NumericalTests.lean :: div128Quot_v2_buggy_at_unreachable_uHi`.

  Fix: refactor BOTH corrections to use the existing
  `div128Quot_phase2b_q0'` helper (which has the `rhat' < B` guard built-in).
  This makes the 1st and 2nd corrections symmetric, matching Knuth's
  classical Algorithm D Step D3 loop body.

  Why a separate file: introducing `div128Quot_v3` as a NEW function
  (instead of editing `div128Quot_v2` in place) avoids breaking the many
  proofs in `SpecCallAddbackBeq.lean` that have inline let-chains
  matching the OLD un-guarded structure. Migration to v3 can proceed
  incrementally.
-/

import EvmAsm.Evm64.DivMod.LoopDefs.Iter

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **FIXED v3** trial quotient: `div128Quot_v2` with the Phase-1b 1st
    D3 correction also guarded by `rhatc >> 32 = 0`, matching the
    Phase-1b 2nd correction.

    Bug fix history: `div128Quot_v2` had an asymmetry — its 2nd D3
    correction reused the well-tested `div128Quot_phase2b_q0'` (which
    has the `rhat' < B` guard built-in), but its 1st correction was
    inlined without any guard. When `rhatc ≥ 2^32`, the truncation in
    `(rhatc << 32) | div_un1` could spuriously fire the BLTU, producing
    `q1' = q_true - 1`. Then Phase-1b's 2nd correction's guard would
    skip the correction (since `rhat' = rhatc + dHi ≥ 2^32`), leaving
    the wrong undershoot intact.

    `div128Quot_v3` fixes this by reusing `div128Quot_phase2b_q0'` for
    BOTH corrections, making the structure symmetric and faithful to
    Knuth's Algorithm D Step D3 (which terminates the correction loop
    when `r̂ ≥ b` — exactly what the guard expresses in bounded
    precision).

    Numerical validation: `div128Quot_v3_correct_at_unreachable_uHi`
    in `SpecCallAddbackBeq/NumericalTestsV3.lean` confirms the fix on
    the buggy input via `decide`.

    Migration plan: when the Phase-1 invariant proof chain stabilizes,
    references to `div128Quot_v2` should migrate to `div128Quot_v3`,
    and v2 should be removed. -/
def div128Quot_v3 (uHi uLo vTop : Word) : Word :=
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := uLo >>> (32 : BitVec 6).toNat
  let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  -- Phase 1b: 1st D3 correction — FIXED to use the guarded helper.
  let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
  let rhat' :=
    if rhatc >>> (32 : BitVec 6).toNat = 0 then
      let qDlo := q1c * dLo
      let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
      if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    else rhatc
  -- Phase 1b: 2nd D3 correction — same guarded helper.
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
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
  (q1'' <<< (32 : BitVec 6).toNat) ||| q0'

/-- **div128Quot_v3 agrees with div128Quot_v2 when rhatc < 2^32**:
    the only difference between v2 and v3 is the new `rhatc >> 32 = 0`
    guard on the 1st correction. When the guard would pass anyway
    (rhatc < 2^32), the two algorithms are bit-identical.

    This means: under runtime preconditions (where rhatc < 2^32 is
    guaranteed), all proofs about `div128Quot_v2` transfer to
    `div128Quot_v3` without modification. Consumers can migrate
    incrementally.

    PROOF STRATEGY (deferred to migration phase): unfold both defs,
    case-split on `rhatc >>> 32 = 0`, the `phase2b_q0'` helper unfolds
    to the same if-chain as v2's inlined form when the guard holds. -/
theorem div128Quot_v3_eq_v2_when_rhatc_lt_pow32 (uHi uLo vTop : Word)
    (_h_rhatc :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let rhat := uHi - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      rhatc >>> (32 : BitVec 6).toNat = 0) :
    div128Quot_v3 uHi uLo vTop = div128Quot_v2 uHi uLo vTop := by
  -- Extract the rhatc-guard hypothesis with lets unfolded.
  have h_rhatc :
      (if (rv64_divu uHi (vTop >>> (32 : BitVec 6).toNat)) >>>
              (32 : BitVec 6).toNat = 0 then
            uHi - rv64_divu uHi (vTop >>> (32 : BitVec 6).toNat) *
                  (vTop >>> (32 : BitVec 6).toNat)
          else
            uHi - rv64_divu uHi (vTop >>> (32 : BitVec 6).toNat) *
                  (vTop >>> (32 : BitVec 6).toNat) +
                (vTop >>> (32 : BitVec 6).toNat)) >>>
        (32 : BitVec 6).toNat = 0 := _h_rhatc
  unfold div128Quot_v3 div128Quot_v2
  -- The only difference between v2 and v3 is the 1st correction's q1'/rhat'.
  -- v2: `q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c`
  -- v3: `q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1`
  --     `rhat' := if rhatc >> 32 = 0 then (...same body as v2...) else rhatc`
  -- Under h_rhatc (rhatc >> 32 = 0), v3's `phase2b_q0'` unfolds to v2's
  -- inlined form, and v3's rhat' takes the if-positive branch matching v2.
  unfold div128Quot_phase2b_q0'
  simp only [h_rhatc, if_true]

end EvmAsm.Evm64
