/-
  EvmAsm.Evm64.DivMod.LoopDefs.IterV4

  Fully-corrected div128 trial quotient `div128Quot_v4` — extends `v3`
  with a Phase-2 2nd D3 correction.

  Bug history:
  - `div128Quot` (v1): had only 1 D3 correction in Phase-1b. Buggy on
    inputs where Knuth's classical D3 loop needs 2 iterations.
  - `div128Quot_v2`: added a 2nd D3 correction in Phase-1b. Fixed v1's
    1-correction bug. BUT the 1st correction had a truncation bug
    (no `rhatc >> 32 = 0` guard).
  - `div128Quot_v3`: fixed v2's truncation bug by reusing
    `div128Quot_phase2b_q0'` (which has the guard) for both Phase-1b
    corrections. BUT Phase-2 still has only 1 correction → q0' may
    overshoot q*_phase2 by 1 in some inputs (Knuth-B max).
  - `div128Quot_v4` (this file): adds a 2nd D3 correction in Phase-2.
    With Knuth's full classical 2-correction loop in BOTH phases, the
    output qHat = q*_full exactly (no overshoot at the 2-limb division
    level).

  Why v4 matters:
  - `phase2_no_wrap_lo_under_runtime` was sorry'd in v2/v3 because Phase-2
    overshoot of 1 made the no-wrap claim false. With v4, q0' = q*_phase2
    exactly, so phase2_no_wrap_lo holds universally.
  - The chain `_no_wrap_under_call_addback_beq_untruncated` →
    `_le_val256_div_plus_two_untruncated` becomes provable.
  - `addback_carry_partition_v2_{zero,nonzero}_case` (deleted in PR #1393)
    can be re-derived for v4.

  Migration path: replace consumers of `div128Quot_v2` / `div128Quot_v3`
  with `div128Quot_v4`. The actual RISC-V program needs the corresponding
  ~6 instructions added for the Phase-2 2nd D3 correction.

  Issue #1337 algorithm fix migration / Issue #61 stack spec closure.
-/

import EvmAsm.Evm64.DivMod.LoopDefs.IterV3

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **FULLY CORRECTED v4** trial quotient: `div128Quot_v3` extended with
    a Phase-2 2nd D3 correction iteration. Mirrors Knuth's classical
    Algorithm D Step D3 with up to 2 correction iterations in BOTH the
    high-half (Phase-1b) and low-half (Phase-2) trial divisions.

    With 2 D3 iterations in each phase, the output `qHat = q*_full =
    ⌊(uHi*2^64+uLo)/vTop⌋` exactly — no per-phase overshoot.

    Compared to `div128Quot_v3`:
    - v3 has 2-correction Phase-1b (proven sound) but 1-correction
      Phase-2 (q0' may = q*_phase2 + 1).
    - v4 adds 2-correction Phase-2 (q0' = q*_phase2 exactly).

    The 2nd Phase-2 correction has the same structure as Phase-1b's
    2nd correction: another call to `div128Quot_phase2b_q0'` which has
    the `rhat2' < B` guard built in. Idempotent on inputs where the
    1st correction already produced the exact quotient.

    Concrete diff from v3: the final lines change from:
    ```
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    (q1'' <<< 32) ||| q0'
    ```
    to:
    ```
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    let rhat2' := if rhat2c >>> 32 = 0 then ... else rhat2c
    let q0'' := div128Quot_phase2b_q0' q0' rhat2' dLo div_un0
    (q1'' <<< 32) ||| q0''
    ```

    Migration: this is the LONG-TERM fix for the Phase-2 overshoot
    issue uncovered in PR #1393 (commit 037579c1). Once `div128Quot_v4`
    is in place + the matching RISC-V instructions are inserted, the
    deleted `phase2_no_wrap_lo` chain can be re-derived universally
    sound.

    **Issue #1337 algorithm fix migration. Path to closing the v2
    Knuth-B v2 chain.** -/
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
    fire on q's mul. If the outer guard `rhat2c >>> 32 = 0` fails OR the
    inner BLTU `(rhat2c << 32) | div_un0 < q * dLo` fails, the helper
    returns its input `q` unchanged.

    Used by `div128Quot_v4_eq_v3_when_no_phase2_overshoot` (below) to
    show that v4's Phase-2 2nd correction is a no-op when v3's Phase-2
    1st correction was already a no-op. -/
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

/-- **div128Quot_v4 agrees with div128Quot_v3 when Phase-2's 1st
    correction already produces the exact quotient.**

    The 2nd Phase-2 correction in v4 only differs from v3 when the 1st
    correction left q0' = q*_phase2 + 1 (Phase-2 overshoot). When the
    1st correction was a no-op (rhat2c-guard or inner BLTU on q0c*dLo
    didn't fire), v4 = v3.

    Concrete sufficient condition: `¬ (rhat2c >>> 32 = 0 ∧ BLTU(...))`.
    Under this hypothesis:
    - The Phase-2 2nd rhat-update is a no-op: `rhat2' = rhat2c`.
    - The Phase-2 1st q-correction was a no-op: `q0' = q0c`.
    - So phase2b_q0' applied to (q0', rhat2c) reproduces q0' (the same
      outer-guard ∧ inner-BLTU disjunction fails on q0' = q0c). -/
theorem div128Quot_v4_eq_v3_when_no_phase2_overshoot (uHi uLo vTop : Word)
    (h_no_overshoot :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let rhat := uHi - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
      let rhat' :=
        if rhatc >>> (32 : BitVec 6).toNat = 0 then
          let qDlo := q1c * dLo
          let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
          if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
        else rhatc
      let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
      let rhat'' :=
        if rhat' >>> (32 : BitVec 6).toNat = 0 then
          let qDlo2 := q1' * dLo
          let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
          if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
        else rhat'
      let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1
      let cu_q1_dlo := q1'' * dLo
      let un21 := cu_rhat_un1 - cu_q1_dlo
      let q0 := rv64_divu un21 dHi
      let rhat2 := un21 - q0 * dHi
      let hi2 := q0 >>> (32 : BitVec 6).toNat
      let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
      let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
      -- "Phase-2 1st correction was a no-op" condition.
      ¬ (rhat2c >>> (32 : BitVec 6).toNat = 0 ∧
        BitVec.ult ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
                    (q0c * dLo))) :
    div128Quot_v4 uHi uLo vTop = div128Quot_v3 uHi uLo vTop := by
  -- Strategy outline (proof body deferred):
  -- 1. Unfold both `div128Quot_v4` and `div128Quot_v3`. Both share the
  --    prefix up through `q0' := div128Quot_phase2b_q0' q0c rhat2c …`.
  -- 2. v4 has additional `rhat2'` and `q0''` lines. Need: q0'' = q0'.
  -- 3. Under `h_no_overshoot`:
  --    a. The 1st rhat-update's inner BLTU on `q0c*dLo` doesn't fire,
  --       so `rhat2' = rhat2c` (whether outer guard is true or false).
  --    b. The 1st q-correction was a no-op, so `q0' = q0c` (apply the
  --       helper lemma `div128Quot_phase2b_q0'_eq_self_of_no_bltu`).
  --    c. Substitute (b) into v4's `q0'' = phase2b_q0' q0' rhat2c …`.
  --       Since q0' = q0c, the inner BLTU on `q0' * dLo` matches the
  --       hypothesis's BLTU on `q0c * dLo` and doesn't fire either.
  --       So `q0'' = q0'` (helper applies again).
  -- 4. Conclude: the final `(q1'' << 32) ||| q0''` equals `… ||| q0'`.
  sorry

end EvmAsm.Evm64
