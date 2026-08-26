/-
  EvmAsm.Evm64.DivMod.LoopDefs.IterV5

  v5 div128 trial quotient `div128Quot_v5` — repairs the two buggy ULTs
  in `div128Quot_v4` discovered in PR #7077 and refuted by PR #7080.

  Bug history (see project_v4_bugs_v5_repair and PRs #7077/#7080):
  - `div128Quot_v4`'s Phase-1a correction sets `q1c := q1 - 1` when
    `hi1 ≠ 0`. When `rhatc ≥ 2^32` the subsequent Phase-1b 1st-correction
    ULT compares against `(rhatc <<< 32) ||| div_un1`, which truncates
    bit 32 in BitVec 64 → the correction misfires → `Q1dd` undershoots.
  - `div128Quot_v4`'s Phase-2a correction sets `q0c := q0 - 1` similarly.
    When `q0c ≥ 2^32`, `q0c * dLo` wraps mod 2^64 → the Phase-2 1st
    correction fails to fire when it should → `Q0dd` overshoots.

  v5 fix (Knuth's classical b-1 cap):
  - Phase-1a: when `hi1 ≠ 0`, cap `q1c := 2^32 - 1` (not `q1 - 1`), and
    recompute `rhatc := uHi - q1c * dHi`. This ensures `q1c < 2^32`
    unconditionally, so `q1c * dLo` fits in BitVec 64.
  - Phase-2a: analogous cap `q0c := 2^32 - 1`, `rhat2c := un21 - q0c * dHi`.
  - Phase-1b 1st correction: add the `rhatc >>> 32 = 0` guard (mirroring
    the guard already present in Phase-1b 2nd correction and Phase-2b
    via `div128Quot_phase2b_q0'`). This blocks the ULT from misfiring
    when `rhatc` is wide.

  Expected unconditional bounds (to be proven under bead `evm-asm-wbc4i.4`
  and `.5`):
  - `div128Quot_v5 uHi uLo vTop ≤ q_true + 1` (Knuth-A `+1` floor).
  - `div128Quot_v5 uHi uLo vTop ≥ q_true` (LB).

  Counterexample regression: under v5 the PR #7080 `cePlus2_*` and
  `ceUnd_*` inputs satisfy both bounds (verified via `decide` once V5.4 /
  V5.5 land).

  Issue #61 stack spec closure (bead `evm-asm-wbc4i`).
-/

module

public import EvmAsm.Evm64.DivMod.LoopDefs.Iter

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **v5** trial quotient: caps `q1c`, `q0c` at `2^32 - 1` and guards
    the Phase-1b 1st correction by `rhatc >>> 32 = 0`. Everything else
    mirrors `div128Quot_v4`.

    The cap ensures `q1c * dLo` and `q0c * dLo` cannot wrap mod 2^64
    (since each factor is `< 2^32`). The guard on the 1st Phase-1b
    correction prevents the buggy ULT that fires when `rhatc << 32`
    loses bit 32 in BitVec 64 arithmetic. Both bug regimes from PR #7077
    / PR #7080 are eliminated. -/
def div128Quot_v5 (uHi uLo vTop : Word) : Word :=
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := uLo >>> (32 : BitVec 6).toNat
  let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  -- v5 Phase-1a: cap at 2^32 - 1 (NOT q1 - 1 as in v4).
  let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1cCap
  let rhatc := if hi1 = 0 then rhat else uHi - q1c * dHi
  -- v5 Phase-1b 1st D3 correction: guarded by rhatc >>> 32 = 0 so the
  -- ULT cannot misfire on wide rhatc.
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let phase1bFire1 :=
    decide (rhatc >>> (32 : BitVec 6).toNat = 0) && BitVec.ult rhatUn1 qDlo
  let q1' := if phase1bFire1 then q1c + signExtend12 4095 else q1c
  let rhat' := if phase1bFire1 then rhatc + dHi else rhatc
  -- Phase-1b 2nd D3 correction (unchanged from v4 — already guarded).
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
  -- v5 Phase-2a: cap at 2^32 - 1 (NOT q0 - 1 as in v4).
  let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0cCap
  let rhat2c := if hi2 = 0 then rhat2 else un21 - q0c * dHi
  -- Phase-2 1st D3 correction (delegated to phase2b_q0' which already
  -- has the rhat2c >>> 32 = 0 guard built-in).
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
  -- Phase-2 2nd D3 correction (unchanged from v4 — already guarded).
  let rhat2' :=
    if rhat2c >>> (32 : BitVec 6).toNat = 0 then
      let qDlo2 := q0c * dLo
      let rhatUn0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
      if BitVec.ult rhatUn0 qDlo2 then rhat2c + dHi else rhat2c
    else rhat2c
  let q0'' := div128Quot_phase2b_q0' q0' rhat2' dLo div_un0
  (q1'' <<< (32 : BitVec 6).toNat) ||| q0''

/-- Borrow condition for n=1 call+skip with the fully-corrected v5
    trial quotient: mulsub does not overflow. Mirror of
    `isSkipBorrowN1CallV4` using `div128Quot_v5`. -/
def isSkipBorrowN1CallV5 (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := div128Quot_v5 u1 u0 v0
  (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word)

-- ============================================================================
-- n=1 per-digit iteration over the v5 (capped) trial quotient
--
-- Mirror of `iterN1Call` / `iterN1Max` / `iterN1` (LoopDefs/Iter.lean), swapping
-- the call-path trial from `div128Quot` to `div128Quot_v5`. The max path uses
-- the saturated `signExtend12 4095` constant and is version-agnostic. These are
-- the building blocks for the v5 n=1 schoolbook `fullDivN1*V5` (bead 9.1).
-- ============================================================================

/-- v5 n=1 call-path iteration: trial = `div128Quot_v5 u1 u0 v0`. -/
@[irreducible] def iterN1Call_v5 (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- v5 n=1 max-path iteration (saturated trial; version-agnostic). -/
@[irreducible] def iterN1Max_v5 (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- v5 n=1 per-digit iteration dispatched on the call/max branch. -/
def iterN1V5 (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  else iterN1Max_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[simp]
theorem iterN1V5_true {v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    iterN1V5 true v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp [iterN1V5]

@[simp]
theorem iterN1V5_false {v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    iterN1V5 false v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    iterN1Max_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp [iterN1V5]

/-- Call-path n=1 v5 carry-zero reducer for a zero incoming top limb. -/
theorem iterN1V5_true_carry_zero_of_mulsub_c3_zero
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hc3 : mulsubN4_c3 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 = 0)
    (huTop : uTop = 0) :
    (iterN1V5 true v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2 = 0 := by
  rw [iterN1V5_true]
  unfold iterN1Call_v5
  exact iterWithDoubleAddback_carry_zero_of_mulsub_c3_zero
    (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop hc3 huTop

/-- Max-path n=1 v5 carry-zero reducer for a zero incoming top limb. -/
theorem iterN1V5_false_carry_zero_of_mulsub_c3_zero
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hc3 : mulsubN4_c3 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 = 0)
    (huTop : uTop = 0) :
    (iterN1V5 false v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2 = 0 := by
  rw [iterN1V5_false]
  unfold iterN1Max_v5
  exact iterWithDoubleAddback_carry_zero_of_mulsub_c3_zero
    (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 uTop hc3 huTop

end EvmAsm.Evm64
