/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Algorithm

  v5 analog of `CallSkipLowerBoundV4/Algorithm.lean`. Provides named
  `_unfold` lemmas for the v5 trial-call algorithm's irreducible
  intermediate Word values, alongside three algorithm-level bundle
  aliases (`algorithmUn21V5`, `algorithmQ1PrimeV5`, `algorithmQ0PrimeV5`)
  that match the role of `algorithmQ1Prime` from v1/v2 chains.

  Foundational for V5.4 (UB) and V5.5 (LB) proof chains under bead
  `evm-asm-wbc4i.4.6` (filed 2026-05-28 as the V5.4.0 prerequisite).

  v5 vs v4 differences (recap from `IterV5.lean` and `TrialCallV5.lean`):
  - Phase-1a `q1c` capped at `0xFFFFFFFF`; `rhatc := uHi - q1c*dHi`.
  - Phase-1b 1st correction guarded by `decide (rhatc >>> 32 = 0) && BLTU`.
  - Phase-2a `q0c` analogously capped; `rhat2c := un21 - q0c*dHi`.
-/

import EvmAsm.Evm64.DivMod.LoopBody.TrialCallV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The v5 algorithm's `un21` output as a function of `(uHi, uLo, vTop)`.
    Named bundle alias for `divKTrialCallV5Un21`. -/
@[irreducible]
def algorithmUn21V5 (uHi uLo vTop : Word) : Word :=
  divKTrialCallV5Un21 uHi uLo vTop

/-- The v5 algorithm's Phase-1b output `q1''`. Named bundle alias for
    `divKTrialCallV5Q1dd`. -/
@[irreducible]
def algorithmQ1PrimeV5 (uHi uLo vTop : Word) : Word :=
  divKTrialCallV5Q1dd uHi uLo vTop

/-- The v5 algorithm's Phase-2 output `q0''`. Named bundle alias for
    `divKTrialCallV5Q0dd`. -/
@[irreducible]
def algorithmQ0PrimeV5 (uHi uLo vTop : Word) : Word :=
  divKTrialCallV5Q0dd uHi uLo vTop

/-- Named unfold for `divKTrialCallV5Un21`. -/
theorem divKTrialCallV5Un21_unfold (uHi uLo vTop : Word) :
    divKTrialCallV5Un21 uHi uLo vTop =
      (let un1 := divKTrialCallV5Un1 uLo
       let q1'' := divKTrialCallV5Q1dd uHi uLo vTop
       let rhat'' := divKTrialCallV5Rhatdd uHi uLo vTop
       let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| un1
       let cu_q1_dlo := q1'' * divKTrialCallV5DLo vTop
       cu_rhat_un1 - cu_q1_dlo) := by
  delta divKTrialCallV5Un21; rfl

-- ============================================================================
-- Phase-1a + Phase-1b-fire-guard algorithm bundles for V5.
-- Bead `evm-asm-wbc4i.4.6.1` (V5.4.0.2).
--
-- v5 vs v4 differences here:
-- * `algorithmQ1cV5` uses the cap `q1cCap = 0xFFFFFFFF` (vs v4's
--   `q1 - 1`).
-- * `algorithmRhatcV5` is recomputed as `uHi - q1c * dHi` (vs v4's
--   `rhat + dHi`).
-- * `algorithmPhase1bFireV5` adds the `rhatc >>> 32 = 0` guard
--   (matching the existing 2nd-correction and Phase-2-helper guards).
-- ============================================================================

/-- The V5 Phase-1a-corrected quotient (before the first Phase-1b dLo
    check). Uses the cap `0xFFFFFFFF` when `hi1 ≠ 0`. -/
@[irreducible]
def algorithmQ1cV5 (uHi vTop : Word) : Word :=
  let dHi := divKTrialCallV5DHi vTop
  let q1 := rv64_divu uHi dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  if hi1 = 0 then q1 else q1cCap

/-- The V5 Phase-1a-corrected remainder. Recomputed from `uHi - q1c*dHi`
    (not `rhat + dHi` as in v4). -/
@[irreducible]
def algorithmRhatcV5 (uHi vTop : Word) : Word :=
  let dHi := divKTrialCallV5DHi vTop
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  if hi1 = 0 then rhat else uHi - q1cCap * dHi

/-- The low 64-bit comparison word for the V5 first Phase-1b dLo check. -/
@[irreducible]
def algorithmRhatUn1cV5 (uHi uLo vTop : Word) : Word :=
  (algorithmRhatcV5 uHi vTop <<< (32 : BitVec 6).toNat) ||| divKTrialCallV5Un1 uLo

/-- The V5 first Phase-1b dLo correction guard. Differs from v4 by the
    additional `rhatc >>> 32 = 0` precondition that gates the BLTU. -/
@[irreducible]
def algorithmPhase1bFireV5 (uHi uLo vTop : Word) : Prop :=
  algorithmRhatcV5 uHi vTop >>> (32 : BitVec 6).toNat = 0 ∧
    BitVec.ult (algorithmRhatUn1cV5 uHi uLo vTop)
      (algorithmQ1cV5 uHi vTop * divKTrialCallV5DLo vTop)

/-- Named unfold for `algorithmQ1cV5`. -/
theorem algorithmQ1cV5_unfold (uHi vTop : Word) :
    algorithmQ1cV5 uHi vTop =
      (let dHi := divKTrialCallV5DHi vTop
       let q1 := rv64_divu uHi dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
       if hi1 = 0 then q1 else q1cCap) := by
  delta algorithmQ1cV5; rfl

/-- Named unfold for `algorithmRhatcV5`. -/
theorem algorithmRhatcV5_unfold (uHi vTop : Word) :
    algorithmRhatcV5 uHi vTop =
      (let dHi := divKTrialCallV5DHi vTop
       let q1 := rv64_divu uHi dHi
       let rhat := uHi - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
       if hi1 = 0 then rhat else uHi - q1cCap * dHi) := by
  delta algorithmRhatcV5; rfl

/-- Named unfold for `algorithmRhatUn1cV5`. -/
theorem algorithmRhatUn1cV5_unfold (uHi uLo vTop : Word) :
    algorithmRhatUn1cV5 uHi uLo vTop =
      ((algorithmRhatcV5 uHi vTop <<< (32 : BitVec 6).toNat) |||
        divKTrialCallV5Un1 uLo) := by
  delta algorithmRhatUn1cV5; rfl

/-- Named unfold for `algorithmPhase1bFireV5`. -/
theorem algorithmPhase1bFireV5_unfold (uHi uLo vTop : Word) :
    algorithmPhase1bFireV5 uHi uLo vTop ↔
      algorithmRhatcV5 uHi vTop >>> (32 : BitVec 6).toNat = 0 ∧
        BitVec.ult (algorithmRhatUn1cV5 uHi uLo vTop)
          (algorithmQ1cV5 uHi vTop * divKTrialCallV5DLo vTop) := by
  delta algorithmPhase1bFireV5; rfl

-- ============================================================================
-- Phase-2a algorithm bundles for V5. Bead `evm-asm-wbc4i.4.6.2` (V5.4.0.3).
--
-- v5 vs v4 differences (same shape as Phase-1a):
-- * `algorithmQ0cV5` uses cap `0xFFFFFFFF` (vs v4's `q0 - 1`).
-- * `algorithmRhat2cV5` recomputed as `un21 - q0c*dHi` (vs v4's `rhat2 + dHi`).
-- ============================================================================

/-- The V5 Phase-2a-corrected quotient (before any Phase-2b correction). -/
@[irreducible]
def algorithmQ0cV5 (uHi uLo vTop : Word) : Word :=
  let dHi := divKTrialCallV5DHi vTop
  let un21 := divKTrialCallV5Un21 uHi uLo vTop
  let q0 := rv64_divu un21 dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  if hi2 = 0 then q0 else q0cCap

/-- The V5 Phase-2a-corrected remainder. Recomputed from `un21 - q0c*dHi`. -/
@[irreducible]
def algorithmRhat2cV5 (uHi uLo vTop : Word) : Word :=
  let dHi := divKTrialCallV5DHi vTop
  let un21 := divKTrialCallV5Un21 uHi uLo vTop
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  if hi2 = 0 then rhat2 else un21 - q0cCap * dHi

/-- Named unfold for `algorithmQ0cV5`. -/
theorem algorithmQ0cV5_unfold (uHi uLo vTop : Word) :
    algorithmQ0cV5 uHi uLo vTop =
      (let dHi := divKTrialCallV5DHi vTop
       let un21 := divKTrialCallV5Un21 uHi uLo vTop
       let q0 := rv64_divu un21 dHi
       let hi2 := q0 >>> (32 : BitVec 6).toNat
       let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
       if hi2 = 0 then q0 else q0cCap) := by
  delta algorithmQ0cV5; rfl

/-- Named unfold for `algorithmRhat2cV5`. -/
theorem algorithmRhat2cV5_unfold (uHi uLo vTop : Word) :
    algorithmRhat2cV5 uHi uLo vTop =
      (let dHi := divKTrialCallV5DHi vTop
       let un21 := divKTrialCallV5Un21 uHi uLo vTop
       let q0 := rv64_divu un21 dHi
       let rhat2 := un21 - q0 * dHi
       let hi2 := q0 >>> (32 : BitVec 6).toNat
       let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
       if hi2 = 0 then rhat2 else un21 - q0cCap * dHi) := by
  delta algorithmRhat2cV5; rfl

/-- The V5 `Q0c` irreducible coincides with the algorithm bundle
    (sanity check; bodies are definitionally equal). -/
theorem divKTrialCallV5Q0c_eq_algorithm (uHi uLo vTop : Word) :
    divKTrialCallV5Q0c uHi uLo vTop = algorithmQ0cV5 uHi uLo vTop := by
  delta divKTrialCallV5Q0c algorithmQ0cV5; rfl

/-- The V5 `Rhat2c` irreducible coincides with the algorithm bundle. -/
theorem divKTrialCallV5Rhat2c_eq_algorithm (uHi uLo vTop : Word) :
    divKTrialCallV5Rhat2c uHi uLo vTop = algorithmRhat2cV5 uHi uLo vTop := by
  delta divKTrialCallV5Rhat2c algorithmRhat2cV5; rfl

end EvmAsm.Evm64
