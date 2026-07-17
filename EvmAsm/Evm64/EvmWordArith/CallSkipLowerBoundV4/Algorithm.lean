/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Algorithm

  Named `_unfold` lemmas for the v4 div128 trial-call algorithm's
  irreducible intermediate Word values. v4 analogue of
  `EvmWordArith.CallSkipLowerBoundV2.Algorithm`, but operating on the
  existing v4 irreducible defs in
  `EvmAsm.Evm64.DivMod.LoopBody.TrialCall` (`divKTrialCallV4Q1dd`,
  `divKTrialCallV4Rhatdd`, `divKTrialCallV4Un21`, `divKTrialCallV4Q0dd`,
  `divKTrialCallV4QHat`) rather than introducing fresh parallel
  bundles. The v1 file duplicated the let-chain via separate
  `algorithmUn21` / `algorithmQ1Prime` / `algorithmQ0Prime` defs; for
  v4 the algorithm defs already exist as `@[irreducible]` in
  `LoopBody/TrialCall.lean`, so we just provide named unfolds.

  These `_unfold` lemmas are the bridge consumers (Knuth-A lower bound
  for v4, exact 128/64 quotient equality) use to expose the algorithm
  structure when needed, while keeping the `@[irreducible]` discipline
  outside the proof bodies.

  Bead `evm-asm-9iqmw.7.1.3.1.1.1`. Foundational slice for the v4
  Knuth-A lower bound (umbrella bead `7.1.3.1.1`).
-/

import EvmAsm.Evm64.DivMod.LoopBody.TrialCall

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The v4 algorithm's `un21` output as a function of `(uHi, uLo, vTop)`.

    This is a named bundle alias for the existing source-of-truth v4
    trial-call definition. It mirrors `algorithmUn21` from the v2 lower-bound
    development while preserving the single implementation in
    `DivMod.LoopBody.TrialCall`. -/
@[irreducible]
def algorithmUn21V4 (uHi uLo vTop : Word) : Word :=
  divKTrialCallV4Un21 uHi uLo vTop

/-- The v4 algorithm's Phase-1b output `q1''`.

    Named bundle alias for `divKTrialCallV4Q1dd`, matching the role of
    `algorithmQ1Prime` in the v2 proof chain. -/
@[irreducible]
def algorithmQ1PrimeV4 (uHi uLo vTop : Word) : Word :=
  divKTrialCallV4Q1dd uHi uLo vTop

/-- The v4 algorithm's Phase-2 output `q0''`.

    Named bundle alias for `divKTrialCallV4Q0dd`, matching the role of
    `algorithmQ0Prime` in the v2 proof chain. -/
@[irreducible]
def algorithmQ0PrimeV4 (uHi uLo vTop : Word) : Word :=
  divKTrialCallV4Q0dd uHi uLo vTop

/-- Named unfold for `divKTrialCallV4Q1dd`: q1'' after Knuth's classical
    2-correction in Phase-1b. The full 14-step let-chain:
    Phase-1a (`q1`, `rhat`, `hi1`), Phase-1a correction (`q1c`, `rhatc`),
    Phase-1b 1st correction (`q1'`, `rhat'`), Phase-1b 2nd correction
    (guarded by `rhatHi2 = 0` ∧ `BLTU rhatUn1' qDlo2`). -/
theorem divKTrialCallV4Q1dd_unfold (uHi uLo vTop : Word) :
    divKTrialCallV4Q1dd uHi uLo vTop =
      (let dHi := divKTrialCallV4DHi vTop
       let dLo := divKTrialCallV4DLo vTop
       let un1 := divKTrialCallV4Un1 uLo
       let q1 := rv64_divu uHi dHi
       let rhat := uHi - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
       let rhatc := if hi1 = 0 then rhat else rhat + dHi
       let qDlo := q1c * dLo
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
       let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
       let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
       let rhatHi2 := rhat' >>> (32 : BitVec 6).toNat
       let qDlo2 := q1' * dLo
       let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
       if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2 then q1' + signExtend12 4095 else q1') := by
  delta divKTrialCallV4Q1dd; rfl

/-- Named unfold for `divKTrialCallV4Un21`: half-word combine + Q1dd
    subtraction over the Phase-1b 2-correction outputs. -/
theorem divKTrialCallV4Un21_unfold (uHi uLo vTop : Word) :
    divKTrialCallV4Un21 uHi uLo vTop =
      (let un1 := divKTrialCallV4Un1 uLo
       let q1'' := divKTrialCallV4Q1dd uHi uLo vTop
       let rhat'' := divKTrialCallV4Rhatdd uHi uLo vTop
       let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| un1
       let cu_q1_dlo := q1'' * divKTrialCallV4DLo vTop
       cu_rhat_un1 - cu_q1_dlo) := by
  delta divKTrialCallV4Un21; rfl

/-- Named unfold for `divKTrialCallV4Q0dd`: q0'' after Knuth's classical
    2-correction in Phase-2 (the v4 enhancement over v2/v3 — Phase-2 1st
    correction `Q0d` further refined by the 2nd-correction guard
    `Rhat2d`). -/
theorem divKTrialCallV4Q0dd_unfold (uHi uLo vTop : Word) :
    divKTrialCallV4Q0dd uHi uLo vTop =
      div128Quot_phase2b_q0'
        (divKTrialCallV4Q0d uHi uLo vTop)
        (divKTrialCallV4Rhat2d uHi uLo vTop)
        (divKTrialCallV4DLo vTop)
        (divKTrialCallV4Un0 uLo) := by
  delta divKTrialCallV4Q0dd; rfl

end EvmAsm.Evm64
