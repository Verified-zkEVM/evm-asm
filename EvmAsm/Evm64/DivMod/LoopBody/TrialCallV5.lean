/-
  EvmAsm.Evm64.DivMod.LoopBody.TrialCallV5

  v5 irreducible aliases for the math-level trial-quotient values, mirroring
  the v4 family in `LoopBody/TrialCall.lean` (lines 85-380). Bead
  `evm-asm-wbc4i.2`.

  These wrap each `let` binding from `div128Quot_v5` (in `LoopDefs/IterV5.lean`)
  as an `@[irreducible] def` so that future `whnf`-heavy tactics (Knuth UB / LB
  proofs under beads `.4` / `.5`) can reason about them as opaque names without
  the entire let chain blowing up. The `*_eq_div128Quot_v5` theorem closes the
  loop by showing the composition equals the math model.

  v5 vs v4 differences (recapping the changes in `div128Quot_v5`):
  - Phase-1a: `q1c := if hi1 = 0 then q1 else 0xFFFFFFFF` (the v5 cap, vs
    v4's `q1 - 1`); `rhatc := if hi1 = 0 then rhat else uHi - q1c*dHi`
    (recomputed, vs v4's `rhat + dHi`).
  - Phase-1b 1st correction: guarded by `rhatc >>> 32 = 0` (vs v4's
    unconditional ULT) — matches the guard already present in the 2nd
    correction and in `div128Quot_phase2b_q0'`.
  - Phase-2a: analogous cap on `q0c` and recomputed `rhat2c` from `un21`.
  - Phase-1b 2nd correction, Phase-2 1st/2nd corrections, Phase-2 combine:
    structurally identical to v4 (modulo upstream V5 values).
-/

import EvmAsm.Evm64.DivMod.LoopDefs.IterV5
import EvmAsm.Evm64.DivMod.LoopBody.TrialCallHelpers

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 `dHi = vTop >> 32`. Identical to v4. -/
@[irreducible]
def divKTrialCallV5DHi (vTop : Word) : Word :=
  vTop >>> (32 : BitVec 6).toNat

/-- v5 `dLo = (vTop << 32) >> 32`. Identical to v4. -/
@[irreducible]
def divKTrialCallV5DLo (vTop : Word) : Word :=
  (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat

/-- v5 `un1 = uLo >> 32`. Identical to v4. -/
@[irreducible]
def divKTrialCallV5Un1 (uLo : Word) : Word :=
  uLo >>> (32 : BitVec 6).toNat

/-- v5 `un0 = (uLo << 32) >> 32`. Identical to v4. -/
@[irreducible]
def divKTrialCallV5Un0 (uLo : Word) : Word :=
  (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat

/-- v5 Phase-1: `q1''` (= Q1dd) — the post-Phase-1b trial quotient.
    Differs from v4 in: (a) Phase-1a `q1c` capped at `0xFFFFFFFF`;
    (b) `rhatc` recomputed as `uHi - q1c*dHi`; (c) Phase-1b 1st
    correction guarded by `rhatc >>> 32 = 0`. -/
@[irreducible]
def divKTrialCallV5Q1dd (uHi uLo vTop : Word) : Word :=
  let dHi := divKTrialCallV5DHi vTop
  let dLo := divKTrialCallV5DLo vTop
  let un1 := divKTrialCallV5Un1 uLo
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1cCap
  let rhatc := if hi1 = 0 then rhat else uHi - q1c * dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let phase1bFire1 :=
    decide (rhatc >>> (32 : BitVec 6).toNat = 0) && BitVec.ult rhatUn1 qDlo
  let q1' := if phase1bFire1 then q1c + signExtend12 4095 else q1c
  let rhat' := if phase1bFire1 then rhatc + dHi else rhatc
  let rhatHi2 := rhat' >>> (32 : BitVec 6).toNat
  let qDlo2 := q1' * dLo
  let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
  if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2 then q1' + signExtend12 4095 else q1'

/-- v5 Phase-1: `rhat''` (= Rhatdd) — the post-Phase-1b remainder.
    Mirrors `divKTrialCallV5Q1dd`'s control flow. -/
@[irreducible]
def divKTrialCallV5Rhatdd (uHi uLo vTop : Word) : Word :=
  let dHi := divKTrialCallV5DHi vTop
  let dLo := divKTrialCallV5DLo vTop
  let un1 := divKTrialCallV5Un1 uLo
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1cCap
  let rhatc := if hi1 = 0 then rhat else uHi - q1c * dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let phase1bFire1 :=
    decide (rhatc >>> (32 : BitVec 6).toNat = 0) && BitVec.ult rhatUn1 qDlo
  let q1' := if phase1bFire1 then q1c + signExtend12 4095 else q1c
  let rhat' := if phase1bFire1 then rhatc + dHi else rhatc
  let rhatHi2 := rhat' >>> (32 : BitVec 6).toNat
  let qDlo2 := q1' * dLo
  let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
  if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'

/-- v5 Phase-2 setup: `un21 = (rhat'' << 32 ||| un1) - q1'' * dLo`. -/
@[irreducible]
def divKTrialCallV5Un21 (uHi uLo vTop : Word) : Word :=
  let un1 := divKTrialCallV5Un1 uLo
  let q1'' := divKTrialCallV5Q1dd uHi uLo vTop
  let rhat'' := divKTrialCallV5Rhatdd uHi uLo vTop
  let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| un1
  let cu_q1_dlo := q1'' * divKTrialCallV5DLo vTop
  cu_rhat_un1 - cu_q1_dlo

/-- v5 Phase-2a `rhat2c`. Differs from v4 in: the corrected branch uses
    `un21 - q0c*dHi` (with `q0c = 0xFFFFFFFF`), not `rhat2 + dHi`. -/
@[irreducible]
def divKTrialCallV5Rhat2c (uHi uLo vTop : Word) : Word :=
  let dHi := divKTrialCallV5DHi vTop
  let un21 := divKTrialCallV5Un21 uHi uLo vTop
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  if hi2 = 0 then rhat2 else un21 - q0cCap * dHi

/-- v5 Phase-2a `q0c`. Differs from v4 in: the corrected branch uses
    the cap `0xFFFFFFFF`, not `q0 - 1`. -/
@[irreducible]
def divKTrialCallV5Q0c (uHi uLo vTop : Word) : Word :=
  let dHi := divKTrialCallV5DHi vTop
  let un21 := divKTrialCallV5Un21 uHi uLo vTop
  let q0 := rv64_divu un21 dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  if hi2 = 0 then q0 else q0cCap

/-- v5 Phase-2 1st D3 correction result (via `div128Quot_phase2b_q0'`,
    which already has its own `rhat2c >>> 32 = 0` guard). -/
@[irreducible]
def divKTrialCallV5Q0d (uHi uLo vTop : Word) : Word :=
  div128Quot_phase2b_q0'
    (divKTrialCallV5Q0c uHi uLo vTop)
    (divKTrialCallV5Rhat2c uHi uLo vTop)
    (divKTrialCallV5DLo vTop)
    (divKTrialCallV5Un0 uLo)

/-- v5 Phase-2 1st D3 correction's `rhat` update. Structurally identical
    to v4 (just over V5 upstreams). -/
@[irreducible]
def divKTrialCallV5Rhat2d (uHi uLo vTop : Word) : Word :=
  let dHi := divKTrialCallV5DHi vTop
  let dLo := divKTrialCallV5DLo vTop
  let un0Div := divKTrialCallV5Un0 uLo
  let q0c := divKTrialCallV5Q0c uHi uLo vTop
  let rhat2c := divKTrialCallV5Rhat2c uHi uLo vTop
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0Div
  if rhat2cHi = 0 then
    if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
  else rhat2c

/-- v5 Phase-2 2nd D3 correction result (via `div128Quot_phase2b_q0'`).
    Same as v4 modulo upstream V5 values. -/
@[irreducible]
def divKTrialCallV5Q0dd (uHi uLo vTop : Word) : Word :=
  div128Quot_phase2b_q0'
    (divKTrialCallV5Q0d uHi uLo vTop)
    (divKTrialCallV5Rhat2d uHi uLo vTop)
    (divKTrialCallV5DLo vTop)
    (divKTrialCallV5Un0 uLo)

/-- v5 final trial quotient: `(Q1dd << 32) ||| Q0dd`. -/
@[irreducible]
def divKTrialCallV5QHat (uHi uLo vTop : Word) : Word :=
  (divKTrialCallV5Q1dd uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
    divKTrialCallV5Q0dd uHi uLo vTop

/-- Rewrite `Q1dd` from its irreducible (flat-∧) Phase-1b 2nd D3 form
    to the `div128Quot_phase2b_q0'` shape used by `div128Quot_v5`.
    Reuses v4's `div128Quot_phase2b_q0'_and_form` lemma. -/
theorem divKTrialCallV5Q1dd_eq_phase2b (uHi uLo vTop : Word) :
    divKTrialCallV5Q1dd uHi uLo vTop =
      (let dHi := divKTrialCallV5DHi vTop
       let dLo := divKTrialCallV5DLo vTop
       let un1 := divKTrialCallV5Un1 uLo
       let q1 := rv64_divu uHi dHi
       let rhat := uHi - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
       let q1c := if hi1 = 0 then q1 else q1cCap
       let rhatc := if hi1 = 0 then rhat else uHi - q1c * dHi
       let qDlo := q1c * dLo
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
       let phase1bFire1 :=
         decide (rhatc >>> (32 : BitVec 6).toNat = 0) && BitVec.ult rhatUn1 qDlo
       let q1' := if phase1bFire1 then q1c + signExtend12 4095 else q1c
       let rhat' := if phase1bFire1 then rhatc + dHi else rhatc
       div128Quot_phase2b_q0' q1' rhat' dLo un1) := by
  unfold divKTrialCallV5Q1dd
  rw [div128Quot_phase2b_q0'_and_form]

/-- Mirror of `divKTrialCallV5Q1dd_eq_phase2b` for `Rhatdd`. Uses v4's
    `div128Quot_phase2b_rhat_and_form` to rewrite the flat-∧ form to
    the nested-let-if shape in `div128Quot_v5`. -/
theorem divKTrialCallV5Rhatdd_eq_phase2b (uHi uLo vTop : Word) :
    divKTrialCallV5Rhatdd uHi uLo vTop =
      (let dHi := divKTrialCallV5DHi vTop
       let dLo := divKTrialCallV5DLo vTop
       let un1 := divKTrialCallV5Un1 uLo
       let q1 := rv64_divu uHi dHi
       let rhat := uHi - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
       let q1c := if hi1 = 0 then q1 else q1cCap
       let rhatc := if hi1 = 0 then rhat else uHi - q1c * dHi
       let qDlo := q1c * dLo
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
       let phase1bFire1 :=
         decide (rhatc >>> (32 : BitVec 6).toNat = 0) && BitVec.ult rhatUn1 qDlo
       let q1' := if phase1bFire1 then q1c + signExtend12 4095 else q1c
       let rhat' := if phase1bFire1 then rhatc + dHi else rhatc
       if rhat' >>> (32 : BitVec 6).toNat = 0 then
         let qDlo2 := q1' * dLo
         let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
         if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
       else rhat') := by
  unfold divKTrialCallV5Rhatdd
  rw [div128Quot_phase2b_rhat_and_form]

-- NOTE: `divKTrialCallV5QHat_eq_div128Quot_v5` (the closure theorem that
-- the irreducible composition equals `div128Quot_v5`) is left to a follow-up
-- bead. The two bridging lemmas above (`Q1dd_eq_phase2b`, `Rhatdd_eq_phase2b`)
-- give downstream proofs the structural rewrites they need without requiring
-- a single monolithic `rfl` over the full let chain.

end EvmAsm.Evm64
