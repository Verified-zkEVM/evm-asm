/-
  EvmAsm.Evm64.DivMod.LoopBody.TrialCall

  Extracted from `LoopBody.lean` (Section 11b).

  `divK_trial_call_full_spec_within`: full trial-quotient call path —
  save j + trial load + BLTU taken + JAL + div128 — composing into a
  single base+448 → base+516 spec when `uHi < vTop`. Used by every
  `LoopBodyN{1..4}.lean` and `LoopIterN1.{Call,CallBeq}`.

  Also defines the `@[irreducible]` bundled postcondition
  `divKTrialCallFullPost` that callers see opaque (with a documented
  `unfold` at use sites).

  Uses public helpers from `LoopBody.lean`:
  - `lb_sub`, `lb_bltu_taken`, `lb_bltu_ntaken` (now public, made
    non-`private` for this split).
  - `divK_save_trial_load_spec_within`, `divK_trial_call_path_spec_within`.
-/

import EvmAsm.Evm64.DivMod.LoopBody.TrialCallPath
import EvmAsm.Evm64.DivMod.LoopBody.TrialCallHelpers
import EvmAsm.Evm64.DivMod.LoopBody.TrialMax

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Section 11b: Trial quotient call path (BLTU taken): save + load + BLTU + JAL + div128
-- When uHi < vTop, calls div128 to compute the trial quotient.
-- Entry: base+448, Exit: base+516, CodeReq: sharedDivModCode base.
-- ============================================================================

/-- Bundled postcondition for `divK_trial_call_full_spec_within` (#1139). Inlines
    the 30+ let chain so xperm / seqFrame see all atoms in one flat sepConj
    when bridging. Marked `@[irreducible]` so the theorem *signature* hides
    the bundle from consumers; call-sites that need per-limb atoms must
    `unfold divKTrialCallFullPost at TF` after invoking the spec. -/
@[irreducible]
def divKTrialCallFullPost (sp j n uHi uLo vTop base : Word) : Assertion :=
  let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
  let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0Div := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0Div
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0Div
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x9Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ x9Exit) ** regOwn .x1 **
  (.x5 ↦ᵣ q0') ** (.x6 ↦ᵣ dHi) **
  (.x7 ↦ᵣ x7Exit) ** (.x10 ↦ᵣ q1') ** (.x11 ↦ᵣ q) **
  (.x2 ↦ᵣ (base + div128CallRetOff)) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
  (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
  (vtopBase + signExtend12 32 ↦ₘ vTop) **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ vTop) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ un0Div)

@[irreducible]
def divKTrialCallV4DHi (vTop : Word) : Word :=
  vTop >>> (32 : BitVec 6).toNat

@[irreducible]
def divKTrialCallV4DLo (vTop : Word) : Word :=
  (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat

@[irreducible]
def divKTrialCallV4Un1 (uLo : Word) : Word :=
  uLo >>> (32 : BitVec 6).toNat

@[irreducible]
def divKTrialCallV4Un0 (uLo : Word) : Word :=
  (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat

@[irreducible]
def divKTrialCallV4Q1dd (uHi uLo vTop : Word) : Word :=
  let dHi := divKTrialCallV4DHi vTop
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
  if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2 then q1' + signExtend12 4095 else q1'

@[irreducible]
def divKTrialCallV4Rhatdd (uHi uLo vTop : Word) : Word :=
  let dHi := divKTrialCallV4DHi vTop
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
  if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'

@[irreducible]
def divKTrialCallV4Un21 (uHi uLo vTop : Word) : Word :=
  let un1 := divKTrialCallV4Un1 uLo
  let q1'' := divKTrialCallV4Q1dd uHi uLo vTop
  let rhat'' := divKTrialCallV4Rhatdd uHi uLo vTop
  let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| un1
  let cu_q1_dlo := q1'' * divKTrialCallV4DLo vTop
  cu_rhat_un1 - cu_q1_dlo

@[irreducible]
def divKTrialCallV4Rhat2c (uHi uLo vTop : Word) : Word :=
  let dHi := divKTrialCallV4DHi vTop
  let un21 := divKTrialCallV4Un21 uHi uLo vTop
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  if hi2 = 0 then rhat2 else rhat2 + dHi

@[irreducible]
def divKTrialCallV4Q0c (uHi uLo vTop : Word) : Word :=
  let dHi := divKTrialCallV4DHi vTop
  let un21 := divKTrialCallV4Un21 uHi uLo vTop
  let q0 := rv64_divu un21 dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  if hi2 = 0 then q0 else q0 + signExtend12 4095

@[irreducible]
def divKTrialCallV4Q0d (uHi uLo vTop : Word) : Word :=
  div128Quot_phase2b_q0'
    (divKTrialCallV4Q0c uHi uLo vTop)
    (divKTrialCallV4Rhat2c uHi uLo vTop)
    (divKTrialCallV4DLo vTop)
    (divKTrialCallV4Un0 uLo)

@[irreducible]
def divKTrialCallV4Rhat2d (uHi uLo vTop : Word) : Word :=
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un0Div := divKTrialCallV4Un0 uLo
  let q0c := divKTrialCallV4Q0c uHi uLo vTop
  let rhat2c := divKTrialCallV4Rhat2c uHi uLo vTop
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0Div
  if rhat2cHi = 0 then
    if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
  else rhat2c

@[irreducible]
def divKTrialCallV4Q0dd (uHi uLo vTop : Word) : Word :=
  div128Quot_phase2b_q0'
    (divKTrialCallV4Q0d uHi uLo vTop)
    (divKTrialCallV4Rhat2d uHi uLo vTop)
    (divKTrialCallV4DLo vTop)
    (divKTrialCallV4Un0 uLo)

@[irreducible]
def divKTrialCallV4QHat (uHi uLo vTop : Word) : Word :=
  (divKTrialCallV4Q1dd uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
    divKTrialCallV4Q0dd uHi uLo vTop

private theorem div128Quot_phase2b_q0'_and_form_legacy (q rhat dLo un : Word) :
    (if rhat >>> (32 : BitVec 6).toNat = 0 ∧
        BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo) then
      q + signExtend12 4095
    else q) = div128Quot_phase2b_q0' q rhat dLo un := by
  unfold div128Quot_phase2b_q0'
  by_cases h_hi : rhat >>> (32 : BitVec 6).toNat = (0 : Word)
  · by_cases h_ult : BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
    · rw [if_pos ⟨h_hi, h_ult⟩]
      rw [if_pos h_hi]
      rw [if_pos h_ult]
    · have h_and : ¬ (rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
          BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)) := by
        intro h
        exact h_ult h.2
      rw [if_neg h_and]
      rw [if_pos h_hi]
      rw [if_neg h_ult]
  · have h_and : ¬ (rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
        BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)) := by
      intro h
      exact h_hi h.1
    rw [if_neg h_and]
    rw [if_neg h_hi]

private theorem div128Quot_phase2b_rhat_and_form_legacy (q rhat dHi dLo un : Word) :
    (if rhat >>> (32 : BitVec 6).toNat = 0 ∧
        BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo) then
      rhat + dHi
    else rhat) =
      (if rhat >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q * dLo
        let rhatUn := (rhat <<< (32 : BitVec 6).toNat) ||| un
        if BitVec.ult rhatUn qDlo then rhat + dHi else rhat
      else rhat) := by
  by_cases h_hi : rhat >>> (32 : BitVec 6).toNat = (0 : Word)
  · by_cases h_ult : BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
    · rw [if_pos ⟨h_hi, h_ult⟩]
      rw [if_pos h_hi]
      rw [if_pos h_ult]
    · have h_and : ¬ (rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
          BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)) := by
        intro h
        exact h_ult h.2
      rw [if_neg h_and]
      rw [if_pos h_hi]
      rw [if_neg h_ult]
  · have h_and : ¬ (rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
        BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)) := by
      intro h
      exact h_hi h.1
    rw [if_neg h_and]
    rw [if_neg h_hi]

theorem divKTrialCallV4Q1dd_eq_phase2b (uHi uLo vTop : Word) :
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
       div128Quot_phase2b_q0' q1' rhat' dLo un1) := by
  unfold divKTrialCallV4Q1dd
  rw [div128Quot_phase2b_q0'_and_form]

theorem divKTrialCallV4Rhatdd_eq_phase2b (uHi uLo vTop : Word) :
    divKTrialCallV4Rhatdd uHi uLo vTop =
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
       if rhat' >>> (32 : BitVec 6).toNat = 0 then
         let qDlo2 := q1' * dLo
         let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
         if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
       else rhat') := by
  unfold divKTrialCallV4Rhatdd
  rw [div128Quot_phase2b_rhat_and_form]

theorem divKTrialCallV4QHat_eq_div128Quot_v4 (uHi uLo vTop : Word) :
    divKTrialCallV4QHat uHi uLo vTop = div128Quot_v4 uHi uLo vTop := by
  unfold divKTrialCallV4QHat divKTrialCallV4Q0dd divKTrialCallV4Q0d divKTrialCallV4Rhat2d
    divKTrialCallV4Q0c divKTrialCallV4Rhat2c divKTrialCallV4Un21
  rw [divKTrialCallV4Rhatdd_eq_phase2b]
  rw [divKTrialCallV4Q1dd_eq_phase2b]
  unfold div128Quot_v4 divKTrialCallV4DHi divKTrialCallV4DLo divKTrialCallV4Un1
    divKTrialCallV4Un0
  rfl

@[irreducible]
def divKTrialCallV4X7Exit (uHi uLo vTop : Word) : Word :=
  let dLo := divKTrialCallV4DLo vTop
  let un21 := divKTrialCallV4Un21 uHi uLo vTop
  let q0c := divKTrialCallV4Q0c uHi uLo vTop
  let q0' := divKTrialCallV4Q0d uHi uLo vTop
  let rhat2c := divKTrialCallV4Rhat2c uHi uLo vTop
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dLo
  let rhat2' := divKTrialCallV4Rhat2d uHi uLo vTop
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let q0Dlo2 := q0' * dLo
  if rhat2cHi ≠ 0 then un21 else if rhat2'Hi ≠ 0 then q0Dlo1 else q0Dlo2

@[irreducible]
def divKTrialCallV4X9Exit (uHi uLo vTop : Word) : Word :=
  let un0Div := divKTrialCallV4Un0 uLo
  let rhat2c := divKTrialCallV4Rhat2c uHi uLo vTop
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let rhat2' := divKTrialCallV4Rhat2d uHi uLo vTop
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let rhat2'Un0 := (rhat2' <<< (32 : BitVec 6).toNat) ||| un0Div
  if rhat2cHi ≠ 0 then rhat2cHi else if rhat2'Hi ≠ 0 then rhat2'Hi else rhat2'Un0

@[irreducible]
def divKTrialCallV4ScratchOut (uHi uLo vTop scratchMem : Word) : Word :=
  let rhat2c := divKTrialCallV4Rhat2c uHi uLo vTop
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  if rhat2cHi ≠ 0 then scratchMem else rhat2c

theorem divKTrialCallV4DLo_eq (vTop : Word) :
    divKTrialCallV4DLo vTop =
      (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat := by
  unfold divKTrialCallV4DLo
  rfl

theorem divKTrialCallV4Un0_eq (uLo : Word) :
    divKTrialCallV4Un0 uLo =
      (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat := by
  unfold divKTrialCallV4Un0
  rfl

theorem divKTrialCallV4ScratchOut_eq
    (uHi uLo vTop scratchMem : Word) :
    divKTrialCallV4ScratchOut uHi uLo vTop scratchMem =
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let rhat := uHi - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      let qDlo := q1c * dLo
      let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
      let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
      let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      let rhatHi2 := rhat' >>> (32 : BitVec 6).toNat
      let qDlo2 := q1' * dLo
      let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
      let q1'' := if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2
                  then q1' + signExtend12 4095 else q1'
      let rhat'' := if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2
                    then rhat' + dHi else rhat'
      let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1
      let cu_q1_dlo := q1'' * dLo
      let un21 := cu_rhat_un1 - cu_q1_dlo
      let q0 := rv64_divu un21 dHi
      let rhat2 := un21 - q0 * dHi
      let hi2 := q0 >>> (32 : BitVec 6).toNat
      let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
      let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
      if rhat2cHi ≠ 0 then scratchMem else rhat2c := by
  unfold divKTrialCallV4ScratchOut divKTrialCallV4Rhat2c divKTrialCallV4Un21
    divKTrialCallV4Q1dd divKTrialCallV4Rhatdd divKTrialCallV4DHi
    divKTrialCallV4DLo divKTrialCallV4Un1
  rfl

/-- Bundled postcondition for the v4 trial-call path. This mirrors
    `divKTrialCallFullPost`, but tracks the extra v4 scratch cell and the
    second D3 correction values from `div128V4SpecPost`. -/
@[irreducible]
def divKTrialCallFullPostV4 (sp j n uHi uLo vTop base scratchMem : Word) : Assertion :=
  let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
  let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un0Div := divKTrialCallV4Un0 uLo
  let q1'' := divKTrialCallV4Q1dd uHi uLo vTop
  let q0'' := divKTrialCallV4Q0dd uHi uLo vTop
  let x7Exit := divKTrialCallV4X7Exit uHi uLo vTop
  let x9Exit := divKTrialCallV4X9Exit uHi uLo vTop
  let q := divKTrialCallV4QHat uHi uLo vTop
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ x9Exit) ** regOwn .x1 **
  (.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) **
  (.x7 ↦ᵣ x7Exit) ** (.x10 ↦ᵣ q1'') ** (.x11 ↦ᵣ q) **
  (.x2 ↦ᵣ (base + div128CallRetOff)) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
  (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
  (vtopBase + signExtend12 32 ↦ₘ vTop) **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ vTop) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ un0Div) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV4ScratchOut uHi uLo vTop scratchMem)

/-- Exact-x1 version of `divKTrialCallFullPostV4`, used by callable
    compositions that must preserve the caller return address concretely. -/
@[irreducible]
def divKTrialCallFullPostV4ExactX1
    (sp j n uHi uLo vTop base scratchMem raVal : Word) : Assertion :=
  let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
  let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un0Div := divKTrialCallV4Un0 uLo
  let q1'' := divKTrialCallV4Q1dd uHi uLo vTop
  let q0'' := divKTrialCallV4Q0dd uHi uLo vTop
  let x7Exit := divKTrialCallV4X7Exit uHi uLo vTop
  let x9Exit := divKTrialCallV4X9Exit uHi uLo vTop
  let q := divKTrialCallV4QHat uHi uLo vTop
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ x9Exit) ** (.x1 ↦ᵣ raVal) **
  (.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) **
  (.x7 ↦ᵣ x7Exit) ** (.x10 ↦ᵣ q1'') ** (.x11 ↦ᵣ q) **
  (.x2 ↦ᵣ (base + div128CallRetOff)) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
  (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
  (vtopBase + signExtend12 32 ↦ₘ vTop) **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ vTop) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ un0Div) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV4ScratchOut uHi uLo vTop scratchMem)

private theorem tc_lb_save_j {base : Word} :
    (base + loopBodyOff : Word) + 4 = base + (loopBodyOff + 4) := by
  simp [BitVec.add_assoc]
private theorem tc_lb_trial_load {base : Word} :
    (base + (loopBodyOff + 4) : Word) + 48 = base + trialCallOff := by bv_addr

/-- Save j + trial load over `sharedDivModCode_v4`: save j to memory, then
    load uHi, uLo, vTop for trial quotient. -/
private theorem divK_save_trial_load_v4_spec_within
    (sp j n jOld v5Old v6Old v7Old v10Old uHi uLo vTop : Word)
    (base : Word) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 13 (base + loopBodyOff) (base + trialCallOff) (sharedDivModCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) **
       (sp + signExtend12 3976 ↦ₘ jOld) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop))
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (sp + signExtend12 3976 ↦ₘ j) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop)) := by
  intro uAddr vtopBase
  have SJ := divK_save_j_spec_within sp j jOld (base + loopBodyOff)
  rw [tc_lb_save_j] at SJ
  have SJe := cpsTripleWithin_extend_code (hmono :=
    lb_sub_v4 0 _ _ (by decide) (by bv_addr) (by decide)) SJ
  have SJf := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
     (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) SJe
  have TL := divK_trial_load_spec_within sp j n v5Old v6Old v7Old v10Old uHi uLo vTop
    (base + (loopBodyOff + 4))
  dsimp only [] at TL
  rw [tc_lb_trial_load] at TL
  have TLe := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub_v4 1 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_v4 2 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_v4 3 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_v4 4 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_v4 5 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_v4 6 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_v4 7 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_v4 8 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_v4 9 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_v4 10 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_v4 11 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub_v4 12 _ _ (by decide) (by bv_addr) (by decide))))))))))))) TL
  seqFrame SJf TLe
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    SJfTLe

/-- Save j + trial load over `sharedDivModCodeNoNop_v4`: save j to memory,
    then load uHi, uLo, vTop for trial quotient. -/
private theorem divK_save_trial_load_v4_spec_within_noNop
    (sp j n jOld v5Old v6Old v7Old v10Old uHi uLo vTop : Word)
    (base : Word) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 13 (base + loopBodyOff) (base + trialCallOff) (sharedDivModCodeNoNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) **
       (sp + signExtend12 3976 ↦ₘ jOld) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop))
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
       (sp + signExtend12 3976 ↦ₘ j) **
       (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop)) := by
  intro uAddr vtopBase
  have SJ := divK_save_j_spec_within sp j jOld (base + loopBodyOff)
  rw [tc_lb_save_j] at SJ
  have SJe := cpsTripleWithin_extend_code (hmono :=
    lb_sub_noNop_v4 0 _ _ (by decide) (by bv_addr) (by decide)) SJ
  have SJf := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
     (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) SJe
  have TL := divK_trial_load_spec_within sp j n v5Old v6Old v7Old v10Old uHi uLo vTop
    (base + (loopBodyOff + 4))
  dsimp only [] at TL
  rw [tc_lb_trial_load] at TL
  have TLe := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub_noNop_v4 1 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v4 2 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v4 3 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v4 4 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v4 5 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v4 6 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v4 7 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v4 8 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v4 9 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v4 10 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v4 11 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub_noNop_v4 12 _ _ (by decide) (by bv_addr) (by decide))))))))))))) TL
  seqFrame SJf TLe
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    SJfTLe

/-- Trial quotient call path: save j + load + BLTU taken + JAL + div128.
    When uHi < vTop, computes qHat = div128(uHi, uLo, vTop).
    Entry: base+448, Exit: base+516, CodeReq: sharedDivModCode base. -/
theorem divK_trial_call_full_spec_within
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 66 (base + loopBodyOff) (base + div128CallRetOff) (sharedDivModCode base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem)) ** regOwn .x1)
      (divKTrialCallFullPost sp j n uHi uLo vTop base) := by
  intro uAddr vtopBase
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro v1Old
  -- Define the same lets locally so the proof body (unchanged from before
  -- bundling) can still reference q0', x1Exit, x7Exit, etc. by name. The
  -- goal's post stays `divKTrialCallFullPost ...` (opaque) throughout the
  -- intermediate `seqFrame` steps — keeping it opaque is what avoids the
  -- `maxRecDepth` blowup a naive `unfold`-at-start would hit.
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0Div := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0Div
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0Div
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  -- 1. Save j + trial load (base+448 → base+500)
  have STL := divK_save_trial_load_spec_within sp j n jOld v5Old v6Old v7Old v10Old uHi uLo vTop
    base
  dsimp only [] at STL
  -- 2. BLTU x7 x10 12 at base + trialCallOff
  have hbltu_raw := bltu_spec_gen_within .x7 .x10 (12 : BitVec 13) uHi vTop (base + trialCallOff)
  rw [lb_bltu_taken, lb_bltu_ntaken] at hbltu_raw
  have hbltu_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub 13 _ _ (by decide) (by bv_addr) (by decide)) hbltu_raw
  -- Eliminate ntaken path (⌜¬BitVec.ult uHi vTop⌝ contradicts hbltu)
  have taken := cpsBranchWithin_takenPath hbltu_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure hbltu)
  -- Strip pure fact from taken postcondition
  have taken_clean := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp) taken
  -- 3. Trial call path (base+512 → base+516)
  have TCP := divK_trial_call_path_spec_within_exact_x1 sp j uLo uHi vTop vtopBase base
    v1Old v2Old v11Old retMem dMem dloMem un0Mem
    halign
  unfold div128SpecPost at TCP
  -- 4. Frame save_trial_load with x1 (v1Old), x2, x11, x0, scratch memory
  have STLf := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) STL
  have taken_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) ** (.x1 ↦ᵣ v1Old) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x11 ↦ᵣ v11Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ j) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) taken_clean
  have TCPf := cpsTripleWithin_frameR
    ((sp + signExtend12 3976 ↦ₘ j) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) TCP
  -- 5. Compose save_trial_load + BLTU taken
  have STLf_taken_clean := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf taken_framed
  -- 6. Compose (save_trial_load + BLTU) + trial_call_path
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf_taken_clean TCPf
  -- 7. Final permutation — unfold the bundled post so xperm sees all atoms.
  unfold divKTrialCallFullPost
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    full

/-- Trial quotient call path over `sharedDivModCode_v4`: save j + load +
    BLTU taken + JAL + `divK_div128_v4`. -/
theorem divK_trial_call_full_v4_spec_within
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 88 (base + loopBodyOff) (base + div128CallRetOff) (sharedDivModCode_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** regOwn .x1)
      (divKTrialCallFullPostV4 sp j n uHi uLo vTop base scratchMem) := by
  intro uAddr vtopBase
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro v1Old
  have STL := divK_save_trial_load_v4_spec_within sp j n jOld v5Old v6Old v7Old v10Old uHi uLo vTop
    base
  dsimp only [] at STL
  have hbltu_raw := bltu_spec_gen_within .x7 .x10 (12 : BitVec 13) uHi vTop (base + trialCallOff)
  rw [lb_bltu_taken, lb_bltu_ntaken] at hbltu_raw
  have hbltu_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub_v4 13 _ _ (by decide) (by bv_addr) (by decide)) hbltu_raw
  have taken := cpsBranchWithin_takenPath hbltu_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure hbltu)
  have taken_clean := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp) taken
  have TCP := divK_trial_call_path_v4_spec_within_exact_x1 sp j uLo uHi vTop vtopBase base
    v1Old v2Old v11Old retMem dMem dloMem un0Mem scratchMem
    halign
  unfold div128V4SpecPost at TCP
  have STLf := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) STL
  have taken_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) ** (.x1 ↦ᵣ v1Old) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x11 ↦ᵣ v11Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ j) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) taken_clean
  have TCPf := cpsTripleWithin_frameR
    ((sp + signExtend12 3976 ↦ₘ j) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) TCP
  have STLf_taken_clean := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf taken_framed
  have STLf_taken_scratch := cpsTripleWithin_frameR
    (sp + signExtend12 3936 ↦ₘ scratchMem)
    (by pcFree) STLf_taken_clean
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf_taken_scratch TCPf
  unfold divKTrialCallFullPostV4
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      simp only [divKTrialCallV4DHi, divKTrialCallV4DLo, divKTrialCallV4Un1, divKTrialCallV4Un0,
        divKTrialCallV4Q1dd, divKTrialCallV4Rhatdd, divKTrialCallV4Un21,
        divKTrialCallV4Rhat2c, divKTrialCallV4Q0c, divKTrialCallV4Q0d,
        divKTrialCallV4Rhat2d, divKTrialCallV4Q0dd, divKTrialCallV4QHat,
        divKTrialCallV4X7Exit, divKTrialCallV4X9Exit, divKTrialCallV4ScratchOut]
      xperm_hyp hq)
    full

/-- Trial quotient call path over `divCode_noNop`: save j + load + BLTU
    taken + JAL + div128. -/
theorem divK_trial_call_full_spec_within_noNop
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 66 (base + loopBodyOff) (base + div128CallRetOff) (divCode_noNop base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem)) ** regOwn .x1)
      (divKTrialCallFullPost sp j n uHi uLo vTop base) := by
  intro uAddr vtopBase
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro v1Old
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0Div := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0Div
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0Div
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  have STL := divK_save_trial_load_spec_within_noNop sp j n jOld v5Old v6Old v7Old v10Old uHi uLo vTop
    base
  dsimp only [] at STL
  have hbltu_raw := bltu_spec_gen_within .x7 .x10 (12 : BitVec 13) uHi vTop (base + trialCallOff)
  rw [lb_bltu_taken, lb_bltu_ntaken] at hbltu_raw
  have hbltu_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub_noNop 13 _ _ (by decide) (by bv_addr) (by decide)) hbltu_raw
  have taken := cpsBranchWithin_takenPath hbltu_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure hbltu)
  have taken_clean := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp) taken
  have TCP := divK_trial_call_path_spec_within_noNop_exact_x1 sp j uLo uHi vTop vtopBase base
    v1Old v2Old v11Old retMem dMem dloMem un0Mem
    halign
  unfold div128SpecPost at TCP
  have STLf := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) STL
  have taken_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) ** (.x1 ↦ᵣ v1Old) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x11 ↦ᵣ v11Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ j) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) taken_clean
  have TCPf := cpsTripleWithin_frameR
    ((sp + signExtend12 3976 ↦ₘ j) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) TCP
  have STLf_taken_clean := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf taken_framed
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf_taken_clean TCPf
  unfold divKTrialCallFullPost
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    full

/-- Trial quotient call path over `sharedDivModCodeNoNop_v4`: save j +
    load + BLTU taken + JAL + `divK_div128_v4`. -/
theorem divK_trial_call_full_v4_spec_within_noNop
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 88 (base + loopBodyOff) (base + div128CallRetOff) (sharedDivModCodeNoNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** regOwn .x1)
      (divKTrialCallFullPostV4 sp j n uHi uLo vTop base scratchMem) := by
  intro uAddr vtopBase
  apply cpsTripleWithin_of_forall_regIs_to_regOwn
  intro v1Old
  have STL := divK_save_trial_load_v4_spec_within_noNop
    sp j n jOld v5Old v6Old v7Old v10Old uHi uLo vTop base
  dsimp only [] at STL
  have hbltu_raw := bltu_spec_gen_within .x7 .x10 (12 : BitVec 13) uHi vTop (base + trialCallOff)
  rw [lb_bltu_taken, lb_bltu_ntaken] at hbltu_raw
  have hbltu_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub_noNop_v4 13 _ _ (by decide) (by bv_addr) (by decide)) hbltu_raw
  have taken := cpsBranchWithin_takenPath hbltu_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure hbltu)
  have taken_clean := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp) taken
  have TCP := divK_trial_call_path_v4_spec_within_noNop_exact_x1
    sp j uLo uHi vTop vtopBase base v1Old v2Old v11Old
    retMem dMem dloMem un0Mem scratchMem halign
  unfold div128V4SpecPost at TCP
  have STLf := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) STL
  have taken_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) ** (.x1 ↦ᵣ v1Old) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x11 ↦ᵣ v11Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ j) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) taken_clean
  have TCPf := cpsTripleWithin_frameR
    ((sp + signExtend12 3976 ↦ₘ j) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) TCP
  have STLf_taken_clean := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf taken_framed
  have STLf_taken_scratch := cpsTripleWithin_frameR
    (sp + signExtend12 3936 ↦ₘ scratchMem)
    (by pcFree) STLf_taken_clean
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf_taken_scratch TCPf
  unfold divKTrialCallFullPostV4
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      simp only [divKTrialCallV4DHi, divKTrialCallV4DLo, divKTrialCallV4Un1, divKTrialCallV4Un0,
        divKTrialCallV4Q1dd, divKTrialCallV4Rhatdd, divKTrialCallV4Un21,
        divKTrialCallV4Rhat2c, divKTrialCallV4Q0c, divKTrialCallV4Q0d,
        divKTrialCallV4Rhat2d, divKTrialCallV4Q0dd, divKTrialCallV4QHat,
        divKTrialCallV4X7Exit, divKTrialCallV4X9Exit, divKTrialCallV4ScratchOut]
      xperm_hyp hq)
    full

/-- Exact-x1 version of `divK_trial_call_full_v4_spec_within_noNop`.
    This avoids hiding the caller return address behind `regOwn .x1`. -/
theorem divK_trial_call_full_v4_spec_within_noNop_exact_x1
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem scratchMem raVal : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 88 (base + loopBodyOff) (base + div128CallRetOff) (sharedDivModCodeNoNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ raVal))
      (divKTrialCallFullPostV4ExactX1 sp j n uHi uLo vTop base scratchMem raVal) := by
  intro uAddr vtopBase
  have STL := divK_save_trial_load_v4_spec_within_noNop
    sp j n jOld v5Old v6Old v7Old v10Old uHi uLo vTop base
  dsimp only [] at STL
  have hbltu_raw := bltu_spec_gen_within .x7 .x10 (12 : BitVec 13) uHi vTop (base + trialCallOff)
  rw [lb_bltu_taken, lb_bltu_ntaken] at hbltu_raw
  have hbltu_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub_noNop_v4 13 _ _ (by decide) (by bv_addr) (by decide)) hbltu_raw
  have taken := cpsBranchWithin_takenPath hbltu_ext (fun hp hQf => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
    exact hpure hbltu)
  have taken_clean := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp) taken
  have TCP := divK_trial_call_path_v4_spec_within_noNop_preserving_x1
    sp j uLo uHi vTop vtopBase base raVal v2Old v11Old
    retMem dMem dloMem un0Mem scratchMem halign
  unfold div128V4SpecPost at TCP
  have STLf := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raVal) ** (.x11 ↦ᵣ v11Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) STL
  have taken_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) ** (.x1 ↦ᵣ raVal) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x11 ↦ᵣ v11Old) ** (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ j) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ un0Mem))
    (by pcFree) taken_clean
  have TCPf := cpsTripleWithin_frameR
    ((sp + signExtend12 3976 ↦ₘ j) **
     (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) TCP
  have STLf_taken_clean := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf taken_framed
  have STLf_taken_scratch := cpsTripleWithin_frameR
    (sp + signExtend12 3936 ↦ₘ scratchMem)
    (by pcFree) STLf_taken_clean
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf_taken_scratch TCPf
  unfold divKTrialCallFullPostV4ExactX1
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      simp only [divKTrialCallV4DHi, divKTrialCallV4DLo, divKTrialCallV4Un1, divKTrialCallV4Un0,
        divKTrialCallV4Q1dd, divKTrialCallV4Rhatdd, divKTrialCallV4Un21,
        divKTrialCallV4Rhat2c, divKTrialCallV4Q0c, divKTrialCallV4Q0d,
        divKTrialCallV4Rhat2d, divKTrialCallV4Q0dd, divKTrialCallV4QHat,
        divKTrialCallV4X7Exit, divKTrialCallV4X9Exit, divKTrialCallV4ScratchOut]
      xperm_hyp hq)
    full

/-- Lift the v4 trial-call path over the DIV no-NOP v4 code bundle. -/
theorem divK_trial_call_full_v4_spec_within_divCode_noNop
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 88 (base + loopBodyOff) (base + div128CallRetOff) (divCode_noNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** regOwn .x1)
      (divKTrialCallFullPostV4 sp j n uHi uLo vTop base scratchMem) := by
  intro uAddr vtopBase
  exact cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
    (divK_trial_call_full_v4_spec_within_noNop sp j n jOld v5Old v6Old v7Old v10Old
      v11Old v2Old uHi uLo vTop retMem dMem dloMem un0Mem scratchMem base halign hbltu)

/-- Lift the v4 trial-call path over the MOD no-NOP v4 code bundle. -/
theorem divK_trial_call_full_v4_spec_within_modCode_noNop
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 88 (base + loopBodyOff) (base + div128CallRetOff) (modCode_noNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** regOwn .x1)
      (divKTrialCallFullPostV4 sp j n uHi uLo vTop base scratchMem) := by
  intro uAddr vtopBase
  exact cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4)
    (divK_trial_call_full_v4_spec_within_noNop sp j n jOld v5Old v6Old v7Old v10Old
      v11Old v2Old uHi uLo vTop retMem dMem dloMem un0Mem scratchMem base halign hbltu)

/-- Lift the v4 trial-call path over the full DIV v4 code bundle. -/
theorem divK_trial_call_full_v4_spec_within_divCode
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 88 (base + loopBodyOff) (base + div128CallRetOff) (divCode_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** regOwn .x1)
      (divKTrialCallFullPostV4 sp j n uHi uLo vTop base scratchMem) := by
  intro uAddr vtopBase
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_trial_call_full_v4_spec_within_divCode_noNop sp j n jOld v5Old v6Old v7Old v10Old
      v11Old v2Old uHi uLo vTop retMem dMem dloMem un0Mem scratchMem base halign hbltu)

/-- Lift the v4 trial-call path over the full MOD v4 code bundle. -/
theorem divK_trial_call_full_v4_spec_within_modCode
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 88 (base + loopBodyOff) (base + div128CallRetOff) (modCode_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** regOwn .x1)
      (divKTrialCallFullPostV4 sp j n uHi uLo vTop base scratchMem) := by
  intro uAddr vtopBase
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_trial_call_full_v4_spec_within_modCode_noNop sp j n jOld v5Old v6Old v7Old v10Old
      v11Old v2Old uHi uLo vTop retMem dMem dloMem un0Mem scratchMem base halign hbltu)

/-- Exact-x1 lift of the v4 trial-call path over the DIV no-NOP v4 code bundle. -/
theorem divK_trial_call_full_v4_spec_within_divCode_noNop_exact_x1
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem scratchMem raVal : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 88 (base + loopBodyOff) (base + div128CallRetOff) (divCode_noNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ raVal))
      (divKTrialCallFullPostV4ExactX1 sp j n uHi uLo vTop base scratchMem raVal) := by
  intro uAddr vtopBase
  exact cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
    (divK_trial_call_full_v4_spec_within_noNop_exact_x1 sp j n jOld v5Old v6Old v7Old v10Old
      v11Old v2Old uHi uLo vTop retMem dMem dloMem un0Mem scratchMem raVal base halign hbltu)

/-- Exact-x1 lift of the v4 trial-call path over the MOD no-NOP v4 code bundle. -/
theorem divK_trial_call_full_v4_spec_within_modCode_noNop_exact_x1
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem scratchMem raVal : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 88 (base + loopBodyOff) (base + div128CallRetOff) (modCode_noNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ raVal))
      (divKTrialCallFullPostV4ExactX1 sp j n uHi uLo vTop base scratchMem raVal) := by
  intro uAddr vtopBase
  exact cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4)
    (divK_trial_call_full_v4_spec_within_noNop_exact_x1 sp j n jOld v5Old v6Old v7Old v10Old
      v11Old v2Old uHi uLo vTop retMem dMem dloMem un0Mem scratchMem raVal base halign hbltu)

/-- Exact-x1 lift of the v4 trial-call path over the full DIV v4 code bundle. -/
theorem divK_trial_call_full_v4_spec_within_divCode_exact_x1
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem scratchMem raVal : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 88 (base + loopBodyOff) (base + div128CallRetOff) (divCode_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ raVal))
      (divKTrialCallFullPostV4ExactX1 sp j n uHi uLo vTop base scratchMem raVal) := by
  intro uAddr vtopBase
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_trial_call_full_v4_spec_within_divCode_noNop_exact_x1 sp j n jOld v5Old v6Old v7Old v10Old
      v11Old v2Old uHi uLo vTop retMem dMem dloMem un0Mem scratchMem raVal base halign hbltu)

/-- Exact-x1 lift of the v4 trial-call path over the full MOD v4 code bundle. -/
theorem divK_trial_call_full_v4_spec_within_modCode_exact_x1
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old v2Old uHi uLo vTop : Word)
    (retMem dMem dloMem un0Mem scratchMem raVal : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 88 (base + loopBodyOff) (base + div128CallRetOff) (modCode_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ un0Mem) **
       (sp + signExtend12 3936 ↦ₘ scratchMem)) ** (.x1 ↦ᵣ raVal))
      (divKTrialCallFullPostV4ExactX1 sp j n uHi uLo vTop base scratchMem raVal) := by
  intro uAddr vtopBase
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_trial_call_full_v4_spec_within_modCode_noNop_exact_x1 sp j n jOld v5Old v6Old v7Old v10Old
      v11Old v2Old uHi uLo vTop retMem dMem dloMem un0Mem scratchMem raVal base halign hbltu)


end EvmAsm.Evm64
