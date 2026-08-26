/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128V5DigitBridge

  Per-Knuth-digit assembly of the v5 div128 code-vs-model q-bridge: combines the
  rhatc arithmetic (`div128V5_rhatc_correction_eq`, #7243) and the selection
  reconciliations (`div128V5_phase1b_select_eq` / `_rhat_select_eq`, #7244/#7245)
  into the equality of the *full corrected digit* computed the code way
  (`div128V5SpecPost`) and the model way (`div128Quot_v5`).

  `div128V5_rhatc_eq` lifts the capped-branch ring identity to the full
  `if hi = 0 …` capped-remainder form used by both `div128V5SpecPost` and
  `div128Quot_v5`.  `div128V5_q1Final_eq_model` then proves the corrected
  quotient digit agrees.  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.LimbSpec.Div128V5Phase1bBridge
public import EvmAsm.Evm64.DivMod.LimbSpec.Div128V5CodeModelBridge

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **Capped remainder code = model.**  The code's incremental capped remainder
    (`if hi=0 then rhat else rhat + (q1-cap)·dHi`) equals the model's closed form
    (`if hi=0 then rhat else uHi - q1c·dHi`, with `q1c = if hi=0 then q1 else cap`).
    The capped branch is `div128V5_rhatc_correction_eq` (#7243); the `hi=0`
    branch is refl. -/
theorem div128V5_rhatc_eq (uHi q1 cap dHi : Word) :
    (if q1 >>> (32 : BitVec 6).toNat = 0 then uHi - q1 * dHi
     else (uHi - q1 * dHi) + (q1 - cap) * dHi)
    = (if q1 >>> (32 : BitVec 6).toNat = 0 then uHi - q1 * dHi
       else uHi - (if q1 >>> (32 : BitVec 6).toNat = 0 then q1 else cap) * dHi) := by
  split
  · rfl
  · exact div128V5_rhatc_correction_eq uHi q1 cap dHi

/-- The div128 **code** quotient: a standalone copy of `div128V5SpecPost`'s
    `q` register (the corrected 128/64 quotient as the RISC-V code computes it,
    with the incremental capped remainders).  `div128V5SpecPost`'s `x11` is this
    by construction (`rfl`). -/
def div128V5CodeQuot (uHi uLo vTop : Word) : Word :=
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else cap
  let rhatc := if hi1 = 0 then rhat else rhat + (q1 - cap) * dHi
  let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
  let qDlo1 := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let bq1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
  let brhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + dHi else rhatc
  let brhat'Hi := brhat' >>> (32 : BitVec 6).toNat
  let qDlo2 := bq1' * dLo
  let rhatUn1' := (brhat' <<< (32 : BitVec 6).toNat) ||| un1
  let q1'' := if BitVec.ult rhatUn1' qDlo2 then bq1' + signExtend12 4095 else bq1'
  let rhat'' := if BitVec.ult rhatUn1' qDlo2 then brhat' + dHi else brhat'
  let q1Final := if rhatcHi ≠ 0 then q1c else (if brhat'Hi = 0 then q1'' else bq1')
  let rhatFinal := if rhatcHi ≠ 0 then rhatc else (if brhat'Hi = 0 then rhat'' else brhat')
  let un21 := ((rhatFinal <<< (32 : BitVec 6).toNat) ||| un1) - q1Final * dLo
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else cap
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + (q0 - cap) * dHi
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let bq0' := if BitVec.ult rhat2Un0 q0Dlo1 then q0c + signExtend12 4095 else q0c
  let brhat2' := if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
  let brhat2'Hi := brhat2' >>> (32 : BitVec 6).toNat
  let q0Dlo2 := bq0' * dLo
  let rhat2'Un0 := (brhat2' <<< (32 : BitVec 6).toNat) ||| un0
  let q0'' := if BitVec.ult rhat2'Un0 q0Dlo2 then bq0' + signExtend12 4095 else bq0'
  let q0Final := if rhat2cHi ≠ 0 then q0c else (if brhat2'Hi = 0 then q0'' else bq0')
  (q1Final <<< (32 : BitVec 6).toNat) ||| q0Final

/-- Phase-1 of the q-bridge: the code's corrected Phase-1 trial quotient digit
    `q1Final` equals the model's `q1''`.  Combines the capped-remainder bridge
    `div128V5_rhatc_eq` (rewriting the incremental `rhatc` to the model's closed
    form) with the selection reconciliation `div128V5_phase1b_select_eq`. -/
theorem div128V5_q1Final_eq_model (uHi dHi dLo un1 : Word) :
    (let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let q1 := rv64_divu uHi dHi
     let rhat := uHi - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else cap
     let rhatc := if hi1 = 0 then rhat else rhat + (q1 - cap) * dHi
     let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
     let qDlo1 := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
     let bq1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
     let brhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + dHi else rhatc
     let brhat'Hi := brhat' >>> (32 : BitVec 6).toNat
     let qDlo2 := bq1' * dLo
     let rhatUn1' := (brhat' <<< (32 : BitVec 6).toNat) ||| un1
     let q1'' := if BitVec.ult rhatUn1' qDlo2 then bq1' + signExtend12 4095 else bq1'
     if rhatcHi ≠ 0 then q1c else (if brhat'Hi = 0 then q1'' else bq1'))
    =
    (let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let q1 := rv64_divu uHi dHi
     let rhat := uHi - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else cap
     let rhatc := if hi1 = 0 then rhat else uHi - q1c * dHi
     let qDlo := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
     let phase1bFire1 :=
       decide (rhatc >>> (32 : BitVec 6).toNat = 0) && BitVec.ult rhatUn1 qDlo
     let q1' := if phase1bFire1 then q1c + signExtend12 4095 else q1c
     let rhat' := if phase1bFire1 then rhatc + dHi else rhatc
     div128Quot_phase2b_q0' q1' rhat' dLo un1) := by
  dsimp only
  rw [div128V5_rhatc_eq uHi (rv64_divu uHi dHi)
    ((BitVec.allOnes 64) >>> (32 : BitVec 6).toNat) dHi]
  exact div128V5_phase1b_select_eq _ _ dHi dLo un1

/-- Phase-1 of the q-bridge, remainder side: the code's corrected Phase-1
    remainder `rhatFinal` equals the model's `rhat''` (needed for `un21`).
    Same template as `div128V5_q1Final_eq_model`, via `div128V5_rhatc_eq` +
    `div128V5_phase1b_rhat_select_eq`. -/
theorem div128V5_rhatFinal_eq_model (uHi dHi dLo un1 : Word) :
    (let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let q1 := rv64_divu uHi dHi
     let rhat := uHi - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else cap
     let rhatc := if hi1 = 0 then rhat else rhat + (q1 - cap) * dHi
     let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
     let qDlo1 := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
     let bq1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
     let brhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + dHi else rhatc
     let brhat'Hi := brhat' >>> (32 : BitVec 6).toNat
     let qDlo2 := bq1' * dLo
     let rhatUn1' := (brhat' <<< (32 : BitVec 6).toNat) ||| un1
     let rhat'' := if BitVec.ult rhatUn1' qDlo2 then brhat' + dHi else brhat'
     if rhatcHi ≠ 0 then rhatc else (if brhat'Hi = 0 then rhat'' else brhat'))
    =
    (let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let q1 := rv64_divu uHi dHi
     let rhat := uHi - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else cap
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
  dsimp only
  rw [div128V5_rhatc_eq uHi (rv64_divu uHi dHi)
    ((BitVec.allOnes 64) >>> (32 : BitVec 6).toNat) dHi]
  exact div128V5_phase1b_rhat_select_eq _ _ dHi dLo un1

/-- Phase-2 of the q-bridge: the code's corrected Phase-2 trial quotient digit
    `q0Final` equals the model's `q0''`.  The code's `q0Final` has the same
    selection shape as `q1Final` (dividend `un21`, low half `un0`), so this
    reuses `div128V5_q1Final_eq_model` at `un21/un0`; the model's Phase-2 1st
    correction `q0'` uses the `div128Quot_phase2b_q0'` *primitive* (vs Phase-1's
    explicit form), reconciled by `div128Quot_phase2b_q0'_and_form` /
    `_rhat_and_form` after Bool→Prop normalization of the `decide … && …`. -/
theorem div128V5_q0Final_eq_model (un21 dHi dLo un0 : Word) :
    (let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let q0 := rv64_divu un21 dHi
     let rhat2 := un21 - q0 * dHi
     let hi2 := q0 >>> (32 : BitVec 6).toNat
     let q0c := if hi2 = 0 then q0 else cap
     let rhat2c := if hi2 = 0 then rhat2 else rhat2 + (q0 - cap) * dHi
     let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
     let qDlo1 := q0c * dLo
     let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
     let bq0' := if BitVec.ult rhat2Un0 qDlo1 then q0c + signExtend12 4095 else q0c
     let brhat2' := if BitVec.ult rhat2Un0 qDlo1 then rhat2c + dHi else rhat2c
     let brhat2'Hi := brhat2' >>> (32 : BitVec 6).toNat
     let qDlo2 := bq0' * dLo
     let rhat2'Un0 := (brhat2' <<< (32 : BitVec 6).toNat) ||| un0
     let q0'' := if BitVec.ult rhat2'Un0 qDlo2 then bq0' + signExtend12 4095 else bq0'
     if rhat2cHi ≠ 0 then q0c else (if brhat2'Hi = 0 then q0'' else bq0'))
    =
    (let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let q0 := rv64_divu un21 dHi
     let rhat2 := un21 - q0 * dHi
     let hi2 := q0 >>> (32 : BitVec 6).toNat
     let q0c := if hi2 = 0 then q0 else cap
     let rhat2c := if hi2 = 0 then rhat2 else un21 - q0c * dHi
     let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0
     let rhat2' :=
       if rhat2c >>> (32 : BitVec 6).toNat = 0 then
         let qDlo2 := q0c * dLo
         let rhatUn0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
         if BitVec.ult rhatUn0 qDlo2 then rhat2c + dHi else rhat2c
       else rhat2c
     div128Quot_phase2b_q0' q0' rhat2' dLo un0) := by
  rw [div128V5_q1Final_eq_model un21 dHi dLo un0]
  simp only [Bool.and_eq_true, decide_eq_true_eq,
    div128Quot_phase2b_q0'_and_form, div128Quot_phase2b_rhat_and_form]

/-- **The v5 div128 q-bridge.**  The code quotient (`div128V5CodeQuot`, i.e.
    `div128V5SpecPost`'s `x11`) equals the model `div128Quot_v5`.  Assembled by
    rewriting the three per-digit bridges (`div128V5_q1Final_eq_model`,
    `div128V5_rhatFinal_eq_model`, `div128V5_q0Final_eq_model`); `un21` then
    agrees on both sides, and the `(q1''<<32)|q0''` combine is refl.  Bead
    `evm-asm-wbc4i.9.1`. -/
theorem div128V5CodeQuot_eq_div128Quot_v5 (uHi uLo vTop : Word) :
    div128V5CodeQuot uHi uLo vTop = div128Quot_v5 uHi uLo vTop := by
  unfold div128V5CodeQuot div128Quot_v5
  -- Phase-1 first (uHi-fixed so these do not also rewrite the same-shaped
  -- `q0Final`), turning `q1Final`/`rhatFinal` into the model forms (which makes
  -- `un21` agree); then Phase-2 rewrites the remaining `q0Final`.
  simp only [div128V5_q1Final_eq_model uHi, div128V5_rhatFinal_eq_model uHi]
  simp only [div128V5_q0Final_eq_model]

end EvmAsm.Evm64
