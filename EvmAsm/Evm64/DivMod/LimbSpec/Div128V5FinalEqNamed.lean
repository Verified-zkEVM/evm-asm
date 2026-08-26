/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128V5FinalEqNamed

  Connect the code-vs-model digit bridges to the **named irreducible** trial
  defs `divKTrialCallV5Q1dd` / `Rhatdd`: the div128 code's Phase-1 corrected
  quotient `q1Final` / remainder `rhatFinal` equal `divKTrialCallV5Q1dd` /
  `divKTrialCallV5Rhatdd` (compact).  Each is `div128V5_q1Final_eq_model` /
  `div128V5_rhatFinal_eq_model` (#7248/#7249, code → model phase2b form)
  composed with `divKTrialCallV5Q1dd_eq_phase2b` / `_Rhatdd_eq_phase2b`
  (named → same phase2b form).  These feed the `un21 = divKTrialCallV5Un21`
  bridge and the x7/x9 exit bridges needed to give `divK_trial_call_full_v5` a
  compact NAMED post (brick 6, bead `evm-asm-wbc4i.9.1`).
-/

module

public import EvmAsm.Evm64.DivMod.LimbSpec.Div128V5DigitBridge
public import EvmAsm.Evm64.DivMod.LoopBody.TrialCallV5

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Code Phase-1 quotient `q1Final` equals the named `divKTrialCallV5Q1dd`. -/
theorem div128V5_q1Final_eq_Q1dd (u1 u0 v0 : Word) :
    (let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let q1 := rv64_divu u1 (divKTrialCallV5DHi v0)
     let rhat := u1 - q1 * divKTrialCallV5DHi v0
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else cap
     let rhatc := if hi1 = 0 then rhat else rhat + (q1 - cap) * divKTrialCallV5DHi v0
     let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
     let qDlo1 := q1c * divKTrialCallV5DLo v0
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| divKTrialCallV5Un1 u0
     let bq1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
     let brhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + divKTrialCallV5DHi v0 else rhatc
     let brhat'Hi := brhat' >>> (32 : BitVec 6).toNat
     let qDlo2 := bq1' * divKTrialCallV5DLo v0
     let rhatUn1' := (brhat' <<< (32 : BitVec 6).toNat) ||| divKTrialCallV5Un1 u0
     let q1'' := if BitVec.ult rhatUn1' qDlo2 then bq1' + signExtend12 4095 else bq1'
     if rhatcHi ≠ 0 then q1c else (if brhat'Hi = 0 then q1'' else bq1'))
    = divKTrialCallV5Q1dd u1 u0 v0 := by
  rw [div128V5_q1Final_eq_model u1 (divKTrialCallV5DHi v0) (divKTrialCallV5DLo v0)
    (divKTrialCallV5Un1 u0)]
  exact (divKTrialCallV5Q1dd_eq_phase2b u1 u0 v0).symm

/-- Code Phase-1 remainder `rhatFinal` equals the named `divKTrialCallV5Rhatdd`. -/
theorem div128V5_rhatFinal_eq_Rhatdd (u1 u0 v0 : Word) :
    (let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let q1 := rv64_divu u1 (divKTrialCallV5DHi v0)
     let rhat := u1 - q1 * divKTrialCallV5DHi v0
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else cap
     let rhatc := if hi1 = 0 then rhat else rhat + (q1 - cap) * divKTrialCallV5DHi v0
     let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
     let qDlo1 := q1c * divKTrialCallV5DLo v0
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| divKTrialCallV5Un1 u0
     let bq1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
     let brhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + divKTrialCallV5DHi v0 else rhatc
     let brhat'Hi := brhat' >>> (32 : BitVec 6).toNat
     let qDlo2 := bq1' * divKTrialCallV5DLo v0
     let rhatUn1' := (brhat' <<< (32 : BitVec 6).toNat) ||| divKTrialCallV5Un1 u0
     let rhat'' := if BitVec.ult rhatUn1' qDlo2 then brhat' + divKTrialCallV5DHi v0 else brhat'
     if rhatcHi ≠ 0 then rhatc else (if brhat'Hi = 0 then rhat'' else brhat'))
    = divKTrialCallV5Rhatdd u1 u0 v0 := by
  rw [div128V5_rhatFinal_eq_model u1 (divKTrialCallV5DHi v0) (divKTrialCallV5DLo v0)
    (divKTrialCallV5Un1 u0)]
  exact (divKTrialCallV5Rhatdd_eq_phase2b u1 u0 v0).symm

/-- The div128 code's Phase-2 setup value `un21` equals the named
    `divKTrialCallV5Un21` — a `congr` consequence of the Phase-1 digit bridges
    `div128V5_rhatFinal_eq_Rhatdd` and `div128V5_q1Final_eq_Q1dd`. -/
theorem div128V5_un21_eq (u1 u0 v0 : Word) :
    (((let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
       let q1 := rv64_divu u1 (divKTrialCallV5DHi v0)
       let rhat := u1 - q1 * divKTrialCallV5DHi v0
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1c := if hi1 = 0 then q1 else cap
       let rhatc := if hi1 = 0 then rhat else rhat + (q1 - cap) * divKTrialCallV5DHi v0
       let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
       let qDlo1 := q1c * divKTrialCallV5DLo v0
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| divKTrialCallV5Un1 u0
       let bq1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
       let brhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + divKTrialCallV5DHi v0 else rhatc
       let brhat'Hi := brhat' >>> (32 : BitVec 6).toNat
       let qDlo2 := bq1' * divKTrialCallV5DLo v0
       let rhatUn1' := (brhat' <<< (32 : BitVec 6).toNat) ||| divKTrialCallV5Un1 u0
       let rhat'' := if BitVec.ult rhatUn1' qDlo2 then brhat' + divKTrialCallV5DHi v0 else brhat'
       if rhatcHi ≠ 0 then rhatc else (if brhat'Hi = 0 then rhat'' else brhat'))
        <<< (32 : BitVec 6).toNat) ||| divKTrialCallV5Un1 u0)
    -
    ((let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu u1 (divKTrialCallV5DHi v0)
      let rhat := u1 - q1 * divKTrialCallV5DHi v0
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else cap
      let rhatc := if hi1 = 0 then rhat else rhat + (q1 - cap) * divKTrialCallV5DHi v0
      let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
      let qDlo1 := q1c * divKTrialCallV5DLo v0
      let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| divKTrialCallV5Un1 u0
      let bq1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
      let brhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + divKTrialCallV5DHi v0 else rhatc
      let brhat'Hi := brhat' >>> (32 : BitVec 6).toNat
      let qDlo2 := bq1' * divKTrialCallV5DLo v0
      let rhatUn1' := (brhat' <<< (32 : BitVec 6).toNat) ||| divKTrialCallV5Un1 u0
      let q1'' := if BitVec.ult rhatUn1' qDlo2 then bq1' + signExtend12 4095 else bq1'
      if rhatcHi ≠ 0 then q1c else (if brhat'Hi = 0 then q1'' else bq1'))
      * divKTrialCallV5DLo v0)
    = divKTrialCallV5Un21 u1 u0 v0 := by
  rw [div128V5_rhatFinal_eq_Rhatdd u1 u0 v0, div128V5_q1Final_eq_Q1dd u1 u0 v0]
  unfold divKTrialCallV5Un21
  rfl

/-- The div128 code's Phase-2a capped remainder `rhat2c` (incremental form, over
    the named `un21`) equals `divKTrialCallV5Rhat2c`.  The `hi2=0` branch is refl;
    the capped branch is `div128V5_rhatc_correction_eq` (#7243) at `uHi := un21`. -/
theorem div128V5_rhat2c_eq (u1 u0 v0 : Word) :
    (let dHi := divKTrialCallV5DHi v0
     let un21 := divKTrialCallV5Un21 u1 u0 v0
     let q0 := rv64_divu un21 dHi
     let rhat2 := un21 - q0 * dHi
     let hi2 := q0 >>> (32 : BitVec 6).toNat
     let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     if hi2 = 0 then rhat2 else rhat2 + (q0 - cap) * dHi)
    = divKTrialCallV5Rhat2c u1 u0 v0 := by
  unfold divKTrialCallV5Rhat2c
  dsimp only
  split
  · rfl
  · exact div128V5_rhatc_correction_eq (divKTrialCallV5Un21 u1 u0 v0)
      (rv64_divu (divKTrialCallV5Un21 u1 u0 v0) (divKTrialCallV5DHi v0))
      ((BitVec.allOnes 64) >>> (32 : BitVec 6).toNat) (divKTrialCallV5DHi v0)

/-- The div128 code's Phase-2a capped quotient `q0c` (over the named `un21`)
    equals `divKTrialCallV5Q0c` — both are `if hi2 = 0 then q0 else cap`. -/
theorem div128V5_q0c_eq (u1 u0 v0 : Word) :
    (let dHi := divKTrialCallV5DHi v0
     let un21 := divKTrialCallV5Un21 u1 u0 v0
     let q0 := rv64_divu un21 dHi
     let hi2 := q0 >>> (32 : BitVec 6).toNat
     let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     if hi2 = 0 then q0 else cap)
    = divKTrialCallV5Q0c u1 u0 v0 := by
  unfold divKTrialCallV5Q0c
  rfl

/-- The Phase-2a capped remainder in **closed** form (`un21 - q0c·dHi`, as the
    model `div128V5_q0Final_eq_model` writes it) equals `divKTrialCallV5Rhat2c`.
    (Distinct from `div128V5_rhat2c_eq`, the incremental code form.) -/
theorem div128V5_rhat2c_closed_eq (u1 u0 v0 : Word) :
    (let dHi := divKTrialCallV5DHi v0
     let un21 := divKTrialCallV5Un21 u1 u0 v0
     let q0 := rv64_divu un21 dHi
     let rhat2 := un21 - q0 * dHi
     let hi2 := q0 >>> (32 : BitVec 6).toNat
     let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let q0c := if hi2 = 0 then q0 else cap
     if hi2 = 0 then rhat2 else un21 - q0c * dHi)
    = divKTrialCallV5Rhat2c u1 u0 v0 := by
  unfold divKTrialCallV5Rhat2c
  dsimp only
  split <;> rfl

/-- The div128 code's Phase-2 corrected quotient digit `q0Final` equals the named
    `divKTrialCallV5Q0dd` — the last register-name bridge for `div128V5SpecPost`. -/
theorem div128V5_q0Final_eq_Q0dd (u1 u0 v0 : Word) :
    (let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let q0 := rv64_divu (divKTrialCallV5Un21 u1 u0 v0) (divKTrialCallV5DHi v0)
     let rhat2 := divKTrialCallV5Un21 u1 u0 v0 - q0 * divKTrialCallV5DHi v0
     let hi2 := q0 >>> (32 : BitVec 6).toNat
     let q0c := if hi2 = 0 then q0 else cap
     let rhat2c := if hi2 = 0 then rhat2 else rhat2 + (q0 - cap) * divKTrialCallV5DHi v0
     let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
     let qDlo1 := q0c * divKTrialCallV5DLo v0
     let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| divKTrialCallV5Un0 u0
     let bq0' := if BitVec.ult rhat2Un0 qDlo1 then q0c + signExtend12 4095 else q0c
     let brhat2' := if BitVec.ult rhat2Un0 qDlo1 then rhat2c + divKTrialCallV5DHi v0 else rhat2c
     let brhat2'Hi := brhat2' >>> (32 : BitVec 6).toNat
     let qDlo2 := bq0' * divKTrialCallV5DLo v0
     let rhat2'Un0 := (brhat2' <<< (32 : BitVec 6).toNat) ||| divKTrialCallV5Un0 u0
     let q0'' := if BitVec.ult rhat2'Un0 qDlo2 then bq0' + signExtend12 4095 else bq0'
     if rhat2cHi ≠ 0 then q0c else (if brhat2'Hi = 0 then q0'' else bq0'))
    = divKTrialCallV5Q0dd u1 u0 v0 := by
  rw [div128V5_q0Final_eq_model (divKTrialCallV5Un21 u1 u0 v0) (divKTrialCallV5DHi v0)
    (divKTrialCallV5DLo v0) (divKTrialCallV5Un0 u0)]
  unfold divKTrialCallV5Q0dd divKTrialCallV5Q0d divKTrialCallV5Rhat2d
  simp only [← div128V5_q0c_eq u1 u0 v0, ← div128V5_rhat2c_closed_eq u1 u0 v0]

end EvmAsm.Evm64
