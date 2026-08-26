/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128V5X7X9Eq

  The div128 code's Phase-2 exit registers `x7Exit` / `x9Exit` (incremental
  forms, as in `div128V5SpecPost`, over the named `un21`) equal the compact
  named `divKTrialCallV5X7Exit` / `divKTrialCallV5X9Exit`.  Obtained by unfolding
  the named exit defs and rewriting their `divKTrialCallV5Rhat2c` / `Q0c` back to
  the incremental code forms via `div128V5_rhat2c_eq` / `div128V5_q0c_eq`
  (#7258).  With the Phase-1 / un21 / rhat2c / q0c bridges, these name the last
  div128V5SpecPost registers, completing the inputs to a compact NAMED
  trial-call-full post (brick 6).  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.LimbSpec.Div128V5FinalEqNamed
public import EvmAsm.Evm64.DivMod.LoopIterN1.CallV5NoNop

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- `divKTrialCallV5X9Exit` in the incremental code form (matching
    `div128V5SpecPost`'s `x9Exit` over the named `un21`). -/
theorem div128V5_x9Exit_eq (u1 u0 v0 : Word) :
    divKTrialCallV5X9Exit u1 u0 v0 =
    (let dHi := divKTrialCallV5DHi v0
     let dLo := divKTrialCallV5DLo v0
     let un0 := divKTrialCallV5Un0 u0
     let un21 := divKTrialCallV5Un21 u1 u0 v0
     let q0 := rv64_divu un21 dHi
     let rhat2 := un21 - q0 * dHi
     let hi2 := q0 >>> (32 : BitVec 6).toNat
     let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let rhat2c := if hi2 = 0 then rhat2 else rhat2 + (q0 - cap) * dHi
     let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
     let q0c := if hi2 = 0 then q0 else cap
     let q0Dlo1 := q0c * dLo
     let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
     let brhat2' := if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
     let brhat2'Hi := brhat2' >>> (32 : BitVec 6).toNat
     let rhat2'Un0 := (brhat2' <<< (32 : BitVec 6).toNat) ||| un0
     if rhat2cHi ≠ 0 then rhat2cHi else (if brhat2'Hi = 0 then rhat2'Un0 else brhat2'Hi)) := by
  unfold divKTrialCallV5X9Exit
  dsimp only
  rw [← div128V5_rhat2c_eq u1 u0 v0, ← div128V5_q0c_eq u1 u0 v0]

/-- `divKTrialCallV5X7Exit` in the incremental code form (matching
    `div128V5SpecPost`'s `x7Exit` over the named `un21`). -/
theorem div128V5_x7Exit_eq (u1 u0 v0 : Word) :
    divKTrialCallV5X7Exit u1 u0 v0 =
    (let dHi := divKTrialCallV5DHi v0
     let dLo := divKTrialCallV5DLo v0
     let un0 := divKTrialCallV5Un0 u0
     let un21 := divKTrialCallV5Un21 u1 u0 v0
     let q0 := rv64_divu un21 dHi
     let rhat2 := un21 - q0 * dHi
     let hi2 := q0 >>> (32 : BitVec 6).toNat
     let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let x7o := if hi2 = 0 then un21 else (q0 - cap) * dHi
     let rhat2c := if hi2 = 0 then rhat2 else rhat2 + (q0 - cap) * dHi
     let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
     let q0c := if hi2 = 0 then q0 else cap
     let q0Dlo1 := q0c * dLo
     let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
     let bq0' := if BitVec.ult rhat2Un0 q0Dlo1 then q0c + signExtend12 4095 else q0c
     let brhat2' := if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
     let brhat2'Hi := brhat2' >>> (32 : BitVec 6).toNat
     let q0Dlo2 := bq0' * dLo
     if rhat2cHi ≠ 0 then x7o else (if brhat2'Hi = 0 then q0Dlo2 else q0Dlo1)) := by
  unfold divKTrialCallV5X7Exit
  dsimp only
  rw [← div128V5_rhat2c_eq u1 u0 v0, ← div128V5_q0c_eq u1 u0 v0]

end EvmAsm.Evm64
