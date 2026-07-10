import EvmAsm.Evm64.DivMod.Compose.Base
import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck2

/-!
# DivMod Compose: div128 postcondition bundle

Shared bundled postcondition for the legacy `divK_div128` subroutine.
Keeping this separate lets v4 code refer to the old post shape in comments or
bridges without importing the full v1 composition theorem.
-/

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Bundled postcondition for `div128_spec_within`.
    Hides the 25-let chain that computes Phase 1 / compute-un21 / Phase 2 /
    Phase 2b-guarded / end-combine intermediates so theorem signatures stay
    as `cpsTripleWithin n A B C P (div128SpecPost …)` instead of exposing a
    large let-chain. Marked `@[irreducible]`; unfold at call sites that need
    the intermediate names. -/
@[irreducible]
def div128SpecPost (sp retAddr d uLo uHi : Word) : Assertion :=
  -- Phase 1 intermediates
  let dHi := d >>> (32 : BitVec 6).toNat
  let dLo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  -- Step 1 intermediates
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  -- compute_un21 intermediates
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  -- Step 2 intermediates
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo un0
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x9Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ retAddr) ** (.x10 ↦ᵣ q1') **
  (.x5 ↦ᵣ q0') ** (.x7 ↦ᵣ x7Exit) **
  (.x6 ↦ᵣ dHi) ** (.x9 ↦ᵣ x9Exit) ** (.x11 ↦ᵣ q) **
  (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3968 ↦ₘ retAddr) **
  (sp + signExtend12 3960 ↦ₘ d) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ un0)

end EvmAsm.Evm64
