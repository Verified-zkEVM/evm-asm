/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.Algorithm

  Irreducible bundles for the div128Quot algorithm's intermediate Word values.
  Used to prevent `maximum recursion depth` when composing Phase 1/Phase 2
  tight lemmas with A2.S1's deeply nested let-chain hypothesis.
  (Matches `feedback_bundle_pre_post_no_lets` guidance.)

  Split out from `CallSkipLowerBoundV2.lean` for file-size hygiene.
-/

import EvmAsm.Evm64.EvmWordArith.Div128CallSkipClose

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The algorithm's `un21` output as a function of `(u4, u3, b3')`.
    Full 17-step let-chain: Phase 1a (q1, rhat, hi1 correction), Phase 1b
    (q1c, rhatc, ult correction → q1', rhat'), halfword combine + subtraction. -/
@[irreducible]
def algorithmUn21 (u4 u3 b3' : Word) : Word :=
  let dHi := b3' >>> (32 : BitVec 6).toNat
  let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u3 >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u4 dHi
  let rhat := u4 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * dLo
  cu_rhat_un1 - cu_q1_dlo

/-- Named unfold for `algorithmUn21`. -/
theorem algorithmUn21_unfold (u4 u3 b3' : Word) :
    algorithmUn21 u4 u3 b3' =
      (let dHi := b3' >>> (32 : BitVec 6).toNat
       let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
       let div_un1 := u3 >>> (32 : BitVec 6).toNat
       let q1 := rv64_divu u4 dHi
       let rhat := u4 - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
       let rhatc := if hi1 = 0 then rhat else rhat + dHi
       let qDlo := q1c * dLo
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
       let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
       let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
       let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
       let cu_q1_dlo := q1' * dLo
       cu_rhat_un1 - cu_q1_dlo) := by
  delta algorithmUn21; rfl

/-- The algorithm's Phase-1b output `q1'` as a function of `(u4, u3, b3')`.
    Same let-chain as `algorithmUn21`, but returns `q1'` instead of `un21`.
    Note: takes `u3` as a parameter (even though q1' doesn't directly depend
    on the low bits of u3) so the Phase 1b ult-check input `rhatUn1` —
    which uses `div_un1 = u3 >>> 32` — lines up with the algorithm.
    Marked `@[irreducible]` to keep the 11-step chain from polluting
    type elaboration (matches `algorithmUn21` treatment). -/
@[irreducible]
def algorithmQ1Prime (u4 u3 b3' : Word) : Word :=
  let dHi := b3' >>> (32 : BitVec 6).toNat
  let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u3 >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u4 dHi
  let rhat := u4 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c

/-- Named unfold for `algorithmQ1Prime`. -/
theorem algorithmQ1Prime_unfold (u4 u3 b3' : Word) :
    algorithmQ1Prime u4 u3 b3' =
      (let dHi := b3' >>> (32 : BitVec 6).toNat
       let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
       let div_un1 := u3 >>> (32 : BitVec 6).toNat
       let q1 := rv64_divu u4 dHi
       let rhat := u4 - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
       let rhatc := if hi1 = 0 then rhat else rhat + dHi
       let qDlo := q1c * dLo
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
       if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c) := by
  delta algorithmQ1Prime; rfl

/-- The algorithm's Phase-2b output `q0'` as a function of `(u4, u3, b3')`.
    Built on `algorithmUn21` + Phase 2a correction + Phase 2b ult check.
    Marked `@[irreducible]` so Phase 2 tight's internal q0' and
    `div128Quot_toNat_eq_strict`'s internal q0' share the same opaque
    symbol — resolves the q0' syntactic mismatch blocking A2.S1's final
    composition. -/
@[irreducible]
def algorithmQ0Prime (u4 u3 b3' : Word) : Word :=
  let dHi := b3' >>> (32 : BitVec 6).toNat
  let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un21 := algorithmUn21 u4 u3 b3'
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  div128Quot_phase2b_q0' q0c rhat2c dLo div_un0

/-- Named unfold for `algorithmQ0Prime`. -/
theorem algorithmQ0Prime_unfold (u4 u3 b3' : Word) :
    algorithmQ0Prime u4 u3 b3' =
      (let dHi := b3' >>> (32 : BitVec 6).toNat
       let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
       let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
       let un21 := algorithmUn21 u4 u3 b3'
       let q0 := rv64_divu un21 dHi
       let rhat2 := un21 - q0 * dHi
       let hi2 := q0 >>> (32 : BitVec 6).toNat
       let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
       let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
       div128Quot_phase2b_q0' q0c rhat2c dLo div_un0) := by
  delta algorithmQ0Prime; rfl

end EvmAsm.Evm64
