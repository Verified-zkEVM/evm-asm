/-
  EvmAsm.Stateless.SpecRef.PrecompilesKzg

  `point_evaluation.py` of
  `execution-specs/src/ethereum/forks/amsterdam/vm/precompiled_contracts/`
  (`@tests-zkevm@v0.5.0`, `bd8c673`, function `point_evaluation`) and
  the `ethereum/crypto/kzg.py` it delegates to
  (`execution-specs/src/ethereum/crypto/kzg.py`, functions
  `kzg_commitment_to_versioned_hash`, `validate_kzg_g1`,
  `bytes_to_bls_field`, `pairing_check`, `verify_kzg_proof`,
  `verify_kzg_proof_impl`):

  * G1 point decompression (`py_ecc/bls/point_compression.py`,
    `decompress_G1`: flag bits 383/382/381, `y = (x³+4)^((p+1)/4)`,
    sign selection by `(2y)/p`) + `KeyValidate` (non-infinity +
    subgroup).
  * `KZG_SETUP_G2_MONOMIAL_1` embedded in DECOMPRESSED affine form
    (computed once from the pinned compressed constant with
    `signature_to_G2`) — G2 decompression is thereby not needed.
  * `pairing_check`: two Miller loops multiplied, ONE final
    exponentiation (`miller_loop_raw` below is the BLS loop without
    the final power).
-/

import EvmAsm.Stateless.SpecRef.PrecompilesBls

namespace EvmAsm.Stateless.SpecRef

namespace Kzg

open Bn128 (FQP Proj pAdd pMul pIsInf fqpPow)
open Bls12

def BLS_MODULUS : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513
def FIELD_ELEMENTS_PER_BLOB : Nat := 4096

/-- `G1_POINT_AT_INFINITY = 0xc0 ‖ 00…` (48 bytes). -/
def G1_POINT_AT_INFINITY : Bytes := 0xC0 :: List.replicate 47 0x00

/-- The BLS12-381 G1/G2 generators (affine). -/
def blsG1 : Proj Nat :=
  (0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
   0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1, 1)
def blsG2 : Proj FQP :=
  ([0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8,
    0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e],
   [0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801,
    0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be],
   fq2Ops.one)

/-- `KZG_SETUP_G2_MONOMIAL_1`, decompressed (see the header). -/
def KZG_SETUP_G2_1 : Proj FQP :=
  ([0x185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2,
    0x15bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72],
   [0x014353bdb96b626dd7d5ee8599d1fca2131569490e28de18e82451a496a9c9794ce26d105941f383ee689bfbbb832a99,
    0x1666c54b0a32529503432fcae0181b4bef79de09fc63671fda5ed1ba9bfa07899495346f3d7ac9cd23048ef30d0a154f],
   fq2Ops.one)

/-- `decompress_G1(z)` (`py_ecc/bls/point_compression.py`). -/
def decompress_G1 (bs : Bytes) : Except EvmError (Proj Nat) := do
  let z := bytesBEtoNat bs
  let c_flag := (z >>> 383) % 2
  let b_flag := (z >>> 382) % 2
  let a_flag := (z >>> 381) % 2
  if c_flag ≠ 1 then throw (.kzgProofError)
  let is_inf_pt := z % 2^381 == 0 && a_flag == 0 && b_flag == 1
  if b_flag == 1 then
    if z % 2^381 ≠ 0 || a_flag ≠ 0 then throw (.kzgProofError)
    else return (1, 1, 0)
  let _ := is_inf_pt
  let x := z % 2^381
  if x ≥ blsP then throw (.kzgProofError)
  let y := EvmAsm.Rv64.Accel.powMod ((x^3 + 4) % blsP) ((blsP + 1) / 4) blsP
  if y * y % blsP ≠ (x^3 + 4) % blsP then throw (.kzgProofError)
  let y := if (y * 2) / blsP == a_flag then y else blsP - y
  pure (x, y, 1)

/-- `validate_kzg_g1(b)`: the exact infinity encoding is allowed;
    otherwise `KeyValidate` (decompress + non-infinity + subgroup). -/
def validate_kzg_g1 (bs : Bytes) : Except EvmError Unit := do
  if bs == G1_POINT_AT_INFINITY then return
  let pt ← decompress_G1 bs
  if pIsInf fqOps pt then throw (.kzgProofError)
  if !pIsInf fqOps (pMul fqOps pt blsOrder) then throw (.kzgProofError)

/-- `bytes_to_bls_field(b)`. -/
def bytes_to_bls_field (bs : Bytes) : Except EvmError Nat := do
  let v := bytesBEtoNat bs
  if v ≥ BLS_MODULUS then throw (.kzgProofError)
  pure v

/-- The BLS Miller loop WITHOUT the final exponentiation
    (`pairing(…, final_exponentiate=False)`); infinities give one. -/
def pairingRaw (Q : Proj FQP) (P : Proj Nat) : FQP :=
  if pIsInf fq2Ops Q || pIsInf fqOps P then Bn128.fqpOne 12
  else Bls12.miller_loop_raw Q P

/-- `pairing_check(values)`: product of the two raw pairings, one
    final exponentiation, compared to one. -/
def pairing_check (p1 : Proj Nat) (q1 : Proj FQP) (p2 : Proj Nat)
    (q2 : Proj FQP) : Bool :=
  let F := fq12Ops
  let prod := F.mul (pairingRaw q1 p1) (pairingRaw q2 p2)
  F.beq (fqpPow blsP 12 fq12MC prod ((blsP^12 - 1) / blsOrder)) F.one

/-- `verify_kzg_proof_impl(commitment, z, y, proof)`. -/
def verify_kzg_proof_impl (commitment : Proj Nat) (z y : Nat)
    (proof : Proj Nat) : Bool :=
  let X_minus_z := pAdd fq2Ops KZG_SETUP_G2_1
    (pMul fq2Ops blsG2 ((BLS_MODULUS - z) % BLS_MODULUS))
  let P_minus_y := pAdd fqOps commitment
    (pMul fqOps blsG1 ((BLS_MODULUS - y) % BLS_MODULUS))
  let negG2 : Proj FQP := (blsG2.1, fq2Ops.sub fq2Ops.zero blsG2.2.1, blsG2.2.2)
  pairing_check P_minus_y negG2 proof X_minus_z

end Kzg

namespace GasCosts
def PRECOMPILE_POINT_EVALUATION : Uint := 50000
end GasCosts

/-- `point_evaluation(evm)` (`point_evaluation.py`, function
    `point_evaluation`). -/
def pPointEvaluation : EvmM Unit := do
  let data := (← EvmM.getEvm).message.data
  if data.length ≠ 192 then throw .kzgProofError
  let versioned_hash := data.take 32
  let zB := (data.drop 32).take 32
  let yB := (data.drop 64).take 32
  let commitmentB := (data.drop 96).take 48
  let proofB := (data.drop 144).take 48
  charge_gas GasCosts.PRECOMPILE_POINT_EVALUATION
  -- kzg_commitment_to_versioned_hash
  if 0x01 :: (sha256 commitmentB).drop 1 != versioned_hash then
    throw .kzgProofError
  let ok ← (do
    match (do
        Kzg.validate_kzg_g1 commitmentB
        Kzg.validate_kzg_g1 proofB
        let commitment ← Kzg.decompress_G1 commitmentB
        let proof ← Kzg.decompress_G1 proofB
        let z ← Kzg.bytes_to_bls_field zB
        let y ← Kzg.bytes_to_bls_field yB
        pure (Kzg.verify_kzg_proof_impl commitment z y proof)
      : Except EvmError Bool) with
    | .ok b => pure b
    | .error _ => pure false)
  if !ok then throw .kzgProofError
  EvmM.modifyEvm (fun e =>
    { e with output := natToBytesBE 32 Kzg.FIELD_ELEMENTS_PER_BLOB
        ++ natToBytesBE 32 Kzg.BLS_MODULUS })

end EvmAsm.Stateless.SpecRef
