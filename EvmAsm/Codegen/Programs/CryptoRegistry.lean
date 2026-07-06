/- EvmAsm.Codegen.Programs.CryptoRegistry
  Crypto and precompile probe sub-registry for codegen programs.
-/

import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashProbes
import EvmAsm.Codegen.Programs.PrecompileBackendProbes

namespace EvmAsm.Codegen

/-- Look up standalone crypto/precompile probe programs by CLI name. -/
def lookupCryptoProgram : String → Option BuildUnit
  | "zisk_keccak_probe" => some ziskKeccakProbeUnit
  | "zisk_keccak256_empty" => some ziskKeccak256EmptyProbeUnit
  | "zisk_keccak256_abc" => some ziskKeccak256AbcProbeUnit
  | "zisk_zkvm_keccak256" => some ziskZkvmKeccak256ProbeUnit
  | "zisk_sha256_probe_le" => some ziskSha256ProbeLeUnit
  | "zisk_zkvm_sha256" => some ziskZkvmSha256ProbeUnit
  | "zisk_sha256_from_input" => some ziskSha256FromInputProbeUnit
  | "zisk_keccak256_from_input" => some ziskKeccak256FromInputProbeUnit
  | "zisk_secp256k1_ecrecover_backend_probe" => some ziskSecp256k1EcrecoverBackendProbeUnit
  | "zisk_secp256k1_ecrecover_real_backend_probe" => some ziskSecp256k1EcrecoverRealBackendProbeUnit
  | "zisk_modexp_backend_probe" => some ziskModexpBackendProbeUnit
  | "zisk_modexp_backend_real_probe" => some ziskModexpBackendRealProbeUnit
  | "zisk_bls12_g1_add_backend_probe" => some ziskBls12G1AddBackendProbeUnit
  | "zisk_bls12_g1_msm_backend_probe" => some ziskBls12G1MsmBackendProbeUnit
  | "zisk_bls12_g2_add_backend_probe" => some ziskBls12G2AddBackendProbeUnit
  | "zisk_bls12_g2_msm_backend_probe" => some ziskBls12G2MsmBackendProbeUnit
  | "zisk_bls12_pairing_backend_probe" => some ziskBls12PairingBackendProbeUnit
  | "zisk_bls12_map_fp_to_g1_backend_probe" => some ziskBls12MapFpToG1BackendProbeUnit
  | "zisk_bls12_map_fp2_to_g2_backend_probe" => some ziskBls12MapFp2ToG2BackendProbeUnit
  | _ => none

/-- CLI names hosted by `lookupCryptoProgram`. -/
def knownCryptoProgramNames : List String :=
  ["zisk_keccak_probe",
   "zisk_keccak256_empty",
   "zisk_keccak256_abc",
   "zisk_zkvm_keccak256",
   "zisk_sha256_probe_le",
   "zisk_zkvm_sha256",
   "zisk_sha256_from_input",
   "zisk_keccak256_from_input",
   "zisk_secp256k1_ecrecover_backend_probe",
   "zisk_secp256k1_ecrecover_real_backend_probe",
   "zisk_modexp_backend_probe",
   "zisk_modexp_backend_real_probe",
   "zisk_bls12_g1_add_backend_probe",
   "zisk_bls12_g1_msm_backend_probe",
   "zisk_bls12_g2_add_backend_probe",
   "zisk_bls12_g2_msm_backend_probe",
   "zisk_bls12_pairing_backend_probe",
   "zisk_bls12_map_fp_to_g1_backend_probe",
   "zisk_bls12_map_fp2_to_g2_backend_probe"]

end EvmAsm.Codegen
