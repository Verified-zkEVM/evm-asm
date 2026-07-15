/-
  EvmAsm.Evm64.Accelerators.SyscallIds

  ECALL syscall-ID table for the cryptographic accelerators declared in
  `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`.

  Background (see `docs/zkvm-accelerators-interface.md`): the ECALL *mechanism*
  follows the SP1 RISC-V convention shared by every zkVM (syscall id selector
  in `t0` / `x5`, args in `a0`–`a2`, return value in `a0`). The *function set*
  and per-function payload layout come from `zkvm_accelerators.h`. The integer
  IDs that select which accelerator to run are not fixed by the C ABI — they
  are a host-side detail. This file pins one concrete assignment that the
  verified guest will use; a host that ships a different table remaps in its
  ECALL handler without affecting the guest's correctness.

  Existing reserved selector values used elsewhere in this repo:

      0x00  HALT       (`Rv64.Program.HALT`)
      0x10  write_output  (`Rv64.Execution.step_ecall_write_output`)
      0xF0  HINT_LEN   (retired; handlers removed from Execution.lean)
      0xF1  HINT_READ  (retired; `Rv64.RLP.Phase4HintRead` deleted)

  We allocate the 19 accelerator IDs in a fresh, contiguous range starting at
  `0x100`, which avoids the existing reservations above and leaves the `0x00`–
  `0xFF` band entirely to the (host-defined) framing syscalls. Values are
  declared as `Nat` to match the `BitVec.ofNat 64 _` literals used at the
  ECALL call sites today; a future per-function callable wrapper can lift them
  to `Word` directly.

  Refs: parent beads task `evm-asm-nr2sk`, slice `evm-asm-yv3qz`.
-/

import EvmAsm.Rv64.Word

namespace EvmAsm
namespace Accelerators
namespace SyscallId

/-! ## Non-precompile accelerators -/

/-- `zkvm_keccak256` — Keccak-256 hash of an arbitrary-length byte buffer. -/
def keccak256 : Nat := 0x100

/-- `zkvm_secp256k1_verify` — secp256k1 ECDSA signature verification. -/
def secp256k1_verify : Nat := 0x101

/-! ## Precompile accelerators (Ethereum precompiles `0x01`–`0x11`) -/

/-- `zkvm_secp256k1_ecrecover` — ECRECOVER (precompile `0x01`). -/
def secp256k1_ecrecover : Nat := 0x102

/-- `zkvm_sha256` — SHA-256 hash (precompile `0x02`). -/
def sha256 : Nat := 0x103

/-- `zkvm_ripemd160` — RIPEMD-160 hash (precompile `0x03`). -/
def ripemd160 : Nat := 0x104

/-- `zkvm_modexp` — modular exponentiation (precompile `0x05`). -/
def modexp : Nat := 0x105

/-- `zkvm_bn254_g1_add` — BN254 G1 point addition (precompile `0x06`). -/
def bn254_g1_add : Nat := 0x106

/-- `zkvm_bn254_g1_mul` — BN254 G1 scalar multiplication (precompile `0x07`). -/
def bn254_g1_mul : Nat := 0x107

/-- `zkvm_bn254_pairing` — BN254 optimal-Ate pairing check (precompile `0x08`). -/
def bn254_pairing : Nat := 0x108

/-- `zkvm_blake2f` — BLAKE2 compression function `F` (precompile `0x09`). -/
def blake2f : Nat := 0x109

/-- `zkvm_kzg_point_eval` — KZG point evaluation precompile (precompile `0x0a`). -/
def kzg_point_eval : Nat := 0x10A

/-- `zkvm_bls12_g1_add` — BLS12-381 G1 point addition (precompile `0x0b`). -/
def bls12_g1_add : Nat := 0x10B

/-- `zkvm_bls12_g1_msm` — BLS12-381 G1 multi-scalar multiplication (precompile `0x0c`). -/
def bls12_g1_msm : Nat := 0x10C

/-- `zkvm_bls12_g2_add` — BLS12-381 G2 point addition (precompile `0x0d`). -/
def bls12_g2_add : Nat := 0x10D

/-- `zkvm_bls12_g2_msm` — BLS12-381 G2 multi-scalar multiplication (precompile `0x0e`). -/
def bls12_g2_msm : Nat := 0x10E

/-- `zkvm_bls12_pairing` — BLS12-381 pairing check (precompile `0x0f`). -/
def bls12_pairing : Nat := 0x10F

/-- `zkvm_bls12_map_fp_to_g1` — map field element to G1 (precompile `0x10`). -/
def bls12_map_fp_to_g1 : Nat := 0x110

/-- `zkvm_bls12_map_fp2_to_g2` — map Fp2 element to G2 (precompile `0x11`). -/
def bls12_map_fp2_to_g2 : Nat := 0x111

/-! ## Extended precompiles -/

/-- `zkvm_secp256r1_verify` — P-256 / secp256r1 ECDSA verification (precompile `0x100`). -/
def secp256r1_verify : Nat := 0x112

/-! ## Reserved framing selectors

These are defined in their respective modules; we restate them here so the
disjointness check below covers the full active selector space. -/

/-- HALT framing selector (matches `Rv64.Program.HALT`). -/
def halt : Nat := 0x00

/-- Host `write_output(ptr, size)` framing selector. -/
def commit : Nat := 0x10

/-- HINT_LEN framing selector (matches `Rv64.HintSpecs`). Deprecated: use `readInput` (0xF2) instead. -/
def hintLen : Nat := 0xF0

/-- HINT_READ framing selector (matches `Rv64.RLP.Phase4HintRead`). Deprecated. -/
def hintRead : Nat := 0xF1

/-- `read_input` framing selector (zkvm-standards C ABI, matches `Rv64.HintSpecs.ecall_read_input_spec_gen_within`). -/
def readInput : Nat := 0xF2

/-! ## Sanity properties

Pairwise distinctness of the 19 accelerator IDs and the four framing
selectors. Discharged by `decide` on `Nat` literals; if a future revision
tries to reuse an ID, this proof fails at build time. -/

/-- All 23 selectors above are pairwise distinct. -/
theorem allSelectors_pairwiseDistinct :
    [halt, commit, hintLen, hintRead,
     keccak256, secp256k1_verify,
     secp256k1_ecrecover, sha256, ripemd160, modexp,
     bn254_g1_add, bn254_g1_mul, bn254_pairing,
     blake2f, kzg_point_eval,
     bls12_g1_add, bls12_g1_msm, bls12_g2_add, bls12_g2_msm,
     bls12_pairing, bls12_map_fp_to_g1, bls12_map_fp2_to_g2,
     secp256r1_verify].Nodup := by
  decide

/-- The 19 accelerator IDs all sit in the contiguous range `[0x100, 0x113)`. -/
theorem accelerator_ids_in_range :
    ∀ id ∈ [keccak256, secp256k1_verify,
            secp256k1_ecrecover, sha256, ripemd160, modexp,
            bn254_g1_add, bn254_g1_mul, bn254_pairing,
            blake2f, kzg_point_eval,
            bls12_g1_add, bls12_g1_msm, bls12_g2_add, bls12_g2_msm,
            bls12_pairing, bls12_map_fp_to_g1, bls12_map_fp2_to_g2,
            secp256r1_verify],
      0x100 ≤ id ∧ id < 0x113 := by
  decide

/-! ## RV64 selector words -/

/-- RV64 `t0` selector-register encoding for a syscall ID. -/
def toWord (id : Nat) : BitVec 64 := BitVec.ofNat 64 id

/-- The active framing and accelerator selectors remain pairwise distinct after
lifting to RV64 selector-register words. -/
theorem allSelectorWords_pairwiseDistinct :
    [toWord halt, toWord commit, toWord hintLen, toWord hintRead,
     toWord keccak256, toWord secp256k1_verify,
     toWord secp256k1_ecrecover, toWord sha256, toWord ripemd160, toWord modexp,
     toWord bn254_g1_add, toWord bn254_g1_mul, toWord bn254_pairing,
     toWord blake2f, toWord kzg_point_eval,
     toWord bls12_g1_add, toWord bls12_g1_msm, toWord bls12_g2_add, toWord bls12_g2_msm,
     toWord bls12_pairing, toWord bls12_map_fp_to_g1, toWord bls12_map_fp2_to_g2,
     toWord secp256r1_verify].Nodup := by
  decide

end SyscallId

/-! ## RV64 Word lifts of the syscall IDs

The ECALL convention places the selector in `t0` (`x5`), which is a 64-bit
RISC-V register. ECALL call sites today produce the selector as
`BitVec.ofNat 64 _` of the `Nat` constants above. This section gives each
selector a named `Word` (= `BitVec 64`) constant, so callable wrappers and
ECALL handler specs can refer to them by name, and bundles a Word-level
pairwise-distinctness theorem matching `SyscallId.allSelectors_pairwiseDistinct`.

All selector values live well below `2^64`, so `BitVec.ofNat 64` is
injective on this set and the Word distinctness mirrors the `Nat` one.
-/

end Accelerators
end EvmAsm

namespace EvmAsm
namespace Rv64
namespace SyscallIdWord

open EvmAsm.Accelerators

/-! ### Non-precompile accelerators -/

/-- `zkvm_keccak256` selector as RV64 `Word`. -/
def keccak256 : Word := BitVec.ofNat 64 SyscallId.keccak256

/-- `zkvm_secp256k1_verify` selector as RV64 `Word`. -/
def secp256k1_verify : Word := BitVec.ofNat 64 SyscallId.secp256k1_verify

/-! ### Precompile accelerators (Ethereum precompiles `0x01`–`0x11`) -/

/-- `zkvm_secp256k1_ecrecover` selector as RV64 `Word`. -/
def secp256k1_ecrecover : Word := BitVec.ofNat 64 SyscallId.secp256k1_ecrecover

/-- `zkvm_sha256` selector as RV64 `Word`. -/
def sha256 : Word := BitVec.ofNat 64 SyscallId.sha256

/-- `zkvm_ripemd160` selector as RV64 `Word`. -/
def ripemd160 : Word := BitVec.ofNat 64 SyscallId.ripemd160

/-- `zkvm_modexp` selector as RV64 `Word`. -/
def modexp : Word := BitVec.ofNat 64 SyscallId.modexp

/-- `zkvm_bn254_g1_add` selector as RV64 `Word`. -/
def bn254_g1_add : Word := BitVec.ofNat 64 SyscallId.bn254_g1_add

/-- `zkvm_bn254_g1_mul` selector as RV64 `Word`. -/
def bn254_g1_mul : Word := BitVec.ofNat 64 SyscallId.bn254_g1_mul

/-- `zkvm_bn254_pairing` selector as RV64 `Word`. -/
def bn254_pairing : Word := BitVec.ofNat 64 SyscallId.bn254_pairing

/-- `zkvm_blake2f` selector as RV64 `Word`. -/
def blake2f : Word := BitVec.ofNat 64 SyscallId.blake2f

/-- `zkvm_kzg_point_eval` selector as RV64 `Word`. -/
def kzg_point_eval : Word := BitVec.ofNat 64 SyscallId.kzg_point_eval

/-- `zkvm_bls12_g1_add` selector as RV64 `Word`. -/
def bls12_g1_add : Word := BitVec.ofNat 64 SyscallId.bls12_g1_add

/-- `zkvm_bls12_g1_msm` selector as RV64 `Word`. -/
def bls12_g1_msm : Word := BitVec.ofNat 64 SyscallId.bls12_g1_msm

/-- `zkvm_bls12_g2_add` selector as RV64 `Word`. -/
def bls12_g2_add : Word := BitVec.ofNat 64 SyscallId.bls12_g2_add

/-- `zkvm_bls12_g2_msm` selector as RV64 `Word`. -/
def bls12_g2_msm : Word := BitVec.ofNat 64 SyscallId.bls12_g2_msm

/-- `zkvm_bls12_pairing` selector as RV64 `Word`. -/
def bls12_pairing : Word := BitVec.ofNat 64 SyscallId.bls12_pairing

/-- `zkvm_bls12_map_fp_to_g1` selector as RV64 `Word`. -/
def bls12_map_fp_to_g1 : Word := BitVec.ofNat 64 SyscallId.bls12_map_fp_to_g1

/-- `zkvm_bls12_map_fp2_to_g2` selector as RV64 `Word`. -/
def bls12_map_fp2_to_g2 : Word := BitVec.ofNat 64 SyscallId.bls12_map_fp2_to_g2

/-! ### Extended precompiles -/

/-- `zkvm_secp256r1_verify` selector as RV64 `Word`. -/
def secp256r1_verify : Word := BitVec.ofNat 64 SyscallId.secp256r1_verify

/-! ### Reserved framing selectors -/

/-- HALT framing selector as RV64 `Word`. -/
def halt : Word := BitVec.ofNat 64 SyscallId.halt

/-- Host `write_output(ptr, size)` framing selector as RV64 `Word`. -/
def commit : Word := BitVec.ofNat 64 SyscallId.commit

/-- HINT_LEN framing selector as RV64 `Word`. -/
def hintLen : Word := BitVec.ofNat 64 SyscallId.hintLen

/-- HINT_READ framing selector as RV64 `Word`. -/
def hintRead : Word := BitVec.ofNat 64 SyscallId.hintRead

/-! ### Sanity properties

Word-level pairwise distinctness mirrors `SyscallId.allSelectors_pairwiseDistinct`.
Discharged by `decide`; if a future revision collides two IDs, this proof
fails at build time alongside the `Nat`-level one. -/

/-- All 23 selectors above are pairwise distinct as 64-bit `Word` values. -/
theorem allSelectors_pairwiseDistinct :
    [halt, commit, hintLen, hintRead,
     keccak256, secp256k1_verify,
     secp256k1_ecrecover, sha256, ripemd160, modexp,
     bn254_g1_add, bn254_g1_mul, bn254_pairing,
     blake2f, kzg_point_eval,
     bls12_g1_add, bls12_g1_msm, bls12_g2_add, bls12_g2_msm,
     bls12_pairing, bls12_map_fp_to_g1, bls12_map_fp2_to_g2,
     secp256r1_verify].Nodup := by
  decide

end SyscallIdWord

end Rv64
end EvmAsm
