/-
  EvmAsm.Evm64.Accelerators.Types

  Lean-side payload type aliases for the fixed-size byte structs declared in
  `zkvm_accelerators.h`.
-/

module

@[expose] public section
namespace EvmAsm
namespace Accelerators

/-- C `uint8_t`, used by the accelerator ABI payload structs. -/
abbrev Byte := BitVec 8

/-- Fixed-size C byte array payload, matching `struct { uint8_t data[n]; }`. -/
structure ByteArray (n : Nat) where
  data : Fin n → Byte

namespace ByteArray

/-- Convert a fixed-size byte payload to a Lean list in index order. -/
def toList {n : Nat} (bytes : ByteArray n) : List Byte :=
  List.ofFn bytes.data

theorem toList_length {n : Nat} (bytes : ByteArray n) :
    bytes.toList.length = n := by
  simp [toList]

theorem toList_get? {n : Nat} (bytes : ByteArray n) (i : Nat) (h_i : i < n) :
    bytes.toList[i]? = some (bytes.data ⟨i, h_i⟩) := by
  simp [toList, h_i]

@[simp] theorem toList_zero (bytes : ByteArray 0) :
    bytes.toList = [] := by
  simp [toList]

theorem toList_injective {n : Nat} :
    Function.Injective (@toList n) := by
  intro a b h_list
  cases a with
  | mk aData =>
    cases b with
    | mk bData =>
      congr
      funext i
      have h_get := congrArg (fun xs : List Byte => xs[i.val]?) h_list
      simpa [toList_get? { data := aData } i.val i.isLt,
        toList_get? { data := bData } i.val i.isLt] using h_get

theorem toList_eq_iff {n : Nat} (a b : ByteArray n) :
    a.toList = b.toList ↔ a = b :=
  ⟨fun h_list => toList_injective h_list, fun h_eq => by rw [h_eq]⟩

end ByteArray

/-! ## Common byte array structs -/

/-- C `zkvm_bytes_16`. -/
abbrev ZkvmBytes16 := ByteArray 16

/-- C `zkvm_bytes_32`. -/
abbrev ZkvmBytes32 := ByteArray 32

/-- C `zkvm_bytes_48`. -/
abbrev ZkvmBytes48 := ByteArray 48

/-- C `zkvm_bytes_64`. -/
abbrev ZkvmBytes64 := ByteArray 64

/-- C `zkvm_bytes_96`. -/
abbrev ZkvmBytes96 := ByteArray 96

/-- C `zkvm_bytes_128`. -/
abbrev ZkvmBytes128 := ByteArray 128

/-- C `zkvm_bytes_192`. -/
abbrev ZkvmBytes192 := ByteArray 192

/-! ## Hash and signature aliases -/

/-- C `zkvm_keccak256_hash`. -/
abbrev ZkvmKeccak256Hash := ZkvmBytes32

/-- C `zkvm_sha256_hash`. -/
abbrev ZkvmSha256Hash := ZkvmBytes32

/-- C `zkvm_ripemd160_hash`: 20-byte hash padded to 32 bytes. -/
abbrev ZkvmRipemd160Hash := ZkvmBytes32

/-- C `zkvm_secp256k1_hash`. -/
abbrev ZkvmSecp256k1Hash := ZkvmBytes32

/-- C `zkvm_secp256k1_signature`. -/
abbrev ZkvmSecp256k1Signature := ZkvmBytes64

/-- C `zkvm_secp256k1_pubkey`. -/
abbrev ZkvmSecp256k1Pubkey := ZkvmBytes64

/-- C `zkvm_secp256r1_hash`. -/
abbrev ZkvmSecp256r1Hash := ZkvmBytes32

/-- C `zkvm_secp256r1_signature`. -/
abbrev ZkvmSecp256r1Signature := ZkvmBytes64

/-- C `zkvm_secp256r1_pubkey`. -/
abbrev ZkvmSecp256r1Pubkey := ZkvmBytes64

/-! ## BN254 aliases -/

/-- C `zkvm_bn254_g1_point`. -/
abbrev ZkvmBn254G1Point := ZkvmBytes64

/-- C `zkvm_bn254_g2_point`. -/
abbrev ZkvmBn254G2Point := ZkvmBytes128

/-- C `zkvm_bn254_scalar`. -/
abbrev ZkvmBn254Scalar := ZkvmBytes32

/-- C `zkvm_bn254_pairing_pair`. -/
structure ZkvmBn254PairingPair where
  g1 : ZkvmBn254G1Point
  g2 : ZkvmBn254G2Point

/-! ## BLS12-381 aliases -/

/-- C `zkvm_bls12_381_g1_point`. -/
abbrev ZkvmBls12_381G1Point := ZkvmBytes96

/-- C `zkvm_bls12_381_g2_point`. -/
abbrev ZkvmBls12_381G2Point := ZkvmBytes192

/-- C `zkvm_bls12_381_scalar`. -/
abbrev ZkvmBls12_381Scalar := ZkvmBytes32

/-- C `zkvm_bls12_381_fp`. -/
abbrev ZkvmBls12_381Fp := ZkvmBytes48

/-- C `zkvm_bls12_381_fp2`. -/
abbrev ZkvmBls12_381Fp2 := ZkvmBytes96

/-- C `zkvm_bls12_381_g1_msm_pair`. -/
structure ZkvmBls12_381G1MsmPair where
  point : ZkvmBls12_381G1Point
  scalar : ZkvmBls12_381Scalar

/-- C `zkvm_bls12_381_g2_msm_pair`. -/
structure ZkvmBls12_381G2MsmPair where
  point : ZkvmBls12_381G2Point
  scalar : ZkvmBls12_381Scalar

/-- C `zkvm_bls12_381_pairing_pair`. -/
structure ZkvmBls12_381PairingPair where
  g1 : ZkvmBls12_381G1Point
  g2 : ZkvmBls12_381G2Point

/-! ## BLAKE2F and KZG aliases -/

/-- C `zkvm_blake2f_state`. -/
abbrev ZkvmBlake2fState := ZkvmBytes64

/-- C `zkvm_blake2f_message`. -/
abbrev ZkvmBlake2fMessage := ZkvmBytes128

/-- C `zkvm_blake2f_offset`. -/
abbrev ZkvmBlake2fOffset := ZkvmBytes16

/-- C `zkvm_kzg_commitment`. -/
abbrev ZkvmKzgCommitment := ZkvmBytes48

/-- C `zkvm_kzg_proof`. -/
abbrev ZkvmKzgProof := ZkvmBytes48

/-- C `zkvm_kzg_field_element`. -/
abbrev ZkvmKzgFieldElement := ZkvmBytes32

/-! ## Length sanity checks for common output payloads -/

theorem zkvmSha256Hash_length (hash : ZkvmSha256Hash) :
    hash.toList.length = 32 :=
  ByteArray.toList_length hash

theorem zkvmRipemd160Hash_length (hash : ZkvmRipemd160Hash) :
    hash.toList.length = 32 :=
  ByteArray.toList_length hash

theorem zkvmBlake2fState_length (state : ZkvmBlake2fState) :
    state.toList.length = 64 :=
  ByteArray.toList_length state

end Accelerators
end EvmAsm
