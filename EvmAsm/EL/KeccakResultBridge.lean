/-
  EvmAsm.EL.KeccakResultBridge

  Bridge from the zkVM KECCAK256 accelerator output to the EVM stack word
  pushed by the executable spec (GH #111).
-/

import EvmAsm.EL.RLP.Basic
import EvmAsm.EL.WorldState
import EvmAsm.Evm64.EvmWord

namespace EvmAsm.EL

namespace KeccakResultBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord

/-- The KECCAK accelerator returns exactly 32 hash bytes. -/
abbrev HashBytes := Fin 32 → Byte

/-- Accelerator output payload for `zkvm_keccak256`. -/
structure AcceleratorOutput where
  hash : HashBytes

def hashBytesList (hash : HashBytes) : List Byte :=
  List.ofFn hash

/-- Big-endian byte conversion matching executable-spec `U256.from_be_bytes`. -/
def wordFromBigEndianBytes (bytes : List Byte) : EvmWord :=
  BitVec.ofNat 256 (EvmAsm.EL.RLP.Nat.fromBytesBE bytes)

/-- Distinctive token: KeccakResultBridge.stackWordFromAcceleratorHash #111. -/
def stackWordFromAcceleratorHash (hash : HashBytes) : EvmWord :=
  wordFromBigEndianBytes (hashBytesList hash)

/-- Stack word pushed by KECCAK256 from the accelerator output buffer. -/
def stackWordFromAcceleratorOutput (output : AcceleratorOutput) : EvmWord :=
  stackWordFromAcceleratorHash output.hash

theorem hashBytesList_length (hash : HashBytes) :
    (hashBytesList hash).length = 32 := by
  simp [hashBytesList]

@[simp] theorem wordFromBigEndianBytes_nil :
    wordFromBigEndianBytes [] = 0 := rfl

theorem wordFromBigEndianBytes_cons (byte : Byte) (tail : List Byte) :
    wordFromBigEndianBytes (byte :: tail) =
      BitVec.ofNat 256
        (byte.toNat * 256 ^ tail.length + EvmAsm.EL.RLP.Nat.fromBytesBE tail) := by
  rfl

theorem stackWordFromAcceleratorHash_eq (hash : HashBytes) :
    stackWordFromAcceleratorHash hash =
      BitVec.ofNat 256 (EvmAsm.EL.RLP.Nat.fromBytesBE (hashBytesList hash)) := rfl

theorem stackWordFromAcceleratorOutput_eq (output : AcceleratorOutput) :
    stackWordFromAcceleratorOutput output =
      stackWordFromAcceleratorHash output.hash := rfl

theorem stackWordFromAcceleratorOutput_hash_length (output : AcceleratorOutput) :
    (hashBytesList output.hash).length = 32 :=
  hashBytesList_length output.hash

end KeccakResultBridge

end EvmAsm.EL
