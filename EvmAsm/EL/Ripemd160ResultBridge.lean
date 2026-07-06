/-
  EvmAsm.EL.Ripemd160ResultBridge

  Bridge from the zkVM RIPEMD160 accelerator output to the EVM stack word
  returned by the precompile-facing executable spec.

  The RIPEMD160 computation boundary returns a raw 20-byte digest. The EVM
  precompile 0x03 returns 32 bytes: 12 leading zero bytes followed by that
  digest, matching execution-specs' `left_pad_zero_bytes(hash_bytes, 32)`.
  Big-endian decoding of the bare 20-byte digest naturally yields the same
  stack word, with the high 12 bytes zero.
-/

import EvmAsm.EL.KeccakResultBridge

namespace EvmAsm.EL

namespace Ripemd160ResultBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord

/-- The RIPEMD160 accelerator returns `zkvm_ripemd160_hash`, a 20-byte array. -/
abbrev HashBytes := Fin 20 → Byte

/-- Accelerator output payload for `zkvm_ripemd160`. -/
structure AcceleratorOutput where
  hash : HashBytes

def hashBytesList (hash : HashBytes) : List Byte :=
  List.ofFn hash

/-- EVM RIPEMD160 returndata: 12 leading zero bytes followed by the digest. -/
def evmOutputBytesFromHash (hash : HashBytes) : List Byte :=
  List.replicate 12 0 ++ hashBytesList hash

/-- EVM RIPEMD160 returndata from an accelerator/software output payload. -/
def evmOutputBytesFromAcceleratorOutput (output : AcceleratorOutput) : List Byte :=
  evmOutputBytesFromHash output.hash

/-- Big-endian byte conversion matching executable-spec `U256.from_be_bytes`. -/
def wordFromBigEndianBytes (bytes : List Byte) : EvmWord :=
  KeccakResultBridge.wordFromBigEndianBytes bytes

/-- Distinctive token: Ripemd160ResultBridge.stackWordFromAcceleratorHash. -/
def stackWordFromAcceleratorHash (hash : HashBytes) : EvmWord :=
  wordFromBigEndianBytes (hashBytesList hash)

/-- Stack word returned by RIPEMD160 from the accelerator output buffer.
The 20-byte hash is left-padded to 32 bytes by big-endian decoding (the
high 12 bytes of the resulting `EvmWord` are zero). -/
def stackWordFromAcceleratorOutput (output : AcceleratorOutput) : EvmWord :=
  stackWordFromAcceleratorHash output.hash

theorem hashBytesList_length (hash : HashBytes) :
    (hashBytesList hash).length = 20 := by
  simp [hashBytesList]

theorem evmOutputBytesFromHash_length (hash : HashBytes) :
    (evmOutputBytesFromHash hash).length = 32 := by
  simp [evmOutputBytesFromHash, hashBytesList]

theorem evmOutputBytesFromHash_take_padding (hash : HashBytes) :
    (evmOutputBytesFromHash hash).take 12 = List.replicate 12 0 := by
  simp [evmOutputBytesFromHash]

theorem evmOutputBytesFromHash_drop_padding (hash : HashBytes) :
    (evmOutputBytesFromHash hash).drop 12 = hashBytesList hash := by
  simp [evmOutputBytesFromHash]

theorem evmOutputBytesFromAcceleratorOutput_length (output : AcceleratorOutput) :
    (evmOutputBytesFromAcceleratorOutput output).length = 32 :=
  evmOutputBytesFromHash_length output.hash

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
    (hashBytesList output.hash).length = 20 :=
  hashBytesList_length output.hash

end Ripemd160ResultBridge

end EvmAsm.EL
