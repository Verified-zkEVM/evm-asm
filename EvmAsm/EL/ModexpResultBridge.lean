/-
  EvmAsm.EL.ModexpResultBridge

  Bridge from the zkVM `zkvm_modexp` accelerator output to the executable
  precompile-result surface (precompile 0x05).

  The accelerator writes exactly `mod_len` bytes to the output buffer.
  The EVM precompile 0x05 returns those bytes verbatim as the result data;
  callers that want a big-endian `EvmWord` projection (e.g. when the result
  is consumed via MLOAD or pushed to the stack) get it via
  `wordFromBigEndianBytes`, which yields `0` on the empty buffer and
  zero-extends short buffers naturally (consistent with
  `Ripemd160ResultBridge.wordFromBigEndianBytes`).
-/

module

public import EvmAsm.EL.KeccakResultBridge
public import EvmAsm.Evm64.Accelerators.Status

@[expose] public section

namespace EvmAsm.EL

namespace ModexpResultBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

/-- Variable-width output payload for `zkvm_modexp`. The buffer length is
exactly `mod_len`; the bytes are the big-endian-encoded value of
`(base ^ exp) % modulus`. -/
structure AcceleratorOutput where
  bytes : List Byte
  deriving Repr

/-- Full ECALL result: status code plus output buffer contents. -/
structure AcceleratorResult where
  status : ZkvmStatus
  output : AcceleratorOutput

/-- Big-endian byte conversion matching executable-spec `U256.from_be_bytes`,
shared with the Keccak/SHA256/RIPEMD160 result bridges. -/
def wordFromBigEndianBytes (bytes : List Byte) : EvmWord :=
  KeccakResultBridge.wordFromBigEndianBytes bytes

/-- `EvmWord` projection of the accelerator output buffer.

For `bytes.length ≤ 32` the high `(32 - bytes.length)` bytes of the
resulting `EvmWord` are zero, matching the EVM convention of
left-padding short MODEXP results when they are pushed onto the stack.
For longer buffers the encoding follows `RLP.Nat.fromBytesBE` and
truncates modulo `2^256` via `BitVec.ofNat`.

Distinctive token: ModexpResultBridge.stackWordFromAcceleratorOutput. -/
def stackWordFromAcceleratorOutput (output : AcceleratorOutput) : EvmWord :=
  wordFromBigEndianBytes output.bytes

@[simp] theorem wordFromBigEndianBytes_nil :
    wordFromBigEndianBytes [] = 0 := rfl

theorem wordFromBigEndianBytes_cons (byte : Byte) (tail : List Byte) :
    wordFromBigEndianBytes (byte :: tail) =
      BitVec.ofNat 256
        (byte.toNat * 256 ^ tail.length + EvmAsm.EL.RLP.Nat.fromBytesBE tail) := by
  rfl

theorem stackWordFromAcceleratorOutput_eq (output : AcceleratorOutput) :
    stackWordFromAcceleratorOutput output =
      wordFromBigEndianBytes output.bytes := rfl

theorem stackWordFromAcceleratorOutput_nil
    (output : AcceleratorOutput) (h : output.bytes = []) :
    stackWordFromAcceleratorOutput output = 0 := by
  simp [stackWordFromAcceleratorOutput, h]

theorem acceleratorOutput_bytes_length (output : AcceleratorOutput) :
    output.bytes.length = output.bytes.length := rfl

theorem acceleratorResult_status (result : AcceleratorResult) :
    result.status = result.status := rfl

theorem acceleratorResult_output (result : AcceleratorResult) :
    result.output = result.output := rfl

end ModexpResultBridge

end EvmAsm.EL
