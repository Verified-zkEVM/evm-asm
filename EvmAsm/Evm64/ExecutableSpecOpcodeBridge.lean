/-
  EvmAsm.Evm64.ExecutableSpecOpcodeBridge

  Opcode-byte bridge to the Ethereum executable-spec `Ops` table in
  execution-specs/src/ethereum/forks/frontier/vm/instructions/__init__.py
  (GH #109).
-/

import EvmAsm.Evm64.Dispatch
import EvmAsm.Evm64.Env.Gas
import EvmAsm.Evm64.TerminatingArgs
import Mathlib.Tactic.IntervalCases

namespace EvmAsm.Evm64

namespace ExecutableSpecOpcodeBridge

namespace Ops

def STOP : Nat := 0x00
def SDIV : Nat := 0x05
def SMOD : Nat := 0x07
def KECCAK : Nat := 0x20
def CALLDATALOAD : Nat := 0x35
def CALLDATASIZE : Nat := 0x36
def CALLDATACOPY : Nat := 0x37
def BLOCKHASH : Nat := 0x40
def BLOBHASH : Nat := 0x49
def BLOBBASEFEE : Nat := 0x4a
def SLOTNUM : Nat := 0x4b
def POP : Nat := 0x50
def MLOAD : Nat := 0x51
def MSTORE : Nat := 0x52
def MSTORE8 : Nat := 0x53
def PUSH0 : Nat := 0x5f
def RETURNDATASIZE : Nat := 0x3d
def RETURNDATACOPY : Nat := 0x3e
def CREATE : Nat := 0xf0
def CALL : Nat := 0xf1
def RETURN : Nat := 0xf3
def DELEGATECALL : Nat := 0xf4
def CREATE2 : Nat := 0xf5
def STATICCALL : Nat := 0xfa
def REVERT : Nat := 0xfd
def INVALID : Nat := 0xfe
def SELFDESTRUCT : Nat := 0xff

end Ops

/-- Executable-spec byte for `PUSH1` through `PUSH32`. -/
def execSpecPushByte (n : Nat) : Nat :=
  0x5f + n

/-- Executable-spec byte for `LOG0` through `LOG4`. -/
def execSpecLogByte (kind : LogArgs.Kind) : Nat :=
  0xa0 + LogArgs.topicCount kind

/-- Executable-spec byte for the block/blob opcode family. -/
def execSpecBlockBlobByte : EvmOpcode.BlockBlobKind → Nat
  | .blockhash => Ops.BLOCKHASH
  | .blobhash => Ops.BLOBHASH
  | .blobbasefee => Ops.BLOBBASEFEE
  | .slotnum => Ops.SLOTNUM

/-- Executable-spec byte for the CALL-family opcode classifier. -/
def execSpecCallByte : CallArgs.Kind → Nat
  | .call => Ops.CALL
  | .delegatecall => Ops.DELEGATECALL
  | .staticcall => Ops.STATICCALL

/-- EVM opcode represented by a frame-terminating opcode classifier. -/
def opcodeOfTerminatingKind : TerminatingArgs.Kind → EvmOpcode
  | .stop => .STOP
  | .return_ => .RETURN
  | .revert => .REVERT
  | .invalid => .INVALID
  | .selfdestruct => .SELFDESTRUCT

/-- Executable-spec byte for a frame-terminating opcode classifier. -/
def execSpecTerminatingByte : TerminatingArgs.Kind → Nat
  | .stop => Ops.STOP
  | .return_ => Ops.RETURN
  | .revert => Ops.REVERT
  | .invalid => Ops.INVALID
  | .selfdestruct => Ops.SELFDESTRUCT

theorem decode_execSpecPushByte_of_valid
    {n : Nat} (h_low : 1 ≤ n) (h_high : n ≤ 32) :
    EvmOpcode.decodeByte? (execSpecPushByte n) = some (EvmOpcode.PUSH n) := by
  unfold execSpecPushByte
  interval_cases n <;> rfl

theorem byte?_execSpecPush_of_valid
    {n : Nat} (h_low : 1 ≤ n) (h_high : n ≤ 32) :
    EvmOpcode.byte? (EvmOpcode.PUSH n) = some (execSpecPushByte n) := by
  unfold execSpecPushByte EvmOpcode.byte? EvmOpcode.validPushWidth
  interval_cases n <;> rfl

theorem roundtrip_execSpecPush_of_valid
    {n : Nat} (h_low : 1 ≤ n) (h_high : n ≤ 32) :
    EvmOpcode.byte? (EvmOpcode.PUSH n) = some (execSpecPushByte n) ∧
      EvmOpcode.decodeByte? (execSpecPushByte n) = some (EvmOpcode.PUSH n) :=
  ⟨byte?_execSpecPush_of_valid h_low h_high,
    decode_execSpecPushByte_of_valid h_low h_high⟩

theorem decode_execSpecLogByte (kind : LogArgs.Kind) :
    EvmOpcode.decodeByte? (execSpecLogByte kind) = some (EvmOpcode.LOG kind) := by
  cases kind <;> rfl

theorem byte?_execSpecLog (kind : LogArgs.Kind) :
    EvmOpcode.byte? (EvmOpcode.LOG kind) = some (execSpecLogByte kind) := by
  cases kind <;> rfl

theorem roundtrip_execSpecLog (kind : LogArgs.Kind) :
    EvmOpcode.byte? (EvmOpcode.LOG kind) = some (execSpecLogByte kind) ∧
      EvmOpcode.decodeByte? (execSpecLogByte kind) = some (EvmOpcode.LOG kind) :=
  ⟨byte?_execSpecLog kind, decode_execSpecLogByte kind⟩

/--
Executable-spec roundtrip for STOP, RETURN, REVERT, INVALID, and
SELFDESTRUCT as one opcode family.

Distinctive token:
ExecutableSpecOpcodeBridge.roundtrip_execSpecTerminatingKind #109 #113.
-/
theorem roundtrip_execSpecTerminatingKind (kind : TerminatingArgs.Kind) :
    EvmOpcode.byte? (opcodeOfTerminatingKind kind) =
        some (execSpecTerminatingByte kind) ∧
      EvmOpcode.decodeByte? (execSpecTerminatingByte kind) =
        some (opcodeOfTerminatingKind kind) := by
  cases kind <;> exact ⟨rfl, rfl⟩

/--
Executable-spec roundtrip for the simple environment opcode family.

Distinctive token:
ExecutableSpecOpcodeBridge.roundtrip_execSpecSimpleEnvField #109 #103.
-/
theorem roundtrip_execSpecSimpleEnvField
    (field : Env.SimpleEnvField) :
    EvmOpcode.byte? field.opcode = some field.opcodeByte ∧
      EvmOpcode.decodeByte? field.opcodeByte = some field.opcode := by
  cases field <;> exact ⟨rfl, rfl⟩

/--
Executable-spec roundtrip for BLOCKHASH, BLOBHASH, and BLOBBASEFEE.

Distinctive token:
ExecutableSpecOpcodeBridge.roundtrip_execSpecBlockBlobKind #109 #124 #117.
-/
theorem roundtrip_execSpecBlockBlobKind
    (kind : EvmOpcode.BlockBlobKind) :
    EvmOpcode.byte? (EvmOpcode.ofBlockBlobKind kind) =
        some (execSpecBlockBlobByte kind) ∧
      EvmOpcode.decodeByte? (execSpecBlockBlobByte kind) =
        some (EvmOpcode.ofBlockBlobKind kind) := by
  cases kind <;> exact ⟨rfl, rfl⟩

/--
Executable-spec roundtrip for CALL, DELEGATECALL, and STATICCALL.

Distinctive token:
ExecutableSpecOpcodeBridge.roundtrip_execSpecCallKind #109 #114.
-/
theorem roundtrip_execSpecCallKind (kind : CallArgs.Kind) :
    EvmOpcode.byte? (EvmOpcode.ofCallKind kind) = some (execSpecCallByte kind) ∧
      EvmOpcode.decodeByte? (execSpecCallByte kind) =
        some (EvmOpcode.ofCallKind kind) := by
  cases kind <;> exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_STOP :
    EvmOpcode.byte? EvmOpcode.STOP = some Ops.STOP ∧
      EvmOpcode.decodeByte? Ops.STOP = some EvmOpcode.STOP := by
  exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_KECCAK :
    EvmOpcode.byte? EvmOpcode.KECCAK256 = some Ops.KECCAK ∧
      EvmOpcode.decodeByte? Ops.KECCAK = some EvmOpcode.KECCAK256 := by
  exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_SDIV :
    EvmOpcode.byte? EvmOpcode.SDIV = some Ops.SDIV ∧
      EvmOpcode.decodeByte? Ops.SDIV = some EvmOpcode.SDIV := by
  exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_SMOD :
    EvmOpcode.byte? EvmOpcode.SMOD = some Ops.SMOD ∧
      EvmOpcode.decodeByte? Ops.SMOD = some EvmOpcode.SMOD := by
  exact ⟨rfl, rfl⟩

/-- Distinctive token:
    ExecutableSpecOpcodeBridge.roundtrip_execSpec_CALLDATALOAD #109 #104. -/
theorem roundtrip_execSpec_CALLDATALOAD :
    EvmOpcode.byte? EvmOpcode.CALLDATALOAD = some Ops.CALLDATALOAD ∧
      EvmOpcode.decodeByte? Ops.CALLDATALOAD =
        some EvmOpcode.CALLDATALOAD := by
  exact ⟨rfl, rfl⟩

/-- Distinctive token:
    ExecutableSpecOpcodeBridge.roundtrip_execSpec_CALLDATASIZE #109 #104. -/
theorem roundtrip_execSpec_CALLDATASIZE :
    EvmOpcode.byte? EvmOpcode.CALLDATASIZE = some Ops.CALLDATASIZE ∧
      EvmOpcode.decodeByte? Ops.CALLDATASIZE =
        some EvmOpcode.CALLDATASIZE := by
  exact ⟨rfl, rfl⟩

/-- Distinctive token:
    ExecutableSpecOpcodeBridge.roundtrip_execSpec_CALLDATACOPY #109 #104. -/
theorem roundtrip_execSpec_CALLDATACOPY :
    EvmOpcode.byte? EvmOpcode.CALLDATACOPY = some Ops.CALLDATACOPY ∧
      EvmOpcode.decodeByte? Ops.CALLDATACOPY =
        some EvmOpcode.CALLDATACOPY := by
  exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_POP :
    EvmOpcode.byte? EvmOpcode.POP = some Ops.POP ∧
      EvmOpcode.decodeByte? Ops.POP = some EvmOpcode.POP := by
  exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_MLOAD :
    EvmOpcode.byte? EvmOpcode.MLOAD = some Ops.MLOAD ∧
      EvmOpcode.decodeByte? Ops.MLOAD = some EvmOpcode.MLOAD := by
  exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_MSTORE :
    EvmOpcode.byte? EvmOpcode.MSTORE = some Ops.MSTORE ∧
      EvmOpcode.decodeByte? Ops.MSTORE = some EvmOpcode.MSTORE := by
  exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_MSTORE8 :
    EvmOpcode.byte? EvmOpcode.MSTORE8 = some Ops.MSTORE8 ∧
      EvmOpcode.decodeByte? Ops.MSTORE8 = some EvmOpcode.MSTORE8 := by
  exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_PUSH0 :
    EvmOpcode.byte? EvmOpcode.PUSH0 = some Ops.PUSH0 ∧
      EvmOpcode.decodeByte? Ops.PUSH0 = some EvmOpcode.PUSH0 := by
  exact ⟨rfl, rfl⟩

/-- Distinctive token:
    ExecutableSpecOpcodeBridge.roundtrip_execSpec_RETURNDATASIZE #109 #114. -/
theorem roundtrip_execSpec_RETURNDATASIZE :
    EvmOpcode.byte? EvmOpcode.RETURNDATASIZE = some Ops.RETURNDATASIZE ∧
      EvmOpcode.decodeByte? Ops.RETURNDATASIZE =
        some EvmOpcode.RETURNDATASIZE := by
  exact ⟨rfl, rfl⟩

/-- Distinctive token:
    ExecutableSpecOpcodeBridge.roundtrip_execSpec_RETURNDATACOPY #109 #114. -/
theorem roundtrip_execSpec_RETURNDATACOPY :
    EvmOpcode.byte? EvmOpcode.RETURNDATACOPY = some Ops.RETURNDATACOPY ∧
      EvmOpcode.decodeByte? Ops.RETURNDATACOPY =
        some EvmOpcode.RETURNDATACOPY := by
  exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_CREATE :
    EvmOpcode.byte? EvmOpcode.CREATE = some Ops.CREATE ∧
      EvmOpcode.decodeByte? Ops.CREATE = some EvmOpcode.CREATE := by
  exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_CALL :
    EvmOpcode.byte? EvmOpcode.CALL = some Ops.CALL ∧
      EvmOpcode.decodeByte? Ops.CALL = some EvmOpcode.CALL := by
  exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_RETURN :
    EvmOpcode.byte? EvmOpcode.RETURN = some Ops.RETURN ∧
      EvmOpcode.decodeByte? Ops.RETURN = some EvmOpcode.RETURN := by
  exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_DELEGATECALL :
    EvmOpcode.byte? EvmOpcode.DELEGATECALL = some Ops.DELEGATECALL ∧
      EvmOpcode.decodeByte? Ops.DELEGATECALL = some EvmOpcode.DELEGATECALL := by
  exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_CREATE2 :
    EvmOpcode.byte? EvmOpcode.CREATE2 = some Ops.CREATE2 ∧
      EvmOpcode.decodeByte? Ops.CREATE2 = some EvmOpcode.CREATE2 := by
  exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_REVERT :
    EvmOpcode.byte? EvmOpcode.REVERT = some Ops.REVERT ∧
      EvmOpcode.decodeByte? Ops.REVERT = some EvmOpcode.REVERT := by
  exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_INVALID :
    EvmOpcode.byte? EvmOpcode.INVALID = some Ops.INVALID ∧
      EvmOpcode.decodeByte? Ops.INVALID = some EvmOpcode.INVALID := by
  exact ⟨rfl, rfl⟩

theorem roundtrip_execSpec_SELFDESTRUCT :
    EvmOpcode.byte? EvmOpcode.SELFDESTRUCT = some Ops.SELFDESTRUCT ∧
      EvmOpcode.decodeByte? Ops.SELFDESTRUCT = some EvmOpcode.SELFDESTRUCT := by
  exact ⟨rfl, rfl⟩

end ExecutableSpecOpcodeBridge

end EvmAsm.Evm64
