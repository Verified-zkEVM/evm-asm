/-
  EvmAsm.Evm64.Gas

  Static gas-cost table for the opcode families currently modeled under
  `EvmAsm.Evm64` (GH #117 slice 1).

  The table records Shanghai static/base costs. Dynamic add-ons (EXP byte
  cost, memory expansion, storage cold/warm access, logging data/topic
  costs, etc.) intentionally live outside this first slice.
-/

import EvmAsm.Evm64.LogArgs
import EvmAsm.Evm64.CallArgs

namespace EvmAsm.Evm64

/-- EVM opcode identifiers for opcode families that already have an
    implementation or specification subtree in `EvmAsm.Evm64`. Parameterized
    families keep their EVM width/index as data so handler code can share one
    gas theorem across all concrete opcodes in the family. -/
inductive EvmOpcode where
  | STOP
  | ADD
  | MUL
  | SUB
  | DIV
  | SDIV
  | MOD
  | SMOD
  | EXP
  | SIGNEXTEND
  | KECCAK256
  | ADDRESS
  | ORIGIN
  | CALLER
  | CALLVALUE
  | LT
  | GT
  | SLT
  | SGT
  | EQ
  | ISZERO
  | AND
  | OR
  | XOR
  | NOT
  | BYTE
  | SHL
  | SHR
  | SAR
  | POP
  | MLOAD
  | MSTORE
  | MSTORE8
  | MSIZE
  | JUMP
  | JUMPI
  | PC
  | GAS
  | JUMPDEST
  | CALLDATALOAD
  | CALLDATASIZE
  | CALLDATACOPY
  | CODESIZE
  | CODECOPY
  | GASPRICE
  | RETURNDATASIZE
  | RETURNDATACOPY
  | BLOCKHASH
  | COINBASE
  | TIMESTAMP
  | NUMBER
  | PREVRANDAO
  | GASLIMIT
  | CHAINID
  | SELFBALANCE
  | BASEFEE
  | BLOBHASH
  | BLOBBASEFEE
  | SLOTNUM
  | LOG (kind : LogArgs.Kind)
  | CREATE
  | CREATE2
  | CALL
  | DELEGATECALL
  | STATICCALL
  | RETURN
  | REVERT
  | SELFDESTRUCT
  | INVALID
  | PUSH0
  | PUSH (n : Nat)
  | DUP (n : Nat)
  | SWAP (n : Nat)
  | DUPN
  | SWAPN
  | EXCHANGE
  deriving DecidableEq, Repr

namespace EvmOpcode

/-- Valid immediate width for PUSH1 through PUSH32. -/
def validPushWidth (n : Nat) : Bool :=
  1 ≤ n && n ≤ 32

/-- Valid stack slot index for DUP1 through DUP16. -/
def validDupIndex (n : Nat) : Bool :=
  1 ≤ n && n ≤ 16

/-- Valid stack slot index for SWAP1 through SWAP16. -/
def validSwapIndex (n : Nat) : Bool :=
  1 ≤ n && n ≤ 16

/-- Concrete EVM opcode byte when this identifier denotes one bytecode. Invalid
    parameterized identifiers return `none`, keeping the gas table total while
    making bytecode emission validate widths explicitly. -/
def byte? : EvmOpcode → Option Nat
  | STOP => some 0x00
  | ADD => some 0x01
  | MUL => some 0x02
  | SUB => some 0x03
  | DIV => some 0x04
  | SDIV => some 0x05
  | MOD => some 0x06
  | SMOD => some 0x07
  | EXP => some 0x0a
  | SIGNEXTEND => some 0x0b
  | KECCAK256 => some 0x20
  | ADDRESS => some 0x30
  | ORIGIN => some 0x32
  | CALLER => some 0x33
  | CALLVALUE => some 0x34
  | LT => some 0x10
  | GT => some 0x11
  | SLT => some 0x12
  | SGT => some 0x13
  | EQ => some 0x14
  | ISZERO => some 0x15
  | AND => some 0x16
  | OR => some 0x17
  | XOR => some 0x18
  | NOT => some 0x19
  | BYTE => some 0x1a
  | SHL => some 0x1b
  | SHR => some 0x1c
  | SAR => some 0x1d
  | POP => some 0x50
  | MLOAD => some 0x51
  | MSTORE => some 0x52
  | MSTORE8 => some 0x53
  | MSIZE => some 0x59
  | JUMP => some 0x56
  | JUMPI => some 0x57
  | PC => some 0x58
  | GAS => some 0x5a
  | JUMPDEST => some 0x5b
  | CALLDATALOAD => some 0x35
  | CALLDATASIZE => some 0x36
  | CALLDATACOPY => some 0x37
  | CODESIZE => some 0x38
  | CODECOPY => some 0x39
  | GASPRICE => some 0x3a
  | RETURNDATASIZE => some 0x3d
  | RETURNDATACOPY => some 0x3e
  | BLOCKHASH => some 0x40
  | COINBASE => some 0x41
  | TIMESTAMP => some 0x42
  | NUMBER => some 0x43
  | PREVRANDAO => some 0x44
  | GASLIMIT => some 0x45
  | CHAINID => some 0x46
  | SELFBALANCE => some 0x47
  | BASEFEE => some 0x48
  | BLOBHASH => some 0x49
  | BLOBBASEFEE => some 0x4a
  | SLOTNUM => some 0x4b
  | LOG kind => some (0xa0 + LogArgs.topicCount kind)
  | CREATE => some 0xf0
  | CREATE2 => some 0xf5
  | CALL => some 0xf1
  | DELEGATECALL => some 0xf4
  | STATICCALL => some 0xfa
  | RETURN => some 0xf3
  | REVERT => some 0xfd
  | SELFDESTRUCT => some 0xff
  | INVALID => some 0xfe
  | PUSH0 => some 0x5f
  | PUSH n => if validPushWidth n then some (0x5f + n) else none
  | DUP n => if validDupIndex n then some (0x7f + n) else none
  | SWAP n => if validSwapIndex n then some (0x8f + n) else none
  | DUPN => some 0xe6
  | SWAPN => some 0xe7
  | EXCHANGE => some 0xe8

/-- Shanghai static/base gas cost. Costs that also have dynamic components
    return only the fixed part charged before the dynamic add-on. -/
def staticGasCost : EvmOpcode → Nat
  | STOP => 0
  | ADD => 3
  | MUL => 5
  | SUB => 3
  | DIV => 5
  | SDIV => 5
  | MOD => 5
  | SMOD => 5
  | EXP => 10
  | SIGNEXTEND => 5
  | KECCAK256 => 30
  | ADDRESS => 2
  | ORIGIN => 2
  | CALLER => 2
  | CALLVALUE => 2
  | LT => 3
  | GT => 3
  | SLT => 3
  | SGT => 3
  | EQ => 3
  | ISZERO => 3
  | AND => 3
  | OR => 3
  | XOR => 3
  | NOT => 3
  | BYTE => 3
  | SHL => 3
  | SHR => 3
  | SAR => 3
  | POP => 2
  | MLOAD => 3
  | MSTORE => 3
  | MSTORE8 => 3
  | MSIZE => 2
  | JUMP => 8
  | JUMPI => 10
  | PC => 2
  | GAS => 2
  | JUMPDEST => 1
  | CALLDATALOAD => 3
  | CALLDATASIZE => 2
  | CALLDATACOPY => 3
  | CODESIZE => 2
  | CODECOPY => 3
  | GASPRICE => 2
  | RETURNDATASIZE => 2
  | RETURNDATACOPY => 3
  | BLOCKHASH => 20
  | COINBASE => 2
  | TIMESTAMP => 2
  | NUMBER => 2
  | PREVRANDAO => 2
  | GASLIMIT => 2
  | CHAINID => 2
  | SELFBALANCE => 5
  | BASEFEE => 2
  | BLOBHASH => 3
  | BLOBBASEFEE => 2
  | SLOTNUM => 2
  | LOG _ => 375
  | CREATE => 32000
  | CREATE2 => 32000
  | CALL => 700
  | DELEGATECALL => 700
  | STATICCALL => 700
  | RETURN => 0
  | REVERT => 0
  | SELFDESTRUCT => 5000
  | INVALID => 0
  | PUSH0 => 2
  | PUSH _ => 3
  | DUP _ => 3
  | SWAP _ => 3
  | DUPN => 3
  | SWAPN => 3
  | EXCHANGE => 3

theorem staticGasCost_PUSH (n : Nat) :
    staticGasCost (PUSH n) = 3 := rfl

theorem staticGasCost_DUP (n : Nat) :
    staticGasCost (DUP n) = 3 := rfl

theorem staticGasCost_SWAP (n : Nat) :
    staticGasCost (SWAP n) = 3 := rfl

theorem staticGasCost_DUPN :
    staticGasCost DUPN = 3 := rfl

theorem staticGasCost_SWAPN :
    staticGasCost SWAPN = 3 := rfl

theorem staticGasCost_EXCHANGE :
    staticGasCost EXCHANGE = 3 := rfl

theorem byte?_PUSH_of_valid {n : Nat} (h : validPushWidth n = true) :
    byte? (PUSH n) = some (0x5f + n) := by
  simp [byte?, h]

theorem byte?_DUP_of_valid {n : Nat} (h : validDupIndex n = true) :
    byte? (DUP n) = some (0x7f + n) := by
  simp [byte?, h]

theorem byte?_SWAP_of_valid {n : Nat} (h : validSwapIndex n = true) :
    byte? (SWAP n) = some (0x8f + n) := by
  simp [byte?, h]

theorem byte?_LOG (kind : LogArgs.Kind) :
    byte? (LOG kind) = some (0xa0 + LogArgs.topicCount kind) := rfl

def ofCallKind : CallArgs.Kind → EvmOpcode
  | .call => CALL
  | .delegatecall => DELEGATECALL
  | .staticcall => STATICCALL

theorem byte?_ofCallKind (kind : CallArgs.Kind) :
    byte? (ofCallKind kind) =
      match kind with
      | .call => some 0xf1
      | .delegatecall => some 0xf4
      | .staticcall => some 0xfa := by
  cases kind <;> rfl

inductive CreateKind where
  | create
  | create2
  deriving DecidableEq, Repr

def ofCreateKind : CreateKind → EvmOpcode
  | .create => CREATE
  | .create2 => CREATE2

theorem byte?_ofCreateKind (kind : CreateKind) :
    byte? (ofCreateKind kind) =
      match kind with
      | .create => some 0xf0
      | .create2 => some 0xf5 := by
  cases kind <;> rfl

inductive SizeLikeKind where
  | code
  | returndata
  deriving DecidableEq, Repr

def ofSizeLikeKind : SizeLikeKind → EvmOpcode
  | .code => CODESIZE
  | .returndata => RETURNDATASIZE

theorem byte?_ofSizeLikeKind (kind : SizeLikeKind) :
    byte? (ofSizeLikeKind kind) =
      match kind with
      | .code => some 0x38
      | .returndata => some 0x3d := by
  cases kind <;> rfl

inductive CopyLikeKind where
  | code
  | calldata
  | returndata
  deriving DecidableEq, Repr

def ofCopyLikeKind : CopyLikeKind → EvmOpcode
  | .code => CODECOPY
  | .calldata => CALLDATACOPY
  | .returndata => RETURNDATACOPY

theorem byte?_ofCopyLikeKind (kind : CopyLikeKind) :
    byte? (ofCopyLikeKind kind) =
      match kind with
      | .code => some 0x39
      | .calldata => some 0x37
      | .returndata => some 0x3e := by
  cases kind <;> rfl

inductive ControlFlowKind where
  | jump
  | jumpi
  | pc
  | gas
  | jumpdest
  deriving DecidableEq, Repr

def ofControlFlowKind : ControlFlowKind → EvmOpcode
  | .jump => JUMP
  | .jumpi => JUMPI
  | .pc => PC
  | .gas => GAS
  | .jumpdest => JUMPDEST

theorem byte?_ofControlFlowKind (kind : ControlFlowKind) :
    byte? (ofControlFlowKind kind) =
      match kind with
      | .jump => some 0x56
      | .jumpi => some 0x57
      | .pc => some 0x58
      | .gas => some 0x5a
      | .jumpdest => some 0x5b := by
  cases kind <;> rfl

inductive BlockBlobKind where
  | blockhash
  | blobhash
  | blobbasefee
  | slotnum
  deriving DecidableEq, Repr

def ofBlockBlobKind : BlockBlobKind → EvmOpcode
  | .blockhash => BLOCKHASH
  | .blobhash => BLOBHASH
  | .blobbasefee => BLOBBASEFEE
  | .slotnum => SLOTNUM

theorem byte?_ofBlockBlobKind (kind : BlockBlobKind) :
    byte? (ofBlockBlobKind kind) =
      match kind with
      | .blockhash => some 0x40
      | .blobhash => some 0x49
      | .blobbasefee => some 0x4a
      | .slotnum => some 0x4b := by
  cases kind <;> rfl

theorem staticGasCost_ofControlFlowKind (kind : ControlFlowKind) :
    staticGasCost (ofControlFlowKind kind) =
      match kind with
      | .jump => 8
      | .jumpi => 10
      | .pc => 2
      | .gas => 2
      | .jumpdest => 1 := by
  cases kind <;> rfl

theorem staticGasCost_ofBlockBlobKind (kind : BlockBlobKind) :
    staticGasCost (ofBlockBlobKind kind) =
      match kind with
      | .blockhash => 20
      | .blobhash => 3
      | .blobbasefee => 2
      | .slotnum => 2 := by
  cases kind <;> rfl

theorem staticGasCost_ofSizeLikeKind (kind : SizeLikeKind) :
    staticGasCost (ofSizeLikeKind kind) = 2 := by
  cases kind <;> rfl

theorem staticGasCost_ofCopyLikeKind (kind : CopyLikeKind) :
    staticGasCost (ofCopyLikeKind kind) = 3 := by
  cases kind <;> rfl

theorem staticGasCost_LOG (kind : LogArgs.Kind) :
    staticGasCost (LOG kind) = 375 := rfl

theorem staticGasCost_ofCallKind (kind : CallArgs.Kind) :
    staticGasCost (ofCallKind kind) = 700 := by
  cases kind <;> rfl

theorem staticGasCost_ofCreateKind (kind : CreateKind) :
    staticGasCost (ofCreateKind kind) = 32000 := by
  cases kind <;> rfl

end EvmOpcode

end EvmAsm.Evm64
