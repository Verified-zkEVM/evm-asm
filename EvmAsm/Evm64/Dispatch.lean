/-
  EvmAsm.Evm64.Dispatch

  First dispatch slice for GH #106. This module defines the pure opcode-byte
  decoder used by later RV64 jump-table or branch-tree dispatch programs. It is
  stacked on the static gas table slice because both layers share the
  `EvmOpcode` identifier type.
-/

import EvmAsm.Evm64.Gas

namespace EvmAsm.Evm64

namespace EvmOpcode

/-- Decode one EVM opcode byte into the opcode families currently modeled in
    `EvmAsm.Evm64`. Unsupported bytes return `none`; later feature slices can
    extend this table as new opcode handlers land. -/
def decodeByte? : Nat → Option EvmOpcode
  | 0x00 => some STOP
  | 0x01 => some ADD
  | 0x02 => some MUL
  | 0x03 => some SUB
  | 0x04 => some DIV
  | 0x05 => some SDIV
  | 0x06 => some MOD
  | 0x07 => some SMOD
  | 0x0a => some EXP
  | 0x0b => some SIGNEXTEND
  | 0x10 => some LT
  | 0x11 => some GT
  | 0x12 => some SLT
  | 0x13 => some SGT
  | 0x14 => some EQ
  | 0x15 => some ISZERO
  | 0x16 => some AND
  | 0x17 => some OR
  | 0x18 => some XOR
  | 0x19 => some NOT
  | 0x1a => some BYTE
  | 0x1b => some SHL
  | 0x1c => some SHR
  | 0x1d => some SAR
  | 0x20 => some KECCAK256
  | 0x30 => some ADDRESS
  | 0x31 => some BALANCE
  | 0x32 => some ORIGIN
  | 0x33 => some CALLER
  | 0x34 => some CALLVALUE
  | 0x35 => some CALLDATALOAD
  | 0x36 => some CALLDATASIZE
  | 0x37 => some CALLDATACOPY
  | 0x38 => some CODESIZE
  | 0x39 => some CODECOPY
  | 0x3a => some GASPRICE
  | 0x3b => some EXTCODESIZE
  | 0x3c => some EXTCODECOPY
  | 0x3d => some RETURNDATASIZE
  | 0x3e => some RETURNDATACOPY
  | 0x3f => some EXTCODEHASH
  | 0x40 => some BLOCKHASH
  | 0x41 => some COINBASE
  | 0x42 => some TIMESTAMP
  | 0x43 => some NUMBER
  | 0x44 => some PREVRANDAO
  | 0x45 => some GASLIMIT
  | 0x46 => some CHAINID
  | 0x47 => some SELFBALANCE
  | 0x48 => some BASEFEE
  | 0x49 => some BLOBHASH
  | 0x4a => some BLOBBASEFEE
  | 0x4b => some SLOTNUM
  | 0x50 => some POP
  | 0x51 => some MLOAD
  | 0x52 => some MSTORE
  | 0x53 => some MSTORE8
  | 0x56 => some JUMP
  | 0x57 => some JUMPI
  | 0x58 => some PC
  | 0x59 => some MSIZE
  | 0x5a => some GAS
  | 0x5b => some JUMPDEST
  | 0x5c => some TLOAD
  | 0x5d => some TSTORE
  | 0x5e => some MCOPY
  | 0x5f => some PUSH0
  | 0x60 => some (PUSH 1)
  | 0x61 => some (PUSH 2)
  | 0x62 => some (PUSH 3)
  | 0x63 => some (PUSH 4)
  | 0x64 => some (PUSH 5)
  | 0x65 => some (PUSH 6)
  | 0x66 => some (PUSH 7)
  | 0x67 => some (PUSH 8)
  | 0x68 => some (PUSH 9)
  | 0x69 => some (PUSH 10)
  | 0x6a => some (PUSH 11)
  | 0x6b => some (PUSH 12)
  | 0x6c => some (PUSH 13)
  | 0x6d => some (PUSH 14)
  | 0x6e => some (PUSH 15)
  | 0x6f => some (PUSH 16)
  | 0x70 => some (PUSH 17)
  | 0x71 => some (PUSH 18)
  | 0x72 => some (PUSH 19)
  | 0x73 => some (PUSH 20)
  | 0x74 => some (PUSH 21)
  | 0x75 => some (PUSH 22)
  | 0x76 => some (PUSH 23)
  | 0x77 => some (PUSH 24)
  | 0x78 => some (PUSH 25)
  | 0x79 => some (PUSH 26)
  | 0x7a => some (PUSH 27)
  | 0x7b => some (PUSH 28)
  | 0x7c => some (PUSH 29)
  | 0x7d => some (PUSH 30)
  | 0x7e => some (PUSH 31)
  | 0x7f => some (PUSH 32)
  | 0x80 => some (DUP 1)
  | 0x81 => some (DUP 2)
  | 0x82 => some (DUP 3)
  | 0x83 => some (DUP 4)
  | 0x84 => some (DUP 5)
  | 0x85 => some (DUP 6)
  | 0x86 => some (DUP 7)
  | 0x87 => some (DUP 8)
  | 0x88 => some (DUP 9)
  | 0x89 => some (DUP 10)
  | 0x8a => some (DUP 11)
  | 0x8b => some (DUP 12)
  | 0x8c => some (DUP 13)
  | 0x8d => some (DUP 14)
  | 0x8e => some (DUP 15)
  | 0x8f => some (DUP 16)
  | 0x90 => some (SWAP 1)
  | 0x91 => some (SWAP 2)
  | 0x92 => some (SWAP 3)
  | 0x93 => some (SWAP 4)
  | 0x94 => some (SWAP 5)
  | 0x95 => some (SWAP 6)
  | 0x96 => some (SWAP 7)
  | 0x97 => some (SWAP 8)
  | 0x98 => some (SWAP 9)
  | 0x99 => some (SWAP 10)
  | 0x9a => some (SWAP 11)
  | 0x9b => some (SWAP 12)
  | 0x9c => some (SWAP 13)
  | 0x9d => some (SWAP 14)
  | 0x9e => some (SWAP 15)
  | 0x9f => some (SWAP 16)
  | 0xe6 => some DUPN
  | 0xe7 => some SWAPN
  | 0xe8 => some EXCHANGE
  | 0xa0 => some (LOG LogArgs.Kind.log0)
  | 0xa1 => some (LOG LogArgs.Kind.log1)
  | 0xa2 => some (LOG LogArgs.Kind.log2)
  | 0xa3 => some (LOG LogArgs.Kind.log3)
  | 0xa4 => some (LOG LogArgs.Kind.log4)
  | 0xf0 => some CREATE
  | 0xf1 => some CALL
  | 0xf2 => some CALLCODE
  | 0xf3 => some RETURN
  | 0xf4 => some DELEGATECALL
  | 0xf5 => some CREATE2
  | 0xfa => some STATICCALL
  | 0xfd => some REVERT
  | 0xfe => some INVALID
  | 0xff => some SELFDESTRUCT
  | _ => none

/-- Predicate form for dispatch tables that only need to know whether a byte is
    implemented by the current verified opcode surface. -/
def modeledByte (b : Nat) : Prop :=
  (decodeByte? b).isSome

theorem decodeByte?_STOP : decodeByte? 0x00 = some STOP := rfl
theorem decodeByte?_INVALID : decodeByte? 0xfe = some INVALID := rfl

end EvmOpcode

end EvmAsm.Evm64
