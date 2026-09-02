/-
  EvmAsm.Codegen.GuestHandlerAddrs

  GENERATED — do not edit by hand.
  `python3 scripts/asm_to_program.py handler-addrs` regenerates this
  from `scripts/asm-fixtures/symbol-addresses.tsv` (the linker-facts
  table): one row per `h_`-prefixed `.text` symbol of the linked
  `stateless_guest`, i.e. the opcode-handler label family that the
  `.data` jump table `opcode_handlers` dispatches to.

  Why this file exists (GH #13229). `opcode_handlers` is emitted as
  256 `.dword <label>` entries, so its CONTENTS are chosen by the
  linker, not by the emitter — unlike `opcode_gas_costs`, whose
  dwords are numbers `staticGasCost` already produces in Lean.
  `Proofs.OpcodeTables.opcodeHandlerEntries` is consequently
  parameterised by a resolver `addrOf : String → Word`; this table
  is the shipped resolver, and
  `Proofs.GuestDataImage.guestHandlerAddr` wraps it.

  Rows cite `GuestAddrs.<label>` BY NAME, so no address is copied
  into a second Lean file and `GuestAddrs.lean` remains the single
  file that churns on guest layout drift.  A superset of the labels
  actually reachable from `opcodeHandlerLabels` is fine (extra rows
  are never looked up); a MISSING row would resolve to the default
  and is caught against the ELF by
  `scripts/check-opcode-tables.sh`.
-/

module

public import EvmAsm.Codegen.GuestAddrs

@[expose] public section
namespace EvmAsm.Codegen.GuestHandlerAddrs

/-- Handler label ↦ its linked `.text` address, by name. -/
def handlerAddrRows : List (String × Nat) :=
  [ ("h_ADD", GuestAddrs.h_ADD)
  , ("h_ADDMOD", GuestAddrs.h_ADDMOD)
  , ("h_ADDRESS", GuestAddrs.h_ADDRESS)
  , ("h_AND", GuestAddrs.h_AND)
  , ("h_BALANCE", GuestAddrs.h_BALANCE)
  , ("h_BASEFEE", GuestAddrs.h_BASEFEE)
  , ("h_BLOBBASEFEE", GuestAddrs.h_BLOBBASEFEE)
  , ("h_BLOBHASH", GuestAddrs.h_BLOBHASH)
  , ("h_BLOCKHASH", GuestAddrs.h_BLOCKHASH)
  , ("h_BYTE", GuestAddrs.h_BYTE)
  , ("h_CALL", GuestAddrs.h_CALL)
  , ("h_CALLCODE", GuestAddrs.h_CALLCODE)
  , ("h_CALLDATACOPY", GuestAddrs.h_CALLDATACOPY)
  , ("h_CALLDATALOAD", GuestAddrs.h_CALLDATALOAD)
  , ("h_CALLDATASIZE", GuestAddrs.h_CALLDATASIZE)
  , ("h_CALLER", GuestAddrs.h_CALLER)
  , ("h_CALLVALUE", GuestAddrs.h_CALLVALUE)
  , ("h_CHAINID", GuestAddrs.h_CHAINID)
  , ("h_CLZ", GuestAddrs.h_CLZ)
  , ("h_CODECOPY", GuestAddrs.h_CODECOPY)
  , ("h_CODESIZE", GuestAddrs.h_CODESIZE)
  , ("h_COINBASE", GuestAddrs.h_COINBASE)
  , ("h_CREATE", GuestAddrs.h_CREATE)
  , ("h_CREATE2", GuestAddrs.h_CREATE2)
  , ("h_DELEGATECALL", GuestAddrs.h_DELEGATECALL)
  , ("h_DIV", GuestAddrs.h_DIV)
  , ("h_DUP1", GuestAddrs.h_DUP1)
  , ("h_DUP10", GuestAddrs.h_DUP10)
  , ("h_DUP11", GuestAddrs.h_DUP11)
  , ("h_DUP12", GuestAddrs.h_DUP12)
  , ("h_DUP13", GuestAddrs.h_DUP13)
  , ("h_DUP14", GuestAddrs.h_DUP14)
  , ("h_DUP15", GuestAddrs.h_DUP15)
  , ("h_DUP16", GuestAddrs.h_DUP16)
  , ("h_DUP2", GuestAddrs.h_DUP2)
  , ("h_DUP3", GuestAddrs.h_DUP3)
  , ("h_DUP4", GuestAddrs.h_DUP4)
  , ("h_DUP5", GuestAddrs.h_DUP5)
  , ("h_DUP6", GuestAddrs.h_DUP6)
  , ("h_DUP7", GuestAddrs.h_DUP7)
  , ("h_DUP8", GuestAddrs.h_DUP8)
  , ("h_DUP9", GuestAddrs.h_DUP9)
  , ("h_DUPN", GuestAddrs.h_DUPN)
  , ("h_EQ", GuestAddrs.h_EQ)
  , ("h_EXCHANGE", GuestAddrs.h_EXCHANGE)
  , ("h_EXP", GuestAddrs.h_EXP)
  , ("h_EXTCODECOPY", GuestAddrs.h_EXTCODECOPY)
  , ("h_EXTCODEHASH", GuestAddrs.h_EXTCODEHASH)
  , ("h_EXTCODESIZE", GuestAddrs.h_EXTCODESIZE)
  , ("h_GAS", GuestAddrs.h_GAS)
  , ("h_GASLIMIT", GuestAddrs.h_GASLIMIT)
  , ("h_GASPRICE", GuestAddrs.h_GASPRICE)
  , ("h_GT", GuestAddrs.h_GT)
  , ("h_INVALID", GuestAddrs.h_INVALID)
  , ("h_ISZERO", GuestAddrs.h_ISZERO)
  , ("h_JUMP", GuestAddrs.h_JUMP)
  , ("h_JUMPDEST", GuestAddrs.h_JUMPDEST)
  , ("h_JUMPI", GuestAddrs.h_JUMPI)
  , ("h_KECCAK256", GuestAddrs.h_KECCAK256)
  , ("h_LOG0", GuestAddrs.h_LOG0)
  , ("h_LOG1", GuestAddrs.h_LOG1)
  , ("h_LOG2", GuestAddrs.h_LOG2)
  , ("h_LOG3", GuestAddrs.h_LOG3)
  , ("h_LOG4", GuestAddrs.h_LOG4)
  , ("h_LT", GuestAddrs.h_LT)
  , ("h_MCOPY", GuestAddrs.h_MCOPY)
  , ("h_MLOAD", GuestAddrs.h_MLOAD)
  , ("h_MOD", GuestAddrs.h_MOD)
  , ("h_MSIZE", GuestAddrs.h_MSIZE)
  , ("h_MSTORE", GuestAddrs.h_MSTORE)
  , ("h_MSTORE8", GuestAddrs.h_MSTORE8)
  , ("h_MUL", GuestAddrs.h_MUL)
  , ("h_MULMOD", GuestAddrs.h_MULMOD)
  , ("h_NOT", GuestAddrs.h_NOT)
  , ("h_NUMBER", GuestAddrs.h_NUMBER)
  , ("h_OR", GuestAddrs.h_OR)
  , ("h_ORIGIN", GuestAddrs.h_ORIGIN)
  , ("h_PC", GuestAddrs.h_PC)
  , ("h_POP", GuestAddrs.h_POP)
  , ("h_PREVRANDAO", GuestAddrs.h_PREVRANDAO)
  , ("h_PUSH0", GuestAddrs.h_PUSH0)
  , ("h_PUSH1", GuestAddrs.h_PUSH1)
  , ("h_PUSH10", GuestAddrs.h_PUSH10)
  , ("h_PUSH11", GuestAddrs.h_PUSH11)
  , ("h_PUSH12", GuestAddrs.h_PUSH12)
  , ("h_PUSH13", GuestAddrs.h_PUSH13)
  , ("h_PUSH14", GuestAddrs.h_PUSH14)
  , ("h_PUSH15", GuestAddrs.h_PUSH15)
  , ("h_PUSH16", GuestAddrs.h_PUSH16)
  , ("h_PUSH17", GuestAddrs.h_PUSH17)
  , ("h_PUSH18", GuestAddrs.h_PUSH18)
  , ("h_PUSH19", GuestAddrs.h_PUSH19)
  , ("h_PUSH2", GuestAddrs.h_PUSH2)
  , ("h_PUSH20", GuestAddrs.h_PUSH20)
  , ("h_PUSH21", GuestAddrs.h_PUSH21)
  , ("h_PUSH22", GuestAddrs.h_PUSH22)
  , ("h_PUSH23", GuestAddrs.h_PUSH23)
  , ("h_PUSH24", GuestAddrs.h_PUSH24)
  , ("h_PUSH25", GuestAddrs.h_PUSH25)
  , ("h_PUSH26", GuestAddrs.h_PUSH26)
  , ("h_PUSH27", GuestAddrs.h_PUSH27)
  , ("h_PUSH28", GuestAddrs.h_PUSH28)
  , ("h_PUSH29", GuestAddrs.h_PUSH29)
  , ("h_PUSH3", GuestAddrs.h_PUSH3)
  , ("h_PUSH30", GuestAddrs.h_PUSH30)
  , ("h_PUSH31", GuestAddrs.h_PUSH31)
  , ("h_PUSH32", GuestAddrs.h_PUSH32)
  , ("h_PUSH4", GuestAddrs.h_PUSH4)
  , ("h_PUSH5", GuestAddrs.h_PUSH5)
  , ("h_PUSH6", GuestAddrs.h_PUSH6)
  , ("h_PUSH7", GuestAddrs.h_PUSH7)
  , ("h_PUSH8", GuestAddrs.h_PUSH8)
  , ("h_PUSH9", GuestAddrs.h_PUSH9)
  , ("h_RETURN", GuestAddrs.h_RETURN)
  , ("h_RETURNDATACOPY", GuestAddrs.h_RETURNDATACOPY)
  , ("h_RETURNDATASIZE", GuestAddrs.h_RETURNDATASIZE)
  , ("h_REVERT", GuestAddrs.h_REVERT)
  , ("h_SAR", GuestAddrs.h_SAR)
  , ("h_SDIV", GuestAddrs.h_SDIV)
  , ("h_SDIV_done", GuestAddrs.h_SDIV_done)
  , ("h_SELFBALANCE", GuestAddrs.h_SELFBALANCE)
  , ("h_SELFDESTRUCT", GuestAddrs.h_SELFDESTRUCT)
  , ("h_SGT", GuestAddrs.h_SGT)
  , ("h_SHL", GuestAddrs.h_SHL)
  , ("h_SHR", GuestAddrs.h_SHR)
  , ("h_SIGNEXTEND", GuestAddrs.h_SIGNEXTEND)
  , ("h_SLOAD", GuestAddrs.h_SLOAD)
  , ("h_SLOTNUM", GuestAddrs.h_SLOTNUM)
  , ("h_SLT", GuestAddrs.h_SLT)
  , ("h_SMOD", GuestAddrs.h_SMOD)
  , ("h_SMOD_done", GuestAddrs.h_SMOD_done)
  , ("h_SSTORE", GuestAddrs.h_SSTORE)
  , ("h_STATICCALL", GuestAddrs.h_STATICCALL)
  , ("h_STOP", GuestAddrs.h_STOP)
  , ("h_SUB", GuestAddrs.h_SUB)
  , ("h_SWAP1", GuestAddrs.h_SWAP1)
  , ("h_SWAP10", GuestAddrs.h_SWAP10)
  , ("h_SWAP11", GuestAddrs.h_SWAP11)
  , ("h_SWAP12", GuestAddrs.h_SWAP12)
  , ("h_SWAP13", GuestAddrs.h_SWAP13)
  , ("h_SWAP14", GuestAddrs.h_SWAP14)
  , ("h_SWAP15", GuestAddrs.h_SWAP15)
  , ("h_SWAP16", GuestAddrs.h_SWAP16)
  , ("h_SWAP2", GuestAddrs.h_SWAP2)
  , ("h_SWAP3", GuestAddrs.h_SWAP3)
  , ("h_SWAP4", GuestAddrs.h_SWAP4)
  , ("h_SWAP5", GuestAddrs.h_SWAP5)
  , ("h_SWAP6", GuestAddrs.h_SWAP6)
  , ("h_SWAP7", GuestAddrs.h_SWAP7)
  , ("h_SWAP8", GuestAddrs.h_SWAP8)
  , ("h_SWAP9", GuestAddrs.h_SWAP9)
  , ("h_SWAPN", GuestAddrs.h_SWAPN)
  , ("h_TIMESTAMP", GuestAddrs.h_TIMESTAMP)
  , ("h_TLOAD", GuestAddrs.h_TLOAD)
  , ("h_TSTORE", GuestAddrs.h_TSTORE)
  , ("h_XOR", GuestAddrs.h_XOR)
  , ("h_invalid", GuestAddrs.h_invalid)
  ]

end EvmAsm.Codegen.GuestHandlerAddrs
