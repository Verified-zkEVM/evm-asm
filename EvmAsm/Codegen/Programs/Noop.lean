/-
  EvmAsm.Codegen.Programs.Noop

  M18 stack-pop / push-zero / halt no-op handler builders. These
  16 opcodes share the same "trusted bytecode, no host state model"
  shape: pop the right number of EVM stack words, optionally push
  32 zero bytes, advance PC by 1 (or halt). Lifted out of
  `Programs/Evm.lean` per the file-size guard at the bottom of
  `EvmAsm/Codegen/Programs.lean`.

  Four builders are exported:
  - `haltHandlers` — RETURN, REVERT, INVALID, SELFDESTRUCT
  - `pushZeroHandlers` — empty (CODESIZE graduated to `codeHandlers` in M33;
    MSIZE/GAS/RETURNDATASIZE have real implementations)
  - `popPushZeroHandlers` — empty (BALANCE and EXTCODESIZE both have
    witness-backed implementations; EXTCODEHASH, BLOBHASH, and BLOCKHASH
    have real implementations in Programs/Evm.lean)
  - `copyNoopHandlers` — empty (CALLDATACOPY/CODECOPY/RETURNDATACOPY all
    have real implementations; CODECOPY graduated to `codeHandlers` in M33)
  - `returnDataHandlers` — RETURNDATASIZE and RETURNDATACOPY

  These opcodes ship with at least one spec-incompliance (returns
  zero / drops side effects) because the dispatcher has no model
  for the relevant state (accounts, calldata, block history, blob
  context, return-data buffers). Trusted bytecode that avoids
  introspecting those subsystems passes through correctly. See
  the CODEGEN.md M18 narrative for the full limitation list.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Codegen.Programs.Modexp
import EvmAsm.Codegen.Programs.NoopHalt
import EvmAsm.Codegen.Programs.NoopReturnData
import EvmAsm.Codegen.Programs.PrecompileRuntime
import EvmAsm.Codegen.Programs.NoopChildFrame
import EvmAsm.Codegen.Programs.Selfdestruct
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- M18 push-zero handlers — now empty.

    All former members have graduated to real env-cell-reading handlers
    in `Programs/Evm.lean`:
    - MSIZE / GAS (M30) → `memoryMetadataHandlers` / `gasHandlers`.
    - RETURNDATASIZE (M32) → `returnDataHandlers`.
    - CODESIZE (M33) → `codeHandlers` (pushes the running bytecode length
      from `env.codeSize`). -/
def pushZeroHandlers : List OpcodeHandlerSpec :=
  []

/-- M18 pop-and-push-zero handlers (BALANCE and EXTCODESIZE).
    This opcode pops one 32-byte input (an address) and pushes a 32-byte zero
    value. Net EVM stack delta = 0.

    Body (4 instructions): overwrite the popped slot with 32 zero
    bytes — same shape as M17's `SLOAD`/`TLOAD`. No `x12` movement
    needed.

    **Known limitations**:
    - BALANCE and EXTCODESIZE both have witness-backed implementations.

    **M21 update**: CALLDATALOAD (0x35) was removed from this group
    and now has a real implementation in `calldataHandlers` (see
    `Programs/Evm.lean`). It reads real calldata bytes from the
    `ziskemu -i` input region.

    **M28 update**: BLOBHASH (0x49) was moved to `blobContextHandlers`
    in `Programs/Evm.lean` with a real blob-hash-list implementation.

    **M29 update**: BLOCKHASH (0x40) was moved to `blockHashHandlers`
    in `Programs/Evm.lean` with a real block-history implementation.

    **M32 update**: EXTCODESIZE (0x3b) and BALANCE (0x31) moved to
    witness-backed implementations (`EvmAccountWitness.lean` / `EvmBalance.lean`). -/
def popPushZeroHandlers : List OpcodeHandlerSpec :=
  []

/-- M18 copy-no-op handlers — now empty.

    All former members have graduated to real handlers in
    `Programs/Evm.lean`:
    - CALLDATACOPY (M21) → `calldataHandlers`.
    - RETURNDATACOPY (M32) → `returnDataHandlers` (EIP-211 bounds against
      the dispatcher-maintained precompile return-data frame).
    - CODECOPY (M33) → `codeHandlers` (verified `Code.evm_codecopy` byte
      loop over the running bytecode, zero-filling past `len(code)`). -/
def copyNoopHandlers : List OpcodeHandlerSpec :=
  []


end EvmAsm.Codegen
