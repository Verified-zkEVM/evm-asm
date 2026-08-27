/-
  EvmAsm.Stateless.Unimplemented

  The stateless-guest port reaches `unimplemented_exit` whenever it
  encounters a code path that has not been implemented yet -- most
  notably every EVM precompile, every cryptographic operation we haven't
  routed through an ECALL bridge yet, and every transaction-type
  variant outside the current scope.

  Distinct from HALT (t0 = 0): we use t0 = 0x10 (write_output) to
  surface a 32-byte marker on `OUTPUT_ADDR`, then halt. The marker is
  `0xFE` repeated 8 times to make Unimplemented exits easy to spot
  in a hex dump and distinguishable from a normal SSZ
  `StatelessValidationResult` (the first byte of a normal
  `new_payload_request_root` is unconstrained, but the full 8-byte
  `0xFE..FE` prefix has negligible collision probability).

  This is also distinct from a normal validation failure
  (`successful_validation = false`): "Unimplemented" means the
  RISC-V code refused to even *try* to validate the input, whereas
  `successful_validation = false` means the RISC-V code attempted
  validation and detected a problem.

  Reason codes (the second 8-byte word in the marker is the reason
  code, written by the caller before invoking `unimplemented_exit`):

  | Reason | Code | Meaning |
  |---|---|---|
  | `PRECOMPILE`           | 0x01 | precompile dispatch (a0 holds addr 0x01..0x14) |
  | `TX_TYPE_UNSUPPORTED`  | 0x02 | unsupported transaction envelope |
  | `EIP7702_DELEGATION`   | 0x03 | SetCodeTransaction delegation |
  | `EIP4844_BLOB`         | 0x04 | blob-tx handling |
  | `EIP7609_BAL`          | 0x05 | block access list generation |
  | `WITNESS_MISSING_NODE` | 0x06 | MPT walk hit a missing witness node |
  | `STATE_ROOT_MISMATCH`  | 0x07 | recomputed state root != header |
  | `STF_BODY`             | 0x08 | the STF body itself is not yet implemented |

  ## Memory it reads / writes
  - reads:  caller-supplied reason code via `x10 (a0)`
  - writes: 32 bytes to `OUTPUT_ADDR + 0..32`
  - exits:  `ECALL` with `t0 = 0` (HALT)
-/

module

public import EvmAsm.Rv64.Program
public import EvmAsm.Stateless.MemoryLayout

public section

namespace EvmAsm.Stateless

open EvmAsm.Rv64

/-! ## Reason codes (see table above). -/

def REASON_PRECOMPILE           : Word := 0x01
def REASON_TX_TYPE_UNSUPPORTED  : Word := 0x02
def REASON_EIP7702_DELEGATION   : Word := 0x03
def REASON_EIP4844_BLOB         : Word := 0x04
def REASON_EIP7609_BAL          : Word := 0x05
def REASON_WITNESS_MISSING_NODE : Word := 0x06
def REASON_STATE_ROOT_MISMATCH  : Word := 0x07
def REASON_STF_BODY             : Word := 0x08

/-! ## Header-validation reason codes

    The `stateless_guest` integration body (PR `feat/stateless-guest-
    integration-test`) wires a curated set of K-PR header validators
    into the run_stateless_guest pipeline. Each validator that catches
    a violation maps to one of the codes below; an RLP parse failure
    in any validator maps to `REASON_RLP_PARSE_FAIL_IN_HEADER`. -/

def REASON_POST_MERGE_VIOLATION     : Word := 0x10
def REASON_EXTRA_DATA_TOO_LONG      : Word := 0x11
def REASON_GAS_USED_OVER_LIMIT      : Word := 0x12
def REASON_BLOB_GAS_MISALIGNED      : Word := 0x13
def REASON_BLOB_GAS_OVER_MAX        : Word := 0x14
def REASON_TIMESTAMP_NOT_INCREASING : Word := 0x15
def REASON_NUMBERS_NOT_CONSECUTIVE  : Word := 0x16
def REASON_RLP_PARSE_FAIL_IN_HEADER : Word := 0x17

/-- Address of the public-output region. Mirrors
    `EvmAsm.Codegen.OUTPUT_ADDR = 0xa0010000`. Duplicated here so
    `EvmAsm/Stateless/*` does not pull in the codegen umbrella. -/
def UNIMPL_OUTPUT_ADDR : Word := 0xa0010000

/-- The 8-byte 0xFE.. marker stored at `OUTPUT_ADDR + 0`. -/
def UNIMPL_MARKER : Word := 0xFEFEFEFEFEFEFEFE

/-- Emit an Unimplemented exit. Caller passes the reason code in `a0`
    (`x10`). The body writes the 0xFE marker at `OUTPUT_ADDR + 0`,
    the reason code at `OUTPUT_ADDR + 8`, then halts with `t0 = 0`.

    Frame: 6 instructions. Side effects: writes 16 bytes to
    `OUTPUT_ADDR`, sets `t0 = 0`, then `ECALL`. Does not return. -/
def unimplemented_exit : Program :=
  LI .x6  UNIMPL_OUTPUT_ADDR ;;
  LI .x7  UNIMPL_MARKER ;;
  SD .x6 .x7 0 ;;
  SD .x6 .x10 8 ;;
  LI .x5 0 ;;
  ECALL

end EvmAsm.Stateless
