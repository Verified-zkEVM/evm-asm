/-
  EvmAsm.Stateless.Entry

  Top-level `run_stateless_guest` Program. Mirrors the Python
  `execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py:33`
  entry point.

  The top-level shape follows the pinned Amsterdam spec:

  ```
  try deserialize_stateless_input
  except: serialize_stateless_output(_default_failed_stateless_output)
  else:  serialize_stateless_output(verify_stateless_new_payload(input))
  ```

  Step 1 records that shape only. The deserialize step, failed-output branch,
  and verification step below are zero-instruction structural stubs; they do
  not decode input, choose a branch, construct the sentinel, or validate a
  payload. Only the existing serializer remains in the emitted stub. This is
  alignment work, not summit capability.

  Once `Stateless.SSZ.Decode`, `Stateless.Headers`, `Stateless.Witness`,
  `Stateless.Block`, `Stateless.Transaction`, and `Stateless.VM` are populated,
  these slots will be replaced in the canonical order:

  ```
  deserialize_stateless_input
      |
      +-- failure: _default_failed_stateless_output
      |
      +-- success: verify_stateless_new_payload
                         |
                         v
                  serialize_stateless_output
  ```

  ## Memory layout (preconditions)
  - `INPUT_ADDR + INPUT_DATA_OFFSET` holds the host-supplied
    SSZ-encoded `SszStatelessInput`.
  - All RAM in `STATELESS_WORK_BASE .. STATELESS_WORK_BASE + 0x20000000`
    is available for scratch (see `MemoryLayout.lean`).

  ## Side effects (postconditions when fully implemented)
  - Writes the SSZ encoding of `StatelessValidationResult` to
    `OUTPUT_ADDR + 0..N`.
  - Halts with the codegen halt stub.

  ## Step 1 status

  The previous PR6 decode/header-count diagnostic is deliberately removed
  from the entry pipeline. Header validation, witness DBs, and STF execution
  remain unimplemented; later steps will replace the named slots rather than
  grow another parallel entry shape.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Stateless.SSZ.Encode.Program

namespace EvmAsm.Stateless

open EvmAsm.Rv64

/-! The following four definitions are the Step 1 structural slots. The empty
    programs are intentional: wiring a real decoder, sentinel, or verifier
    belongs to later steps. -/

/-- Spec step 1: `deserialize_stateless_input` (structural stub only). -/
def deserialize_stateless_input_step : Program := []

/-- Spec failure branch: `_default_failed_stateless_output` (shape only). -/
def failed_stateless_output_step : Program := []

/-- Spec success step 2: `verify_stateless_new_payload` (structural stub only). -/
def verify_stateless_new_payload_step : Program := []

/-- Spec-shaped Step 1 entry. The branch selection is not implemented yet;
    the named slots make the later replacement points explicit. -/
def run_stateless_guest : Program :=
  deserialize_stateless_input_step ++
  failed_stateless_output_step ++
  verify_stateless_new_payload_step ++
  EvmAsm.Stateless.SSZ.Encode.serialize_stateless_output

end EvmAsm.Stateless
