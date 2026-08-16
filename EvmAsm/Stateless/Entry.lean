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

  The emitted guest now owns the composition boundary: its epilogue decodes
  the schema-prefixed SSZ envelope, branches to the failure sentinel on a
  decode error, and then enters the already-linked validator/verdict pipeline.
  The core `Program` remains an empty structural slot because the raw guest
  epilogue is the image-level owner of the schema decoder and its failure
  branch; keeping that boundary here avoids a second serializer and a second
  set of input-layout constants.

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

  ## Current status

  The previous PR6 decode/header-count diagnostic is no longer the entry
  pipeline. The emitted decoder performs the schema and canonical outer-SSZ
  checks, derives the chain-config and witness-header views consumed by the
  existing validators, and preserves the exact default-failure sentinel for
  malformed input. Header validation, witness DBs, and STF execution remain
  the responsibility of the already-linked verifier machinery.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Stateless.SSZ.Encode.Program

namespace EvmAsm.Stateless

open EvmAsm.Rv64

/-! These definitions are the structural slots for the four spec stages. The
    image-level codegen epilogue currently owns their emitted composition; the
    slots remain the canonical verified-side replacement points. -/

/-- `deserialize_stateless_input` replacement point. -/
def deserialize_stateless_input_step : Program := []

/-- `_default_failed_stateless_output` replacement point. -/
def failed_stateless_output_step : Program := []

/-- `verify_stateless_new_payload` replacement point. -/
def verify_stateless_new_payload_step : Program := []

/-- Spec-shaped entry slots. The emitted image supplies the current boundary;
    the verified `Program` slots remain empty until their machine triples land. -/
def run_stateless_guest : Program :=
  deserialize_stateless_input_step ++
  failed_stateless_output_step ++
  verify_stateless_new_payload_step

end EvmAsm.Stateless
