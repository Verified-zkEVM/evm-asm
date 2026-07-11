/-
  EvmAsm.Stateless.SpecRef.Seam

  The execution-seam interface types, moved out of `Stateless.lean` so
  the seam *implementation* (`SeamShell.lean`, bead `evm-asm-s1d19.3`)
  can be defined below `Stateless.lean` and wired in as
  `verify_stateless_new_payload`'s default without an import cycle.

  * `ChainContext` — `fork.py`, class `ChainContext`
  * `ExecutionSeamInput` — the argument bundle of the call to
    `execution-specs/src/ethereum/forks/amsterdam/stateless.py`
    function `verify_stateless_new_payload` makes to
    `execute_new_payload_request` (`stateless.py:378`)
  * `ExecutionSeam`, `executeAlwaysOk` — the seam abstraction and the
    original stub (kept for comparison/tests; no longer the default).
-/

import EvmAsm.Stateless.SpecRef.WitnessReads

namespace EvmAsm.Stateless.SpecRef

/-- `ChainContext(chain_id, block_hashes, parent_header)` (`fork.py`,
    class `ChainContext`). -/
structure ChainContext where
  chainId : U64
  blockHashes : List Hash32
  parentHeader : Header
  deriving Repr

/-- The exact argument bundle passed to `execute_new_payload_request`
    (`stateless.py:378`). -/
structure ExecutionSeamInput where
  newPayloadRequest : NewPayloadRequest
  preState : WitnessPreState
  chainContext : ChainContext
  transactionPublicKeys : List Bytes

/-- The execution engine, abstracted at the seam. `ok ()` mirrors Python
    returning normally; `error _` mirrors any raised exception. -/
abbrev ExecutionSeam := ExecutionSeamInput → Except SpecError Unit

/-- The original placeholder seam that accepts every payload.  No longer
    the default (see `SeamShell.lean`); kept for tests and for measuring
    the stub↔shell divergence. -/
def executeAlwaysOk : ExecutionSeam := fun _ => .ok ()

end EvmAsm.Stateless.SpecRef
