# SpecRef v0.5.0 audit

Scope audit for `evm-asm-n9rtz`, against execution-specs `bd8c673`
(`tests-zkevm@v0.5.0`).  The baseline is `tests-zkevm@v0.4.0`
(`a0c182656`).  This is a classification document, not a porting claim.

## Result

The diff changes 27 Amsterdam Python files (+1157/-834).  The current Lean
SpecRef deliberately models the stateless input/output shell, SSZ, witness
decoding helpers, and a small runtime helper module; it cuts at
`execute_new_payload_request`.  The agreed direction is to replace that cut
only along the concrete call graph needed by `run_stateless_guest`: this is a
vertical-slice reference model, not a general-purpose Lean EVM or a port of
every Amsterdam VM API.  EIP-8037 and VM deltas reachable from that call graph
are real reference-model gaps; unrelated generic API reshaping is not work.

Two direct v0.5.0 changes were already present on `main` before this audit:

| Source delta | Current status | Evidence |
|---|---|---|
| `ProtocolFork`: remove Constantinople/ConstantinopleFix/BPO3–BPO5; add StPetersburg | unchanged — already v0.5.0-correct | `9d5ee19a8` updated `Types.lean` and the enum ordering |
| payload `block_access_list` cap becomes `MAX_BYTES_PER_TRANSACTION` | unchanged — already v0.5.0-correct | `9d4f3f995` updated `Ssz.lean` |

## Per-Module Delta Table

| Lean module | v0.5.0 sources examined | Classification | Required follow-up |
|---|---|---|---|
| `Guest.lean` | `stateless_guest.py` | needs-update | Add `_default_failed_stateless_output`; make `run_stateless_guest` catch decoding errors and serialize the sentinel result rather than return `SpecError`. |
| `Stateless.lean` | `stateless.py` | unchanged | The diff is `@final` and documentation only; its only semantic enum delta is already correct in `Types.lean`. |
| `Types.lean` | `stateless.py`, `stateless_ssz.py` | unchanged | Current enum and the payload list cap match v0.5.0.  No new stateless shell fields were added. |
| `Ssz.lean` | `stateless_ssz.py` | needs-update | Update `MAX_WITNESS_NODES` to `2^22`, `MAX_WITNESS_CODES` to `2^18`, `MAX_BYTES_PER_CODE` to `2^16`, `MAX_BYTES_PER_WITNESS_NODE` to `2^10`, and `MAX_PUBLIC_KEYS` to `2^15`. |
| `SszCodec.lean` | `stateless_ssz.py` / remerkleable use | unchanged | No generic codec algorithm changed; only schemas/constants changed. |
| `WitnessState.lean` | `witness_state.py`, `incremental_mpt.py` | new-function-to-add | v0.5.0 adds `storage_clears` to `compute_state_root_and_trie_changes`; that method is currently behind the execution seam and has no Lean port. |
| `Runtime.lean` | `vm/runtime.py` | unchanged | `vm/runtime.py` is absent from the v0.4.0→v0.5.0 diff. |
| `Crypto.lean` | crypto helpers | unchanged | No mapped crypto helper changed. |

`Secp256k1Recover.lean` is additionally present under `SpecRef/`, but is not in
the assigned eight-module source map and none of its mapped source files changed
in this diff.

## Execution-Seam Deltas (New Surface Required)

The following changed source is not currently represented by a SpecRef function.
It cannot be called “unchanged”; faithful v0.5.0 coverage needs a new execution
reference-model layer or a replacement of the current seam.

| Source families | v0.5.0 delta | Classification |
|---|---|---|
| `vm/gas.py`, `fork.py`, `transactions.py`, `blocks.py` | EIP-8037 two-dimensional regular/state gas, `StateGasCosts`, `TX_MAX_GAS_LIMIT`, settlement/check-transaction changes, receipt gas and header `gas_used = max(regular, state)` | new-function-to-add when reached by the guest slice |
| `state_tracker.py`, `witness_state.py`, `incremental_mpt.py`, `block_access_lists.py` | pre-state reads, account deployability, preserving-balance clear, storage clear propagation, BAL state changes | new-function-to-add when reached by the guest slice |
| `vm/__init__.py`, `vm/interpreter.py`, `vm/instructions/{system,storage,stack,environment,keccak,log}.py` | state-gas accounting/refill, full-U256 copy guards and RETURNDATACOPY OOB behavior, create/collision handling, PREVRANDAO/beacon-root behavior, SELFDESTRUCT transfer-only behavior | new-function-to-add when reached by the guest slice |
| `vm/eoa_delegation.py` | EIP-7702 authorization/delegation changes, including one-hop execution | new-function-to-add when reached by the guest slice |
| `requests.py`, `execution_engine/{requests,types}.py`, BLS files, package/doc-only changes | request typing/cleanup and BLS call-site signature adjustments | removed/not currently ported unless shown reachable |

## EIP-8037 Gap

SpecRef currently has only payload/header scalar gas fields and the three blob
schedule constants.  It has no `Evm`, transaction, receipt, gas-accounting, or
state-transition model.  Therefore it models none of EIP-8037: separate regular
and state gas, `block_state_gas_used`, `TX_MAX_GAS_LIMIT`,
`StateGasCosts.NEW_ACCOUNT`, transaction inclusion and settlement, or the
Amsterdam `GasCosts` table.

The modeling decision is now resolved: implement the smallest concrete
execution slice that `run_stateless_guest` calls, including reachable EIP-8037
and VM behavior, and leave unrelated generic VM APIs out of SpecRef.  The
children must demonstrate reachability from the guest call graph before adding a
source function.

## Citation Audit

`scripts/check-spec-refs.sh` initially reported one allowlisted stale path:
`EvmAsm/Stateless/SSZ/HashTreeRoot/ZeroHashes.lean` cited the removed
`amsterdam/_serialize.py`.  The citation was removed in favor of the canonical
consensus SSZ-merkleization reference; the allowlist is now empty.

## Child Work

The child beads created under `evm-asm-n9rtz` correspond to the direct Guest and
SSZ ports, witness-state storage-clear support, the EIP-8037 guest slice, and
the remaining reachable VM/state-transition surface.  Their descriptions name
the exact v0.5.0 source families and acceptance criteria.
