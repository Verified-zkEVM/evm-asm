# tests-zkevm@v0.6.0 migration: scope and decomposition

Scoping document for bead `evm-asm-0w05f` (GH #10207): migrate the whole
stack from `tests-zkevm@v0.5.0` (execution-specs `bd8c673`) to
`tests-zkevm@v0.6.0` (execution-specs
`40f956fab76463e113cb7f0dda4a8a263a1ee776`, published 2026-07-10).
SpecRef reached full-suite v0.5.0 conformance (25,477 fixtures, succ
FAIL 0); re-establishing that at v0.6.0 is the milestone.

All Python line numbers below are at `40f956fab`,
`src/ethereum/forks/amsterdam/` unless noted. The upstream fork diff is
17 files, +479/−457; nothing outside `forks/amsterdam/` that we depend
on changed (other forks got the same EIP-155 refactor; no shared
`src/ethereum/*` module changed).

**Pin reconciliation (phase 0, resolved):** the working submodule and
the gitlink both sit at `bd8c673` — the `3496e719b` discrepancy flagged
in the bead does not exist on current `main`. `scripts/eest-fixture-tag.txt`
already reads `tests-zkevm@v0.5.0` (not v0.4.0 as the bead feared).
The `tests-zkevm@v0.6.0` release exists on `ethereum/execution-specs`
with the `fixtures_zkevm.tar.gz` asset (496,163,081 bytes, published
2026-07-10T16:22Z).

The fork's `__init__.py` docstring newly *lists* EIP-2780/7708/7778/
7843/7976/7981/8024/8037/8038/8282 — those were already implemented in
v0.5.0 (we have conformance checks for them); the doc additions are not
new behavior. The behavioral deltas are the eleven items in §1.

## 1. Upstream behavioral changes (bd8c673 → 40f956fab)

### C1. Stateless input schema id: `0x0001` → `0x1501` — **wire format**

`stateless_ssz.py:89-98`. The 2-byte big-endian schema-id prefix on
guest input bytes becomes `fork_index << 8 | schema_revision` with
`ProtocolFork.Amsterdam = 0x15` and revision `0x01`: bytes `15 01`
instead of `00 01`. Every v0.5.0 fixture input is rejected by a v0.6.0
decoder and vice versa.

### C2. `ProtocolFork` StrEnum → IntEnum; `ForkConfig` loses `fork` + `blob_schedule` — **wire format**

`stateless.py:81-105` (IntEnum, Frontier=0x01 … Amsterdam=0x15),
`stateless.py:142-149` (`ForkConfig` = `activation` only),
`stateless_ssz.py:206-215` (`SszForkConfig` = `{activation}`,
`SszChainConfig` = `{chain_id, fork_config}`). Deleted:
`BlobSchedule`, `SszBlobSchedule`, `SszOptionalBlobSchedule`,
`_protocol_fork_to_ssz`/`_ssz_to_protocol_fork` and the blob-schedule
conversion helpers. The SSZ `ChainConfig` container shrinks: inside
`ForkConfig` only the (variable-size) `SszForkActivation` remains, so
all fixed-part offsets of `SszChainConfig` and the outer
`SszStatelessInput` change.

`validate_chain_config` (`stateless.py:311-333`) no longer checks
"active fork is Amsterdam" or the blob-schedule match —
`UnsupportedForkConfigError` and `_expected_amsterdam_blob_schedule`
are deleted. Fork identity is now carried by the schema id (C1), not by
a payload field. `InactiveForkConfigError` / activation checking stay.

### C3. Host skips unrecoverable public keys — host-side only

`stateless_host.py:109-122`: `build_stateless_input` wraps
`recover_transaction_public_key` in `try/except InvalidSignatureError:
continue`. Guest side unchanged in effect: `fork.py:320-324` still
requires `len(public_keys) == len(block.transactions)`, so an invalid
payload containing an unrecoverable-signature tx now yields a *short*
key list and fails validation gracefully (instead of crashing the host
builder). Affects our host-side input builder
(`scripts/eest-stateless-to-input.py`) only if it mirrors
`build_stateless_input`; fixtures carry the recorded bytes.

### C4. EIP-155 chain-id validation moved into `process_transaction` — **consensus**

New `transactions.py:772-787 chain_id(tx)`: legacy v∈{27,28} → `None`;
legacy v<35 → `InvalidSignatureError`; else `(v−35)>>1`; typed txs
return their `chain_id` field. `recover_sender` (`transactions.py:790`)
loses its `chain_id` parameter and derives the recovery chain id from
the tx itself (0 for pre-155). `process_transaction`
(`fork.py:1051-1057`) raises the new `WrongChainIdError`
(`exceptions.py:15`) when `chain_id(tx) ≠ block_env.chain_id` — this
check happens *before* sender recovery, and *per transaction* rather
than inside signature recovery. Semantic delta vs v0.5.0: a mismatched
chain id used to surface as an invalid-signature failure from
`recover_sender`'s signing-hash mismatch (wrong sender → nonce/balance
failure) when using recorded public keys; now it is an explicit
`InvalidTransaction` → invalid block, *regardless* of the supplied
public key.

### C5. EIP-2780 intrinsic-cost rework: state-dependent charges move to the top frame — **consensus (gas)**

`transactions.py:638-769 calculate_intrinsic_cost` +
`transactions.py:584-635 validate_transaction`:

- Create txs: intrinsic no longer charges `StateGasCosts.NEW_ACCOUNT`
  (state) — moved to `prepare_dispatch` (C7), conditioned on the target
  leaf being `EMPTY_ACCOUNT` in pre-state. `init_code_cost` split out
  of `recipient_regular_gas` into its own term (affects the floor
  anchor, next bullet).
- Calldata floor (EIP-7623/7976): anchored on `base_regular_gas =
  TX_BASE + recipient_regular_gas` (which includes `CREATE_ACCESS` or
  `COLD_ACCOUNT_ACCESS`+`TX_VALUE_COST` and `TRANSFER_LOG_COST`)
  instead of bare `TX_BASE` (`transactions.py:734-745`). `init_code_gas`
  is *not* part of the anchor.
- SetCode txs: intrinsic charges only
  `REGULAR_PER_AUTH_BASE_COST × |auths|` (regular). The v0.5.0
  worst-case `(ACCOUNT_WRITE)` regular and `(NEW_ACCOUNT + AUTH_BASE)`
  state charges per tuple (and their refund machinery) are deleted —
  replaced by exact state-dependent charges in `set_delegation` (C6).
- `validate_transaction`: `intrinsic_gas` computed via explicit
  `Uint()` coercions (type-level); the init-code-size check
  (`InitCodeTooLargeError`) moves *up*, before the `TX_MAX_GAS_LIMIT` /
  blob-gas / nonce checks (`transactions.py:591-597` region) —
  exception-*class* selection changes for txs violating several limits
  at once.
- `IntrinsicGasCost` fields become `RegularGas`/`StateGas` NewTypes
  (`fork_types.py:37-63`, incl. new `StateGasPerByte` with `__mul__`)
  — type-level, no numeric change. `StateGasCosts` constants unchanged
  (1530/byte; 120/64/23 bytes).

### C6. EIP-7702 `set_delegation` rewrite: refund machinery → exact charges — **consensus (gas)**

`vm/eoa_delegation.py:165-284`. `validate_authorization` returns just
the authority address. `set_delegation(evm)` (was `(message) →
(state_refund, regular_refund)`) now runs at the top frame and charges
per valid authorization, on top of the intrinsic per-tuple base:

- `NEW_ACCOUNT` (state) iff the authority leaf does not exist;
- `ACCOUNT_WRITE` (regular) iff this is the tx's first write to the
  authority (`written_accounts` starts as `{origin}` ∪ `{recipient if
  value>0}`; each authority added once);
- `AUTH_BASE` (state) iff a net-new delegation indicator is written
  (not delegated pre-tx, none set earlier in this tx, and this auth
  sets one — `NULL_ADDRESS` clears never charge); at most once per
  authority, never credited back.

All v0.5.0 refund plumbing (`message.state_gas_reservoir +=`,
returned refund tuple, `MessageCallOutput.state_refund`) is deleted.
Code resolution for the frame moved out (C7). OOG inside
`set_delegation` → `ExceptionalHalt` at the top frame (C8 rollback).

### C7. New `prepare_dispatch` at depth 0 — **consensus (gas + delegation resolution)**

`vm/interpreter.py:246-312`. Runs after `set_delegation`, before
dispatch; must not mutate tx state:

- create tx: charge `NEW_ACCOUNT` (state) iff
  `get_pre_state_account(target) == EMPTY_ACCOUNT`;
- call tx: charge `NEW_ACCOUNT` (state) iff `value>0` and recipient
  not alive; resolve EIP-7702 delegation on the *recipient's* code —
  charging `WARM_ACCESS` **or** `COLD_ACCOUNT_ACCESS` by
  `evm.accessed_addresses` membership (v0.5.0 always charged cold) —
  set `disable_precompiles`, point `code`/`code_address` at the
  delegate, recompute `valid_jump_destinations`.

Correspondingly `utils/message.py:63-69 prepare_message` no longer
loads recipient code (`code = b""`); `process_message_call`
(`vm/interpreter.py:110-173`) loses the delegation-resolution block and
the `set_delegation` call.

### C8. Top-frame preparation rollback + state-gas bookkeeping rework — **consensus (gas)**

`vm/interpreter.py:315-375 process_message` at depth 0: snapshot; run
`set_delegation` (folding its state-gas use into the frame baseline:
`auth_state_gas_used = frame_state_gas_used(evm)`,
`message.state_gas_reservoir = evm.state_gas_left`, spill reset) then
`prepare_dispatch`; on `ExceptionalHalt`: restore snapshot and
reservoir, zero `auth_state_gas_used`, refill, consume *all* gas
(`gas_left = 0`), return errored frame without dispatching.

`vm/__init__.py`: `Evm.state_gas_used` (running counter) deleted;
new `Evm.auth_state_gas_used`; new `frame_state_gas_used(evm) =
reservoir_at_entry − state_gas_left + state_gas_spilled`
(`vm/__init__.py:259-283`); `refill_frame_state_gas` simplifies to
`state_gas_left = message.state_gas_reservoir`
(`vm/__init__.py:240-256`); `credit_state_gas_refund` and
`incorporate_child_on_success` drop the counter updates;
`charge_state_gas` (`vm/gas.py:314-339`) drops it too.
`MessageCallOutput` (`vm/interpreter.py:83-107`) loses `state_refund`
and `created_target_alive`; `state_gas_used` is now computed as
`frame_state_gas_used(evm) + evm.auth_state_gas_used`.

### C9. Block accounting: calldata floor binds at block level; create refund deleted — **consensus (gas)**

`fork.py:1010-1120 process_transaction`:

- the post-execution top-level-create refund block (v0.5.0: refund
  `NEW_ACCOUNT` when the create failed or the target was alive) is
  deleted — superseded by the conditional charge in C7;
- `tx_state_gas = intrinsic_state + state_gas_used` (no
  `state_refund` subtraction);
- `tx_regular_gas = max(tx_gas_used_before_refund − max(0,
  tx_state_gas), intrinsic.calldata_floor)` — the EIP-7623/7976 floor
  now binds the *regular-gas dimension of block accounting* (state gas
  subtracted first), where v0.5.0 applied the floor to the receipt
  gas... **note:** v0.5.0 applied the floor inside
  `process_transaction` before splitting dimensions; the v0.6.0 form
  changes which transactions the floor binds for (state-heavy txs no
  longer get the floor discounted by their state spending) and the
  floor value itself is bigger (C5 anchor). Receipt
  `cumulative_gas_used` and `block.gas_used` both flow from these.

### C10. SSTORE: access charge precedes BAL slot-read recording — **consensus (gas + BAL)**

`vm/instructions/storage.py:67-148 sstore`: compute cold/warm access
cost first; sentry `check_gas(max(access_cost, CALL_STIPEND+1))`
*before* `get_storage_original`/`get_storage` record the slot in the
Block Access List; only then mark the key accessed. v0.5.0 checked the
bare stipend, read storage (recording the slot in the BAL), then
charged. Divergence window: an SSTORE that dies with gas in
`(CALL_STIPEND, access_cost]` — post-repricing cold access (2100+) can
exceed the stipend (2300)... cold storage access cost vs stipend: the
comment says the stipend sentry alone is no longer sufficient. Failing
earlier also keeps the slot *out* of the BAL and out of
`accessed_storage_keys`.

### C11. `generic_create`: conditional NEW_ACCOUNT + reordered gas splits — **consensus (gas)**

`vm/instructions/system.py:65-166`:

- v0.5.0 charged `NEW_ACCOUNT` state gas unconditionally up front
  (pay-before-execute, refund on every failure path and on
  target-alive success). v0.6.0 charges it only when
  `not is_account_alive(target)` ("charge decided by existence alone"),
  *after* the balance/nonce/depth early-out (which no longer touches
  state gas), and refills only-if-charged on collision and on child
  error; no more target-alive refund on success.
- Ordering: the state-gas charge now happens *before*
  `max_message_call_gas(gas_left)` — a spill (reservoir empty, state
  gas taken from `gas_left`) now reduces the 63/64 child allowance;
  in v0.5.0 the charge also preceded the split, but on the early-out
  paths gas/reservoir moves differ. The reservoir hand-off to the child
  moves after the collision check.
- `selfdestruct` (`system.py:635`): comment-only changes (EIP-8038
  comment dropped, transfer-log comment reworded).

### C12. EIP-8282 builder predeploy addresses changed — **consensus (system contracts)**

`fork.py:141-146`: `BUILDER_DEPOSIT_CONTRACT_ADDRESS`
`0x0000884d2AA32eAa155F59A2f24eFa73D9008282` →
`0x0000BFF46984E3725691FA540A8C7589300D8282`;
`BUILDER_EXIT_CONTRACT_ADDRESS`
`0x000014574A74c805590AFF9499fc7A690f008282` →
`0x000064D678505AD48F8CCB093BC65613800E8282`.

Doc-only / type-only (no port action beyond line-anchor refresh):
`state_tracker.py` (docstrings; `pre_state` field comment),
`RegularGas`/`StateGas` NewTypes, gas.py docstring deletions
(`AUTH_TUPLE_BYTES`, TLOAD/TSTORE), `exceptions.py` beyond
`WrongChainIdError`.

## 2. Affected surfaces in this repo

### 2.1 SpecRef (`EvmAsm/Stateless/SpecRef/`, phase 4)

| Change | Files |
|---|---|
| C1 schema id | `Ssz.lean:45-48` (`STATELESS_INPUT_SCHEMA_ID = 0x0001`) |
| C2 fork/blob-schedule | `Ssz.lean:110-124,166-172,339-384` (`sszBlobScheduleType`, `sszForkConfigType`, `protocolForkToSsz`, converters); `Types.lean` (`ProtocolFork`, `BlobSchedule`, `ForkConfig`, `SpecError.unknownProtocolFork`/`unsupportedForkConfig`); `Stateless.lean:120-137,182` (`_expected_amsterdam_blob_schedule`, `validate_chain_config`, `sanityForkConfig`) |
| C4 chain id | `Transactions.lean` (`recover_sender` signature, new `chain_id`), `Fork.lean` (`process_transaction`), error type |
| C5 intrinsic | `Transactions.lean` (`calculate_intrinsic_cost`, `validate_transaction`, `IntrinsicGasCost`) |
| C6 set_delegation | `Interpreter.lean:180-238` (`set_delegation`) |
| C7 prepare_dispatch | `Interpreter.lean` (new fn; `process_message_call` at 833-874; `prepare_message` port in `InstructionsEnv`/utils region) |
| C8 bookkeeping | `Vm.lean` (`Evm` state, `refill_frame_state_gas`, `credit_state_gas_refund`, `incorporate_child_*`), `Gas.lean` (`charge_state_gas`), `Interpreter.lean` (`MessageCallOutput:252-253`) |
| C9 block accounting | `Fork.lean:388-410` (refund block, `tx_state_gas`/`tx_regular_gas`) |
| C10 SSTORE | `InstructionsCore.lean` (sstore) |
| C11 create | `InstructionsCore.lean`/system instructions port (`generic_create`) |
| C12 builder addrs | `Fork.lean` (`BUILDER_DEPOSIT/EXIT_CONTRACT_ADDRESS`) |

Plus: ~30 Lean files cite `bd8c673`/`v0.5.0` in headers/docstrings —
refresh alongside the port (`check-spec-refs` re-anchors symbols
automatically; the version strings are prose).

### 2.2 Guest code (phase 5)

The guest is assembled from `BuildUnit`s
(`EvmAsm/Codegen/Programs/StatelessGuest.lean:59-98` `statelessGuestUnit`
concatenates `run_stateless_guest`, the epilogue, dispatcher core,
system-request derivation, and data sections; registry in
`Registry.lean`/`RegistryNames.lean`, layout in `GuestAddrs.lean`).

| Change | Guest surfaces |
|---|---|
| C1 schema id | `Codegen/Programs/StatelessGuestEpilogue.lean:828-874` (emitted check: bytes at INPUT+16/17 must be `00 01` → becomes `15 01`; earlier decode `:160-208`); `Stateless/SSZ/Decode/Program.lean:108-222` (`SCHEMA_ID_SIZE`, offsets); `Stateless/SpecRef/Guest.lean:30-35` |
| C2 ChainConfig layout | `Codegen/Programs/BlockVerdictChainConfig.lean:100-140` — emitted semantic check of `active_fork == Amsterdam` (hardcodes v0.5.0 StrEnum *index* 20) + activation + blob-schedule; the fork and blob-schedule fields are **deleted** in v0.6.0, so this check must be removed/reworked, not re-indexed. `Stateless/SSZ/Decode/ChainIdSAsm.lean:108-128` (`read_chain_id_verified`), `ActiveForkSAsm.lean` (fork reader — field gone), `Stateless/SSZ/Encode/Program.lean:9-36,150-216` (byte-map docs incl. blob_schedule) |
| C4 chain id | `Codegen/Programs/Tx.lean:642-651` + `TxValidateAgainstBlockSAsm.lean` (`tx_validate_against_block`, status 1 = chain-id mismatch) exists but is a **probe BuildUnit, apparently not wired** into the live verdict path (`Tx.lean:9-33`; `Stateless/Transaction/Validate.lean:37` TODO). v0.6.0 makes the check consensus-relevant (`WrongChainIdError`) → must be wired for real |
| C5 intrinsic | `Codegen/Programs/IntrinsicGas.lean:52,117-140` (calldata counts, EIP-7623 floor `tokens*FLOOR + GAS_TX_BASE` → anchor changes to `base_regular_gas`); `TxIntrinsicStateGas.lean:11-12,83-153` (`intrinsic_state_gas = (is_creation ? NEW_ACCOUNT : 0) + auth_count*AUTH_STATE_GAS_PER_AUTH` → both terms leave the intrinsic in v0.6.0); `InitCodeCostSAsm.lean:12-52` (unchanged math, new floor exclusion); auth capacity constant `TxIntrinsicStateGas.lean:50` |
| C6 set_delegation | `TxIntrinsicStateGas.lean:239-611` (`tx_eip7702_existing_authority_refund` — the entire refund model is deleted upstream, replaced by exact charges); `BlockVerdictMtxEoa.lean:50-153` (`eip7702_warm_recovered_authorities`); `BlockVerdictDispatchTx.lean:758-786` (auth staging + NEW_ACCOUNT refund) |
| C7 prepare_dispatch | `BlockVerdictDispatchTx.lean:277-326` (recipient code load + delegation follow — gains warm/cold charge + jumpdest recompute placement); `ChildFrameHandlerTails.lean:23-49,230` (same-block delegation resolve); no named `created_target_alive` — the top-frame value-transfer NEW_ACCOUNT is folded into dispatch state gas, so the *conditional* v0.6.0 form needs explicit treatment |
| C8 bookkeeping | `DispatcherExecStateGas.lean:11,69-99` (`tx_state_gas = intrinsic.state + state_gas_used − state_refund` → `state_refund` term dies); `DispatcherTxGasSettle.lean:4-45`; `DispatcherCaptureExecStateGasSAsm.lean`; `ChildFrameHandlerTails.lean` frame state-gas plumbing |
| C9 block accounting | `DispatcherTxGasSettle.lean` + `BlockVerdict*` gas fold (floor `max` placement moves here); EIP-7778/8037 check scripts cover it |
| C10 SSTORE | `Codegen/Programs/SstoreRegularGas.lean:4-77` (cold/warm charge order vs stipend sentry), `SstoreGasRefund.lean`, `Evm64/StorageGas.lean` |
| C11 create | `CreateFrameDescend.lean:12,82` (63/64 forward), `CreateDescend/CreateRuntime/BlockVerdictCreationStage/ChildFrameCreateTail`, `EL/Create*.lean` — child-CREATE NEW_ACCOUNT conditional charge/refill needs mapping onto the frame state-gas machinery |
| C12 builder addrs | **no guest-side occurrence** of either old builder address (`SystemCallStaging.lean:156-208` holds the EIP-7002/7251 predeploys only) — builder execution requests appear to flow through generic requests machinery or are not yet emitted; confirm in 5c whether any emitted data section carries them (likely SpecRef-only change) |
| C8 pubkeys (C3) | `BlockVerdictChainConfig.lean:11-73` (`public_keys_valid`, exact `count == tx_count`) + `VerifyPublicKeysSenders.lean:14-106` — semantics unchanged in v0.6.0; keep wired |

### 2.3 Harness / scripts (phases 2-3)

- `scripts/eest-fixture-tag.txt` → `tests-zkevm@v0.6.0`.
- 68 scripts default `TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.5.0}"` —
  mechanical sed, one commit.
- `scripts/eest-succ-allow.txt` (21 lines): entries are justified
  against `bd8c673`; must be re-triaged from scratch at v0.6.0 (goal:
  empty).
- `scripts/eest-stateless-to-input.py`, `eest-stateless-input-parity-check.sh`:
  schema-id and SSZ layout assumptions (C1/C2).
- `scripts/check-spec-refs` anchors: re-run at the new pin; fix DEAD
  SYMBOL hits (`set_delegation` signature moved, `BlobSchedule` /
  `UnsupportedForkConfigError` / `_protocol_fork_to_ssz` deleted,
  `prepare_dispatch`/`frame_state_gas_used`/`chain_id` new).

## 3. Phase plan and child beads

| Phase | Bead | Content | Depends on |
|---|---|---|---|
| 1 | `0w05f.1` | this doc + beads (this PR) | — |
| 2 | `0w05f.2` | submodule bump to `40f956fab` + spec-ref anchor fixes; `execution-spec-tests` submodule left as-is unless check breakage says otherwise | 1 |
| 3 | `0w05f.3` | fixture tag v0.6.0 everywhere; fetch + verify tarball parses; re-baseline conformance reports (expect mass FAIL until 4/5 land) | 2 |
| 4a | `0w05f.4` | SpecRef wire format: C1+C2 (+C3 note) — Ssz/Types/Stateless | 2 |
| 4b | `0w05f.5` | SpecRef tx layer: C4+C5 — Transactions/Fork/exceptions | 4a |
| 4c | `0w05f.6` | SpecRef VM gas plumbing: C6+C7+C8 — Vm/Gas/Interpreter | 4b |
| 4d | `0w05f.7` | SpecRef opcodes + block accounting + addresses: C9+C10+C11+C12; then full-suite succ gate to FAIL 0 | 4c |
| 5a | `0w05f.8` | guest input parsing: C1+C2 | 4a |
| 5b | `0w05f.9` | guest gas/tx/eoa/interpreter: C4-C11; byte-tie + ziskemu/EEST + Spike A/B parity | 4d, 5a |
| 5c | `0w05f.10` | guest builder addresses C12 + sweep of remaining constants | 5b |

Phases 4a-4d are separable PRs each based on the prior branch;
conformance (succ FAIL 0) is the exit gate of 4d, not of each step —
intermediate steps keep `lake build` + `check-spec-refs` +
`check-axioms` green but will show fixture divergence until the last
lands (fixtures are all-or-nothing on the wire format).

## 4. Risks / open questions

- **Floor-binding semantics (C9)** interact with EIP-7778
  block-gas accounting; our EIP-7778/8037 conformance checks
  (`codegen-eest-eip7778-block-gas-check.sh`, `eip8037-*`) will catch
  regressions but the SpecRef port must get the `max(...)` placement
  exactly right — it is the most likely succ-divergence source.
- **Warm-vs-cold delegation access (C7)** is a new gas path with no
  v0.5.0 analogue; needs a targeted fixture check.
- **`InitCodeTooLargeError` reorder (C5)** changes which exception
  fires first; SpecRef verdicts only care about valid/invalid block, so
  impact is likely nil — verify via succ gate.
- **Guest chain-id enforcement (C4)**: the emitted
  `tx_validate_against_block` exists only as a probe BuildUnit; v0.6.0
  turns the chain-id mismatch into an explicit consensus rejection
  (`WrongChainIdError`). If recorded public keys previously made
  mismatched-chain-id fixtures fail "by accident" (wrong recovered
  sender), the guest may already agree on verdicts — but the port must
  wire the explicit check to be faithful. Phase 5b item.
- **EIP-8282 builder requests (C12)**: no builder predeploy address
  occurs in guest Lean code. Determine in 5c whether builder execution
  requests are exercised by v0.6.0 zkevm fixtures at all; if they are
  and the guest lacks the routines, that is the bead's
  "new-EIP-requiring-substantial-guest-routines" STOP condition.
- **Guest parser rework (C1/C2)**: schema id is a 2-byte constant and
  the ChainConfig container shrinks; if the guest parser turns out to
  hardcode offsets across the whole `SszStatelessInput` fixed part,
  the rework could be wider than 5a assumes — assess right after 4a
  and STOP-and-report if it needs maintainer sequencing decisions
  (per the bead's escalation rule).
