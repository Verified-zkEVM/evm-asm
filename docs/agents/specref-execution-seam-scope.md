# SpecRef execution seam: scope and decomposition

Scoping document for bead `evm-asm-s1d19` (P0): replace SpecRef's
placeholder `executeAlwaysOk` with a real `ExecutionSeam`, so that
`verify_stateless_new_payload`'s `successful_validation` verdict matches
execution-specs @ `bd8c673` (`tests-zkevm@v0.5.0`) on every fixture —
including the ~974 `succ=0` EEST fixtures where SpecRef currently
diverges (issue #10141).  Realizes obligations **#7** (MPT verification
of the pre-state witness) and **#8** (post-state root), both of which
sit behind the stubbed seam today.

Companion to the `evm-asm-n9rtz` v0.5.0 audit
(`docs/agents/specref-v050-audit.md`); the boundary with `n9rtz` is
recorded in §5.

## 1. The gap

`EvmAsm/Stateless/SpecRef/Stateless.lean` cuts the port of
`stateless.py::verify_stateless_new_payload` at the call to
`execute_new_payload_request` (`stateless.py:378` in the v0.4.0 line
numbering; the function is unchanged at `bd8c673`).  Everything above
the cut (chain-config validation, header-chain validation, witness DB
assembly, NPR root, SSZ shell) is a real port; the call itself is the
parameter `execute : ExecutionSeam`, defaulting to
`executeAlwaysOk := fun _ => .ok ()`.  Consequences:

- `successfulValidation` is always `true`, so SpecRef wrongly accepts
  every block whose real EVM execution fails.
- The pre-state witness is assembled (`build_node_db`, keccak-keyed)
  but never authenticated against `parent_header.stateRoot` — MPT
  witness verification (obligation #7) never happens.
- The post-state root is never recomputed or compared to
  `header.state_root` (obligation #8).
- `scripts/eest-specref-check.sh` can gate only the pre-execution
  regions (`root`, `tail`); the verdict byte (`succ`) is explicitly
  ungated.

## 2. What the seam must contain (execution-specs @ `bd8c673`)

The Python call graph below the cut, with sizes (lines at `bd8c673`,
`src/ethereum/forks/amsterdam/`):

| Layer | Source | Size | Content |
|---|---|---|---|
| Seam entry | `execution_engine/new_payload.py::execute_new_payload_request` | 169 | empty-tx check; block-hash check; versioned-hash check; payload→Block; `execute_block` |
| Payload→header/block | `execution_engine/validation_helpers.py` | 106 | `_payload_header` / `_payload_block` (needs unsecured trie roots over txs/withdrawals, `compute_requests_hash`, BAL keccak) |
| Block shell | `fork.py::execute_block` (+`validate_header`, `check_transaction`, receipts, system txs) | ~1,258 | RLP size cap, header validation, `apply_body`, eight post-execution root/gas/bloom checks incl. `state_root` |
| Witness reads | `witness_state.py` (`WitnessState` methods) | 307 | `get_account_optional` / `get_storage` / `get_code` / `account_has_storage` / `compute_state_root_and_trie_changes` |
| Witness trie | `incremental_mpt.py` | 1,040 | read side: `compact_to_nibbles`, `_decode_witness_node`, `_resolve_child_ref`, `decode_witness_to_mpt`; write side: `mpt_set`/`mpt_delete`/`mpt_root`, node encoding |
| State tracking | `state_tracker.py`, `block_access_lists.py` | 928 + 744 | `BlockState`/`TransactionState` journaling, BAL builder, EIP-8037 state-gas hooks |
| Transactions | `transactions.py` | 1,078 | envelope decoding, `recover_sender` (via supplied public keys), intrinsic costs, EIP-8037 `TX_MAX_GAS_LIMIT` |
| EVM | `vm/` (`interpreter.py`, `gas.py`, `instructions/*`, `eoa_delegation.py`, `memory.py`, `stack.py`, `runtime.py`, `exceptions.py`) | ~5,900 | the interpreter and all 149 opcodes, incl. CALL/CREATE family, EIP-7702 one-hop delegation, EIP-8037 two-dimensional gas |
| Precompiles | `vm/precompiled_contracts/` | ~2,300 | all 20: ecrecover, sha256, ripemd160, identity, modexp, bn128 (3), blake2f, KZG point-eval, bls12-381 (7+), p256verify |

Total: roughly **12k lines of Python**, dominated by the EVM +
precompiles.  The witness/trie layer (obligations #7 and #8) is a
self-contained ~1,350 lines.

## 3. Methodology decision: staged pure port (`elExecute`), witness layer first

The task admits two routes for the seam's content: a **pure port** into
SpecRef, or **instantiating the seam against the RV64 guest**.  The
project's own decision record already settles the architecture —
`docs/4ch8f-top-spec.md` §4 (bead `4ch8f.8`):

> the seam is closed *by definition on the spec side*, not by axiom and
> not by the guest. Bead `.10`'s interpreter strategy delivers a Lean
> functional model of `execute_new_payload_request` (the EL: blocks,
> txs, EVM) — call it `elExecute`.

Instantiating the seam with the RV64 guest is **circular** for the
purpose the seam exists for: `EntrySpec.lean::runStatelessGuestSound`
verifies the guest *against* `verify_stateless_new_payload execute`, so
the seam's content must be guest-independent.  It would also be
useless for the EEST conformance signal (the ziskemu harness already
runs the guest; SpecRef's value is being an in-process executable
reference).  And it is not even available: a survey of the non-SpecRef
`EvmAsm/Stateless/*` lane confirms `ExecutionEngine/NewPayload.lean`,
`VM/Interpreter.lean`, `Witness/MPT/*`, `State/StateRoot.lean` are
doc-only scaffolds — there is no callable Lean execution engine
anywhere in the repo today (the guest's 52 proven opcode handlers are
RISC-V `Program`s, not Lean functions).

**Decision: a pure, staged port.**  The witness-verification layer and
the state-transition shell are ported now (they are self-contained,
reasoning-heavy, and realize obligations #7/#8); the EVM core is a
separate epic-sized child with its own maintainer checkpoint (§6),
consistent with `4ch8f.10`'s `elExecute` plan and coordinated with the
`n9rtz.4`/`.5` v0.5.0 VM-slice work (§5).

Reusable existing assets for the later EVM stage:
`EvmAsm/Stateless/VM/Precompiles.lean` (pure Lean gas/output models
for 13 of the 20 precompiles), `EvmAsm/Stateless/SpecRef/Crypto.lean` +
`Secp256k1Recover.lean` (keccak, secp256k1 recovery for sender/
ecrecover), `SpecRef/Runtime.lean` (`get_valid_jump_destinations`).

### Wiring discipline: monotone, sound-for-accepts partial seams

Intermediate stages must not introduce **false rejects** (rejecting a
block the real spec accepts).  The safe rule: a partial seam may reject
only on a check that the real spec's *accepting path* unconditionally
performs.  If the real spec accepts a block, it necessarily ran the
full pipeline — all pre-checks passed, the state trie root decoded from
the witness, execution completed, and all eight post-root checks
matched.  So each of the following can be wired as soon as it is
ported, strictly shrinking the set of false *accepts* without ever
producing a false reject:

1. the `execute_new_payload_request` pre-checks (empty-tx, block-hash,
   versioned-hashes);
2. `execute_block`'s pre-execution frame (RLP size cap,
   `validate_header`, ommers-empty);
3. root-anchored witness authentication: `decode_witness_to_mpt` on
   `pre_state.stateRoot` must succeed (the accepting path always
   decodes the state trie for the post-root computation).

What can NOT be wired early: rejection on unresolved `HashedNode`s
merely being *present* in the witness (the real spec fails only if
execution actually touches one), and everything requiring the EVM
(execution failures, post-root mismatch).  The `succ` gate flip
(§6, `s1d19.6`) happens only when the seam is complete and the
divergence count on the full EEST run reaches zero.

## 4. Obligation #7: what "authentication" means here

`build_node_db` keys every witness preimage by its keccak-256 hash, so
a node fetched from the DB *by hash* is authenticated by construction
(fetched bytes hash to the requested key; keccak collision resistance
is the standing modeling assumption — we model the authenticated read,
we do not prove binding).  `decode_witness_to_mpt` therefore *is* the
authentication: it fetches the root by `node_db[pre_state.stateRoot]`
(missing → `KeyError` → reject) and resolves every ≥32-byte child
reference by hash lookup, decoding the reachable subtree; children not
in the DB become `HashedNode` placeholders, and `_trie_lookup` raises
(→ reject) if a read ever reaches one.  Genuine semantics, matching
`bd8c673`: an authenticated read returns the true value; a missing or
wrong-hash node yields a rejection, never a wrong value.

## 5. Boundary with `n9rtz` (SpecRef v0.5.0 audit)

`n9rtz` owns *v0.5.0-correctness of what SpecRef models*; `s1d19` owns
*making the seam real*.  Concretely:

- **`s1d19` children own**: the seam architecture and wiring
  discipline (§3), the witness/trie layer (`incremental_mpt.py`,
  `witness_state.py` — obligations #7/#8), the
  `execute_new_payload_request` + `execute_block` shell, and the
  `eest-specref-check` succ gate.
- **`n9rtz.4` (EIP-8037 gas model) and `n9rtz.5` (reachable VM/
  state-transition slice) own**: the v0.5.0 semantic content of the
  EVM interior — two-dimensional gas, instruction-level deltas,
  SELFDESTRUCT/copy-range/delegation behavior — under the
  vertical-slice discipline (every added function needs a recorded
  `run_stateless_guest` call-graph path).
- **Overlap point**: the EVM-core child (`s1d19.5`) is the *mass* of
  the interior; `n9rtz.4`/`.5` are the *v0.5.0 deltas* of the same
  surface.  Rule: `s1d19.5` work consumes and extends the modules
  `n9rtz.4`/`.5` introduce (gas model first), never forks them;
  `n9rtz.5`'s acceptance (call-graph-reachability recording) applies
  to everything `s1d19.5` adds.  One `WitnessState.lean` note:
  `n9rtz`'s audit lists `compute_state_root_and_trie_changes`
  `storage_clears` as "new-function-to-add" — that lands in `s1d19.4`
  (post-state root), not as a separate `n9rtz` port.
- Both beads edit `EvmAsm/Stateless/SpecRef/*`; coordinate stacked PRs
  with the `n9rtz` owner (Codex @ yoichi-bkp/evm-asm) to avoid
  conflicts, especially in `Stateless.lean` and any new `Vm*.lean`.

## 6. Decomposition: `s1d19.N` children

| Child | Deliverable | Sources @ `bd8c673` | Depends on |
|---|---|---|---|
| `.1` | `decode_witness_to_mpt` port + root authentication (obligation #7): `compact_to_nibbles`, `_resolve_child_ref`, `_decode_witness_node`, `decode_witness_to_mpt` over the existing `MutableNode`/`build_node_db`/`trieLookup` primitives | `incremental_mpt.py:859–1040` | — |
| `.2` | authenticated witness-backed reads: `get_account_optional`, `get_storage`, `get_code`, `account_has_storage` (+ decoded-root caching semantics) | `witness_state.py:131–223` | `.1` |
| `.3` | seam shell: `execute_new_payload_request` pre-checks (empty-tx, `is_valid_block_hash` via `_payload_header` incl. unsecured tx/withdrawal trie roots, `is_valid_versioned_hashes` incl. the tx-envelope decode subset) + `execute_block` pre-execution frame (`MAX_RLP_BLOCK_SIZE`, `validate_header`, ommers); wire as the first partial seam per §3 | `new_payload.py`, `validation_helpers.py`, `fork.py:287–360,457–514` | `.1` (wire with) |
| `.4` | post-state root (obligation #8): incremental-MPT write side (`mpt_set`, `mpt_delete`, node encoding, `mpt_root`) + `compute_state_root_and_trie_changes` with v0.5.0 `storage_clears` | `incremental_mpt.py:231–857`, `witness_state.py:225–307` | `.1`, `.2` |
| `.5` | EVM execution core (`elExecute` interior): `apply_body`, transaction processing, `state_tracker`/BAL, interpreter + instructions + precompiles, EIP-8037 gas — **epic-sized; maintainer checkpoint below** | `fork.py`, `transactions.py`, `state_tracker.py`, `block_access_lists.py`, `vm/**` | `.2`, `.3`, `.4`; coordinate `n9rtz.4`/`.5` |
| `.6` | flip `scripts/eest-specref-check.sh` to gate `succ` (add `--min-succ`/fold into fail); retire the `[root/----/tail]` divergence reporting as "expected" | `eest-specref-check.sh` | `.5` complete, divergences = 0 |

Status (2026-07-10): `.1` landed (`IncrementalMpt.lean`, PR #10166);
`.2` landed (`WitnessReads.lean` — `WitnessState` read methods,
cache-free over the `.1` decoder); `.4` landed
(`IncrementalMptWrite.lean` — the full `incremental_mpt.py` write side —
and `WitnessStateRoot.lean` — `compute_state_root_and_trie_changes`
with `storage_clears`, obligation #8; roots cross-checked against the
Python spec); `.3` landed (`Seam.lean`/`Transactions.lean`/`Gas.lean`/
`BlocksRlp.lean`/`SeamShell.lean` — the `execute_new_payload_request`
pre-checks + `execute_block` pre-execution frame + root-anchored
witness authentication, wired as the default partial seam
`executeSeamShell` per §3). The `.5` maintainer decision is
**resolved**: proceed with the full pure port (see the bead comment on
`s1d19.5`).

### Maintainer checkpoint (STOP-and-report, per the bead — since resolved)

Children `.1`–`.4` and `.6` are bounded and are committed work.  `.5`
is the whole EVM (~10k Python lines even after reuse): a faithful pure
port is the architecturally required end state (it is also `4ch8f.10`'s
`elExecute`, which the top-level theorem `.64` needs on the spec side),
but it is a **multi-PR epic, not one effort**, and its
prioritization/staffing (and its interleaving with the `n9rtz.4`/`.5`
delta work, which builds parts of the same interior) is a maintainer
call.  This document intentionally does not commit to a timeline for
`.5`; the request for a decision is filed on the bead.

## 7. Validation

EEST is *post-implementation* signal, not scoping input (today all
fixtures "pass" because the gate excludes `succ`).  Once stages wire
in: run `scripts/eest-specref-check.sh --all` and track the `succ`
divergence count (974 at the 2026-07-10 baseline run of 25,474
fixtures) monotonically down; any *new* pre-execution (`root`/`tail`)
failure or any fixture where SpecRef rejects but the fixture records
`succ=1` is a false-reject bug in the ported stage.  Gate flip (`.6`)
at zero divergences.
