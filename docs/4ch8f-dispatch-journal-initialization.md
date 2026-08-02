# Runtime-dispatch journal initialization contract

This is the proof-lane input for issue `#11152` and the predicate work that
follows the region-map audit. It records the logical initialization contract
of the scalar journals cleared by `runtime_dispatcher_callable_setup`.

The contract is intentionally expressed in logical cell and lifetime terms,
not absolute ELF addresses. Link-dependent addresses belong to the generated
image inventory; a predicate must quantify its `arena_base` and use the
structural overlay relation `arena_base + (d - 1) * 0x19000` for
`1 ≤ d ≤ 1024`. These scalar cells are standalone dispatcher state: they are
not members of the shared frame-memory pool or of the `baap_storage_values`
overlay.

## Contract vocabulary

For each named precondition below:

- a **cell** is one logical u64 state cell, independent of its link-dependent
  address;
- a **zero-assuming reader** is a routine that can read the cell before any
  producer in the current dispatcher invocation writes a nonzero value;
- the **initialization invariant** is `cell = 0` at dispatcher entry;
- the **lifetime** is one user or system dispatch, ending when its consumer
  finishes or the next dispatcher entry resets the cell.

The explicit zero stores are therefore load-bearing initialization, not a
leftover from the former append-log design. The twelve rows below are named
preconditions for the eventual separation-logic predicates: a caller opening
the dispatcher state must provide these cells at zero, or account for the
corresponding reset before opening a reader.

## Named zero preconditions

| ID | Cell | Zero-assuming reader | Initialization invariant and lifetime | What breaks if nonzero |
|---|---|---|---|---|
| DJ-01 | `evm_refund_acc` | `dispatcher_tx_gas_settle`; the call-frame snapshot/restore path also carries it | Zero before each dispatch; SSTORE may accumulate the current transaction's refund delta | A no-SSTORE or system call settles a stale refund from the preceding dispatch |
| DJ-02 | `evm_selfdestruct_seen_count` | `call_frame_descend` snapshot; SELFDESTRUCT seen-set scans and delegated-target checks | Zero before the dispatch; entries and child snapshots live only for that transaction/frame lifetime | A child inherits stale seen addresses, changing repeat-SELFDESTRUCT and beneficiary behavior |
| DJ-03 | `evm_selfdestruct_seen_overflow` | `call_frame_descend` snapshot and the SELFDESTRUCT seen-set scan | Zero before the dispatch; set only when the current seen-set capacity is exceeded | A prior overflow suppresses current seen-set recording and changes the reject/skip path |
| DJ-04 | `create_nonce_table_count` | `create_creator_nonce_use`, `create_creator_nonce_current`, `create_creator_nonce_seed_one`, and `create_creator_nonce_contains` | Zero before the dispatch; entries are the current transaction's creator-nonce overlay | A later transaction scans stale entries, returns a wrong nonce, or consumes stale table capacity |
| DJ-05 | `create_nonce_table_overflow` | The block-verdict fixed-arena overflow checks after transaction dispatch | Zero before the dispatch; only the current nonce overlay may raise it | A stale flag rejects a valid block, or masks whether the current dispatch overflowed |
| DJ-06 | `create_nonce_undo_count` | `create_creator_nonce_undo_to` and the call-frame snapshot path | Zero before the dispatch; undo entries are scoped to the current transaction/frame | Revert/restore replays stale undo entries into the current nonce table |
| DJ-07 | `account_state_pending_count` | `block_verdict_tx_state_gas_inline_prepare`, `account_state_find`, and call-frame snapshot/restore | Zero before the dispatch; pending account overlays accumulate only during this transaction | State-gas accounting and account lookup see stale pending rows from an earlier dispatch |
| DJ-08 | `account_state_created_count` | `account_state_created_contains` and the CREATE/account-state commit stage | Zero before the dispatch; the created set is the current transaction's EIP-6780 scope | A stale created-address membership changes CREATE collision or SELFDESTRUCT cleanup behavior |
| DJ-09 | `account_state_delete_count` | Delete promotion/creation-stage scans and call-frame snapshot/restore | Zero before the dispatch; deletion markers are current-transaction state | Stale deletion markers are promoted or restored into the current account-state view |
| DJ-10 | `account_state_overflow` | Block-verdict pre/deferred overflow checks | Zero before the dispatch; only the current account-state producers may set it | A stale overflow flag rejects the current block or changes the failure code |
| DJ-11 | `evm_log_data_used` | Log handlers read the cursor before appending metadata and payload bytes | Zero before the dispatch; the cursor advances only through this dispatch's logs | New log metadata/data starts at a stale offset and can overlap or misreport prior data |
| DJ-12 | `evm_log_data_overflow` | Log handlers read the overflow flag before the overflow store and later log checks | Zero before the dispatch; set only when this dispatch exceeds the data arena | A stale flag suppresses valid log payloads or routes a normal log through the overflow path |

These are cell-level obligations. They are not claims that the twelve cells
are physically contiguous, nor that their current addresses are stable across
images. The predicate work must separately carry each cell's width, reset
point, lifetime, and aliasing relation to the frame/pool views.

## Two retained cells not promoted to deletion

The fourteen-cell emitted setup also clears `evm_selfdestruct_staged` and
`cd_destroyed_empty_hits`. The measurement corpus observed no post-entry write
to the latter, and observed `evm_selfdestruct_staged` only on the
SELFDESTRUCT path where its non-wipe read follows that path's own `sd 1`.
Those are not deletion proofs: `SPIKE_WATCH` absence is evidence over a sample,
not an all-path or reject-side reachability proof. Both stores remain in the
emitted setup until a complete reader/lifetime proof exists.

The three `code_state_mtx_active`-gated code-effect cells and the
system-preserved destroyed-address pair are outside this twelve-row contract;
they have separate lifetime guards and must not be folded into this table.

## Evidence boundary and convergence

The measurement used the fresh `origin/main` image at commit `e9e7dd5fa` with
ELF SHA-256
`90bbdf185cd6405fa3453355f0f78cfc31d67f89b7bac944a8e64f05e51fc7038`.
The empty-requests fixture reached `stage_system_call` at emitted PC
`0x80063244`; `SPIKE_WATCH` reported `hits=0` for all fourteen cells on that
real system-call fixture. Targeted SELFDESTRUCT, CREATE, LOG, and multi-request
fixtures produced the expected writes for the corresponding producer cells.

The evidence is asymmetric: one zero-assuming reader is sufficient to retain a
store, while zero writes across a finite sample cannot prove that a cell has no
future writer. Accordingly, all fourteen stores remain. The execution-specs
system-call path has no equivalent whole-set scalar wipe: it uses fresh
per-call transaction/message objects and snapshots over one mutable state. The
guest's explicit cell reset is the implementation mechanism that supplies the
same scoping guarantee at this boundary.
