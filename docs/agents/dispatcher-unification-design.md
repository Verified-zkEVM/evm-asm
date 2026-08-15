# Dispatcher unification design (lhkn7)

**Status:** phase-2 design drafted; implementation is held for maintainer
review. **Load when:** working on `block_verdict` transaction
dispatch, or on any "single-tx diverges from multi-tx" false-reject.

## Why

`block_verdict` runs transactions through **two disjoint code paths** that both
funnel into one shared terminal:

- **single-tx** (`.Lbv_singletx`, `BlockVerdictFunction.lean:278`) — taken when
  `bv_tx_count < 2`; three-way recipient routing (creation / contract / EOA).
- **multi-tx** (`.Lbv_mtx_loop`, `BlockVerdictMtxRuntime.lean:97`) — taken for
  `2..bvMtxActiveTxCap`; two-way routing (contract / EOA), **creation
  unsupported** (`.Lbv_mtx_creation_unsupported`).

The selector is a `bv_tx_count` test at the head of `blockVerdictMtxRuntimeLoop`
(`BlockVerdictMtxRuntime.lean:34-36`), inlined just before `.Lbv_singletx`
(`BlockVerdictFunction.lean:277`).

execution-specs has **one** loop — `for tx in transactions` in
`fork.py apply_body` — with no single-vs-many split. Our dual implementation is
the **common root of the single-lane whack-a-mole**: nonce-timing, count-clobber,
capture-timing, missing-caller, receipt-coupling bugs recur because a fix lands
in one path and the other drifts. Every "single-tx behaves differently from
multi-tx" FR is a symptom of this structural split. Unifying to one per-tx loop
is the biggest structural lever on the roadmap: it makes each per-tx behavior
have exactly one implementation, so a fix cannot land in only one lane.

This mirrors the spec-alignment doctrine (`docs/agents/spec-alignment-doctrine.md`
§1): mirror the spec's MODEL (one loop over transactions), not two
reconstructions that happen to agree on most blocks.

## What is already shared (keep as-is)

- **Prologue, before the tx split** — block hash (`BlockVerdictFunction.lean:68-76`),
  header/state-root comparison `block_state_root` + `.Lbv_cmp` (`:95-104`),
  witness/pre-state globals `sv_pre_rlp_*` / `bv_witness_state_*` / `bv_exec_p`
  (`:44-50`, `:110-111`), callee-saved conventions `s0=params`, `s3=SSZ_BASE`,
  `s1=header_status`, `s2=state_status` (`:37-40`, `:84`, `:96`).
- **Runtime dispatch** — `dispatch_tx_runtime_code` is a shared helper called
  from both paths (`BlockVerdictDispatchTx.lean:829`, `BlockVerdictMtxRuntime.lean:268`).
- **Terminal postlude** — both paths converge on `.Lbv_after_tx_gas_precharge`
  (`BlockVerdictGasGatePrelude.lean:15`, inlined at `BlockVerdictFunction.lean:1385`):
  arena prepare → EIP-8037 net + EIP-7778 block-gas gate over the per-tx
  state-gas **already accumulated inline per tx** (via
  `block_verdict_tx_state_gas_inline_prepare`/`inline_finalize` +
  `dispatcher_capture_exec_state_gas`, the post-#10513 mechanism — the old
  terminal `block_verdict_tx_state_gas_array` fill was dead after #10513 and is
  removed by 7r7w9/#10515) → `blockVerdictExactGasCheck` →
  `blockVerdictReceiptsTail` → epilogue `.Lbv_ret:`. This terminal is already
  single; unification does not touch it (beyond feeding it uniformly).

The shared prologue and terminal mean the unification is **bounded to the middle**
— replace the two per-tx regions with one loop that feeds the same terminal.

## The divergence surface (what unification must reconcile)

Per-tx context base differs only by register + struct pointer: single-tx keeps
the ctx ptr in `t2` at `bv_simple_transfer_tx` (`BlockVerdictFunction.lean:280`),
MTx in `t0` at `bv_mtx_ctx` indexed by `bv_mtx_i` (`BlockVerdictMtxRuntime.lean:99`).
**Both structs share the identical 192-byte simple_transfer layout** (offsets: +0
status, +8 tx ptr, +16 tx len, +24 sender key, +32 base-fee ptr, +40 gas_limit,
+48 is_creation, +56/+64 data ptr/len, +72 recipient[20], +96 value[32],
+128/+136/+144/+152 extractor statuses, +160 tx type, +168 inner-off, +176/+184
inner ptr/len; both builders zero 24 qwords then use the same tx extractors).
**This layout identity is the concrete alias-stability fact** that lets the
single-tx body be folded into the loop with the index fixed at 0.

**Phase-1 verified (2026-07-25, on 3dceb5ebf) — with two builder-stage caveats
the unification must handle:** `multi_tx_nth_context` deliberately leaves **+24
(sender pubkey)** and **+32 (BE base-fee ptr)** ZERO; MTxRuntime fills +24
separately at `BVMtxRuntime:202-206` before dispatch and uses a shared
`bv_mtx_base_fee_be` (writing +32 only in the creation lane, `:467`). So: **alias
the single-tx body into the loop only AFTER +24 is normalized, and keep base-fee
explicit — do NOT assume +32 is initialized by the MTx builder.** No offset
conflict exists in the intrinsic fields; the caveats are init-ordering, not layout.

Hook-by-hook (from the current-main map):

| Hook | single site | MTx site | Reconciliation |
|---|---|---|---|
| Fee validity (`tx_effective_gas_pricing`) | `BVFunction:305-310` | `BVMtxRuntime:112-117` | same helper, dedupe to one call in the loop |
| **Nonce check** | `== pre` (`:704-708`) | `== pre + running_count` (`b1_sender_table_find`, `:131-151`) | **MTx form is general**; single is the degenerate count==0 case — adopt running-count |
| Upfront-balance lower bound | `:709-746` | `:163-196` | near-identical inline block, dedupe |
| **Pending credit publish** | per-tx pending flags (`:759-803`) | B2.2/B2.3 cumulative-balance table (`BVMtxTail:106-227`), now reached after the gas-result gate (`BlockVerdictReceiptsTail:20-25`, restored by #10516) | B2 is live only as final sender validation. #10517 makes its value debit success-gated; it remains incomplete as a general credit model until it shares the self-transfer, recipient, and coinbase rules below. |
| **Result store** | scalars, index 0 (`:837-878`) | strided by `bv_mtx_i` (`:275-286`) | **strided form is general**; count==1 is stride-with-one-element |
| EIP-7702 auth-state setup | shared helper (contract) / re-inlined for EOA (`BVMtxEoa:52-60`) | same helper (contract) / MtxEoa mirror | one shared auth helper for BOTH contract and EOA — kill the MtxEoa duplicate |
| Effect-log snapshot + REVERT/OOG truncation | `.Lbv_tx0_effects_kept` (`:820-869`) | `.Lbv_mtx_effects_kept` (`:262-296`) | near-verbatim, dedupe |
| PRE-header gating (`dtrc_use_pre_header`) | `:666`/`:833` | `:231`/`:269` | dedupe |
| Inline state-gas capture (`dispatcher_capture_exec_state_gas`) | idx 0 (`:834-836`) | idx `bv_mtx_i` (`:271-274`) | the post-#10513 hook; strided form general |
| Receipt/cumulative-gas feed | count=1 publish (`:875-878`) | count=`bv_tx_count` publish (`.Lbv_mtx_publish:334-338`) | shared terminal helper, one publish site with count=`bv_tx_count` |

**MTx-only hooks the unified loop must ALWAYS run** (single-tx currently skips —
verify no regression when count==1):

- block-access-index stamp `current_block_access_index = i+1` (`BVMtxRuntime:227`)
- per-tx user-storage capture `capture_system_storage_exec_rows` (`:304-307`)
- canonical block `storage_writes` incorporation and preload
  (`write_sets_incorporate_tx` → `storage_writes_block_latest_value`)

For a 1-tx block these are correct and currently absent on the single path — a
likely source of single-vs-multi storage/access FRs that unification fixes for
free.

**Creation capability the unified loop must PRESERVE:** the live MTx creation
route (`.Lbv_mtx_creation_*`, `BlockVerdictMtxRuntime.lean`) is now the only
emitted creation dispatch.  The former `.Lbv_creation_dispatch` single-tx
definition was source-only dead and has been removed; any future unification
must preserve the MTx route rather than resurrecting that stale twin.

## Target architecture

One `run_tx(i)` body, looped `for i in 0..bv_tx_count`, subsuming `.Lbv_singletx`
as the `i==0`/`count==1` case:

1. Build ctx via one context builder into a single ctx base (normalize the
   register: pick one of `t0`/`t2`, prove the offset layout, alias the single-tx
   body in with `i` fixed at 0 for the count==1 entry).
2. Run every per-tx hook in the general (MTx) form — running-count nonce (reduces
   to `==pre` at count 0), strided result store (reduces to scalar at stride-1),
   single shared auth helper, always-run access-index/user-storage/committed-
   snapshot. **Balance/credit is the exception:** it must use the one model
   below rather than inheriting either existing lane verbatim.
3. Three-way recipient routing (creation / contract / EOA) inside the loop —
   restoring creation support that MTx lacks.
4. Feed the one shared terminal (`.Lbv_after_tx_gas_precharge`) with count =
   `bv_tx_count` uniformly (count==1 is not special).

Pre-loop MTx setup that must be preserved or hoisted for all counts: base-fee
reversal `bv_mtx_base_fee_be` (`:92-96`), sorted sender index `bv_b1_sender_table`
(`:64-81`), committed cross-tx tables reset (`:83-84`).

## Fresh-main hook inventory and boundaries

This map is from merged main `573a0e031` (the #10517 baseline).  It is the
implementation boundary for the future change, not permission to change the
emitted program yet.

- **Once per block:** `BlockVerdictFunction` establishes the witness/header
  globals and calls `blockVerdictMtxRuntimeLoop`; MTx setup initializes the
  sender table, the AccountState/CodeState mirrors, committed logs, and the
  explicit BE base-fee buffer before the loop.
- **Once per transaction:** the MTx loop clears the auth-phase scratch, calls
  `multi_tx_nth_context`, normalizes the omitted context `+24` sender key,
  applies fee/nonce/auth preparation, dispatches creation/contract/EOA, stores
  the indexed result/status, captures storage rows, then commits or rolls back
  effects according to that transaction's status.  The future unified loop
  must execute this full sequence even when `bv_tx_count == 1`.
- **Shared terminal only after all transactions:** both lanes feed
  `.Lbv_after_tx_gas_precharge`, then exact gas checking and
  `blockVerdictReceiptsTail`.  No per-tx balance calculation may reread the
  header balance at this terminal; it consumes the ordered per-tx records.

The two important per-tx boundaries are therefore (1) immediately after the
transaction's status is known, where its credit/debit record becomes final, and
(2) the ordered cross-tx commit, which is the only source for the next
transaction's as-of balance/existence.

## Phase-2 unified credit model (design only)

The unified loop must compute **one ordered credit/debit record per
transaction**, after the transaction status and its exact receipt gas are
available.  All consumers — AccountState, nonstorage effects, B2.3 final
comparison, and receipt/gas accounting — must consume that same record rather
than recomputing an adjacent variant.

For transaction `i`:

- `gasDebit(i)` is charged unconditionally from exact gas used and the existing
  exact fee calculation (including blob fee where applicable).  A reverting or
  OOG body still pays its consumed gas.
- `committedValue(i)` is `tx.value` only when the runtime status for `i` is
  successful; otherwise it is zero.  This is the #10517 rule expressed in the
  shared model, not a B2-only exception.
- The sender is debited by `gasDebit(i)`.  It is debited by
  `committedValue(i)` only when recipient and sender differ.  A self-transfer
  therefore pays gas but does not manufacture a transient value debit/credit
  pair; this preserves the EIP-7708 self-recipient rule.
- A distinct recipient receives `committedValue(i)` from the prior committed
  transaction state.  Failed/reverted bodies and self-transfers publish no
  recipient value credit.
- Coinbase receives the exact priority-fee component for `i`, accumulated on
  its already-committed live balance.  It must not be rebuilt from a
  header-pre-state balance for each transaction.

The record is appended/published in transaction order to the same committed
state used by subsequent transactions.  This makes a later transaction observe
only earlier committed credits, while the terminal B2.3 comparison observes the
whole block result.  The implementation must reuse the existing exact fee
calculator rather than duplicate fee arithmetic here.

## Eventual fixture and safety-control matrix

Any implementation of the design must run a full A/B, but these are mandatory
focused controls first:

- **B2.3 false-accept forges:** the tracked inputs in
  `fixtures/kat/mtx-sender-balance/` and
  `fixtures/kat/mtx-self-transfer-b2/` must reject (output success byte 32 is
  zero).  `scripts/make-mtx-sender-balance-forge.py` regenerates the original
  sender-under-debit case; `scripts/kat/make_mtx_self_transfer_b2_forgery_kat.py`
  materializes the self-transfer control as a packed ziskemu input.
- **Reverted/OOG value semantics:** #10517's nine controls remain accepted:
  deposits `23016/23018/23024/23057/23058`, withdrawals `23191/23193`, and
  consolidations `23345/23347`.
- **Multi-tx creation:** `11617/11618/11619`
  `dynamic_create2_selfdestruct_collision_multi_tx` must route through the
  unified creation path rather than the present MTx creation bailout.
- **Self transfer:** `00236` `transfer_to_self_no_log` and `00504`
  `bal_self_transfer` guard the no-value-net-debit rule; a multi-tx self-transfer
  fixture must be added or constructed before implementation because the
  current named controls are single-block variants.
- **Cross-tx sender/cumulative state:** `00624`
  `bal_7702_delegation_update` and a multi-tx same-sender block exercise the
  ordered sender/coinbase credit source.  The latter must be chosen from the
  manifest (or added) before the implementation gate.

## Migration strategy

- **Lift the MTx loop as the general form**, fold single-tx's creation-support
  and EOA path into it — do NOT try to generalize the single path outward. The
  MTx path already has the general (count-parameterized) shape; single-tx is the
  degenerate case. Per the doctrine (§3): the working logic is lifted, not
  discarded; only the redundant second structure is retired.
- **Prove ctx-offset stability first** (the layout-identity table) before
  aliasing single-tx-body into the loop.
- **A/B corpus-parity is the gate, not neutrality.** Unification is *intended* to
  change verdicts on the blocks where the two paths currently disagree — that is
  the point (fixing single-lane bugs once). So the gate is directional, not
  zero-delta:
  - On the **1-tx corpus**: no `OK→FR` regression vs the old single path (every
    case single-tx handled must survive), and ideally `FR→OK` on cases where
    single-tx was buggy relative to MTx.
  - On the **multi-tx corpus**: no `OK→FR` vs the old MTx path.
  - Net FR should **drop** (multi-tx-with-creation stops bailing;
    single-tx gains the always-run storage/access hooks).
- **Empirical iff is the ship-gate** (doctrine §2): `FA = 0` remains inviolable,
  and an in-envelope false reject is a defect (not tolerated churn).
  swept==shipped byte-cmp of `.text`/`.data`. check-axioms classical-3 (proofs
  of the retired path move to the provability track — replacing proven with
  unverified is allowed, doctrine §2; do not block on the proof).

## Risks / open items

- **FA-RISK — self-transfer balance exception:** the live B2.2/B2.3 sender
  table still needs an explicit recipient-equals-sender exception, while
  `tx_gas_bal_post_verify_runtime` already has it (`:214-229`).  Reusing B2
  without the unified record's self-transfer rule can create a false accept.
- **B2 is live but intentionally interim:** #10516 restored the receipts-tail
  predecessor to `.Lbv_b2_entry`; #10517 added the success gate for its value
  debit.  It remains sender-only and cannot be lifted wholesale: recipient and
  cumulative coinbase credits need the shared ordered model above.
- **Register normalization** (`t2` vs `t0`) — a clobber here is the classic
  register-clobber trap; prove the ctx base is stable across every per-tx `jal`.
- **Divergent-model reductions** (phase-1 status): running-count nonce **REDUCES**
  (tx0 count 0 ⇒ `==pre`, verified `BVMtxRuntime:212-229`); strided result store
  **REDUCES** (count=1 consumer reads index 0 = the sole scalar, `:374-381`); the
  cumulative-balance credit **does NOT universally reduce** (the self-transfer
  gap above) — the unified credit model is not an inheritance from either lane.
- **Creation inside the loop** is new for the multi-tx shape — the highest-value
  new capability and the least-tested; build the multi-tx-with-creation control
  fixtures first.

## References

- Doctrine: `docs/agents/spec-alignment-doctrine.md` (§1 model-mirroring, §3
  final-form-over-hybrid, §6 single-writer).
- Inline state-gas precedent: #10513 (inline EIP-7702 state-gas accounting) moved
  per-tx state-gas onto the inline `block_verdict_tx_state_gas_inline_prepare`/
  `inline_finalize` + `dispatcher_capture_exec_state_gas` hooks — the current
  per-tx state-gas mechanism the unified loop feeds. It left the old array
  Programs/proofs orphaned; the dead-code retirement of that closure is 7r7w9/
  #10515. The unified loop must run these inline hooks per iteration.
