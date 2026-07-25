# Dispatcher unification design (lhkn7)

**Status:** design — approved direction, implementation pending (follows the
7r7w9 dead-code cleanup). **Load when:** working on `block_verdict` transaction
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
**Both structs share the identical simple_transfer layout** (offsets: +0 status,
+8 tx ptr, +16 tx len, +24 sender key, +40 gas_limit, +48 is_creation, +72
recipient[20], +96 value[32], +160 tx type, +176/+184 raw ptr/len). **This layout
identity is the concrete alias-stability fact** that lets the single-tx body be
folded into the loop with the index fixed at 0. Prove it before aliasing.

Hook-by-hook (from the current-main map):

| Hook | single site | MTx site | Reconciliation |
|---|---|---|---|
| Fee validity (`tx_effective_gas_pricing`) | `BVFunction:305-310` | `BVMtxRuntime:112-117` | same helper, dedupe to one call in the loop |
| **Nonce check** | `== pre` (`:704-708`) | `== pre + running_count` (`b1_sender_table_find`, `:131-151`) | **MTx form is general**; single is the degenerate count==0 case — adopt running-count |
| Upfront-balance lower bound | `:709-746` | `:163-196` | near-identical inline block, dedupe |
| **Pending credit publish** | per-tx pending flags (`:759-803`) | cumulative sender-balance table B2.2/B2.3 (`BVMtxTail:106-227`) | **MTx cumulative model is general**; adopt it, single reduces to one-row |
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
- committed-storage cross-tx snapshot `bv_mtx_committed_chunked_snapshot_upsert`
  (`:309-319`)

For a 1-tx block these are correct and currently absent on the single path — a
likely source of single-vs-multi storage/access FRs that unification fixes for
free.

**Single-tx-only capability the unified loop must PRESERVE:** creation dispatch
(`.Lbv_creation_dispatch`, `BlockVerdictFunction.lean:288`). MTx bails on creation
today; the unified loop must route creation like single-tx does, so
multi-tx-with-creation stops bailing.

## Target architecture

One `run_tx(i)` body, looped `for i in 0..bv_tx_count`, subsuming `.Lbv_singletx`
as the `i==0`/`count==1` case:

1. Build ctx via one context builder into a single ctx base (normalize the
   register: pick one of `t0`/`t2`, prove the offset layout, alias the single-tx
   body in with `i` fixed at 0 for the count==1 entry).
2. Run every per-tx hook in the general (MTx) form — running-count nonce,
   cumulative-balance credit, strided result store, single shared auth helper,
   always-run access-index/user-storage/committed-snapshot.
3. Three-way recipient routing (creation / contract / EOA) inside the loop —
   restoring creation support that MTx lacks.
4. Feed the one shared terminal (`.Lbv_after_tx_gas_precharge`) with count =
   `bv_tx_count` uniformly (count==1 is not special).

Pre-loop MTx setup that must be preserved or hoisted for all counts: base-fee
reversal `bv_mtx_base_fee_be` (`:92-96`), sorted sender index `bv_b1_sender_table`
(`:64-81`), committed cross-tx tables reset (`:83-84`).

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
- **FA=0 is inviolable** (doctrine §2 ship-gate). swept==shipped byte-cmp of
  `.text`/`.data`. check-axioms classical-3 (proofs of the retired path move to
  the provability track — replacing proven with unverified is allowed, doctrine
  §2; do not block on the proof).

## Risks / open items

- **`.Lbv_b2_entry` appears defined-but-unwired** (`BVMtxTail:106`, returns to
  `.Lbv_mtx_b2_return:231`) — the map found no active jump into it (only comments
  at `:101,123`). Investigate before unification: either a latent
  cumulative-sender-debit path that should be wired, or dead code to remove
  (coordinate with 7r7w9). Resolve which before adopting the B2 cumulative model
  as the general credit form.
- **Register normalization** (`t2` vs `t0`) — a clobber here is the classic
  register-clobber trap; prove the ctx base is stable across every per-tx `jal`.
- **Divergent-model reductions** must be verified, not assumed: confirm the
  running-count nonce reduces to `==pre` at count 0, the cumulative-balance
  credit reduces to the single pending-flag result for one tx, and the strided
  store reduces to the scalar store at stride-1. A false reduction is an FA risk.
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
