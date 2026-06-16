# Deposit Requests Hash Wiring Audit

This note records the current EIP-6110 deposit side of the EIP-7685
`requests_hash` path for `evm-asm-8uld3.2.3.3.3.1`. It is intentionally
behavior-neutral: the remaining implementation work is tracked by the child
beads below.

## Current Derived Path

`BlockVerdictReceiptsTail.lean` now has the tx-bearing derived-deposit check.
After receipt records and per-record log descriptors are materialized, the tail:

1. calls `materialize_log_records` over `bv_block_log_descs`,
   `bv_block_log_data`, and `bv_block_log_meta` into `c1_log_records`;
2. calls `parse_deposit_requests(c1_log_records, bv_block_log_count,
   c1_dbody, c1_dstatus)`;
3. stores the derived deposit byte length in `c1_dlen`;
4. combines `c1_dbody/c1_dlen` with derived withdrawal/consolidation bodies
   `dbsr_wbody/dbsr_wlen` and `dbsr_cbody/dbsr_clen`;
5. calls `requests_hash_verify` against `erh_requests_hash`, the header value
   computed earlier by the state-root prelude.

For this tail path, the guest no longer trusts the SSZ
`execution_requests.deposits` body. A tx-bearing block whose SSZ deposits body
matches the header but whose execution logs derive a different deposit body is
supposed to fail through `.Lbv_requests_hash_fail` after `requests_hash_verify`.

## Remaining Trust Boundaries

`BlockVerdictStateRoot.lean` still computes `erh_requests_hash` before entering
`block_verdict`. That prelude uses the SSZ `execution_requests` deposit body as
input while deriving only the withdrawal and consolidation bodies from system
calls. This is still necessary for paths that do not reach the receipt tail, but
it means the early value is a header commitment, not yet proof that deposits were
execution-derived.

The former `hv09f.1` no-tx SSZ-deposit length guard has been retired. For
`svf_tx_count == 0`, the prelude now assembles `requests_hash` with an empty
execution-derived deposit body before header comparison. A no-tx block with a
non-empty SSZ `execution_requests.deposits` body therefore rejects through the
general derived requests-hash/header mismatch path rather than through a
special-case deposit-length fail code.


## No-Runtime Classification

The only path that can use an empty derived deposit body without inspecting
receipt logs is the true no-transaction path:

- `svf_tx_count == 0`: no transaction can call the deposit contract, so the
  execution-derived deposit body is exactly empty. The prelude may assemble the
  requests hash with `c1_dbody` and `c1_dlen = 0`, then compare it against the
  header commitment. This is the scope of `evm-asm-8uld3.2.3.3.3.2.1`.

Tx-bearing paths need stricter handling because a syntactically unsupported or
non-runtime-dispatched transaction may still be capable, in the execution spec,
of emitting a deposit-contract log if it were executed. These paths must not be
silently converted to empty deposits merely because the guest did not
materialize runtime logs:

- `bvgr_arena_status != 0` or `bvgr_arena_runtime_count == 0` for a block with
  transactions: the guest lacks complete runtime receipt/log evidence, so deposit
  derivation is unsupported rather than empty.
- `bv_block_log_overflow != 0`: log capture exceeded the current arena; a
  deposit log might be among the uncaptured logs, so the path remains capacity
  debt.
- `bv_receipt_logs_status == 3`: block-log arena overflow propagated through
  `block_receipt_logs_materialize`; this is also capacity debt, not evidence of
  zero deposits.
- receipt/encoder/validator helper statuses that conservatively accept due to
  capacity (`bv_receipts_encoder_status` 3 or 5, or validator helper failure on a
  non-enforced shape) do not prove the deposit log set is empty.

For tx-bearing blocks, the precise path is the receipt tail: materialize all
block logs, parse deposits from those logs, and verify `requests_hash` with the
derived deposit body. If that path is not reached or is blocked by capacity, the
follow-up should preserve a precise unsupported/capacity status rather than
claiming empty deposits.

## Debug Fields For Follow-Up Evidence

The existing stateless debug output already exposes the request-body fields the
follow-up checks need:

- `request_dstatus` mirrors `c1_dstatus` from `parse_deposit_requests`;
- `request_dlen` mirrors `c1_dlen`, the derived deposit byte length;
- `request_dbody_cap` mirrors the deposit body arena capacity;
- `request_log_records_cap` mirrors the log-record staging capacity;
- `request_wlen` and `request_clen` mirror derived withdrawal/consolidation
  body lengths;
- `request_er_assembled_len` and `request_er_assembled_cap` cover the assembled
  SSZ `ExecutionRequests` section;
- `request_erh_status` mirrors `c1_erh_status` from `execution_requests_hash` or
  `requests_hash_verify`;
- `request_notx_deposit_len` is retained only as a retired/zero debug word for
  compatibility with the existing debug output layout.

## Follow-Up Beads

- `evm-asm-8uld3.2.3.3.3.2`: route remaining no-runtime paths through precise
  derived-deposit handling where sound; the no-tx `hv09f.1` special guard is
  retired.
- `evm-asm-8uld3.2.3.3.3.3`: add tx-bearing forged-deposit EEST/debug evidence
  for the receipt-tail derived path and a paired valid case.
