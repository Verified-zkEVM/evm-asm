# v0.6.0 guest semantics (phase 5b) — live-path map and port plan

Working notes for bead `evm-asm-0w05f.9` (GH #10207). The emitted
guest's LIVE verdict path is `statelessGuestUnit` →
`statelessGuestEpilogue` → `stateless_verdict_v2`
(`statelessVerdictV2GuestClosure`, `BlockVerdictV2.lean:217-528`) +
the runtime dispatcher; anything not in that closure is a probe.

Status after the second 5b commit (A/B full match 10/40, root/tail
40/40): items 1 DONE (both intrinsic sites + floor anchor + auth 7816),
5 partially DONE (exact-gas block floor; settle/receipt paths pending),
gate fixed (eip8037_tx_gas_gate intrinsic.state = 0). Layout regen DONE
(incl. offset-aware SAsm literal remap — the uniform-shift assumption
does not hold across data subsections). Remaining failures: bv_fail=53
(receipts root, 18/40) and bv_fail=41 (header gas_used over-claim,
12/40) — both the v0.5.0 auth/state-charge replay, items 2-4 below,
which must land as ONE unit. Fail-code legend: codes live in
BlockVerdictReceiptsTail.lean:132-215 (+ .Lbv_eip8037_gas_fail = a0+7,
so 10 = gate status 3); 53 = receipts-root mismatch; 41 = header
gas_used over-claim. Iterate with
`--backend spike --max-jobs 20 --jobs 20` (minutes, not tens of
minutes); final parity with ziskemu.

## Live sites and required v0.6.0 changes

1. **Intrinsic regular gas** — `intrinsic_gas_amsterdam_counts`
   (`IntrinsicGas.lean:312+`, prog-form, length pin, GuestImageEntries
   slot). DONE in this branch: recipient/value regular gas accumulates
   in x28 and feeds both the intrinsic (x31) and the floor (x30 anchor
   = TX_BASE + recipient), init-code gas excluded from the anchor;
   per-auth 15816 → 7816 (ACCOUNT_WRITE 8000 leaves the intrinsic).
   `intrinsic_gas_calldata_floor_eip7623` is NOT live (floor inline).

2. **Intrinsic state gas** — `tx_intrinsic_state_gas`
   (`TxIntrinsicStateGas.lean:82-138`): v0.5.0 charges
   `is_creation·NEW_ACCOUNT(183600) + auth_count·AUTH_STATE(218790)`.
   v0.6.0: BOTH terms leave the intrinsic. Must land TOGETHER with
   item 3 (else `eip8037_tx_state_gas` underflows on the refund
   subtraction). Live caller: `block_verdict_tx_state_gas_array`
   (`:707-815`, prog, jalOff relocs 812/813) → `bvgr_tx_state_gas[]`.

3. **EIP-7702 exact charges** — `tx_eip7702_existing_authority_refund`
   (`TxIntrinsicStateGas.lean:252-680`) computes v0.5.0 REFUNDS
   (worst-case minus actual); called from
   `block_verdict_tx_state_gas_array` and `BlockVerdictMtxEoa.lean:65`
   (`runtime_tx_auth_state_refund`/`_regular_refund`). v0.6.0 rework:
   flip to EXACT CHARGES —
   - state: NEW_ACCOUNT iff authority absent in pre-state/BAL;
     AUTH_BASE iff net-new delegation (not delegated pre-tx, none set
     earlier this tx, auth.address ≠ NULL);
   - regular: ACCOUNT_WRITE iff first tx write to authority
     (`written_accounts` seeded with origin + value-receiving
     recipient).
   Note the per-auth algebra `worst − v0.5.0-refund ≡ v0.6.0-charge`
   holds for NEW_ACCOUNT/exists and invalid-auth cases, so much of the
   walk survives; the deltas are the AUTH_BASE net-new rule, the
   ACCOUNT_WRITE first-write rule, and the OOG charge-point fixtures
   (`set_delegation_oog_*`).
   There is NO live set_delegation applier (BAL-replay: markers/nonces
   verified, not written).

4. **Top-frame dispatch charges** — `dispatch_tx_runtime_code`
   (`BlockVerdictDispatchTx.lean:261+`): delegation follow charges
   3000 ALWAYS (lines 302/327 via `runtime_tx_top_frame_regular_gas`);
   v0.6.0 charges WARM_ACCESS 100 when the delegate is already in the
   accessed set, else 3000. Create-tx NEW_ACCOUNT becomes conditional
   on pre-state EMPTY_ACCOUNT (moves out of item 2's intrinsic);
   value-to-dead-recipient NEW_ACCOUNT charge has NO live site — must
   be added (v0.5.0 also had it spec-side; check how v0.5.0 fixtures
   passed before assuming absent).

5. **Settlement** — `eip8037_tx_state_gas` (`IntrinsicGas.lean:594-612`):
   drop the creation-revert NEW_ACCOUNT refund branch (C9 deleted it);
   `tx_gas_result_increments` (`Account.lean:1130-1159`): v0.6.0
   block_inc = max(before_refund − max(0,tx_state_gas), floor) — the
   state subtraction moves BEFORE the floor max at block level;
   receipt_inc = max(after_refund, floor) unchanged.
   `eip8037_block_gas_used` (`IntrinsicGas.lean:839-877`) final
   max(block_regular, block_state) — re-derive against v0.6.0 fork.py
   before touching.
   FLAG (pre-existing): executed state_gas_used is not summed into
   block_state per DispatcherExecStateGas.lean:16-18.

6. **SSTORE** — live handler is `h_SSTORE` (`Storage.lean:255+`), NOT
   SstoreRegularGas.lean (probe). Current order: stipend check
   (gas_left < 2201, table already took 100) → cold/warm charge →
   BAL record. v0.6.0 wants check_gas(max(access_cost, stipend+1))
   before the BAL record — the guest's stipend-first + charge-before-
   record order may already be equivalent; verify against the
   eip2200/sstore fixtures before editing.

7. **CREATE** — `child_frame_create_tail` charges NEW_ACCOUNT
   pay-before-execute unconditionally; v0.6.0 charges iff target not
   alive, after the balance/nonce/depth early-out, before the 63/64
   split, refill-only-if-charged (collision/child-error), no
   target-alive success refund.

8. **Chain-id** — `tx_validate_against_block` NOT in the closure.
   v0.6.0 gate (reject block when tx chain-id ≠ block chain-id, before
   sender recovery) must be wired into `block_verdict` pre-checks
   (`BlockVerdictFunction.lean` ~282-330, before
   `verify_public_keys_match_senders`).

## Pins that break on edits
Prog-form: `intrinsicGasAmsterdamCounts_prog` (74, updated),
`eip8037BlockGasUsed_prog` (35), `txGasResultIncrements_prog` (26),
`blockVerdictTxStateGasArray_prog` (96, jalOff → items 2/3),
`blockVerdictEip8037TxStateGasNetArray_prog` (54),
`blockVerdictEip7702AuthNonstorageEffectsArray_prog` (66),
`dispatcher_tx_gas_settle` (AUIPC relocs). String-form targets have no
pins but moving their byte length shifts `GuestAddrs`.

## Regen flow (after any emitted-code change)
build guest ELF (eest harness or codegen-stateless-link-check.sh) →
`scripts/gen-symbol-addresses.py` → `python3
scripts/guest_image_coverage.py --emit-lean` → fix drift → `lake
build` → A/B smoke `scripts/codegen-eest-stateless-check.sh --limit 40`
(driver: the 33 succ-failing fixtures, mostly eip2780 calldata_floor +
eip7702 auth).


## RESOLVED: receipts-root mystery (was: dispatcher stale intrinsics)
The bv_fail=53 rejections were the callable dispatcher's OWN
per-authorization intrinsic still charging v0.5.0 constants
(Dispatch.lean ~2666: 15816 regular + 218790/auth state reserve) →
exactly-sized v0.6.0 fixtures OOG'd inside the runtime → receipt
status 0 with spec-exact cumulative. Fixed (7816, state reserve
deleted); single_authorization_charges 6/6 PASS, smoke 31/40
(was 10). Diagnosis pattern that worked: remap the verdict debug
probe's low OUTPUT slots to bv_receipts_validator_status +
brr_records fields (record status was the tell); spike_run has been
rebuilt with SPIKE_OUTPUT_LEN support so next time just set
SPIKE_OUTPUT_LEN=1024 and read the extended fields directly.

## REMAINING (9/40): the C8 set_delegation-OOG rollback family
test_set_delegation_oog_charge_point (3), _oog_rolls_back_first_auth
(4), recipient_charge_oog_rolls_back_delegations,
recipient_new_account_refilled_on_dispatch_halt — all diff at byte 32
(succ). Root cause: tx_eip7702_existing_authority_refund computes
charges from the FINAL BAL, which for an OOG-rolled-back tx shows NO
nonce advance (finals[40]=0) → per-auth contribution 0 → the guest
runtime never OOGs → guest says tx succeeded / wrong verdict. The
port needs the C8 semantics: detect that the auths were VALID against
pre-state but the BAL shows no application → the spec charged, OOG'd
at some charge point, and rolled back → expected outcome is a failed
tx consuming ALL gas (and, for charge_point variants, validating
WHICH charge triggers the OOG against tx.gas). Sketch: when a
validated auth has finals nonce-change = 0, compute the WOULD-BE
charge sequence against the tx gas budget (regular+state pools per
the spec order: per-auth NEW_ACCOUNT/ACCOUNT_WRITE/AUTH_BASE, then
prepare_dispatch recipient NEW_ACCOUNT) and require OOG; stage
all-gas-burned failed-tx settlement.

## Session status 2026-07-12 early AM: 39/40 smoke, 99/100 random
The C8 family is DONE except one fixture. Landed:
- would-be charges from pre-state validity (finals gate removed; path-A
  rollback detection via BAL-entry-without-nonce-advance; path-B
  header-state fallback for authorities absent from the BAL);
- applied/would-be split: a0/a1 = applied (zero on rollback, feeds
  block-state arrays); teer_wouldbe_state/_regular globals drive the
  runtime pools and the simple-transfer gas math;
- simple_transfer_intrinsic_gas folds the would-be charges into its
  outputs/cells (the v0.5.0 refund subtraction there was the last
  inverted consumer); direct + publish exhausted branches are C8
  failed-tx settlements (tgbpv_direct_oog → status 0, exec state 0).

LAST FIXTURE: recipient_new_account_refilled_on_dispatch_halt_with_
reservoir — the tx's own auth delegates the RECIPIENT, so the spec
dispatches the delegated code (which halts, burning the TX_MAX-capped
regular budget; header gas_used = 16777216) while the guest routes to
the simple-transfer shortcut (pre-state code empty) and never
dispatches. Fix: the EOA/simple-transfer routing must detect a
same-tx delegation on the recipient (authority == recipient with a
non-NULL set) and fall through to the runtime dispatch path (which
already does same-block delegation resolve).

## Wider validation (300 random, seed 23): 294/300
The 6 failures pinpoint the remaining work, matching map items:
1. recipient_new_account_refilled_on_dispatch_halt_with_reservoir (1x)
   — routing: same-tx delegated recipient must dispatch (above).
2. test_top_frame_charges_delegation_in_access_list (2x) — item 4's
   warm/cold delta: the delegate is pre-warmed by the tx access list,
   so prepare_dispatch charges WARM_ACCESS 100; DispatchTx stages a
   flat 3000 (BlockVerdictDispatchTx.lean:302/327). Implement the
   accessed-set membership check (tx access list ∪ warmed authorities)
   when staging runtime_tx_top_frame_regular_gas.
3. test_varying_calldata_costs RefundTypes.STORAGE_CLEAR (3x) — item
   5's settlement formulas: receipt = max(after_refund, floor) with a
   real refund_counter; check tx_gas_result_increments' block_inc
   (max(before_refund, floor) vs v0.6.0's max(before_refund −
   max(0,state), floor)) and the refund flow through
   dispatcher_tx_gas_settle on the SSTORE-clear path.

## Older diagnosis notes (superseded)

The refund→charge flip produces SPEC-EXACT receipt cumulatives on the
`single_authorization_charges` fixtures (22816/30816/66006/249606,
verified against `dump_receipts_for_fixture.py`), yet all 6 variants
reject with bv_fail=53 (receipts root) — including `invalid`, which
already failed PRE-flip. So a second, non-gas receipts discrepancy
exists (status byte or logs/bloom suspected; spec says n_logs=0,
error=False on these).

Next diagnostic step: the harness's dbg parser already understands
`bv_receipts_validator_status` (OUTPUT+424: 2=root mismatch, 4=bloom
mismatch) and friends, but the verdict-debug probe dump is only 256
bytes — either the probe's debug prologue variant stops early or
spike_run/ziskemu truncate the OUTPUT dump. Find where the dump length
is set (scripts/spike/spike_run capture; ziskemu -o extent) or extend
`ziskStatelessVerdictV2Prologue` (BlockVerdict.lean:85+, which in
source writes ≥360 bytes) and re-run
`codegen-eest-stateless-check.sh --filter single_authorization_charges
--backend spike --max-jobs 20 --jobs 20` (~1 min). validator_status 2
vs 4 splits root-vs-bloom immediately.

Pre-flip baseline on those 6: 1 PASS (creates_account) / 5 FAIL —
creates_account's pre-flip pass is arithmetically inconsistent with
the spec receipt (241606 vs 249606 by hand), suggesting compensating
errors pre-flip; do NOT treat it as a regression oracle.
