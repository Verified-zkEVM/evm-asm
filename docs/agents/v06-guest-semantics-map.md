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
