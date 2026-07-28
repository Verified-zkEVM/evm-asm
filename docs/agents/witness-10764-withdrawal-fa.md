# Witness: GH #10764 withdrawal-credit false accept (fixture 00565)

Status: **FALSE ACCEPT CONFIRMED** (diagnostic only; no guest behavior change).

Generator: `scripts/witness-10764-withdrawal-fa.py` (construction documented in
its docstring). All final numbers below were produced by pristine ELFs emitted
from `main` @ cb5afc7f8 via `lake exe codegen --program <p> --halt linux93`,
run under `scripts/spike/spike_run`.

## Fixture

`gen-out/eest-fixtures/tests-zkevm@v0.6.2/fixtures/fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_eip4895/bal_withdrawal_and_value_transfer_same_address.json`

One block, one transaction, one withdrawal of 10 gwei
(10,000,000,000 wei) to `0xc0f6dc9e5836f54caadbf59cc69346c508e1992b`.
That address declares two BAL balance changes: BAI 1 -> 5,000,000,000 wei
(the tx value transfer) and BAI 2 -> 15,000,000,000 wei (after the
withdrawal credit).

## Mutation (minimal)

1. BAI-2 `postBalance` 15,000,000,000 -> 5,000,000,000 (one 5-byte RLP
   string replaced by an equal-length one at blob offset 1051; blob length
   unchanged). The declared BAL now credits the withdrawal address nothing
   for the withdrawal.
2. Re-pin `payload.state_root` (blob offset 114) to the guest-derived
   post-state root `0xa73c763559709d17bd19c12fb20ee647e378f4ee1232f8bb307bb2a8bb83b726`.
3. Re-pin `payload.block_hash` (blob offset 534) to the recomputed header
   hash `0xd8a995521d4c46beba61bfca53fa815edbb98a1b83f6ed60e8531020c6ea3bf3`
   (keccak of the header RLP with the mutated BAL hash and re-pinned state
   root).

Re-pinning to guest-derived values is mandatory: it makes the block
self-consistent with the guest's own model by construction, which is exactly
what a false accept means here. The guest's post-state root is BAL-fed, so
pinning makes the guest's output echo the header's oracle (the circularity
this FA exploits). The diff is one declared value plus two forced re-pins.

## Results

- **execution-specs** (`run_stateless_guest`, submodule e5a8caf1b =
  tests-zkevm@v0.6.2): **REJECTS** — output succ byte = 0. Re-running the
  `verify_stateless_new_payload` body without its blanket `except` raises
  `ethereum.exceptions.InvalidBlock` from `execute_block`
  (`fork.py:379`, the block-diff / BAL-vs-state check inside
  `execute_new_payload_request`).
- **Guest** (`stateless_guest` ELF, spike): **ACCEPTS** — output succ byte = 1.
- **Verdict probe** (`zisk_stateless_verdict_v2`, pristine): verdict = 1,
  bv_fail = 0, header_status = 0, state_status = 0.

Compared pair (BAI-2 postBalance for the withdrawal address):

- declared: 5,000,000,000 wei
- true:     15,000,000,000 wei (withdrawal of 10,000,000,000 wei credited)

Conclusion: on the MTx route nothing validates withdrawal credits against
execution; the only reconciler (`block_verdict_withdrawal_nonstorage_effects`)
is reachable solely from the dead legacy route (tx count 0).

## Guest-derived root extraction

The pristine probe dies at `.Lbv_block_hash_mismatch` (bv_fail = 31) before
`block_state_root` runs, so `sv_recomputed` is unavailable on the mutated
blob. A diagnostic no-hash probe (emitted `verdict_probe.s` copied and
patched: `bv_block_hash_check_enabled` `.dword 1` -> `.dword 0`; tree
untouched) reaches `block_state_root` and reports the expected state-root
mismatch signature (verdict=0, bv_fail=1, statuses 0) with
`sv_recomputed` at OUTPUT+168. The pristine ELFs were used for every final
number above.
