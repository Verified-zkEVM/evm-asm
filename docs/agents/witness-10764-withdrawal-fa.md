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
  (`fork.py:379`, the state-root comparison inside
  `execute_new_payload_request`: execution-derived post-state root vs
  header `state_root`).
- **Guest** (`stateless_guest` ELF, spike): **ACCEPTS** — output succ byte = 1.
- **Verdict probe** (`zisk_stateless_verdict_v2`, pristine): verdict = 1,
  bv_fail = 0, header_status = 0, state_status = 0.

Compared pair (BAI-2 postBalance for the withdrawal address):

- declared: 5,000,000,000 wei
- true:     15,000,000,000 wei (withdrawal of 10,000,000,000 wei credited)

Conclusion: on the MTx route the BAL-vs-effects comparators DO run
(MtxTail 286-289 aggregates the effect log, 291-295 compares the declared
BAL against that aggregate, 297-301 the reverse direction, gating
`.Lbv_bal_nonstorage_fail`) — but against an effect log containing no
withdrawal rows, because the only recorder of the withdrawal credit
(`block_verdict_withdrawal_nonstorage_effects`, which computes
amount × 1e9 + post and calls `record_nonstorage_effect`; the comparison
itself is `bal_all_accounts_nonstorage_consistent` / `_covers`) is reachable
solely from the dead legacy route (tx count 0). A live comparator reading
an incomplete input: the withdrawal credit is compared against nothing.

Mechanism: the guest's post-state root is BAL-fed, so with the mutated BAL
it derives a root that is wrong but self-consistent, then accepts it — while
the spec executes the block, computes the true root, and rejects on the
state-root comparison. The header's state-root oracle cannot catch any BAL
field here because the guest's output IS that oracle once re-pinned.

## Guest-derived root extraction

The pristine probe dies at `.Lbv_block_hash_mismatch` (bv_fail = 31) before
`block_state_root` runs, so `sv_recomputed` is unavailable on the mutated
blob. A diagnostic no-hash probe (emitted `verdict_probe.s` copied and
patched: `bv_block_hash_check_enabled` `.dword 1` -> `.dword 0`; tree
untouched) reaches `block_state_root` and reports the expected state-root
mismatch signature (verdict=0, bv_fail=1, statuses 0) with
`sv_recomputed` at OUTPUT+168. The pristine ELFs were used for every final
number above.

## Variant bai1: intermediate BAI row (tx credit)

Both variants come from one generator (`--variant bai2|bai1`), run against
the same fixture and the same pristine ELFs. After the refactor that
introduced `--variant`, the bai2 numbers above were re-verified identical
(`0xa73c76...`, `0xd8a995...`), so the shared script did not drift between
the two results.

Mutation: BAI-1 `postBalance` (the ordinary tx credit to the same address)
5,000,000,000 -> 25,210,765,039 wei (`0x5deadbeef`), an equal-length 5-byte
RLP string at blob offset 1043. The edit is anchored on row context because
the 5e9 RLP string also occurs at offset 636 inside the tx RLP (the transfer
value), which is left untouched.

Results:

- **execution-specs**: **REJECTS** — succ byte = 0; bare re-run raises
  `ethereum.exceptions.InvalidBlock` "Invalid block access list hash" at
  `fork.py:391` inside `execute_block` (computed BAL hash vs header
  `block_access_list_hash`). A different spec check than bai2's
  `fork.py:379` state-root comparison: the spec's BAL-vs-execution
  validation firing directly.
- **Guest**: **ACCEPTS** — succ byte = 1; pristine probe verdict = 1,
  bv_fail = 0, header_status = 0, state_status = 0.

Compared pair (BAI-1 postBalance): declared 25,210,765,039 vs true
5,000,000,000 wei.

The structural claim: **a final-balance row is constrained by both the state
root and the BAL hash; an intermediate row is constrained by the BAL hash
alone — therefore any check built only on the state root is blind to
intermediate rows.** The trie commits to the final balance, so a lie about
an intermediate BAI value is invisible to the state root by construction,
and the only spec mechanism that catches it is the BAL hash comparison —
which the guest does not yet perform.

The bai1 witness exhibits exactly this. The mutated row is the *intermediate*
BAI-1 value, and BAI-2 pins the account's final balance, so the guest's
BAL-fed state root is unchanged: the no-hash probe returned `sv_recomputed`
equal to the original declared state root
(`0x205facaa70b938f4c70e381b36d7e03c6fbd1216a867c69a84732c4226ee2255`) and the
state-root re-pin was a no-op. Only the `block_hash` re-pin is load-bearing
(new value `0xf7df9bad6c6a2433090d30983bfac647434492afc155cedd2cafe79df3583b38`).
Correspondingly the spec caught this variant not at the state-root comparison
but at the BAL hash comparison (`fork.py:391`).

It also shows the granular per-account/per-field comparators are insufficient
in principle, not merely incomplete: they never check ordering or BAI
indices. On the tx-credit side this matches the measured log: no
nonstorage-effect row for the recipient's 5e9 credit, and the recipient is
in `bv_mtx_skip_list` — unrecorded AND skipped.

The re-pin count forms a spectrum of *witness construction*, not of attacker
difficulty or severity. Re-pinning is a cost only because we mutate an
existing valid fixture and must keep its internal consistency; an attacker
constructs the block outright, so every header field (state root, block
hash, declared BAL) is theirs to choose from the start, subject only to
which checks the verifier performs. Re-pinning is therefore free to an
attacker, and the bai1 and bai2 lies are equally exploitable and equally
severe — the guest accepts an invalid block in both. The spectrum is how the
structural claim above was discovered; the claim is what it means.
