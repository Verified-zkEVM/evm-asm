# EEST Stateless Guest Testing

This runbook covers the fixture-driven stateless guest harness:

```bash
scripts/codegen-eest-stateless-check.sh [options]
```

The harness builds `stateless_guest`, converts EEST `zkevm` fixture blocks
into `ziskemu -i` inputs, runs each selected input, and compares the 105-byte
guest output with the fixture's `statelessOutputBytes`.

For missing-feature scheduling, see
[`docs/eest-feature-surfaces.md`](eest-feature-surfaces.md). It maps EEST
fixture classes to the active transaction, gas, state, opcode, call/create,
precompile, and receipt/log feature beads.

For the byte-level input contract shared with execution-specs
`run_stateless_guest`, see
[`docs/agents/stateless-input-contract.md`](agents/stateless-input-contract.md).
The main harness verifies by default that each generated `ziskemu -i` file
unpacks to the fixture `statelessInputBytes`; pass
`--verify-execution-spec-input` when you also want the selected bytes decoded
through the local `execution-specs` submodule stateless input path.

## Prerequisites

Install the normal codegen requirements from the README: Lean/Lake,
`riscv64-elf-binutils`, and `ziskemu`.

Fetch the EEST fixture tarball once:

```bash
scripts/eest-fetch-fixtures.sh zkevm@v0.4.0
```

By default the harness reads:

```text
gen-out/eest-fixtures/zkevm@v0.4.0/fixtures/fixtures
```

Override that with `EEST_FIXTURES_DIR=/path/to/fixtures` when needed. Use
`EEST_FIXTURE_TAG=...` or `--tag ...` to select a different cached release.

## Common Commands

Run the default smoke subset:

```bash
scripts/codegen-eest-stateless-check.sh
```

Run a focused fixture subset:

```bash
scripts/codegen-eest-stateless-check.sh \
  --filter bal_7002_partial_sweep \
  --limit 2 \
  --jobs 32 \
  --steps 1000000000
```

Run a focused gas-parity comparison against the local Python execution-specs:

```bash
scripts/codegen-eest-gas-parity-report.sh \
  --filter eip7778_block_gas_accounting_without_refunds/gas_accounting/multi_transaction_gas_accounting.json \
  --limit 1 \
  --jobs 1 \
  --max-failures 1
```

This wrapper runs the selected inputs through the normal ziskemu stateless
harness, decodes the exact same guest-visible bytes through
`execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py`, and prints
fixture/Python/guest success bits plus payload `gas_used`, `gas_limit`,
remaining block gas, transaction count, and verdict-debug fields when the
guest emitted them. Add `--tsv` for machine-readable triage output.

Run the complete `random_statetest` regression class for `zkevm@v0.4.0`:

```bash
scripts/codegen-eest-random-statetest-check.sh --jobs 8
```

This wrapper first counts the selected `random_statetest` blocks for the active
fixture tag, then loops over every block in fixed-size windows with
`--min-full` set to the actual chunk size and `--max-failures 1`. Set
`EEST_RANDOM_WINDOW=N` to change the default 200-case window size.

Run a focused simple value-transfer transaction frontier:

```bash
scripts/codegen-eest-simple-value-transfer-frontier-check.sh --jobs 1
```

This wrapper loops over the simple transaction/value-transfer fixture filters
from the feature-surface report and forwards `--skip`, `--limit`, `--jobs`, and
`--max-failures` to the stateless harness. It is a baseline probe today: it does
not claim the selected fixtures pass until the value-transfer validation,
state-effect, gas-settlement, and post-state integration children under bead
`evm-asm-fhsxz.2.4.2.56` land.

Run the literal EXTCODEHASH missing-code regression filters:

```bash
scripts/codegen-eest-literal-extcodehash-check.sh --jobs 4
```

This wrapper counts and runs the `witness_codes_extcodehash_only` and
`witness_codes_extcode_delegated_eoa` filters with `--min-full` set to each
filter's current selected count, so future cases added to those filters are
covered automatically.

Run the 1,000-block windows immediately after `random_statetest`:

```bash
scripts/codegen-eest-post-random-window-check.sh --jobs 8
scripts/codegen-eest-post-random-window-2-check.sh --jobs 8
scripts/codegen-eest-post-random-window-3-check.sh --jobs 8
scripts/codegen-eest-post-random-window-4-check.sh --jobs 8
```

The first starts at `--skip 17085` (`16582 + 503`), the second starts at
`--skip 18085`, the third starts at `--skip 19085`, and the fourth starts at
`--skip 20085`. Each checks `--limit 1000` with a `--min-full 1000`
regression threshold.

Run the focused EXP opcode regression:

```bash
scripts/codegen-eest-exp-power256-check.sh
```

This checks the Amsterdam `exp_power256` state-test fixture and requires a full
105-byte stateless output match. Treat it as a focused EXP smoke regression, not
as a claim that the whole EXP frontier is complete: dynamic-gas coverage,
large-exponent edge coverage, and the remaining software/proof work are tracked
separately under bead `evm-asm-fhsxz.2.4.2.60.2.6`. Override
`EEST_EXP_POWER256_JOBS` or `EEST_EXP_POWER256_STEPS` for this wrapper without
changing the broader harness defaults.

Run the full EXP fixture frontier:

```bash
scripts/codegen-eest-exp-frontier-check.sh
```

This discovers every stateless block selected by the current `opcodes/exp/` filter and
requires all selected opcode EXP blocks to full-match. It is the EEST-facing completion
gate for the promoted EXP runtime frontier; proof work remains tracked
separately from this runtime/fixture coverage.

Run the EIP-8037 state-dominated block-gas accounting frontier:

```bash
scripts/codegen-eest-eip8037-state-dominates-check.sh
```

This filter-driven wrapper discovers all `block_gas_used_state_dominates` cases
for the active fixture tag and requires all selected cases to full-match. It
keeps the conservative transaction inclusion gate from rejecting valid
multi-transaction blocks before exact execution gas accounting is available.

Run the EIP-8037 nested-reservoir reset frontier:

```bash
scripts/codegen-eest-eip8037-nested-reservoir-check.sh
```

This filter-driven wrapper discovers all
`nested_failure_resets_to_tx_reservoir` rows for the active fixture tag and
requires the selected rows to full-match. Use
`EEST_EIP8037_NESTED_RESERVOIR_SKIP`, `LIMIT`, and `MIN_FULL` to target a
specific row group while keeping the default script complete for future fixture
additions.

Run the EIP-7939 CLZ/JUMP frontier:

```bash
scripts/codegen-eest-eip7939-clz-jump-check.sh
```

This filter-driven wrapper discovers all `clz_jump_operation` rows for the
active fixture tag and requires the selected rows to full-match. It defaults to
one `ziskemu` worker because these rows can be memory-heavy on this host; set
`EEST_EIP7939_CLZ_JUMP_LIMIT` and `EEST_EIP7939_CLZ_JUMP_MIN_FULL` for a quick
prefix check.

Run the EIP-8037 high-block-gas layout launch regression:

```bash
scripts/codegen-eest-eip8037-layout-check.sh
```

This selects `pricing_at_various_gas_limits`, requires the 200M, 300M, 500M,
and 1G block-gas rows to be present, and fails unless each required high-gas row
launches and full-matches the expected 105-byte stateless verdict. This keeps
the 1G layout work aimed at semantic EEST success, not merely avoiding
`ERROR(layout)`.

Run the broader EIP-8037 high-block-gas state-pricing frontier:

```bash
scripts/codegen-eest-eip8037-state-pricing-high-gas-check.sh
```

This selects the full `eip8037_state_creation_gas_cost_increase/state_gas_pricing`
surface and requires the observed 200M, 300M, 500M, and 1G rows for the six
high-gas pricing fixture files to be present and to full-match. Use this when
checking that the largest EEST gas-limit cases are succeeding semantically, not
only fitting in the static layout.

Run a fast EIP-2929 precompile-warming frontier:

```bash
scripts/codegen-eest-precompile-warming-frontier-check.sh
```

This selects the first `precompile_warming` fixture. The executable-spec source
is `execution-specs/tests/berlin/eip2929_gas_cost_increases/test_precompile_warming.py`:
it runs a transaction whose contract measures `BALANCE` gas for precompile
addresses across a fork transition, then checks the resulting storage. The
current guest gets the stateless root and tail correct for this case, but the
success bit is still `0` instead of the expected `1`, making it a quick
transaction/opcode frontier distinct from the BAL large-witness non-completion.
Override `EEST_PRECOMPILE_WARMING_JOBS` or `EEST_PRECOMPILE_WARMING_STEPS`
for this wrapper without changing the broader harness defaults.

Run the focused warm/cold BAL visibility frontier:

```bash
scripts/codegen-eest-warm-cold-bal-visibility-check.sh
```

This runs small `precompile_warming` and `stEIP150singleCodeGasPrices/eip2929`
selections through the stateless guest and fails on harness ERROR/BUDGET rows.
Use `EEST_WARM_COLD_BAL_MIN_FULL` or `--min-full` to turn the same frontier
into a hard full-match gate once the remaining EIP-2929 gas semantics are ready.

To see the broader precompile fixture frontier, including families not selected
by the narrow warming probe, run:

```bash
scripts/eest-precompile-frontier-report.py --markdown
```

After any `scripts/codegen-eest-stateless-check.sh` run, the same command also
reads the latest `manifest.tsv` and `*.result.tsv` files under `gen-out/eest-run`
(including the harness's `run-*` subdirectories) and groups completed
full/root/success/tail outcomes by precompile family. The report is a coverage
matrix, not a success claim: today
`EvmAsm/Stateless/VM/Precompiles.lean` still routes precompile dispatch to the
unimplemented frontier, while the reusable accelerator payload/ECALL bridges
are tracked from [`docs/zkvm-accelerators-interface.md`](zkvm-accelerators-interface.md).

Run the focused BLS12 G1 ADD/MSM frontier:

```bash
scripts/codegen-eest-bls12-g1-frontier-check.sh --jobs 4
```

This wrapper selects EIP-2537 G1 ADD and G1 MSM fixture families by filter and
derives each per-filter run limit from the generated manifest, so new rows are
covered without editing the script. It supports `--skip`, `--limit`, and
`--max-failures` for fast local bisection; add `--require-full` once the
selected rows are expected to full-match. Some fixture tags, including older
Amsterdam-only cached tags, may not contain Prague BLS12 fixtures; use
`--allow-empty` only when checking wrapper plumbing rather than coverage. Set
`EEST_BLS12_G1_FILTERS` or pass repeated `--filter` options when a fixture tag
uses different generated path names.

Run the focused BLS12 G2 ADD/MSM frontier:

```bash
scripts/codegen-eest-bls12-g2-frontier-check.sh --jobs 4
```

This wrapper selects EIP-2537 G2 ADD and G2 MSM fixture families by filter and
derives each per-filter run limit from the generated manifest, so new rows are
covered without editing the script. It supports `--skip`, `--limit`, and
`--max-failures` for fast local bisection; add `--require-full` once the
selected rows are expected to full-match. Some fixture tags, including older
Amsterdam-only cached tags, may not contain Prague BLS12 fixtures; use
`--allow-empty` only when checking wrapper plumbing rather than coverage. Set
`EEST_BLS12_G2_FILTERS` or pass repeated `--filter` options when a fixture tag
uses different generated path names.

Run the focused BLS12 pairing/map frontier:

```bash
scripts/codegen-eest-bls12-pairing-map-frontier-check.sh --jobs 4
```

This wrapper selects EIP-2537 pairing, map-Fp-to-G1, and map-Fp2-to-G2
fixture families by filter and derives each per-filter run limit from the
generated manifest, so new rows are covered without editing the script. It
supports `--skip`, `--limit`, and `--max-failures` for fast local bisection;
add `--require-full` once the selected rows are expected to full-match. Some
fixture tags, including older Amsterdam-only cached tags, may not contain
Prague BLS12 fixtures; use `--allow-empty` only when checking wrapper plumbing
rather than coverage. Set `EEST_BLS12_PAIRING_MAP_FILTERS` or pass repeated
`--filter` options when a fixture tag uses different generated path names.

Run the focused EIP-7708 simple ETH transfer-log regression:

```bash
scripts/codegen-eest-eip7708-simple-transfer-check.sh
```

By default this converts and runs every stateless row selected by the
`simple_transfer_emits_log` fixture filter, so future parameter rows for that
fixture are picked up without editing the script. It is a first EIP-7708
transfer-log gate, not the full CALL/CREATE/SELFDESTRUCT/finalization burn
frontier.

Run the current BAL replay frontier around the EIP-7002 withdrawal-request
cluster:

```bash
scripts/codegen-eest-bal-replay-frontier-check.sh --jobs 4
```

This filters to `withdrawal_requests`, starts at local `--skip 83`, checks
`--limit 20`, and stops after the two known conservative misses. With parallel
jobs, the number of completed passes before the stop point depends on
scheduling. Use `scripts/eest-bal-replay-report.py --details` after a run to
inspect the BAL row shape for the selected inputs.

Run the focused EIP-7928/EIP-2935 BAL regression:

```bash
scripts/codegen-eest-eip2935-bal-check.sh
```

By default this converts and runs every stateless row selected by the
`block_access_lists_eip2935` fixture-directory filter, so future fixture
additions under that directory are picked up without editing the script. For a
short local smoke, set `EEST_EIP2935_BAL_LIMIT=N`; the default gate should keep
the full auto-counted selection.

Run the focused EIP-7928/EIP-4788 BAL regression:

```bash
scripts/codegen-eest-eip4788-bal-check.sh
```

This has the same future-proof auto-count shape, but selects the
`block_access_lists_eip4788` fixture directory. For a short local smoke, set
`EEST_EIP4788_BAL_LIMIT=N`; the default gate should keep the full auto-counted
selection.

To inspect only the completed frontier misses from the latest run:

```bash
uv run --directory execution-specs --quiet python3 \
  ../scripts/eest-bal-replay-report.py --failures-only --details
```

The report includes `state_witness_bytes`, `over_bsr_cap`, `bal_rows`, and
`over_bsr_bal_cap`; the cap columns mark inputs whose state witness or BAL row
count exceeds the current `block_state_root` caps. Pass `--bsr-cap N` and
`--bsr-bal-cap N` to model different proposed arena caps in those columns. The
guest default is a 64 KiB state-witness cap. That is an implementation cap for
the current EEST harness, not a protocol maximum.

The BSR scratch layout was reviewed against the local `execution-specs`
checkout. The hard protocol/test limits that matter for the current layout are:
Prague/Amsterdam withdrawal requests cap at 16 per payload
(`execution-specs/src/ethereum/forks/amsterdam/stateless_ssz.py`), Osaka block
RLP size caps at 8,388,608 bytes
(`execution-specs/src/ethereum/forks/osaka/fork.py`), Osaka transaction gas
caps at 16,777,216 (`execution-specs/src/ethereum/forks/osaka/transactions.py`),
and EVM code/initcode caps are 24 KiB / 48 KiB
(`execution-specs/src/ethereum/forks/osaka/vm/interpreter.py`). Amsterdam BAL
validation is gas-derived rather than a fixed row count: the accepted item count
is at most `block_gas_limit / 2000`, where items are account addresses plus
unique storage keys
(`execution-specs/src/ethereum/forks/amsterdam/block_access_lists.py` and
`execution-specs/src/ethereum/forks/amsterdam/vm/gas.py`).

The guest uses bounded arenas rather than dynamic host memory. `block_state_root`
first applies the Amsterdam gas-derived BAL budget, then checks actual decoded
BAL/state/storage counts against its static replay arenas. Those arenas are
sized for 500,000 BAL items, the worst-case BAL budget implied by a
1,000,000,000 gas block, but the harness no longer rejects a fixture solely
because the declared gas limit is larger. Very high gas-limit fixtures still
launch when their actual resource consumption fits; actual overflows or arena
exhaustion must be detected at runtime by the guest. Larger gas-valid BALs need
a streaming/chunked replay path or a separately built larger static layout. The
1G block-gas sizing plan is
[`docs/eest-1g-block-gas-layout-plan.md`](eest-1g-block-gas-layout-plan.md);
that plan explains the current arena capacity and supersedes tests that expect
observed high-gas EIP-8037 fixtures to stop at `ERROR(layout)`.

To run a focused harness experiment with different guest-side replay caps, pass
`--bsr-witness-cap N` for the block-state-root witness-byte cap or
`--bsr-bal-cap N` to add a lower BAL-row cap after the Amsterdam gas-derived
budget. The harness patches the emitted assembly and relinks only for that run:

```bash
scripts/codegen-eest-bal-replay-frontier-check.sh \
  --steps 400000000
```

The checked version of that experiment is:

```bash
scripts/codegen-eest-bal-replay-frontier-64k-check.sh
```

It requires the current `19/20` full-match frontier and leaves the large
170 KiB witness case as the remaining conservative miss.

For the current post-state-root implementation surface, execution-specs parity
references, focused probes, and known gaps, see
[`post-state-root-parity.md`](post-state-root-parity.md).

To expose the next blocker behind that conservative miss, run:

```bash
scripts/codegen-eest-bal-large-witness-frontier-check.sh
```

This selects the single large-witness withdrawal-request case, raises the
experimental block-state-root witness cap to 256 KiB, and stops after the first
reported failure or error. The current blocker is an emulator non-completion
before the guest writes stateless output, even with a 2B-step cap.

To probe the large remaining case past both known caps:

```bash
scripts/codegen-eest-stateless-check.sh \
  --filter withdrawal_requests \
  --skip 83 \
  --limit 20 \
  --jobs 4 \
  --quiet-passes \
  --bsr-witness-cap 262144 \
  --bsr-bal-cap 1024 \
  --steps 400000000
```

The same cap experiment can be run against the focused verdict probe, which
emits debug counters instead of the full stateless output:

```bash
scripts/codegen-zisk-stateless-verdict-check.sh \
  --filter withdrawal_requests \
  --skip 87 \
  --limit 1 \
  --bsr-witness-cap 262144 \
  --bsr-bal-cap 1024 \
  --steps 2000000000
```

Each verdict line prints the fixture's block gas limit separately from the
path, followed by named debug counters from fixed 8-byte output slots:

```text
dbg=[bv_fail=... header=... state=... bal_count=... bsr_fail=... change_count=... witness_len=... baacd_fail=... bacv_fail=... baap_fail=... sri_index=... sri_mode=... sri_status=...]
```

The main EEST harness uses the same fixed-size probe automatically on
`successful_validation` mismatches and appends its decoded slots to the `FAIL`
line. Disable that rerun with `--no-verdict-debug` or `EEST_VERDICT_DEBUG=0`
when only the canonical 105-byte stateless output comparison is wanted.

`bv_fail` is the top-level block-verdict failure code. `bsr_fail` and
`bal_count` classify the block-state-root replay path, while the `baacd`,
`bacv`, `baap`, and `sri` fields expose the lower-level account, storage, and
state-read helpers.

For receipt/log-specific misses, generate a triage map that links likely
blockers to focused beads:

```bash
scripts/eest-receipt-log-frontier-report.py --run-dir gen-out/eest-run --limit 100
```

See [`eest-receipt-log-frontier.md`](eest-receipt-log-frontier.md) for the
class definitions and owner beads.

Run a large batch:

```bash
scripts/codegen-eest-stateless-check.sh \
  --limit 1000 \
  --jobs 32 \
  --steps 1000000000
```

Resume from a later offset by skipping the first selected cases:

```bash
scripts/codegen-eest-stateless-check.sh \
  --skip 1000 \
  --limit 1000 \
  --jobs 32 \
  --steps 1000000000
```

Collect only the first few failures from a large or highly parallel run:

```bash
scripts/codegen-eest-stateless-check.sh \
  --all \
  --jobs 32 \
  --quiet-passes \
  --max-failures 20 \
  --steps 1000000000
```

Run every selected stateless block:

```bash
scripts/codegen-eest-stateless-check.sh \
  --all \
  --jobs 32 \
  --steps 1000000000
```

`--filter` is applied first, `--skip N` skips the first N stateless blocks in
that filtered order, and `--limit N` caps how many remaining blocks are emitted.
With `--all`, `--skip` still applies but no limit is added.

`--max-failures N` stops the harness once N `FAIL` or `ERROR` results have been
classified. `--stop-after-failures N` is an alias. With parallel jobs, workers
that already finished before the stop point may also be reported, but the
harness stops scheduling new cases and cleans up active workers once the cap is
observed.

Use `--quiet-passes` (or `EEST_QUIET_PASSES=1`) to suppress per-case
`PASS(full)` lines while still printing every `FAIL` and `ERROR` plus the final
summary. This is useful for large `--jobs 32 --max-failures N` searches after a
long passing prefix. `--show-passes` restores the default verbose pass output.

## Focused Verdict Probe

For verdict-only debugging, use the smaller probe harness:

```bash
scripts/codegen-zisk-stateless-verdict-check.sh \
  --filter validation_codes_missing \
  --limit 100 \
  --max-failures 5 \
  --steps 1000000000
```

In this probe, `--max-failures N` stops after N `ERROR`, false-positive, or
unexpected `DIFF` rows. Conservative misses (`verdict=0 exp=1`) are still
reported, but they do not count toward this cap because they are not unsound
acceptances.

## Outputs

Each harness invocation writes to a fresh run directory so concurrent EEST
searches do not clobber each other's manifests or case outputs:

```text
gen-out/eest-run/run-<timestamp>-<pid>/
```

Set `EEST_RUN_DIR=/path/to/dir` to force a stable directory for a single
reproducible run; that directory is recreated at the start of the invocation.

Important files:

- `manifest.tsv`: one row per selected guest invocation.
- `<case>.input`: ziskemu input for that fixture block.
- `<case>.output`: raw guest output.
- `<case>.emu.log`: ziskemu stdout/stderr.
- `<case>.result.tsv`: per-case harness status and output hex.
- `stateless_guest.{s,o,elf}`: guest artifacts for this invocation.
- `eest-baseline.txt`: run summary for this invocation.
- `gen-out/eest-baseline.txt`: copy of the latest harness summary.

The summary reports:

- `full match`: all 105 output bytes match.
- `root match`: bytes 0:32 match `new_payload_request_root`.
- `succ match`: byte 32 matches `successful_validation`.
- `tail match`: bytes 33:105 match the offset and chain config tail.
- `root-only diff`: success and tail match, but the root field differs.

Use `--min-full`, `--min-root`, or `--min-succ` to turn a batch into a
regression gate. For example:

```bash
scripts/codegen-eest-stateless-check.sh --limit 1000 --min-full 1000
```

## Useful Knobs

- `ZISKEMU=/path/to/ziskemu`: choose a specific emulator binary.
- `EEST_STEPS=N` or `--steps N`: set the ziskemu step cap.
- `EEST_JOBS=N` or `--jobs N`: set parallel guest jobs.
- `--max-failures N` or `--stop-after-failures N`: stop after N failures/errors.
- `EEST_QUIET_PASSES=1` or `--quiet-passes`: hide per-case pass lines.
- `EEST_MEM_RESERVE_MIB=N`: reserve host memory when auto-sizing jobs.
- `EEST_FIXTURES_DIR=/path`: point at an already extracted fixture directory.
