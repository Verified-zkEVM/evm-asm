# Per-file lakeprof timing in weekly benchmark — design note

GH issue: #949 (follow-up).
Beads parent: `evm-asm-hj6c`. This slice: `evm-asm-mcc4`.
Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

## 1. Problem

The weekly benchmark workflow (`.github/workflows/benchmark.yml`, landed
in #1477 / `evm-asm-uv6q`) records two scalars per run: total `lake build`
wall time and peak RSS. That is enough to spot a *global* regression but
gives no signal about *which file* slowed down. Slice 2 of #949
(`evm-asm-7a4p`, design note) explicitly deferred per-target / per-file
timing via [lakeprof](https://github.com/Kha/lakeprof) to a follow-up.

This note is the design for that follow-up. It does NOT add lakeprof to
CI; it specifies how the next implementation slice should wire it.

## 2. Constraints (recap from #949 design notes)

- Weekly cron only — no PR-time cost.
- One workflow file (`benchmark.yml`) — keep the surface small.
- Existing scalars (wall + RSS) must keep flowing untouched.
- History persistence on the orphan `benchmark-history` branch must stay
  append-only and idempotent.
- No new GitHub Actions services or external dashboards. Run summary +
  `benchmark-history` JSONL only.
- `python3` stdlib only. The current workflow already uses a
  tempfile-script pattern for JSONL appending; keep that style.

## 3. lakeprof in 30 seconds

Recipe (from upstream README):

    # 1. Record (wraps `lake build`, captures Lake's task log + timestamps)
    lakeprof record -o lakeprof.log lake build

    # 2. Report (consumes lakeprof.log; uses `lake query` to recover edges)
    lakeprof report -i lakeprof.log [--print-crit-path]
                                    [--print-avg-crit]
                                    [--print-sim-times]
                                    [--save-chrome-trace trace.json]
                                    [--all]

Two output shapes are useful for our use case:

- `--print-crit-path` / `--print-avg-crit` — human-readable lists already
  sorted by contribution to the longest path. Cheap to scrape, but
  format is unstable across versions.
- `--save-chrome-trace trace.json` — Chrome `trace_event` JSON: a single
  array of `{name, ph, ts, dur, ...}` records, one per built target.
  Stable, machine-readable, and trivially parseable with `json` from the
  stdlib. **This is what we want.**

A `trace_event` record from lakeprof looks like (paraphrased):

    {
      "name": "EvmAsm.Evm64.DivMod.Spec.CallAddback",
      "ph":   "X",
      "ts":   1234567,
      "dur":  4567890,         # microseconds
      "pid":  1,
      "tid":  1,
      "args": { "category": "lean" }
    }

So a top-N table is `sort -k dur desc | head -N` over `name, dur`.

Caveats:

- lakeprof uses `lake query` to recover edges, so `.lake/build` must
  still exist when `lakeprof report` runs. Easy: run `report`
  immediately after `record` in the same job.
- `lakeprof record` re-invokes the build, so it must replace (not run
  alongside) our existing `lake build` step in the lakeprof job, OR run
  a clean second build in a separate job. We do the latter — see §5.

Install: `uv tool install --from git+https://github.com/Kha/lakeprof
lakeprof`. The runner already has a Lean toolchain via lean-action;
adding `astral-sh/setup-uv@v3` (or `pipx`) is a single-line workflow
change.

## 4. Schema additions

We extend `history.jsonl` (one JSON object per line on the
`benchmark-history` branch) by one OPTIONAL field:

    {
      ...                       # existing fields (commit, ref, wall_seconds, ...)
      "top_modules": [
        { "name": "EvmAsm.Evm64.DivMod.Spec.CallAddback",
          "dur_seconds": 87.31 },
        { "name": "EvmAsm.Evm64.DivMod.Spec.V4",
          "dur_seconds": 42.05 },
        ...                     # bounded length, default 20
      ]
    }

Rules:

- `top_modules` is OPTIONAL. Records produced before this slice ships
  (or by a workflow run where lakeprof failed) MUST omit it, not stub it
  to `null` or `[]`. Consumers should treat its absence as "lakeprof did
  not run".
- `dur_seconds` is a `float` rounded to two decimals. The raw lakeprof
  unit is microseconds; we divide by `1_000_000.0` and `round(_, 2)`.
  Avoids spurious sub-millisecond noise drowning a top-N diff.
- `name` is the lakeprof-reported target name verbatim (typically the
  Lean module name, e.g. `EvmAsm.Evm64.DivMod.Spec.V4`). We do NOT
  rewrite `.` to `/` or strip prefixes — keep the format machine-stable
  even if it isn't a filesystem path.
- `top_modules` length defaults to 20 (configurable via a workflow env
  var `LAKEPROF_TOP_N`).

We deliberately do NOT add a per-module record of every target. Sticking
to top-N keeps the JSONL line small (~2 KB) and steady over time; if the
full distribution is ever needed, the chrome-trace file is uploaded as
an artifact (§5) and is keyed by `run_id`.

The README on `benchmark-history` should grow one bullet documenting the
new optional field.

## 5. Workflow shape

We add a SEPARATE job `lakeprof` to `.github/workflows/benchmark.yml`,
running on the same trigger (Mon 06:00 UTC + manual dispatch). Two
reasons for a sibling job rather than appending steps to `benchmark`:

1. Lakeprof needs a clean second `lake build` (its own `record` wraps
   the build). Putting it in the same job would either duplicate the
   timed build (skewing wall) or replace it (changing the meaning of
   the existing scalar). Both undesirable.
2. If lakeprof itself breaks (upstream change, install failure), the
   primary wall/RSS metric must still flow. A sibling job with
   `if: always()` semantics on history-write isolates the failure.

Sketch (final wording happens in the implementation slice; this is
indicative shape, not a copy-pasteable patch):

    jobs:
      benchmark:
        # unchanged: wall + RSS
        ...

      lakeprof:
        runs-on: ubuntu-latest
        timeout-minutes: 360
        # Independent of `benchmark`. Runs on the same trigger.
        steps:
          - uses: actions/checkout@v4
            with: { submodules: recursive }
          - uses: leanprover/lean-action@v1
            with:
              use-mathlib-cache: true
              use-github-cache: false
              lake-package-directory: .
              build: "false"
          - run: lake exe cache get      # Mathlib cache, AGENTS.md
          - uses: astral-sh/setup-uv@v3
          - name: lakeprof record
            run: |
              uvx --from git+https://github.com/Kha/lakeprof \
                lakeprof record -o lakeprof.log lake build
          - name: lakeprof report (chrome-trace + crit-path)
            run: |
              uvx --from git+https://github.com/Kha/lakeprof lakeprof report \
                -i lakeprof.log \
                --save-chrome-trace lakeprof.trace.json \
                --print-crit-path \
                --print-avg-crit \
                | tee lakeprof.report.txt
          - name: Extract top-N
            id: topn
            run: python3 .github/workflows/scripts/lakeprof_topn.py \
                   --in lakeprof.trace.json \
                   --out lakeprof.topn.json \
                   --n "${LAKEPROF_TOP_N:-20}"
          - name: Write job summary
            run: |
              {
                echo "## lakeprof top-${LAKEPROF_TOP_N:-20} slowest modules"
                python3 .github/workflows/scripts/lakeprof_md.py \
                  --in lakeprof.topn.json
              } >> "$GITHUB_STEP_SUMMARY"
          - name: Append top-modules to benchmark-history
            if: success()
            run: bash .github/workflows/scripts/lakeprof_append.sh
            env:
              GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
          - uses: actions/upload-artifact@v4
            if: always()
            with:
              name: lakeprof-${{ github.run_id }}
              path: |
                lakeprof.log
                lakeprof.trace.json
                lakeprof.report.txt
                lakeprof.topn.json
              retention-days: 90

The two helper scripts (`lakeprof_topn.py`, `lakeprof_md.py`,
`lakeprof_append.sh`) live under `.github/workflows/scripts/` so the
workflow YAML stays readable and the parsing logic is unit-testable
locally with stdlib Python. The implementation slice is responsible for
landing those helper files.

`lakeprof_append.sh` mirrors the existing benchmark-history clone +
append + retry-loop pattern from the `benchmark` job; the only
difference is that the appended record contains ONLY commit, ref,
run_id, and `top_modules` (no `wall_seconds` / `peak_rss_kb` — those
came from the sibling job). The lakeprof record carries `"kind":
"lakeprof"` and the benchmark record carries `"kind": "build"` so the
two streams are distinguishable. Existing pre-#949-followup records
have neither key, which is fine — consumers default to `"build"` when
absent.

## 6. Failure modes and rollback

- **lakeprof install fails** (network issue, upstream change). The
  `lakeprof` job fails red but the `benchmark` job is unaffected.
  History gets a normal `kind=build` entry, no lakeprof entry. Acceptable.
- **lakeprof produces no chrome-trace** (e.g. an `lake query` failure
  after a Lake bump). `lakeprof_topn.py` exits non-zero, the job fails;
  same isolation as above.
- **Schema regret** — if the appended `top_modules` shape proves wrong,
  we can stop writing it (skip the `lakeprof_append.sh` step) without
  rewriting history. Existing entries without the field are
  forward-compatible.
- **Cost** — one extra ~30-min runner-hour per week. The current
  benchmark job already takes ~30 min; this doubles weekly benchmark
  cost but stays well under any sensible budget.

## 7. Out of scope for this slice

- Trend detection / "module X regressed N%" alerts. Tracked separately
  via #949 slice 4 (`evm-asm-9o8v`, already CLOSED for the wall/RSS
  scalars).
- A built-in dashboard. Consumers can read `history.jsonl` directly or
  spin up an external viewer over the chrome-trace artifacts.
- Replacing the existing wall/RSS scalars. Both metrics are useful; we
  add lakeprof, we don't displace it.

## 8. Acceptance for this slice

This slice is documentation only. Acceptance:

- This file (`docs/949-lakeprof-design.md`) lands on `main`.
- A follow-up beads slice exists for the implementation work, blocked
  on this one. The implementation slice's acceptance: lakeprof job
  green on a manual `workflow_dispatch` run, top-modules entry visible
  in `benchmark-history`, no regression to the existing wall/RSS
  scalars.
