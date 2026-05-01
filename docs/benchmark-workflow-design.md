# Benchmark workflow design for evm-asm

Slice 2 of #949 (parent beads `evm-asm-d8t5`, slice beads `evm-asm-7a4p`).
Informed by a slice-1 survey of
`Beneficial-AI-Foundation/curve25519-dalek-lean-verify`'s benchmark
workflows (`evm-asm-5pbn`); that survey was a fact-finding exercise and
its standalone notes file has been dropped — relevant decisions are
captured below and credited inline.

This note records the design decisions for evm-asm's own benchmark CI.
Slice 3 (`evm-asm-uv6q`) implements the workflow following these
decisions; slice 4 (`evm-asm-9o8v`) implements regression surfacing.

## Scope of #949

#949 asks for a *weekly* benchmark workflow that captures `lake build`
times so we can detect proof-time regressions over months. PR-on-demand
benchmarks (the curve25519 `!bench` pattern) are explicitly out of scope
here — they are a worthwhile follow-up, but we want the weekly series in
place first. This design therefore ships only the weekly-cron piece,
while leaving the door open for PR comments later.

## (a) What gets timed

**Decision**: per-Lake-target wall-clock time, captured by `lakeprof`
(`github.com/Kha/lakeprof`), plus the total `lake build` wall-clock as a
top-line summary.

Rationale:

- `lakeprof` is the same tool curve25519-dalek-lean-verify uses, is
  toolchain-agnostic (works with any `lean-toolchain`-pinned version),
  and emits per-target timings without modifying the project. We don't
  need to invent our own profiling harness.
- Per-target granularity is what we actually need for #949: a single
  total-build number tells us *that* something regressed, but not
  *where*. The proof-time hot spots in evm-asm move around as we
  refactor (DivMod compose chains, Shift compose chains, RLP files);
  per-target lets us see which specific module slowed down.
- We deliberately do **not** capture `lake exe profile-time`,
  per-declaration heartbeats, or `set_option trace.profiler`-style data
  in this slice. Those are useful for ad-hoc proof debugging, not for
  long-running regression tracking, and they balloon the storage
  footprint. They can be added later if a particular regression hunt
  needs them.
- We also do **not** include `lake build EvmAsm.lean` cache-cold vs
  cache-warm splits. The weekly run is always cache-cold (fresh runner,
  no Mathlib cache), which is the correct steady-state measurement.
  `lake exe cache get` should be invoked before `lake build` to pull
  Mathlib oleans (otherwise we'd be measuring Mathlib build time, not
  ours).

Concrete shape of the captured data: a single JSON document per run
containing `{date, sha, total_seconds, targets: [{name, seconds}, ...]}`.
This is what `lakeprof` already produces; the runner just has to attach
the SHA and date.

## (b) Where the historical series is stored

**Decision**: committed JSON in `bench/history/YYYY-MM-DD-<short-sha>.json`
on a dedicated `bench-history` orphan branch, plus a rolled-up
`bench/latest.json` symlink/copy on the same branch. The weekly workflow
pushes new entries; nothing else writes there.

Rationale and alternatives considered:

- **External hosted API (benchwarmer-style)** — rejected. curve25519
  uses this, but it requires standing up and maintaining a server, plus
  a secret URL/token. evm-asm doesn't have the operational appetite for
  a long-lived external service, and a self-hosted API is a much larger
  scope than #949.
- **Workflow artifacts retention** — rejected as the *source of truth*.
  GitHub's default 90-day artifact retention is too short for the
  multi-month regression series #949 wants (proofs slowly drift over
  quarters as Mathlib bumps and large refactors land). Artifacts are
  also awkward to query — you can't `git log -p bench/history/` to see
  how a specific target's time evolved.
- **Committed JSON on `main`** — rejected. Adding a weekly commit to
  `main` would pollute `git log --oneline main`, churn `git blame`, and
  trigger CI on every weekly write. We want the data in-repo but
  invisible to anyone working on `main`.
- **`gh-pages` branch** — rejected as overkill. `gh-pages` is for HTML;
  if we ever want a chart UI we can add one later (the JSON is the
  primary asset, the chart is derived).
- **Dedicated orphan branch** — chosen. `bench-history` lives entirely
  outside the `main` history (orphan = no shared ancestor), so it
  doesn't affect anything `main`-side. The workflow checks it out into
  a temporary directory, appends today's JSON, and pushes. Storage is
  cheap (one small JSON per week, ~52/year). Anyone who wants the
  series clones the branch directly.

Schema: see `bench/SCHEMA.md` (created in slice 3). Versioned via a
`schema_version` field so we can extend without breaking older entries.

## (c) Regression-surfacing UI

**Decision (for #949 / slice 3)**: weekly run posts/updates a single
tracking issue. Specifically:

- The weekly workflow looks for an open issue with the label
  `benchmark-tracking` and a fixed title (e.g. `Weekly benchmark report`).
- If it exists, the workflow edits the body to show the latest run plus
  a brief diff against the previous week (which targets got slower /
  faster, by how much, top 5 each direction).
- If it doesn't exist (first run, or someone closed it), the workflow
  opens a new one with the same label and title.

Rationale:

- A *single* updated issue, rather than curve25519's "open a new issue
  every week" pattern, keeps the issue tracker clean. The full history
  lives in `bench-history`; the issue is just the most-recent snapshot.
- A tracking issue is browseable, subscribable, and supports comments
  (humans can call out a specific regression for follow-up). A README
  badge or static gh-pages chart can't.
- Threshold-based *failure* (red CI on regression) is **deliberately
  not** in this slice. evm-asm proof times are noisy enough on shared
  GitHub runners that a strict threshold would flap; we want humans to
  read the weekly report and decide whether a regression is real before
  any CI gate is added. A noisy-CI feature can be added later (slice 4
  or a separate task) once we have a few months of data to set a
  reasonable threshold.
- README badges, gh-pages charts, and PR comments are explicitly
  deferred — they are valuable additions but not required by #949 and
  each adds its own maintenance surface.

## (d) Cadence

**Decision**: `cron: '0 6 * * 1'` (Mondays 06:00 UTC, same as
curve25519), plus `workflow_dispatch` for manual runs. One run per week.

Rationale:

- Weekly is what #949 asks for. Daily would 7x the noise without
  giving us new signal — proofs don't drift fast enough day-to-day
  for daily granularity to matter, and a single weekly snapshot is
  cheap to read.
- Monday 06:00 UTC = 07:00 / 08:00 CET (winter / summer). The user's
  Monday morning starts with the latest report visible without any
  weekend churn on the issue tracker.
- `workflow_dispatch` lets us trigger a benchmark on demand (e.g.
  after a suspected-slowdown PR merges) without waiting for the next
  Monday.

## Out of scope here (followups)

These are explicitly *not* part of the slice 3 implementation; track
each as its own future task if/when wanted:

- PR-on-demand `!bench` benchmarks (curve25519's pattern).
- Threshold-based CI failure on regression.
- README badge or gh-pages chart of the historical series.
- Per-declaration heartbeats / `lake exe profile-time` integration.
- Cross-repo benchmark comparison or shared infra with other Lean
  projects.

## Summary of slice-3 deliverables

For the implementer of `evm-asm-uv6q` (slice 3) — the workflow needs
to, on the Monday cron:

1. Check out `main`, install elan + `uv`, install `lakeprof`.
2. Run `lake exe cache get` to pull Mathlib oleans.
3. Run `lakeprof` against the `EvmAsm` library, producing per-target
   wall-clock JSON.
4. Decorate the JSON with date + SHA, commit to
   `bench-history:bench/history/YYYY-MM-DD-<sha>.json` and update
   `bench/latest.json`, push (using a workflow token with branch
   write access).
5. Compute a diff against the previous entry on `bench-history`.
6. Update (or open) the `benchmark-tracking`-labeled issue with the
   markdown report (latest snapshot + diff).

Slice 4 (`evm-asm-9o8v`) handles the regression-surfacing details
(diff format, top-N selection, threshold tuning if any).
Slice 5 (`evm-asm-xzn0`) adds the AGENTS.md note pointing readers at
the `bench-history` branch and the tracking issue.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
