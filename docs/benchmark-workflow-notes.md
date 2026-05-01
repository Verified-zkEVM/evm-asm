# Benchmark workflow survey: curve25519-dalek-lean-verify

Survey of how `Beneficial-AI-Foundation/curve25519-dalek-lean-verify` runs Lean
build benchmarks via GitHub Actions. Captured 2026-05-01 from
`.github/workflows/{bench-main,bench-pr,bench-weekly}.yml`. This is a fact-finding
note for slice 1 of #949 (parent beads `evm-asm-d8t5`); design choices for evm-asm
itself are deferred to slice 2.

## Three-workflow split

The repo has three separate workflow files that share one runner script:

1. `bench-main.yml` — triggered on every push to the default branch (and
   `workflow_dispatch`). Runs the benchmark, posts results to an external API.
2. `bench-pr.yml` — triggered by `issue_comment` of `!bench` from MEMBER /
   OWNER / COLLABORATOR. Runs against the PR head, fetches a PR-vs-base diff
   report from the API, and edits a status comment on the PR with the markdown
   report.
3. `bench-weekly.yml` — `cron: '0 6 * * 1'` (Mondays 06:00 UTC) plus
   `workflow_dispatch`. Runs the benchmark and opens a fresh GitHub issue
   titled `Weekly Benchmark Report - $DATE` whose body is markdown returned
   by the API.

All three run on `ubuntu-latest` and use the same setup steps:

- `curl … elan-init.sh` to install elan with `--default-toolchain none` (the
  toolchain is then picked up from `lean-toolchain`).
- `astral-sh/setup-uv@v4` to install `uv`.
- `uv tool install --from git+https://github.com/Kha/lakeprof lakeprof` —
  Sebastian Ullrich's `lakeprof` tool is the actual measurement engine.
- `bash "$RUNNER_SRC/bench.sh" "$BENCH_LIBRARY_NAME" "$BENCH_API_ENDPOINT"` —
  the heavy lifting lives in a separate runner script (`runner/bench.sh`),
  not in the workflow YAML.

## What is measured

`lakeprof` (https://github.com/Kha/lakeprof) is a per-target Lake build
profiler — it captures wall-clock time per Lake build target/file. Raw
timings are produced by the runner script and uploaded to the external
benchmark API; the workflow YAML itself does not parse them.

## Where data is stored

There is no in-repo storage of historical timings — no committed JSON, no
`gh-pages` branch, no Actions artifact retention used as the source of truth.
Everything goes through an external HTTP API ("benchwarmer"):

- `BENCH_API_ENDPOINT` — secret URL of the API server.
- `BENCH_AUTH_TOKEN` — secret for upload auth.
- `BENCH_LIBRARY_NAME` — repo-vars-configured library identifier.
- `BENCHWARMER_RUNNER_PATH` (var, optional, defaults to `runner`) — path to
  the checked-out runner source.

The API serves three report endpoints, all returning JSON `{markdown: "..."}`:

- `${ENDPOINT}/${repo}/${sha}/report/pr?base=${baseSha}` — PR-vs-base diff
  (with a fallback to default-branch tip if the base SHA isn't known to the
  server).
- `${ENDPOINT}/${repo}/${sha}/report/weekly` — weekly summary.
- (The push-on-main run only uploads; it doesn't fetch a report.)

## How regressions are surfaced

- **PR runs (`bench-pr.yml`)**: opt-in via `!bench` comment from a member/
  owner/collaborator. Workflow reacts `+1` to the comment, posts a "running"
  status comment, then PATCHes that comment with the markdown report from the
  API once the run completes. Empty/non-200 responses fail the job.
- **Weekly (`bench-weekly.yml`)**: opens a brand-new issue
  `Weekly Benchmark Report - YYYY-MM-DD` with the markdown report as the
  body. No automatic threshold-based failure — surfacing is purely
  informational.
- **Main (`bench-main.yml`)**: silent — only uploads. No comment, no issue.
  This appears to exist to populate the historical series so PR diffs have a
  baseline to compare against.

## External dependencies

- **lakeprof** (`Kha/lakeprof`) — third-party tool, installed fresh per run
  via `uv tool install`.
- **benchwarmer** API — a separate hosted service that the curve25519 group
  maintains; not part of the Lean ecosystem.
- **runner/bench.sh** — assumed checked out into `runner/` (or
  `BENCHWARMER_RUNNER_PATH`); not present in the public repo workflow YAML
  itself.

## Implications for evm-asm (deferred to slice 2)

Notes for slice 2 (`evm-asm-7a4p`) to consider — not decisions:

- The reference design assumes a hosted API (benchwarmer). evm-asm probably
  doesn't want to stand up an external service for slice 3, so storage will
  need a different answer (artifacts vs gh-pages vs committed JSON).
- `lakeprof` is the obvious off-the-shelf measurement tool for per-target
  timings.
- Three-trigger split (push-on-main, opt-in PR, weekly cron) is overkill for
  #949 which only asks for the weekly cron. PR-on-demand is a worthwhile
  follow-up but out of scope here.
- The PR workflow's `!bench` opt-in pattern (gated on
  `author_association`) is a useful template if/when slice 3+ adds PR
  benchmarks.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
