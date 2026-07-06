# Merge-queue design — batching + TAP test-and-bisect

> Steering Phase 4, report §5 step 14 (R-C5 companion). **This is the design
> doc that must land *before* the merge queue is switched on** (report §6:
> "Do NOT make CI gates that exceed the Lean build budget … Use the merge
> queue with batching + auto-bisect, not serial re-runs"). Activating the
> queue is a repository *setting* the maintainer flips after reading this; the
> doc exists so the eviction behaviour is understood before friction lands.

## 1. Problem

`evm-asm`'s heaviest CI is a full clean Lean build plus the ~516 `codegen-*.sh`
ziskemu round-trip scripts and the EEST stateless harness. Running that suite
serially, once per PR, at merge time, bottlenecks throughput to roughly a
handful of merges per hour and makes the single maintainer (`@pirapira`) the
scaling limit. Worse, **merge skew** — a PR that proved green in isolation but
breaks `main` once a *different* PR merges underneath it — is unguarded today:
`build.yml` runs on `pull_request` against the PR's base, not against the
post-merge trunk.

## 2. What is already in place

- `build.yml` **already triggers on `merge_group`** (line 7). The plumbing for
  a GitHub merge queue is half-present: the workflow will run against the
  queue's speculative merge commit the moment the queue is enabled. No workflow
  change is required to start.
- The queue itself is **not enabled** — there is no required-status / merge-
  queue ruleset yet (see `.github/CODEOWNERS` header and the Phase 4 PR open
  questions). Enabling it is the action this doc gates.

## 3. Design — GitHub native merge queue with batching

Enable GitHub's built-in merge queue on `main` with:

- **Batch (group) merges**, not a single-PR-at-a-time queue. The queue forms a
  speculative commit stacking N pending PRs on top of current `main` and runs
  `build.yml` once against that combined commit. On success the whole batch
  merges; throughput is N merges per CI run, not one.
- **Required check:** the `build` job from `build.yml` (it runs on
  `merge_group`). This is the post-merge-skew guard — the batch is tested
  against the *actual* trunk it will become, catching the "green in isolation,
  red on trunk" class the per-PR `pull_request` run cannot.

### 3.1 TAP test-and-bisect on batch failure

The danger of batching is a single bad PR failing the whole batch. Re-running
the full ~516-script ziskemu suite per PR to find the culprit would defeat the
point. Instead, on a batch failure the queue follows the Google **TAP**
(Test Anything Protocol) test-and-bisect pattern:

1. The batch CI run fails. GitHub's merge queue does **not** merge the batch.
2. **Bisect, don't re-run-all.** Split the failing batch in half and test each
   half's speculative commit. Recurse on the failing half. This finds the
   offending PR in `O(log N)` CI runs rather than `O(N)` full-suite re-runs.
   GitHub's native queue approximates this by re-forming smaller speculative
   groups after a failure and ejecting the PR whose group cannot go green.
3. **Eject** the offending PR from the queue (GitHub removes it and comments on
   it); the remaining PRs re-form a fresh batch and proceed.
4. The ejected PR's author rebases / fixes and re-queues.

GitHub's merge queue does the speculative-grouping and eviction automatically
once configured; the **explicit knob** is the batch size (`Maximum PRs to
build` / `Minimum/Maximum group size`). The bisection cost model above is why
we batch rather than serialize, and why batch size is a tunable, not "as large
as possible".

### 3.2 Heavy vs light check placement

To keep the queue from becoming the very budget-buster §6 warns against:

| Check | PR push (`pull_request`) | Merge queue (`merge_group`) | Nightly |
|---|---|---|---|
| Forbidden-tactic / file-size / unimported / roundtrip-coverage | ✅ | ✅ | |
| `lake build` + no-warnings + drift + axiom audit + conformance floor | ✅ | ✅ | |
| Arith differential fuzz (Lean fast-path) | ✅ | ✅ | |
| Full ~516 `codegen-*.sh` ziskemu suite | ❌ (too heavy) | ✅ batch only | ✅ |
| execution-specs Python differential fuzz (`fuzz-arith.yml`) | ❌ | ❌ | ✅ |
| EEST `--min-full` stateless harness | ❌ | ✅ batch only (once wired) | ✅ |

The principle: **cheap, cached checks on every PR push; the expensive full
suite once per *batch* at the queue**, never serially per PR. Long fuzz/dual-
path suites stay nightly. This is consistent with the existing PR/`merge_group`
split already encoded in `build.yml`'s cache-save logic (PR runs restore-only;
`merge_group`/push save).

## 4. Activation checklist (maintainer)

This doc does **not** enable anything. To turn the queue on:

1. Confirm `build`'s required-status name and that it runs on `merge_group`
   (it does today).
2. Repo Settings → Branches/Rulesets → enable **Merge queue** on `main`.
3. Set batch size (start small, e.g. 3–5; raise after observing bisect cost).
4. Choose merge method consistent with project policy (the project uses
   merge commits, not rebase — see `progress-history.yml` "no rebase" note).
5. Require the `build` check in the queue.
6. Land the companion CODEOWNERS ruleset (R-C5) in the same settings pass.

## 5. Non-goals / cautions (report §6)

- **Do not** make per-PR CI run the full ziskemu suite — that is the
  ~4-merges/hour bottleneck this design exists to avoid.
- **Do not** raise batch size without watching the bisect cost: a too-large
  batch makes every failure expensive to localize.
- The merge queue guards **merge skew and throughput**; it does not replace the
  kernel, conformance floor, or tamper scans. It is a scheduling mechanism.
- Risk scores (R-B1) are triage ordering for the human, **not** auto-merge
  authority for the verified core (report §6).

## 6. Open questions (carried into the Phase 4 PR)

- Batch size + eviction policy — confirm before flipping the queue on
  (Phase 4 open question #2).
- Whether to gate the queue with the full ziskemu suite immediately, or phase
  it in (start with `lake build` + fast checks, add the suite once bisect
  behaviour is observed in practice).
