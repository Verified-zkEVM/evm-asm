# Bead-claim & long-running-branch ledger

> Steering Phase 4, report §3 G2.6 / step 17 (D6). A lightweight,
> human-maintained **claim ledger** so two agents don't silently claim the
> same bead and so long-running `feat/…` branches are visible *before* they
> merge. Point-in-time metrics (`PROGRESS.md`, `progress-velocity.sh`) only
> see work once it lands on `main`; this file is the pre-merge view.

## Source of truth

The **`bd` beads tracker is the source of truth for outstanding work**
(see `AGENTS.md` → "Bead closure rules"). This file does **not** replace it
and must not be used to open/close beads. It is a *coordination overlay*:
which bead each in-flight branch/PR is working, so claims are legible and
collisions are caught by eye.

## How to use (agents + humans)

1. **Before starting work on a bead**, scan the table below. If a row already
   claims that bead id with an *active* status, coordinate instead of
   double-claiming (G2.6 collision detection).
2. **When you open a branch/PR for a bead**, add a row.
3. **When the PR merges or you abandon the branch**, set status to `merged` /
   `dropped` (or delete the row in the same PR that merges the work).
4. Keep it short — one row per active branch. Stale rows are noise.

Status vocabulary: `active` (in progress) · `review` (PR open, awaiting
review) · `blocked` (waiting on another bead/branch — name it) · `merged` ·
`dropped`.

## Active claims

| Bead id (`bd`) | Branch | PR | Worker | Claimed | Status | Notes / blocked-by |
|---|---|---|---|---|---|---|
| evm-asm-vgyg9 (=4ch8f.49.a) | `feat/vgyg9-guard-flag-ret` | — | Fable | 2026-07-04 | active | guard→flag+ret (guest-byte, races layout); coordinate merge order with #9792 (.49.1) |
| _(steering rollout)_ | `feat/phase4-review-throughput` | — | c1 | 2026-06-04 | review | Phase 4 review-throughput; stacked on `feat/phase3-divclass-defense` |
| _(steering rollout)_ | `feat/phase3-divclass-defense` | #8050 | c1 | — | review | stacked on `feat/phase2-direction-tracking` |
| _(steering rollout)_ | `feat/phase2-direction-tracking` | #8040 | c1 | — | review | base of the Phase 3/4 stack |

> Rows above are the steering-rollout stack (Phases 2–4 stacked, unmerged at
> Phase-4 hand-off). Replace/prune as the stack lands. The
> `feat/exp-*`/`feat/v5-*` working branches managed via `bd` need not be
> mirrored here unless two workers might collide on them.

## Stale-branch nudge

`.github/workflows/stale-pr-nudge.yml` labels a PR `stale` and posts a nudge
comment after a fixed idle window (it **never auto-closes** — agents are
forbidden from `gh pr merge`/`--approve`/`issue close`, see
`EEST_INSERT_HANDOFF.md`). Add the `long-running` label to a PR to exempt a
deliberately long-lived stacked branch from the nudge.
