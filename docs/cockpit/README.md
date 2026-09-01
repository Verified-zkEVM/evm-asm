# evm-asm progress cockpit

Live visual dashboard of the kernel-checked progress registries
(`EvmAsm/Progress.lean`, `Progress/Routines.lean`, `Progress/Obligations.lean`,
`Progress/Correspondence.lean`, `Progress/GuestImageCoverage.lean`).

**Published site:** <https://verified-zkevm.github.io/evm-asm/>

The homepage is [`docs/index.html`](../index.html). CSS/JS and the generated
snapshot live in this directory so `docs/` does not accumulate cockpit files.

## What is committed

| File | Role |
|---|---|
| `docs/index.html` | Pages homepage (count-free) |
| `docs/.nojekyll` | disable Jekyll if Pages is pointed at `/docs` |
| `docs/cockpit/cockpit.css` | styles |
| `docs/cockpit/cockpit.js` | load snapshot + render |
| `docs/cockpit/snapshot.json` | **not committed** — generated |
| `docs/cockpit/snapshot.js` | **not committed** — same payload as a script |

Counts are generated on demand. Committing them would recreate the #12683
`PROGRESS.md` merge-conflict class.

## Local preview

```bash
scripts/progress-cockpit.sh --write
open docs/index.html
```

`open` uses `file://`. That works because the snapshot is also written as
`snapshot.js` (browsers block `fetch()` of local JSON — HTTP status 0).
A static server from `docs/` still works: `python3 -m http.server 8080`.

## How it stays fresh

Do **not** hand-edit counts into the HTML. Update the Lean registries (and
regenerate `DRIFT.md` with `scripts/drift-report.sh --write` when those
rows change). Merge to `main`; `.github/workflows/progress-cockpit.yml`
rebuilds the snapshot and deploys Pages.

One-time repo setting (admin): **Pages source = GitHub Actions**.

“Deploy from branch `main`, folder `/docs`” serves the committed HTML but
**not** the snapshot (gitignored), so the live page sticks on “Snapshot not
available”. The Actions job can still go green; GitHub keeps serving `/docs`
until the source is switched. The Actions artifact is cockpit files only
and includes the generated snapshot.
