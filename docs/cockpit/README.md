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
| `docs/cockpit/cockpit.js` | fetch + render |
| `docs/cockpit/snapshot.json` | **not committed** — generated |

Counts are generated on demand. Committing them would recreate the #12683
`PROGRESS.md` merge-conflict class.

## Local preview

```bash
scripts/progress-cockpit.sh --write
cd docs && python3 -m http.server 8080
```

Then open <http://localhost:8080/>. Serve from `docs/` so `index.html` can
resolve `./cockpit/…`.

## How it stays fresh

Do **not** hand-edit counts into the HTML. Update the Lean registries (and
regenerate `DRIFT.md` with `scripts/drift-report.sh --write` when those
rows change). Merge to `main`; `.github/workflows/progress-cockpit.yml`
rebuilds the snapshot and deploys Pages.

One-time repo setting (admin): **Pages source = GitHub Actions**. Until that
is enabled, the deploy job fails; the generator and local preview still work.

The fallback setting “Deploy from branch `main`, folder `/docs`” also serves
`docs/index.html` as `/`, but would publish every other file under `docs/`
as well — prefer the Actions artifact (cockpit files only).
