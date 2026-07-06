# EEST Stateless Work Handoff

This file used to contain a one-off account-INSERT debug handoff. That material
is stale: the branches, PR numbers, debug output layout, and commit-trailer
instructions no longer describe the current EEST workflow.

Use these current sources instead:

- `LOOP.md` for the agent work loop, claim-file convention, PR rules, and commit
  trailer.
- `bd ready --limit 80` for the live priority queue. Prefer concrete child
  beads over old handoff narratives.
- `docs/eest-stateless-testing.md` for the stateless EEST harness, focused
  wrappers, row reproduction flags, randomized sampling, memory/job controls,
  verdict-debug output, and `--max-failures`.
- `docs/eest-feature-surfaces.md` for mapping fixture families to active feature
  beads.
- `docs/agents/stateless-input-contract.md` for the byte-level contract that
  must match execution-specs `run_stateless_guest`.

When a pasted EEST failure includes `manifest_row`, `rerun_skip`, `rerun_limit`,
and `random_seed`, reproduce it directly with:

```bash
scripts/codegen-eest-stateless-check.sh \
  --skip <rerun_skip> \
  --limit <rerun_limit> \
  --seed <random_seed> \
  --random \
  --jobs 1 \
  --quiet-passes \
  --steps 1000000000
```

For non-random output, omit `--random` and `--seed`. Use `--run-dir DIR` when
you need to preserve or compare a specific run directory.

Account-INSERT or MPT-insert investigations should now be tracked in beads with
the exact failing row, current branch/PR state, and current debug fields. Do not
restart from the obsolete instructions that were previously in this file.
