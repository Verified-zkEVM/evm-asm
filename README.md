# cycles-history

Append-only consumed-step datapoints from the Spike EEST stateless-guest
producer (`scripts/codegen-eest-stateless-check.sh --append-cycles`).

One JSON object per line in `cycles-history.jsonl`:

- `commit`, `date`, `eest_tag`: source and fixture provenance
- `program`, `elf`: logical case and guest artifact path
- `steps`: exact retired RISC-V instructions from Spike's `minstret`
- `cycles`: nullable zkVM-cycle field (not emitted by Spike)
- `halted`: clean-halt marker; persisted records must be `true`
- `source`: producer script

From a main checkout, produce and persist a local Spike datapoint with the
checked-in producer, an explicit guest artifact and a narrow fixture selection:

```sh
EEST_FIXTURE_TAG=tests-zkevm@v0.6.2 \
scripts/codegen-eest-stateless-check.sh \
  --backend spike \
  --guest-elf "$PWD/gen-out/regionmap/stateless_guest.elf" \
  --filter account_write_authority_is_recipient \
  --limit 1 \
  --append-cycles \
  --persist-cycles
```

The run must be clean and the caller needs `GITHUB_TOKEN` plus
`GITHUB_REPOSITORY` (or `HISTORY_ORIGIN_URL` for a local test remote).  The
producer validates the non-null `steps`/`halted=true` record, then the
persistence command appends it to this branch through the shared
orphan-history helper.

The branch is performance history only, not a conformance or verification
signal.
