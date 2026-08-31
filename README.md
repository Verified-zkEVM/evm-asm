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

The branch is performance history only, not a conformance or verification
signal.
