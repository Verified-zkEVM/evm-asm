# EEST Static Layout Lessons

Moved out of `AGENTS.md` to keep the agent guide compact. Load this when:

- changing `stateless_guest`, `block_state_root`, BAL replay, or EEST harness
  memory layout;
- changing static `.data` arenas used by EEST codegen programs;
- adding harness filters or cap checks for EEST stateless runs.

## Protocol Limits First

Do not pick static arena sizes from the failing fixture alone. Check the local
`execution-specs` and `execution-spec-tests` submodules first, then size or
gate from the protocol/test limit that actually constrains the data.

For BAL replay, Amsterdam does not use a fixed account-row cap. The rule is
gas-derived:

```text
bal_items <= block_gas_limit / 2000
bal_items = account addresses + unique storage keys
```

The source of truth is
`execution-specs/src/ethereum/forks/amsterdam/block_access_lists.py` plus
`execution-specs/src/ethereum/forks/amsterdam/vm/gas.py`.

This means a complete static layout is complete only relative to a declared
maximum supported **actual BAL item count**, not merely a declared block gas
limit. For the execution-specs default block gas limit of 120,000,000, the BAL
item budget is 60,000. The current emitted static replay arenas are sized for
100,000 BAL items (the 200M target); the older 500,000-item/1G layout is
historical. A layout with a declared capacity must cover both extreme shapes:

- many account rows, which stress `basr_*` account-record arrays and the
  top-level `bsr_*` state-change arrays;
- one/few accounts with many storage keys, which stress per-account storage
  replay arrays such as `baap_storage_desc`, `baap_storage_paths`,
  `baap_storage_delete_paths`, and `baap_storage_values`. The
  `baap_storage_delete_paths` child is historical/probe-only in the current
  guest; the emitted `RegionMap.dataUnionChildren` has no such symbol.

Do not resize only the first array that failed. Follow every index that derives
from the same count and resize the matching backing storage together.

Large static arenas can outgrow the previous linked `.data` location. When
that happens, treat the ELF memory map as part of the layout: keep linked
`.data`, fixed working-RAM anchors, public output, and `.sszscratch` disjoint.
The current stateless guest layout (sized for the Amsterdam 200M block-gas
target, `bsrMaxBalItems = 100000`) puts `.data` at `0xa3000000` and
`.sszscratch` at `0xbf980000`, both inside the verified RAM zone. Keep the
linked `.data` growth below the `.sszscratch` start and leave headroom below
`0xc0000000`.

## State Witness Caps

The `block_state_root` witness-length guard is different from the BAL row and
state-change arena caps. The witness bytes are carried in the EEST input and
searched by the MPT helpers; simply raising the guard does not allocate a larger
`.data` arena, but it can expose execution-time blowups from repeated linear
witness scans.

Before changing the default witness cap, run both the full stateless harness and
the fixed-size verdict probe on the exact frontier that motivated the change.
For example, EIP-7251 `consolidation_requests.json` selected index 138 has
`witness_len=204888`: the default 64 KiB cap gives a conservative
`bsr_fail=111`, while an experimental 256 KiB cap reaches
`EmulationNoCompleted` even in the verdict probe at 2B steps. That means the
next implementation frontier is replay/indexing performance, not only a larger
constant.

## Runtime Resource Compatibility

Do not reject an EEST fixture only because its declared block or transaction
gas limit is larger than the gas value used to size the current static arenas.
Some legacy/static tests use deliberately huge gas limits while consuming tiny
resources. The runner should launch those fixtures and let the guest enforce
the real resource boundaries:

- Amsterdam BAL validity: `actual_bal_items <= block_gas_limit / 2000`;
- static arena compatibility: actual decoded BAL/state/storage counts must fit
  the compiled guest layout;
- arithmetic overflow/underflow in runtime gas, memory, and address
  computations must be detected at the operation that would exceed the
  implemented resource model.

If a future PR needs to support an actual decoded item count above the current
static arena capacity, choose one of these approaches explicitly:

- build a larger layout and a corresponding ELF, with docs naming the supported
  maximum actual resource counts;
- implement streaming/chunked replay so memory scales with actual contents
  instead of worst-case gas.

For the current EIP-8037 high-block-gas frontier, see
[`docs/eest-1g-block-gas-layout-plan.md`](../eest-1g-block-gas-layout-plan.md).
It records the memory-map changes that made 500,000 BAL items fit and explains
why the old `ERROR(layout)` behavior was not the desired endpoint.

## Documentation

When changing these limits, update both:

- this agent note, for future implementation work;
- `docs/eest-stateless-testing.md`, for users running the harness.
