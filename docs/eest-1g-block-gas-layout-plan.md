# EEST 1G Block-Gas Layout Plan

> **SUPERSEDED (2026-06-11): the static layout is right-sized to the 200M
> Amsterdam block-gas target.** The 1G sizing below was implemented (PR #8089)
> but cost ~416 MiB of the fixed 512 MiB ziskemu RAM window and forced the
> call-frame arena into the #8513 `basr_values`+`basr_accounts` union. Amsterdam
> aims at 200,000,000 gas, so `bsrMaxBalItems` is now **100,000**
> (= 200M / 2000), the BAL arenas shrink to ~83 MiB, and `call_frame_arena` is a
> standalone ~164 MiB block (the union and its execution-dead soundness gate are
> retired). Blocks declaring more than 200M gas still launch; if their actual
> BAL/state-change counts exceed the 100,018-row caps they take the conservative
> `bsr_fail` path. The sizing *mechanics* below remain the reference; only the
> 500,000-item column is obsolete.

This is the implementation plan for bead
`evm-asm-fhsxz.2.4.2.57.9.1.1`. It replaces the PR #8044 direction of
classifying high-gas EIP-8037 fixtures as `ERROR(layout)`: the desired behavior
is to make those fixtures launch and expose semantic verdict failures or passes.

## Target

The full EEST log at `/tmp/eest-all-2026-06-03.txt` shows
`ERROR(layout)` for EIP-8037 `state_gas_pricing` fixtures at these block gas
limits:

- 200,000,000
- 300,000,000
- 500,000,000
- 1,000,000,000

Use 1,000,000,000 as the static arena sizing target. Amsterdam BAL validation is
gas-derived:

```text
bal_items <= block_gas_limit / 2000
```

So the target BAL arena capacity is 500,000 items. `block_state_root` also starts with
two modeled system changes, so any top-level change-count cap must cover at
least 500,002 rows.

This 1G target is not a launch-time maximum block gas limit. Later EEST
fixtures can declare much larger gas limits while consuming small actual
resources; those fixtures should launch. The guest enforces the gas-derived BAL
rule and the actual arena capacities at runtime.

## Current Blocker

Current `BlockVerdict.lean` guards are sized for the execution-specs default
120,000,000 block gas limit:

```asm
li t0, 120000000; bgtu a0, t0, .Lbsr_cons_change_cap
...
add t0, s1, t6; li t1, 60018; bgtu t0, t1, .Lbsr_cons_change_cap
```

The EEST shell harness mirrors this with
`EEST_BSR_MAX_BLOCK_GAS_LIMIT=120000000`, so the 1G cases currently fail before
ziskemu launches.

## Static Sizing

For a direct 1G static layout, scale every arena indexed by `bsr_bal_count` or
state-change count together. Do not only raise the gas guard.

| Arena | Current bytes | Current capacity | 1G capacity | 1G bytes |
| --- | ---: | ---: | ---: | ---: |
| `basr_records` | 1,440,432 | 60,018 * 24 | 500,002 | 12,000,048 |
| `basr_paths` | 3,841,152 | 60,018 * 64 | 500,002 | 32,000,128 |
| `basr_values` | 15,364,608 | 60,018 * 256 | 500,002 | 128,000,512 |
| `basr_accounts` | 15,364,608 | 60,018 * 256 | 500,002 | 128,000,512 |

The per-account storage replay arrays in `BlockVerdict.lean` also need scaling
for the opposite BAL shape: one or a few accounts with many storage keys. Their
current hard caps are effectively 60,000 storage paths/values and 100,000
storage descriptors:

| Arena | Current bytes | Current capacity | Minimum 1G capacity | Minimum 1G bytes |
| --- | ---: | ---: | ---: | ---: |
| `baap_storage_desc` | 2,400,000 | 60,000 * 40 | 500,000 | 20,000,000 |
| `baap_storage_paths` | 3,840,000 | 60,000 * 64 | 500,000 | 32,000,000 |
| `baap_storage_delete_paths` | 3,840,000 | 60,000 * 64 | 500,000 | 32,000,000 |
| `baap_storage_values` | 3,840,000 | 60,000 * 64 | 500,000 | 32,000,000 |

`BalAccountApplyPostFields.lean` has matching hard-coded `60000` guards for
storage-output and deletion counts. The `BlockVerdict.lean` embedded copy must
be kept consistent with those guards if the implementation remains static.

The straightforward static increase adds about 344 MiB over the current BSR/BAL
arena sizes before unrelated `.data` objects.

## Memory Map

The current stateless layout is:

```text
0xa0010000 .. 0xa0020000   OUTPUT_ADDR
0xa0020000 .. 0xa5000000   working RAM
0xa5000000 .. 0xb0000000   .data
0xb0000000 .. 0xb2000000   .sszscratch
0xb2000000 .. 0xc0000000   remaining verified RAM headroom
```

A direct 1G static layout does not fit comfortably in the current
`0xa5000000..0xb0000000` `.data` window, and it must not collide with
`.sszscratch`. The implementation should move `.sszscratch` upward and enlarge
or relocate `.data` while staying inside verified RAM `0xa0000000..0xc0000000`.

Implemented static map:

```text
0xa0010000 .. 0xa0020000   OUTPUT_ADDR
0xa0020000 .. 0xa3000000   working RAM, unchanged fixed anchors plus headroom
0xa3000000 .. 0xbf500000   .data, enough for 1G BSR/BAL static arenas
0xbf500000 .. 0xbfb80000   .sszscratch, 6.5 MiB NOBITS
0xbfb80000 .. 0xc0000000   guard/headroom
```

This keeps all regions in the existing verified RAM range and preserves a gap
between the documented working-RAM anchors and `.data`, and between `.data` and
`.sszscratch`. Update all linker invocations together:

- `EvmAsm/Codegen/Driver.lean`
- `scripts/codegen-eest-stateless-check.sh`
- `scripts/codegen-zisk-stateless-verdict-check.sh`
- `EvmAsm/Stateless/MemoryLayout.lean`
- any docs that spell out the stateless memory map

## Implementation Checklist

Implementation status: the direct static layout is the current path. The code
derives `BlockVerdict.lean` arena sizes from named constants and moves
`.sszscratch` to `0xbf500000`. The EEST harness no longer has a blanket
pre-launch gas cap; instead, the guest checks Amsterdam's gas-derived BAL rule
and the actual arena capacities at runtime. The old values in the "Current
Blocker" section are historical evidence for why PR #8044's `ERROR(layout)`
behavior was not the desired endpoint.

The implementation address is higher than the initial recommendation because
the full linked `.data` segment with all existing stateless tables plus the 1G
BSR/BAL arenas reaches about `0xbf4398ef`; the actual `.sszscratch` reservation
is 6.5 MiB, so `0xbf500000..0xbfb80000` fits inside verified RAM. Dense
`bsr_paths`/`bsr_newaccts` arrays indexed by the global state-change counter do
not fit: BAL descriptors already point into `basr_paths`/`basr_accounts`, so the
implemented layout keeps `bsr_paths`/`bsr_newaccts` compact for the two modeled
system rows plus the 16 withdrawal rows and records those pointers in the dense
`bsr_changes` descriptor array.

1. Introduce named layout constants in `BlockVerdict.lean` before changing
   assembly strings, at least:
   - `bsrBalItemGasCost = 2000`
   - `bsrMaxBalItems = 500000`
   - `bsrMaxStateChanges = 500018`
2. Replace hard-coded `120000000`, `60018`, and `60000` values in the BSR/BAL
   path with values derived from those constants.
3. Resize all `basr_*` and `baap_storage_*` static arenas consistently.
4. Move `.sszscratch` to the selected high address and update
   `SSZ_SCRATCH_BASE` docs/constants.
5. Remove the EEST harness blanket gas-limit prefilter and update
   `patch_bsr_caps_asm` so experimental BAL caps still patch the new runtime
   resource check.
6. Replace the PR #8044 regression with a launch-coverage test: the high-gas
   EIP-8037 fixtures should run ziskemu and produce semantic pass/fail output,
   not `ERROR(layout)`.
7. Run focused EEST with `--filter eip8037_state_creation_gas_cost_increase`
   and an explicit `--max-failures` to capture the next semantic blockers.

## Static vs Streaming

A streaming/chunked replay design would be better long-term because memory would
scale with actual fixture contents instead of worst-case gas. However, the next
implementation PR can be a larger static layout if it keeps the ELF map disjoint
and documents the supported maximum as 1G. Do not keep the pre-launch layout
error for these observed EEST gas limits.
