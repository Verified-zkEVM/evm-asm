# 12894 pilot: `rlp_walk_init` positive control

This is the first bounded reachability pilot for issue 12894.  It is an
instrumentation result, not a claim that the invalid-block corpus exercises the
target check.  The valid/invalid split was produced before any guest run.

## Provenance

- `repo_head`: `0e56df67085307dad73633ab28cb9049de818a7e`
- `repo_base`: `d9c90f0e38d174bb8894c13f39833aa155250be9`
- `fixture_tag`: `tests-zkevm@v0.6.2` (repo tag/corpus provenance is
  `r20260810-2`; this is not an upstream execution-specs release tag)
- `guest_elf_sha256`:
  `8618ff3dbc0183563a1f00dbc2bed277e8376baef77150182db564a2e0084739`
- backend: custom `scripts/spike/spike_run`
- target symbol/address from the fresh linked ELF: `rlp_walk_init` at
  `0x80004c18`
- deterministic sample: seed `12894`, 200 rows, 100 valid and 100 invalid

## Instrument and matching rule

Each row first ran with `SPIKE_BREAK_PC=0x80004c18`.  A reached row was rerun
with `SPIKE_DEBUG_CMD`: stop at the same entry, read the actual `ra`, then stop
at that literal return address before running to the halt flag.  This is an
entry/return-address check against the linked image, not a source or TSV
assumption.  `rlp_walk_init` is a leaf (the disassembly contains no call in its
212-byte body), so the entry and return observations retain the same `sp`; the
pilot records that as `leaf-sp-unchanged` rather than inventing a dynamic call
depth.

## Result

| population | rows | entry reached | exact return matched | completed |
|---|---:|---:|---:|---:|
| valid | 100 | 100 | 100 | 100 |
| invalid | 100 | 99 | 99 | 100 |
| total | 200 | 199 | 199 | 200 |

The sole non-reached row is invalid case `02246_test_invalid_stateless_input_bytes_are_rejected...` (unsupported-schema stateless-input rejection).  It is recorded as
`target_reached=0`, not as a failed predicate.  No reached row had a mismatched
return address, and no runner/backend disagreement was observed.  The complete
row-level observation is emitted as `reachability-observation-v1` by
`scripts/reachability_pilot.py`; the generated sample, inputs, ELF and logs are
kept outside the repository under `/tmp/12894-pilot-artifacts`.

## What “~192 calls” means

The `calls 193` note in `docs/4ch8f-transcription-queue.md` is a **static source
demand count**, produced by `scripts/transcription_queue.py`'s textual call-site
patterns.  It was `192` before commit `78bb5aa56`; that commit added one
`jalOff` citation and therefore changed the source count to `193`.  It is not a
runtime invocation count.  On this fresh ELF, `objdump` finds 60 direct `jal`
instructions targeting `0x80004c18`; the pilot's 199 figure is rows reaching at
least one invocation (the harness intentionally records the first invocation
per row), not 199 calls.

## Coverage boundary

This positive control validates manifest-to-PC mapping and return matching.  It
does not turn the 1,036 invalid rows into target-check coverage: the corpus
split remains 25,068 valid / 1,036 invalid, and invalid-path conclusions must
use the denominator of invalid rows that actually reach the target.  A future
instrumented condition report should therefore retain the separate valid and
invalid denominators and report zero-reached invalid conditions as
corpus-limited rather than safe.
