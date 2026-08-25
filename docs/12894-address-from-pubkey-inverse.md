# 12894 inverse probe: `address_from_pubkey`'s scratch precondition

This is the inverse companion to the `rlp_walk_init` positive control.  It
tests a stateful precondition of a `.proven` registry row rather than treating
entry reachability as proof that every call satisfies the row.

## Provenance

- codegen ref for the linked image: `0e56df67085307dad73633ab28cb9049de818a7e`
- branch carrying the instruments: `4dc00e176c7e379c39ee5bd17e008cedc58836bd`
- guest ELF SHA-256:
  `8618ff3dbc0183563a1f00dbc2bed277e8376baef77150182db564a2e0084739`
- backend: `/tmp/12894-pilot/scripts/spike/spike_run`
- deterministic sample: seed `12894`, 200 rows, 100 valid and 100 invalid

The sample was split before instrumentation.  The generated TSVs and runner
logs are under `/tmp/12894-pilot-artifacts` and are intentionally not source
or generated-guest files.

## Why this is an inverse case

The registry calls `address_from_pubkey` `.proven` at
`EvmAsm/Progress/Routines.lean:3501-3514`, but its actual whole-routine theorem
is not total over arbitrary machine states.  The caller precondition at
`EvmAsm/Codegen/Programs/AddressFromPubkeySpec.lean:1352-1363` contains

```
bytesRegion afpDigestPtr (List.replicate 32 0)
```

and `addressFromPubkey_spec_within` carries that precondition through the
whole-routine triple at `:1418-1448`.  The body invokes `zkvm_keccak256` at
`:105-123` and never clears `afp_digest`; the source documentation therefore
states that the zero scratch is satisfied by the first call only.  This is a
state/cursor-like contract premise, not merely an ABI alignment fact.

The fresh linked ELF confirms the same shape.  `nm` resolves
`address_from_pubkey` to `0x8002ae80` and `afp_digest` to `0xaa8453a0`.
The linked body at `0x8002ae9c` calls `zkvm_keccak256` with `a2 = 0xaa8453a0`,
then copies from that buffer; there is no zeroing store in the body.

## Instrument and self-check

The first pass reused `scripts/reachability_pilot.py` with
`SPIKE_BREAK_PC=0x8002ae80`.  Each reached row was rerun with the literal `ra`
observed at the entry and had to stop at that return PC; the leaf `sp` check was
retained.  The inverse pass (`scripts/reachability_inverse.py`) then reused
that observed first `ra`, read the eight-byte cell at `0xaa8453a0` at the first
entry, stopped at the first return, and looked for a second entry before halt.
It read the same cell at that second entry.  Thus the second measurement is
not a guessed callsite or a source-level count.

## Result

| population | rows | first entry reached | first return matched | second entry | second cell nonzero |
|---|---:|---:|---:|---:|---:|
| valid | 100 | 94 | 94 | 94 | 94 |
| invalid | 100 | 20 | 20 | 20 | 20 |
| total | 200 | 114 | 114 | 114 | 114 |

For every one of the 114 reached rows, the first-entry cell was exactly zero
(`0x0000000000000000`), while a second `address_from_pubkey` entry occurred
and the cell was nonzero.  Every inverse debug run completed with return code
0.  The 86 rows with no first entry are not evidence that the precondition is
false; they simply never reached this routine in this sample.

As an independent spot check, a commit log for one reached row contains eight
entries at `0x8002ae80`; the first-entry/second-entry probe already suffices for
the precondition result and avoids making commit logs for the full sample.

## Interpretation

The `.proven` theorem's zero-scratch premise is reachable for the first call in
a fresh guest, but it is **not a per-call invariant**: every reached row in this
sample calls the routine again after the first keccak write, with nonzero
`afp_digest`.  This is therefore a precondition-coverage finding, not a claim
that the routine is unreachable and not a claim that the first call is unsafe.
The contract can be applied soundly only when a caller proves it owns a fresh,
zeroed digest cell (or after the keccak contract is generalized over arbitrary
initial output bytes, as the source note already suggests).
