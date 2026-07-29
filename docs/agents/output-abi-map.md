# Output-area map by build unit

The output address (`0xa0010000`) is not a single ABI.  Claims on offsets are
meaningful only with the build unit that emits them.  In particular, a bare
"highest output offset" is not an allocation boundary.

This map was made by walking every output-base writer in the emitted
`stateless_guest` assembly, then checking the separate
`zisk_stateless_verdict_v2` probe prologue in source.  A *claimed* range means
that some reachable writer in the unit may write it; a conditional writer still
claims its slot.

## `stateless_guest` (production and census unit)

| Range | Writer / role | Lifetime |
| --- | --- | --- |
| `0..111` | SSZ validation result, including the success byte at `32`; default-failure copy also writes this prefix. | Final output. |
| `0..255` | Runtime dispatcher exits (`RETURN`, `REVERT`, exceptional exits) use result fields and return-data slots, including length at `248`. | Transient during `stateless_verdict_v2`; the epilogue saves and restores `0..111` but does not reserve this as a diagnostic-only range. |
| `112..191` | Verdict, shadow-BAL, and storage-read diagnostics. | Final diagnostic output. |
| `192..248`, `256` | Producer-side BAL diagnostic cells.  `248` is contended with runtime return-data length, so the eighth cell is deliberately at `256`. | Final diagnostic output. |
| `264..343` | BAL witness cells. | Final diagnostic output. |
| `472..487` | `block_verdict_creation_runtime` stores at `472` and `480`. | Linked writer; may survive the verdict call. |

The highest claimed offset in `stateless_guest` is therefore **487** (the
eight-byte store at `480`), even though its post-verdict diagnostic block ends
at **343**.  The output census and locality instrumentation use this build
unit, so a new census slot must be allocated above `487`, not from a ceiling
reported by another unit.

## `zisk_stateless_verdict_v2` (standalone verdict-debug probe)

`ziskStatelessVerdictV2Prologue` writes 8-byte debug cells beginning at offset
`0` and continuing through the store at `1120`.  Thus this ABI claims
**`0..1127`**.  It also calls the verdict/runtime code, whose output writers
are contained below that ceiling.

The highest claimed offset for this probe ABI is **1127**.

## Allocation rule

The two ABI maps overlap completely through `487`.  A slot above `343` is safe
only from the production post-verdict diagnostics; it is not automatically safe
from all production writers.  A slot above `487` is safe for the production
census unit.  A slot above `1127` is safe for both units.  Choose the boundary
for the unit actually being run, and state that unit together with every
`SPIKE_OUTPUT_LEN` claim.
