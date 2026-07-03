# Guest-wide misaligned wide-access audit

Bead: [`evm-asm-4ch8f.7`](https://github.com/Verified-zkEVM/evm-asm/issues)
(P0 plan under epic `evm-asm-4ch8f`, verify-guest).
Related: `evm-asm-iwzun` (SSZ decode LWU/LD trap) and `evm-asm-4ch8f.27`
(SSZ input extractors).

## Why this matters

The verified RV64 semantics **traps** on a misaligned wide memory access:
`isValidMemAccess` / `isValidDwordAccess` require `isAligned4` / `isAligned8`
(`EvmAsm/Rv64/Basic.lean:299-311`), so a `lw`/`lwu`/`ld`/`sw`/`sd`/`flw`/
`fld`/`fsw`/`fsd` to an address that is not 4- or 8-byte aligned makes `step`
return `none`. ziskemu, by contrast, tolerates misaligned access, so a routine
can pass EEST on the emulator yet be **unverifiable as emitted**: its triple
cannot be proved because the model has no successor state for the trapping step.

The SSZ container starts at `INPUT_BASE + 18` (16-byte ziskemu preamble +
2-byte schema id) = `0x40000012`, which is **2 mod 4**. Any wide load at an even
byte offset off that base lands on a `2 mod 4` (or `2/6 mod 8`) address.

## Method

`scripts/audit-misaligned-access.py` runs a per-routine, straight-line
abstract interpretation over the emitted `.s`. Register values are tracked in
the abstract domain

| tag | meaning |
|-----|---------|
| `('const', n)` | statically-known 64-bit value `n` |
| `('input', off, exact)` | `INPUT_BASE + off`; `exact=False` once `off` picks up a data-dependent term (a value read from memory) |
| `None` | untracked (arg register, spilled value, clobbered across a label) |

Transfer functions cover `li`/`lui`/`addi`/`add` (constant folding + INPUT-region
tagging); every other instruction clobbers its destination. Register knowledge
is **reset at every label** — control-flow joins could deliver any value, so we
never propagate a constant across a basic-block boundary. This makes the
analysis sound for the CONFIRMED bucket (a CONFIRMED requires a fully-known
constant address reached along one straight-line path) at the cost of
under-reporting inside called routines.

Each wide access is classified:

- **CONFIRMED** — effective address statically known **and misaligned** for its
  width. A hard model trap.
- **ALIGNED** — statically known and correctly aligned (not reported).
- **INPUT_DEP** — base provably in the INPUT region but offset data-dependent;
  alignment is input-controlled, so it can still trap. These are the SSZ/RLP
  offset-table cursor chases.
- **UNKNOWN** — base not statically tracked (sp-relative frame slots, heap
  pointers, callee arguments). Not reported (see *Coverage / blind spot*).

Reproduce (regenerate the asm first — the checked-in `gen-out/*.s` are
git-ignored artifacts and can be stale):

```
lake exe codegen --program stateless_guest    --halt linux93 -o gen-out/stateless_guest    --asm-only
lake exe codegen --program runtime_dispatcher --halt linux93 -o gen-out/runtime_dispatcher --asm-only
python3 scripts/audit-misaligned-access.py gen-out/stateless_guest.s gen-out/runtime_dispatcher.s
```

## Findings (as of `origin/main`, this audit)

| target | total wide ops | CONFIRMED traps | INPUT_DEP | routines with traps |
|--------|---------------:|----------------:|----------:|---------------------|
| `stateless_guest.s`   | 19 748 | **57** | 2 | `_start` only |
| `runtime_dispatcher.s`|  8 143 |  **0** | 1 | — |

**The confirmed traps are concentrated entirely in the `_start` SSZ
input-extraction prologue** — not spread across the guest:

- 54 of 57 are `ld`/`lwu` off `s6`, where `s6 = INPUT_BASE + 18 = 0x40000012`
  (the SSZ ExecutionPayload container base). Offsets are fixed byte positions of
  SSZ fields, so every address is `2 mod 4` (`ld`: 37 at `2 mod 8`, 16 at
  `6 mod 8`; `lwu`: 4 at `2 mod 4`).
- 3 of 57 are early `lwu` off `x17` (also `base+18`), reading the outer offset
  table (`0x40000016`, `0x4000001a`, `0x4000001e`) — exactly the case cited in
  `evm-asm-iwzun` (`read_chain_id`'s `lwu …,8(x12) -> 0x4000001a`).
- The 2 INPUT_DEP loads are the pointer-chase after an offset-table read
  (`lwu 8(x22)`, `lwu 0(x21)` off input-derived pointers); their alignment
  depends on the offset value in the input and so can also trap.

The **runtime dispatcher / EVM interpreter has zero statically-confirmed
traps** (its 1 INPUT_DEP is the same input-preamble read). Its 8 143 wide ops
are dominated by `sp`- and heap-pointer-relative accesses (frame slots and RAM
scratch), which are aligned by construction.

Root cause is singular and layout-driven: **the SSZ container base is
`2 mod 4`, and the emitter reads SSZ fields with wide `ld`/`lwu` at even
offsets.** There is no second, unrelated family of misalignment elsewhere in
the emitted guest.

## Coverage / blind spot

The analysis is intra-procedural and resets at labels, so it classifies only
accesses whose base alignment is statically determinable — essentially the
inlined `_start` prologue. The ~20 k `UNKNOWN` wide ops fall into two groups:

1. **`sp`-relative frame slots and RAM scratch** (the large majority, incl. the
   6 472 `sp`-relative ops): aligned by construction — the stack pointer is kept
   8-aligned and frame offsets are multiples of 8. Not a concern.
2. **Cursor loads inside called routines** (`lwu off(a0)`, `ld off(a1)`, …
   where the pointer arrives as an argument): the SSZ/RLP decode helpers
   (`rlp_*`, `ssz_*`, `header_*`, `tx_*`, `mpt_*`) read wide off a cursor whose
   alignment is the **caller's** obligation. Static intra-procedural analysis
   cannot see this. These are **deferred to per-routine verification**: when a
   routine is ported to an SAsm triple, its precondition states the alignment of
   its pointer arguments, and the wide-load steps are discharged (or the routine
   is rewritten byte-wise) at that point. This is precisely the per-family work
   already carved out by `evm-asm-4ch8f.12`..`.38`; no separate blanket bead is
   warranted, because the trap only fires when the caller passes an unaligned
   (e.g. SSZ-`2 mod 4`) pointer, which the callee's spec makes explicit.

## Remediation

All confirmed traps share one fix surface — the SSZ read path in the emitter.
Three options (from `evm-asm-iwzun`), in preference order:

1. **Byte-assemble the SSZ field reads** (`lbu` + shift/or), matching the
   already-verified SAsm ports. Local to the emitter, keeps the `2 mod 4`
   layout, and every step stays aligned (single-byte loads are always valid).
   Recommended for the fixed-offset `s6`/`x17` reads and the offset-table
   `lwu`s.
2. **Aligned staging**: `memcpy` the SSZ container into an 8-aligned RAM buffer
   once, then read wide from there. Fewer instructions per field but adds a copy
   and a scratch region; useful if many fields are read.
3. **Realign the input layout** so the SSZ container starts 8-aligned. This is
   controlled by the ziskemu preamble / schema-id width and is likely not ours
   to change; treat as out of scope unless the host contract can be revised.

## Filed follow-ups

The confirmed traps live in the `_start` SSZ extraction prologue, which is the
emitted image of the SSZ input extractors already tracked by
**`evm-asm-4ch8f.27`** and the decode-trap bug **`evm-asm-iwzun`**. Rather than
open a duplicate per-instruction bead, this audit's remediation (byte-assemble
option 1) is attached to those beads as the concrete fix, with this document as
the classified inventory. The INPUT_DEP pointer-chase reads are part of the same
extraction path and covered by the same fix.
