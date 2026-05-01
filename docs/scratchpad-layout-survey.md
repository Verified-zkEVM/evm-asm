# Scratchpad-Layout Survey (Issue #334)

This document catalogues every `sp`-relative scratchpad cell currently baked
into specs/programs as a hardcoded `signExtend12 N` literal. It is the
input for issue #334 ("make scratchpad locations variable"): the layout
abstraction (slice 2) and per-routine parameterizations (slices 3–4) need
to know which cells exist, what role each plays, and which routines touch
them.

Scope: docs only — no code changes. Generated from a static scan
(`grep -rE 'sp [+-] signExtend12 [0-9]+' EvmAsm/`) plus a manual reading
of the precondition/postcondition bundles in `EvmAsm/Evm64/DivMod/LoopDefs/`.

Beads: evm-asm-l9g1 (slice 1 of evm-asm-4mka / GH #334).

## 1. Files containing `sp ± signExtend12 N` literals

94 files total under `EvmAsm/`:

| Subtree                  | Files |
|--------------------------|-------|
| `EvmAsm/Evm64/DivMod`    | 91    |
| `EvmAsm/Evm64/Byte`      |  1    |
| `EvmAsm/Evm64/Shift`     |  1    |
| `EvmAsm/Evm64/SignExtend`|  1    |
| `EvmAsm/Rv64`            |  0    |

DivMod dominates the survey. Multiply (`EvmAsm/Evm64/Multiply/`) does not
appear because, at the time of writing, its specs are written against
caller-supplied register pointers (`.x12 ↦ᵣ ptr`) rather than baked-in
`sp + signExtend12 N` cells — Multiply already satisfies the spirit of
#334. SignExtend / Shift use only the single low slot `sp + signExtend12 32`
as a working-limb pointer.

## 2. Distinct offsets observed

Only these literal offsets occur in the codebase today:

```
0, 8, 16, 24, 32, 40, 48, 56,
3936, 3944, 3952, 3960, 3968, 3976, 3984, 3992,
4000, 4008, 4016, 4024, 4032, 4040, 4048, 4056,
4064, 4072, 4080, 4088
```

Notes
- All offsets are 8-byte aligned.
- Values ≥ 3936 are big-endian in role (low addresses of the caller frame's
  saved area); values 0..56 are the low scratchpad block close to `sp`.
- Because `signExtend12` of values ≥ 2048 sign-extends to a *negative*
  offset, e.g. `signExtend12 4088` = `-8`, the high-numbered slots are
  reachable as `sp - 8`, `sp - 16`, etc. The proofs use the
  `+ signExtend12 4088`/`+ signExtend12 4080` form (rather than `sp - 8`)
  so that `bv_addr` and the `divmod_addr` grindset can fold them
  uniformly. Slice 2 should pick a side (probably `sp - k` with a
  `divmod_addr`-friendly normalization lemma) and stick to it.

## 3. Roles (DivMod, the hot subtree)

The DivMod loop maintains a Knuth-D-style running quotient `q[0..3]` and
remainder `u[0..4]` over four 64-bit limbs, plus a small set of
loop-control / call-path scratch cells. The j-indexed cells live in two
moving windows anchored at `sp + signExtend12 4056` (u-base) and
`sp + signExtend12 4088` (q-base):

```
u_base(j)  := sp + signExtend12 4056 - j * 8
q_addr(j)  := sp + signExtend12 4088 - j * 8
```

Cell map (j=0; subtract `j*8` for higher j-iterations):

| Offset (`sp + signExtend12 …`) | Role                                         | Source of role                        |
|--------------------------------|----------------------------------------------|---------------------------------------|
| 32                             | `v[0]` (divisor limb 0, normalized)          | `LoopDefs/Bundle.lean` line 45        |
| 40                             | `v[1]`                                       | `LoopDefs/Bundle.lean` line 46        |
| 48                             | `v[2]`                                       | `LoopDefs/Bundle.lean` line 47        |
| 56                             | `v[3]`                                       | `LoopDefs/Bundle.lean` line 48        |
| 4024  (= `u_base(0)+4064`)     | `u_top` / `u[4]` (overflow limb)             | `LoopComposeN1.lean` line 150         |
| 4032  (= `u_base(0)+4072`)     | `u[3]` at j=0 / `u_top` at j=1               | `LoopComposeN1.lean` lines 53, 84, 115|
| 4040  (= `u_base(0)+4080`)     | `u[2]`                                       | `LoopDefs/Bundle.lean` line 47        |
| 4048  (= `u_base(0)+4088`)     | `u[1]`                                       | `LoopDefs/Bundle.lean` line 46        |
| 4056                           | `u[0]` (u-base anchor)                       | `LoopDefs/Bundle.lean` line 45        |
| 4064  (= `q_addr(0)+4072`)     | `q[3]`                                       | `LoopComposeN2.lean` line 83          |
| 4072                           | `q[2]`                                       | `LoopComposeN2.lean` line 82          |
| 4080                           | `q[1]`                                       | `LoopComposeN2.lean` line 81          |
| 4088                           | `q[0]` (q-base anchor)                       | `LoopComposeN2.lean` line 80 / 73     |
| 3936                           | extra call-path scratch (Div128V4 only)      | `Compose/Div128V4.lean`               |
| 3944                           | `scratch_un0` (saved `un[0]` across calls)   | `LoopDefs/Bundle.lean` line 70        |
| 3952                           | `dloMem` (low limb of normalized divisor)    | `LoopDefs/Bundle.lean` line 69        |
| 3960                           | `dMem`   (saved divisor word)                | `LoopDefs/Bundle.lean` line 68        |
| 3968                           | `retMem` (return slot for div128 sub-call)   | `LoopDefs/Bundle.lean` line 67        |
| 3976                           | `jOld`   (saved loop counter `j`)            | `LoopDefs/Bundle.lean` line 44        |
| 3984                           | `n`      (active divisor-limb count, 1/2/3/4)| `LoopDefs/Bundle.lean` line 44        |
| 3992                           | epilogue/FullPath frame slot (caller-saved)  | `Compose/Epilogue.lean`               |
| 4000..4016                     | caller-saved register / staging slots used by Phase B and the epilogue load phase | `Compose/FullPath.lean`, `Compose/Epilogue.lean` |

The "roving" j-indexed slots overlap intentionally:
- `u_base(0)+4072` and `u_base(1)+4064` both denote `sp+4032`, i.e. iteration j's
  `u[3]` is the next iteration's `u_top`. The chain of equalities at
  `LoopComposeN1.lean` lines 53/84/115 is exactly what threads one
  iteration's output into the next iteration's input. Any layout
  abstraction must preserve this aliasing.

## 4. Roles (Byte, Shift, SignExtend)

Independent of DivMod, three other routines use a small fixed scratchpad
near `sp`:

| File                                     | Offsets used                  | Role                                                                 |
|------------------------------------------|-------------------------------|----------------------------------------------------------------------|
| `EvmAsm/Evm64/Byte/LimbSpec.lean`        | 0, 8, 16, 24, 32, 40, 48, 56  | `idx0..idx3` (byte-index inputs at 0/8/16/24); 32-byte result limb scratch (limbs at 32/40/48/56) used by `BYTE`. The `sd_x0_*` calls at lines 217–248 zero this 32-byte block. |
| `EvmAsm/Evm64/Shift/LimbSpec.lean`       | 32                            | `(.x12 ↦ᵣ sp + signExtend12 32)` — pointer to the working-limb scratch consumed by the shift LimbSpec. |
| `EvmAsm/Evm64/SignExtend/Compose.lean`   | 32                            | Same pointer convention as Shift — `.x12` carries `sp + signExtend12 32` into the SignExtend body. |

Byte's 0..56 block is **disjoint in role** from DivMod's 32..56 v[]-block:
no current top-level program runs Byte interleaved with DivMod, so the
overlap is benign today but is the single most fragile point if a future
caller wants to compose them. Slice 2's abstraction must let Byte and
DivMod each name their own block, not share these eight low slots by
accident.

## 5. Existing partial abstractions to build on

The codebase already has *some* named-offset infrastructure, but for
program-counter offsets, not scratchpad addresses:

- `EvmAsm/Evm64/DivMod/Spec/Base.lean` defines `clzOff`, `phaseC2Off`,
  `addbackBeqOff`, `storeLoopOff`, `denormOff`, `loopBodyOff`,
  `div128Off`, `div128CallRetOff` — these name **code** addresses (e.g.
  `base + addbackBeqOff`), not scratch addresses.
- `EvmAsm/Evm64/DivMod/AddrNorm.lean` registers the `divmod_addr`
  grindset that closes equalities like `(base + 728) + 156 = base + storeLoopOff`.
- `EvmAsm/Evm64/Multiply` uses register-pointer parameters (no `sp +
  signExtend12 N` at all), so it is the model the DivMod
  parameterization should converge toward.

What is **missing** for #334:
- A `DivModScratchLayout` struct (suggested fields: `vBaseOff`, `uBaseOff`,
  `qBaseOff`, `retOff`, `dOff`, `dloOff`, `un0Off`, `jOff`, `nOff`,
  `frameOff`) with proved `Disjoint` and validity (`isValidAddr`)
  obligations bundled.
- An analogous `ByteScratchLayout` (probably trivial: one base + the
  fixed 0..56 sub-layout).
- A small set of address-equality lemmas — analogous to those in
  `AddrNorm.lean` — proved generically over a layout struct so the
  current `bv_addr` consumers continue to work after parameterization.

## 6. Slice-2 inputs

For the design note (slice 2, evm-asm-86d1), the catalogue above gives:

- 26 distinct concrete offsets in DivMod, collapsing to ~10 named roles
  (v-base, u-base/u-anchor, q-base/q-anchor, retMem, dMem, dloMem,
  un0-scratch, jOld, n, frame-save block).
- Two cross-iteration aliasing constraints (u[3]@j ≡ u_top@(j-1), and the
  `q_addr`/`u_base` arithmetic identities used by the
  `divmod_addr`-grindset proofs).
- 91 files to migrate in DivMod, plus the three Byte/Shift/SignExtend
  files. The pilot in slice 3 is `Multiply` (already parameterized);
  slice 4 broadens to DivMod / Shift; SignExtend and Byte are likely
  cheap follow-ons because they each touch a single layout group.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
