# MSTORE opcode design (GH issue #99 slice 4, beads slice evm-asm-j6vh)

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

This document plans the implementation of the EVM `MSTORE` opcode
(`MSTORE(offset, value)` writes `value` as a big-endian 256-bit word
into 32 bytes of EVM memory starting at `offset`). It is the
deliverable of the pre-slice of `evm-asm-j432` / GH #99 slice 4, and is
referenced by the subsequent Program / spec slices.

It mirrors the MLOAD design — the byte-shuffling
direction is reversed (limb→memory instead of memory→limb), and the
RV64IM kernel uses `SB` (verified by `generic_sb_spec_within` already
exercised in MSTORE8) instead of `LBU`. Structure, slice plan, and
proof tier-decomposition stay the same.

No code changes; this slice is documentation only. The Program and spec
land in follow-up slices per §6 below.

## 1. EVM semantics — what `MSTORE` does

Per the yellow paper §H.1 and `execution-specs/.../vm/instructions/memory.py`:

```
def mstore(evm):
    pop offset (256-bit, treated as Nat)
    pop value  (256-bit)
    expand active memory to (size := max(size, ceil((offset+32)/32) * 32))
    mem[offset .. offset + 31] := value as big-endian 32 bytes
```

Edge cases:

- `offset = 0`: writes to bytes `[0, 32)`; expands `size` to 32.
- `offset = 31`: writes to bytes `[31, 63)`, straddling two 32-byte
  words; expands `size` to 64.
- `offset = 2^256 - 1`: out-of-gas in real EVM; in the verified evm-asm
  setting we will assume `offset` fits in `Word` (64 bits) — the higher
  3 limbs of the EVM offset must be zero, which is a precondition (see
  §3.5). Same convention as MLOAD.

Stack effect: `[..., offset, value] -> [...]` (two pops, no push). Net
`x12` advance is `+64` (two 32-byte pops).

## 2. Stack layout (LP64 + EVM-stack convention)

Using the same convention as MSTORE8 / MLOAD (cf. `Evm64/MStore8/Program.lean`,
`Evm64/MLoad/Program.lean`):

- `x12 = sp_evm` (EVM stack pointer, grows down).
- On entry, the top-of-stack is `offset` at `sp_evm + 0 .. sp_evm + 24`
  (4 LE limbs, low limb at `sp_evm`); `value` is just below at
  `sp_evm + 32 .. sp_evm + 56` (4 LE limbs, low limb at `sp_evm + 32`).
- On exit, `x12 = sp_evm + 64` (both 32-byte words popped). The 64
  bytes at `[sp_evm, sp_evm + 64)` are scratch from the caller's
  perspective (separation-logic frame).

Net `x12` advance is `+64`.

## 3. RISC-V byte-assembly recipe

EVM memory is byte-addressable (per yellow paper). RV64IM memory is
dword-addressable but `Rv64/ByteOps.lean` already lifts byte operations
on top via `extractByte` / `replaceByte` and the verified
`generic_sb_spec_within` (SB, byte-store). MSTORE8 already uses SB this
way for one byte; MSTORE drives 32 of them.

### 3.1. High-level structure (4 EVM-stack-limbs, 8 bytes each)

The 256-bit big-endian EVM value at byte offsets `[offset .. offset+31]`
maps to the 4 little-endian 64-bit limbs `lo .. hi` exactly as in MLOAD:

```
  byte    EVM big-endian role         RISC-V LE limb position
  ----    ----------------------       ------------------------
  off+ 0  most-significant byte (b31)  hi   limb (sp+24+32), byte 7 (high)
  off+ 1  b30                          hi   limb (sp+24+32), byte 6
  ...
  off+ 7  b24                          hi   limb (sp+24+32), byte 0 (low)
  off+ 8  b23                          mh   limb (sp+16+32), byte 7
  ...
  off+15  b16                          mh   limb (sp+16+32), byte 0
  off+16  b15                          ml   limb (sp+ 8+32), byte 7
  ...
  off+23  b 8                          ml   limb (sp+ 8+32), byte 0
  off+24  b 7                          lo   limb (sp+ 0+32), byte 7
  ...
  off+31  b 0                          lo   limb (sp+ 0+32), byte 0
```

Same byte→limb rule as MLOAD: byte `off + k` (for `k = 0 .. 31`) goes
to/from limb `3 - (k / 8)` at byte-position `7 - (k % 8)`. The only
direction-flip is that MSTORE _writes_ those bytes rather than reading
them.

### 3.2. Per-limb byte-unpack with shift-and-SB

For each input limb `L_j` (`j = 0..3`, `j = 0` is `lo`):

```
  // base = sp_evm offset of this limb in EVM stack = 8 * j + 32   (value is below offset)
  // dst  = target byte-address inside EVM memory buffer
  //      = mem_base + offset + 8 * (3 - j) ..
  //                  mem_base + offset + 8 * (3 - j) + 7
  acc := LD sp_evm + (8 * j + 32)        // load this 64-bit limb
  for k in 0..7:
      // Write byte `7 - k` of acc (the most-significant remaining byte)
      // to dst + k. The MSB-first order means we shift before each SB
      // EXCEPT the first one (which uses acc as-is via SB acc[7:0]
      // after a 56-bit right shift), or equivalently we extract via
      // SRLI + SB and rotate. Concrete sequence picked in slice 4c.
      SB dst+k acc>>((7-k)*8)
```

Two equally-valid concrete instruction patterns for the per-byte step:

(a) **shift-then-store** (mirror of MLOAD's load-then-shift-then-OR):

```
  SRLI byteReg accReg ((7-k)*8)    // isolate byte (7-k) into low 8 bits
  SB   addrReg byteReg k           // SB writes the low 8 bits at offset k
```

(b) **rotate-and-store** (single accumulator, no separate byte reg):

```
  SB   addrReg accReg k            // SB writes acc[7:0]
  SRLI accReg accReg 8             // shift down for next iteration
```

Pattern (b) is shorter (1 instruction less per byte) but mutates `acc`
destructively, so the per-byte spec must thread the shifted-down acc as
a runtime value. Pattern (a) keeps `acc` invariant and matches MLOAD's
spec shape more directly. **Recommendation: pattern (a)** for tier-1
spec uniformity with MLOAD; revisit if zk-circuit cost matters.

Per-byte instruction count under pattern (a): SRLI + SB = 2.

256-bit total under pattern (a): 4 limbs × (1 LD + 8 × (SRLI + SB)) =
4 × (1 + 16) = 68 core instructions, plus prologue (compute
`mem_base + offset`) and epilogue (`ADDI x12 x12 64`).

### 3.3. Concrete instruction count

Prologue:

```
  LD   offReg     x12  0          # low limb of offset (high 3 limbs MUST be 0; precondition)
  ADD  addrReg    memBaseReg  offReg
                                  # base byte-address of the 32-byte write
```

(Plus the optional BNE-against-zero validity check on the high 3 offset
limbs — same status as MLOAD: lifted to spec precondition; see §3.5.)

Per limb (×4): 1 LD + 8 × (SRLI + SB) = 17 instructions.

Epilogue: `ADDI x12 x12 64` (drop both 32-byte stack words).

Total: 2 (prologue) + 4 × 17 (limbs) + 1 (epilogue) = 71 instructions =
284 bytes. Slightly smaller than MLOAD (94 instructions) because each
limb saves 7 OR's and the ADDI epilogue replaces no MLOAD-side work.

### 3.4. Register usage

- `x12` (`a2`) — EVM stack pointer (caller-saved, advanced by +64).
- `memBaseReg` — caller-supplied EVM-memory base (unchanged).
- `offReg`, `addrReg` — scratch (low offset limb; per-byte target addr).
- `byteReg` — scratch holding each shifted byte before `SB`.
- `accReg` — per-limb accumulator (recycled across the 4 limbs by
  reloading with `LD` between them).

Recommended: `offReg = x5`, `addrReg = x6`, `byteReg = x7`, `accReg = x10`
— exactly the same caller-saved temporaries as MLOAD (per LP64,
`AGENTS.md` "Calling Convention (LP64)"). MSTORE and MLOAD never run
simultaneously, so they can share names without collision.

### 3.5. Offset width precondition

Same convention as MLOAD: the three high limbs of `offset` (bytes
`sp_evm + 8 .. sp_evm + 31`) must be zero. We do NOT add a runtime
check in the Program — encode it in the spec's hypothesis list. A
later slice may extend the prologue with a BNE-against-zero `ECALL`
trap without breaking this spec.

## 4. Memory expansion (high-water mark)

Identical formula to MLOAD: MSTORE must update `evmMemSizeIs` to
`evmMemExpand sizeBytes (val256 offset) 32`. `Memory.lean` already has
the pure function and `evmMemSizeIs_unfold`. Concretely:

- New high-water `size' := max sizeBytes (roundUpTo32 (offset + 32))`.
- The Program must read the current `size` cell, compute `size'`, and
  write back (3 instructions: LD, branch+max, SD — or a small CMOV-style
  sequence using SLT + select).

The simplest implementation: an unconditional `BLTU`-skipped `SD` that
writes the new bound only when greater. Recommended: do expansion
in-Program (matches MLOAD's recommendation; lets callers ignore the
high-water bookkeeping).

## 5. Per-byte spec composition strategy (for the proof)

Mirror DivMod's "limb-spec → composition" structure and MLOAD's three
tiers. The proof tower is dual to MLOAD's: source = limb register,
destination = byte cells in `evmMemIs`.

### 5.1. `mstore_byte_unpack_step_spec` (level 1)

A small `cpsTripleWithin` for the SRLI + SB pair that writes one byte
of `accReg` to `addrReg + k`:

```
  cpsTripleWithin 2 base (base + 8) cr
    ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accVal) **
     (dwordAddr ↦ₘ wordOld))
    ((addrReg ↦ᵣ addrPtr) ** (byteReg ↦ᵣ byteShifted) ** (accReg ↦ᵣ accVal) **
     (dwordAddr ↦ₘ wordNew))
```

where `byteShifted := (accVal >>> ((7-k)*8)).zeroExtend 64 &&& 0xFF`
and `wordNew := replaceByte wordOld (byteOffset addrPtr) byteShifted.lo`.
Building block analogue of `mload_byte_pack_step_spec_within`
(`Evm64/MLoad/LimbSpec.lean`, beads `evm-asm-8dk7`), and reuses
`generic_sb_spec_within` and `srli_spec_gen_*`.

### 5.2. `mstore_one_limb_spec_within` (level 2)

Compose 1 LD + 8 byte-unpack steps into one limb spec. Postcondition:
the 8 EVM-memory bytes in the dword(s) covered by
`[addrPtr + 8*(3-j) .. addrPtr + 8*(3-j) + 7]` hold the big-endian
serialisation of the limb. Use `runBlock` / `xperm`. Frame out the
unrelated 24 bytes of the 32-byte write window with `seqFrame`.

The byte-to-limb arithmetic (the inverse of `bytePack8_eq` from MLOAD)
is already discharged: `bytePack8_eq` is the equation
`(b7 ++ b6 ++ … ++ b0) = …`. For MSTORE we need the **bytes-of-a-limb**
projection identity `extractByte limb i = (limb >>> (i*8)).truncate 8`,
which `bv_decide` should handle. Encapsulate as
`bytePack8_extract` (or reuse if already present) to avoid repeating
the proof per limb.

### 5.3. `evm_mstore_stack_spec_within` (level 3)

Compose 4 limb specs back-to-back, plus the prologue, the epilogue
(`ADDI x12 x12 64`), and the size-cell update. Postcondition expressed
in terms of `evmMemIs` covering the 32-byte slice (plus the unchanged
remainder) and `evmWordIs` having been _consumed_ from the input slot.
Use the MUL / MLOAD `evmWordIs`-lift pattern in reverse: start from
two `evmWordIs` premises (offset, value) and end with `evmMemIs` plus
the value bytes equal to a big-endian projection of `value`.

## 6. Sub-slice plan (replaces the monolithic `j432`)

The single `evm-asm-j432` "MSTORE spec" task is too large for one PR
(estimated 400+ lines of Program + spec, plus several composition
lemmas and the byte-extract identity, mirroring MLOAD). Proposed split:

1. **Slice 4a — `evm_mstore` Program** (`evm-asm-j432` → new sub-slice).
   Defines `evm_mstore (offReg valReg byteReg accReg addrReg memBaseReg sizeLoc : Reg)`
   in `Evm64/MStore/Program.lean`. Wires `Evm64/MStore.lean` umbrella
   into `Evm64.lean`. Includes the `evm_mstore_code` `CodeReq` abbrev.
   Sized to ~30-40 LoC per the MLOAD precedent. No spec.

2. **Slice 4b — `bytePack8_extract` Word identity** (or reuse). Pure
   lemma in `Evm64/MStore/ByteAlg.lean` (or shared `Evm64/ByteAlg.lean`
   if MLOAD's `bytePack8_eq` belongs there too):
   `extractByte (b7 ++ … ++ b0) i = bᵢ` (or the SRLI-based dual). ~30
   LoC, decided by `bv_decide`.

3. **Slice 4c — `mstore_byte_unpack_step_spec`**. The 2-instruction
   SRLI + SB pair in `Evm64/MStore/LimbSpec.lean`. Builds on
   `generic_sb_spec_within` and basic register-arith specs. ~80 LoC.

4. **Slice 4d — `mstore_one_limb_spec_within`**. Compose 1 LD + 8
   byte-unpack steps for one input limb. ~150 LoC (the heavy `xperm` /
   `runBlock` plumbing).

5. **Slice 4e — `evm_mstore_stack_spec_within`**. Compose 4 limbs +
   prologue + epilogue + memory-size-cell update. ~200 LoC. Final
   `evmMemIs`-form theorem.

6. **Slice 4f — wire MSTORE into `Evm64.lean` umbrella + 0-sorry
   acceptance + status comment on GH #99**.

Each slice ≤ ~200 LoC, fits the worker per-iteration budget. Slices
4c/4d/4e are sequentially dependent; 4a/4b can be done in parallel.

## 7. Reuse table

| MSTORE need              | Reuse from                                | File / decl                                      |
|--------------------------|-------------------------------------------|--------------------------------------------------|
| Byte write               | RV64 byte-ops                             | `EvmAsm/Rv64/ByteOps.lean :: generic_sb_spec_within` |
| One-byte EVM write       | MSTORE8                                   | `EvmAsm/Evm64/MStore8/Program.lean`              |
| Memory model & expansion | EVM memory                                | `EvmAsm/Evm64/Memory.lean :: evmMemIs, evmMemSizeIs, evmMemExpand` |
| Stack-form pre bridge    | MUL pattern                               | `EvmAsm/Evm64/Multiply/Spec.lean :: evmWordIs lift` |
| EVM-stack assertion      | `evmWordIs`                               | `EvmAsm/Evm64/Stack.lean`                       |
| Three-tier proof shape   | MLOAD precedent                            | `Evm64/MLoad/*.lean` |
| Big-endian byte identity | MLOAD slice 3b                             | `EvmAsm/Evm64/MLoad/ByteAlg.lean :: bytePack8_eq` |
| Program-only landing     | MSTORE8 slice                              | `EvmAsm/Evm64/MStore8/Program.lean` (precedent)  |

## 8. Open questions deferred to later slices

1. **Do we add a runtime offset-too-large check?** Recommended: NO for
   slice 4a-4f; lift to spec precondition (same as MLOAD §3.5). File a
   P3 follow-up if the `run_stateless_guest` integration needs the
   runtime fault.

2. **Memory-size cell location.** Where does `sizeLoc` live in the
   `run_stateless_guest` frame? Open in #99; will be pinned down by the
   caller (top-level guest harness slice). MSTORE takes `sizeLoc` as a
   parameter for now (consistent with MLOAD).

3. **Per-byte instruction pattern (a) vs (b).** Pattern (a)
   (SRLI-then-SB, non-destructive accumulator) is recommended in §3.2
   for spec uniformity with MLOAD. Revisit in slice 4c if zk-circuit
   instruction-count cost dominates the spec-uniformity gain.

4. **Shared `Evm64/ByteAlg.lean` for big-endian byte identities.**
   `bytePack8_eq` lives in `Evm64/MLoad/ByteAlg.lean` today. If MSTORE
   slice 4b adds the dual `bytePack8_extract`, consider promoting both
   to a shared `Evm64/ByteAlg.lean` so future opcodes (e.g. CALLDATALOAD,
   RETURNDATACOPY) can reuse them without an MLOAD/MSTORE import. File
   as P4 follow-up after slice 4b lands.
