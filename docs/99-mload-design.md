# MLOAD opcode design (GH issue #99 slice 3, beads slice evm-asm-zwrs)

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

This document plans the implementation of the EVM `MLOAD` opcode
(`MLOAD(offset)` reads 32 bytes of EVM memory starting at `offset` as a
big-endian 256-bit word and pushes it onto the EVM stack). It is the
deliverable of the pre-slice of `evm-asm-cegc` / GH #99 slice 3, and is
referenced by the subsequent Program / spec slices.

No code changes; this slice is documentation only. The Program and spec
land in follow-up slices per §6 below.

## 1. EVM semantics — what `MLOAD` does

Per the yellow paper §H.1 and `execution-specs/.../vm/instructions/memory.py`:

```
def mload(evm):
    pop offset (256-bit, treated as Nat)
    expand active memory to (size := max(size, ceil((offset+32)/32) * 32))
    bytes := mem[offset .. offset + 31]      # zero-filled outside active range
    push (bytes interpreted big-endian as 256-bit)
```

Edge cases:

- `offset = 0`, fresh memory: returns 0; expands `size` to 32.
- `offset = 31`, fresh memory: returns 0; expands `size` to 64
  (the access `[31, 63)` straddles two 32-byte words).
- `offset = 2^256 - 1`: out-of-gas in real EVM; in the verified evm-asm
  setting we will assume `offset` fits in `Word` (64 bits) — the higher
  3 limbs of the EVM offset must be zero, which is a precondition (see
  §3.5).

## 2. Stack layout (LP64 + EVM-stack convention)

Using the same convention as MSIZE / MSTORE8 (cf. `Evm64/MStore8/Program.lean`):

- `x12 = sp_evm` (EVM stack pointer, grows down).
- On entry, the top-of-stack is `offset` at `sp_evm + 0 .. sp_evm + 24`
  (4 LE limbs, low limb at `sp_evm`).
- On exit, `x12 = sp_evm` (offset popped, value pushed = net zero — see
  the EVM stack-effect of `MLOAD`: `[..., offset] -> [..., value]`),
  and the result `value` lives at `sp_evm + 0 .. sp_evm + 24` (4 LE
  limbs, low limb at `sp_evm`).

Net `x12` advance is 0 (1 pop, 1 push, equal width).

## 3. RISC-V byte-assembly recipe

EVM memory is byte-addressable (per yellow paper). RV64IM memory is
dword-addressable but `Rv64/ByteOps.lean` already lifts byte operations
on top via `extractByte` / `replaceByte` and the verified
`generic_lbu_spec_within` (LBU, byte-load). MSTORE8 uses `generic_sb_spec_within`
the same way. MLOAD reuses LBU.

### 3.1. High-level structure (4 EVM-stack-limbs, 8 bytes each)

The 256-bit big-endian EVM value at byte offsets `[offset .. offset+31]`
is laid out, when read into 4 little-endian 64-bit limbs `lo .. hi`, as:

```
  byte    EVM big-endian role         RISC-V LE limb position
  ----    ----------------------       ------------------------
  off+ 0  most-significant byte (b31)  hi   limb (sp+24), byte 7 (high)
  off+ 1  b30                          hi   limb (sp+24), byte 6
  ...
  off+ 7  b24                          hi   limb (sp+24), byte 0 (low)
  off+ 8  b23                          mh   limb (sp+16), byte 7
  ...
  off+15  b16                          mh   limb (sp+16), byte 0
  off+16  b15                          ml   limb (sp+ 8), byte 7
  ...
  off+23  b 8                          ml   limb (sp+ 8), byte 0
  off+24  b 7                          lo   limb (sp+ 0), byte 7
  ...
  off+31  b 0                          lo   limb (sp+ 0), byte 0
```

So byte `off + k` (for `k = 0 .. 31`) goes into limb `3 - (k / 8)` at
byte-position `7 - (k % 8)`.

### 3.2. Per-limb byte-pack with shift-and-OR

For each output limb `L_j` (`j = 0..3`, `j = 0` is `lo`):

```
  // base = sp_evm offset of this limb in EVM stack = 8 * j
  // src  = source byte-address inside EVM memory buffer
  //      = mem_base + offset + 8 * (3 - j) ..
  //                  mem_base + offset + 8 * (3 - j) + 7
  L_j := 0
  for k in 0..7:
      byte := LBU(src + k)             // zero-extends to 64 bits
      L_j  := (L_j << 8) | byte
  SD L_j -> sp_evm + 8 * j
```

256-bit total: 4 limbs × (8 LBU + 7 SLLI + 7 OR + 1 SD) = 4 × 23 = 92
core instructions, plus prologue (compute `mem_base + offset`) and
epilogue (the final `x12` is unchanged so no `ADDI` needed).

### 3.3. Concrete instruction count

Prologue:

```
  LD   offReg     x12  0          # low limb of offset (high 3 limbs MUST be 0; precondition)
  ADD  addrReg    memBaseReg  offReg
                                  # base byte-address of the 32-byte read
```

(Plus optional reads of the high 3 offset limbs into a scratch reg + a
BNE-against-zero validity check to discharge the "offset fits in 64
bits" precondition at runtime — see §3.5; this can be a NOP at the
program level if we lift it to a spec-level precondition, which we will.)

Per limb (×4): 8 LBU + 7 SLLI 8 + 7 OR + 1 SD = 23 instructions.

Epilogue: none (x12 stays at sp_evm).

Total: 2 (prologue) + 4 × 23 (limbs) = 94 instructions = 376 bytes.

This is large but mechanical — most of it is a regular shift-and-OR
chain. We will likely keep the bytecode literal (no inner loop) because
an inner loop would (a) require an iteration counter register, (b)
require pre-/post-conditions tracking partial pack state, and (c) be
slower in zk-circuit terms. MSTORE8's straight-line precedent applies.

### 3.4. Register usage

- `x12` (`a2`) — EVM stack pointer (caller-saved, unchanged across MLOAD).
- `memBaseReg` — caller-supplied EVM-memory base (unchanged; passed as
  parameter just like MSTORE8 takes `memBaseReg`).
- `offReg`, `addrReg` — scratch (low offset limb; per-byte target addr).
- `byteReg` — scratch holding each byte's LBU result.
- `accReg0`..`accReg3` — per-limb accumulators. Can be a single recycled
  register if we SD between limbs (recommended — reduces register pressure;
  ABI permits since these are caller-saved temporaries).

Recommended: `offReg = x5`, `addrReg = x6`, `byteReg = x7`, `accReg = x10`
(all caller-saved temporaries per LP64 — see `AGENTS.md` "Calling
Convention (LP64)").

### 3.5. Offset width precondition

The full EVM `offset` is 256 bits. Real EVM rejects out-of-gas before
computing oversized addresses. evm-asm models the "in-bounds" case and
takes the precondition as a spec-level fact: the three high limbs of
`offset` (bytes `sp_evm + 8 .. sp_evm + 31`) must be zero. We do NOT
add a runtime check in the Program — we encode it in the spec's
hypothesis list (cf. how SHL/SHR `phase_a` handles "shift ≥ 256" but
MLOAD takes the simpler purely-spec-level approach because there is no
useful EVM behaviour for oversized offsets in our verification scope).

If a later slice wants to add a runtime BNE-against-zero check that
faults via `ECALL`, it can extend the prologue without breaking the
spec; the no-runtime-check version is simpler to land first.

## 4. Memory expansion (high-water mark)

Per §1, MLOAD must update `evmMemSizeIs` to
`evmMemExpand sizeBytes (val256 offset) 32`. `Memory.lean` already has
the pure function and `evmMemSizeIs_unfold`. Concretely:

- New high-water `size' := max sizeBytes (roundUpTo32 (offset + 32))`.
- The Program must read the current `size` cell, compute `size'`, and
  write back (3 instructions: LD, branch+max, SD — or a small CMOV-style
  sequence using SLT + select).

The simplest implementation: an unconditional `BLTU`-skipped `SD` that
writes the new bound only when greater. Pattern matches how MSIZE
slice 6 plans to read the cell.

Alternative: lift expansion entirely to the spec's postcondition via the
"caller already pre-expanded" precondition — but this pushes complexity
to every caller. Recommended: do expansion in-Program.

## 5. Per-byte spec composition strategy (for the proof)

Mirror DivMod's "limb-spec → composition" structure. Three tiers:

### 5.1. `mload_byte_pack_step_spec` (level 1)

A small `cpsTripleWithin` for the LBU + SLLI + OR triple that packs one
byte into the running accumulator. Building block analogue of
`push_one_byte_spec_within` (`Push/Spec.lean`, beads `evm-asm-530s`).

### 5.2. `mload_one_limb_spec_within` (level 2)

Compose 8 byte-pack steps + final SD into one limb spec. Postcondition:
the EVM stack cell at `sp_evm + 8*j` holds the packed limb value. Use
`runBlock` and `xperm`. Frame out the unrelated 3 limbs with `seqFrame`.

### 5.3. `evm_mload_stack_spec_within` (level 3)

Compose 4 limb specs back-to-back, plus the prologue and the size-cell
update. Postcondition expressed in terms of the `evmWordIs` lifted
predicate over the 4 LE limbs (cf. `Evm64/Stack.lean` and how MUL's
`evm_mul_stack_spec` packages 4-limb output as `evmWordIs`).

The byte-to-limb arithmetic (`(b7 << 56) | (b6 << 48) | ... | b0`) is
a pure-Word identity that can be discharged by `bv_decide` or a small
`bv_omega`-driven calculation; encapsulate it in a helper lemma
`bytePack8_eq` to avoid repeating the proof per limb.

## 6. Sub-slice plan (replaces the monolithic `cegc`)

The single `evm-asm-cegc` "MLOAD spec" task is too large for one PR
(estimated 400+ lines of Program + spec, plus several composition
lemmas and the byte-pack identity). Proposed split:

1. **Slice 3a — `evm_mload` Program** (`evm-asm-cegc` → new sub-slice).
   Defines `evm_mload (offReg byteReg accReg addrReg memBaseReg sizeLoc : Reg)`
   in `Evm64/MLoad/Program.lean`. Wires `Evm64/MLoad.lean` umbrella into
   `Evm64.lean`. Includes the `evm_mload_code` `CodeReq` abbrev. Sized
   to ~20-30 LoC per the MSTORE8 precedent. No spec.

2. **Slice 3b — `bytePack8_eq` Word identity**. Pure lemma in
   `Evm64/MLoad/ByteAlg.lean`:
   `((b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) : BitVec 64)`
   = appropriate shift-OR composition. Standalone, usable by the
   limb-spec slice. ~30 LoC, decided by `bv_decide`.

3. **Slice 3c — `mload_byte_pack_step_spec`**. The 3-instruction
   LBU + SLLI + OR triple in `Evm64/MLoad/LimbSpec.lean`. Builds on
   `generic_lbu_spec_within` and basic register-arith specs. ~80 LoC.

4. **Slice 3d — `mload_one_limb_spec_within`**. Compose 8 byte-pack
   steps + SD for one output limb. ~150 LoC (the heavy `xperm` /
   `runBlock` plumbing).

5. **Slice 3e — `evm_mload_stack_spec_within`**. Compose 4 limbs +
   prologue + memory-size-cell update. ~200 LoC. Final `evmWordIs`-form
   theorem.

6. **Slice 3f — wire MLOAD into `Evm64.lean` umbrella + 0-sorry
   acceptance + status comment on GH #99**.

Each slice ≤ ~200 LoC, fits the worker per-iteration budget. Slices
3c/3d/3e are sequentially dependent; 3a/3b can be done in parallel.

## 7. Reuse table

| MLOAD need              | Reuse from                                | File / decl                                      |
|-------------------------|-------------------------------------------|--------------------------------------------------|
| Byte read               | RV64 byte-ops                             | `EvmAsm/Rv64/ByteOps.lean :: generic_lbu_spec_within` |
| Memory model & expansion | EVM memory                                | `EvmAsm/Evm64/Memory.lean :: evmMemIs, evmMemSizeIs, evmMemExpand` |
| Stack-form post bridge  | MUL pattern                               | `EvmAsm/Evm64/Multiply/Spec.lean :: evmWordIs lift` |
| EVM-stack assertion      | `evmWordIs`                               | `EvmAsm/Evm64/Stack.lean`                       |
| Program-only landing pattern | MSTORE8 slice                          | `EvmAsm/Evm64/MStore8/Program.lean` (new)       |

## 8. Open questions deferred to later slices

1. **Do we add a runtime offset-too-large check?** Recommended: NO for
   slice 3a-3f; lift to spec precondition. File a P3 follow-up if the
   `run_stateless_guest` integration needs the runtime fault.

2. **Memory-size cell location.** Where does `sizeLoc` live in the
   `run_stateless_guest` frame? Open in #99; will be pinned down by the
   caller (top-level guest harness slice). MLOAD takes `sizeLoc` as a
   parameter for now.

3. **Big-endian byte-pack identity proof tooling.** `bv_decide` should
   handle `bytePack8_eq`; if not, we fall back to a manual
   `BitVec.toNat`-bridge proof. Decide in slice 3b.

## 9. Acceptance / next-slice handoff

This slice is complete when:

- `docs/99-mload-design.md` is checked in.
- `evm-asm-cegc` (the parent slice 3 task) is updated to reference the
  6 sub-slices proposed in §6 (or replaced by them).
- The next slice (3a, `evm_mload` Program) can proceed without further
  investigation.

No Lean code changes; CI should pass trivially.
