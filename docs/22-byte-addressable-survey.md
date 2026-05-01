# GH #22 — byte-addressable memory: current-state survey

GH issue #22 ("consider byte-addressible memory") is a one-line design
suggestion: *"Maybe things are easier when the memory can be split byte-wise?"*.
This document inventories what byte-level memory reasoning evm-asm already
supports today, where it is exercised, and whether any production call site
falls back to a dword-level workaround for what should naturally be byte-level
work. The output drives the slice-2 recommendation on whether to close #22 as
"addressed" or to file followups.

Tracking: beads `evm-asm-ndo1` (slice 1 of `evm-asm-59i5` / GH #22).

## TL;DR

The underlying RV64 memory model is dword-keyed (`Word → Word`, see
`EvmAsm/Rv64/Basic.lean`), but a byte-level read/write semantics is layered on
top via `extractByte` / `replaceByte` and the `getByte` / `setByte`
projections, lifted to separation logic by the `generic_lbu_spec_within` /
`generic_lb_spec_within` / `generic_sb_spec_within` triples in
`EvmAsm/Rv64/ByteOps.lean`. Every production byte-level call site (RLP
decoder, code-region projection used by EVM dispatch) goes through these
primitives — there are no observed workarounds where byte-level reasoning was
needed but author had to drop down to dword reasoning. The infrastructure
covers the cases the project actually has today.

## A. ByteOps.lean coverage (`EvmAsm/Rv64/ByteOps.lean`, 205 LoC)

Defs (re-exported from `Rv64/Basic.lean`):

- `extractByte (w : Word) (pos : Nat) : BitVec 8` — pure projection of byte
  `pos` from a 64-bit word.
- `replaceByte (w : Word) (pos : Nat) (b : BitVec 8) : Word` — pure update of
  byte `pos` to `b`.
- `alignToDword (addr : Word) : Word := addr &&& ~~~7#64` — drop low 3 bits.
- `byteOffset (addr : Word) : Nat := (addr &&& 7#64).toNat` — low 3 bits as
  Nat (`< 8`).
- `MachineState.getByte / setByte` (in `Basic.lean`) — `extractByte ∘ getMem ∘
  alignToDword` and the symmetric `setMem ∘ alignToDword ∘ replaceByte ∘
  getMem`.
- `isValidByteAccess` — alignment+region predicate; one-liner in `Basic.lean`.

Algebraic lemmas proved in `ByteOps.lean`:

- `byteOffset_lt_8`.
- `extractByte_replaceByte_same` (8 per-position cases `erbs_0..erbs_7` plus a
  `Fin 8`-indexed wrapper). Closed via the `byte_algebra` macro
  (`ext i (hi : i < 8); simp [BitVec.truncate, BitVec.zeroExtend];
  try { interval_cases i <;> simp_all }`).
- `getByte_eq` / `setByte_eq` — definitional reductions to the
  `extractByte` / `replaceByte` form.

CPS-style separation-logic specs (the user-facing surface):

- `generic_lbu_spec_within` — `LBU rd rs1 offset` reads a byte and zero-extends
  to 64 bits. Pre/post own `(rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** (dwordAddr ↦ₘ
  wordVal)` ; postcondition reads the extracted byte, pre/post assert
  `alignToDword (v_addr + signExtend12 offset) = dwordAddr` and
  `isValidByteAccess (...) = true` as side conditions.
- `generic_lb_spec_within` — `LB`, identical shape but `signExtend 64`.
- `generic_sb_spec_within` — `SB rs1 rs2 offset` writes
  `(v_data.truncate 8)` into the appropriate byte slot of the dword via
  `replaceByte`, preserves `rs1` / `rs2` registers.

These are re-exposed under the spec-gen registry in
`EvmAsm/Rv64/SyscallSpecs.lean` (`@[spec_gen_rv64]` wrappers
`lbu_spec_gen_within`, `lb_spec_gen_within`, `sb_spec_gen_within`) so
`liftSpec` / `runBlock` automation pulls them automatically when a basic block
contains an LB/LBU/SB instruction.

## B. byte_alg grindset (`EvmAsm/Rv64/ByteAlg.lean`, 61 LoC)

`Rv64/ByteAlg.lean` declares the `@[byte_alg]` simp / `@[grind =]` attribute
(`Rv64/ByteAlgAttr.lean`) and seeds it with
`extractByte_replaceByte_same`. The `byte_alg` macro is
`first | grind | simp only [byte_alg]`, intended to grow as more identities
(diff-position, idempotent replace, byte-index arithmetic, concrete-literal
extraction) are added.

Current users of the `@[byte_alg]` attribute *as a rewriter*: 0 outside
`Rv64/ByteAlg.lean` itself. The attribute is a forward-looking scaffold; the
single seeded fact is in practice always discharged via the `extractByte_*`
lemma name directly or via `grind`. This is consistent with the GRIND.md
Phase 4 design — the set is meant to grow before adoption broadens.

## C. Production byte-level call sites

### C.1 RLP decoder (`EvmAsm/Rv64/RLP/`, 28 files)

This is the largest byte-level consumer. Files that touch `extractByte` /
`byteOffset` / `isValidByteAccess` / `generic_lbu_spec_within`:

- `Phase1E3LongStringOne.lean` — single LBU spec invocation, walks one
  long-string-prefix byte.
- `Phase2LongLoad.lean` — LBU at the start of each long-string iteration:
  `generic_lbu_spec_within .x12 .x13 ptr v12Old 0 base dwordAddr wordVal`.
- `Phase2LongIter.lean` — same shape, applied inside the iteration body.
- `Phase2LongLoopOne.lean` … `Phase2LongLoopEight.lean` and
  `Phase2LongLoopBody.lean` — composition pipeline that threads the read byte
  through the loop's accumulator. `extractByte` / `byteOffset` /
  `isValidByteAccess` co-occur in each (per the rg histogram: 2..10 hits per
  file, total ~46 `extractByte` and ~57 `byteOffset` references across the
  Phase2 chain).

Pattern observed everywhere: `generic_lbu_spec_within` produces a postcondition
of the form `rd ↦ᵣ (extractByte wordVal (byteOffset addr)).zeroExtend 64`,
which downstream proofs leave abstract (treated as an opaque value plumbed to
the next `seqFrame`). They never need to *reduce* the `extractByte` symbolically
because the RLP semantics is byte-oriented from the start: the post is
forwarded into the next step's pre via `xperm_hyp`.

### C.2 Code region projection (`EvmAsm/Evm64/CodeRegion.lean`)

The pure bridge `extractByte_packDword` / `extractByte_packBytes` /
`extractByte_codeRegion_at` proves that reading byte `k` from a packed dword
representation of a byte list returns `bytes[k]`. Used for the EVM bytecode
region: callers fetch the dword, then read the relevant byte for opcode
dispatch via `extractByte`. This is the only file outside `Rv64/RLP/` and
`Rv64/ByteOps.lean` that touches `extractByte`, and it is a derivation, not a
machine-state interaction (no `getByte` / `setByte` involved).

### C.3 Other consumers

- `Rv64/HalfwordOps.lean` and `Rv64/WordOps.lean` reference `byteOffset` for
  the alignment side conditions of LH/LW (halfword/word load). These *do
  not* use `extractByte` — they assert dword alignment directly. This is
  correct: halfword/word loads in our region don't decompose to bytes.
- `Rv64/Instructions.lean` and `Rv64/Execution.lean` — the operational
  semantics of `LB` / `LBU` / `SB` themselves, defined in terms of
  `s.getByte` / `s.setByte`. Not consumer code; these are the source of truth
  the byte specs reduce to.

## D. Workarounds / gaps

Searched for places where byte-level reasoning would be natural but a
dword-level workaround was used:

- **No occurrences found.** The RLP decoder is the only system that needs
  byte addressing; it uses `generic_lbu_spec_within` uniformly. The EVM
  opcode tree (`Evm64/Add`, `Evm64/Sub`, …, `Evm64/DivMod`) operates on
  256-bit words (4 dword limbs) and never reads sub-dword granularity in its
  operational paths. The single EVM opcode that *does* dissect a word into
  bytes — `BYTE` (`Evm64/Byte/`) — operates on the EVM `EvmWord` (BitVec 256)
  in pure-bitvector land; its `Program.lean` / `Spec.lean` / `LimbSpec.lean`
  contain no `extractByte` / `byteOffset` references because the operation is
  realized via shifts and masks on 64-bit limbs, not memory byte access.
  This is by design: `BYTE` doesn't *load* a byte from memory, it indexes
  into a 256-bit register-resident value.
- The future-work hooks called out in `Rv64/ByteAlg.lean`
  (`extractByte_replaceByte_diff`, `replaceByte_replaceByte_same`,
  byte-index arithmetic) are not currently needed because every caller in
  the codebase ends each instruction sequence with `extractByte` and never
  composes two consecutive `replaceByte` calls — SB writes the byte then
  hands the new dword off as an opaque `wordOld'`. This would change if a
  contiguous byte-buffer write loop showed up; today no such loop exists.

## E. Recommendation input for slice 2

- The byte-addressable feature requested in #22, interpreted as *"reasoning
  about byte-grain memory access on top of a dword-keyed underlying model"*,
  is fully addressed by `Rv64/ByteOps.lean` plus the spec-gen wrappers, and
  is in production use under `Rv64/RLP/`.
- An alternate interpretation — *"replace the underlying memory model with a
  byte-keyed map (`Word → BitVec 8`)"* — would be a much larger refactor with
  no current consumer; the dword-level model is what the EVM 256-bit
  opcodes already operate on, so a byte-keyed reformulation would force an
  extra layer of "pack 8 bytes" reasoning across the Evm64 tree. Not
  motivated by any open issue.
- Recommend slice 2 post a status comment proposing closure of GH #22 as
  *"addressed by `Rv64/ByteOps.lean` + `Rv64/ByteAlg.lean` + the byte-spec
  generators in `SyscallSpecs.lean`"*, with the survey link, and noting that
  the `byte_alg` grindset is the natural growth path for additional byte
  identities should new consumers (e.g. EL Trie, Keccak, EVM `MSTORE8`)
  ever require them. Each such future need should be filed as its own issue
  rather than parked under the open #22 umbrella.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
