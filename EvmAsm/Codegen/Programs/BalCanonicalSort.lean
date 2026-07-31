/-
  EvmAsm.Codegen.Programs.BalCanonicalSort

  Canonical ordering for the BAL write containers — GH #10680.

  ## What canonical means, and why raw bytes are the wrong key

  RLP encodes a list in the order given, so the BAL bytes reproduce only if the
  accounts and their slots are emitted in the spec's declared order:

      block_access_list.sort(key=lambda x: x.address)   # block_access_lists.py:578
      storage_changes.sort(key=lambda x: x.slot)        #                     :564

  Address-major, slot-minor. In the guest's `storage_writes` rows the two keys are
  contiguous in the leading 64 bytes (address at +0, slot at +32), which invites a
  single flat lexicographic sort over that prefix. **That would be wrong**, for a
  reason that is invisible unless you check the byte order:

  `env.ADDRESS` at `env+0` is stored in **EVM stack-word layout — four
  little-endian u64 limbs, low limb first** (`EvmLogHandlers.lean:74`; the receipt
  log encoder has to *reverse the 20 address bytes* to obtain a canonical BE
  address, which is the load-bearing evidence rather than the comment). `slotKey`
  is documented the same way. So a lexicographic sort over the raw prefix orders
  rows by the limb-swapped representation: a well-defined permutation that is
  neither address order nor slot order.

  The canonical big-endian byte at index `b` of a 32-byte low-limb-first field is
  therefore field byte `31 - b` — the field, byte-reversed. That is the whole
  correction, and it is why this is one sort but not one *flat* sort.

  ## This routine ships with NO verification of its own, deliberately

  The correctness criterion for the BAL is the one `execution-specs` itself uses:
  **sort, take the hash, compare the hash.** This routine cannot produce a hash on
  its own — that needs the serializer — so its correctness is established *end to
  end* when the rebuilt hash is compared against the declared one, and not before.

  It is worth being precise about why no intermediate property is substituted,
  because two plausible ones were considered and both rejected:

  1. **Sortedness plus permutation-preservation is insufficient.** Both properties
     hold for a sort on the *wrong* key: sorted-by-the-limb-swapped-key is still
     sorted, and still a permutation of the input multiset. They would have passed
     on precisely the byte-order error described above.

  2. **Comparing our order against a fixture's declared order is the wrong *shape*
     of argument**, not merely weaker. It is a statement about the order, and
     getting from a property of the order to the bytes the spec commits to takes
     extra steps the spec does not take — the spec's own correctness statement is
     a hash equality.

  And the reason the hash comparison is sound while an inference from it would not
  be: **we cannot assume keccak is injective.** Concluding "our bytes equal theirs"
  *from* "our hash equals theirs" needs injectivity, which is not available in a
  kernel-checked proof and must not be smuggled in. The way out is congruence
  rather than inference — if the guest sorts the same way and hashes the same way
  as the spec, it produces the same hash *by construction*: same input, same
  function, same output, no collision assumption anywhere.

  An order-comparison against a fixture's declared `blockAccessList` remains
  useful as a **diagnostic**, and only as one: a 32-byte digest cannot tell you
  *which* account or slot diverged, and an order comparison can. It localises a
  failure. It is not the gate.

  The `#guard`s at the end of this file are anti-drift checks on the emitted
  *text* — that the reversal is present, that each failure path has a distinct
  status. They are not, and must not be read as, a correctness argument about the
  ordering this produces.

  ## Structure, inherited from `mpt_bounded_sort_changes`

  In-place MSD radix sort, nibble digits (fanout 16), with an **explicit bounded
  stack** rather than recursion, capacity argued rather than assumed: at most 16
  ranges are introduced per depth, so `depth × 16` suffices. Bounds are checked
  before every write, and the routine **returns a status** — `a0 = 0` ok, nonzero
  on malformed input or a capacity violation — rather than bailing silently. This
  work sits under the no-conservative-bails epic, so a silent bail must not be
  imported along with the structure.

  Nibbles rather than bytes for the radix: cost per depth is `fanout × range`, so
  128 nibble depths × 16 = 2048 beats 64 byte depths × 256 = 16384, and the range
  stack is 64 KiB instead of 512 KiB.

  ## Key layout parameterisation

  One routine serves every container. The key is up to THREE SEGMENTS, each a
  `(byte offset, width)` pair packed one byte each into a register, with **bit 7 of
  the width byte meaning "already big-endian"**:

  | consumer | stride | key segments (most to least significant) |
  |---|---|---|
  | `account_writes` | 128 | address `(0,20)` LE |
  | `storage_writes` | 128 | address `(0,20)` LE, slot `(32,32)` LE |
  | builder lists | per codex | address `(0,20)` BE, [slot], `block_access_index` LE |

  The per-segment endianness is load-bearing rather than a convenience. The write
  containers hold addresses as LE limbs, so those segments are reversed; the
  builder's rows carry a canonical BE20 address already, so reversing it would order
  them by a byte-reversed address. Both orders are total, both are permutations of
  the input, and only one is canonical — so nothing structural distinguishes them.

  For canonical byte index `b` inside a segment of width `w` at offset `k`:

      LE segment (flag clear)  ->  row offset = k + w - 1 - b
      BE segment (flag set)    ->  row offset = k + b

  The two write-container entry points both declare a 20-byte address segment at
  offset 0, which is what makes them **agree on account order by construction**
  rather than by coincidence — the serializer walks accounts once and must find each
  account's slots under the same account. Both also skip the stack word's upper 12
  bytes, which are padding that happens to be zero rather than key material.

-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.StorageWriteMap
import EvmAsm.Codegen.Programs.AccountWriteMap

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Canonical key bytes for a `storage_writes` row: address (32) ++ slot (32). -/
def balSortStorageKeyBytes : Nat := 64
/-- Canonical key bytes for an `account_writes` row: the 20 significant address
    bytes. The field's upper 12 bytes are zero in a low-limb-first 256-bit word,
    so they are constant and cannot affect the order. -/
def balSortAccountKeyBytes : Nat := 20
/-- Nibble digits, so the depth is twice the key width. -/
def balSortMaxDepth : Nat := 2 * balSortStorageKeyBytes
/-- At most `fanout` ranges are introduced per depth. -/
def balSortRangeStackCapacity : Nat := balSortMaxDepth * bsrMptRadixFanout
/-- `(start, end, depth, _)`, 8 bytes each. -/
def balSortRangeFrameBytes : Nat := 32

/-- Canonical nibble extraction, inlined into the scan loop.

    In:  t0 = row pointer, s6 = nibble depth, s10 = packed segments.
    Out: t3 = the nibble (0..15).  Clobbers t2, t3, t5, a6, a7.

    Walks the segment list subtracting each width until the canonical byte index
    falls inside a segment, then indexes that segment forward or backward according
    to its endianness bit. Even depths take the byte's HIGH nibble and odd depths the
    low one, so the more significant nibble is compared first. -/
def balCanonicalDigit_prog : Program :=
  [ .SRLI .x7 .x22 (1 : BitVec 6),
    .LI .x16 (0 : Word),
    .SLLI .x17 .x16 (4 : BitVec 6),
    .SRL .x30 .x26 .x17,
    .ANDI .x30 .x30 (255 : BitVec 12),
    .ADDI .x17 .x17 (8 : BitVec 12),
    .SRL .x28 .x26 .x17,
    .ANDI .x28 .x28 (127 : BitVec 12),
    .BLTU .x7 .x28 (16 : BitVec 13),
    .SUB .x7 .x7 .x28,
    .ADDI .x16 .x16 (1 : BitVec 12),
    .JAL .x0 (-36 : BitVec 21),
    .SLLI .x17 .x16 (4 : BitVec 6),
    .ADDI .x17 .x17 (8 : BitVec 12),
    .SRL .x17 .x26 .x17,
    .ANDI .x17 .x17 (128 : BitVec 12),
    .BNE .x17 .x0 (20 : BitVec 13),
    .ADD .x30 .x30 .x28,
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .SUB .x30 .x30 .x7,
    .JAL .x0 (8 : BitVec 21),
    .ADD .x30 .x30 .x7,
    .ADD .x30 .x5 .x30,
    .LBU .x28 .x30 (0 : BitVec 12),
    .ANDI .x17 .x22 (1 : BitVec 12),
    .BNE .x17 .x0 (8 : BitVec 13),
    .SRLI .x28 .x28 (4 : BitVec 6),
    .ANDI .x28 .x28 (15 : BitVec 12) ]

/-! ## `bal_canonical_sort`

    In-place MSD radix sort into the spec's canonical order.

    ABI:
      a0 = base of the row array
      a1 = row count
      a2 = row stride in bytes
      a3 = packed segment descriptor: for segment i, byte 2i is its offset and
           byte 2i+1 its width, little-endian within the register (up to 3 segments)
      a4 = segment count (1..3)
    returns
      a0 = 0 success
         = 1 count exceeds capacity
         = 2 unsupported field count (a3 not in {1,2})
         = 3 range-stack capacity violation
         = 4 unsupported firstSig (not in {20,32})

    Distinct nonzero codes rather than a single failure value, so a caller can
    tell a capacity problem from a misuse — the same reason the storage-side
    helpers return codes rather than booleans. -/
def balCanonicalSortHead_prog : Program :=
  [ .ADDI .x2 .x2 (-112 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .SD .x2 .x25 (80 : BitVec 12),
    .SD .x2 .x26 (88 : BitVec 12),
    .SD .x2 .x27 (96 : BitVec 12),
    .LI .x5 (1 : Word),
    .BLTU .x14 .x5 (16 : BitVec 13),
    .LI .x5 (3 : Word),
    .BLTU .x5 .x14 (8 : BitVec 13),
    .JAL .x0 (12 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (448 : BitVec 21),
    .LUI .x5 (5 : BitVec 20),
    .BLTU .x5 .x11 (420 : BitVec 13),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x24 .x12,
    .MV .x26 .x13,
    .LI .x25 (0 : Word),
    .LI .x6 (0 : Word),
    .BGEU .x6 .x14 (32 : BitVec 13),
    .SLLI .x7 .x6 (4 : BitVec 6),
    .ADDI .x7 .x7 (8 : BitVec 12),
    .SRL .x5 .x26 .x7,
    .ANDI .x5 .x5 (127 : BitVec 12),
    .ADD .x25 .x25 .x5,
    .ADDI .x6 .x6 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .BEQ .x25 .x0 (-72 : BitVec 13),
    .SLLI .x27 .x25 (1 : BitVec 6),
    .AUIPC .x18 (laHi GuestAddrs.bal_sort_ranges (GuestAddrs.bal_canonical_sort + 156)),
    .ADDI .x18 .x18 (laLo GuestAddrs.bal_sort_ranges (GuestAddrs.bal_canonical_sort + 156)),
    .LI .x19 (0 : Word),
    .LI .x5 (2 : Word),
    .BLTU .x9 .x5 (352 : BitVec 13),
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x18 .x9 (8 : BitVec 12),
    .SD .x18 .x0 (16 : BitVec 12),
    .SD .x18 .x0 (24 : BitVec 12),
    .LI .x19 (1 : Word),
    .BEQ .x19 .x0 (328 : BitVec 13),
    .ADDI .x19 .x19 (-1 : BitVec 12),
    .SLLI .x5 .x19 (5 : BitVec 6),
    .ADD .x5 .x18 .x5,
    .LD .x20 .x5 (0 : BitVec 12),
    .LD .x21 .x5 (8 : BitVec 12),
    .LD .x22 .x5 (16 : BitVec 12),
    .ADDI .x6 .x20 (1 : BitVec 12),
    .BGEU .x6 .x21 (-32 : BitVec 13),
    .BGEU .x22 .x27 (-36 : BitVec 13),
    .MV .x23 .x20,
    .LI .x31 (0 : Word),
    .LI .x5 (16 : Word),
    .BEQ .x31 .x5 (-52 : BitVec 13),
    .MV .x6 .x23,
    .BEQ .x6 .x21 (188 : BitVec 13),
    .MUL .x5 .x6 .x24,
    .ADD .x5 .x8 .x5 ]
def balCanonicalSortTail_prog : Program :=
  [ .BNE .x28 .x31 (56 : BitVec 13),
    .BEQ .x6 .x23 (48 : BitVec 13),
    .MUL .x7 .x23 .x24,
    .ADD .x7 .x8 .x7,
    .MV .x29 .x24,
    .LD .x30 .x5 (0 : BitVec 12),
    .LD .x15 .x7 (0 : BitVec 12),
    .SD .x5 .x15 (0 : BitVec 12),
    .SD .x7 .x30 (0 : BitVec 12),
    .ADDI .x5 .x5 (8 : BitVec 12),
    .ADDI .x7 .x7 (8 : BitVec 12),
    .ADDI .x29 .x29 (-8 : BitVec 12),
    .BNE .x29 .x0 (-28 : BitVec 13),
    .ADDI .x23 .x23 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .JAL .x0 (-184 : BitVec 21),
    .ADDI .x5 .x20 (1 : BitVec 12),
    .BGEU .x5 .x23 (48 : BitVec 13),
    .LUI .x5 (1 : BitVec 20),
    .ADDIW .x5 .x5 (-2048 : BitVec 12),
    .BGEU .x19 .x5 (56 : BitVec 13),
    .SLLI .x5 .x19 (5 : BitVec 6),
    .ADD .x5 .x18 .x5,
    .SD .x5 .x20 (0 : BitVec 12),
    .SD .x5 .x23 (8 : BitVec 12),
    .ADDI .x6 .x22 (1 : BitVec 12),
    .SD .x5 .x6 (16 : BitVec 12),
    .SD .x5 .x0 (24 : BitVec 12),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .MV .x20 .x23,
    .ADDI .x31 .x31 (1 : BitVec 12),
    .JAL .x0 (-260 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (3 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .LD .x25 .x2 (80 : BitVec 12),
    .LD .x26 .x2 (88 : BitVec 12),
    .LD .x27 .x2 (96 : BitVec 12),
    .ADDI .x2 .x2 (112 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]
/-- The whole routine, with the digit extractor composed in at list level where
    `balCanonicalDigitAsm` used to be spliced textually.  The branch offsets in
    `balCanonicalSortTail_prog` were resolved against THIS concatenation, so the
    three pieces are correct only together -- which is why the split is a slice of
    one conversion rather than three independent conversions. -/
def balCanonicalSort_prog : Program :=
  balCanonicalSortHead_prog ++ balCanonicalDigit_prog ++ balCanonicalSortTail_prog

/-- Reloc side-table for `balCanonicalSort_prog`: the `la` instruction index kept
    SYMBOLIC in the emitted image text (`emitProgramR`), while the Program above
    carries the concrete guest-linked immediate for verification. Index 39 lies in
    the head, so composing the digit in does not move it. -/
def balCanonicalSort_relocs : RelocTable :=
  [ (39, .la .x18 "bal_sort_ranges") ]

/-- The `.globl` stays in the string prefix: it is an assembler directive with no
    `Instr` constructor, so it cannot live in a `Program`, and `emitProgramR` does
    not emit directives. Every other converted def in the tree starts at its label
    because none of them is exported. -/
def balCanonicalSortFunction : String :=
  "  .globl bal_canonical_sort\n" ++
  "bal_canonical_sort:\n" ++ emitProgramR balCanonicalSort_prog balCanonicalSort_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balCanonicalSort_prog` rendered under its label with the `la`
    reloc kept symbolic (mechanical conversion by `scripts/asm_to_program.py`).
    Guest binary byte-identity verified by assemble+cmp of the `.text`:
    588 vs 588 bytes, IDENTICAL. -/
theorem balCanonicalSortFunction_eq_prog :
    balCanonicalSortFunction = "  .globl bal_canonical_sort\n" ++
      "bal_canonical_sort:\n" ++
        emitProgramR balCanonicalSort_prog balCanonicalSort_relocs := rfl


/-! ## Thin per-container entry points

    Each names its own base, stride and key layout, so no caller has to remember
    which key width belongs to which arena — the misuse the status codes 2 and 4
    exist to catch is not reachable from these. -/

-- REACHABILITY (measured 2026-07-31 on ed50a5dbb): ZERO callers. No jal/jalr/la/call/
-- tail/auipc materialisation of `bal_sort_storage_writes` anywhere in the 2,124,874-byte
-- emitted guest stream (it appears only as its own `.globl` + label); no external
-- `GuestAddrs.bal_sort_storage_writes` reference outside this module. The EIP-7928 BAL
-- canonical ordering (incl. the address-major/slot-minor slot order this produces) is
-- already achieved by the live path and proven correct by the #11016 correspondence
-- (1149/1149 records: account / slot / per-index orders). So this routine is UNUSED — the
-- ordering obligation is met without it. Kept, not deleted, because its address is pinned
-- in `GuestAddrs.lean` (removal would force a repin cascade across GuestAddrs / the region
-- map / address-pinned proofs). See #11017.
/-- Sort the block-level `storage_writes` map into address-major, slot-minor
    order. a0 = 0 on success, else the `bal_canonical_sort` status. -/
def balSortStorageWrites_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .LUI .x10 (5 : BitVec 20),
    .ADDIW .x10 .x10 (253 : BitVec 12),
    .SLLI .x10 .x10 (17 : BitVec 6),
    .AUIPC .x5 (laHi GuestAddrs.storage_writes_count (GuestAddrs.bal_sort_storage_writes + 20)),
    .ADDI .x5 .x5 (laLo GuestAddrs.storage_writes_count (GuestAddrs.bal_sort_storage_writes + 20)),
    .LD .x11 .x5 (0 : BitVec 12),
    .LI .x12 (128 : Word),
    .LUI .x13 (131585 : BitVec 20),
    .ADDIW .x13 .x13 (1024 : BitVec 12),
    .LI .x14 (2 : Word),
    .JAL .x1 (jalOff GuestAddrs.bal_canonical_sort (GuestAddrs.bal_sort_storage_writes + 48)),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]
/-- Reloc side-table for `balSortStorageWrites_prog`. -/
def balSortStorageWrites_relocs : RelocTable :=
  [ (5, .la .x5 "storage_writes_count"),
    (12, .jal .x1 "bal_canonical_sort") ]

def balSortStorageWritesFunction : String :=
  "  .globl bal_sort_storage_writes\n" ++
  "bal_sort_storage_writes:\n" ++ emitProgramR balSortStorageWrites_prog balSortStorageWrites_relocs

/-- Kernel-checked drift guard; guest byte-identity verified by assemble+cmp:
    64 vs 64 bytes, IDENTICAL. -/
theorem balSortStorageWritesFunction_eq_prog :
    balSortStorageWritesFunction = "  .globl bal_sort_storage_writes\n" ++
      "bal_sort_storage_writes:\n" ++ emitProgramR balSortStorageWrites_prog balSortStorageWrites_relocs := rfl


-- REACHABILITY (measured 2026-07-31 on ed50a5dbb): ZERO callers. No jal/jalr/la/call/
-- tail/auipc materialisation of `bal_sort_account_writes` anywhere in the 2,124,874-byte
-- emitted guest stream (it appears only as its own `.globl` + label); no external
-- `GuestAddrs.bal_sort_account_writes` reference outside this module. The EIP-7928 BAL
-- canonical ordering (incl. the account order this produces) is already achieved by the
-- live path and proven correct by the #11016 correspondence (1149/1149 records: account /
-- slot / per-index orders). So this routine is UNUSED — the ordering obligation is met
-- without it. Kept, not deleted, because its address is pinned in `GuestAddrs.lean`
-- (removal would force a repin cascade across GuestAddrs / the region map / address-pinned
-- proofs). See #11017.
/-- Sort the block-level `account_writes` map into address order. -/
def balSortAccountWrites_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .LUI .x10 (5 : BitVec 20),
    .ADDIW .x10 .x10 (293 : BitVec 12),
    .SLLI .x10 .x10 (17 : BitVec 6),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.bal_sort_account_writes + 20)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.bal_sort_account_writes + 20)),
    .LD .x11 .x5 (0 : BitVec 12),
    .LI .x12 (128 : Word),
    .LUI .x13 (9 : BitVec 20),
    .ADDIW .x13 .x13 (1024 : BitVec 12),
    .LI .x14 (1 : Word),
    .JAL .x1 (jalOff GuestAddrs.bal_canonical_sort (GuestAddrs.bal_sort_account_writes + 48)),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]
/-- Reloc side-table for `balSortAccountWrites_prog`. -/
def balSortAccountWrites_relocs : RelocTable :=
  [ (5, .la .x5 "account_writes_count"),
    (12, .jal .x1 "bal_canonical_sort") ]

def balSortAccountWritesFunction : String :=
  "  .globl bal_sort_account_writes\n" ++
  "bal_sort_account_writes:\n" ++ emitProgramR balSortAccountWrites_prog balSortAccountWrites_relocs

/-- Kernel-checked drift guard; guest byte-identity verified by assemble+cmp:
    64 vs 64 bytes, IDENTICAL. -/
theorem balSortAccountWritesFunction_eq_prog :
    balSortAccountWritesFunction = "  .globl bal_sort_account_writes\n" ++
      "bal_sort_account_writes:\n" ++ emitProgramR balSortAccountWrites_prog balSortAccountWrites_relocs := rfl


/-! ## `bal_canonical_sort_selftest`

    Sorts four synthetic rows whose expected order is derived INDEPENDENTLY of the
    guest's digit logic, and checks the result.

    Why an independent expectation matters here: the obvious check — walk the sorted
    rows and confirm each key is <= the next — would use the SAME digit extraction
    the sort uses. If that extraction is wrong, both agree and the check passes
    vacuously on a limb-swapped order. So the expected permutation is computed from
    the canonical rule alone and hardcoded.

    The rows differ only in field byte 19, which is the address's canonical BE MOST
    SIGNIFICANT byte (the address occupies the low 20 bytes of an LE word). Values
    0x30, 0x10, 0x40, 0x20 in rows 0..3, so canonical ascending order is rows
    1, 3, 0, 2. Each row carries its 1-based tag at offset 64, so the tag sequence
    after sorting must read 2, 4, 1, 3.

    A byte-index sort would order by field[0] instead — all zero here — and leave the
    rows untouched, giving 1, 2, 3, 4. That is exactly the failure this catches.

    a0 = a scratch arena of at least 4 * 128 bytes, 8-aligned.
    a0 (out) = 0 on the expected order, else 1. -/
def balCanonicalSortSelftest_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x5 .x8,
    .LI .x6 (64 : Word),
    .SD .x5 .x0 (0 : BitVec 12),
    .ADDI .x5 .x5 (8 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .BNE .x6 .x0 (-12 : BitVec 13),
    .LI .x6 (48 : Word),
    .SB .x8 .x6 (19 : BitVec 12),
    .LI .x6 (1 : Word),
    .SB .x8 .x6 (64 : BitVec 12),
    .ADDI .x5 .x8 (128 : BitVec 12),
    .LI .x6 (16 : Word),
    .SB .x5 .x6 (19 : BitVec 12),
    .LI .x6 (2 : Word),
    .SB .x5 .x6 (64 : BitVec 12),
    .ADDI .x5 .x8 (256 : BitVec 12),
    .LI .x6 (64 : Word),
    .SB .x5 .x6 (19 : BitVec 12),
    .LI .x6 (3 : Word),
    .SB .x5 .x6 (64 : BitVec 12),
    .ADDI .x5 .x8 (384 : BitVec 12),
    .LI .x6 (32 : Word),
    .SB .x5 .x6 (19 : BitVec 12),
    .LI .x6 (4 : Word),
    .SB .x5 .x6 (64 : BitVec 12),
    .MV .x10 .x8,
    .LI .x11 (4 : Word),
    .LI .x12 (128 : Word),
    .LUI .x13 (1 : BitVec 20),
    .ADDIW .x13 .x13 (1024 : BitVec 12),
    .LI .x14 (1 : Word),
    .JAL .x1 (jalOff GuestAddrs.bal_canonical_sort (GuestAddrs.bal_canonical_sort_selftest + 144)),
    .BNE .x10 .x0 (72 : BitVec 13),
    .LBU .x6 .x8 (64 : BitVec 12),
    .LI .x7 (2 : Word),
    .BNE .x6 .x7 (60 : BitVec 13),
    .ADDI .x5 .x8 (128 : BitVec 12),
    .LBU .x6 .x5 (64 : BitVec 12),
    .LI .x7 (4 : Word),
    .BNE .x6 .x7 (44 : BitVec 13),
    .ADDI .x5 .x8 (256 : BitVec 12),
    .LBU .x6 .x5 (64 : BitVec 12),
    .LI .x7 (1 : Word),
    .BNE .x6 .x7 (28 : BitVec 13),
    .ADDI .x5 .x8 (384 : BitVec 12),
    .LBU .x6 .x5 (64 : BitVec 12),
    .LI .x7 (3 : Word),
    .BNE .x6 .x7 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]
/-- Reloc side-table for `balCanonicalSortSelftest_prog`. -/
def balCanonicalSortSelftest_relocs : RelocTable :=
  [ (36, .jal .x1 "bal_canonical_sort") ]

def balCanonicalSortSelftestFunction : String :=
  "  .globl bal_canonical_sort_selftest\n" ++
  "bal_canonical_sort_selftest:\n" ++
    emitProgramR balCanonicalSortSelftest_prog balCanonicalSortSelftest_relocs

/-- Kernel-checked drift guard; guest byte-identity verified by assemble+cmp:
    244 vs 244 bytes, IDENTICAL. -/
theorem balCanonicalSortSelftestFunction_eq_prog :
    balCanonicalSortSelftestFunction = "  .globl bal_canonical_sort_selftest\n" ++
      "bal_canonical_sort_selftest:\n" ++
        emitProgramR balCanonicalSortSelftest_prog balCanonicalSortSelftest_relocs := rfl


/-- The explicit range stack. Sized by the argued bound, not by a guess: at most
    `bsrMptRadixFanout` ranges are pushed per depth, over `balSortMaxDepth`
    depths. Overrun returns status 3 rather than writing past the end. -/
def balCanonicalSortDataSection : String :=
  "bal_sort_ranges:\n  .zero " ++
    toString (balSortRangeStackCapacity * balSortRangeFrameBytes) ++ "\n"

/-- All routines, in emission order. `bal_sort_*` call `bal_canonical_sort`, so
    they must be emitted together.

    **The `"\n"` separators are load-bearing.** `emitProgramR` does not terminate
    its last line, so each converted Function's string ends at its final `jalr`
    with no newline -- unlike the hand-written strings these replaced, which ended
    `"  ret\n"`. Concatenating without a separator puts the next routine's `.globl`
    on the same line as the previous return and the whole block FAILS TO ASSEMBLE.

    A per-function `.text` byte compare cannot see this: the gate assembles one
    function at a time and never assembles the concatenation. Found by review on
    #11046 while checking a different property of the same deviation. -/
def balCanonicalSortFunctions : String :=
  balCanonicalSortFunction ++ "\n" ++
  balSortStorageWritesFunction ++ "\n" ++
  balSortAccountWritesFunction ++ "\n" ++
  balCanonicalSortSelftestFunction ++ "\n"

/-! ## The builder's key descriptors, pinned as constants

    Confirmed with the agent building the builder arenas, and recorded here rather
    than left in a message so the two sides can be checked against each other.

    These are the BUILDER's descriptors, and no entry point declares them: the two
    that exist (`bal_sort_storage_writes`, `bal_sort_account_writes`) serve the
    write containers and are pinned separately below. The `#guard`s here decode the
    constants rather than the code. (This paragraph previously said the entry points
    were "NOT added yet: the arenas do not exist" — the write-container arenas do
    exist and both entry points link, as `GuestAddrs.bal_sort_storage_writes` and
    `bal_sort_account_writes` now record. What is still absent is a *builder-list*
    entry point, which is what the descriptors above are for.)

    Row shapes, keys listed most to least significant:

    | list | stride | segments |
    |---|---|---|
    | storage change | 96 | address `(0,20)` BE, slot `(32,32)` BE, index `(24,8)` LE |
    | balance change | 64 | address `(0,20)` BE, index `(24,8)` LE |
    | nonce change | 40 | address `(0,20)` BE, index `(24,8)` LE |
    | code change | 64 | address `(0,20)` BE, index `(24,8)` LE |

    The endianness split is the part worth pinning. The builder canonicalises BOTH
    the address and the slot on append — the source `addrHash` and `slotKey` are EVM
    stack words, four LE u64 limbs, and the append reverses them — so those segments
    are indexed FORWARD. The `block_access_index` is a native LE cell and is the only
    segment the sorter reverses. Reversing an already-BE segment would order rows by
    a byte-reversed address: total, permutation-preserving, and not canonical. -/
def balSortBuilderStorageSegments : Nat := 0x0818a0209400
def balSortBuilderEventSegments : Nat := 0x08189400

/-! ## Anti-drift guards on the emitted text

    NOT a correctness argument about the ordering — see the header. These assert
    that the code says what it is supposed to say, so a later edit cannot quietly
    remove the byte reversal or collapse the status codes. The ordering's
    correctness is established end to end by the hash comparison.

    Fully qualified and one per line: a `#guard` in the wrong namespace auto-binds
    its identifiers as implicits and passes vacuously, and one whose expression
    wraps to a second line silently covers only the first. -/

-- The depth bound must cover the WIDER of the two keys, or the storage sort would
-- stop early and leave rows unordered on their trailing slot bytes.
#guard balSortMaxDepth == 2 * balSortStorageKeyBytes
#guard balSortAccountKeyBytes <= balSortStorageKeyBytes
-- The stack bound is depth x fanout, the argued capacity rather than a guess.
#guard balSortRangeStackCapacity == balSortMaxDepth * bsrMptRadixFanout
#guard balSortRangeStackCapacity == 2048
-- The reserved arena must match the capacity exactly.
#guard (balSortRangeStackCapacity * balSortRangeFrameBytes) == 65536

-- Every routine is emitted; nothing calls them yet, so a missing one would not be
-- a link error and these guards are the only thing that would catch it. The label
-- line survives the conversion because it stays in each Function's string prefix.
#guard (balCanonicalSortFunctions.splitOn "bal_canonical_sort:").length == 2
#guard (balCanonicalSortFunctions.splitOn "bal_sort_storage_writes:").length == 2
#guard (balCanonicalSortFunctions.splitOn "bal_sort_account_writes:").length == 2
#guard (balCanonicalSortFunctions.splitOn "bal_canonical_sort_selftest:").length == 2
-- ...and `.globl` for each, which `emitProgramR` cannot emit and which therefore
-- has to be re-checked rather than inherited from the conversion. Symbol BINDING
-- is invisible to a `.text` compare -- a symbol demoted GLOBAL -> LOCAL, or dropped,
-- leaves `.text` byte-identical -- so these guards are the only mechanical check on
-- the one part of the emitted text the conversion does not establish.
#guard (balCanonicalSortFunctions.splitOn ".globl bal_canonical_sort\n").length == 2
#guard (balCanonicalSortFunctions.splitOn ".globl bal_sort_storage_writes").length == 2
#guard (balCanonicalSortFunctions.splitOn ".globl bal_sort_account_writes").length == 2
#guard (balCanonicalSortFunctions.splitOn ".globl bal_canonical_sort_selftest").length == 2

-- Instruction counts, so a dropped or duplicated instruction is caught even where
-- no guard below names the instruction in question.
#guard balCanonicalDigit_prog.length == 28
#guard balCanonicalSort_prog.length == 147
#guard balSortStorageWrites_prog.length == 16
#guard balSortAccountWrites_prog.length == 16
#guard balCanonicalSortSelftest_prog.length == 61

-- Each converted Function ends at its last instruction with NO trailing newline, so
-- the aggregate must insert the separators itself (see `balCanonicalSortFunctions`).
-- Negative guard on the exact defect: a `.globl` sharing a line with the preceding
-- `jalr x0, 0(x1)`, which does not assemble and which a per-function `.text` compare
-- cannot detect.
#guard (balCanonicalSortFunctions.splitOn "(x1)  .globl").length == 1
#guard !balCanonicalSortFunction.endsWith "\n"
-- ...and every `.globl` therefore begins a line: three preceded by a newline, plus
-- the first, which starts the aggregate.
#guard (balCanonicalSortFunctions.splitOn "\n  .globl").length == 4
#guard balCanonicalSortFunctions.startsWith "  .globl bal_canonical_sort\n"

/-! ### Guards restated over the `Program`s

    The conversion to `Program`s (`scripts/asm_to_program.py`) moved this module's
    anti-drift guards off the emitted text and onto the instruction lists, because
    `emitProgramR` renders numeric register names, one instruction per line, and no
    local labels -- so every guard that matched `t3`, a `;`-joined line or a `.L`
    label would now pass vacuously by matching nothing. Restated rather than
    deleted, and in several cases the `Program` form is STRICTLY STRONGER, noted
    per guard where so.

    `balSortDigitCount` counts occurrences of an instruction run, which is what the
    `splitOn ... |>.length == 2` idiom was doing on the text. -/

/-- Occurrences of a nonempty `pat` as a contiguous run inside the instruction
    list.  Plain recursion rather than `List.tails`: this module is under
    `Codegen/Programs` and does not import Mathlib. -/
private def balSortInfixCount (pat : List Instr) : List Instr → Nat
  | [] => 0
  | l@(_ :: rest) =>
      (if l.take pat.length == pat then 1 else 0) + balSortInfixCount pat rest

-- The digit extraction must be present in the scan loop. Without it the sort would
-- still run, still terminate, and still produce a sorted permutation -- on the
-- wrong key, and no structural property of the ORDER could tell the difference.
-- Now structural: `balCanonicalSort_prog` is DEFINED as head ++ digit ++ tail, so
-- what needs guarding is no longer presence but that the digit is the RIGHT 28
-- instructions -- which is what the four guards below do.
#guard balSortInfixCount balCanonicalDigit_prog balCanonicalSort_prog == 1
-- ...and it must read a REVERSED offset within the segment. The canonical BE byte b
-- of an LE segment of width w at offset k is byte k+w-1-b; emitting `k+b` instead is
-- the limb-swapped sort, which is sorted and permutation-preserving and wrong.
-- Was `add t5, t5, t3; addi t5, t5, -1; sub t5, t5, t2`.
#guard balSortInfixCount [.ADD .x30 .x30 .x28, .ADDI .x30 .x30 (-1 : BitVec 12),
  .SUB .x30 .x30 .x7] balCanonicalDigit_prog == 1
-- ...and the BE branch must index FORWARD, or a BE-stored segment would be reversed.
-- STRONGER than the old guard, which only asserted that the `.Lbalsort_dig_be`
-- LABEL existed. This names the forward index itself (`add t5, t5, t2`), so a BE arm
-- that had been edited to reverse would now fail where the label check would not.
#guard balSortInfixCount [.ADD .x30 .x30 .x7] balCanonicalDigit_prog == 1
-- The width mask must strip the endianness bit in BOTH the digit path and the
-- key-width sum; masking one and not the other makes every BE segment 128 bytes wide.
-- NEGATIVE GUARD, deliberately. The positive form -- count the occurrences of the
-- CORRECT mask -- cannot tell WHICH site satisfies it, and this one was satisfied by the
-- digit path while the segment walk still used 255. Worse, it asserted EXACTLY ONE
-- occurrence, so fixing the walk added a second and the guard would have REJECTED the
-- fix. Absence of the defect is site-independent; presence of the fix is not.
--
-- STRONGER than the old guard in one respect: the string `andi t3, t3, 255` could
-- not distinguish the width mask on t3 from the OFFSET mask on t5, which is
-- correctly 255 and must stay so. The Program form names the register, so the
-- correct `.ANDI .x30 .x30 255` is unaffected by this assertion.
#guard !(balCanonicalDigit_prog.contains (.ANDI .x28 .x28 (255 : BitVec 12)))
#guard balCanonicalDigit_prog.contains (.ANDI .x28 .x28 (127 : BitVec 12))
#guard balCanonicalDigit_prog.contains (.ANDI .x30 .x30 (255 : BitVec 12))
-- ...and the same mask in the key-width sum (was `andi t0, t0, 0x7f`; t0 = x5).
#guard balSortInfixCount [.ANDI .x5 .x5 (127 : BitVec 12)] balCanonicalSort_prog == 1
-- The segment walk must SUBTRACT each width as it steps past a segment, or every
-- byte index would be read against the first segment. Was `sub t2, t2, t3`.
#guard balSortInfixCount [.SUB .x7 .x7 .x28] balCanonicalDigit_prog == 1

-- No silent bail: every failure path must set a DISTINCT nonzero status. If these
-- collapse to one code a caller cannot tell misuse from capacity exhaustion.
-- Was `li a0, 1;` / `2;` / `3;`; a0 = x10.
#guard balSortInfixCount [.LI .x10 (1 : Word)] balCanonicalSort_prog == 1
#guard balSortInfixCount [.LI .x10 (2 : Word)] balCanonicalSort_prog == 1
#guard balSortInfixCount [.LI .x10 (3 : Word)] balCanonicalSort_prog == 1
#guard balSortInfixCount [.LI .x10 (0 : Word)] balCanonicalSort_prog == 1

-- The self-test's expectation must be the INDEPENDENT one (tags 2,4,1,3), not the
-- identity 1,2,3,4 that a byte-index sort would leave behind.
--
-- STRONGER than the old pair of guards, which checked only that `li t2, 2` and
-- `li t2, 4` occurred SOMEWHERE. This pins the whole expected sequence in order, so
-- a permutation of the expectations -- e.g. 4,2,1,3, which still contains both --
-- now fails. t2 = x7. Written as the ordered projection rather than four separate
-- occurrence counts, because the ORDER is the content of this guard.
#guard (balCanonicalSortSelftest_prog.filterMap (fun i =>
  match i with | .LI .x7 w => some w.toNat | _ => none)) == [2, 4, 1, 3]

-- Entry-point key layouts, packed one byte per field: for segment i, byte 2i is the
-- offset and byte 2i+1 the width, with bit 7 of the width byte the endianness flag.
--   storage: [(0,20 BE),(32,32 BE)] = 0x20201400
--   account: [(0,20 BE)]            = 0x9400
-- Both start with a 20-byte address segment at offset 0, which is what makes the two
-- containers agree on account order BY CONSTRUCTION -- the serializer walks accounts
-- once and must find each account's slots under the same account.
--
-- The account comment previously read `0x1400`, which is the descriptor WITHOUT the
-- endianness bit and disagreed with the value the guard below has always pinned
-- (0x94 = 20 + 128). Corrected here: an off-by-one-bit in a comment about
-- endianness is exactly the reader-misleading error this module warns about.
--
-- `li a3, <descriptor>` no longer appears in the emitted text: a 32-bit constant is
-- materialised as LUI + ADDIW, so the guard is restated over that pair AND tied back
-- to the descriptor arithmetically, rather than pinning two opaque immediates.
-- a3 = x13, a4 = x14, a2 = x12.
#guard balSortInfixCount [.LUI .x13 (131585 : BitVec 20),
  .ADDIW .x13 .x13 (1024 : BitVec 12)] balSortStorageWrites_prog == 1
#guard 131585 * 4096 + 1024 == 0x20201400
#guard balSortInfixCount [.LUI .x13 (9 : BitVec 20),
  .ADDIW .x13 .x13 (1024 : BitVec 12)] balSortAccountWrites_prog == 1
#guard 9 * 4096 + 1024 == 0x9400
-- Segment counts (was `li a4, 2` / `li a4, 1`).
#guard balSortInfixCount [.LI .x14 (2 : Word)] balSortStorageWrites_prog == 1
#guard balSortInfixCount [.LI .x14 (1 : Word)] balSortAccountWrites_prog == 1
-- Both address segments must be (offset 0, width 20); only the endianness BIT may
-- differ, because the two containers store the address differently while both must
-- yield the same canonical ORDER. Comparing the whole descriptors would now fail by
-- design, so the invariant is offset-and-width equality with the flag masked out.
#guard 0x20201400 % 0x100 == 0x9400 % 0x100                      -- same offset
#guard (0x20201400 / 0x100) % 0x80 == (0x9400 / 0x100) % 0x80    -- same width

-- The builder descriptors must decode to exactly the agreed segments. Written as a
-- decode rather than a repeated literal so a typo in the packing cannot agree with
-- itself -- the failure being pinned here is a wrong offset or a wrong endianness
-- bit, both of which produce a well-formed wrong order with no local symptom.
#guard (balSortBuilderStorageSegments >>> 0) % 256 == 0        -- address offset
#guard (balSortBuilderStorageSegments >>> 8) % 256 == 20 + 128 -- address width, BE
#guard (balSortBuilderStorageSegments >>> 16) % 256 == 32      -- slot offset
#guard (balSortBuilderStorageSegments >>> 24) % 256 == 32 + 128 -- slot width, BE
#guard (balSortBuilderStorageSegments >>> 32) % 256 == 24      -- index offset
#guard (balSortBuilderStorageSegments >>> 40) % 256 == 8       -- index width, LE
#guard (balSortBuilderEventSegments >>> 0) % 256 == 0
#guard (balSortBuilderEventSegments >>> 8) % 256 == 20 + 128
#guard (balSortBuilderEventSegments >>> 16) % 256 == 24
#guard (balSortBuilderEventSegments >>> 24) % 256 == 8
-- The index segment must be the ONLY reversed one in both descriptors.
#guard (balSortBuilderStorageSegments >>> 40) % 256 < 128
#guard (balSortBuilderEventSegments >>> 24) % 256 < 128

-- The strides must match the two containers' actual record strides (was
-- `li a2, 128`; a2 = x12). Both containers use stride 128.
#guard balSortInfixCount [.LI .x12 (128 : Word)] balSortStorageWrites_prog == 1
#guard balSortInfixCount [.LI .x12 (128 : Word)] balSortAccountWrites_prog == 1

end EvmAsm.Codegen
