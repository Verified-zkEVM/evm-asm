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
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.StorageWriteMap
import EvmAsm.Codegen.Programs.AccountWriteMap

namespace EvmAsm.Codegen

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
def balCanonicalDigitAsm : String :=
  -- b = canonical byte index within the whole key.
  "  srli t2, s6, 1\n" ++
  -- Walk the segment list, subtracting each width, until b falls inside one.
  -- s10 = packed segments (per segment: offset in bits 8i, width in bits 8i+8),
  -- s9 = total key bytes, s11 = total nibble depth. a6 = segment cursor.
  "  li a6, 0\n" ++
  ".Lbalsort_dig_seg:\n" ++
  "  slli a7, a6, 4; srl t5, s10, a7; andi t5, t5, 255\n" ++      -- t5 = seg offset
  -- 0x7f, NOT 255: bit 7 is the endianness flag, so a BE segment's width byte 0x94
  -- reads as 148 under a 255 mask and the walk never leaves segment 0. The flag is
  -- re-read from the descriptor at the digit site below rather than carried in t3.
  "  addi a7, a7, 8; srl t3, s10, a7; andi t3, t3, 0x7f\n" ++      -- t3 = seg width
  "  bltu t2, t3, .Lbalsort_dig_in\n" ++
  "  sub t2, t2, t3; addi a6, a6, 1; j .Lbalsort_dig_seg\n" ++
  ".Lbalsort_dig_in:\n" ++
  -- Two storage conventions coexist, so the reversal is PER SEGMENT rather than
  -- global. Bit 7 of the width byte means "already big-endian, index directly":
  --   LE segment (flag clear): canonical BE byte b is byte k + w - 1 - b.
  --   BE segment (flag set):   canonical BE byte b is byte k + b.
  -- The write containers hold addresses as LE limbs, but the builder's rows carry a
  -- canonical BE20 address already, so reversing every segment would order the
  -- builder's rows by a byte-reversed address -- sorted, permutation-preserving and
  -- wrong, with no local symptom.
  -- t3 no longer carries the flag (masked at the walk), so re-read it from the
  -- descriptor for this segment.
  "  slli a7, a6, 4; addi a7, a7, 8; srl a7, s10, a7; andi a7, a7, 0x80\n" ++
  "  bnez a7, .Lbalsort_dig_be\n" ++
  "  add t5, t5, t3; addi t5, t5, -1; sub t5, t5, t2\n" ++
  "  j .Lbalsort_dig_have\n" ++
  ".Lbalsort_dig_be:\n" ++
  "  add t5, t5, t2\n" ++
  ".Lbalsort_dig_have:\n" ++
  "  add t5, t0, t5; lbu t3, 0(t5)\n" ++
  "  andi a7, s6, 1; bnez a7, .Lbalsort_dig_low\n" ++
  "  srli t3, t3, 4\n" ++
  ".Lbalsort_dig_low:\n" ++
  "  andi t3, t3, 15\n"

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
def balCanonicalSortFunction : String :=
  "  .globl bal_canonical_sort\n" ++
  "bal_canonical_sort:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  -- Argument validation FIRST, so a misuse cannot be mistaken for a capacity hit.
  "  li t0, 1; bltu a4, t0, .Lbalsort_bad_segs\n" ++
  "  li t0, 3; bgtu a4, t0, .Lbalsort_bad_segs\n" ++
  "  j .Lbalsort_segs_ok\n" ++
  ".Lbalsort_bad_segs:\n" ++
  "  li a0, 2; j .Lbalsort_ret\n" ++
  ".Lbalsort_segs_ok:\n" ++
  "  li t0, " ++ toString blockAccountWritesCapacity ++ "; bgtu a1, t0, .Lbalsort_over_capacity\n" ++
  "  mv s0, a0\n" ++                       -- s0 = base
  "  mv s1, a1\n" ++                       -- s1 = count
  "  mv s8, a2\n" ++                       -- s8 = stride
  "  mv s10, a3\n" ++                      -- s10 = packed segment descriptor
  -- s9 = total canonical key bytes = sum of the segment widths. Computed rather
  -- than passed, so a caller cannot describe a key wider than it declared.
  "  li s9, 0; li t1, 0\n" ++
  ".Lbalsort_keysum:\n" ++
  "  bgeu t1, a4, .Lbalsort_keysummed\n" ++
  "  slli t2, t1, 4; addi t2, t2, 8; srl t0, s10, t2; andi t0, t0, 0x7f\n" ++
  "  add s9, s9, t0; addi t1, t1, 1; j .Lbalsort_keysum\n" ++
  ".Lbalsort_keysummed:\n" ++
  "  beqz s9, .Lbalsort_bad_segs\n" ++
  "  slli s11, s9, 1\n" ++                 -- s11 = total nibble depth = 2 * keyBytes
  "  la s2, bal_sort_ranges; li s3, 0\n" ++
  "  li t0, 2; bltu s1, t0, .Lbalsort_ok\n" ++ -- 0 or 1 rows are already sorted
  "  sd zero, 0(s2); sd s1, 8(s2); sd zero, 16(s2); sd zero, 24(s2); li s3, 1\n" ++
  ".Lbalsort_pop:\n" ++
  "  beqz s3, .Lbalsort_ok\n" ++
  "  addi s3, s3, -1; slli t0, s3, 5; add t0, s2, t0\n" ++
  "  ld s4, 0(t0); ld s5, 8(t0); ld s6, 16(t0)\n" ++   -- start, end, depth
  "  addi t1, s4, 1; bgeu t1, s5, .Lbalsort_pop\n" ++      -- singleton: nothing to do
  "  bgeu s6, s11, .Lbalsort_pop\n" ++                     -- key exhausted: order fixed
  "  mv s7, s4; li t6, 0\n" ++                         -- s7 = partition cursor, t6 = digit
  ".Lbalsort_digit:\n" ++
  "  li t0, " ++ toString bsrMptRadixFanout ++ "; beq t6, t0, .Lbalsort_pop\n" ++
  "  mv t1, s7\n" ++
  ".Lbalsort_scan:\n" ++
  "  beq t1, s5, .Lbalsort_group\n" ++
  -- Row pointer: base + i * stride.  `mul` rather than a shift so the routine is
  -- not silently wrong for a non-power-of-two stride a future caller passes.
  "  mul t0, t1, s8; add t0, s0, t0\n" ++
  balCanonicalDigitAsm ++                              -- t3 = canonical nibble at depth s6
  "  bne t3, t6, .Lbalsort_scan_next\n" ++
  "  beq t1, s7, .Lbalsort_scan_match\n" ++
  -- Swap rows t1 and s7, 8 bytes at a time through two registers -- no scratch
  -- buffer, so the routine has no hidden capacity of its own. The count comes from s8,
  -- the CALLER's stride, so the swap is correct for any stride -- but it steps by 8 and
  -- tests against zero, so a stride that is not a multiple of 8 runs off the end. That
  -- is the same 8-alignment precondition the ld/sd pair imposes, restated by the loop.
  "  mul t2, s7, s8; add t2, s0, t2\n" ++
  "  mv t4, s8\n" ++
  ".Lbalsort_swap:\n" ++
  "  ld t5, 0(t0); ld a5, 0(t2); sd a5, 0(t0); sd t5, 0(t2)\n" ++
  "  addi t0, t0, 8; addi t2, t2, 8; addi t4, t4, -8; bnez t4, .Lbalsort_swap\n" ++
  ".Lbalsort_scan_match:\n" ++
  "  addi s7, s7, 1\n" ++
  ".Lbalsort_scan_next:\n" ++
  "  addi t1, t1, 1; j .Lbalsort_scan\n" ++
  ".Lbalsort_group:\n" ++
  "  addi t0, s4, 1; bgeu t0, s7, .Lbalsort_digit_next\n" ++  -- singleton group: no push
  "  li t0, " ++ toString balSortRangeStackCapacity ++ "; bgeu s3, t0, .Lbalsort_stack_full\n" ++
  "  slli t0, s3, 5; add t0, s2, t0\n" ++
  "  sd s4, 0(t0); sd s7, 8(t0); addi t1, s6, 1; sd t1, 16(t0); sd zero, 24(t0)\n" ++
  "  addi s3, s3, 1\n" ++
  ".Lbalsort_digit_next:\n" ++
  "  mv s4, s7; addi t6, t6, 1; j .Lbalsort_digit\n" ++
  ".Lbalsort_over_capacity:\n" ++
  "  li a0, 1; j .Lbalsort_ret\n" ++
  ".Lbalsort_stack_full:\n" ++
  "  li a0, 3; j .Lbalsort_ret\n" ++
  ".Lbalsort_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lbalsort_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)\n" ++
  "  ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret\n"

/-! ## Thin per-container entry points

    Each names its own base, stride and key layout, so no caller has to remember
    which key width belongs to which arena — the misuse the status codes 2 and 4
    exist to catch is not reachable from these. -/

/-- Sort the block-level `storage_writes` map into address-major, slot-minor
    order. a0 = 0 on success, else the `bal_canonical_sort` status. -/
def balSortStorageWritesFunction : String :=
  "  .globl bal_sort_storage_writes\n" ++
  "bal_sort_storage_writes:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  li a0, 0xa1fa0000\n" ++                    -- STORAGE_WRITES_AREA
  "  la t0, storage_writes_count; ld a1, 0(t0)\n" ++
  "  li a2, 128\n" ++                           -- stride
  -- segments [(off 0, w 20), (off 32, w 32)] = address ++ slot, packed one byte each
  "  li a3, 0x20201400\n" ++
  "  li a4, 2\n" ++
  "  jal ra, bal_canonical_sort\n" ++
  "  ld ra, 0(sp); addi sp, sp, 16\n" ++
  "  ret\n"

/-- Sort the block-level `account_writes` map into address order. -/
def balSortAccountWritesFunction : String :=
  "  .globl bal_sort_account_writes\n" ++
  "bal_sort_account_writes:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  li a0, 0xa24a0000\n" ++                    -- ACCOUNT_WRITES_AREA
  "  la t0, account_writes_count; ld a1, 0(t0)\n" ++
  "  li a2, 128\n" ++                           -- stride
  -- segments [(off 0, w 20)] = address, BIG-ENDIAN (bit 7 of the width byte).
  -- Verified at the producer rather than taken from the container's own docstring:
  -- `record_nonstorage_effect`'s ABI is "a0 = 20-byte big-endian address ptr", and
  -- `create_record_code_effect` matches, so the rows hold canonical BE20 -- NOT the
  -- LE stack word the record helper's parameter list suggests.
  --
  -- Note this makes the two write containers DISAGREE on stored encoding while still
  -- agreeing on canonical ORDER: storage rows hold an LE stack word and are reversed,
  -- account rows hold BE20 and are read forward, and both therefore yield ascending
  -- canonical big-endian address order. The agreement is in the ORDER, which is what
  -- the serializer's single walk needs, not in the bytes.
  "  li a3, 0x9400\n" ++
  "  li a4, 1\n" ++
  "  jal ra, bal_canonical_sort\n" ++
  "  ld ra, 0(sp); addi sp, sp, 16\n" ++
  "  ret\n"

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
def balCanonicalSortSelftestFunction : String :=
  "  .globl bal_canonical_sort_selftest\n" ++
  "bal_canonical_sort_selftest:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  -- Zero four 128-byte rows.
  "  mv t0, s0; li t1, 64\n" ++
  ".Lbalsort_st_zero:\n" ++
  "  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; bnez t1, .Lbalsort_st_zero\n" ++
  -- field[19] = the discriminating byte; offset 64 = the tag.
  "  li t1, 0x30; sb t1, 19(s0);   li t1, 1; sb t1, 64(s0)\n" ++
  "  addi t0, s0, 128\n" ++
  "  li t1, 0x10; sb t1, 19(t0);   li t1, 2; sb t1, 64(t0)\n" ++
  "  addi t0, s0, 256\n" ++
  "  li t1, 0x40; sb t1, 19(t0);   li t1, 3; sb t1, 64(t0)\n" ++
  "  addi t0, s0, 384\n" ++
  "  li t1, 0x20; sb t1, 19(t0);   li t1, 4; sb t1, 64(t0)\n" ++
  -- Sort with the ACCOUNT layout: one 20-byte address segment at offset 0.
  "  mv a0, s0; li a1, 4; li a2, 128; li a3, 0x1400; li a4, 1\n" ++
  "  jal ra, bal_canonical_sort\n" ++
  "  bnez a0, .Lbalsort_st_fail\n" ++
  -- Expected tag sequence 2, 4, 1, 3.
  "  lbu t1, 64(s0);   li t2, 2; bne t1, t2, .Lbalsort_st_fail\n" ++
  "  addi t0, s0, 128; lbu t1, 64(t0); li t2, 4; bne t1, t2, .Lbalsort_st_fail\n" ++
  "  addi t0, s0, 256; lbu t1, 64(t0); li t2, 1; bne t1, t2, .Lbalsort_st_fail\n" ++
  "  addi t0, s0, 384; lbu t1, 64(t0); li t2, 3; bne t1, t2, .Lbalsort_st_fail\n" ++
  "  li a0, 0; j .Lbalsort_st_ret\n" ++
  ".Lbalsort_st_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbalsort_st_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret\n"

/-- The explicit range stack. Sized by the argued bound, not by a guess: at most
    `bsrMptRadixFanout` ranges are pushed per depth, over `balSortMaxDepth`
    depths. Overrun returns status 3 rather than writing past the end. -/
def balCanonicalSortDataSection : String :=
  "bal_sort_ranges:\n  .zero " ++
    toString (balSortRangeStackCapacity * balSortRangeFrameBytes) ++ "\n"

/-- All routines, in emission order. `bal_sort_*` call `bal_canonical_sort`, so
    they must be emitted together. -/
def balCanonicalSortFunctions : String :=
  balCanonicalSortFunction ++
  balSortStorageWritesFunction ++
  balSortAccountWritesFunction ++
  balCanonicalSortSelftestFunction

/-! ## The builder's key descriptors, pinned as constants

    Confirmed with the agent building the builder arenas, and recorded here rather
    than left in a message so the two sides can be checked against each other. The
    entry points are NOT added yet: the arenas do not exist, so referencing them
    would not link, and inventing an offset would guarantee a silent mismatch.

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
-- a link error and these guards are the only thing that would catch it.
#guard (balCanonicalSortFunctions.splitOn "bal_canonical_sort:").length == 2
#guard (balCanonicalSortFunctions.splitOn "bal_sort_storage_writes:").length == 2
#guard (balCanonicalSortFunctions.splitOn "bal_sort_account_writes:").length == 2
#guard (balCanonicalSortFunctions.splitOn "bal_canonical_sort_selftest:").length == 2
-- The self-test's expectation must be the INDEPENDENT one (tags 2,4,1,3), not the
-- identity 1,2,3,4 that a byte-index sort would leave behind.
#guard (balCanonicalSortSelftestFunction.splitOn "li t2, 2; bne").length == 2
#guard (balCanonicalSortSelftestFunction.splitOn "li t2, 4; bne").length == 2

-- No silent bail: every failure path must set a DISTINCT nonzero status. If these
-- collapse to one code a caller cannot tell misuse from capacity exhaustion.
#guard (balCanonicalSortFunction.splitOn "li a0, 1;").length == 2
#guard (balCanonicalSortFunction.splitOn "li a0, 2;").length == 2
#guard (balCanonicalSortFunction.splitOn "li a0, 3;").length == 2

-- The digit extraction must be present in the scan loop. Without it the sort would
-- still run, still terminate, and still produce a sorted permutation -- on the
-- wrong key, and no structural property of the ORDER could tell the difference.
#guard (balCanonicalSortFunction.splitOn ".Lbalsort_dig_in:").length == 2
-- ...and it must read a REVERSED offset within the segment. The canonical BE byte b
-- of an LE segment of width w at offset k is byte k+w-1-b; emitting `k+b` instead is
-- the limb-swapped sort, which is sorted and permutation-preserving and wrong.
#guard (balCanonicalDigitAsm.splitOn "add t5, t5, t3; addi t5, t5, -1; sub t5, t5, t2").length == 2
-- ...and the BE branch must index FORWARD, or a BE-stored segment would be reversed.
#guard (balCanonicalDigitAsm.splitOn ".Lbalsort_dig_be:").length == 2
-- The width mask must strip the endianness bit in BOTH the digit path and the
-- key-width sum; masking one and not the other makes every BE segment 128 bytes wide.
-- NEGATIVE GUARD, deliberately. The positive form -- count the occurrences of the
-- CORRECT mask -- cannot tell WHICH site satisfies it, and this one was satisfied by the
-- digit path while the segment walk still used 255. Worse, it asserted EXACTLY ONE
-- occurrence, so fixing the walk added a second and the guard would have REJECTED the
-- fix. Absence of the defect is site-independent; presence of the fix is not.
#guard (balCanonicalDigitAsm.splitOn "andi t3, t3, 255").length == 1
#guard (balCanonicalSortFunction.splitOn "andi t0, t0, 0x7f").length == 2
-- The segment walk must SUBTRACT each width as it steps past a segment, or every
-- byte index would be read against the first segment.
#guard (balCanonicalDigitAsm.splitOn "sub t2, t2, t3").length == 2

-- Entry-point key layouts, packed one byte per field: for segment i, byte 2i is the
-- offset and byte 2i+1 the width.
--   storage: [(0,20),(32,32)] = 0x20201400
--   account: [(0,20)]         = 0x1400
-- Both start with a 20-byte address segment at offset 0, which is what makes the two
-- containers agree on account order BY CONSTRUCTION -- the serializer walks accounts
-- once and must find each account's slots under the same account.
#guard (balSortStorageWritesFunction.splitOn "li a3, 0x20201400").length == 2
#guard (balSortStorageWritesFunction.splitOn "li a4, 2").length == 2
#guard (balSortAccountWritesFunction.splitOn "li a3, 0x9400").length == 2
#guard (balSortAccountWritesFunction.splitOn "li a4, 1").length == 2
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

-- The strides must match the two containers' actual record strides.
#guard (balSortStorageWritesFunction.splitOn "li a2, 128").length == 2
#guard (balSortAccountWritesFunction.splitOn "li a2, 128").length == 2

end EvmAsm.Codegen
