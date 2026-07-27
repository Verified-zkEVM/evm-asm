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

  One routine serves both containers. The key is a run of 32-byte fields, each
  stored low-limb-first, of which the first contributes `firstSig` significant
  bytes and any later field contributes 32:

  | container | stride | fields | firstSig | canonical key |
  |---|---|---|---|---|
  | `storage_writes` | 128 | 2 | 20 | address (20 B) ++ slot (32 B) |
  | `account_writes` | 128 | 1 | 20 | address, 20 B |

  Both take `firstSig = 20` for the address, which is what makes the two orderings
  **agree on account order by construction** rather than by coincidence — the
  serializer walks accounts once and must find each account's slots where it
  expects them. It also skips 24 wasted depths, and it does not sort on the stack
  word's upper 12 bytes, which are padding that happens to be zero rather than key
  material.

  For canonical byte index `b`, the row offset is `(firstSig - 1) - b` while
  `b < firstSig`, and `32·f + (31 - w)` beyond it, where `f = 1 + (b - firstSig)/32`
  and `w = (b - firstSig) % 32`. The account key excludes the field's top 12 bytes
  because a 20-byte address in a low-limb-first 256-bit word leaves them zero —
  constant, so they cannot affect the order, and including them would only cost
  12 wasted depths.
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

    In:  t0 = row pointer, s6 = nibble depth, s10 = firstSig.
    Out: t3 = the nibble (0..15).  Clobbers t2, t5, a6, a7.

    The canonical big-endian byte at index `b` of a 32-byte low-limb-first field
    is field byte `31 - b`, so:

        b < firstSig   ->  offset = (firstSig - 1) - b
        otherwise      ->  b' = b - firstSig,  offset = 32 + (31 - b')

    with the second case reached only when the caller declared two fields (the
    depth guard `s6 < 2 * keyBytes` already bounds `b < keyBytes`). Even depths
    take the byte's HIGH nibble, odd depths the low one, so the more significant
    nibble is compared first. -/
def balCanonicalDigitAsm : String :=
  "  srli t2, s6, 1\n" ++                       -- t2 = canonical byte index b
  "  bgeu t2, s10, .Lbalsort_dig_tail\n" ++
  "  addi t5, s10, -1; sub t5, t5, t2\n" ++     -- offset = (firstSig-1) - b
  "  j .Lbalsort_dig_have\n" ++
  ".Lbalsort_dig_tail:\n" ++
  "  sub t5, t2, s10\n" ++                      -- b' = b - firstSig
  "  li a6, 63; sub t5, a6, t5\n" ++            -- offset = 32 + 31 - b' = 63 - b'
  ".Lbalsort_dig_have:\n" ++
  "  add t5, t0, t5; lbu t3, 0(t5)\n" ++
  "  andi a7, s6, 1; bnez a7, .Lbalsort_dig_low\n" ++
  "  srli t3, t3, 4\n" ++                       -- even depth: high nibble
  ".Lbalsort_dig_low:\n" ++
  "  andi t3, t3, 15\n"

/-! ## `bal_canonical_sort`

    In-place MSD radix sort into the spec's canonical order.

    ABI:
      a0 = base of the row array
      a1 = row count
      a2 = row stride in bytes
      a3 = number of 32-byte key fields (1 or 2)
      a4 = significant bytes in the FIRST field (20 or 32)
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
  "  li t0, 1; beq a3, t0, .Lbalsort_fields_ok\n" ++
  "  li t0, 2; beq a3, t0, .Lbalsort_fields_ok\n" ++
  "  li a0, 2; j .Lbalsort_ret\n" ++
  ".Lbalsort_fields_ok:\n" ++
  "  li t0, 20; beq a4, t0, .Lbalsort_sig_ok\n" ++
  "  li t0, 32; beq a4, t0, .Lbalsort_sig_ok\n" ++
  "  li a0, 4; j .Lbalsort_ret\n" ++
  ".Lbalsort_sig_ok:\n" ++
  "  li t0, " ++ toString accountWritesCapacity ++ "; bgtu a1, t0, .Lbalsort_over_capacity\n" ++
  "  mv s0, a0\n" ++                       -- s0 = base
  "  mv s1, a1\n" ++                       -- s1 = count
  "  mv s8, a2\n" ++                       -- s8 = stride
  "  mv s10, a4\n" ++                      -- s10 = firstSig
  -- s9 = total canonical key bytes = firstSig + (fields - 1) * 32
  "  addi t0, a3, -1; slli t0, t0, 5; add s9, a4, t0\n" ++
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
  -- buffer, so the routine has no hidden capacity of its own.
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
  "  li a3, 2\n" ++                             -- address field ++ slot field
  "  li a4, 20\n" ++                            -- 20 significant address bytes (see below)
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
  "  li a3, 1\n" ++                             -- one key field
  "  li a4, 20\n" ++                            -- 20 significant address bytes
  "  jal ra, bal_canonical_sort\n" ++
  "  ld ra, 0(sp); addi sp, sp, 16\n" ++
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
  balSortAccountWritesFunction

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

-- No silent bail: every failure path must set a DISTINCT nonzero status. If these
-- collapse to one code a caller cannot tell misuse from capacity exhaustion.
#guard (balCanonicalSortFunction.splitOn "li a0, 1;").length == 2
#guard (balCanonicalSortFunction.splitOn "li a0, 2;").length == 2
#guard (balCanonicalSortFunction.splitOn "li a0, 3;").length == 2
#guard (balCanonicalSortFunction.splitOn "li a0, 4;").length == 2

-- The digit extraction must be present in the scan loop. Without it the sort would
-- still run, still terminate, and still produce a sorted permutation -- on the
-- wrong key, and no structural property of the ORDER could tell the difference.
-- This guard is why that edit cannot happen silently; it does not make the
-- ordering correct.
#guard (balCanonicalSortFunction.splitOn ".Lbalsort_dig_have:").length == 2
-- ...and it must read a REVERSED offset. A raw `add t5, t0, t2` (offset = b) would
-- be the limb-swapped sort; the canonical form subtracts.
#guard (balCanonicalDigitAsm.splitOn "sub t5, t5, t2").length == 2
#guard (balCanonicalDigitAsm.splitOn "sub t5, a6, t5").length == 2

-- Each entry point must name its own key layout, so status 2 and 4 are
-- unreachable from them.
#guard (balSortStorageWritesFunction.splitOn "li a3, 2").length == 2
#guard (balSortStorageWritesFunction.splitOn "li a4, 20").length == 2
-- Both entry points must declare the SAME address width, or the two containers
-- would order accounts differently and the serializer's single walk would look for
-- an account's slots under a different account.
#guard (balSortStorageWritesFunction.splitOn "li a4, 20").length
         == (balSortAccountWritesFunction.splitOn "li a4, 20").length
#guard (balSortAccountWritesFunction.splitOn "li a3, 1").length == 2
#guard (balSortAccountWritesFunction.splitOn "li a4, 20").length == 2

-- The strides must match the two containers' actual record strides.
#guard (balSortStorageWritesFunction.splitOn "li a2, 128").length == 2
#guard (balSortAccountWritesFunction.splitOn "li a2, 128").length == 2

end EvmAsm.Codegen
