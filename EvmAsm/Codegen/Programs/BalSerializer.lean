import EvmAsm.Codegen.Programs.BalRlpEncode
import EvmAsm.Codegen.Programs.BalCapacities

/-!
# BAL serializer: the measure and emit passes

Split out of `BlockAccessListBuilder.lean`, which crossed the 1500-line cap for
`Codegen/Programs`. The boundary is the one the code already had: this file holds the
routines that READ builder rows and produce RLP; the builder file keeps the arenas, the
row layouts and the append/upsert producers.

The guards stay with `blockAccessListBuilderFunctions` in the builder file, because they
assert properties of the CONCATENATED guest text rather than of these definitions alone.
-/

namespace EvmAsm.Codegen

/-! ## `bal_serializer_addr_matches` / `bal_serializer_slot_written`

    Two leaves the read filter needs. Split out so the filter reads as the spec's loop
    rather than as three nested scans.

    `bal_serializer_addr_matches`: does a read row belong to this account?
      a0 = address ptr (20 B BE)   a1 = read row ptr (addrHash at +0, 32 B stack word)
      a0 (out) = 1 on match, 0 otherwise

    The read row's key is a 32-byte EVM stack word and the account address is canonical
    BE20 — the same encoding split the sort descriptors already record, storage rows
    holding a stack word while account rows hold BE20. So the comparison reverses the
    row's low 20 bytes rather than comparing the two forms directly.

    `bal_serializer_slot_written`: does this account also have a storage CHANGE for this
    slot?
      a0 = slot ptr (32 B, as stored in the read row)   a1 = address ptr (20 B BE)
      a0 (out) = 1 if a change row matches (address, slot), 0 otherwise

    A hit means the spec drops the read (`:545-546`). Matching on BOTH address and slot
    is what makes the exclusion per-account: the same slot written by a different
    account must not suppress this account's read. -/
def balSerializerAddrMatchesFunction : String :=
  "bal_serializer_addr_matches:\n" ++
  "  li t0, 20; li t1, 0\n" ++
  -- BE20 byte i of the address vs byte (19 - i) of the reversed stack word, i.e.
  -- row byte i counted from the word's low end.
  ".Lbsam_cmp:\n" ++
  "  beq t1, t0, .Lbsam_yes\n" ++
  "  add t2, a0, t1\n" ++
  "  li t3, 19; sub t3, t3, t1; add t3, a1, t3\n" ++
  "  lbu t4, 0(t2); lbu t5, 0(t3); bne t4, t5, .Lbsam_no\n" ++
  "  addi t1, t1, 1; j .Lbsam_cmp\n" ++
  ".Lbsam_yes:\n" ++
  "  li a0, 1; ret\n" ++
  ".Lbsam_no:\n" ++
  "  li a0, 0; ret\n"

def balSerializerSlotWrittenFunction : String :=
  "bal_serializer_slot_written:\n" ++
  "  addi sp, sp, -32; sd ra, 0(sp); sd a0, 8(sp); sd a1, 16(sp)\n" ++
  "  la t0, bal_builder_storage_change_count; ld t1, 0(t0)\n" ++
  "  li t3, 0\n" ++
  ".Lbssw_scan:\n" ++
  "  bgeu t3, t1, .Lbssw_no\n" ++
  "  li t0, 96; mul t2, t3, t0; la t4, bal_builder_storage_changes; add t4, t4, t2\n" ++
  -- slot at +32 of the change row, 4 dwords, against the read row's slot
  -- CROSS-CONVENTION COMPARE. The read row's slot is an LE stack word
  -- (`StorageReadLog.lean:43`); the change row's slot is BE32, reversed on append. So
  -- byte i of the read slot must be compared against byte 31-i of the change slot. A
  -- dword-wise compare of the two matches only palindromic slots -- and matches
  -- everything if both sides happen to be seeded in one convention, which is how this
  -- survived. See the builder row field table.
  "  ld a2, 8(sp)\n" ++
  "  li t5, 32; li t6, 0\n" ++
  ".Lbssw_scmp:\n" ++
  "  beq t6, t5, .Lbssw_slot_eq\n" ++
  "  add t0, a2, t6\n" ++
  "  li t2, 31; sub t2, t2, t6; addi t2, t2, 32; add t2, t4, t2\n" ++
  "  lbu t0, 0(t0); lbu t2, 0(t2); bne t0, t2, .Lbssw_next\n" ++
  "  addi t6, t6, 1; j .Lbssw_scmp\n" ++
  ".Lbssw_slot_eq:\n" ++
  -- address at +0, BE20 in both, so a straight byte compare
  "  ld a2, 16(sp); li t5, 20; li t6, 0\n" ++
  ".Lbssw_acmp:\n" ++
  "  beq t6, t5, .Lbssw_yes\n" ++
  "  add t0, a2, t6; add t2, t4, t6\n" ++
  "  lbu t0, 0(t0); lbu t2, 0(t2); bne t0, t2, .Lbssw_next\n" ++
  "  addi t6, t6, 1; j .Lbssw_acmp\n" ++
  ".Lbssw_next:\n" ++
  "  addi t3, t3, 1; j .Lbssw_scan\n" ++
  ".Lbssw_yes:\n" ++
  "  li a0, 1; j .Lbssw_ret\n" ++
  ".Lbssw_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbssw_ret:\n" ++
  "  ld ra, 0(sp); addi sp, sp, 32; ret\n"

/-! ## `bal_serializer_filter_reads`

    Phase one of the serializer: build one account's SURVIVING storage_reads.

    Mirrors `_build_from_builder` (`:544-547`):

        storage_reads = []
        for slot in changes.storage_reads:
            if slot not in changes.storage_changes:
                storage_reads.append(slot)

    ## Filtered once, here — not during emission

    The surviving COUNT sizes the read list's RLP header, so the filter has to run
    before any emission regardless. Running it again inside emit would mean two
    implementations of one predicate, and a disagreement there yields a well-formed
    buffer whose read-list header is wrong by the number of slots the two passes
    disagreed about.

    ## PER ACCOUNT, NOT GLOBAL

    In the spec both fields hang off the same `changes` object inside
    `for address, changes in builder.accounts.items()`. So a slot excluded from account
    A's reads because A wrote it **must still appear in account B's reads if B only read
    it**. This routine is therefore called once per account with that account's address,
    and it consults only rows matching that address.

    ## Why a fixture cannot stumble into the discriminating case

    The rule only bites when a slot is BOTH read and written by one account. A block
    that only reads, or only writes, produces the same output with or without the
    filter — and, worse, so does a block that reads and writes DIFFERENT slots. The
    case that discriminates is a slot read in one transaction and written in a LATER
    one, which no single-transaction fixture can produce.

    Calling convention:
      a0 = address ptr (20 B big-endian)
      ra = return
      a0 (out) = surviving read count, also left in
                 `bal_serializer_surviving_read_count`

    Reads `STORAGE_READS_AREA` rows (`addrHash[32], slotKey[32]`, 64 B stride) against
    `bal_builder_storage_changes` (`address[20], pad[4], BAI[8], slot[32], value[32]`,
    96 B stride), and writes surviving 32-byte slot keys into
    `bal_serializer_read_scratch`.

    DELIBERATELY INERT PENDING ITS CALLER: the measure and emit phases land separately. -/
def balSerializerFilterReadsFunction : String :=
  "bal_serializer_filter_reads:\n" ++
  "  addi sp, sp, -32; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++                                             -- s0 = address ptr
  "  la t0, bal_serializer_surviving_read_count; sd zero, 0(t0)\n" ++
  "  li s1, 0\n" ++                                              -- s1 = survivor count
  "  la t0, storage_reads_count; ld s2, 0(t0)\n" ++               -- s2 = read row count
  "  li t3, 0\n" ++                                              -- t3 = read index
  ".Lbsfr_read:\n" ++
  "  bgeu t3, s2, .Lbsfr_done\n" ++
  "  li t0, 0xa1ba0000; slli t1, t3, 6; add t4, t0, t1\n" ++      -- t4 = &readrow[i]
  -- The read row's addrHash is a 32-byte stack-word key; the account address is BE20.
  -- Compare the low 20 bytes of the reversed key against it, which is the same
  -- canonicalisation the builder rows use.
  "  mv a0, s0; mv a1, t4; jal ra, bal_serializer_addr_matches\n" ++
  "  beqz a0, .Lbsfr_next\n" ++
  -- This read belongs to the account. Is its slot also in storage_changes FOR THIS
  -- ACCOUNT? Scan the change stream; a hit means the spec drops the read.
  "  addi a0, t4, 32; mv a1, s0; jal ra, bal_serializer_slot_written\n" ++
  "  bnez a0, .Lbsfr_next\n" ++                                  -- written => EXCLUDE
  -- Survivor: COUNT it. Nothing is materialised -- see the note above on why no
  -- scratch list exists.
  "  addi s1, s1, 1\n" ++
  ".Lbsfr_next:\n" ++
  "  addi t3, t3, 1; j .Lbsfr_read\n" ++
  ".Lbsfr_done:\n" ++
  "  la t0, bal_serializer_surviving_read_count; sd s1, 0(t0)\n" ++
  "  mv a0, s1\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret\n"

/-! ## `bal_serializer_measure_reads`

    Measure one account's `storage_reads` field into the length table's `+16` slot.

    The field is `Tuple[U256, ...]` — a flat list of slot keys — so its payload is the
    sum of each surviving key's encoded scalar length, and nothing nested.

    ## It measures the FILTERED list, not the raw read set

    Runs after `bal_serializer_filter_reads` and reads
    `bal_serializer_read_scratch` / `_count`. Measuring the raw set instead would
    produce a header sized for slots the emit pass will not write — the two would
    disagree by exactly the excluded slots, and the buffer would be well-formed with a
    long header.

    ## The entry is a PAYLOAD length

    Per the table's convention: the bytes INSIDE the list, excluding its own header.
    `rlp_encode_list_prefix` and `bal_rlp_emit_list_header` both consume exactly this,
    so the entry is handed over unmodified. A caller needing the ENCODED size adds
    `bal_rlp_list_header_len` of this value.

    ## Why the scalar measurer and not a throwaway emit here

    `bal_rlp_scalar_rlp_len` and `bal_rlp_emit_scalar` are a matched pair over the same
    input shape — a pointer to a 32-byte field — and the pair is already checked
    per-case by the RLP self-test's fifteen assertions. So for this shape the single
    implementation property already holds without a throwaway context.

    The throwaway route (`bal_rlp_measure_into_throwaway`) is for shapes whose measurer
    would otherwise be a SECOND implementation — the code byte string, where the only
    measurers available are in the other layer.

    a0 = (unused; the filtered list is in scratch)
    a0 (out) = the payload length, also stored at `bal_serializer_len_table + 16`

    DELIBERATELY INERT PENDING ITS CALLER. -/
def balSerializerMeasureReadsFunction : String :=
  "bal_serializer_measure_reads:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0\n" ++
  "  li s1, 0\n" ++
  "  la t0, storage_reads_count; ld s2, 0(t0)\n" ++
  "  li s3, 0\n" ++
  ".Lbsmr_loop:\n" ++
  "  bgeu s3, s2, .Lbsmr_done\n" ++
  -- SAME two predicates the filter and the emit use. Re-running one routine cannot
  -- diverge from itself, which is why no materialised survivor list is needed.
  "  li t0, 0xa1ba0000; slli t1, s3, 6; add t4, t0, t1\n" ++
  "  mv a0, s0; mv a1, t4; jal ra, bal_serializer_addr_matches\n" ++
  "  beqz a0, .Lbsmr_next\n" ++
  "  li t0, 0xa1ba0000; slli t1, s3, 6; add t4, t0, t1\n" ++
  "  addi a0, t4, 32; mv a1, s0; jal ra, bal_serializer_slot_written\n" ++
  "  bnez a0, .Lbsmr_next\n" ++
  "  li t0, 0xa1ba0000; slli t1, s3, 6; add t4, t0, t1\n" ++
  "  addi a0, t4, 32; jal ra, bal_rlp_scalar_rlp_len\n" ++
  "  add s1, s1, a0\n" ++
  ".Lbsmr_next:\n" ++
  "  addi s3, s3, 1; j .Lbsmr_loop\n" ++
  ".Lbsmr_done:\n" ++
  "  la t0, bal_serializer_len_table; sd s1, 16(t0)\n" ++
  "  mv a0, s1\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret\n"

/-! ## `bal_serializer_measure_storage`

    The deepest field. `storage_changes` is `Tuple[SlotChanges, ...]`, `SlotChanges` is
    `[slot, changes]`, `changes` is `Tuple[StorageChange, ...]`, and `StorageChange` is
    `[block_access_index, new_value]` — so there are **three header levels below the field
    list**, against one for balance and nonce and none for reads:

        encoded(SlotChanges) = hdr(p2) + p2
        p2                   = scalar(slot) + hdr(p3) + p3
        p3                   = Σ over changes of ( hdr(p4) + p4 )
        p4                   = scalar(bai) + scalar(new_value)

    Getting a level wrong here is the nesting error the table's convention exists to
    prevent, and it is silent: every intermediate is still a well-formed RLP list, just
    the wrong length.

    ## The rows are flat, so grouping is this routine's job

    The builder stream is `{address[20], pad[4], BAI[8], slot[32], value[32]}` per row with
    no grouping. `_build_from_builder` (`:537-542`) groups by slot and sorts each slot's
    changes by `block_access_index`, so the walk over a flat stream must do the same: for
    each DISTINCT slot belonging to this account, sum that slot's changes.

    Distinctness is found by scanning backwards — a row is the FIRST occurrence of its slot
    if no earlier row for this account carries the same slot. That is O(n²) in the account's
    change count, which is bounded by the arena and paid once per account in a measure pass
    that is already O(n) per field. Sorting the stream first would be faster and would need
    somewhere to put the sorted copy, which the `.bss` budget does not have.

      a0 = address ptr (20 B BE)
      a0 (out) = payload length, stored at `bal_serializer_len_table + 8`

    DELIBERATELY INERT PENDING ITS CALLER. -/
/-- Reverse the BE32 slot at `a0` into `bal_serializer_slot_le`, an LE field the scalar
    pair can read. a0 = pointer to the row's slot (row+32).

    Needed because the storage row carries TWO conventions: the slot is reversed to BE32
    on append while the value four dwords later is passed verbatim as LE. See the builder
    row field table above. `bal_rlp_scalar_len` / `bal_rlp_emit_scalar` are documented for
    LE limbs, so they are correct on the value and wrong on the slot.

    Reversing into scratch rather than adding a BE variant of the scalar pair is
    deliberate: a second implementation of one encoding rule can agree with the first by
    construction rather than by correctness, and the canonical-minimal-length logic is
    exactly the part that must not be duplicated. `bal_emit_storage_changes` already uses
    this shape with `besc_slot_be`, in the opposite direction. -/
def balSerializerSlotToLeFunction : String :=
  "bal_serializer_slot_to_le:\n" ++
  "  la t0, bal_serializer_slot_le; li t1, 32; addi t2, a0, 31\n" ++
  ".Lbssl_rev:\n" ++
  "  beqz t1, .Lbssl_done\n" ++
  "  lbu t3, 0(t2); sb t3, 0(t0); addi t2, t2, -1; addi t0, t0, 1; addi t1, t1, -1\n" ++
  "  j .Lbssl_rev\n" ++
  ".Lbssl_done:\n" ++
  "  ret\n"

/-- Reverse the BE32 balance at `a0` into `bal_serializer_balance_le`, an LE field the
    scalar pair can read.  a0 = pointer to the row's post balance (row+32).

    Same defect and same remedy as `bal_serializer_slot_to_le`, on a different field.
    The balance is produced by the `u256_*_be` helpers -- `u256AddBe_prog` propagates carry
    from byte 31 DOWN TO byte 0, so byte 0 is the most significant -- and it is then copied
    verbatim at every hop (`record_nonstorage_effect` -> `account_write_record` ->
    `bal_builder_append_balance`).  `bal_rlp_scalar_len` scans DOWN FROM BYTE 31 for the
    most significant byte, so on a BE32 field holding a 12-byte value right-aligned in
    bytes 20..31 it reported 32 significant bytes and every balance row encoded as a
    33-byte string instead of its minimal form.  GH #10820.

    The builder row field table called this field LE, which is why the hand-off looked
    correct: the balance was grouped with the storage VALUE (a genuine LE stack word) by
    row position rather than by provenance.

    A separate scratch buffer rather than reusing `bal_serializer_slot_le`: the balance
    legs and the storage legs are independent, and sharing one buffer would make their
    emit order load-bearing. Duplicating the six-line REVERSAL is not the duplication
    `bal_serializer_slot_to_le` argues against -- that argument is about the
    canonical-minimal-length logic, which still exists exactly once. -/
def balSerializerBalanceToLeFunction : String :=
  "bal_serializer_balance_to_le:\n" ++
  "  la t0, bal_serializer_balance_le; li t1, 32; addi t2, a0, 31\n" ++
  ".Lbsbl_rev:\n" ++
  "  beqz t1, .Lbsbl_done\n" ++
  "  lbu t3, 0(t2); sb t3, 0(t0); addi t2, t2, -1; addi t0, t0, 1; addi t1, t1, -1\n" ++
  "  j .Lbsbl_rev\n" ++
  ".Lbsbl_done:\n" ++
  "  ret\n"

/-- One slot's `SlotChanges` measurement, shared by the measure pass and the emit pass.

`a0` = address ptr, `a1` = a representative builder row for this slot (its slot key is
read at `+32`).  Returns `a0` = the `SlotChanges` PAYLOAD length and `a1` = the inner
changes-list PAYLOAD length.

Both numbers are returned, and it is a payload rather than an encoded size, because the
emit pass needs exactly these two to write the two nested list headers, and it cannot
recover either from the length table: the table has one entry for the whole
`storage_changes` field, while the per-slot count is unbounded.  Factoring this out is
what makes the two passes agree by construction -- a separate emit-side computation of
the same quantity is free to drift, and the only symptom would be a wrong digest with
every intermediate check passing. -/
def balSerializerMeasureSlotFunction : String :=
  "bal_serializer_measure_slot:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s4, 24(sp)\n" ++
  "  sd s5, 32(sp); sd s6, 40(sp); sd s7, 48(sp)\n" ++
  "  mv s0, a0; mv s4, a1\n" ++
  "  la t0, bal_builder_storage_change_count; ld s1, 0(t0)\n" ++
  "  li s5, 0\n" ++                                              -- s5 = inner changes payload
  "  li s6, 0\n" ++                                              -- s6 = inner index
  ".Lbsmsl_chg:\n" ++
  "  bgeu s6, s1, .Lbsmsl_chg_done\n" ++
  "  li t0, 96; mul t1, s6, t0; la t2, bal_builder_storage_changes; add s7, t2, t1\n" ++
  "  mv a0, s0; mv a1, s7; jal ra, bal_serializer_addr_matches_be\n" ++
  "  beqz a0, .Lbsmsl_chg_next\n" ++
  "  addi a0, s4, 32; addi a1, s7, 32; jal ra, bal_serializer_slot_eq\n" ++
  "  beqz a0, .Lbsmsl_chg_next\n" ++
  -- p4 = scalar(bai) + scalar(new_value)
  "  ld a1, 24(s7); la a0, bal_serializer_u64_field; jal ra, bal_serializer_u64_to_field\n" ++
  "  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len; mv t5, a0\n" ++
  "  addi a0, s7, 64; jal ra, bal_rlp_scalar_rlp_len; add t5, t5, a0\n" ++
  -- LEVEL 4 header: StorageChange is itself a list
  "  mv a0, t5; jal ra, bal_rlp_list_header_len; add t5, t5, a0\n" ++
  "  add s5, s5, t5\n" ++
  ".Lbsmsl_chg_next:\n" ++
  "  addi s6, s6, 1; j .Lbsmsl_chg\n" ++
  ".Lbsmsl_chg_done:\n" ++
  -- SlotChanges payload = scalar(slot) + encoded(changes list)
  "  mv s7, s5\n" ++                                             -- s7 = inner payload, preserved
  "  mv a0, s5; jal ra, bal_rlp_list_header_len; add s5, s5, a0\n" ++
  -- The slot is BE32 in the row; the scalar pair reads LE. Reverse first.
  "  addi a0, s4, 32; jal ra, bal_serializer_slot_to_le\n" ++
  "  la a0, bal_serializer_slot_le; jal ra, bal_rlp_scalar_rlp_len; add s5, s5, a0\n" ++
  "  mv a0, s5; mv a1, s7\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s4, 24(sp)\n" ++
  "  ld s5, 32(sp); ld s6, 40(sp); ld s7, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

def balSerializerMeasureStorageFunction : String :=
  "bal_serializer_measure_storage:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0\n" ++                                              -- s0 = address ptr
  "  la t0, bal_builder_storage_change_count; ld s1, 0(t0)\n" ++
  "  li s2, 0\n" ++                                              -- s2 = field payload
  "  li s3, 0\n" ++                                              -- s3 = outer row index
  ".Lbsms_slot:\n" ++
  "  bgeu s3, s1, .Lbsms_done\n" ++
  "  li t0, 96; mul t1, s3, t0; la t2, bal_builder_storage_changes; add s4, t2, t1\n" ++
  "  mv a0, s0; mv a1, s4; jal ra, bal_serializer_addr_matches_be\n" ++
  "  beqz a0, .Lbsms_slot_next\n" ++
  -- FIRST-OCCURRENCE test: skip this row if an earlier row of this account has the same
  -- slot, so each distinct slot is measured exactly once.
  "  mv a0, s0; mv a1, s4; mv a2, s3; jal ra, bal_serializer_slot_seen_before\n" ++
  "  bnez a0, .Lbsms_slot_next\n" ++
  -- This slot's SlotChanges payload, from the routine the emit pass also calls.
  "  mv a0, s0; mv a1, s4; jal ra, bal_serializer_measure_slot\n" ++
  "  mv s5, a0\n" ++
  -- LEVEL 2 header: SlotChanges is a list
  "  mv a0, s5; jal ra, bal_rlp_list_header_len; add s5, s5, a0\n" ++
  "  add s2, s2, s5\n" ++
  ".Lbsms_slot_next:\n" ++
  "  addi s3, s3, 1; j .Lbsms_slot\n" ++
  ".Lbsms_done:\n" ++
  "  la t0, bal_serializer_len_table; sd s2, 8(t0)\n" ++
  "  mv a0, s2\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret\n"

/-- 32-byte slot-key equality. a0, a1 = slot ptrs. a0 (out) = 1 if equal. -/
def balSerializerSlotEqFunction : String :=
  "bal_serializer_slot_eq:\n" ++
  "  ld t0, 0(a0);  ld t1, 0(a1);  bne t0, t1, .Lbsse_no\n" ++
  "  ld t0, 8(a0);  ld t1, 8(a1);  bne t0, t1, .Lbsse_no\n" ++
  "  ld t0, 16(a0); ld t1, 16(a1); bne t0, t1, .Lbsse_no\n" ++
  "  ld t0, 24(a0); ld t1, 24(a1); bne t0, t1, .Lbsse_no\n" ++
  "  li a0, 1; ret\n" ++
  ".Lbsse_no:\n" ++
  "  li a0, 0; ret\n"

/-- Has an EARLIER row of this account already carried this slot? a0 = address ptr,
    a1 = this row, a2 = this row's index. a0 (out) = 1 if seen before, so the caller
    measures each distinct slot exactly once. -/
def balSerializerSlotSeenBeforeFunction : String :=
  "bal_serializer_slot_seen_before:\n" ++
  "  addi sp, sp, -48; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  li s3, 0\n" ++
  ".Lbssb_loop:\n" ++
  "  bgeu s3, s2, .Lbssb_no\n" ++
  "  li t0, 96; mul t1, s3, t0; la t2, bal_builder_storage_changes; add t3, t2, t1\n" ++
  "  mv a0, s0; mv a1, t3; jal ra, bal_serializer_addr_matches_be\n" ++
  "  beqz a0, .Lbssb_next\n" ++
  "  li t0, 96; mul t1, s3, t0; la t2, bal_builder_storage_changes; add t3, t2, t1\n" ++
  "  addi a0, s1, 32; addi a1, t3, 32; jal ra, bal_serializer_slot_eq\n" ++
  "  bnez a0, .Lbssb_yes\n" ++
  ".Lbssb_next:\n" ++
  "  addi s3, s3, 1; j .Lbssb_loop\n" ++
  ".Lbssb_yes:\n" ++
  "  li a0, 1; j .Lbssb_ret\n" ++
  ".Lbssb_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbssb_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48; ret\n"

/-- Widen a u64 (`a1`) into the 32-byte scalar field at `a0`.

    The field is LITTLE-ENDIAN limbs -- byte 0 is the LEAST significant -- because that
    is what every consumer in `BalRlpEncode.lean` reads:
    `bal_rlp_scalar_len` scans DOWNWARD from byte 31 for the most significant byte, and
    `bal_rlp_emit_scalar` emits field byte `len-1-i` at BE output index `i`.

    This routine previously wrote the u64 the other way round -- LSB at byte 31 -- under
    a comment that called that "big-endian". `bal_rlp_scalar_len`'s docstring calls byte
    31 "the canonical BE most-significant byte". Both said BE and meant opposite layouts,
    so the two agreed in prose and disagreed in bytes. The cost was not subtle: for
    `block_access_index = 1` the field got `0x01` at byte 31, `bal_rlp_scalar_len`
    reported 32 significant bytes, and `bal_rlp_scalar_rlp_len` returned 33 instead of 1
    -- every storage change over-measured by 32 bytes, and the emit pass would have
    absorbed a 32-byte string where the spec has a single `0x01`.

    RV64 is little-endian, so one `sd` of the u64 at offset 0 IS the LE field. -/
def balSerializerU64ToFieldFunction : String :=
  "bal_serializer_u64_to_field:\n" ++
  "  sd zero, 0(a0); sd zero, 8(a0); sd zero, 16(a0); sd zero, 24(a0)\n" ++
  "  sd a1, 0(a0)\n" ++
  "  ret\n"

def balSerializerAddrMatchesBeFunction : String :=
  "bal_serializer_addr_matches_be:\n" ++
  "  li t0, 20; li t1, 0\n" ++
  ".Lbsab_cmp:\n" ++
  "  beq t1, t0, .Lbsab_yes\n" ++
  "  add t2, a0, t1; add t3, a1, t1\n" ++
  "  lbu t4, 0(t2); lbu t5, 0(t3); bne t4, t5, .Lbsab_no\n" ++
  "  addi t1, t1, 1; j .Lbsab_cmp\n" ++
  ".Lbsab_yes:\n" ++
  "  li a0, 1; ret\n" ++
  ".Lbsab_no:\n" ++
  "  li a0, 0; ret\n"

/-! ## `bal_serializer_measure_nonce`

    The last flat field measurer that needs nothing new. `storage_changes` is doubly
    nested and lands separately, and `code_changes` lands with #10739 because it needs
    `bal_rlp_emit_bytes` and `bal_rlp_measure_into_throwaway` — the byte-string shape has
    no measurer in this layer, so its length must come from running the emitter against a
    discarded sponge.

    ## Nonce: identical in shape to balance

    `NonceChange` is `[block_access_index, new_nonce]` with a **u64** payload, so both
    scalars go through `bal_serializer_u64_to_field` first. The widener is used twice per
    row rather than once, which is the only difference from the balance measurer.

    ## Code: the one field that needs the throwaway context

    `CodeChange` is `[block_access_index, new_code]` where `new_code` is a
    variable-length byte string. `bal_rlp` has no byte-string MEASURER — only
    `bal_rlp_emit_bytes` — and the measurers that do exist for that shape live in the
    generic layer, so using one would make measure and emit two different
    implementations of the string rule.

    So the length comes from running the emitter itself against a discarded context:
    `bal_rlp_measure_into_throwaway`. The emitter is then the single implementation, and
    measure/emit disagreement is not merely untested but unrepresentable.

    **The row's `+32` and `+40` are the code POINTER and LENGTH**, confirmed from the live
    caller at `AccountWriteMap.lean:355` — `ld a2, 80(s4); ld a3, 88(s4)` — not a hash and
    not opaque meta, despite the row docstring's "reference/meta". The remaining 16 bytes
    of the 32 are spare.

      a0 = address ptr (20 B BE)
      a0 (out) = payload length, stored at `+32` (nonce) or `+40` (code)

    DELIBERATELY INERT PENDING THEIR CALLER. -/

def balSerializerMeasureBalanceFunction : String :=
  "bal_serializer_measure_balance:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0\n" ++                                              -- s0 = address ptr
  "  la t0, bal_builder_balance_count; ld s1, 0(t0)\n" ++
  "  li s2, 0\n" ++                                              -- s2 = payload accum
  "  li s3, 0\n" ++                                              -- s3 = row index
  ".Lbsmb_loop:\n" ++
  "  bgeu s3, s1, .Lbsmb_done\n" ++
  "  li t0, 64; mul t1, s3, t0; la t2, bal_builder_balance_changes; add s4, t2, t1\n" ++
  -- per account: skip rows belonging to another address
  "  mv a0, s0; mv a1, s4; jal ra, bal_serializer_addr_matches_be\n" ++
  "  beqz a0, .Lbsmb_next\n" ++
  -- inner payload = scalar(bai) + scalar(post_balance)
  "  ld a1, 24(s4); la a0, bal_serializer_u64_field; jal ra, bal_serializer_u64_to_field\n" ++
  "  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len; mv t5, a0\n" ++
  -- #10820: the row's post balance is BE32; the scalar pair reads LE limbs.  Reverse
  -- into scratch first, exactly as the slot leg does.  MUST stay in lockstep with
  -- `bal_serializer_emit_balance` -- if only one side is corrected the length prefix and
  -- the payload disagree and the RLP is malformed with a still-plausible total.
  "  addi a0, s4, 32; jal ra, bal_serializer_balance_to_le\n" ++
  "  la a0, bal_serializer_balance_le; jal ra, bal_rlp_scalar_rlp_len; add t5, t5, a0\n" ++
  -- the row's ENCODED size adds the inner list's own header
  "  mv a0, t5; jal ra, bal_rlp_list_header_len; add t5, t5, a0\n" ++
  "  add s2, s2, t5\n" ++
  ".Lbsmb_next:\n" ++
  "  addi s3, s3, 1; j .Lbsmb_loop\n" ++
  ".Lbsmb_done:\n" ++
  "  la t0, bal_serializer_len_table; sd s2, 24(t0)\n" ++
  "  mv a0, s2\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret\n"

/-- Builder rows hold a canonical BE20 address at +0, so this compares directly rather
    than reversing a stack word the way `bal_serializer_addr_matches` must for read
    rows. Two routines because the two row families store the address differently — the
    encoding split the sort descriptors already record. -/

def balSerializerMeasureNonceFunction : String :=
  "bal_serializer_measure_nonce:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0\n" ++
  "  la t0, bal_builder_nonce_count; ld s1, 0(t0)\n" ++
  "  li s2, 0; li s3, 0\n" ++
  ".Lbsmn_loop:\n" ++
  "  bgeu s3, s1, .Lbsmn_done\n" ++
  -- nonce rows are 40 bytes: index*40 = index*32 + index*8
  "  slli t1, s3, 5; slli t2, s3, 3; add t1, t1, t2\n" ++
  "  la t2, bal_builder_nonce_changes; add s4, t2, t1\n" ++
  "  mv a0, s0; mv a1, s4; jal ra, bal_serializer_addr_matches_be\n" ++
  "  beqz a0, .Lbsmn_next\n" ++
  "  ld a1, 24(s4); la a0, bal_serializer_u64_field; jal ra, bal_serializer_u64_to_field\n" ++
  "  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len; mv t5, a0\n" ++
  "  ld a1, 32(s4); la a0, bal_serializer_u64_field; jal ra, bal_serializer_u64_to_field\n" ++
  "  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len; add t5, t5, a0\n" ++
  "  mv a0, t5; jal ra, bal_rlp_list_header_len; add t5, t5, a0\n" ++
  "  add s2, s2, t5\n" ++
  ".Lbsmn_next:\n" ++
  "  addi s3, s3, 1; j .Lbsmn_loop\n" ++
  ".Lbsmn_done:\n" ++
  "  la t0, bal_serializer_len_table; sd s2, 32(t0)\n" ++
  "  mv a0, s2\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

/-! ## `bal_serializer_measure_code`

    `CodeChange` is `[block_access_index, new_code]` where `new_code` is a variable-length
    byte string. `bal_rlp` has no byte-string MEASURER — only `bal_rlp_emit_bytes` — and the
    measurers for that shape live in the generic layer, so using one would make measure and
    emit two different implementations of the string rule.

    So the length comes from running the emitter itself against a discarded context, via
    `bal_rlp_measure_into_throwaway`. The emitter is then the single implementation and
    disagreement is unrepresentable rather than merely untested.

    **`+32` is the code POINTER and `+40` the LENGTH**, from the live caller at
    `AccountWriteMap.lean:355` (`ld a2, 80(s4); ld a3, 88(s4)`) — not a hash, despite the row
    docstring's "reference/meta". The remaining 16 bytes of the 32 are spare.

      a0 = address ptr (20 B BE)
      a0 (out) = payload length, stored at `bal_serializer_len_table + 40` -/
def balSerializerMeasureCodeFunction : String :=
  "bal_serializer_measure_code:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0\n" ++
  "  la t0, bal_builder_code_count; ld s1, 0(t0)\n" ++
  "  li s2, 0; li s3, 0\n" ++
  ".Lbsmc_loop:\n" ++
  "  bgeu s3, s1, .Lbsmc_done\n" ++
  "  slli t1, s3, 6; la t2, bal_builder_code_changes; add s4, t2, t1\n" ++
  "  mv a0, s0; mv a1, s4; jal ra, bal_serializer_addr_matches_be\n" ++
  "  beqz a0, .Lbsmc_next\n" ++
  "  ld a1, 24(s4); la a0, bal_serializer_u64_field; jal ra, bal_serializer_u64_to_field\n" ++
  "  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len; mv t5, a0\n" ++
  -- `bal_rlp_measure_into_throwaway` calls the variable-length byte emitter,
  -- which may clobber caller-saved t5.  Preserve the block-access-index size
  -- while measuring the code byte string.
  "  sd t5, 48(sp)\n" ++
  "  la a0, bal_serializer_throwaway_ctx\n" ++
  "  la a1, bal_rlp_emit_bytes\n" ++
  "  ld a2, 32(s4); ld a3, 40(s4); la a4, bal_serializer_hdr_scratch\n" ++
  "  jal ra, bal_rlp_measure_into_throwaway\n" ++
  "  ld t5, 48(sp)\n" ++
  "  add t5, t5, a0\n" ++
  "  mv a0, t5; jal ra, bal_rlp_list_header_len; add t5, t5, a0\n" ++
  "  add s2, s2, t5\n" ++
  ".Lbsmc_next:\n" ++
  "  addi s3, s3, 1; j .Lbsmc_loop\n" ++
  ".Lbsmc_done:\n" ++
  "  la t0, bal_serializer_len_table; sd s2, 40(t0)\n" ++
  "  mv a0, s2\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

/-! ## `bal_serializer_measure_account`

    Fill all six entries of the length table for one account, then compute the account's own
    payload from them.

    **The account payload is the sum of each field's ENCODED size** — every field is a list,
    so each contributes its own header plus its payload — **plus the encoded address**. The
    table holds PAYLOADS, so each entry is converted by adding
    `bal_rlp_list_header_len` of itself. Summing the entries directly would leave the account
    header short by five field headers, silently.

    This is the one place all six conversions happen, so it is the one place that error can
    be made, which is why the six `header_len` calls are guarded by count.

      a0 = address ptr (20 B BE)
      a0 (out) = the account's PAYLOAD length, stored at `bal_serializer_len_table + 0` -/
def balSerializerMeasureAccountFunction : String :=
  "bal_serializer_measure_account:\n" ++
  "  addi sp, sp, -48; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0; li s1, 0\n" ++
  -- the address is a 21-byte RLP string: 0x94 then 20 bytes, so its encoded size is fixed
  "  addi s1, s1, 21\n" ++
  "  mv a0, s0; jal ra, bal_serializer_measure_storage\n" ++
  "  mv a0, a0; jal ra, bal_rlp_list_header_len\n" ++
  "  la t0, bal_serializer_len_table; ld t1, 8(t0); add s1, s1, t1; add s1, s1, a0\n" ++
  "  mv a0, s0; jal ra, bal_serializer_measure_reads\n" ++
  "  jal ra, bal_rlp_list_header_len\n" ++
  "  la t0, bal_serializer_len_table; ld t1, 16(t0); add s1, s1, t1; add s1, s1, a0\n" ++
  "  mv a0, s0; jal ra, bal_serializer_measure_balance\n" ++
  "  jal ra, bal_rlp_list_header_len\n" ++
  "  la t0, bal_serializer_len_table; ld t1, 24(t0); add s1, s1, t1; add s1, s1, a0\n" ++
  "  mv a0, s0; jal ra, bal_serializer_measure_nonce\n" ++
  "  jal ra, bal_rlp_list_header_len\n" ++
  "  la t0, bal_serializer_len_table; ld t1, 32(t0); add s1, s1, t1; add s1, s1, a0\n" ++
  "  mv a0, s0; jal ra, bal_serializer_measure_code\n" ++
  "  jal ra, bal_rlp_list_header_len\n" ++
  "  la t0, bal_serializer_len_table; ld t1, 40(t0); add s1, s1, t1; add s1, s1, a0\n" ++
  "  la t0, bal_serializer_len_table; sd s1, 0(t0)\n" ++
  "  mv a0, s1\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); addi sp, sp, 48\n" ++
  "  ret\n"

/-- Emit this account's `storage_changes` field into a keccak context.

    a0 = keccak ctx, a1 = address ptr (20 BE bytes), a2 = scratch (>= 33 bytes).

    Walks the same rows in the same order as `bal_serializer_measure_storage` and takes
    every nested length from `bal_serializer_measure_slot`, so the two passes cannot
    disagree about a header. Emission is streaming -- bytes are absorbed, never buffered
    -- so a header written before its payload cannot be backpatched, which is exactly
    why the lengths have to come from the shared measurer rather than from a local count.

    THE ADDRESS IS NOT EMITTED HERE and this routine must not use
    `bal_rlp_emit_address`: that helper REVERSES its input (`src[19-i]`), because it
    expects the address in the low bytes of an LE stack word. Builder rows hold the
    address big-endian already -- which is why `bal_serializer_addr_matches_be` exists --
    so passing a row through it would silently reverse every address. -/
def balSerializerEmitStorageFunction : String :=
  "bal_serializer_emit_storage:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++       -- ctx, address, scratch
  "  la t0, bal_builder_storage_change_count; ld s3, 0(t0)\n" ++
  "  li s4, 0\n" ++                              -- outer row index
  ".Lbses_slot:\n" ++
  "  bgeu s4, s3, .Lbses_done\n" ++
  "  li t0, 96; mul t1, s4, t0; la t2, bal_builder_storage_changes; add s5, t2, t1\n" ++
  "  mv a0, s1; mv a1, s5; jal ra, bal_serializer_addr_matches_be\n" ++
  "  beqz a0, .Lbses_slot_next\n" ++
  "  mv a0, s1; mv a1, s5; mv a2, s4; jal ra, bal_serializer_slot_seen_before\n" ++
  "  bnez a0, .Lbses_slot_next\n" ++
  -- Both nested payloads come from the measurer the measure pass uses.
  "  mv a0, s1; mv a1, s5; jal ra, bal_serializer_measure_slot\n" ++
  "  mv s6, a0; mv s7, a1\n" ++                  -- s6 = SlotChanges payload, s7 = inner
  "  mv a0, s0; mv a1, s6; mv a2, s2; jal ra, bal_rlp_emit_list_header\n" ++
  "  addi a0, s5, 32; jal ra, bal_serializer_slot_to_le\n" ++
  "  mv a0, s0; la a1, bal_serializer_slot_le; mv a2, s2; jal ra, bal_rlp_emit_scalar\n" ++
  "  mv a0, s0; mv a1, s7; mv a2, s2; jal ra, bal_rlp_emit_list_header\n" ++
  "  li s8, 0\n" ++                              -- inner row index
  ".Lbses_chg:\n" ++
  "  bgeu s8, s3, .Lbses_chg_done\n" ++
  "  li t0, 96; mul t1, s8, t0; la t2, bal_builder_storage_changes; add t3, t2, t1\n" ++
  "  sd t3, 80(sp)\n" ++
  "  mv a0, s1; mv a1, t3; jal ra, bal_serializer_addr_matches_be\n" ++
  "  beqz a0, .Lbses_chg_next\n" ++
  "  ld t3, 80(sp); addi a0, s5, 32; addi a1, t3, 32; jal ra, bal_serializer_slot_eq\n" ++
  "  beqz a0, .Lbses_chg_next\n" ++
  -- StorageChange payload = scalar(bai) + scalar(new_value), measured before emitting
  -- the header, because the header goes into the sponge first and cannot be revised.
  "  ld t3, 80(sp); ld a1, 24(t3); la a0, bal_serializer_u64_field\n" ++
  "  jal ra, bal_serializer_u64_to_field\n" ++
  "  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len; sd a0, 88(sp)\n" ++
  "  ld t3, 80(sp); addi a0, t3, 64; jal ra, bal_rlp_scalar_rlp_len\n" ++
  "  ld t4, 88(sp); add t4, t4, a0; sd t4, 88(sp)\n" ++
  "  mv a0, s0; ld a1, 88(sp); mv a2, s2; jal ra, bal_rlp_emit_list_header\n" ++
  "  la t0, bv_bal_shadow_emit_storage_changes; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  mv a0, s0; la a1, bal_serializer_u64_field; mv a2, s2; jal ra, bal_rlp_emit_scalar\n" ++
  "  ld t3, 80(sp); mv a0, s0; addi a1, t3, 64; mv a2, s2; jal ra, bal_rlp_emit_scalar\n" ++
  ".Lbses_chg_next:\n" ++
  "  addi s8, s8, 1; j .Lbses_chg\n" ++
  ".Lbses_chg_done:\n" ++
  ".Lbses_slot_next:\n" ++
  "  addi s4, s4, 1; j .Lbses_slot\n" ++
  ".Lbses_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret\n"

/-- Emit `storage_reads`: a flat list of slot scalars. a0 = ctx, a1 = address, a2 = scratch.

    Mirrors `bal_serializer_measure_reads`, including its use of
    `bal_serializer_addr_matches` -- the REVERSING comparator -- rather than the `_be`
    one. Read rows come from the exec log at `0xa1ba0000` and hold the address in the low
    bytes of an LE stack word, unlike the builder rows, which are big-endian. The two
    comparators are not interchangeable and picking the wrong one silently matches
    nothing. -/
def balSerializerEmitReadsFunction : String :=
  "bal_serializer_emit_reads:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  la t0, storage_reads_count; ld s3, 0(t0)\n" ++
  "  li s4, 0\n" ++
  ".Lbser_loop:\n" ++
  "  bgeu s4, s3, .Lbser_done\n" ++
  "  li t0, 0xa1ba0000; slli t1, s4, 6; add t4, t0, t1; sd t4, 48(sp)\n" ++
  "  mv a0, s1; mv a1, t4; jal ra, bal_serializer_addr_matches\n" ++
  "  beqz a0, .Lbser_next\n" ++
  "  ld t4, 48(sp); addi a0, t4, 32; mv a1, s1; jal ra, bal_serializer_slot_written\n" ++
  "  bnez a0, .Lbser_next\n" ++
  "  ld t4, 48(sp); mv a0, s0; addi a1, t4, 32; mv a2, s2; jal ra, bal_rlp_emit_scalar\n" ++
  "  la t0, bv_bal_shadow_emit_storage_reads; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  ".Lbser_next:\n" ++
  "  addi s4, s4, 1; j .Lbser_loop\n" ++
  ".Lbser_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

/-- Emit `balance_changes`: one `[block_access_index, post_balance]` list per row.
    a0 = ctx, a1 = address, a2 = scratch. Mirrors `bal_serializer_measure_balance`. -/
def balSerializerEmitBalanceFunction : String :=
  "bal_serializer_emit_balance:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  la t0, bal_builder_balance_count; ld s3, 0(t0)\n" ++
  -- Diagnostic cell: the builder row count as the emitter sees it.  Written on
  -- every call (the emitter runs once per account), so last-write-wins leaves
  -- the count; it is the same value each call because nothing appends during
  -- serialization.  This is the cell that separates "no row was ever built"
  -- from "rows exist and the emitter's address filter dropped them".
  "  la t0, bald_bal_builder_count; sd s3, 0(t0)\n" ++
  "  li s4, 0\n" ++
  ".Lbseb_loop:\n" ++
  "  bgeu s4, s3, .Lbseb_done\n" ++
  "  li t0, 64; mul t1, s4, t0; la t2, bal_builder_balance_changes; add t3, t2, t1\n" ++
  "  sd t3, 48(sp)\n" ++
  -- Diagnostic cell: one increment per address-filter comparison attempted.
  -- If this equals builder_count x (accounts visited) then every row was offered
  -- to every account and a missing row was REJECTED by the compare (cause 3, the
  -- key representation); a shortfall means the account loop never reached it
  -- (cause 4).  t3 is already spilled to 48(sp), so t0/t1 are free.
  "  la t0, bald_bal_cmp_attempts; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  ld t3, 48(sp); mv a0, s1; mv a1, t3; jal ra, bal_serializer_addr_matches_be\n" ++
  "  beqz a0, .Lbseb_next\n" ++
  -- Measure the pair BEFORE emitting the header: streaming means no backpatch.
  "  ld t3, 48(sp); ld a1, 24(t3); la a0, bal_serializer_u64_field\n" ++
  "  jal ra, bal_serializer_u64_to_field\n" ++
  "  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len; sd a0, 56(sp)\n" ++
  -- #10820: reverse the BE32 balance into LE scratch before measuring, in lockstep with
  -- `bal_serializer_measure_balance`.  The reversal happens ONCE here and the same scratch
  -- is emitted below, so the measured length and the emitted payload cannot diverge.
  "  ld t3, 48(sp); addi a0, t3, 32; jal ra, bal_serializer_balance_to_le\n" ++
  "  la a0, bal_serializer_balance_le; jal ra, bal_rlp_scalar_rlp_len\n" ++
  "  ld t4, 56(sp); add t4, t4, a0; sd t4, 56(sp)\n" ++
  "  mv a0, s0; ld a1, 56(sp); mv a2, s2; jal ra, bal_rlp_emit_list_header\n" ++
  "  la t0, bv_bal_shadow_emit_balance_changes; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  mv a0, s0; la a1, bal_serializer_u64_field; mv a2, s2; jal ra, bal_rlp_emit_scalar\n" ++
  -- #10820: emit the SAME LE scratch that was measured above.  `bal_serializer_u64_to_field`
  -- writes a different buffer (`bal_serializer_u64_field`), so the reversed balance survives
  -- the intervening bai emit and no second reversal is needed.
  "  mv a0, s0; la a1, bal_serializer_balance_le; mv a2, s2; jal ra, bal_rlp_emit_scalar\n" ++
  ".Lbseb_next:\n" ++
  "  addi s4, s4, 1; j .Lbseb_loop\n" ++
  ".Lbseb_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret\n"

/-- Emit `nonce_changes`: one `[block_access_index, new_nonce]` list per row. Both members
    are u64s widened through the scalar field, so BOTH need the widener -- unlike balance,
    whose post value is already a 32-byte field. a0 = ctx, a1 = address, a2 = scratch. -/
def balSerializerEmitNonceFunction : String :=
  "bal_serializer_emit_nonce:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  la t0, bal_builder_nonce_count; ld s3, 0(t0)\n" ++
  -- Diagnostic cell; see `bald_bal_builder_count` in the balance emitter.
  "  la t0, bald_non_builder_count; sd s3, 0(t0)\n" ++
  "  li s4, 0\n" ++
  ".Lbsen_loop:\n" ++
  "  bgeu s4, s3, .Lbsen_done\n" ++
  "  slli t1, s4, 5; slli t2, s4, 3; add t1, t1, t2\n" ++
  "  la t2, bal_builder_nonce_changes; add t3, t2, t1; sd t3, 48(sp)\n" ++
  -- Diagnostic cell; see `bald_bal_cmp_attempts` in the balance emitter.
  "  la t0, bald_non_cmp_attempts; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  ld t3, 48(sp); mv a0, s1; mv a1, t3; jal ra, bal_serializer_addr_matches_be\n" ++
  "  beqz a0, .Lbsen_next\n" ++
  "  ld t3, 48(sp); ld a1, 24(t3); la a0, bal_serializer_u64_field\n" ++
  "  jal ra, bal_serializer_u64_to_field\n" ++
  "  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len; sd a0, 56(sp)\n" ++
  "  ld t3, 48(sp); ld a1, 32(t3); la a0, bal_serializer_u64_field\n" ++
  "  jal ra, bal_serializer_u64_to_field\n" ++
  "  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len\n" ++
  "  ld t4, 56(sp); add t4, t4, a0; sd t4, 56(sp)\n" ++
  "  mv a0, s0; ld a1, 56(sp); mv a2, s2; jal ra, bal_rlp_emit_list_header\n" ++
  "  la t0, bv_bal_shadow_emit_nonce_changes; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  -- Re-widen the BAI: the field is a single shared buffer and the nonce overwrote it.
  "  ld t3, 48(sp); ld a1, 24(t3); la a0, bal_serializer_u64_field\n" ++
  "  jal ra, bal_serializer_u64_to_field\n" ++
  "  mv a0, s0; la a1, bal_serializer_u64_field; mv a2, s2; jal ra, bal_rlp_emit_scalar\n" ++
  "  ld t3, 48(sp); ld a1, 32(t3); la a0, bal_serializer_u64_field\n" ++
  "  jal ra, bal_serializer_u64_to_field\n" ++
  "  mv a0, s0; la a1, bal_serializer_u64_field; mv a2, s2; jal ra, bal_rlp_emit_scalar\n" ++
  ".Lbsen_next:\n" ++
  "  addi s4, s4, 1; j .Lbsen_loop\n" ++
  ".Lbsen_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret\n"

/-- Emit `code_changes`: one `[block_access_index, new_code]` list per row, where the code
    is a byte string rather than a scalar. a0 = ctx, a1 = address, a2 = scratch.

    The code length is measured through the throwaway-keccak route, exactly as
    `bal_serializer_measure_code` does, because a byte string's encoded size is not
    derivable from a fixed field width. -/
def balSerializerEmitCodeFunction : String :=
  "bal_serializer_emit_code:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  la t0, bal_builder_code_count; ld s3, 0(t0)\n" ++
  "  li s4, 0\n" ++
  ".Lbsec_loop:\n" ++
  "  bgeu s4, s3, .Lbsec_done\n" ++
  "  slli t1, s4, 6; la t2, bal_builder_code_changes; add t3, t2, t1; sd t3, 48(sp)\n" ++
  "  mv a0, s1; mv a1, t3; jal ra, bal_serializer_addr_matches_be\n" ++
  "  beqz a0, .Lbsec_next\n" ++
  "  ld t3, 48(sp); ld a1, 24(t3); la a0, bal_serializer_u64_field\n" ++
  "  jal ra, bal_serializer_u64_to_field\n" ++
  "  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len; sd a0, 56(sp)\n" ++
  "  la a0, bal_serializer_throwaway_ctx; la a1, bal_rlp_emit_bytes\n" ++
  "  ld t3, 48(sp); ld a2, 32(t3); ld a3, 40(t3); la a4, bal_serializer_hdr_scratch\n" ++
  "  jal ra, bal_rlp_measure_into_throwaway\n" ++
  "  ld t4, 56(sp); add t4, t4, a0; sd t4, 56(sp)\n" ++
  "  mv a0, s0; ld a1, 56(sp); mv a2, s2; jal ra, bal_rlp_emit_list_header\n" ++
  "  la t0, bv_bal_shadow_emit_code_changes; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  mv a0, s0; la a1, bal_serializer_u64_field; mv a2, s2; jal ra, bal_rlp_emit_scalar\n" ++
  "  ld t3, 48(sp); mv a0, s0; ld a1, 32(t3); ld a2, 40(t3)\n" ++
  "  la a3, bal_serializer_hdr_scratch; jal ra, bal_rlp_emit_bytes\n" ++
  ".Lbsec_next:\n" ++
  "  addi s4, s4, 1; j .Lbsec_loop\n" ++
  ".Lbsec_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret\n"

/-- Emit one account's `AccountChanges`. a0 = ctx, a1 = address, a2 = scratch.

    `bal_serializer_measure_account` MUST have run for this address first: every header
    here is read from the length table, never recomputed. The five field headers come
    from table entries +8..+40 and the account header from +0.

    FIELD ORDER, verified against the `AccountChanges` class definition at
    `block_access_lists.py:174-208` rather than taken from prose: `address`,
    `storage_changes`, `storage_reads`, `balance_changes`, `nonce_changes`,
    `code_changes`. An RLP list is positional, so a swapped pair is a well-formed
    account with two fields exchanged -- and if both are empty lists, byte-identical.
    That is why the order is cited to the class rather than to a docstring.

    Accounts are NOT filtered: `_build_from_builder` appends every entry in
    `builder.accounts`, so an account whose fields are all empty still emits as five
    empty lists. `emit_outer` walks every account for the same reason. -/
def balSerializerEmitAccountFunction : String :=
  "bal_serializer_emit_account:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  -- account list header, payload from table +0
  "  la t0, bal_serializer_len_table; ld a1, 0(t0)\n" ++
  "  mv a0, s0; mv a2, s2; jal ra, bal_rlp_emit_list_header\n" ++
  -- address: a 21-byte RLP string via emit_bytes with length 20, which writes 0x94 then
  -- the bytes VERBATIM. Not `bal_rlp_emit_address`, which reverses for an LE stack word.
  "  mv a0, s0; mv a1, s1; li a2, 20; mv a3, s2; jal ra, bal_rlp_emit_bytes\n" ++
  "  la t0, bal_serializer_len_table; ld a1, 8(t0)\n" ++
  "  mv a0, s0; mv a2, s2; jal ra, bal_rlp_emit_list_header\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; jal ra, bal_serializer_emit_storage\n" ++
  "  la t0, bal_serializer_len_table; ld a1, 16(t0)\n" ++
  "  mv a0, s0; mv a2, s2; jal ra, bal_rlp_emit_list_header\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; jal ra, bal_serializer_emit_reads\n" ++
  "  la t0, bal_serializer_len_table; ld a1, 24(t0)\n" ++
  "  mv a0, s0; mv a2, s2; jal ra, bal_rlp_emit_list_header\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; jal ra, bal_serializer_emit_balance\n" ++
  "  la t0, bal_serializer_len_table; ld a1, 32(t0)\n" ++
  "  mv a0, s0; mv a2, s2; jal ra, bal_rlp_emit_list_header\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; jal ra, bal_serializer_emit_nonce\n" ++
  "  la t0, bal_serializer_len_table; ld a1, 40(t0)\n" ++
  "  mv a0, s0; mv a2, s2; jal ra, bal_rlp_emit_list_header\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; jal ra, bal_serializer_emit_code\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret\n"

/-- Outer accumulation: the BAL is a list of `AccountChanges`, so its payload is the sum
    of each account's ENCODED size, not of their payloads. a0 (out) = that sum, also
    stored to `bal_serializer_outer_payload`.

    Summing payloads instead of encoded sizes is the same error the account measurer
    guards against one level down, and it is silent in exactly the same way: the result
    is a well-formed list whose header is short by one header per account. -/
def balSerializerMeasureOuterFunction : String :=
  "bal_serializer_measure_outer:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  la t0, bal_builder_account_count; ld s1, 0(t0)\n" ++
  "  li s2, 0\n" ++                                    -- s2 = outer payload accumulator
  "  li s3, 0\n" ++                                    -- s3 = account index
  ".Lbsmo_loop:\n" ++
  "  bgeu s3, s1, .Lbsmo_done\n" ++
  "  li t0, 24; mul t1, s3, t0; la t2, bal_builder_accounts; add s0, t2, t1\n" ++
  "  mv a0, s0; jal ra, bal_serializer_measure_account\n" ++
  "  mv t5, a0\n" ++
  "  jal ra, bal_rlp_list_header_len\n" ++
  "  add s2, s2, t5; add s2, s2, a0\n" ++              -- ENCODED size, not payload
  "  addi s3, s3, 1; j .Lbsmo_loop\n" ++
  ".Lbsmo_done:\n" ++
  "  la t0, bal_serializer_outer_payload; sd s2, 0(t0)\n" ++
  "  mv a0, s2\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret\n"

/-- Emit the whole block access list. a0 = keccak ctx, a1 = scratch (>= 33 bytes).

    THE ACCOUNT LIST MUST ALREADY BE IN CANONICAL ORDER. EIP-7928 sorts accounts by
    address, and this walks `bal_builder_accounts` in storage order -- it does not sort.
    Ordering is `bal_canonical_sort`'s job and must happen before this runs; emitting an
    unsorted list produces a perfectly well-formed BAL with the wrong hash, which is the
    one failure the digest comparison cannot localise.

    Each account is re-measured immediately before it is emitted, because the length
    table holds ONE account at a time and the emitters read their headers from it. -/
def balSerializerEmitOuterFunction : String :=
  "bal_serializer_emit_outer:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++                        -- ctx, scratch
  "  jal ra, bal_serializer_measure_outer\n" ++
  "  mv a0, s0; la t0, bal_serializer_outer_payload; ld a1, 0(t0); mv a2, s1\n" ++
  "  jal ra, bal_rlp_emit_list_header\n" ++
  "  la t0, bal_builder_account_count; ld s2, 0(t0)\n" ++
  "  li s3, 0\n" ++
  ".Lbseo_loop:\n" ++
  "  bgeu s3, s2, .Lbseo_done\n" ++
  "  li t0, 24; mul t1, s3, t0; la t2, bal_builder_accounts; add t3, t2, t1\n" ++
  "  sd t3, 40(sp)\n" ++
  -- Re-measure THIS account: the table is a single-account buffer, and
  -- `measure_outer` above left it holding whichever account it saw last.
  "  mv a0, t3; jal ra, bal_serializer_measure_account\n" ++
  "  ld t3, 40(sp); mv a0, s0; mv a1, t3; mv a2, s1\n" ++
  "  jal ra, bal_serializer_emit_account\n" ++
  "  addi s3, s3, 1; j .Lbseo_loop\n" ++
  ".Lbseo_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret\n"

/-- Sort the accounts into canonical order and hash the rebuilt BAL.
    a0 = scratch (>= 33 bytes), a1 = 32-byte output pointer.
    `bal_serializer_rebuild_hash` returns 0, or the canonical sort's OWN nonzero status
    (1, 2 or 3). It deliberately does NOT normalise: `bal_serializer_verify` is the
    routine that maps any nonzero to its own code 2, and the specific sort code stays in
    `bal_serializer_sort_status`. Naming the routine in this sentence is deliberate --
    the two contracts sit twelve lines apart and both describe an a0-out with small
    integer codes, which is enough for proximity to substitute for attribution.

    Split out from `bal_serializer_verify` so it can be executed on its own: the probe
    seeds the accounts OUT of order and checks the digest still matches the in-order one,
    which is the only way to demonstrate that the sort actually runs. Verifying that
    through the full comparator would need a real SSZ payload for the supplied side.

    THE SORT LIVES HERE, NOT IN A CALLER. Ordering is part of the encoding: an unsorted
    emission is a well-formed BAL with the wrong hash, and it is the single failure a
    digest comparison cannot localise, because every byte is individually correct and
    only the sequence is wrong. Leaving it to a caller makes the one unlocalisable
    failure the easiest to cause.

    Accounts are 20-byte rows sorted on one BIG-ENDIAN 20-byte segment: offset byte 0,
    width byte 0x94 -- that is `0x80 | 20`, the 0x80 being the big-endian flag -- so the
    descriptor is 0x9400 (GH #11054: this used to cite `bal_sort_account_writes`, which
    passed the same value and has since been deleted as unreachable -- the CONSTANT is the
    contract here, not that routine). Writing 0x1400
    instead declares a big-endian address little-endian; it does not sort wrongly and
    carry on, it faults on a bad pointer inside the sort. -/
def balSerializerRebuildHashFunction : String :=
  "bal_serializer_rebuild_hash:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  -- `_build_from_builder` first folds the block account-read set into the
  -- builder as empty touched-account entries.  This must precede every sort:
  -- the account walk below is the single source of outer BAL rows.
  "  jal ra, bal_builder_incorporate_touched_accounts\n" ++
  -- SEVEN ORDERING RULES (block_access_lists.py:539-579), all of them here so the
  -- emitters can stay order-free. Every stride below is 8-ALIGNED, per the rule on
  -- `balBuilderAccountRowBytes` -- the sort swaps rows with ld/sd.
  --
  -- The storage sort carries TWO rules in one pass: sorting the change rows by
  -- (address, slot, block_access_index) makes slots ascend within an account AND
  -- changes ascend by index within a slot, because the emitter walks rows in order and
  -- takes each slot at its first occurrence. `balSortBuilderStorageSegments` is exactly
  -- that key and already exists -- offset 0 width 20 BE, offset 32 width 32 BE, offset
  -- 24 width 8 LE.
  "  la a0, bal_builder_storage_changes\n" ++
  "  la t0, bal_builder_storage_change_count; ld a1, 0(t0)\n" ++
  "  li a2, 96; li a3, 0x0818a0209400; li a4, 3; li a5, " ++
  toString balBuilderStorageChangeCapacity ++ "\n" ++
  "  jal ra, bal_canonical_sort\n" ++
  "  la t0, bal_serializer_sort_status; sd a0, 0(t0)\n" ++
  "  bnez a0, .Lbsrh_ret\n" ++
  -- storage_reads by slot value. The read row's slot is an LE stack word at +32, so the
  -- segment carries no BE flag: offset 0x20, width 0x20.
  "  li a0, 0xa1ba0000\n" ++
  "  la t0, storage_reads_count; ld a1, 0(t0)\n" ++
  "  li a2, 64; li a3, 0x2020; li a4, 1; li a5, " ++
  toString balBuilderStorageReadsCapacity ++ "\n" ++
  "  jal ra, bal_canonical_sort\n" ++
  "  la t0, bal_serializer_sort_status; sd a0, 0(t0)\n" ++
  "  bnez a0, .Lbsrh_ret\n" ++
  -- balance, nonce and code each by (address, block_access_index): segment 0 is the
  -- BE20 address, segment 1 the native-LE u64 index at +24 -> 0x08189400.
  "  la a0, bal_builder_balance_changes\n" ++
  "  la t0, bal_builder_balance_count; ld a1, 0(t0)\n" ++
  "  li a2, 64; li a3, 0x08189400; li a4, 2; li a5, " ++
  toString balBuilderBalanceCapacity ++ "\n" ++
  "  jal ra, bal_canonical_sort\n" ++
  "  la t0, bal_serializer_sort_status; sd a0, 0(t0)\n" ++
  "  bnez a0, .Lbsrh_ret\n" ++
  "  la a0, bal_builder_nonce_changes\n" ++
  "  la t0, bal_builder_nonce_count; ld a1, 0(t0)\n" ++
  "  li a2, 40; li a3, 0x08189400; li a4, 2; li a5, " ++
  toString balBuilderNonceCapacity ++ "\n" ++
  "  jal ra, bal_canonical_sort\n" ++
  "  la t0, bal_serializer_sort_status; sd a0, 0(t0)\n" ++
  "  bnez a0, .Lbsrh_ret\n" ++
  "  la a0, bal_builder_code_changes\n" ++
  "  la t0, bal_builder_code_count; ld a1, 0(t0)\n" ++
  "  li a2, 64; li a3, 0x08189400; li a4, 2; li a5, " ++
  toString balBuilderCodeCapacity ++ "\n" ++
  "  jal ra, bal_canonical_sort\n" ++
  "  la t0, bal_serializer_sort_status; sd a0, 0(t0)\n" ++
  "  bnez a0, .Lbsrh_ret\n" ++
  "  la a0, bal_builder_accounts\n" ++
  "  la t0, bal_builder_account_count; ld a1, 0(t0)\n" ++
  "  li a2, 24; li a3, 0x9400; li a4, 1; li a5, " ++
  toString balBuilderAccountCapacity ++ "\n" ++
  "  jal ra, bal_canonical_sort\n" ++
  "  la t0, bal_serializer_sort_status; sd a0, 0(t0)\n" ++
  "  beqz a0, .Lbsrh_sorted\n" ++
  "  j .Lbsrh_ret\n" ++
  ".Lbsrh_sorted:\n" ++
  -- Streaming: nothing is buffered, so no size bound applies to the rebuilt BAL.
  "  la a0, bal_serializer_rebuilt_ctx; jal ra, keccak_init\n" ++
  "  la a0, bal_serializer_rebuilt_ctx; mv a1, s0; jal ra, bal_serializer_emit_outer\n" ++
  "  la a0, bal_serializer_rebuilt_ctx; mv a1, s1; jal ra, keccak_final\n" ++
  "  li a0, 0\n" ++
  ".Lbsrh_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret\n"

/-- Rebuild the block access list and compare its hash against the supplied one.
    a0 = SSZ_BASE, a1 = scratch (>= 33 bytes).
    `bal_serializer_verify` returns 0 if the rebuilt BAL hashes to the supplied BAL's
    hash, 1 if it does not, and 2 if the canonical sort failed -- normalising ANY nonzero
    from `bal_serializer_rebuild_hash` (which may be 1, 2 or 3) to 2, and leaving the
    specific code in `bal_serializer_sort_status`.

    This is the spec's own check rather than an approximation of it: EIP-7928 commits the
    BAL through a hash, so agreeing on the hash is agreeing on every byte. Nothing weaker
    substitutes -- matching lengths, counts and field sets are all satisfiable by a BAL
    that hashes differently.

    WIRED AND BINDING since GH #10680 (see GH #11258 for the history of this
    docstring claiming otherwise). Called from the shadow-verify block in
    `BlockVerdictReceiptsTail.lean` (`jal ra, bal_serializer_verify`); its return is
    stored to `bv_bal_shadow_status`; and the status is bound into the verdict there --
    a digest mismatch rejects with `bv_fail_code = 60`, a rebuild failure with `61`,
    checked on ACCEPT paths only (the ACCEPT-only guard is what keeps the FR delta
    attributable). The binding contract is pinned by `#guard`s at the bottom of that
    file, so an edit cannot loosen it silently. -/
def balSerializerVerifyFunction : String :=
  "bal_serializer_verify:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv a0, a1; la a1, bal_serializer_rebuilt_hash; jal ra, bal_serializer_rebuild_hash\n" ++
  "  beqz a0, .Lbsv_rebuilt\n" ++
  "  li a0, 2; j .Lbsv_ret\n" ++
  ".Lbsv_rebuilt:\n" ++
  "  mv a0, s0; la a1, bal_serializer_supplied_hash; jal ra, block_access_list_hash\n" ++
  "  la t0, bal_serializer_rebuilt_hash; la t1, bal_serializer_supplied_hash\n" ++
  "  ld t2, 0(t0);  ld t3, 0(t1);  bne t2, t3, .Lbsv_differ\n" ++
  "  ld t2, 8(t0);  ld t3, 8(t1);  bne t2, t3, .Lbsv_differ\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lbsv_differ\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lbsv_differ\n" ++
  "  li a0, 0; j .Lbsv_ret\n" ++
  ".Lbsv_differ:\n" ++
  "  li a0, 1\n" ++
  ".Lbsv_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret\n"

/-! ## Guards on the RETURN CODES against their documented contracts

    A guard class this file did not have. Every other guard here pins emitted text or
    field selection; none pinned what a routine RETURNS against what its docstring says
    it returns. That gap is not hypothetical: a reviewer read `verify`'s 0/1/2 contract
    as applying to `rebuild_hash`'s bail path and reported a defect that was not there,
    because nothing in the code said which routine owned which contract. -/

-- `verify` NORMALISES. Without this the conversion looks redundant -- rebuild_hash
-- already returns nonzero -- and deleting it would silently widen verify's contract to
-- leak sort codes 1 and 3, where 1 collides with "hash does not match".
#guard (balSerializerVerifyFunction.splitOn "li a0, 2; j .Lbsv_ret").length == 2

-- `rebuild_hash` does NOT normalise: it propagates the sort's own code, as its contract
-- says. Stated as the ABSENCE of the conversion, because absence is site-independent
-- while presence could be satisfied by any `li a0, 2` elsewhere in the def.
#guard (balSerializerRebuildHashFunction.splitOn "li a0, 2").length == 1

end EvmAsm.Codegen
