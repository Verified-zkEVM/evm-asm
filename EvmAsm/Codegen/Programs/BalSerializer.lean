import EvmAsm.Codegen.Programs.BalRlpEncode
import EvmAsm.Codegen.Programs.BalCapacities
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

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

open EvmAsm.Rv64

/-! Probe-only local PC placeholder for the unlinked filter helper. -/
def balSerializerFilterReadsPc : Nat := 0x80000000

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

def balSerializerSlotWritten_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x10 (8 : BitVec 12),
    .SD .x2 .x11 (16 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_storage_change_count (GuestAddrs.bal_serializer_slot_written + 16)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_storage_change_count (GuestAddrs.bal_serializer_slot_written + 16)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.bal_serializer_slot_written + 172) (GuestAddrs.bal_serializer_slot_written + 32)),
    .LI .x5 (96 : Word),
    .MUL .x7 .x28 .x5,
    .AUIPC .x29 (laHi GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_slot_written + 44)),
    .ADDI .x29 .x29 (laLo GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_slot_written + 44)),
    .ADD .x29 .x29 .x7,
    .LD .x12 .x2 (8 : BitVec 12),
    .LI .x30 (32 : Word),
    .LI .x31 (0 : Word),
    .BEQ .x31 .x30 (44 : BitVec 13),
    .ADD .x5 .x12 .x31,
    .LI .x7 (31 : Word),
    .SUB .x7 .x7 .x31,
    .ADDI .x7 .x7 (32 : BitVec 12),
    .ADD .x7 .x29 .x7,
    .LBU .x5 .x5 (0 : BitVec 12),
    .LBU .x7 .x7 (0 : BitVec 12),
    .BNE .x5 .x7 (56 : BitVec 13),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .JAL .x0 (-40 : BitVec 21),
    .LD .x12 .x2 (16 : BitVec 12),
    .LI .x30 (20 : Word),
    .LI .x31 (0 : Word),
    .BEQ .x31 .x30 (40 : BitVec 13),
    .ADD .x5 .x12 .x31,
    .ADD .x7 .x29 .x31,
    .LBU .x5 .x5 (0 : BitVec 12),
    .LBU .x7 .x7 (0 : BitVec 12),
    .BNE .x5 .x7 (12 : BitVec 13),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_slot_written + 32) (GuestAddrs.bal_serializer_slot_written + 160)),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerSlotWritten_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerSlotWritten_relocs : RelocTable :=
  [ (4, .la .x5 "bal_builder_storage_change_count"),
    (11, .la .x29 "bal_builder_storage_changes") ]

def balSerializerSlotWrittenFunction : String :=
  "bal_serializer_slot_written:\n" ++ emitProgramR balSerializerSlotWritten_prog balSerializerSlotWritten_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerSlotWritten_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerSlotWrittenFunction_eq_prog :
    balSerializerSlotWrittenFunction = "bal_serializer_slot_written:\n" ++ emitProgramR balSerializerSlotWritten_prog balSerializerSlotWritten_relocs := rfl

#guard balSerializerSlotWrittenFunction.startsWith "bal_serializer_slot_written:\n"
#guard balSerializerSlotWritten_prog.length = 47
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
def balSerializerFilterReads_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .AUIPC .x5 (laHi 0 (balSerializerFilterReadsPc + 24)),
    .ADDI .x5 .x5 (laLo 0 (balSerializerFilterReadsPc + 24)),
    .SD .x5 .x0 (0 : BitVec 12),
    .LI .x9 (0 : Word),
    .AUIPC .x5 (laHi GuestAddrs.storage_reads_count (balSerializerFilterReadsPc + 40)),
    .ADDI .x5 .x5 (laLo GuestAddrs.storage_reads_count (balSerializerFilterReadsPc + 40)),
    .LD .x18 .x5 (0 : BitVec 12),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x18 (brOff (balSerializerFilterReadsPc + 128) (balSerializerFilterReadsPc + 56)),
    .LUI .x5 (20 : BitVec 20),
    .ADDIW .x5 .x5 (801 : BitVec 12),
    .SLLI .x5 .x5 (15 : BitVec 6),
    .ADDI .x5 .x5 (1920 : BitVec 12),
    .SLLI .x6 .x28 (6 : BitVec 6),
    .ADD .x29 .x5 .x6,
    .MV .x10 .x8,
    .MV .x11 .x29,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches (balSerializerFilterReadsPc + 92)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .ADDI .x10 .x29 (32 : BitVec 12),
    .MV .x11 .x8,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_slot_written (balSerializerFilterReadsPc + 108)),
    .BNE .x10 .x0 (8 : BitVec 13),
    .ADDI .x9 .x9 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (jalOff (balSerializerFilterReadsPc + 56) (balSerializerFilterReadsPc + 124)),
    .AUIPC .x5 (laHi 0 (balSerializerFilterReadsPc + 128)),
    .ADDI .x5 .x5 (laLo 0 (balSerializerFilterReadsPc + 128)),
    .SD .x5 .x9 (0 : BitVec 12),
    .MV .x10 .x9,
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerFilterReads_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerFilterReads_relocs : RelocTable :=
  [ (6, .la .x5 "bal_serializer_surviving_read_count"),
    (10, .la .x5 "storage_reads_count"),
    (23, .jal .x1 "bal_serializer_addr_matches"),
    (27, .jal .x1 "bal_serializer_slot_written"),
    (32, .la .x5 "bal_serializer_surviving_read_count") ]

def balSerializerFilterReadsFunction : String :=
  "bal_serializer_filter_reads:\n" ++ emitProgramR balSerializerFilterReads_prog balSerializerFilterReads_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerFilterReads_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerFilterReadsFunction_eq_prog :
    balSerializerFilterReadsFunction = "bal_serializer_filter_reads:\n" ++ emitProgramR balSerializerFilterReads_prog balSerializerFilterReads_relocs := rfl

#guard balSerializerFilterReadsFunction.startsWith "bal_serializer_filter_reads:\n"
#guard balSerializerFilterReads_prog.length = 42
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
def balSerializerMeasureReads_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .LI .x9 (0 : Word),
    .AUIPC .x5 (laHi GuestAddrs.storage_reads_count (GuestAddrs.bal_serializer_measure_reads + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.storage_reads_count (GuestAddrs.bal_serializer_measure_reads + 32)),
    .LD .x18 .x5 (0 : BitVec 12),
    .LI .x19 (0 : Word),
    .BGEU .x19 .x18 (brOff (GuestAddrs.bal_serializer_measure_reads + 176) (GuestAddrs.bal_serializer_measure_reads + 48)),
    .LUI .x5 (20 : BitVec 20),
    .ADDIW .x5 .x5 (801 : BitVec 12),
    .SLLI .x5 .x5 (15 : BitVec 6),
    .ADDI .x5 .x5 (1920 : BitVec 12),
    .SLLI .x6 .x19 (6 : BitVec 6),
    .ADD .x29 .x5 .x6,
    .MV .x10 .x8,
    .MV .x11 .x29,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches (GuestAddrs.bal_serializer_measure_reads + 84)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_measure_reads + 168) (GuestAddrs.bal_serializer_measure_reads + 88)),
    .LUI .x5 (20 : BitVec 20),
    .ADDIW .x5 .x5 (801 : BitVec 12),
    .SLLI .x5 .x5 (15 : BitVec 6),
    .ADDI .x5 .x5 (1920 : BitVec 12),
    .SLLI .x6 .x19 (6 : BitVec 6),
    .ADD .x29 .x5 .x6,
    .ADDI .x10 .x29 (32 : BitVec 12),
    .MV .x11 .x8,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_slot_written (GuestAddrs.bal_serializer_measure_reads + 124)),
    .BNE .x10 .x0 (40 : BitVec 13),
    .LUI .x5 (20 : BitVec 20),
    .ADDIW .x5 .x5 (801 : BitVec 12),
    .SLLI .x5 .x5 (15 : BitVec 6),
    .ADDI .x5 .x5 (1920 : BitVec 12),
    .SLLI .x6 .x19 (6 : BitVec 6),
    .ADD .x29 .x5 .x6,
    .ADDI .x10 .x29 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_measure_reads + 160)),
    .ADD .x9 .x9 .x10,
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_measure_reads + 48) (GuestAddrs.bal_serializer_measure_reads + 172)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_reads + 176)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_reads + 176)),
    .SD .x5 .x9 (16 : BitVec 12),
    .MV .x10 .x9,
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerMeasureReads_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerMeasureReads_relocs : RelocTable :=
  [ (8, .la .x5 "storage_reads_count"),
    (21, .jal .x1 "bal_serializer_addr_matches"),
    (31, .jal .x1 "bal_serializer_slot_written"),
    (40, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (44, .la .x5 "bal_serializer_len_table") ]

def balSerializerMeasureReadsFunction : String :=
  "bal_serializer_measure_reads:\n" ++ emitProgramR balSerializerMeasureReads_prog balSerializerMeasureReads_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerMeasureReads_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerMeasureReadsFunction_eq_prog :
    balSerializerMeasureReadsFunction = "bal_serializer_measure_reads:\n" ++ emitProgramR balSerializerMeasureReads_prog balSerializerMeasureReads_relocs := rfl

#guard balSerializerMeasureReadsFunction.startsWith "bal_serializer_measure_reads:\n"
#guard balSerializerMeasureReads_prog.length = 55
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
def balSerializerSlotToLe_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.bal_serializer_slot_le (GuestAddrs.bal_serializer_slot_to_le + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_slot_le (GuestAddrs.bal_serializer_slot_to_le + 0)),
    .LI .x6 (32 : Word),
    .ADDI .x7 .x10 (31 : BitVec 12),
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x28 .x7 (0 : BitVec 12),
    .SB .x5 .x28 (0 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerSlotToLe_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerSlotToLe_relocs : RelocTable :=
  [ (0, .la .x5 "bal_serializer_slot_le") ]

def balSerializerSlotToLeFunction : String :=
  "bal_serializer_slot_to_le:\n" ++ emitProgramR balSerializerSlotToLe_prog balSerializerSlotToLe_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerSlotToLe_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerSlotToLeFunction_eq_prog :
    balSerializerSlotToLeFunction = "bal_serializer_slot_to_le:\n" ++ emitProgramR balSerializerSlotToLe_prog balSerializerSlotToLe_relocs := rfl

#guard balSerializerSlotToLeFunction.startsWith "bal_serializer_slot_to_le:\n"
#guard balSerializerSlotToLe_prog.length = 12
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
def balSerializerBalanceToLe_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.bal_serializer_balance_le (GuestAddrs.bal_serializer_balance_to_le + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_balance_le (GuestAddrs.bal_serializer_balance_to_le + 0)),
    .LI .x6 (32 : Word),
    .ADDI .x7 .x10 (31 : BitVec 12),
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x28 .x7 (0 : BitVec 12),
    .SB .x5 .x28 (0 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerBalanceToLe_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerBalanceToLe_relocs : RelocTable :=
  [ (0, .la .x5 "bal_serializer_balance_le") ]

def balSerializerBalanceToLeFunction : String :=
  "bal_serializer_balance_to_le:\n" ++ emitProgramR balSerializerBalanceToLe_prog balSerializerBalanceToLe_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerBalanceToLe_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerBalanceToLeFunction_eq_prog :
    balSerializerBalanceToLeFunction = "bal_serializer_balance_to_le:\n" ++ emitProgramR balSerializerBalanceToLe_prog balSerializerBalanceToLe_relocs := rfl

#guard balSerializerBalanceToLeFunction.startsWith "bal_serializer_balance_to_le:\n"
#guard balSerializerBalanceToLe_prog.length = 12
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
def balSerializerMeasureSlot_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x20 (24 : BitVec 12),
    .SD .x2 .x21 (32 : BitVec 12),
    .SD .x2 .x22 (40 : BitVec 12),
    .SD .x2 .x23 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x20 .x11,
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_storage_change_count (GuestAddrs.bal_serializer_measure_slot + 40)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_storage_change_count (GuestAddrs.bal_serializer_measure_slot + 40)),
    .LD .x9 .x5 (0 : BitVec 12),
    .LI .x21 (0 : Word),
    .LI .x22 (0 : Word),
    .BGEU .x22 .x9 (brOff (GuestAddrs.bal_serializer_measure_slot + 184) (GuestAddrs.bal_serializer_measure_slot + 60)),
    .LI .x5 (96 : Word),
    .MUL .x6 .x22 .x5,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_measure_slot + 72)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_measure_slot + 72)),
    .ADD .x23 .x7 .x6,
    .MV .x10 .x8,
    .MV .x11 .x23,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches_be (GuestAddrs.bal_serializer_measure_slot + 92)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_measure_slot + 176) (GuestAddrs.bal_serializer_measure_slot + 96)),
    .ADDI .x10 .x20 (32 : BitVec 12),
    .ADDI .x11 .x23 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_slot_eq (GuestAddrs.bal_serializer_measure_slot + 108)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_measure_slot + 176) (GuestAddrs.bal_serializer_measure_slot + 112)),
    .LD .x11 .x23 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_slot + 120)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_slot + 120)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_measure_slot + 128)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_slot + 132)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_slot + 132)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_measure_slot + 140)),
    .MV .x30 .x10,
    .ADDI .x10 .x23 (64 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_measure_slot + 152)),
    .ADD .x30 .x30 .x10,
    .MV .x10 .x30,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_list_header_len (GuestAddrs.bal_serializer_measure_slot + 164)),
    .ADD .x30 .x30 .x10,
    .ADD .x21 .x21 .x30,
    .ADDI .x22 .x22 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_measure_slot + 60) (GuestAddrs.bal_serializer_measure_slot + 180)),
    .MV .x23 .x21,
    .MV .x10 .x21,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_list_header_len (GuestAddrs.bal_serializer_measure_slot + 192)),
    .ADD .x21 .x21 .x10,
    .ADDI .x10 .x20 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_slot_to_le (GuestAddrs.bal_serializer_measure_slot + 204)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_slot_le (GuestAddrs.bal_serializer_measure_slot + 208)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_slot_le (GuestAddrs.bal_serializer_measure_slot + 208)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_measure_slot + 216)),
    .ADD .x21 .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x23,
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x20 .x2 (24 : BitVec 12),
    .LD .x21 .x2 (32 : BitVec 12),
    .LD .x22 .x2 (40 : BitVec 12),
    .LD .x23 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerMeasureSlot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerMeasureSlot_relocs : RelocTable :=
  [ (10, .la .x5 "bal_builder_storage_change_count"),
    (18, .la .x7 "bal_builder_storage_changes"),
    (23, .jal .x1 "bal_serializer_addr_matches_be"),
    (27, .jal .x1 "bal_serializer_slot_eq"),
    (30, .la .x10 "bal_serializer_u64_field"),
    (32, .jal .x1 "bal_serializer_u64_to_field"),
    (33, .la .x10 "bal_serializer_u64_field"),
    (35, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (38, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (41, .jal .x1 "bal_rlp_list_header_len"),
    (48, .jal .x1 "bal_rlp_list_header_len"),
    (51, .jal .x1 "bal_serializer_slot_to_le"),
    (52, .la .x10 "bal_serializer_slot_le"),
    (54, .jal .x1 "bal_rlp_scalar_rlp_len") ]

def balSerializerMeasureSlotFunction : String :=
  "bal_serializer_measure_slot:\n" ++ emitProgramR balSerializerMeasureSlot_prog balSerializerMeasureSlot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerMeasureSlot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerMeasureSlotFunction_eq_prog :
    balSerializerMeasureSlotFunction = "bal_serializer_measure_slot:\n" ++ emitProgramR balSerializerMeasureSlot_prog balSerializerMeasureSlot_relocs := rfl

#guard balSerializerMeasureSlotFunction.startsWith "bal_serializer_measure_slot:\n"
#guard balSerializerMeasureSlot_prog.length = 67
def balSerializerMeasureStorage_prog : Program :=
  [ .ADDI .x2 .x2 (-96 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .MV .x8 .x10,
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_storage_change_count (GuestAddrs.bal_serializer_measure_storage + 44)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_storage_change_count (GuestAddrs.bal_serializer_measure_storage + 44)),
    .LD .x9 .x5 (0 : BitVec 12),
    .LI .x18 (0 : Word),
    .LI .x19 (0 : Word),
    .BGEU .x19 .x9 (brOff (GuestAddrs.bal_serializer_measure_storage + 164) (GuestAddrs.bal_serializer_measure_storage + 64)),
    .LI .x5 (96 : Word),
    .MUL .x6 .x19 .x5,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_measure_storage + 76)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_measure_storage + 76)),
    .ADD .x20 .x7 .x6,
    .MV .x10 .x8,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches_be (GuestAddrs.bal_serializer_measure_storage + 96)),
    .BEQ .x10 .x0 (56 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x20,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_slot_seen_before (GuestAddrs.bal_serializer_measure_storage + 116)),
    .BNE .x10 .x0 (36 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_measure_slot (GuestAddrs.bal_serializer_measure_storage + 132)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_list_header_len (GuestAddrs.bal_serializer_measure_storage + 144)),
    .ADD .x21 .x21 .x10,
    .ADD .x18 .x18 .x21,
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_measure_storage + 64) (GuestAddrs.bal_serializer_measure_storage + 160)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_storage + 164)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_storage + 164)),
    .SD .x5 .x18 (8 : BitVec 12),
    .MV .x10 .x18,
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (96 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerMeasureStorage_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerMeasureStorage_relocs : RelocTable :=
  [ (11, .la .x5 "bal_builder_storage_change_count"),
    (19, .la .x7 "bal_builder_storage_changes"),
    (24, .jal .x1 "bal_serializer_addr_matches_be"),
    (29, .jal .x1 "bal_serializer_slot_seen_before"),
    (33, .jal .x1 "bal_serializer_measure_slot"),
    (36, .jal .x1 "bal_rlp_list_header_len"),
    (41, .la .x5 "bal_serializer_len_table") ]

def balSerializerMeasureStorageFunction : String :=
  "bal_serializer_measure_storage:\n" ++ emitProgramR balSerializerMeasureStorage_prog balSerializerMeasureStorage_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerMeasureStorage_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerMeasureStorageFunction_eq_prog :
    balSerializerMeasureStorageFunction = "bal_serializer_measure_storage:\n" ++ emitProgramR balSerializerMeasureStorage_prog balSerializerMeasureStorage_relocs := rfl

#guard balSerializerMeasureStorageFunction.startsWith "bal_serializer_measure_storage:\n"
#guard balSerializerMeasureStorage_prog.length = 56
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
def balSerializerSlotSeenBefore_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .LI .x19 (0 : Word),
    .BGEU .x19 .x18 (brOff (GuestAddrs.bal_serializer_slot_seen_before + 132) (GuestAddrs.bal_serializer_slot_seen_before + 40)),
    .LI .x5 (96 : Word),
    .MUL .x6 .x19 .x5,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_slot_seen_before + 52)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_slot_seen_before + 52)),
    .ADD .x28 .x7 .x6,
    .MV .x10 .x8,
    .MV .x11 .x28,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches_be (GuestAddrs.bal_serializer_slot_seen_before + 72)),
    .BEQ .x10 .x0 (40 : BitVec 13),
    .LI .x5 (96 : Word),
    .MUL .x6 .x19 .x5,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_slot_seen_before + 88)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_slot_seen_before + 88)),
    .ADD .x28 .x7 .x6,
    .ADDI .x10 .x9 (32 : BitVec 12),
    .ADDI .x11 .x28 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_slot_eq (GuestAddrs.bal_serializer_slot_seen_before + 108)),
    .BNE .x10 .x0 (12 : BitVec 13),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_slot_seen_before + 40) (GuestAddrs.bal_serializer_slot_seen_before + 120)),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerSlotSeenBefore_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerSlotSeenBefore_relocs : RelocTable :=
  [ (13, .la .x7 "bal_builder_storage_changes"),
    (18, .jal .x1 "bal_serializer_addr_matches_be"),
    (22, .la .x7 "bal_builder_storage_changes"),
    (27, .jal .x1 "bal_serializer_slot_eq") ]

def balSerializerSlotSeenBeforeFunction : String :=
  "bal_serializer_slot_seen_before:\n" ++ emitProgramR balSerializerSlotSeenBefore_prog balSerializerSlotSeenBefore_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerSlotSeenBefore_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerSlotSeenBeforeFunction_eq_prog :
    balSerializerSlotSeenBeforeFunction = "bal_serializer_slot_seen_before:\n" ++ emitProgramR balSerializerSlotSeenBefore_prog balSerializerSlotSeenBefore_relocs := rfl

#guard balSerializerSlotSeenBeforeFunction.startsWith "bal_serializer_slot_seen_before:\n"
#guard balSerializerSlotSeenBefore_prog.length = 41
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

def balSerializerMeasureBalance_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_balance_count (GuestAddrs.bal_serializer_measure_balance + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_balance_count (GuestAddrs.bal_serializer_measure_balance + 32)),
    .LD .x9 .x5 (0 : BitVec 12),
    .LI .x18 (0 : Word),
    .LI .x19 (0 : Word),
    .BGEU .x19 .x9 (brOff (GuestAddrs.bal_serializer_measure_balance + 172) (GuestAddrs.bal_serializer_measure_balance + 52)),
    .LI .x5 (64 : Word),
    .MUL .x6 .x19 .x5,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_balance_changes (GuestAddrs.bal_serializer_measure_balance + 64)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_balance_changes (GuestAddrs.bal_serializer_measure_balance + 64)),
    .ADD .x20 .x7 .x6,
    .MV .x10 .x8,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches_be (GuestAddrs.bal_serializer_measure_balance + 84)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_measure_balance + 164) (GuestAddrs.bal_serializer_measure_balance + 88)),
    .LD .x11 .x20 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_balance + 96)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_balance + 96)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_measure_balance + 104)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_balance + 108)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_balance + 108)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_measure_balance + 116)),
    .MV .x30 .x10,
    .ADDI .x10 .x20 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_balance_to_le (GuestAddrs.bal_serializer_measure_balance + 128)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_balance_le (GuestAddrs.bal_serializer_measure_balance + 132)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_balance_le (GuestAddrs.bal_serializer_measure_balance + 132)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_measure_balance + 140)),
    .ADD .x30 .x30 .x10,
    .MV .x10 .x30,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_list_header_len (GuestAddrs.bal_serializer_measure_balance + 152)),
    .ADD .x30 .x30 .x10,
    .ADD .x18 .x18 .x30,
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_measure_balance + 52) (GuestAddrs.bal_serializer_measure_balance + 168)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_balance + 172)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_balance + 172)),
    .SD .x5 .x18 (24 : BitVec 12),
    .MV .x10 .x18,
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerMeasureBalance_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerMeasureBalance_relocs : RelocTable :=
  [ (8, .la .x5 "bal_builder_balance_count"),
    (16, .la .x7 "bal_builder_balance_changes"),
    (21, .jal .x1 "bal_serializer_addr_matches_be"),
    (24, .la .x10 "bal_serializer_u64_field"),
    (26, .jal .x1 "bal_serializer_u64_to_field"),
    (27, .la .x10 "bal_serializer_u64_field"),
    (29, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (32, .jal .x1 "bal_serializer_balance_to_le"),
    (33, .la .x10 "bal_serializer_balance_le"),
    (35, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (38, .jal .x1 "bal_rlp_list_header_len"),
    (43, .la .x5 "bal_serializer_len_table") ]

def balSerializerMeasureBalanceFunction : String :=
  "bal_serializer_measure_balance:\n" ++ emitProgramR balSerializerMeasureBalance_prog balSerializerMeasureBalance_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerMeasureBalance_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerMeasureBalanceFunction_eq_prog :
    balSerializerMeasureBalanceFunction = "bal_serializer_measure_balance:\n" ++ emitProgramR balSerializerMeasureBalance_prog balSerializerMeasureBalance_relocs := rfl

#guard balSerializerMeasureBalanceFunction.startsWith "bal_serializer_measure_balance:\n"
#guard balSerializerMeasureBalance_prog.length = 55
/-- Builder rows hold a canonical BE20 address at +0, so this compares directly rather
    than reversing a stack word the way `bal_serializer_addr_matches` must for read
    rows. Two routines because the two row families store the address differently — the
    encoding split the sort descriptors already record. -/

def balSerializerMeasureNonce_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_nonce_count (GuestAddrs.bal_serializer_measure_nonce + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_nonce_count (GuestAddrs.bal_serializer_measure_nonce + 32)),
    .LD .x9 .x5 (0 : BitVec 12),
    .LI .x18 (0 : Word),
    .LI .x19 (0 : Word),
    .BGEU .x19 .x9 (brOff (GuestAddrs.bal_serializer_measure_nonce + 184) (GuestAddrs.bal_serializer_measure_nonce + 52)),
    .SLLI .x6 .x19 (5 : BitVec 6),
    .SLLI .x7 .x19 (3 : BitVec 6),
    .ADD .x6 .x6 .x7,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_nonce_changes (GuestAddrs.bal_serializer_measure_nonce + 68)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_nonce_changes (GuestAddrs.bal_serializer_measure_nonce + 68)),
    .ADD .x20 .x7 .x6,
    .MV .x10 .x8,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches_be (GuestAddrs.bal_serializer_measure_nonce + 88)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_measure_nonce + 176) (GuestAddrs.bal_serializer_measure_nonce + 92)),
    .LD .x11 .x20 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_nonce + 100)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_nonce + 100)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_measure_nonce + 108)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_nonce + 112)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_nonce + 112)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_measure_nonce + 120)),
    .MV .x30 .x10,
    .LD .x11 .x20 (32 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_nonce + 132)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_nonce + 132)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_measure_nonce + 140)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_nonce + 144)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_nonce + 144)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_measure_nonce + 152)),
    .ADD .x30 .x30 .x10,
    .MV .x10 .x30,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_list_header_len (GuestAddrs.bal_serializer_measure_nonce + 164)),
    .ADD .x30 .x30 .x10,
    .ADD .x18 .x18 .x30,
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_measure_nonce + 52) (GuestAddrs.bal_serializer_measure_nonce + 180)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_nonce + 184)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_nonce + 184)),
    .SD .x5 .x18 (32 : BitVec 12),
    .MV .x10 .x18,
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerMeasureNonce_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerMeasureNonce_relocs : RelocTable :=
  [ (8, .la .x5 "bal_builder_nonce_count"),
    (17, .la .x7 "bal_builder_nonce_changes"),
    (22, .jal .x1 "bal_serializer_addr_matches_be"),
    (25, .la .x10 "bal_serializer_u64_field"),
    (27, .jal .x1 "bal_serializer_u64_to_field"),
    (28, .la .x10 "bal_serializer_u64_field"),
    (30, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (33, .la .x10 "bal_serializer_u64_field"),
    (35, .jal .x1 "bal_serializer_u64_to_field"),
    (36, .la .x10 "bal_serializer_u64_field"),
    (38, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (41, .jal .x1 "bal_rlp_list_header_len"),
    (46, .la .x5 "bal_serializer_len_table") ]

def balSerializerMeasureNonceFunction : String :=
  "bal_serializer_measure_nonce:\n" ++ emitProgramR balSerializerMeasureNonce_prog balSerializerMeasureNonce_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerMeasureNonce_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerMeasureNonceFunction_eq_prog :
    balSerializerMeasureNonceFunction = "bal_serializer_measure_nonce:\n" ++ emitProgramR balSerializerMeasureNonce_prog balSerializerMeasureNonce_relocs := rfl

#guard balSerializerMeasureNonceFunction.startsWith "bal_serializer_measure_nonce:\n"
#guard balSerializerMeasureNonce_prog.length = 58
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
def balSerializerMeasureCode_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_code_count (GuestAddrs.bal_serializer_measure_code + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_code_count (GuestAddrs.bal_serializer_measure_code + 32)),
    .LD .x9 .x5 (0 : BitVec 12),
    .LI .x18 (0 : Word),
    .LI .x19 (0 : Word),
    .BGEU .x19 .x9 (brOff (GuestAddrs.bal_serializer_measure_code + 192) (GuestAddrs.bal_serializer_measure_code + 52)),
    .SLLI .x6 .x19 (6 : BitVec 6),
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_code_changes (GuestAddrs.bal_serializer_measure_code + 60)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_code_changes (GuestAddrs.bal_serializer_measure_code + 60)),
    .ADD .x20 .x7 .x6,
    .MV .x10 .x8,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches_be (GuestAddrs.bal_serializer_measure_code + 80)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_measure_code + 184) (GuestAddrs.bal_serializer_measure_code + 84)),
    .LD .x11 .x20 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_code + 92)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_code + 92)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_measure_code + 100)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_code + 104)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_measure_code + 104)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_measure_code + 112)),
    .MV .x30 .x10,
    .SD .x2 .x30 (48 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_throwaway_ctx (GuestAddrs.bal_serializer_measure_code + 124)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_throwaway_ctx (GuestAddrs.bal_serializer_measure_code + 124)),
    .AUIPC .x11 (laHi GuestAddrs.bal_rlp_emit_bytes (GuestAddrs.bal_serializer_measure_code + 132)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_rlp_emit_bytes (GuestAddrs.bal_serializer_measure_code + 132)),
    .LD .x12 .x20 (32 : BitVec 12),
    .LD .x13 .x20 (40 : BitVec 12),
    .AUIPC .x14 (laHi GuestAddrs.bal_serializer_hdr_scratch (GuestAddrs.bal_serializer_measure_code + 148)),
    .ADDI .x14 .x14 (laLo GuestAddrs.bal_serializer_hdr_scratch (GuestAddrs.bal_serializer_measure_code + 148)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_measure_into_throwaway (GuestAddrs.bal_serializer_measure_code + 156)),
    .LD .x30 .x2 (48 : BitVec 12),
    .ADD .x30 .x30 .x10,
    .MV .x10 .x30,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_list_header_len (GuestAddrs.bal_serializer_measure_code + 172)),
    .ADD .x30 .x30 .x10,
    .ADD .x18 .x18 .x30,
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_measure_code + 52) (GuestAddrs.bal_serializer_measure_code + 188)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_code + 192)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_code + 192)),
    .SD .x5 .x18 (40 : BitVec 12),
    .MV .x10 .x18,
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerMeasureCode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerMeasureCode_relocs : RelocTable :=
  [ (8, .la .x5 "bal_builder_code_count"),
    (15, .la .x7 "bal_builder_code_changes"),
    (20, .jal .x1 "bal_serializer_addr_matches_be"),
    (23, .la .x10 "bal_serializer_u64_field"),
    (25, .jal .x1 "bal_serializer_u64_to_field"),
    (26, .la .x10 "bal_serializer_u64_field"),
    (28, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (31, .la .x10 "bal_serializer_throwaway_ctx"),
    (33, .la .x11 "bal_rlp_emit_bytes"),
    (37, .la .x14 "bal_serializer_hdr_scratch"),
    (39, .jal .x1 "bal_rlp_measure_into_throwaway"),
    (43, .jal .x1 "bal_rlp_list_header_len"),
    (48, .la .x5 "bal_serializer_len_table") ]

def balSerializerMeasureCodeFunction : String :=
  "bal_serializer_measure_code:\n" ++ emitProgramR balSerializerMeasureCode_prog balSerializerMeasureCode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerMeasureCode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerMeasureCodeFunction_eq_prog :
    balSerializerMeasureCodeFunction = "bal_serializer_measure_code:\n" ++ emitProgramR balSerializerMeasureCode_prog balSerializerMeasureCode_relocs := rfl

#guard balSerializerMeasureCodeFunction.startsWith "bal_serializer_measure_code:\n"
#guard balSerializerMeasureCode_prog.length = 60
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
def balSerializerMeasureAccount_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .LI .x9 (0 : Word),
    .ADDI .x9 .x9 (21 : BitVec 12),
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_measure_storage (GuestAddrs.bal_serializer_measure_account + 32)),
    .MV .x10 .x10,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_list_header_len (GuestAddrs.bal_serializer_measure_account + 40)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_account + 44)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_account + 44)),
    .LD .x6 .x5 (8 : BitVec 12),
    .ADD .x9 .x9 .x6,
    .ADD .x9 .x9 .x10,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_measure_reads (GuestAddrs.bal_serializer_measure_account + 68)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_list_header_len (GuestAddrs.bal_serializer_measure_account + 72)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_account + 76)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_account + 76)),
    .LD .x6 .x5 (16 : BitVec 12),
    .ADD .x9 .x9 .x6,
    .ADD .x9 .x9 .x10,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_measure_balance (GuestAddrs.bal_serializer_measure_account + 100)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_list_header_len (GuestAddrs.bal_serializer_measure_account + 104)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_account + 108)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_account + 108)),
    .LD .x6 .x5 (24 : BitVec 12),
    .ADD .x9 .x9 .x6,
    .ADD .x9 .x9 .x10,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_measure_nonce (GuestAddrs.bal_serializer_measure_account + 132)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_list_header_len (GuestAddrs.bal_serializer_measure_account + 136)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_account + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_account + 140)),
    .LD .x6 .x5 (32 : BitVec 12),
    .ADD .x9 .x9 .x6,
    .ADD .x9 .x9 .x10,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_measure_code (GuestAddrs.bal_serializer_measure_account + 164)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_list_header_len (GuestAddrs.bal_serializer_measure_account + 168)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_account + 172)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_account + 172)),
    .LD .x6 .x5 (40 : BitVec 12),
    .ADD .x9 .x9 .x6,
    .ADD .x9 .x9 .x10,
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_account + 192)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_measure_account + 192)),
    .SD .x5 .x9 (0 : BitVec 12),
    .MV .x10 .x9,
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerMeasureAccount_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerMeasureAccount_relocs : RelocTable :=
  [ (8, .jal .x1 "bal_serializer_measure_storage"),
    (10, .jal .x1 "bal_rlp_list_header_len"),
    (11, .la .x5 "bal_serializer_len_table"),
    (17, .jal .x1 "bal_serializer_measure_reads"),
    (18, .jal .x1 "bal_rlp_list_header_len"),
    (19, .la .x5 "bal_serializer_len_table"),
    (25, .jal .x1 "bal_serializer_measure_balance"),
    (26, .jal .x1 "bal_rlp_list_header_len"),
    (27, .la .x5 "bal_serializer_len_table"),
    (33, .jal .x1 "bal_serializer_measure_nonce"),
    (34, .jal .x1 "bal_rlp_list_header_len"),
    (35, .la .x5 "bal_serializer_len_table"),
    (41, .jal .x1 "bal_serializer_measure_code"),
    (42, .jal .x1 "bal_rlp_list_header_len"),
    (43, .la .x5 "bal_serializer_len_table"),
    (48, .la .x5 "bal_serializer_len_table") ]

def balSerializerMeasureAccountFunction : String :=
  "bal_serializer_measure_account:\n" ++ emitProgramR balSerializerMeasureAccount_prog balSerializerMeasureAccount_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerMeasureAccount_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerMeasureAccountFunction_eq_prog :
    balSerializerMeasureAccountFunction = "bal_serializer_measure_account:\n" ++ emitProgramR balSerializerMeasureAccount_prog balSerializerMeasureAccount_relocs := rfl

#guard balSerializerMeasureAccountFunction.startsWith "bal_serializer_measure_account:\n"
#guard balSerializerMeasureAccount_prog.length = 57
