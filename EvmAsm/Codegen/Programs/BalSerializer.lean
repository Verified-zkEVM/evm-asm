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
def balSerializerEmitStorage_prog : Program :=
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
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_storage_change_count (GuestAddrs.bal_serializer_emit_storage + 56)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_storage_change_count (GuestAddrs.bal_serializer_emit_storage + 56)),
    .LD .x19 .x5 (0 : BitVec 12),
    .LI .x20 (0 : Word),
    .BGEU .x20 .x19 (brOff (GuestAddrs.bal_serializer_emit_storage + 432) (GuestAddrs.bal_serializer_emit_storage + 72)),
    .LI .x5 (96 : Word),
    .MUL .x6 .x20 .x5,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_emit_storage + 84)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_emit_storage + 84)),
    .ADD .x21 .x7 .x6,
    .MV .x10 .x9,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches_be (GuestAddrs.bal_serializer_emit_storage + 104)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_emit_storage + 424) (GuestAddrs.bal_serializer_emit_storage + 108)),
    .MV .x10 .x9,
    .MV .x11 .x21,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_slot_seen_before (GuestAddrs.bal_serializer_emit_storage + 124)),
    .BNE .x10 .x0 (brOff (GuestAddrs.bal_serializer_emit_storage + 424) (GuestAddrs.bal_serializer_emit_storage + 128)),
    .MV .x10 .x9,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_measure_slot (GuestAddrs.bal_serializer_emit_storage + 140)),
    .MV .x22 .x10,
    .MV .x23 .x11,
    .MV .x10 .x8,
    .MV .x11 .x22,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_storage + 164)),
    .ADDI .x10 .x21 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_slot_to_le (GuestAddrs.bal_serializer_emit_storage + 172)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_slot_le (GuestAddrs.bal_serializer_emit_storage + 180)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_slot_le (GuestAddrs.bal_serializer_emit_storage + 180)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_storage + 192)),
    .MV .x10 .x8,
    .MV .x11 .x23,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_storage + 208)),
    .LI .x24 (0 : Word),
    .BGEU .x24 .x19 (brOff (GuestAddrs.bal_serializer_emit_storage + 424) (GuestAddrs.bal_serializer_emit_storage + 216)),
    .LI .x5 (96 : Word),
    .MUL .x6 .x24 .x5,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_emit_storage + 228)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_emit_storage + 228)),
    .ADD .x28 .x7 .x6,
    .SD .x2 .x28 (80 : BitVec 12),
    .MV .x10 .x9,
    .MV .x11 .x28,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches_be (GuestAddrs.bal_serializer_emit_storage + 252)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_emit_storage + 416) (GuestAddrs.bal_serializer_emit_storage + 256)),
    .LD .x28 .x2 (80 : BitVec 12),
    .ADDI .x10 .x21 (32 : BitVec 12),
    .ADDI .x11 .x28 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_slot_eq (GuestAddrs.bal_serializer_emit_storage + 272)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_emit_storage + 416) (GuestAddrs.bal_serializer_emit_storage + 276)),
    .LD .x28 .x2 (80 : BitVec 12),
    .LD .x11 .x28 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_storage + 288)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_storage + 288)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_emit_storage + 296)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_storage + 300)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_storage + 300)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_emit_storage + 308)),
    .SD .x2 .x10 (88 : BitVec 12),
    .LD .x28 .x2 (80 : BitVec 12),
    .ADDI .x10 .x28 (64 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_emit_storage + 324)),
    .LD .x29 .x2 (88 : BitVec 12),
    .ADD .x29 .x29 .x10,
    .SD .x2 .x29 (88 : BitVec 12),
    .MV .x10 .x8,
    .LD .x11 .x2 (88 : BitVec 12),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_storage + 352)),
    .AUIPC .x5 (laHi GuestAddrs.bv_bal_shadow_emit_storage_changes (GuestAddrs.bal_serializer_emit_storage + 356)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_bal_shadow_emit_storage_changes (GuestAddrs.bal_serializer_emit_storage + 356)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_storage + 380)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_storage + 380)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_storage + 392)),
    .LD .x28 .x2 (80 : BitVec 12),
    .MV .x10 .x8,
    .ADDI .x11 .x28 (64 : BitVec 12),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_storage + 412)),
    .ADDI .x24 .x24 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_emit_storage + 216) (GuestAddrs.bal_serializer_emit_storage + 420)),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_emit_storage + 72) (GuestAddrs.bal_serializer_emit_storage + 428)),
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
    .ADDI .x2 .x2 (112 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerEmitStorage_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerEmitStorage_relocs : RelocTable :=
  [ (14, .la .x5 "bal_builder_storage_change_count"),
    (21, .la .x7 "bal_builder_storage_changes"),
    (26, .jal .x1 "bal_serializer_addr_matches_be"),
    (31, .jal .x1 "bal_serializer_slot_seen_before"),
    (35, .jal .x1 "bal_serializer_measure_slot"),
    (41, .jal .x1 "bal_rlp_emit_list_header"),
    (43, .jal .x1 "bal_serializer_slot_to_le"),
    (45, .la .x11 "bal_serializer_slot_le"),
    (48, .jal .x1 "bal_rlp_emit_scalar"),
    (52, .jal .x1 "bal_rlp_emit_list_header"),
    (57, .la .x7 "bal_builder_storage_changes"),
    (63, .jal .x1 "bal_serializer_addr_matches_be"),
    (68, .jal .x1 "bal_serializer_slot_eq"),
    (72, .la .x10 "bal_serializer_u64_field"),
    (74, .jal .x1 "bal_serializer_u64_to_field"),
    (75, .la .x10 "bal_serializer_u64_field"),
    (77, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (81, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (88, .jal .x1 "bal_rlp_emit_list_header"),
    (89, .la .x5 "bv_bal_shadow_emit_storage_changes"),
    (95, .la .x11 "bal_serializer_u64_field"),
    (98, .jal .x1 "bal_rlp_emit_scalar"),
    (103, .jal .x1 "bal_rlp_emit_scalar") ]

def balSerializerEmitStorageFunction : String :=
  "bal_serializer_emit_storage:\n" ++ emitProgramR balSerializerEmitStorage_prog balSerializerEmitStorage_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerEmitStorage_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerEmitStorageFunction_eq_prog :
    balSerializerEmitStorageFunction = "bal_serializer_emit_storage:\n" ++ emitProgramR balSerializerEmitStorage_prog balSerializerEmitStorage_relocs := rfl

#guard balSerializerEmitStorageFunction.startsWith "bal_serializer_emit_storage:\n"
#guard balSerializerEmitStorage_prog.length = 120
/-- Emit `storage_reads`: a flat list of slot scalars. a0 = ctx, a1 = address, a2 = scratch.

    Mirrors `bal_serializer_measure_reads`, including its use of
    `bal_serializer_addr_matches` -- the REVERSING comparator -- rather than the `_be`
    one. Read rows come from the exec log at `0xa1908780` and hold the address in the low
    bytes of an LE stack word, unlike the builder rows, which are big-endian. The two
    comparators are not interchangeable and picking the wrong one silently matches
    nothing. -/
def balSerializerEmitReads_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x5 (laHi GuestAddrs.storage_reads_count (GuestAddrs.bal_serializer_emit_reads + 40)),
    .ADDI .x5 .x5 (laLo GuestAddrs.storage_reads_count (GuestAddrs.bal_serializer_emit_reads + 40)),
    .LD .x19 .x5 (0 : BitVec 12),
    .LI .x20 (0 : Word),
    .BGEU .x20 .x19 (brOff (GuestAddrs.bal_serializer_emit_reads + 172) (GuestAddrs.bal_serializer_emit_reads + 56)),
    .LUI .x5 (20 : BitVec 20),
    .ADDIW .x5 .x5 (801 : BitVec 12),
    .SLLI .x5 .x5 (15 : BitVec 6),
    .ADDI .x5 .x5 (1920 : BitVec 12),
    .SLLI .x6 .x20 (6 : BitVec 6),
    .ADD .x29 .x5 .x6,
    .SD .x2 .x29 (48 : BitVec 12),
    .MV .x10 .x9,
    .MV .x11 .x29,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches (GuestAddrs.bal_serializer_emit_reads + 96)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_emit_reads + 164) (GuestAddrs.bal_serializer_emit_reads + 100)),
    .LD .x29 .x2 (48 : BitVec 12),
    .ADDI .x10 .x29 (32 : BitVec 12),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_slot_written (GuestAddrs.bal_serializer_emit_reads + 116)),
    .BNE .x10 .x0 (44 : BitVec 13),
    .LD .x29 .x2 (48 : BitVec 12),
    .MV .x10 .x8,
    .ADDI .x11 .x29 (32 : BitVec 12),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_reads + 140)),
    .AUIPC .x5 (laHi GuestAddrs.bv_bal_shadow_emit_storage_reads (GuestAddrs.bal_serializer_emit_reads + 144)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_bal_shadow_emit_storage_reads (GuestAddrs.bal_serializer_emit_reads + 144)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_emit_reads + 56) (GuestAddrs.bal_serializer_emit_reads + 168)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerEmitReads_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerEmitReads_relocs : RelocTable :=
  [ (10, .la .x5 "storage_reads_count"),
    (24, .jal .x1 "bal_serializer_addr_matches"),
    (29, .jal .x1 "bal_serializer_slot_written"),
    (35, .jal .x1 "bal_rlp_emit_scalar"),
    (36, .la .x5 "bv_bal_shadow_emit_storage_reads") ]

def balSerializerEmitReadsFunction : String :=
  "bal_serializer_emit_reads:\n" ++ emitProgramR balSerializerEmitReads_prog balSerializerEmitReads_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerEmitReads_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerEmitReadsFunction_eq_prog :
    balSerializerEmitReadsFunction = "bal_serializer_emit_reads:\n" ++ emitProgramR balSerializerEmitReads_prog balSerializerEmitReads_relocs := rfl

#guard balSerializerEmitReadsFunction.startsWith "bal_serializer_emit_reads:\n"
#guard balSerializerEmitReads_prog.length = 51
/-- Emit `balance_changes`: one `[block_access_index, post_balance]` list per row.
    a0 = ctx, a1 = address, a2 = scratch. Mirrors `bal_serializer_measure_balance`. -/
def balSerializerEmitBalance_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_balance_count (GuestAddrs.bal_serializer_emit_balance + 40)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_balance_count (GuestAddrs.bal_serializer_emit_balance + 40)),
    .LD .x19 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bald_bal_builder_count (GuestAddrs.bal_serializer_emit_balance + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_bal_builder_count (GuestAddrs.bal_serializer_emit_balance + 52)),
    .SD .x5 .x19 (0 : BitVec 12),
    .LI .x20 (0 : Word),
    .BGEU .x20 .x19 (brOff (GuestAddrs.bal_serializer_emit_balance + 292) (GuestAddrs.bal_serializer_emit_balance + 68)),
    .LI .x5 (64 : Word),
    .MUL .x6 .x20 .x5,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_balance_changes (GuestAddrs.bal_serializer_emit_balance + 80)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_balance_changes (GuestAddrs.bal_serializer_emit_balance + 80)),
    .ADD .x28 .x7 .x6,
    .SD .x2 .x28 (48 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bald_bal_cmp_attempts (GuestAddrs.bal_serializer_emit_balance + 96)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_bal_cmp_attempts (GuestAddrs.bal_serializer_emit_balance + 96)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x28 .x2 (48 : BitVec 12),
    .MV .x10 .x9,
    .MV .x11 .x28,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches_be (GuestAddrs.bal_serializer_emit_balance + 128)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_emit_balance + 284) (GuestAddrs.bal_serializer_emit_balance + 132)),
    .LD .x28 .x2 (48 : BitVec 12),
    .LD .x11 .x28 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_balance + 144)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_balance + 144)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_emit_balance + 152)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_balance + 156)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_balance + 156)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_emit_balance + 164)),
    .SD .x2 .x10 (56 : BitVec 12),
    .LD .x28 .x2 (48 : BitVec 12),
    .ADDI .x10 .x28 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_balance_to_le (GuestAddrs.bal_serializer_emit_balance + 180)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_balance_le (GuestAddrs.bal_serializer_emit_balance + 184)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_balance_le (GuestAddrs.bal_serializer_emit_balance + 184)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_emit_balance + 192)),
    .LD .x29 .x2 (56 : BitVec 12),
    .ADD .x29 .x29 .x10,
    .SD .x2 .x29 (56 : BitVec 12),
    .MV .x10 .x8,
    .LD .x11 .x2 (56 : BitVec 12),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_balance + 220)),
    .AUIPC .x5 (laHi GuestAddrs.bv_bal_shadow_emit_balance_changes (GuestAddrs.bal_serializer_emit_balance + 224)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_bal_shadow_emit_balance_changes (GuestAddrs.bal_serializer_emit_balance + 224)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_balance + 248)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_balance + 248)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_balance + 260)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_balance_le (GuestAddrs.bal_serializer_emit_balance + 268)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_balance_le (GuestAddrs.bal_serializer_emit_balance + 268)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_balance + 280)),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_emit_balance + 68) (GuestAddrs.bal_serializer_emit_balance + 288)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerEmitBalance_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerEmitBalance_relocs : RelocTable :=
  [ (10, .la .x5 "bal_builder_balance_count"),
    (13, .la .x5 "bald_bal_builder_count"),
    (20, .la .x7 "bal_builder_balance_changes"),
    (24, .la .x5 "bald_bal_cmp_attempts"),
    (32, .jal .x1 "bal_serializer_addr_matches_be"),
    (36, .la .x10 "bal_serializer_u64_field"),
    (38, .jal .x1 "bal_serializer_u64_to_field"),
    (39, .la .x10 "bal_serializer_u64_field"),
    (41, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (45, .jal .x1 "bal_serializer_balance_to_le"),
    (46, .la .x10 "bal_serializer_balance_le"),
    (48, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (55, .jal .x1 "bal_rlp_emit_list_header"),
    (56, .la .x5 "bv_bal_shadow_emit_balance_changes"),
    (62, .la .x11 "bal_serializer_u64_field"),
    (65, .jal .x1 "bal_rlp_emit_scalar"),
    (67, .la .x11 "bal_serializer_balance_le"),
    (70, .jal .x1 "bal_rlp_emit_scalar") ]

def balSerializerEmitBalanceFunction : String :=
  "bal_serializer_emit_balance:\n" ++ emitProgramR balSerializerEmitBalance_prog balSerializerEmitBalance_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerEmitBalance_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerEmitBalanceFunction_eq_prog :
    balSerializerEmitBalanceFunction = "bal_serializer_emit_balance:\n" ++ emitProgramR balSerializerEmitBalance_prog balSerializerEmitBalance_relocs := rfl

#guard balSerializerEmitBalanceFunction.startsWith "bal_serializer_emit_balance:\n"
#guard balSerializerEmitBalance_prog.length = 81
/-- Emit `nonce_changes`: one `[block_access_index, new_nonce]` list per row. Both members
    are u64s widened through the scalar field, so BOTH need the widener -- unlike balance,
    whose post value is already a 32-byte field. a0 = ctx, a1 = address, a2 = scratch. -/
def balSerializerEmitNonce_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_nonce_count (GuestAddrs.bal_serializer_emit_nonce + 40)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_nonce_count (GuestAddrs.bal_serializer_emit_nonce + 40)),
    .LD .x19 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bald_non_builder_count (GuestAddrs.bal_serializer_emit_nonce + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_non_builder_count (GuestAddrs.bal_serializer_emit_nonce + 52)),
    .SD .x5 .x19 (0 : BitVec 12),
    .LI .x20 (0 : Word),
    .BGEU .x20 .x19 (brOff (GuestAddrs.bal_serializer_emit_nonce + 344) (GuestAddrs.bal_serializer_emit_nonce + 68)),
    .SLLI .x6 .x20 (5 : BitVec 6),
    .SLLI .x7 .x20 (3 : BitVec 6),
    .ADD .x6 .x6 .x7,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_nonce_changes (GuestAddrs.bal_serializer_emit_nonce + 84)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_nonce_changes (GuestAddrs.bal_serializer_emit_nonce + 84)),
    .ADD .x28 .x7 .x6,
    .SD .x2 .x28 (48 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bald_non_cmp_attempts (GuestAddrs.bal_serializer_emit_nonce + 100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_non_cmp_attempts (GuestAddrs.bal_serializer_emit_nonce + 100)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x28 .x2 (48 : BitVec 12),
    .MV .x10 .x9,
    .MV .x11 .x28,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches_be (GuestAddrs.bal_serializer_emit_nonce + 132)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_emit_nonce + 336) (GuestAddrs.bal_serializer_emit_nonce + 136)),
    .LD .x28 .x2 (48 : BitVec 12),
    .LD .x11 .x28 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 148)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 148)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_emit_nonce + 156)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 160)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 160)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_emit_nonce + 168)),
    .SD .x2 .x10 (56 : BitVec 12),
    .LD .x28 .x2 (48 : BitVec 12),
    .LD .x11 .x28 (32 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 184)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 184)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_emit_nonce + 192)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 196)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 196)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_emit_nonce + 204)),
    .LD .x29 .x2 (56 : BitVec 12),
    .ADD .x29 .x29 .x10,
    .SD .x2 .x29 (56 : BitVec 12),
    .MV .x10 .x8,
    .LD .x11 .x2 (56 : BitVec 12),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_nonce + 232)),
    .AUIPC .x5 (laHi GuestAddrs.bv_bal_shadow_emit_nonce_changes (GuestAddrs.bal_serializer_emit_nonce + 236)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_bal_shadow_emit_nonce_changes (GuestAddrs.bal_serializer_emit_nonce + 236)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x28 .x2 (48 : BitVec 12),
    .LD .x11 .x28 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 264)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 264)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_emit_nonce + 272)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 280)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 280)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_nonce + 292)),
    .LD .x28 .x2 (48 : BitVec 12),
    .LD .x11 .x28 (32 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 304)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 304)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_emit_nonce + 312)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 320)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 320)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_nonce + 332)),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_emit_nonce + 68) (GuestAddrs.bal_serializer_emit_nonce + 340)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerEmitNonce_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerEmitNonce_relocs : RelocTable :=
  [ (10, .la .x5 "bal_builder_nonce_count"),
    (13, .la .x5 "bald_non_builder_count"),
    (21, .la .x7 "bal_builder_nonce_changes"),
    (25, .la .x5 "bald_non_cmp_attempts"),
    (33, .jal .x1 "bal_serializer_addr_matches_be"),
    (37, .la .x10 "bal_serializer_u64_field"),
    (39, .jal .x1 "bal_serializer_u64_to_field"),
    (40, .la .x10 "bal_serializer_u64_field"),
    (42, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (46, .la .x10 "bal_serializer_u64_field"),
    (48, .jal .x1 "bal_serializer_u64_to_field"),
    (49, .la .x10 "bal_serializer_u64_field"),
    (51, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (58, .jal .x1 "bal_rlp_emit_list_header"),
    (59, .la .x5 "bv_bal_shadow_emit_nonce_changes"),
    (66, .la .x10 "bal_serializer_u64_field"),
    (68, .jal .x1 "bal_serializer_u64_to_field"),
    (70, .la .x11 "bal_serializer_u64_field"),
    (73, .jal .x1 "bal_rlp_emit_scalar"),
    (76, .la .x10 "bal_serializer_u64_field"),
    (78, .jal .x1 "bal_serializer_u64_to_field"),
    (80, .la .x11 "bal_serializer_u64_field"),
    (83, .jal .x1 "bal_rlp_emit_scalar") ]

def balSerializerEmitNonceFunction : String :=
  "bal_serializer_emit_nonce:\n" ++ emitProgramR balSerializerEmitNonce_prog balSerializerEmitNonce_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerEmitNonce_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerEmitNonceFunction_eq_prog :
    balSerializerEmitNonceFunction = "bal_serializer_emit_nonce:\n" ++ emitProgramR balSerializerEmitNonce_prog balSerializerEmitNonce_relocs := rfl

#guard balSerializerEmitNonceFunction.startsWith "bal_serializer_emit_nonce:\n"
#guard balSerializerEmitNonce_prog.length = 94
/-- Emit `code_changes`: one `[block_access_index, new_code]` list per row, where the code
    is a byte string rather than a scalar. a0 = ctx, a1 = address, a2 = scratch.

    The code length is measured through the throwaway-keccak route, exactly as
    `bal_serializer_measure_code` does, because a byte string's encoded size is not
    derivable from a fixed field width. -/
def balSerializerEmitCode_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_code_count (GuestAddrs.bal_serializer_emit_code + 40)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_code_count (GuestAddrs.bal_serializer_emit_code + 40)),
    .LD .x19 .x5 (0 : BitVec 12),
    .LI .x20 (0 : Word),
    .BGEU .x20 .x19 (brOff (GuestAddrs.bal_serializer_emit_code + 276) (GuestAddrs.bal_serializer_emit_code + 56)),
    .SLLI .x6 .x20 (6 : BitVec 6),
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_code_changes (GuestAddrs.bal_serializer_emit_code + 64)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_code_changes (GuestAddrs.bal_serializer_emit_code + 64)),
    .ADD .x28 .x7 .x6,
    .SD .x2 .x28 (48 : BitVec 12),
    .MV .x10 .x9,
    .MV .x11 .x28,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches_be (GuestAddrs.bal_serializer_emit_code + 88)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_emit_code + 268) (GuestAddrs.bal_serializer_emit_code + 92)),
    .LD .x28 .x2 (48 : BitVec 12),
    .LD .x11 .x28 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_code + 104)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_code + 104)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_emit_code + 112)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_code + 116)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_code + 116)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_emit_code + 124)),
    .SD .x2 .x10 (56 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_throwaway_ctx (GuestAddrs.bal_serializer_emit_code + 132)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_throwaway_ctx (GuestAddrs.bal_serializer_emit_code + 132)),
    .AUIPC .x11 (laHi GuestAddrs.bal_rlp_emit_bytes (GuestAddrs.bal_serializer_emit_code + 140)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_rlp_emit_bytes (GuestAddrs.bal_serializer_emit_code + 140)),
    .LD .x28 .x2 (48 : BitVec 12),
    .LD .x12 .x28 (32 : BitVec 12),
    .LD .x13 .x28 (40 : BitVec 12),
    .AUIPC .x14 (laHi GuestAddrs.bal_serializer_hdr_scratch (GuestAddrs.bal_serializer_emit_code + 160)),
    .ADDI .x14 .x14 (laLo GuestAddrs.bal_serializer_hdr_scratch (GuestAddrs.bal_serializer_emit_code + 160)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_measure_into_throwaway (GuestAddrs.bal_serializer_emit_code + 168)),
    .LD .x29 .x2 (56 : BitVec 12),
    .ADD .x29 .x29 .x10,
    .SD .x2 .x29 (56 : BitVec 12),
    .MV .x10 .x8,
    .LD .x11 .x2 (56 : BitVec 12),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_code + 196)),
    .AUIPC .x5 (laHi GuestAddrs.bv_bal_shadow_emit_code_changes (GuestAddrs.bal_serializer_emit_code + 200)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_bal_shadow_emit_code_changes (GuestAddrs.bal_serializer_emit_code + 200)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_code + 224)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_code + 224)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_code + 236)),
    .LD .x28 .x2 (48 : BitVec 12),
    .MV .x10 .x8,
    .LD .x11 .x28 (32 : BitVec 12),
    .LD .x12 .x28 (40 : BitVec 12),
    .AUIPC .x13 (laHi GuestAddrs.bal_serializer_hdr_scratch (GuestAddrs.bal_serializer_emit_code + 256)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bal_serializer_hdr_scratch (GuestAddrs.bal_serializer_emit_code + 256)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_bytes (GuestAddrs.bal_serializer_emit_code + 264)),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_emit_code + 56) (GuestAddrs.bal_serializer_emit_code + 272)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerEmitCode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerEmitCode_relocs : RelocTable :=
  [ (10, .la .x5 "bal_builder_code_count"),
    (16, .la .x7 "bal_builder_code_changes"),
    (22, .jal .x1 "bal_serializer_addr_matches_be"),
    (26, .la .x10 "bal_serializer_u64_field"),
    (28, .jal .x1 "bal_serializer_u64_to_field"),
    (29, .la .x10 "bal_serializer_u64_field"),
    (31, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (33, .la .x10 "bal_serializer_throwaway_ctx"),
    (35, .la .x11 "bal_rlp_emit_bytes"),
    (40, .la .x14 "bal_serializer_hdr_scratch"),
    (42, .jal .x1 "bal_rlp_measure_into_throwaway"),
    (49, .jal .x1 "bal_rlp_emit_list_header"),
    (50, .la .x5 "bv_bal_shadow_emit_code_changes"),
    (56, .la .x11 "bal_serializer_u64_field"),
    (59, .jal .x1 "bal_rlp_emit_scalar"),
    (64, .la .x13 "bal_serializer_hdr_scratch"),
    (66, .jal .x1 "bal_rlp_emit_bytes") ]

def balSerializerEmitCodeFunction : String :=
  "bal_serializer_emit_code:\n" ++ emitProgramR balSerializerEmitCode_prog balSerializerEmitCode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerEmitCode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerEmitCodeFunction_eq_prog :
    balSerializerEmitCodeFunction = "bal_serializer_emit_code:\n" ++ emitProgramR balSerializerEmitCode_prog balSerializerEmitCode_relocs := rfl

#guard balSerializerEmitCodeFunction.startsWith "bal_serializer_emit_code:\n"
#guard balSerializerEmitCode_prog.length = 77
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
def balSerializerEmitAccount_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 32)),
    .LD .x11 .x5 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_account + 52)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (20 : Word),
    .MV .x13 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_bytes (GuestAddrs.bal_serializer_emit_account + 72)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 76)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 76)),
    .LD .x11 .x5 (8 : BitVec 12),
    .MV .x10 .x8,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_account + 96)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_emit_storage (GuestAddrs.bal_serializer_emit_account + 112)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 116)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 116)),
    .LD .x11 .x5 (16 : BitVec 12),
    .MV .x10 .x8,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_account + 136)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_emit_reads (GuestAddrs.bal_serializer_emit_account + 152)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 156)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 156)),
    .LD .x11 .x5 (24 : BitVec 12),
    .MV .x10 .x8,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_account + 176)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_emit_balance (GuestAddrs.bal_serializer_emit_account + 192)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 196)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 196)),
    .LD .x11 .x5 (32 : BitVec 12),
    .MV .x10 .x8,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_account + 216)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_emit_nonce (GuestAddrs.bal_serializer_emit_account + 232)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 236)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 236)),
    .LD .x11 .x5 (40 : BitVec 12),
    .MV .x10 .x8,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_account + 256)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_emit_code (GuestAddrs.bal_serializer_emit_account + 272)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerEmitAccount_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerEmitAccount_relocs : RelocTable :=
  [ (8, .la .x5 "bal_serializer_len_table"),
    (13, .jal .x1 "bal_rlp_emit_list_header"),
    (18, .jal .x1 "bal_rlp_emit_bytes"),
    (19, .la .x5 "bal_serializer_len_table"),
    (24, .jal .x1 "bal_rlp_emit_list_header"),
    (28, .jal .x1 "bal_serializer_emit_storage"),
    (29, .la .x5 "bal_serializer_len_table"),
    (34, .jal .x1 "bal_rlp_emit_list_header"),
    (38, .jal .x1 "bal_serializer_emit_reads"),
    (39, .la .x5 "bal_serializer_len_table"),
    (44, .jal .x1 "bal_rlp_emit_list_header"),
    (48, .jal .x1 "bal_serializer_emit_balance"),
    (49, .la .x5 "bal_serializer_len_table"),
    (54, .jal .x1 "bal_rlp_emit_list_header"),
    (58, .jal .x1 "bal_serializer_emit_nonce"),
    (59, .la .x5 "bal_serializer_len_table"),
    (64, .jal .x1 "bal_rlp_emit_list_header"),
    (68, .jal .x1 "bal_serializer_emit_code") ]

def balSerializerEmitAccountFunction : String :=
  "bal_serializer_emit_account:\n" ++ emitProgramR balSerializerEmitAccount_prog balSerializerEmitAccount_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerEmitAccount_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerEmitAccountFunction_eq_prog :
    balSerializerEmitAccountFunction = "bal_serializer_emit_account:\n" ++ emitProgramR balSerializerEmitAccount_prog balSerializerEmitAccount_relocs := rfl

#guard balSerializerEmitAccountFunction.startsWith "bal_serializer_emit_account:\n"
#guard balSerializerEmitAccount_prog.length = 75
/-- Outer accumulation: the BAL is a list of `AccountChanges`, so its payload is the sum
    of each account's ENCODED size, not of their payloads. a0 (out) = that sum, also
    stored to `bal_serializer_outer_payload`.

    Summing payloads instead of encoded sizes is the same error the account measurer
    guards against one level down, and it is silent in exactly the same way: the result
    is a well-formed list whose header is short by one header per account. -/
def balSerializerMeasureOuter_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_account_count (GuestAddrs.bal_serializer_measure_outer + 24)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_account_count (GuestAddrs.bal_serializer_measure_outer + 24)),
    .LD .x9 .x5 (0 : BitVec 12),
    .LI .x18 (0 : Word),
    .LI .x19 (0 : Word),
    .BGEU .x19 .x9 (56 : BitVec 13),
    .LI .x5 (24 : Word),
    .MUL .x6 .x19 .x5,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_accounts (GuestAddrs.bal_serializer_measure_outer + 56)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_accounts (GuestAddrs.bal_serializer_measure_outer + 56)),
    .ADD .x8 .x7 .x6,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_measure_account (GuestAddrs.bal_serializer_measure_outer + 72)),
    .MV .x30 .x10,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_list_header_len (GuestAddrs.bal_serializer_measure_outer + 80)),
    .ADD .x18 .x18 .x30,
    .ADD .x18 .x18 .x10,
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (-52 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_outer_payload (GuestAddrs.bal_serializer_measure_outer + 100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_outer_payload (GuestAddrs.bal_serializer_measure_outer + 100)),
    .SD .x5 .x18 (0 : BitVec 12),
    .MV .x10 .x18,
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerMeasureOuter_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerMeasureOuter_relocs : RelocTable :=
  [ (6, .la .x5 "bal_builder_account_count"),
    (14, .la .x7 "bal_builder_accounts"),
    (18, .jal .x1 "bal_serializer_measure_account"),
    (20, .jal .x1 "bal_rlp_list_header_len"),
    (25, .la .x5 "bal_serializer_outer_payload") ]

def balSerializerMeasureOuterFunction : String :=
  "bal_serializer_measure_outer:\n" ++ emitProgramR balSerializerMeasureOuter_prog balSerializerMeasureOuter_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerMeasureOuter_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerMeasureOuterFunction_eq_prog :
    balSerializerMeasureOuterFunction = "bal_serializer_measure_outer:\n" ++ emitProgramR balSerializerMeasureOuter_prog balSerializerMeasureOuter_relocs := rfl

#guard balSerializerMeasureOuterFunction.startsWith "bal_serializer_measure_outer:\n"
#guard balSerializerMeasureOuter_prog.length = 36
/-- Emit the whole block access list. a0 = keccak ctx, a1 = scratch (>= 33 bytes).

    THE ACCOUNT LIST MUST ALREADY BE IN CANONICAL ORDER. EIP-7928 sorts accounts by
    address, and this walks `bal_builder_accounts` in storage order -- it does not sort.
    Ordering is `bal_canonical_sort`'s job and must happen before this runs; emitting an
    unsorted list produces a perfectly well-formed BAL with the wrong hash, which is the
    one failure the digest comparison cannot localise.

    Each account is re-measured immediately before it is emitted, because the length
    table holds ONE account at a time and the emitters read their headers from it. -/
def balSerializerEmitOuter_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_measure_outer (GuestAddrs.bal_serializer_emit_outer + 32)),
    .MV .x10 .x8,
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_outer_payload (GuestAddrs.bal_serializer_emit_outer + 40)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_outer_payload (GuestAddrs.bal_serializer_emit_outer + 40)),
    .LD .x11 .x5 (0 : BitVec 12),
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_outer + 56)),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_account_count (GuestAddrs.bal_serializer_emit_outer + 60)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_account_count (GuestAddrs.bal_serializer_emit_outer + 60)),
    .LD .x18 .x5 (0 : BitVec 12),
    .LI .x19 (0 : Word),
    .BGEU .x19 .x18 (brOff (GuestAddrs.bal_serializer_emit_outer + 140) (GuestAddrs.bal_serializer_emit_outer + 76)),
    .LI .x5 (24 : Word),
    .MUL .x6 .x19 .x5,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_accounts (GuestAddrs.bal_serializer_emit_outer + 88)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_accounts (GuestAddrs.bal_serializer_emit_outer + 88)),
    .ADD .x28 .x7 .x6,
    .SD .x2 .x28 (40 : BitVec 12),
    .MV .x10 .x28,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_measure_account (GuestAddrs.bal_serializer_emit_outer + 108)),
    .LD .x28 .x2 (40 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x28,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_emit_account (GuestAddrs.bal_serializer_emit_outer + 128)),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerEmitOuter_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerEmitOuter_relocs : RelocTable :=
  [ (8, .jal .x1 "bal_serializer_measure_outer"),
    (10, .la .x5 "bal_serializer_outer_payload"),
    (14, .jal .x1 "bal_rlp_emit_list_header"),
    (15, .la .x5 "bal_builder_account_count"),
    (22, .la .x7 "bal_builder_accounts"),
    (27, .jal .x1 "bal_serializer_measure_account"),
    (32, .jal .x1 "bal_serializer_emit_account") ]

def balSerializerEmitOuterFunction : String :=
  "bal_serializer_emit_outer:\n" ++ emitProgramR balSerializerEmitOuter_prog balSerializerEmitOuter_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerEmitOuter_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerEmitOuterFunction_eq_prog :
    balSerializerEmitOuterFunction = "bal_serializer_emit_outer:\n" ++ emitProgramR balSerializerEmitOuter_prog balSerializerEmitOuter_relocs := rfl

#guard balSerializerEmitOuterFunction.startsWith "bal_serializer_emit_outer:\n"
#guard balSerializerEmitOuter_prog.length = 42
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
  "  li a0, 0xa1908780\n" ++
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
def balSerializerVerify_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .MV .x8 .x10,
    .MV .x10 .x11,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_rebuilt_hash (GuestAddrs.bal_serializer_verify + 20)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_rebuilt_hash (GuestAddrs.bal_serializer_verify + 20)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_rebuild_hash (GuestAddrs.bal_serializer_verify + 28)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (2 : Word),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_verify + 136) (GuestAddrs.bal_serializer_verify + 40)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_supplied_hash (GuestAddrs.bal_serializer_verify + 48)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_supplied_hash (GuestAddrs.bal_serializer_verify + 48)),
    .JAL .x1 (jalOff GuestAddrs.block_access_list_hash (GuestAddrs.bal_serializer_verify + 56)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_rebuilt_hash (GuestAddrs.bal_serializer_verify + 60)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_rebuilt_hash (GuestAddrs.bal_serializer_verify + 60)),
    .AUIPC .x6 (laHi GuestAddrs.bal_serializer_supplied_hash (GuestAddrs.bal_serializer_verify + 68)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bal_serializer_supplied_hash (GuestAddrs.bal_serializer_verify + 68)),
    .LD .x7 .x5 (0 : BitVec 12),
    .LD .x28 .x6 (0 : BitVec 12),
    .BNE .x7 .x28 (48 : BitVec 13),
    .LD .x7 .x5 (8 : BitVec 12),
    .LD .x28 .x6 (8 : BitVec 12),
    .BNE .x7 .x28 (36 : BitVec 13),
    .LD .x7 .x5 (16 : BitVec 12),
    .LD .x28 .x6 (16 : BitVec 12),
    .BNE .x7 .x28 (24 : BitVec 13),
    .LD .x7 .x5 (24 : BitVec 12),
    .LD .x28 .x6 (24 : BitVec 12),
    .BNE .x7 .x28 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerVerify_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerVerify_relocs : RelocTable :=
  [ (5, .la .x11 "bal_serializer_rebuilt_hash"),
    (7, .jal .x1 "bal_serializer_rebuild_hash"),
    (12, .la .x11 "bal_serializer_supplied_hash"),
    (14, .jal .x1 "block_access_list_hash"),
    (15, .la .x5 "bal_serializer_rebuilt_hash"),
    (17, .la .x6 "bal_serializer_supplied_hash") ]

def balSerializerVerifyFunction : String :=
  "bal_serializer_verify:\n" ++ emitProgramR balSerializerVerify_prog balSerializerVerify_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerVerify_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerVerifyFunction_eq_prog :
    balSerializerVerifyFunction = "bal_serializer_verify:\n" ++ emitProgramR balSerializerVerify_prog balSerializerVerify_relocs := rfl

#guard balSerializerVerifyFunction.startsWith "bal_serializer_verify:\n"
#guard balSerializerVerify_prog.length = 38
/-! ## Guards on the RETURN CODES against their documented contracts

    A guard class this file did not have. Every other guard here pins emitted text or
    field selection; none pinned what a routine RETURNS against what its docstring says
    it returns. That gap is not hypothetical: a reviewer read `verify`'s 0/1/2 contract
    as applying to `rebuild_hash`'s bail path and reported a defect that was not there,
    because nothing in the code said which routine owned which contract. -/

-- `verify` NORMALISES. Without this the conversion looks redundant -- rebuild_hash
-- already returns nonzero -- and deleting it would silently widen verify's contract to
-- leak sort codes 1 and 3, where 1 collides with "hash does not match". The generated
-- Program length pin above plus the fixture byte-identity check protect this branch
-- after conversion (the old source-level semicolon guard no longer matches the
-- one-instruction-per-line rendering).

-- `rebuild_hash` does NOT normalise: it propagates the sort's own code, as its contract
-- says. Stated as the ABSENCE of the conversion, because absence is site-independent
-- while presence could be satisfied by any `li a0, 2` elsewhere in the def.
#guard (balSerializerRebuildHashFunction.splitOn "li a0, 2").length == 1

end EvmAsm.Codegen
