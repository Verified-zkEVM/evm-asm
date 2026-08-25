/-
  EvmAsm.Codegen.Programs.BlockAccessListBuilderStorage

  Storage-change producer extracted from BlockAccessListBuilder to keep the
  Codegen/Programs file-size gate meaningful. The public definitions retain
  their original names and emitted strings.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## `bal_emit_storage_changes`

    Emits this transaction's storage CHANGES into the builder, applying the spec's
    net-zero exclusion (`block_access_lists.py:667-676`).

    ## Where the baseline comes from — no capture and no carry

    The spec compares each write against
    `_get_pre_tx_storage(block_state.storage_writes, pre_state, ...)`: the block
    container if the slot is present, else pre-state. Both halves are readable AT THE
    MOMENT OF USE:

    * **Container hit** — the block-level scan already distinguishes found from
      not-found, so the discriminator comes from the scan and nothing needs storing.
      This must run BEFORE the tx→block merge, which is why it is called from the top
      of `write_sets_incorporate_tx`: the spec does the same, and says so
      (`state_tracker.py`: "Update BAL builder before merging writes into block
      state").
    * **Container miss** — `slot_at_header_state_root` against the PARENT header.

    The four arguments that read needs come from **globals `block_verdict` already
    publishes** at its own top, before this runs:

    | global | source | meaning |
    |---|---|---|
    | `sv_pre_rlp_ptr` | `params+8` | PARENT header rlp ptr |
    | `sv_pre_rlp_len` | `params+16` | PARENT header rlp len |
    | `bv_witness_state_ptr` | `params+80` | witness section ptr |
    | `bv_witness_state_len` | `params+88` | witness section len |

    That is the property that makes this design immune to what defeated four earlier
    attempts at the same value: nothing is carried, nothing's validity depends on which
    path arrived, and the reads are identical on every path by construction.

    **`sv_pre_rlp_*`, never `sv_this_rlp`** — the latter is this block's POST-state
    header and would silently return a post-state baseline.

    State and storage are passed as ONE section twice, matching the working SSTORE-side
    caller: this guest has a single witness section, not separate state and storage.

    ## ABSENT IS NOT ZERO

    A container miss does NOT mean the baseline is zero. `_get_pre_tx_storage` falls
    back to pre-state, which can be nonzero, and its "Returns `0` if not set" is about
    PRE-STATE being unset rather than about the container. Treating a miss as zero
    emits a spurious entry for every first-write-in-block to a nonzero slot — a
    well-formed BAL with the wrong entry count and therefore the wrong hash.

    ## Encodings

    Tx rows hold EVM stack words (little-endian limbs); `slot_at_header_state_root`
    wants a 20-byte BE address and a 32-byte BE slot, and the builder row wants BE20 +
    BE32 to match `balSortBuilderStorageSegments`. So the address and slot are reversed
    into scratch before either call — the same conversion the SSTORE path already does
    for its own lookup (`.Lsstore_prestate_addr_rev` / `.Lsstore_prestate_key_rev`).
    The VALUE needs no conversion: container, tx row and builder row all hold LE limbs,
    and the RLP scalar encoder consumes that form.

    a0 = block_access_index for this transaction.

    TWO CALLERS, and the docstring said "INERT: nothing calls this yet" long after
    the first arrived -- corrected here rather than deleted, because which callers
    exist is the fact a reader most needs:
    * `write_sets_incorporate_tx` (`StorageWriteMap.lean`), per transaction, with
      `current_block_access_index`;
    * the end-of-block system-call phase (`BlockVerdictStateRoot.lean`), once, with
      `svf_tx_count + 1` -- `fork.py:917-919`.  That caller EMITS AND DISCARDS
      rather than incorporating, so this routine's block-container baseline scan
      sees an empty container there: correct for those predeploy queue slots, which
      no transaction writes, and the reason the net-zero filter falls back to
      pre-state (GH #10866). -/
def balEmitStorageChanges_prog : Program :=
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
    .SD .x2 .x24 (72 : BitVec 12),
    .SD .x2 .x10 (80 : BitVec 12),
    .AUIPC .x8 (laHi GuestAddrs.tx_storage_writes_count (GuestAddrs.bal_emit_storage_changes + 48)),
    .ADDI .x8 .x8 (laLo GuestAddrs.tx_storage_writes_count (GuestAddrs.bal_emit_storage_changes + 48)),
    .LD .x9 .x8 (0 : BitVec 12),
    .LUI .x18 (20 : BitVec 20),
    .ADDIW .x18 .x18 (1451 : BitVec 12),
    .SLLI .x18 .x18 (15 : BitVec 6),
    .ADDI .x18 .x18 (-320 : BitVec 12),
    .LI .x19 (0 : Word),
    .BGEU .x19 .x9 (brOff (GuestAddrs.bal_emit_storage_changes + 696) (GuestAddrs.bal_emit_storage_changes + 80)),
    .SLLI .x20 .x19 (7 : BitVec 6),
    .ADD .x20 .x18 .x20,
    .AUIPC .x5 (laHi GuestAddrs.storage_writes_count (GuestAddrs.bal_emit_storage_changes + 92)),
    .ADDI .x5 .x5 (laLo GuestAddrs.storage_writes_count (GuestAddrs.bal_emit_storage_changes + 92)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x28 (162 : BitVec 20),
    .ADDIW .x28 .x28 (1333 : BitVec 12),
    .SLLI .x28 .x28 (12 : BitVec 6),
    .ADDI .x28 .x28 (-1600 : BitVec 12),
    .LI .x29 (0 : Word),
    .LI .x21 (0 : Word),
    .BGEU .x29 .x6 (brOff (GuestAddrs.bal_emit_storage_changes + 252) (GuestAddrs.bal_emit_storage_changes + 128)),
    .SLLI .x7 .x29 (7 : BitVec 6),
    .ADD .x30 .x28 .x7,
    .LD .x7 .x30 (0 : BitVec 12),
    .LD .x31 .x20 (0 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.bal_emit_storage_changes + 244) (GuestAddrs.bal_emit_storage_changes + 148)),
    .LD .x7 .x30 (8 : BitVec 12),
    .LD .x31 .x20 (8 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.bal_emit_storage_changes + 244) (GuestAddrs.bal_emit_storage_changes + 160)),
    .LD .x7 .x30 (16 : BitVec 12),
    .LD .x31 .x20 (16 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.bal_emit_storage_changes + 244) (GuestAddrs.bal_emit_storage_changes + 172)),
    .LD .x7 .x30 (24 : BitVec 12),
    .LD .x31 .x20 (24 : BitVec 12),
    .BNE .x7 .x31 (60 : BitVec 13),
    .LD .x7 .x30 (32 : BitVec 12),
    .LD .x31 .x20 (32 : BitVec 12),
    .BNE .x7 .x31 (48 : BitVec 13),
    .LD .x7 .x30 (40 : BitVec 12),
    .LD .x31 .x20 (40 : BitVec 12),
    .BNE .x7 .x31 (36 : BitVec 13),
    .LD .x7 .x30 (48 : BitVec 12),
    .LD .x31 .x20 (48 : BitVec 12),
    .BNE .x7 .x31 (24 : BitVec 13),
    .LD .x7 .x30 (56 : BitVec 12),
    .LD .x31 .x20 (56 : BitVec 12),
    .BNE .x7 .x31 (12 : BitVec 13),
    .ADDI .x21 .x30 (64 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_emit_storage_changes + 516) (GuestAddrs.bal_emit_storage_changes + 240)),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_emit_storage_changes + 128) (GuestAddrs.bal_emit_storage_changes + 248)),
    .AUIPC .x5 (laHi GuestAddrs.besc_addr_be (GuestAddrs.bal_emit_storage_changes + 252)),
    .ADDI .x5 .x5 (laLo GuestAddrs.besc_addr_be (GuestAddrs.bal_emit_storage_changes + 252)),
    .LI .x6 (20 : Word),
    .ADDI .x7 .x20 (19 : BitVec 12),
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .SB .x5 .x30 (0 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.besc_slot_be (GuestAddrs.bal_emit_storage_changes + 296)),
    .ADDI .x5 .x5 (laLo GuestAddrs.besc_slot_be (GuestAddrs.bal_emit_storage_changes + 296)),
    .LI .x6 (32 : Word),
    .ADDI .x7 .x20 (63 : BitVec 12),
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .SB .x5 .x30 (0 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.bal_emit_storage_changes + 340)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.bal_emit_storage_changes + 340)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_len (GuestAddrs.bal_emit_storage_changes + 352)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_len (GuestAddrs.bal_emit_storage_changes + 352)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.besc_addr_be (GuestAddrs.bal_emit_storage_changes + 364)),
    .ADDI .x12 .x12 (laLo GuestAddrs.besc_addr_be (GuestAddrs.bal_emit_storage_changes + 364)),
    .AUIPC .x13 (laHi GuestAddrs.besc_slot_be (GuestAddrs.bal_emit_storage_changes + 372)),
    .ADDI .x13 .x13 (laLo GuestAddrs.besc_slot_be (GuestAddrs.bal_emit_storage_changes + 372)),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_ptr (GuestAddrs.bal_emit_storage_changes + 380)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_ptr (GuestAddrs.bal_emit_storage_changes + 380)),
    .LD .x14 .x5 (0 : BitVec 12),
    .LD .x16 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_len (GuestAddrs.bal_emit_storage_changes + 396)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_len (GuestAddrs.bal_emit_storage_changes + 396)),
    .LD .x15 .x5 (0 : BitVec 12),
    .LD .x17 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.slot_at_header_state_root (GuestAddrs.bal_emit_storage_changes + 412)),
    .BNE .x10 .x0 (brOff (GuestAddrs.bal_emit_storage_changes + 484) (GuestAddrs.bal_emit_storage_changes + 416)),
    .AUIPC .x5 (laHi GuestAddrs.besc_base_le (GuestAddrs.bal_emit_storage_changes + 420)),
    .ADDI .x5 .x5 (laLo GuestAddrs.besc_base_le (GuestAddrs.bal_emit_storage_changes + 420)),
    .LI .x6 (32 : Word),
    .AUIPC .x7 (laHi GuestAddrs.sahsr_u256 (GuestAddrs.bal_emit_storage_changes + 432)),
    .ADDI .x7 .x7 (laLo GuestAddrs.sahsr_u256 (GuestAddrs.bal_emit_storage_changes + 432)),
    .ADDI .x7 .x7 (31 : BitVec 12),
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .SB .x5 .x30 (0 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x21 (laHi GuestAddrs.besc_base_le (GuestAddrs.bal_emit_storage_changes + 472)),
    .ADDI .x21 .x21 (laLo GuestAddrs.besc_base_le (GuestAddrs.bal_emit_storage_changes + 472)),
    .JAL .x0 (36 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.besc_base_le (GuestAddrs.bal_emit_storage_changes + 484)),
    .ADDI .x5 .x5 (laLo GuestAddrs.besc_base_le (GuestAddrs.bal_emit_storage_changes + 484)),
    .SD .x5 .x0 (0 : BitVec 12),
    .SD .x5 .x0 (8 : BitVec 12),
    .SD .x5 .x0 (16 : BitVec 12),
    .SD .x5 .x0 (24 : BitVec 12),
    .AUIPC .x21 (laHi GuestAddrs.besc_base_le (GuestAddrs.bal_emit_storage_changes + 508)),
    .ADDI .x21 .x21 (laLo GuestAddrs.besc_base_le (GuestAddrs.bal_emit_storage_changes + 508)),
    .ADDI .x22 .x20 (64 : BitVec 12),
    .LD .x7 .x21 (0 : BitVec 12),
    .LD .x31 .x22 (0 : BitVec 12),
    .BNE .x7 .x31 (44 : BitVec 13),
    .LD .x7 .x21 (8 : BitVec 12),
    .LD .x31 .x22 (8 : BitVec 12),
    .BNE .x7 .x31 (32 : BitVec 13),
    .LD .x7 .x21 (16 : BitVec 12),
    .LD .x31 .x22 (16 : BitVec 12),
    .BNE .x7 .x31 (20 : BitVec 13),
    .LD .x7 .x21 (24 : BitVec 12),
    .LD .x31 .x22 (24 : BitVec 12),
    .BNE .x7 .x31 (8 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.bal_emit_storage_changes + 688) (GuestAddrs.bal_emit_storage_changes + 568)),
    .AUIPC .x5 (laHi GuestAddrs.besc_addr_be (GuestAddrs.bal_emit_storage_changes + 572)),
    .ADDI .x5 .x5 (laLo GuestAddrs.besc_addr_be (GuestAddrs.bal_emit_storage_changes + 572)),
    .LI .x6 (20 : Word),
    .ADDI .x7 .x20 (19 : BitVec 12),
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .SB .x5 .x30 (0 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.besc_slot_be (GuestAddrs.bal_emit_storage_changes + 616)),
    .ADDI .x5 .x5 (laLo GuestAddrs.besc_slot_be (GuestAddrs.bal_emit_storage_changes + 616)),
    .LI .x6 (32 : Word),
    .ADDI .x7 .x20 (63 : BitVec 12),
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .SB .x5 .x30 (0 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.besc_addr_be (GuestAddrs.bal_emit_storage_changes + 660)),
    .ADDI .x10 .x10 (laLo GuestAddrs.besc_addr_be (GuestAddrs.bal_emit_storage_changes + 660)),
    .LD .x11 .x2 (80 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.besc_slot_be (GuestAddrs.bal_emit_storage_changes + 672)),
    .ADDI .x12 .x12 (laLo GuestAddrs.besc_slot_be (GuestAddrs.bal_emit_storage_changes + 672)),
    .ADDI .x13 .x20 (64 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_builder_record_storage_change (GuestAddrs.bal_emit_storage_changes + 684)),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_emit_storage_changes + 80) (GuestAddrs.bal_emit_storage_changes + 692)),
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
    .ADDI .x2 .x2 (96 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balEmitStorageChanges_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balEmitStorageChanges_relocs : RelocTable :=
  [ (12, .la .x8 "tx_storage_writes_count"),
    (23, .la .x5 "storage_writes_count"),
    (63, .la .x5 "besc_addr_be"),
    (74, .la .x5 "besc_slot_be"),
    (85, .la .x5 "sv_pre_rlp_ptr"),
    (88, .la .x5 "sv_pre_rlp_len"),
    (91, .la .x12 "besc_addr_be"),
    (93, .la .x13 "besc_slot_be"),
    (95, .la .x5 "bv_witness_state_ptr"),
    (99, .la .x5 "bv_witness_state_len"),
    (103, .jal .x1 "slot_at_header_state_root"),
    (105, .la .x5 "besc_base_le"),
    (108, .la .x7 "sahsr_u256"),
    (118, .la .x21 "besc_base_le"),
    (121, .la .x5 "besc_base_le"),
    (127, .la .x21 "besc_base_le"),
    (143, .la .x5 "besc_addr_be"),
    (154, .la .x5 "besc_slot_be"),
    (165, .la .x10 "besc_addr_be"),
    (168, .la .x12 "besc_slot_be"),
    (171, .jal .x1 "bal_builder_record_storage_change") ]

def balEmitStorageChangesFunction : String :=
  "bal_emit_storage_changes:\n" ++ emitProgramR balEmitStorageChanges_prog balEmitStorageChanges_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balEmitStorageChanges_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balEmitStorageChangesFunction_eq_prog :
    balEmitStorageChangesFunction = "bal_emit_storage_changes:\n" ++ emitProgramR balEmitStorageChanges_prog balEmitStorageChanges_relocs := rfl

#guard balEmitStorageChangesFunction.startsWith "bal_emit_storage_changes:\n"
#guard balEmitStorageChanges_prog.length = 186

end EvmAsm.Codegen
