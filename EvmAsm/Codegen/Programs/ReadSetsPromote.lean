/-
  EvmAsm.Codegen.Programs.ReadSetsPromote

  GH #10619 (review gate 3) — the **promotion boundary** between the spec's two read
  levels.

  ## What the spec does

  `TransactionState` gets **fresh** read sets per transaction
  (`field(default_factory=set)`; `fork.py:1043`
  `TransactionState(parent=block_env.state)`), and every recorder targets that level:
  `tx_state.storage_reads.add(...)` (`state_tracker.py:295`, `:578`),
  `account_reads` (`:139`, `:199`), `code_reads` (`:269`).

  `incorporate_tx_into_block` (`:832`; callers `fork.py:858`, `:1204`, `:1226`) then

  * merges upward — `block.storage_reads.update(tx_state.storage_reads)` and the same
    for `account_reads` / `code_reads` (`:858-861`);
  * and **clears** the tx sets (`:879-881`).

  `build_block_access_list(builder, block_env.state)` (`fork.py:928`) reads the
  **block** level, which is why consumers must too.

  ## Why the clear is load-bearing

  A merge without a clear double-counts across transactions: transaction 2 would
  re-promote transaction 1's reads. A **single-transaction smoke test cannot observe
  this** — there is no second transaction to double-count into — and multi-tx is the
  universal path after the selector flip. So the clear is verified on a multi-tx
  fixture, not inferred.

  ## Why a block-level-only mirror is not equivalent

  `fork.py:745-752` uses a **throwaway** `TransactionState` to pre-check that a system
  contract has code — in the spec's own words *"never propagated back to BlockState
  (no `incorporate_tx_into_block` call)"* — and its reads are deliberately
  **discarded**; the same lookups are re-done and properly tracked by
  `process_unchecked_system_transaction`, which it always calls.

  With only block-level containers, every recorded read is promoted by construction
  and there is **nowhere to express that path**. `read_sets_discard_tx` gives it a
  name, so "deliberately not promoted" is an operation a reader can find rather than
  an absence they must notice.

  ## Merge is a set union, not a concatenation

  The block level is a **set**, so the merge inserts each tx entry only if absent —
  the same dedup the recorders use. A slot read in two transactions appears once at
  block level, matching `set.update`.
-/

module

public import EvmAsm.Rv64.Program
public import EvmAsm.Codegen.Programs.BalCapacities
public import EvmAsm.Codegen.Emit
public import EvmAsm.Codegen.AsmReloc
public import EvmAsm.Codegen.GuestAddrs
meta import EvmAsm.Rv64.Program
meta import EvmAsm.Codegen.Programs.BalCapacities
meta import EvmAsm.Codegen.Emit
meta import EvmAsm.Codegen.AsmReloc
meta import EvmAsm.Codegen.GuestAddrs

@[expose] public section

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- One entry-stride merge loop, shared by all three kinds.

    `a0` = tx arena base, `a1` = tx count ptr, `a2` = block arena base,
    `a3` = block count ptr, `a4` = entry stride in bytes, `a5` = compare length in
    bytes (may be less than the stride, e.g. a 20-byte address in a 32-byte slot),
    `a6` = block capacity, `a7` = block overflow flag ptr.

    Byte-wise compare and copy (`lbu`/`sb`) so no arena needs an alignment argument;
    the entry widths differ per kind and the address slots are zero-padded. Overflow
    sets the flag rather than dropping silently, matching the recorders. -/
def readSetsMergeOne_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
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
    .MV .x9 .x12,
    .MV .x18 .x14,
    .MV .x19 .x15,
    .MV .x20 .x13,
    .MV .x21 .x16,
    .MV .x22 .x17,
    .LD .x23 .x11 (0 : BitVec 12),
    .LI .x5 (0 : Word),
    .BGEU .x5 .x23 (brOff (GuestAddrs.read_sets_merge_one + 248) (GuestAddrs.read_sets_merge_one + 76)),
    .MUL .x6 .x5 .x18,
    .ADD .x6 .x8 .x6,
    .LD .x7 .x20 (0 : BitVec 12),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x7 (56 : BitVec 13),
    .MUL .x29 .x28 .x18,
    .ADD .x29 .x9 .x29,
    .LI .x30 (0 : Word),
    .BGEU .x30 .x19 (brOff (GuestAddrs.read_sets_merge_one + 240) (GuestAddrs.read_sets_merge_one + 112)),
    .ADD .x31 .x6 .x30,
    .LBU .x31 .x31 (0 : BitVec 12),
    .ADD .x10 .x29 .x30,
    .LBU .x10 .x10 (0 : BitVec 12),
    .BNE .x31 .x10 (12 : BitVec 13),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-52 : BitVec 21),
    .BGEU .x7 .x21 (brOff (GuestAddrs.read_sets_merge_one + 232) (GuestAddrs.read_sets_merge_one + 152)),
    .MUL .x29 .x7 .x18,
    .ADD .x29 .x9 .x29,
    .LI .x30 (0 : Word),
    .BGEU .x30 .x18 (20 : BitVec 13),
    .ADD .x31 .x29 .x30,
    .SB .x31 .x0 (0 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .LI .x30 (0 : Word),
    .BGEU .x30 .x18 (28 : BitVec 13),
    .ADD .x31 .x6 .x30,
    .LBU .x31 .x31 (0 : BitVec 12),
    .ADD .x10 .x29 .x30,
    .SB .x10 .x31 (0 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .SD .x20 .x7 (0 : BitVec 12),
    .JAL .x0 (12 : BitVec 21),
    .LI .x30 (1 : Word),
    .SD .x22 .x30 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.read_sets_merge_one + 76) (GuestAddrs.read_sets_merge_one + 244)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def readSetsMergeOneFunction : String :=
  "read_sets_merge_one:\n" ++ emitProgram readSetsMergeOne_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `readSetsMergeOne_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem readSetsMergeOneFunction_eq_prog :
    readSetsMergeOneFunction = "read_sets_merge_one:\n" ++ emitProgram readSetsMergeOne_prog := rfl

#guard readSetsMergeOneFunction.startsWith "read_sets_merge_one:\n"
#guard readSetsMergeOne_prog.length = 73
/-- `read_sets_incorporate_tx` — the guest's `incorporate_tx_into_block` for the read
    side: merge all three tx sets upward, then CLEAR them (`:858-861`, `:879-881`).
    No arguments; call where a transaction is incorporated. -/
def readSetsIncorporateTx_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .LUI .x10 (162 : BitVec 20),
    .ADDIW .x10 .x10 (821 : BitVec 12),
    .SLLI .x10 .x10 (12 : BitVec 6),
    .ADDI .x10 .x10 (-1600 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.tx_storage_reads_count (GuestAddrs.read_sets_incorporate_tx + 24)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tx_storage_reads_count (GuestAddrs.read_sets_incorporate_tx + 24)),
    .LUI .x12 (20 : BitVec 20),
    .ADDIW .x12 .x12 (801 : BitVec 12),
    .SLLI .x12 .x12 (15 : BitVec 6),
    .ADDI .x12 .x12 (1920 : BitVec 12),
    .AUIPC .x13 (laHi GuestAddrs.storage_reads_count (GuestAddrs.read_sets_incorporate_tx + 48)),
    .ADDI .x13 .x13 (laLo GuestAddrs.storage_reads_count (GuestAddrs.read_sets_incorporate_tx + 48)),
    .LI .x14 (64 : Word),
    .LI .x15 (64 : Word),
    .LUI .x16 (16 : BitVec 20),
    .ADDIW .x16 .x16 (1130 : BitVec 12),
    .AUIPC .x17 (laHi GuestAddrs.storage_reads_overflow (GuestAddrs.read_sets_incorporate_tx + 72)),
    .ADDI .x17 .x17 (laLo GuestAddrs.storage_reads_overflow (GuestAddrs.read_sets_incorporate_tx + 72)),
    .JAL .x1 (jalOff GuestAddrs.read_sets_merge_one (GuestAddrs.read_sets_incorporate_tx + 80)),
    .LUI .x10 (162 : BitVec 20),
    .ADDIW .x10 .x10 (1077 : BitVec 12),
    .SLLI .x10 .x10 (12 : BitVec 6),
    .ADDI .x10 .x10 (-1600 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.tx_account_reads_count (GuestAddrs.read_sets_incorporate_tx + 100)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tx_account_reads_count (GuestAddrs.read_sets_incorporate_tx + 100)),
    .LUI .x12 (81 : BitVec 20),
    .ADDIW .x12 .x12 (-371 : BitVec 12),
    .SLLI .x12 .x12 (13 : BitVec 6),
    .ADDI .x12 .x12 (512 : BitVec 12),
    .AUIPC .x13 (laHi GuestAddrs.account_reads_count (GuestAddrs.read_sets_incorporate_tx + 124)),
    .ADDI .x13 .x13 (laLo GuestAddrs.account_reads_count (GuestAddrs.read_sets_incorporate_tx + 124)),
    .LI .x14 (32 : Word),
    .LI .x15 (20 : Word),
    .LUI .x16 (16 : BitVec 20),
    .ADDIW .x16 .x16 (1130 : BitVec 12),
    .AUIPC .x17 (laHi GuestAddrs.account_reads_overflow (GuestAddrs.read_sets_incorporate_tx + 148)),
    .ADDI .x17 .x17 (laLo GuestAddrs.account_reads_overflow (GuestAddrs.read_sets_incorporate_tx + 148)),
    .JAL .x1 (jalOff GuestAddrs.read_sets_merge_one (GuestAddrs.read_sets_incorporate_tx + 156)),
    .LUI .x10 (162 : BitVec 20),
    .ADDIW .x10 .x10 (1205 : BitVec 12),
    .SLLI .x10 .x10 (12 : BitVec 6),
    .ADDI .x10 .x10 (-1600 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.tx_code_reads_count (GuestAddrs.read_sets_incorporate_tx + 176)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tx_code_reads_count (GuestAddrs.read_sets_incorporate_tx + 176)),
    .LUI .x12 (162 : BitVec 20),
    .ADDIW .x12 .x12 (-221 : BitVec 12),
    .SLLI .x12 .x12 (12 : BitVec 6),
    .ADDI .x12 .x12 (-192 : BitVec 12),
    .AUIPC .x13 (laHi GuestAddrs.code_reads_count (GuestAddrs.read_sets_incorporate_tx + 200)),
    .ADDI .x13 .x13 (laLo GuestAddrs.code_reads_count (GuestAddrs.read_sets_incorporate_tx + 200)),
    .LI .x14 (64 : Word),
    .LI .x15 (64 : Word),
    .LUI .x16 (16 : BitVec 20),
    .ADDIW .x16 .x16 (1130 : BitVec 12),
    .AUIPC .x17 (laHi GuestAddrs.code_reads_overflow (GuestAddrs.read_sets_incorporate_tx + 224)),
    .ADDI .x17 .x17 (laLo GuestAddrs.code_reads_overflow (GuestAddrs.read_sets_incorporate_tx + 224)),
    .JAL .x1 (jalOff GuestAddrs.read_sets_merge_one (GuestAddrs.read_sets_incorporate_tx + 232)),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JAL .x0 (jalOff GuestAddrs.read_sets_discard_tx (GuestAddrs.read_sets_incorporate_tx + 244)) ]

/-- Reloc side-table for `readSetsIncorporateTx_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def readSetsIncorporateTx_relocs : RelocTable :=
  [ (6, .la .x11 "tx_storage_reads_count"),
    (12, .la .x13 "storage_reads_count"),
    (18, .la .x17 "storage_reads_overflow"),
    (20, .jal .x1 "read_sets_merge_one"),
    (25, .la .x11 "tx_account_reads_count"),
    (31, .la .x13 "account_reads_count"),
    (37, .la .x17 "account_reads_overflow"),
    (39, .jal .x1 "read_sets_merge_one"),
    (44, .la .x11 "tx_code_reads_count"),
    (50, .la .x13 "code_reads_count"),
    (56, .la .x17 "code_reads_overflow"),
    (58, .jal .x1 "read_sets_merge_one"),
    (61, .jal .x0 "read_sets_discard_tx") ]

def readSetsIncorporateTxFunction : String :=
  "read_sets_incorporate_tx:\n" ++ emitProgramR readSetsIncorporateTx_prog readSetsIncorporateTx_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `readSetsIncorporateTx_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem readSetsIncorporateTxFunction_eq_prog :
    readSetsIncorporateTxFunction = "read_sets_incorporate_tx:\n" ++ emitProgramR readSetsIncorporateTx_prog readSetsIncorporateTx_relocs := rfl

#guard readSetsIncorporateTxFunction.startsWith "read_sets_incorporate_tx:\n"
#guard readSetsIncorporateTx_prog.length = 62
/-- `read_sets_discard_tx` — zero the three tx cursors WITHOUT merging.

    Two callers by design: the tail of `read_sets_incorporate_tx` (the spec's clear at
    `:879-881`), and any path that mirrors `fork.py:745-752`'s throwaway
    `TransactionState`, whose reads are deliberately never promoted. Naming it makes
    that path expressible; a block-level-only design has no way to say it. -/
def readSetsDiscardTx_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.tx_storage_reads_count (GuestAddrs.read_sets_discard_tx + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_storage_reads_count (GuestAddrs.read_sets_discard_tx + 0)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_reads_count (GuestAddrs.read_sets_discard_tx + 12)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_reads_count (GuestAddrs.read_sets_discard_tx + 12)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.tx_code_reads_count (GuestAddrs.read_sets_discard_tx + 24)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_code_reads_count (GuestAddrs.read_sets_discard_tx + 24)),
    .SD .x5 .x0 (0 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `readSetsDiscardTx_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def readSetsDiscardTx_relocs : RelocTable :=
  [ (0, .la .x5 "tx_storage_reads_count"),
    (3, .la .x5 "tx_account_reads_count"),
    (6, .la .x5 "tx_code_reads_count") ]

def readSetsDiscardTxFunction : String :=
  "read_sets_discard_tx:\n" ++ emitProgramR readSetsDiscardTx_prog readSetsDiscardTx_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `readSetsDiscardTx_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem readSetsDiscardTxFunction_eq_prog :
    readSetsDiscardTxFunction = "read_sets_discard_tx:\n" ++ emitProgramR readSetsDiscardTx_prog readSetsDiscardTx_relocs := rfl

#guard readSetsDiscardTxFunction.startsWith "read_sets_discard_tx:\n"
#guard readSetsDiscardTx_prog.length = 10
/-- Block-level cursors and overflow flags. The tx-level ones live with their
    recorders. All zero-initialised, so they land in the ambient `.bss` (NOBITS) —
    adding them to `.data` would shift pinned data addresses in unrelated SAsm
    modules. -/
def readSetsBlockDataSection : String :=
  "storage_reads_count:\n  .zero 8\n" ++
  "storage_reads_overflow:\n  .zero 8\n" ++
  "account_reads_count:\n  .zero 8\n" ++
  "account_reads_overflow:\n  .zero 8\n" ++
  "code_reads_count:\n  .zero 8\n" ++
  "code_reads_overflow:\n  .zero 8\n"

end EvmAsm.Codegen
