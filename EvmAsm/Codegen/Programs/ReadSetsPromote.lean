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

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.BalCapacities
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

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
def readSetsMergeOneFunction : String :=
  "read_sets_merge_one:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0\n" ++                                    -- tx base
  "  mv s1, a2\n" ++                                    -- block base
  "  mv s2, a4\n" ++                                    -- stride
  "  mv s3, a5\n" ++                                    -- compare length
  "  mv s4, a3\n" ++                                    -- block count ptr
  "  mv s5, a6\n" ++                                    -- block capacity
  "  mv s6, a7\n" ++                                    -- block overflow ptr
  "  ld s7, 0(a1)\n" ++                                 -- tx count
  "  li t0, 0\n" ++                                     -- i = 0
  ".Lrsm_tx:\n" ++
  "  bgeu t0, s7, .Lrsm_done\n" ++
  "  mul t1, t0, s2; add t1, s0, t1\n" ++                -- &tx[i]
  -- scan the block arena for an equal entry (set semantics)
  "  ld t2, 0(s4)\n" ++                                  -- block count
  "  li t3, 0\n" ++                                      -- j = 0
  ".Lrsm_blk:\n" ++
  "  bgeu t3, t2, .Lrsm_append\n" ++
  "  mul t4, t3, s2; add t4, s1, t4\n" ++                -- &block[j]
  "  li t5, 0\n" ++
  ".Lrsm_cmp:\n" ++
  "  bgeu t5, s3, .Lrsm_next_tx\n" ++                    -- all compared equal -> present
  "  add t6, t1, t5; lbu t6, 0(t6)\n" ++
  "  add a0, t4, t5; lbu a0, 0(a0)\n" ++
  "  bne t6, a0, .Lrsm_next_blk\n" ++
  "  addi t5, t5, 1; j .Lrsm_cmp\n" ++
  ".Lrsm_next_blk:\n" ++
  "  addi t3, t3, 1; j .Lrsm_blk\n" ++
  ".Lrsm_append:\n" ++
  "  bgeu t2, s5, .Lrsm_overflow\n" ++
  "  mul t4, t2, s2; add t4, s1, t4\n" ++                -- &block[count]
  -- zero the destination slot first, so padding is written rather than inherited
  "  li t5, 0\n" ++
  ".Lrsm_zero:\n" ++
  "  bgeu t5, s2, .Lrsm_copy_init\n" ++
  "  add t6, t4, t5; sb zero, 0(t6)\n" ++
  "  addi t5, t5, 1; j .Lrsm_zero\n" ++
  ".Lrsm_copy_init:\n" ++
  "  li t5, 0\n" ++
  ".Lrsm_copy:\n" ++
  "  bgeu t5, s2, .Lrsm_bump\n" ++
  "  add t6, t1, t5; lbu t6, 0(t6)\n" ++
  "  add a0, t4, t5; sb t6, 0(a0)\n" ++
  "  addi t5, t5, 1; j .Lrsm_copy\n" ++
  ".Lrsm_bump:\n" ++
  "  addi t2, t2, 1; sd t2, 0(s4)\n" ++
  "  j .Lrsm_next_tx\n" ++
  ".Lrsm_overflow:\n" ++
  "  li t5, 1; sd t5, 0(s6)\n" ++
  ".Lrsm_next_tx:\n" ++
  "  addi t0, t0, 1; j .Lrsm_tx\n" ++
  ".Lrsm_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret\n"

/-- `read_sets_incorporate_tx` — the guest's `incorporate_tx_into_block` for the read
    side: merge all three tx sets upward, then CLEAR them (`:858-861`, `:879-881`).
    No arguments; call where a transaction is incorporated. -/
def readSetsIncorporateTxFunction : String :=
  "read_sets_incorporate_tx:\n" ++
  "  addi sp, sp, -16; sd ra, 0(sp)\n" ++
  -- storage_reads: 64 B stride, 64 B compared (addrHash ++ slotKey), cap 16384
  "  li a0, 0xa23349c0; la a1, tx_storage_reads_count; li a2, 0xa1908780\n" ++
  "  la a3, storage_reads_count; li a4, 64; li a5, 64; li a6, " ++
  toString balBuilderStorageReadsCapacity ++ "\n" ++
  "  la a7, storage_reads_overflow; jal ra, read_sets_merge_one\n" ++
  -- account_reads: 32 B stride, 20 B compared (the address; bytes 20..31 are padding)
  "  li a0, 0xa24349c0; la a1, tx_account_reads_count; li a2, 0xa1d1a200\n" ++
  "  la a3, account_reads_count; li a4, 32; li a5, 20; li a6, 66666\n" ++
  "  la a7, account_reads_overflow; jal ra, read_sets_merge_one\n" ++
  -- code_reads: 64 B stride; compare the 20-byte address AND the 32-byte hash, so
  -- compare the whole 64-byte slot (padding is zeroed on both sides)
  "  li a0, 0xa24b49c0; la a1, tx_code_reads_count; li a2, 0xa1f22f40\n" ++
  "  la a3, code_reads_count; li a4, 64; li a5, 64; li a6, 66666\n" ++
  "  la a7, code_reads_overflow; jal ra, read_sets_merge_one\n" ++
  "  ld ra, 0(sp); addi sp, sp, 16\n" ++
  "  j read_sets_discard_tx\n" ++                        -- the CLEAR at :879-881
  ""

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
