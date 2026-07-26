/-
  EvmAsm.Codegen.Programs.StorageReadLog

  GH #10619 — `storage_read_record`: the producer for the guest's `storage_reads`
  container, which mirrors the spec's `storage_reads` **set**.

  ## Why this is a separate container rather than a flag on the write log

  `state_tracker.py` (pin `e5a8caf1b`) keeps reads and writes in different
  containers with different lifetimes, deliberately. `BlockState` (`:67-77`) and
  `TransactionState` (`:96-104`) each carry `storage_reads : Set[Tuple[Address,
  Bytes32]]` alongside `storage_writes : Dict[...]`, and `restore_tx_state`
  (`:809-826`) restores **only** the write structures. The `TransactionState`
  docstring (`:90-93`) states the consequence in the spec's own words: the read
  sets are *"shared references that survive rollback (reads from failed calls
  still appear in the Block Access List)"*.

  The guest previously had no read container: one array of 128-byte rows where a
  read was the *derived* case `current == original`. That collapse is what this
  file removes. **Rollback does not touch this container** — there is no snapshot
  field and no restore, which is the point rather than an omission.

  ## It is a SET, and the dedup is load-bearing

  `add_storage_read` is a set insert, so a loop that SLOADs one slot a million
  times contributes one element. This routine therefore scans before appending.
  Without the dedup a hot read loop would exhaust the arena, and the arena's
  capacity guard would turn a valid block into a rejection — so the dedup is a
  correctness property of the container, not an optimisation.

  ## Overflow is recorded, never silently dropped

  On a full arena the routine sets `tx_storage_reads_overflow` instead of discarding
  the read. A dropped read is not FA-safe to ignore *quietly*: it leaves a BAL
  read with no exec-log support, which reads downstream as a genuine mismatch. The
  flag lets a consumer distinguish "this block has no such read" from "we stopped
  recording", the same way `exec_nonstorage_effect_overflow` does for the
  nonstorage log.

  ## Entry layout — mirrors the spec's tuple

      +0  addrHash (32 B)  the frame's env.ADDRESS, keyed exactly as the write log
      +32 slotKey  (32 B)  the EVM stack word

  64 B stride over `STORAGE_READS_AREA` (`0xa1da0000`, 16384 entries). Base and
  stride are both 8-aligned, so every `ld`/`sd` below is 8-aligned as the RV64
  operational semantics require.
  ## Two levels (GH #10619 review gate 3)

  This recorder targets the **TRANSACTION-level** arena, which is where the spec's
  `.add()` calls point (`tx_state.*_reads.add(...)`). The block-level arena is filled
  only by `read_sets_incorporate_tx`, mirroring `incorporate_tx_into_block`
  (`state_tracker.py:832`): merge up at `:858-861`, then CLEAR the tx set at
  `:879-881`. The clear is load-bearing — a merge without it double-counts across
  transactions in a multi-tx block, which a single-tx smoke test cannot see.

  `fork.py:745-752`'s throwaway `TransactionState`, whose reads are deliberately NOT
  promoted, is expressed by `read_sets_discard_tx` — a named operation rather than an
  absence.

-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

/-! ## `storage_read_record`

    Calling convention:
      a0 = addrHash ptr (32 B) — the frame's `env.ADDRESS`, same keying as the
           persistent write log, so the same slot in two contracts is two reads
      a1 = slotKey ptr  (32 B) — the EVM stack word
      ra = return
      no result register.

    Clobbers **nothing** the caller can see: `t0`-`t6` are saved and restored, so
    this is safe to call from a handler `preBody` that is holding live dispatcher
    state in caller-saved registers. That matters because the SLOAD handler's body
    is a *verified* Program (`EvmAsm.Evm64.Storage.evm_sload`, witnessed by
    `evm_sload_stack_spec_within` with a byte-identity `#guard`): recording the
    read from `preBody` leaves that proof untouched instead of invalidating it. -/
def storageReadRecordFunction : String :=
  "storage_read_record:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)\n" ++
  "  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)\n" ++
  "  la t0, tx_storage_reads_count; ld t1, 0(t0)\n" ++          -- t1 = count
  "  li t2, 16384\n" ++
  "  bgeu t1, t2, .Lsrr_overflow\n" ++
  "  li t3, 0xa1da0000\n" ++                                 -- t3 = STORAGE_READS_AREA
  "  li t4, 0\n" ++                                          -- t4 = i
  ".Lsrr_scan:\n" ++
  "  bgeu t4, t1, .Lsrr_append\n" ++
  "  slli t5, t4, 6; add t5, t3, t5\n" ++                     -- t5 = &entry[i]
  -- addrHash compare (32 B); any mismatch -> next entry
  "  ld t2, 0(t5);  ld t6, 0(a0);  bne t2, t6, .Lsrr_next\n" ++
  "  ld t2, 8(t5);  ld t6, 8(a0);  bne t2, t6, .Lsrr_next\n" ++
  "  ld t2, 16(t5); ld t6, 16(a0); bne t2, t6, .Lsrr_next\n" ++
  "  ld t2, 24(t5); ld t6, 24(a0); bne t2, t6, .Lsrr_next\n" ++
  -- slotKey compare (32 B) at +32
  "  ld t2, 32(t5); ld t6, 0(a1);  bne t2, t6, .Lsrr_next\n" ++
  "  ld t2, 40(t5); ld t6, 8(a1);  bne t2, t6, .Lsrr_next\n" ++
  "  ld t2, 48(t5); ld t6, 16(a1); bne t2, t6, .Lsrr_next\n" ++
  "  ld t2, 56(t5); ld t6, 24(a1); bne t2, t6, .Lsrr_next\n" ++
  "  j .Lsrr_done\n" ++                                       -- already in the set
  ".Lsrr_next:\n" ++
  "  addi t4, t4, 1; j .Lsrr_scan\n" ++
  ".Lsrr_append:\n" ++
  "  slli t5, t1, 6; add t5, t3, t5\n" ++                     -- t5 = &entry[count]
  "  ld t2, 0(a0);  sd t2, 0(t5)\n" ++
  "  ld t2, 8(a0);  sd t2, 8(t5)\n" ++
  "  ld t2, 16(a0); sd t2, 16(t5)\n" ++
  "  ld t2, 24(a0); sd t2, 24(t5)\n" ++
  "  ld t2, 0(a1);  sd t2, 32(t5)\n" ++
  "  ld t2, 8(a1);  sd t2, 40(t5)\n" ++
  "  ld t2, 16(a1); sd t2, 48(t5)\n" ++
  "  ld t2, 24(a1); sd t2, 56(t5)\n" ++
  "  addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  j .Lsrr_done\n" ++
  ".Lsrr_overflow:\n" ++
  "  la t0, tx_storage_reads_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".Lsrr_done:\n" ++
  "  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)\n" ++
  "  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

/-- Data symbols for the `storage_reads` container.

    The entries themselves live in `STORAGE_READS_AREA` (a NOBITS RAM slab, so
    zero-initialised by the loader); only the cursor and the overflow flag need
    `.data` storage. Both are block-lifetime: nothing resets them per transaction
    and nothing restores them on rollback, mirroring `restore_tx_state` leaving
    `storage_reads` alone. -/
def storageReadLogDataSection : String :=
  "tx_storage_reads_count:\n  .zero 8\n" ++
  "tx_storage_reads_overflow:\n  .zero 8\n"

end EvmAsm.Codegen
