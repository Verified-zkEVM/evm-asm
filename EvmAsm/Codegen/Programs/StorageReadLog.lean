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

/-! ## `account_state_promote_delete_reads`

    Successful transaction finalization promotes storage rows touched by an
    EIP-6780 deletion into the transaction `storage_reads` set.  The delete
    address set is the execution-side source of truth; the regular storage log
    is walked by address and every matching slot is inserted through
    `storage_read_record`, whose set scan supplies the required deduplication.

    The normal nested-callee key is the byte-reversed stack-word form.  A
    constructor that self-destructs is the depth-0/top-frame exception and can
    leave the address in canonical big-endian form, so both forms are checked.
    This routine is called before `read_sets_incorporate_tx`, while the
    transaction read set is still live.  Its caller is the successful
    `account_state_commit_pending` boundary; reverted transactions never reach
    it and therefore cannot contribute reads.
-/
def accountStatePromoteDeleteReadsFunction : String :=
  "account_state_promote_delete_reads:\n" ++
  "  addi sp, sp, -224; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  la t0, account_state_delete_count; ld s0, 0(t0); li t0, 8192; bgtu s0, t0, .Laspdr_over\n" ++
  "  la t0, evm_env; ld s2, 448(t0); li t0, 16384; bgtu s2, t0, .Laspdr_over\n" ++
  "  li s1, 0\n" ++
  ".Laspdr_delete:\n" ++
  "  bgeu s1, s0, .Laspdr_done\n" ++
  "  slli t0, s1, 5; la t1, account_state_delete; add s4, t1, t0; ld t0, 24(s4); beqz t0, .Laspdr_next_delete\n" ++
  -- Reverse (nested-callee) key at sp+96; bal_addr_to_exec_log_key zeroes padding.
  "  mv a0, s4; addi a1, sp, 96; jal ra, bal_addr_to_exec_log_key\n" ++
  -- Canonical BE key at sp+128 for the top-frame constructor exception.
  "  addi s5, sp, 128; sd zero, 0(s5); sd zero, 8(s5); sd zero, 16(s5); sd zero, 24(s5); li t0, 0\n" ++
  ".Laspdr_be_copy:\n" ++
  "  li t1, 20; beq t0, t1, .Laspdr_scan_reverse; add t1, s4, t0; lbu t2, 0(t1); add t1, s5, t0; sb t2, 0(t1); addi t0, t0, 1; j .Laspdr_be_copy\n" ++
  -- Scan the persistent execution storage log for the reverse key.
  ".Laspdr_scan_reverse:\n" ++
  "  addi s6, sp, 96; li s3, 0\n" ++
  ".Laspdr_rev_loop:\n" ++
  "  bgeu s3, s2, .Laspdr_scan_be\n" ++
  "  slli t0, s3, 7; li t1, 0xa0630000; add s7, t1, t0\n" ++
  "  ld t1, 0(s7); ld t2, 0(s6); bne t1, t2, .Laspdr_rev_next\n" ++
  "  ld t1, 8(s7); ld t2, 8(s6); bne t1, t2, .Laspdr_rev_next\n" ++
  "  ld t1, 16(s7); ld t2, 16(s6); bne t1, t2, .Laspdr_rev_next\n" ++
  "  ld t1, 24(s7); ld t2, 24(s6); bne t1, t2, .Laspdr_rev_next\n" ++
  "  mv a0, s6; addi a1, s7, 32; jal ra, storage_read_record\n" ++
  ".Laspdr_rev_next:\n" ++
  "  addi s3, s3, 1; j .Laspdr_rev_loop\n" ++
  -- Scan the same log for the canonical BE key (top-frame constructor path).
  ".Laspdr_scan_be:\n" ++
  "  mv s6, s5; li s3, 0\n" ++
  ".Laspdr_be_loop:\n" ++
  "  bgeu s3, s2, .Laspdr_next_delete\n" ++
  "  slli t0, s3, 7; li t1, 0xa0630000; add s7, t1, t0\n" ++
  "  ld t1, 0(s7); ld t2, 0(s6); bne t1, t2, .Laspdr_be_next\n" ++
  "  ld t1, 8(s7); ld t2, 8(s6); bne t1, t2, .Laspdr_be_next\n" ++
  "  ld t1, 16(s7); ld t2, 16(s6); bne t1, t2, .Laspdr_be_next\n" ++
  "  ld t1, 24(s7); ld t2, 24(s6); bne t1, t2, .Laspdr_be_next\n" ++
  "  mv a0, s6; addi a1, s7, 32; jal ra, storage_read_record\n" ++
  ".Laspdr_be_next:\n" ++
  "  addi s3, s3, 1; j .Laspdr_be_loop\n" ++
  ".Laspdr_next_delete:\n" ++
  "  addi s1, s1, 1; j .Laspdr_delete\n" ++
  ".Laspdr_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 224; ret\n" ++
  ".Laspdr_over:\n" ++
  "  la t0, account_state_overflow; li t1, 1; sd t1, 0(t0); j .Laspdr_done\n"

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
