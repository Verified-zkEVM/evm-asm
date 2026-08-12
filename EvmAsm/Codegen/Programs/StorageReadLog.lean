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

  64 B stride over `TX_STORAGE_READS_AREA` (`0xa23349c0`, 16384 entries). Base and
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
import EvmAsm.Codegen.ArenaCapacities
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## `exec_log_addr_to_bal_canonical`

    Convert the 32-byte address key carried by the execution storage log into
    the builder's canonical 20-byte big-endian address.

    Both live `storage_read_record` callers pass `x20`, the frame's
    `env.ADDRESS`.  The top-level runtime stager writes it as a little-endian
    stack word, and `call_frame_set_call_env` copies that same form for nested
    frames.  Thus this producer has one representation at every depth: reverse
    its low 20 bytes into the builder's BE20 key.  The representation belongs
    to the producing call site, not to call depth; a wrong form merely creates
    a silent zero-match in the BAL, which is why this convention has one named
    helper.

    Calling convention:
      a0 = 32-byte exec-log address key
      a1 = writable 20-byte canonical-BE output

    Leaf; clobbers `t0`-`t4`. -/
def execLogAddrToBalCanonicalFunction : String :=
  "exec_log_addr_to_bal_canonical:\n" ++
  "  li t0, 0\n" ++
  ".Lelatbc_loop:\n" ++
  "  li t1, 20; beq t0, t1, .Lelatbc_done\n" ++
  "  li t2, 19; sub t2, t2, t0; add t2, a0, t2; lbu t3, 0(t2)\n" ++
  "  add t4, a1, t0; sb t3, 0(t4)\n" ++
  "  addi t0, t0, 1; j .Lelatbc_loop\n" ++
  ".Lelatbc_done:\n" ++
  "  ret\n"

/-! ## `storage_read_record`

    Calling convention:
      a0 = addrHash ptr (32 B) — the frame's `env.ADDRESS`, same keying as the
           persistent write log, so the same slot in two contracts is two reads
      a1 = slotKey ptr  (32 B) — the EVM stack word
      ra = return
      no result register.

    After inserting (or finding) the read, it interns the same account in the
    block access-list builder.  This mirrors `add_storage_read` ensuring the
    account at read-record time, so a reverted transaction's read still has an
    account entry independently of the transaction-promotion boundary.

    Clobbers **nothing** the caller can see: input registers `a0`-`a2`,
    `t0`-`t6`, and `ra` are saved and restored, so
    this is safe to call from a handler `preBody` that is holding live dispatcher
    state in caller-saved registers. The SLOAD handler remains an emitted
    Program; recording the read from `preBody` keeps this logging helper
    independent of the retired persistent-log proof surface. -/
def storageReadRecord_prog : Program :=
  [ .ADDI .x2 .x2 (-112 : BitVec 12),
    .SD .x2 .x5 (0 : BitVec 12),
    .SD .x2 .x6 (8 : BitVec 12),
    .SD .x2 .x7 (16 : BitVec 12),
    .SD .x2 .x28 (24 : BitVec 12),
    .SD .x2 .x29 (32 : BitVec 12),
    .SD .x2 .x30 (40 : BitVec 12),
    .SD .x2 .x31 (48 : BitVec 12),
    .SD .x2 .x1 (56 : BitVec 12),
    .SD .x2 .x10 (88 : BitVec 12),
    .SD .x2 .x11 (96 : BitVec 12),
    .SD .x2 .x12 (104 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.system_call_mode (GuestAddrs.storage_read_record + 48)),
    .ADDI .x5 .x5 (laLo GuestAddrs.system_call_mode (GuestAddrs.storage_read_record + 48)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BEQ .x5 .x0 (12 : BitVec 13),
    .JAL .x1 (jalOff GuestAddrs.storage_read_record_block (GuestAddrs.storage_read_record + 64)),
    .JAL .x0 (jalOff (GuestAddrs.storage_read_record + 348) (GuestAddrs.storage_read_record + 68)),
    .AUIPC .x5 (laHi GuestAddrs.tx_storage_reads_count (GuestAddrs.storage_read_record + 72)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_storage_reads_count (GuestAddrs.storage_read_record + 72)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (4 : BitVec 20),
    .BGEU .x6 .x7 (brOff (GuestAddrs.storage_read_record + 332) (GuestAddrs.storage_read_record + 88)),
    .LUI .x28 (162 : BitVec 20),
    .ADDIW .x28 .x28 (821 : BitVec 12),
    .SLLI .x28 .x28 (12 : BitVec 6),
    .ADDI .x28 .x28 (-1600 : BitVec 12),
    .LI .x29 (0 : Word),
    .BGEU .x29 .x6 (brOff (GuestAddrs.storage_read_record + 232) (GuestAddrs.storage_read_record + 112)),
    .SLLI .x30 .x29 (6 : BitVec 6),
    .ADD .x30 .x28 .x30,
    .LD .x7 .x30 (0 : BitVec 12),
    .LD .x31 .x10 (0 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.storage_read_record + 224) (GuestAddrs.storage_read_record + 132)),
    .LD .x7 .x30 (8 : BitVec 12),
    .LD .x31 .x10 (8 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.storage_read_record + 224) (GuestAddrs.storage_read_record + 144)),
    .LD .x7 .x30 (16 : BitVec 12),
    .LD .x31 .x10 (16 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.storage_read_record + 224) (GuestAddrs.storage_read_record + 156)),
    .LD .x7 .x30 (24 : BitVec 12),
    .LD .x31 .x10 (24 : BitVec 12),
    .BNE .x7 .x31 (56 : BitVec 13),
    .LD .x7 .x30 (32 : BitVec 12),
    .LD .x31 .x11 (0 : BitVec 12),
    .BNE .x7 .x31 (44 : BitVec 13),
    .LD .x7 .x30 (40 : BitVec 12),
    .LD .x31 .x11 (8 : BitVec 12),
    .BNE .x7 .x31 (32 : BitVec 13),
    .LD .x7 .x30 (48 : BitVec 12),
    .LD .x31 .x11 (16 : BitVec 12),
    .BNE .x7 .x31 (20 : BitVec 13),
    .LD .x7 .x30 (56 : BitVec 12),
    .LD .x31 .x11 (24 : BitVec 12),
    .BNE .x7 .x31 (8 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.storage_read_record + 312) (GuestAddrs.storage_read_record + 220)),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.storage_read_record + 112) (GuestAddrs.storage_read_record + 228)),
    .SLLI .x30 .x6 (6 : BitVec 6),
    .ADD .x30 .x28 .x30,
    .LD .x7 .x10 (0 : BitVec 12),
    .SD .x30 .x7 (0 : BitVec 12),
    .LD .x7 .x10 (8 : BitVec 12),
    .SD .x30 .x7 (8 : BitVec 12),
    .LD .x7 .x10 (16 : BitVec 12),
    .SD .x30 .x7 (16 : BitVec 12),
    .LD .x7 .x10 (24 : BitVec 12),
    .SD .x30 .x7 (24 : BitVec 12),
    .LD .x7 .x11 (0 : BitVec 12),
    .SD .x30 .x7 (32 : BitVec 12),
    .LD .x7 .x11 (8 : BitVec 12),
    .SD .x30 .x7 (40 : BitVec 12),
    .LD .x7 .x11 (16 : BitVec 12),
    .SD .x30 .x7 (48 : BitVec 12),
    .LD .x7 .x11 (24 : BitVec 12),
    .SD .x30 .x7 (56 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .ADDI .x11 .x2 (64 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.exec_log_addr_to_bal_canonical (GuestAddrs.storage_read_record + 316)),
    .MV .x10 .x11,
    .JAL .x1 (jalOff GuestAddrs.bal_builder_ensure_account (GuestAddrs.storage_read_record + 324)),
    .JAL .x0 (20 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.tx_storage_reads_overflow (GuestAddrs.storage_read_record + 332)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_storage_reads_overflow (GuestAddrs.storage_read_record + 332)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x10 .x2 (88 : BitVec 12),
    .LD .x11 .x2 (96 : BitVec 12),
    .LD .x12 .x2 (104 : BitVec 12),
    .LD .x5 .x2 (0 : BitVec 12),
    .LD .x6 .x2 (8 : BitVec 12),
    .LD .x7 .x2 (16 : BitVec 12),
    .LD .x28 .x2 (24 : BitVec 12),
    .LD .x29 .x2 (32 : BitVec 12),
    .LD .x30 .x2 (40 : BitVec 12),
    .LD .x31 .x2 (48 : BitVec 12),
    .LD .x1 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (112 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `storageReadRecord_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def storageReadRecord_relocs : RelocTable :=
  [ (12, .la .x5 "system_call_mode"),
    (16, .jal .x1 "storage_read_record_block"),
    (18, .la .x5 "tx_storage_reads_count"),
    (79, .jal .x1 "exec_log_addr_to_bal_canonical"),
    (81, .jal .x1 "bal_builder_ensure_account"),
    (83, .la .x5 "tx_storage_reads_overflow") ]

def storageReadRecordFunction : String :=
  "storage_read_record:\n" ++ emitProgramR storageReadRecord_prog storageReadRecord_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `storageReadRecord_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem storageReadRecordFunction_eq_prog :
    storageReadRecordFunction = "storage_read_record:\n" ++ emitProgramR storageReadRecord_prog storageReadRecord_relocs := rfl

#guard storageReadRecordFunction.startsWith "storage_read_record:\n"
#guard storageReadRecord_prog.length = 100
/-! ## `storage_read_record_block`

    Insert an execution-keyed storage read directly into the block-level set.
    Modeled system calls have no user-transaction promotion boundary, so their
    `storage_reads` must not enter the transaction-local arena first.

    Calling convention and address representation match `storage_read_record`:
      a0 = 32-byte little-endian execution address key
      a1 = 32-byte little-endian execution slot key

    The builder performs read/write suppression later. This helper records only
    the block-lifetime read set. -/
def storageReadRecordBlockFunction : String :=
  "storage_read_record_block:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)\n" ++
  "  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp); sd ra, 56(sp)\n" ++
  "  sd a0, 88(sp); sd a1, 96(sp); sd a2, 104(sp)\n" ++
  "  la t0, storage_reads_count; ld t1, 0(t0)\n" ++
  "  li t2, 66666\n" ++
  "  bgeu t1, t2, .Lsrrb_overflow\n" ++
  "  li t3, 0xa1908780\n" ++
  "  li t4, 0\n" ++
  ".Lsrrb_scan:\n" ++
  "  bgeu t4, t1, .Lsrrb_append\n" ++
  "  slli t5, t4, 6; add t5, t3, t5\n" ++
  "  ld t2, 0(t5);  ld t6, 0(a0);  bne t2, t6, .Lsrrb_next\n" ++
  "  ld t2, 8(t5);  ld t6, 8(a0);  bne t2, t6, .Lsrrb_next\n" ++
  "  ld t2, 16(t5); ld t6, 16(a0); bne t2, t6, .Lsrrb_next\n" ++
  "  ld t2, 24(t5); ld t6, 24(a0); bne t2, t6, .Lsrrb_next\n" ++
  "  ld t2, 32(t5); ld t6, 0(a1);  bne t2, t6, .Lsrrb_next\n" ++
  "  ld t2, 40(t5); ld t6, 8(a1);  bne t2, t6, .Lsrrb_next\n" ++
  "  ld t2, 48(t5); ld t6, 16(a1); bne t2, t6, .Lsrrb_next\n" ++
  "  ld t2, 56(t5); ld t6, 24(a1); bne t2, t6, .Lsrrb_next\n" ++
  "  j .Lsrrb_intern_account\n" ++
  ".Lsrrb_next:\n" ++
  "  addi t4, t4, 1; j .Lsrrb_scan\n" ++
  ".Lsrrb_append:\n" ++
  "  slli t5, t1, 6; add t5, t3, t5\n" ++
  "  ld t2, 0(a0);  sd t2, 0(t5)\n" ++
  "  ld t2, 8(a0);  sd t2, 8(t5)\n" ++
  "  ld t2, 16(a0); sd t2, 16(t5)\n" ++
  "  ld t2, 24(a0); sd t2, 24(t5)\n" ++
  "  ld t2, 0(a1);  sd t2, 32(t5)\n" ++
  "  ld t2, 8(a1);  sd t2, 40(t5)\n" ++
  "  ld t2, 16(a1); sd t2, 48(t5)\n" ++
  "  ld t2, 24(a1); sd t2, 56(t5)\n" ++
  "  addi t1, t1, 1; sd t1, 0(t0)\n" ++
  ".Lsrrb_intern_account:\n" ++
  "  addi a1, sp, 64\n" ++
  "  jal ra, exec_log_addr_to_bal_canonical\n" ++
  "  mv a0, a1; jal ra, bal_builder_ensure_account\n" ++
  "  j .Lsrrb_done\n" ++
  ".Lsrrb_overflow:\n" ++
  "  la t0, storage_reads_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".Lsrrb_done:\n" ++
  "  ld a0, 88(sp); ld a1, 96(sp); ld a2, 104(sp)\n" ++
  "  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)\n" ++
  "  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp); ld ra, 56(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret\n"

/-! ## `account_state_promote_delete_reads`

    Successful transaction finalization runs `destroy_storage` for each address
    in the EIP-6780 / clear-account delete set (GH #10645).  Spec
    `clear_account_preserving_balance` and `destroy_account` both call
    `destroy_storage` (`state_tracker.py:532,556,560-580`); the guest stages those
    addresses in `account_state_delete` and converts here before
    `read_sets_incorporate_tx`, while the transaction read set is still live.

    ONE shared conversion: this loop only supplies addresses; `destroy_storage`
    owns the write-to-read walk and the write-map delete.

    MTx preparation-halt clears `account_state_delete_count` before the shared
    tail, so the loop is a no-op on reverted transactions.
-/
def accountStatePromoteDeleteReadsFunction : String :=
  "account_state_promote_delete_reads:\n" ++
  "  addi sp, sp, -96; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  la t0, account_state_delete_count; ld s0, 0(t0); li t0, " ++ toString accountStateDeleteCapacity ++ "; bgtu s0, t0, .Laspdr_over\n" ++
  "  li s1, 0\n" ++
  ".Laspdr_delete:\n" ++
  "  bgeu s1, s0, .Laspdr_done\n" ++
  "  slli t0, s1, 5; la t1, account_state_delete; add s2, t1, t0; ld t0, 24(s2); beqz t0, .Laspdr_next\n" ++
  -- GH #10645: shared destroy_storage (storage_writes -> storage_reads then del).
  -- Delete-set rows are 20-byte BE; storage map keys are LE env words.
  "  addi s3, sp, 48; sd zero, 0(s3); sd zero, 8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  mv a0, s2; mv a1, s3; jal ra, bal_addr_to_exec_log_key\n" ++
  "  mv a0, s3; jal ra, destroy_storage\n" ++
  ".Laspdr_next:\n" ++
  "  addi s1, s1, 1; j .Laspdr_delete\n" ++
  ".Laspdr_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); addi sp, sp, 96; ret\n" ++
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
