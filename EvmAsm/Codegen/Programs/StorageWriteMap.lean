/-
  EvmAsm.Codegen.Programs.StorageWriteMap

  GH #10619 / bead `evm-asm-r59nm` slice S2 — the guest's `storage_writes`
  container, mirroring the spec's `Dict[Address, Dict[Bytes32, U256]]`.

  This is the WRITE-side counterpart of `StorageReadLog`. Together they give the
  guest the spec's two containers with the spec's two lifetimes, which is what
  `restore_tx_state` (`state_tracker.py:809-826`) discriminates on: it restores
  `account_writes`, `storage_writes`, `code_writes` and `transient_storage`, and
  **nothing else**. The read sets are passed by reference in `take_snapshot`
  (`:800-806`) and so survive rollback.

  ## One map, not one per source

  The spec has **no** system-specific write container. `BlockState` carries
  exactly one `storage_writes` (`:74`) and `TransactionState` exactly one
  (`:101`); the only occurrence of "system" in `state_tracker.py` is an EIP-2935
  comment. All three write sources merge into that one pair:
  `process_unchecked_system_transaction` (`fork.py:782`) builds an ordinary
  `TransactionState(parent=block_env.state)` and incorporates at `:858`, regular
  transactions incorporate at `:1204`, and withdrawals (`wd_state`) at `:1226`.

  The guest's split into `bv_system_storage_log` (38 refs, plus a six-symbol
  capture family) and `bv_user_storage_log` (16 refs) therefore mirrors nothing —
  **two arenas where the spec has one map is itself the shape defect**,
  independently of any lifetime question. These two areas replace both.

  Note that unifying the *container* must not unify the *timing*: the spec still
  applies system writes at block boundaries and user writes inside transactions.
  One map, three feeds, three schedules.

  ## Entry layout

  The spec's nested dict collapses to one flat key pair, because RISC-V has no
  dynamic allocation and therefore no inner dict to allocate per address:

      +0  addrHash (32 B)   the outer `Address` key
      +32 slotKey  (32 B)   the inner `Bytes32` key
      +64 value    (32 B)   the `U256`

  96 B used of a 128 B stride (`bvStorageLogRowBytes`), shared with the exec logs
  so that retiring them in S6 is a same-stride migration rather than a re-layout.
  Base and stride are both 8-aligned, so every `ld`/`sd` below is 8-aligned as
  the RV64 operational semantics require.

  ## It is a MAP, so the recorder upserts

  `set_storage` (`:489`) assigns `storage_writes[address][key] = value`, so the
  last write to a slot wins and a slot written a million times contributes one
  entry. The recorder therefore scans for an existing key and overwrites in
  place, appending only on a miss. This is the same scan-then-act discipline as
  `storage_read_record`, but the hit case *overwrites* where the read set's hit
  case *returns* — which is precisely the Dict-versus-Set difference.

  **Consequence for rollback, recorded here because it constrains S5:** because
  the container is an upsert map rather than an append-only log, a saved entry
  count is NOT a valid snapshot. A frame that overwrites a key which already
  existed before the snapshot cannot be undone by truncating back to a count.
  Truncation is only sound for append-only structures — which is exactly what
  the exec log is, and exactly why it truncates.

  ## Overflow is recorded, never silently dropped

  On a full arena the recorder sets `tx_storage_writes_overflow` instead of
  discarding the write, mirroring `storage_read_record`'s posture. A silently
  dropped write is not FA-safe: it leaves a BAL change with no exec-log support,
  which reads downstream as a genuine mismatch rather than as a capacity event.

  ## Not yet consulted

  Nothing reads these containers in this slice. The recorder and the promotion
  boundary are written and linked, but every existing comparator still reads the
  exec-log arenas, so this slice cannot change any verdict. Wiring the
  comparators over is S3 (forward) and S4 (reverse).

  `write_sets_restore_tx`, the third operation, is deliberately absent — see the
  rollback note above; its representation is a named forcing-constraint decision
  and lands with S5 rather than being guessed at here.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

/-- Entries per level. Matches the read arenas' 16384 so a write container
    cannot overflow before its read counterpart does. -/
def storageWritesCapacity : Nat := 16384

/-! ## `storage_write_record`

    Mirrors `set_storage` (`state_tracker.py:489`):
    `tx_state.storage_writes[address][key] = value`.

    Calling convention:
      a0 = addrHash ptr (32 B) — the outer `Address` key, keyed exactly as
           `storage_read_record` keys its reads, so the same slot in two
           contracts is two entries
      a1 = slotKey ptr  (32 B) — the inner `Bytes32` key
      a2 = value ptr    (32 B) — the `U256` to store
      ra = return
      no result register.

    Targets the TRANSACTION level, which is where the spec's assignment points.
    The block level is filled only by `write_sets_incorporate_tx`.

    Clobbers nothing the caller can see: `t0`-`t6` are saved and restored, so
    this is safe to call from a handler `preBody` holding live dispatcher state
    in caller-saved registers — the same property `storage_read_record` relies on
    to leave the verified `evm_sstore` Program untouched. -/
def storageWriteRecordFunction : String :=
  "storage_write_record:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)\n" ++
  "  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)\n" ++
  "  la t0, tx_storage_writes_count; ld t1, 0(t0)\n" ++          -- t1 = count
  "  li t3, 0xa21a0000\n" ++                                     -- t3 = TX_STORAGE_WRITES_AREA
  "  li t4, 0\n" ++                                              -- t4 = i
  ".Lswr_scan:\n" ++
  "  bgeu t4, t1, .Lswr_append\n" ++
  "  slli t5, t4, 7; add t5, t3, t5\n" ++                        -- t5 = &entry[i]
  -- addrHash compare (32 B); any mismatch -> next entry
  "  ld t2, 0(t5);  ld t6, 0(a0);  bne t2, t6, .Lswr_next\n" ++
  "  ld t2, 8(t5);  ld t6, 8(a0);  bne t2, t6, .Lswr_next\n" ++
  "  ld t2, 16(t5); ld t6, 16(a0); bne t2, t6, .Lswr_next\n" ++
  "  ld t2, 24(t5); ld t6, 24(a0); bne t2, t6, .Lswr_next\n" ++
  -- slotKey compare (32 B) at +32
  "  ld t2, 32(t5); ld t6, 0(a1);  bne t2, t6, .Lswr_next\n" ++
  "  ld t2, 40(t5); ld t6, 8(a1);  bne t2, t6, .Lswr_next\n" ++
  "  ld t2, 48(t5); ld t6, 16(a1); bne t2, t6, .Lswr_next\n" ++
  "  ld t2, 56(t5); ld t6, 24(a1); bne t2, t6, .Lswr_next\n" ++
  "  j .Lswr_store\n" ++                                         -- key hit: overwrite in place
  ".Lswr_next:\n" ++
  "  addi t4, t4, 1; j .Lswr_scan\n" ++
  ".Lswr_append:\n" ++
  "  li t2, " ++ toString storageWritesCapacity ++ "\n" ++
  "  bgeu t1, t2, .Lswr_overflow\n" ++
  "  slli t5, t1, 7; add t5, t3, t5\n" ++                        -- t5 = &entry[count]
  "  ld t2, 0(a0);  sd t2, 0(t5)\n" ++
  "  ld t2, 8(a0);  sd t2, 8(t5)\n" ++
  "  ld t2, 16(a0); sd t2, 16(t5)\n" ++
  "  ld t2, 24(a0); sd t2, 24(t5)\n" ++
  "  ld t2, 0(a1);  sd t2, 32(t5)\n" ++
  "  ld t2, 8(a1);  sd t2, 40(t5)\n" ++
  "  ld t2, 16(a1); sd t2, 48(t5)\n" ++
  "  ld t2, 24(a1); sd t2, 56(t5)\n" ++
  "  addi t1, t1, 1; sd t1, 0(t0)\n" ++
  ".Lswr_store:\n" ++
  -- value (32 B) at +64, written on both the hit and the append path
  "  ld t2, 0(a2);  sd t2, 64(t5)\n" ++
  "  ld t2, 8(a2);  sd t2, 72(t5)\n" ++
  "  ld t2, 16(a2); sd t2, 80(t5)\n" ++
  "  ld t2, 24(a2); sd t2, 88(t5)\n" ++
  "  j .Lswr_done\n" ++
  ".Lswr_overflow:\n" ++
  "  la t0, tx_storage_writes_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".Lswr_done:\n" ++
  "  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)\n" ++
  "  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

/-! ## `write_sets_incorporate_tx`

    Mirrors the write half of `incorporate_tx_into_block`
    (`state_tracker.py:832`): merge the transaction level into the block level
    (`:858-861`), then **CLEAR** the transaction level (`:879-881`).

    The clear is load-bearing, for the same reason it is on the read side: a
    merge without a clear double-counts across transactions, so transaction 2
    would re-promote transaction 1's writes. A single-transaction smoke test
    cannot observe this — there is no second transaction to double-count into —
    so it is verified on a multi-tx fixture, not inferred.

    The merge is an upsert per entry rather than an append, because the block
    level is a map too: a slot written in two transactions holds the later value,
    not two entries.

    No arguments; no result register. Overflow of the block level sets
    `storage_writes_overflow`. -/
def writeSetsIncorporateTxFunction : String :=
  "write_sets_incorporate_tx:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  la s0, tx_storage_writes_count; ld s1, 0(s0)\n" ++          -- s1 = tx count
  "  li s2, 0xa21a0000\n" ++                                     -- s2 = tx area
  "  li s3, 0\n" ++                                              -- s3 = i
  ".Lwsi_loop:\n" ++
  "  bgeu s3, s1, .Lwsi_clear\n" ++
  "  slli s4, s3, 7; add s4, s2, s4\n" ++                        -- s4 = &tx_entry[i]
  -- upsert this (addrHash, slotKey, value) into the block level
  "  mv a0, s4; addi a1, s4, 32; addi a2, s4, 64\n" ++
  "  jal ra, storage_writes_block_upsert\n" ++
  "  addi s3, s3, 1; j .Lwsi_loop\n" ++
  ".Lwsi_clear:\n" ++
  -- state_tracker.py:879-881 -- clear the tx level after merging up.
  "  sd zero, 0(s0)\n" ++
  "  la s5, tx_storage_writes_overflow; sd zero, 0(s5)\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret\n"

/-! ## `storage_writes_block_upsert`

    The block-level half of the merge, factored out so the promotion boundary
    reads as one loop over one operation. Same upsert discipline as
    `storage_write_record`, targeting `STORAGE_WRITES_AREA`.

      a0 = addrHash ptr (32 B), a1 = slotKey ptr (32 B), a2 = value ptr (32 B) -/
def storageWritesBlockUpsertFunction : String :=
  "storage_writes_block_upsert:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)\n" ++
  "  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)\n" ++
  "  la t0, storage_writes_count; ld t1, 0(t0)\n" ++
  "  li t3, 0xa1fa0000\n" ++                                     -- t3 = STORAGE_WRITES_AREA
  "  li t4, 0\n" ++
  ".Lswb_scan:\n" ++
  "  bgeu t4, t1, .Lswb_append\n" ++
  "  slli t5, t4, 7; add t5, t3, t5\n" ++
  "  ld t2, 0(t5);  ld t6, 0(a0);  bne t2, t6, .Lswb_next\n" ++
  "  ld t2, 8(t5);  ld t6, 8(a0);  bne t2, t6, .Lswb_next\n" ++
  "  ld t2, 16(t5); ld t6, 16(a0); bne t2, t6, .Lswb_next\n" ++
  "  ld t2, 24(t5); ld t6, 24(a0); bne t2, t6, .Lswb_next\n" ++
  "  ld t2, 32(t5); ld t6, 0(a1);  bne t2, t6, .Lswb_next\n" ++
  "  ld t2, 40(t5); ld t6, 8(a1);  bne t2, t6, .Lswb_next\n" ++
  "  ld t2, 48(t5); ld t6, 16(a1); bne t2, t6, .Lswb_next\n" ++
  "  ld t2, 56(t5); ld t6, 24(a1); bne t2, t6, .Lswb_next\n" ++
  "  j .Lswb_store\n" ++
  ".Lswb_next:\n" ++
  "  addi t4, t4, 1; j .Lswb_scan\n" ++
  ".Lswb_append:\n" ++
  "  li t2, " ++ toString storageWritesCapacity ++ "\n" ++
  "  bgeu t1, t2, .Lswb_overflow\n" ++
  "  slli t5, t1, 7; add t5, t3, t5\n" ++
  "  ld t2, 0(a0);  sd t2, 0(t5)\n" ++
  "  ld t2, 8(a0);  sd t2, 8(t5)\n" ++
  "  ld t2, 16(a0); sd t2, 16(t5)\n" ++
  "  ld t2, 24(a0); sd t2, 24(t5)\n" ++
  "  ld t2, 0(a1);  sd t2, 32(t5)\n" ++
  "  ld t2, 8(a1);  sd t2, 40(t5)\n" ++
  "  ld t2, 16(a1); sd t2, 48(t5)\n" ++
  "  ld t2, 24(a1); sd t2, 56(t5)\n" ++
  "  addi t1, t1, 1; sd t1, 0(t0)\n" ++
  ".Lswb_store:\n" ++
  "  ld t2, 0(a2);  sd t2, 64(t5)\n" ++
  "  ld t2, 8(a2);  sd t2, 72(t5)\n" ++
  "  ld t2, 16(a2); sd t2, 80(t5)\n" ++
  "  ld t2, 24(a2); sd t2, 88(t5)\n" ++
  "  j .Lswb_done\n" ++
  ".Lswb_overflow:\n" ++
  "  la t0, storage_writes_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".Lswb_done:\n" ++
  "  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)\n" ++
  "  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

/-- Data symbols for the two `storage_writes` levels.

    The entries live in `STORAGE_WRITES_AREA` / `TX_STORAGE_WRITES_AREA` (NOBITS
    RAM slabs, so zero-initialised by the loader); only the cursors and overflow
    flags need `.data` storage.

    The block-level pair is block-lifetime. The tx-level pair is cleared by
    `write_sets_incorporate_tx`, mirroring `state_tracker.py:879-881`. Neither is
    touched by rollback in this slice — `write_sets_restore_tx` lands with S5. -/
def storageWriteMapDataSection : String :=
  "storage_writes_count:\n  .zero 8\n" ++
  "storage_writes_overflow:\n  .zero 8\n" ++
  "tx_storage_writes_count:\n  .zero 8\n" ++
  "tx_storage_writes_overflow:\n  .zero 8\n"

end EvmAsm.Codegen
