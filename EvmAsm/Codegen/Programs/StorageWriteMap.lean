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

      +0  rowAddress (32 B) the outer `Address` key
      +32 slotKey  (32 B)   the inner `Bytes32` key
      +64 value    (32 B)   the `U256`

  Formerly known as `addrHash`: `rowAddress` holds `env.ADDRESS`, not a hash.

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

  ## Rollback (r59nm S5a)

  `write_sets_snapshot_frame` / `write_sets_restore_frame` stand in for
  `take_snapshot` (`:800-806`) and `restore_tx_state` (`:809-826`) via an UNDO
  JOURNAL rather than a dict copy.

  **Forcing constraint:** no dynamic allocation, so the spec's per-frame copy of
  a keyed map would cost capacity × call depth (16384 × 1024), four orders of
  magnitude beyond what can be reserved. The journal is bounded by the number of
  writes instead, and needs no overflow path of its own because the SSTORE
  handler already exits on the 16385th exec-log append.

  This is the *reasoned-to-be-the-same* form rather than the *looking-the-same*
  form, which is why the constraint is named rather than assumed.
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
      a0 = rowAddress ptr (32 B) — the outer `Address` key, keyed exactly as
           `storage_read_record` keys its reads, so the same slot in two
           contracts is two entries
      a1 = slotKey ptr  (32 B) — the inner `Bytes32` key
      a2 = value ptr    (32 B) — the `U256` to store
      a6 = pre-tx baseline ptr (32 B), or 0 — the slot's value at the START of
           this transaction, captured into the row's spare bytes on APPEND only.
           A null pointer means "the baseline is zero", which is not a sentinel
           abuse: `_get_pre_tx_storage` documents "Returns `0` if not set", so
           zero IS the spec's answer for a slot with no prior value.
      ra = return
      no result register.

    ## The captured baseline, and why it is captured here

    `block_access_lists.py:667-676` excludes net-zero writes from the BAL by
    comparing each write against `_get_pre_tx_storage(block_state.storage_writes,
    pre_state, ...)` — the value at the start of this transaction. That comparison
    happens at the incorporate boundary, by which point the value is gone.

    Rather than re-derive it there (a per-slot witness read at a boundary that does
    no per-slot work today), it is captured at write time into the row's spare 32
    bytes at +96, because the EVM ALREADY HAS IT: `original_value` under EIP-2200
    and EIP-3529 is the transaction-start value, and the SSTORE path resolves it via
    `bv_mtx_committed_chunked_latest_value` against the committed log with a
    prestate-header fallback — which is `_get_pre_tx_storage` by another name. The
    committed log is snapshotted only at the per-transaction commit boundary, never
    inside a transaction, so the value is transaction-scoped rather than
    frame-scoped: a slot written in a reverted inner frame and again at top level
    sees the same baseline both times.

    **Captured on APPEND ONLY, never on the hit path.** A second write to the same
    slot within one transaction must not move the baseline; if it did, every net-zero
    test would compare a value against what the previous write left, and the filter
    would still run, still produce a well-formed BAL, and produce the wrong entry
    count. The append path is already where the undo journal makes the same
    insert-versus-update distinction, so the capture sits where that distinction is
    already load-bearing rather than introducing a second one.

    Note the block-level `storage_writes_block_upsert` has an identical field-copy
    shape and deliberately does NOT capture: it merges an already-filtered
    transaction result, so a baseline there would describe the wrong interval.

    INERT: nothing reads +96 yet. The consumer is the storage-change emission at the
    incorporate boundary, which lands separately.

    Targets the TRANSACTION level, which is where the spec's assignment points.
    The block level is filled only by `write_sets_incorporate_tx`.

    Clobbers nothing the caller can see: `t0`-`t6` are saved and restored, so
    this is safe to call from a handler `preBody` holding live dispatcher state
    in caller-saved registers — the same property `storage_read_record` relies on
    to leave the verified `evm_sstore` Program untouched. -/
def storageWriteRecordFunction : String :=
  "storage_write_record:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)\n" ++
  "  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)\n" ++
  -- r59nm S5a: no longer a leaf (it journals before mutating), so ra must
  -- be saved; a3-a5 carry the helper args and are LIVE in the SSTORE
  -- handler across this call, so they are saved too and the
  -- clobbers-nothing-visible contract in the docstring still holds.
  "  sd ra, 56(sp); sd a3, 64(sp); sd a4, 72(sp); sd a5, 80(sp)\n" ++
  -- a6 (the baseline ptr) must survive storage_writes_undo_push; slot 88 of the
  -- existing 96-byte frame was already spare, so no frame growth.
  "  sd a6, 88(sp)\n" ++
  "  la t0, tx_storage_writes_count; ld t1, 0(t0)\n" ++          -- t1 = count
  "  li t3, 0xa21a0000\n" ++                                     -- t3 = TX_STORAGE_WRITES_AREA
  "  li t4, 0\n" ++                                              -- t4 = i
  ".Lswr_scan:\n" ++
  "  bgeu t4, t1, .Lswr_append\n" ++
  "  slli t5, t4, 7; add t5, t3, t5\n" ++                        -- t5 = &entry[i]
  -- rowAddress compare (32 B); any mismatch -> next entry
  "  ld t2, 0(t5);  ld t6, 0(a0);  bne t2, t6, .Lswr_next\n" ++
  "  ld t2, 8(t5);  ld t6, 8(a0);  bne t2, t6, .Lswr_next\n" ++
  "  ld t2, 16(t5); ld t6, 16(a0); bne t2, t6, .Lswr_next\n" ++
  "  ld t2, 24(t5); ld t6, 24(a0); bne t2, t6, .Lswr_next\n" ++
  -- slotKey compare (32 B) at +32
  "  ld t2, 32(t5); ld t6, 0(a1);  bne t2, t6, .Lswr_next\n" ++
  "  ld t2, 40(t5); ld t6, 8(a1);  bne t2, t6, .Lswr_next\n" ++
  "  ld t2, 48(t5); ld t6, 16(a1); bne t2, t6, .Lswr_next\n" ++
  "  ld t2, 56(t5); ld t6, 24(a1); bne t2, t6, .Lswr_next\n" ++
  -- Key hit.  Journal the SUPERSEDED value before overwriting it (r59nm S5a):
  -- undo{entryIndex = t4, wasAbsent = 0, prevValue = entry[64..96]}.
  "  mv a3, t4; li a4, 0; addi a5, t5, 64\n" ++
  "  jal ra, storage_writes_undo_push\n" ++
  "  j .Lswr_store\n" ++                                         -- then overwrite in place
  ".Lswr_next:\n" ++
  "  addi t4, t4, 1; j .Lswr_scan\n" ++
  ".Lswr_append:\n" ++
  "  li t2, " ++ toString storageWritesCapacity ++ "\n" ++
  "  bgeu t1, t2, .Lswr_overflow\n" ++
  -- Journal the APPEND before making it: undo{entryIndex = t1, wasAbsent = 1}.
  -- wasAbsent is a field rather than a zero sentinel because zero is a
  -- legitimate stored value -- restoring an appended key by writing zero would
  -- invent a written-zero slot where the spec has no key at all.
  "  mv a3, t1; li a4, 1; li a5, 0\n" ++
  "  jal ra, storage_writes_undo_push\n" ++
  "  slli t5, t1, 7; add t5, t3, t5\n" ++                        -- t5 = &entry[count]
  "  ld t2, 0(a0);  sd t2, 0(t5)\n" ++
  "  ld t2, 8(a0);  sd t2, 8(t5)\n" ++
  "  ld t2, 16(a0); sd t2, 16(t5)\n" ++
  "  ld t2, 24(a0); sd t2, 24(t5)\n" ++
  "  ld t2, 0(a1);  sd t2, 32(t5)\n" ++
  "  ld t2, 8(a1);  sd t2, 40(t5)\n" ++
  "  ld t2, 16(a1); sd t2, 48(t5)\n" ++
  "  ld t2, 24(a1); sd t2, 56(t5)\n" ++
  -- Capture the transaction-start baseline at +96. APPEND PATH ONLY.
  "  beqz a6, .Lswr_base_zero\n" ++
  "  ld t2, 0(a6);  sd t2, 96(t5)\n" ++
  "  ld t2, 8(a6);  sd t2, 104(t5)\n" ++
  "  ld t2, 16(a6); sd t2, 112(t5)\n" ++
  "  ld t2, 24(a6); sd t2, 120(t5)\n" ++
  "  j .Lswr_base_done\n" ++
  ".Lswr_base_zero:\n" ++
  -- a6 = 0 means the baseline IS zero, per _get_pre_tx_storage's documented default.
  "  sd zero, 96(t5); sd zero, 104(t5); sd zero, 112(t5); sd zero, 120(t5)\n" ++
  ".Lswr_base_done:\n" ++
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
  "  ld ra, 56(sp); ld a3, 64(sp); ld a4, 72(sp); ld a5, 80(sp)\n" ++
  "  ld a6, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
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
  -- #10680: emit this tx's storage CHANGES into the BAL builder BEFORE the merge
  -- below overwrites the block container, which is the tx-start baseline the
  -- net-zero filter reads. The spec orders it the same way and says so:
  -- "Update BAL builder before merging writes into block state".
  --
  -- BAI from `current_block_access_index`, which block_verdict maintains as
  -- `bv_mtx_i + 1` (and 1 for the first case) -- NOT `bal_builder_current_bai`,
  -- which is defined with zero writers.
  "  la t0, current_block_access_index; ld a0, 0(t0)\n" ++
  "  jal ra, bal_emit_storage_changes\n" ++
  "  la s0, tx_storage_writes_count; ld s1, 0(s0)\n" ++          -- s1 = tx count
  "  li s2, 0xa21a0000\n" ++                                     -- s2 = tx area
  "  li s3, 0\n" ++                                              -- s3 = i
  ".Lwsi_loop:\n" ++
  "  bgeu s3, s1, .Lwsi_clear\n" ++
  "  slli s4, s3, 7; add s4, s2, s4\n" ++                        -- s4 = &tx_entry[i]
  -- upsert this (rowAddress, slotKey, value) into the block level
  "  mv a0, s4; addi a1, s4, 32; addi a2, s4, 64\n" ++
  "  jal ra, storage_writes_block_upsert\n" ++
  "  addi s3, s3, 1; j .Lwsi_loop\n" ++
  ".Lwsi_clear:\n" ++
  -- state_tracker.py:879-881 -- clear the tx level after merging up.
  "  sd zero, 0(s0)\n" ++
  "  la s5, tx_storage_writes_overflow; sd zero, 0(s5)\n" ++
  -- r59nm S5a: the undo records index into the tx map that was just
  -- cleared, so they must go with it -- a stale record would restore a
  -- value into a slot the next transaction has reused.
  "  la s5, storage_writes_undo_count; sd zero, 0(s5)\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret\n"

/-! ## Anti-drift guards for the captured baseline -/

-- The baseline is captured on the APPEND path and NOWHERE ELSE. If it ever moves to
-- the hit path, a slot written twice in one transaction loses its baseline and every
-- net-zero test compares a value against what the previous write left -- the filter
-- still runs, still produces a well-formed BAL, and produces the wrong entry count.
-- So: exactly one capture block, and it must sit before `.Lswr_store` (the shared
-- tail) rather than inside it.
#guard (storageWriteRecordFunction.splitOn "sd t2, 96(t5)").length == 2
#guard (storageWriteRecordFunction.splitOn ".Lswr_base_zero").length == 3
#guard (storageWriteRecordFunction.splitOn "beqz a6, .Lswr_base_zero").length == 2
#guard
  (storageWriteRecordFunction.splitOn ".Lswr_base_done:").head!.length
    < (storageWriteRecordFunction.splitOn ".Lswr_store:").head!.length

-- a6 must be saved AND restored, since it has to survive storage_writes_undo_push.
#guard (storageWriteRecordFunction.splitOn "sd a6, 88(sp)").length == 2
#guard (storageWriteRecordFunction.splitOn "ld a6, 88(sp)").length == 2

/-! ## `storage_writes_block_upsert`

    The block-level half of the merge, factored out so the promotion boundary
    reads as one loop over one operation. Same upsert discipline as
    `storage_write_record`, targeting `STORAGE_WRITES_AREA`.

      a0 = rowAddress ptr (32 B), a1 = slotKey ptr (32 B), a2 = value ptr (32 B). -/
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

-- THE BLOCK-LEVEL UPSERT MUST NOT CAPTURE. It has an identical field-copy shape, so
-- a copy-paste or a careless global edit lands there just as easily -- but it merges
-- an already-filtered transaction result, so a baseline there would describe the
-- wrong interval entirely.
#guard (storageWritesBlockUpsertFunction.splitOn "96(t5)").length == 1
#guard (storageWritesBlockUpsertFunction.splitOn "a6").length == 1

/-! ## `storage_writes_undo_push`

    Append one undo record. Called by `storage_write_record` BEFORE it mutates,
    which is what makes the journal a faithful stand-in for `take_snapshot`'s
    dict copy (`state_tracker.py:800-806`).

      a3 = entryIndex, a4 = wasAbsent (0/1), a5 = prevValue ptr (32 B; ignored
      when a4 = 1)

    Preserves `t0`-`t6` so the caller's scan state survives the call.

    No overflow path, and that is a derived fact rather than an omission: the
    SSTORE handler exits on the 16385th exec-log append, so a transaction cannot
    perform more writes than this arena holds. -/
def storageWritesUndoPushFunction : String :=
  "storage_writes_undo_push:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)\n" ++
  "  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)\n" ++
  "  la t0, storage_writes_undo_count; ld t1, 0(t0)\n" ++
  "  li t2, " ++ toString storageWritesCapacity ++ "\n" ++
  "  bgeu t1, t2, .Lswup_done\n" ++          -- unreachable: see the docstring
  "  li t3, 0xa23a0000\n" ++                 -- STORAGE_WRITES_UNDO_AREA
  "  slli t4, t1, 6; add t4, t3, t4\n" ++    -- 64 B stride
  "  sd a3, 0(t4)\n" ++
  "  sd a4, 8(t4)\n" ++
  "  bnez a4, .Lswup_bump\n" ++              -- appended key: prevValue unused
  "  ld t5, 0(a5);  sd t5, 32(t4)\n" ++
  "  ld t5, 8(a5);  sd t5, 40(t4)\n" ++
  "  ld t5, 16(a5); sd t5, 48(t4)\n" ++
  "  ld t5, 24(a5); sd t5, 56(t4)\n" ++
  ".Lswup_bump:\n" ++
  "  addi t1, t1, 1; sd t1, 0(t0)\n" ++
  ".Lswup_done:\n" ++
  "  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)\n" ++
  "  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

/-! ## `write_sets_restore_frame`

    The pair that stands in for `take_snapshot` (`state_tracker.py:800-806`) and
    `restore_tx_state` (`:809-826`).

    The frame's mark is the journal cursor at descend. It is captured INLINE in
    `call_frame_descend`, into a per-depth slot, rather than through a named
    helper. Taking a mark copies nothing, which is the whole point of the
    journal.

    `write_sets_restore_frame` takes that mark in `a0` and replays the journal
    backwards down to it: an overwrite has its previous value written back, an
    append is unwound by decrementing the map count. Then the cursor is reset to
    the mark.

    **Reverse order is load-bearing**, not stylistic. A slot written twice in one
    frame has two undo records, and only the *earlier* one holds the value the
    frame started with; replaying forwards would leave the intermediate value.
    And appends are only safely unwound from the end, which reverse order
    guarantees because frames nest LIFO.

    **A successful frame does NOT discard its segment.** Its entries stay above
    the parent's mark so that a later parent revert still undoes them — the same
    merge-on-success discipline `frame_return` already applies to the exec-log
    cursors. Success is simply the absence of a restore call. -/
def writeSetsRestoreFrameFunction : String :=
  "write_sets_restore_frame:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)\n" ++
  "  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)\n" ++
  "  la t0, storage_writes_undo_count; ld t1, 0(t0)\n" ++   -- t1 = cursor
  "  li t3, 0xa23a0000\n" ++                                -- undo area
  "  li t6, 0xa21a0000\n" ++                                -- tx map area
  ".Lswrf_loop:\n" ++
  "  bleu t1, a0, .Lswrf_done\n" ++                         -- cursor <= mark -> finished
  "  addi t1, t1, -1\n" ++
  "  slli t4, t1, 6; add t4, t3, t4\n" ++                   -- &undo[cursor]
  "  ld t2, 8(t4)\n" ++                                     -- wasAbsent
  "  bnez t2, .Lswrf_unappend\n" ++
  -- Overwrite: restore prevValue into entry[index].value (+64).
  "  ld t2, 0(t4); slli t5, t2, 7; add t5, t6, t5\n" ++
  "  ld t2, 32(t4); sd t2, 64(t5)\n" ++
  "  ld t2, 40(t4); sd t2, 72(t5)\n" ++
  "  ld t2, 48(t4); sd t2, 80(t5)\n" ++
  "  ld t2, 56(t4); sd t2, 88(t5)\n" ++
  "  j .Lswrf_loop\n" ++
  ".Lswrf_unappend:\n" ++
  -- Append: the key did not exist before this write, so remove it.  Reverse
  -- replay guarantees it is the LAST entry, so dropping the count is exact.
  "  la t2, tx_storage_writes_count; ld t5, 0(t2)\n" ++
  "  beqz t5, .Lswrf_loop\n" ++
  "  addi t5, t5, -1; sd t5, 0(t2)\n" ++
  "  j .Lswrf_loop\n" ++
  ".Lswrf_done:\n" ++
  "  la t0, storage_writes_undo_count; sd a0, 0(t0)\n" ++
  "  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)\n" ++
  "  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

/-! ## `write_sets_discard_tx`

    The transaction-level map is dropped WITHOUT being promoted.

    The spec gets this for free: every transaction runs against a **fresh**
    `TransactionState` (`fork.py:1043`), so a transaction whose writes are never
    incorporated simply has them discarded when the object goes away. The guest
    reuses one arena across transactions, so the drop has to be a named
    operation — the same reason `read_sets_discard_tx` exists on the read side
    for `fork.py:745-752`'s throwaway state.

    **Why this is required rather than tidy.** `write_sets_incorporate_tx` is
    called from `account_state_commit_pending`, which the multi-tx loop
    **skips** on transaction failure (`BlockVerdictMtxRuntime`: a zero receipt
    status with no applied auth phase jumps straight to
    `.Lbv_mtx_code_commit_done`). Without this call the failed transaction's
    writes would still be sitting in the tx-level map when the next transaction
    starts, and would be promoted to the block level by *its* incorporate — a
    failed transaction's writes surviving into the block, which is precisely the
    lifetime error this bead exists to remove.

    Note the asymmetry with the read side, which is the whole point of the two
    containers: the reads of a failed transaction are **kept** (they are already
    promoted, and the spec's read sets survive rollback), while its writes are
    **dropped**. Same event, opposite treatment.

    No arguments; no result register. -/
def writeSetsDiscardTxFunction : String :=
  "write_sets_discard_tx:\n" ++
  "  la t0, tx_storage_writes_count; sd zero, 0(t0)\n" ++
  "  la t0, tx_storage_writes_overflow; sd zero, 0(t0)\n" ++
  "  la t0, storage_writes_undo_count; sd zero, 0(t0)\n" ++
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
  "tx_storage_writes_overflow:\n  .zero 8\n" ++
  "storage_writes_undo_count:\n  .zero 8\n" ++
  -- Per-depth journal high-water mark: one 8-byte slot per call depth,
  -- written at descend and replayed to on child failure. 1025 slots cover
  -- depths 0..1024.
  "storage_writes_undo_checkpoint:\n  .zero " ++ toString (1025 * 8) ++ "\n"

end EvmAsm.Codegen
