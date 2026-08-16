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

  The guest keeps `TX_STORAGE_WRITES_AREA` for the current transaction and
  `STORAGE_WRITES_AREA` for the cumulative block map. The retired storage-log
  staging probes are not a third state map. This separates the two spec
  lifetimes without introducing a container the spec does not have.

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

    96 B used of a 128 B stride, matching the execution-log row layout.
  Base and stride are both 8-aligned, so every `ld`/`sd` below is 8-aligned as
  the RV64 operational semantics require.

  `storage_root` is deliberately not another row field or mask bit.  Consumers
  derive the account's new root from these storage slots through
  `mpt_bounded_storage_root` at the point where the storage trie is rebuilt;
  there is no stored map cell whose value could be read instead.

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

  On a full arena the recorder sets `tx_storage_writes_overflow` and fails closed
  instead of discarding the write, mirroring `storage_read_record`'s posture. A
  silently dropped write is not FA-safe: it leaves a BAL change with no exec-log
  support, which reads downstream as a genuine mismatch rather than as a capacity
  event. The undo helper also latches the block-level overflow flag so callers that
  do not consume its result still reject before the truncated map can be published.

  ## Readers

  `storagePrestateResolveAsm` and the block-verdict dispatch preload now scan
  this canonical map through `storage_writes_block_latest_value`. The BAL
  serializer consumes the same map through `bal_emit_storage_changes`; no
  separately populated committed-storage cache is retained.

  ## Rollback (r59nm S5a)

  `write_sets_snapshot_frame` / `write_sets_restore_frame` stand in for
  `take_snapshot` (`:800-806`) and `restore_tx_state` (`:809-826`) via an UNDO
  JOURNAL rather than a dict copy.

  **Forcing constraint:** no dynamic allocation, so the spec's per-frame copy of
  a keyed map would cost capacity × call depth (16384 × 1024), four orders of
  magnitude beyond what can be reserved. The journal is bounded by the number of
  rollback-relevant writes instead: value-unchanged hits do not need an undo
  record because restoring their prior value is an identity. The journal's
  live-row map cap is 16384, but changed writes can still be repeated while the
  live map count stays flat. The gas-derived 167652-entry cap therefore remains
  a fail-closed safety bound for records that are actually pushed.

  This is the *reasoned-to-be-the-same* form rather than the *looking-the-same*
  form, which is why the constraint is named rather than assumed.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! The live block map is bounded by the block-lifetime cold-slot gas budget;
    the transaction map has its own smaller capacity.  They must not share a
    name: the former is `200,000,000 / 3,000 = 66,666`, while the latter is
    `(16,777,216 - 12,000) / 3,000 = 5,588`. -/

/-- Undo journal capacity, derived from the regular-gas bound rather than from
    the map's slot-count capacity. `TX_MAX_GAS_LIMIT` is 16,777,216
    (`Stateless/SpecRef/Transactions.lean:517-518`) and `TX_BASE` is 12,000
    (`Stateless/SpecRef/Gas.lean:90`); subtracting the base and dividing by the
    100-gas warm-access repeat (`Stateless/SpecRef/Gas.lean:68`) gives
    `floor((16,777,216 - 12,000) / 100) = 167,652` records. A tighter
    one-slot construction gives 167,523 before loop overhead, so this bound is
    safe rather than tight. The 160-byte record stride is derived from the
    emitted index arithmetic below. -/
def storageWritesUndoCapacity : Nat := 167652

#guard blockStorageWritesCapacity == 66666
#guard txStorageWritesCapacity == 5588
#guard storageWritesUndoCapacity == 167652
#guard blockStorageWritesCapacity * 128 == 0x823500
#guard txStorageWritesCapacity * 128 == 0xaea00
#guard storageWritesUndoCapacity * 160 == 0x1994e80
#guard storageWritesUndoBase % 0x1000 == 0
#guard storageWritesStateGasDiagEnd <= storageWritesUndoBase
#guard storageWritesUndoBase == EvmAsm.Stateless.STORAGE_WRITES_UNDO_AREA.toNat
#guard storageWritesBlockBase + blockStorageWritesCapacity * 128 <= storageWritesTxBase
#guard storageWritesTxBase + txStorageWritesCapacity * 128 <= EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat

/-! The undo base is derived from the link-pinned `.bss`/diagnostic end, so it
    floats upward when those sections grow.  Keep the top-end slack visible at
    the guard: it is currently `0x73e180 = 7,594,368` bytes — the #11978 dead
    AccountState journal deletion shrank `.bss` by 4,923,016 B and the undo
    base floated down with it (from `0x28c180` after the GH #11186 high-pack
    relocate). The enlarged account map leaves exactly `0x180` bytes of checked
    headroom before the next page-aligned arena. If this check trips, the undo region has floated into the
    account-writes arena; move one of those arenas before raising a capacity. -/
def storageWritesUndoHeadroom : Nat :=
  EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat -
    (storageWritesUndoBase + storageWritesUndoCapacity * 160)

#guard storageWritesUndoHeadroom == 0x180
#guard storageWritesUndoBase + storageWritesUndoCapacity * 160 <
  EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat

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
    `storage_writes_block_latest_value` against the canonical block map with a
    prestate-header fallback — which is `_get_pre_tx_storage` by another name.
    The block map is updated only at the per-transaction commit boundary, never
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

    The block-level `storage_writes_block_upsert` copies +96 on APPEND only (from
    the tx entry's already-captured baseline) and leaves it untouched on HIT.
    That freezes the first-write / pre-block baseline for the whole block so
    `execution_map_state_changes` can compare final value vs parent for MPT
    apply — without it, a zero-clear of a nonzero parent looks like 0→0 and is
    silently omitted from the state root (code-1 / #11547; 7251 multi-block
    consolidation residual after #11600).

    Targets the TRANSACTION level for the initial capture. The block level is
    filled only by `write_sets_incorporate_tx` (plus system-storage seed paths
    that call `storage_writes_block_upsert` directly with an explicit baseline).

    Clobbers nothing the caller can see: `t0`-`t6` are saved and restored, so
    this is safe to call from a handler `preBody` holding live dispatcher state
    in caller-saved registers — the same property `storage_read_record` relies on
    to leave the verified `evm_sstore` Program untouched. -/
def storageWriteRecord_prog : Program :=
  [ .ADDI .x2 .x2 (-112 : BitVec 12),
    .SD .x2 .x5 (0 : BitVec 12),
    .SD .x2 .x6 (8 : BitVec 12),
    .SD .x2 .x7 (16 : BitVec 12),
    .SD .x2 .x28 (24 : BitVec 12),
    .SD .x2 .x29 (32 : BitVec 12),
    .SD .x2 .x30 (40 : BitVec 12),
    .SD .x2 .x31 (48 : BitVec 12),
    .SD .x2 .x1 (56 : BitVec 12),
    .SD .x2 .x13 (64 : BitVec 12),
    .SD .x2 .x14 (72 : BitVec 12),
    .SD .x2 .x15 (80 : BitVec 12),
    .SD .x2 .x16 (88 : BitVec 12),
    .SD .x2 .x10 (96 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.tx_storage_writes_count (GuestAddrs.storage_write_record + 56)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_storage_writes_count (GuestAddrs.storage_write_record + 56)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x28 (20 : BitVec 20),
    .ADDIW .x28 .x28 (1451 : BitVec 12),
    .SLLI .x28 .x28 (15 : BitVec 6),
    .ADDI .x28 .x28 (-320 : BitVec 12),
    .LI .x29 (0 : Word),
    .BGEU .x29 .x6 (brOff (GuestAddrs.storage_write_record + 284) (GuestAddrs.storage_write_record + 88)),
    .SLLI .x30 .x29 (7 : BitVec 6),
    .ADD .x30 .x28 .x30,
    .LD .x7 .x30 (0 : BitVec 12),
    .LD .x31 .x10 (0 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.storage_write_record + 276) (GuestAddrs.storage_write_record + 108)),
    .LD .x7 .x30 (8 : BitVec 12),
    .LD .x31 .x10 (8 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.storage_write_record + 276) (GuestAddrs.storage_write_record + 120)),
    .LD .x7 .x30 (16 : BitVec 12),
    .LD .x31 .x10 (16 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.storage_write_record + 276) (GuestAddrs.storage_write_record + 132)),
    .LD .x7 .x30 (24 : BitVec 12),
    .LD .x31 .x10 (24 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.storage_write_record + 276) (GuestAddrs.storage_write_record + 144)),
    .LD .x7 .x30 (32 : BitVec 12),
    .LD .x31 .x11 (0 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.storage_write_record + 276) (GuestAddrs.storage_write_record + 156)),
    .LD .x7 .x30 (40 : BitVec 12),
    .LD .x31 .x11 (8 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.storage_write_record + 276) (GuestAddrs.storage_write_record + 168)),
    .LD .x7 .x30 (48 : BitVec 12),
    .LD .x31 .x11 (16 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.storage_write_record + 276) (GuestAddrs.storage_write_record + 180)),
    .LD .x7 .x30 (56 : BitVec 12),
    .LD .x31 .x11 (24 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.storage_write_record + 276) (GuestAddrs.storage_write_record + 192)),
    .LD .x7 .x30 (64 : BitVec 12),
    .LD .x31 .x12 (0 : BitVec 12),
    .BNE .x7 .x31 (44 : BitVec 13),
    .LD .x7 .x30 (72 : BitVec 12),
    .LD .x31 .x12 (8 : BitVec 12),
    .BNE .x7 .x31 (32 : BitVec 13),
    .LD .x7 .x30 (80 : BitVec 12),
    .LD .x31 .x12 (16 : BitVec 12),
    .BNE .x7 .x31 (20 : BitVec 13),
    .LD .x7 .x30 (88 : BitVec 12),
    .LD .x31 .x12 (24 : BitVec 12),
    .BNE .x7 .x31 (8 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.storage_write_record + 456) (GuestAddrs.storage_write_record + 244)),
    .MV .x13 .x29,
    .LI .x14 (0 : Word),
    .ADDI .x15 .x30 (64 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.storage_writes_undo_push (GuestAddrs.storage_write_record + 260)),
    .BNE .x10 .x0 (brOff (GuestAddrs.storage_write_record + 492) (GuestAddrs.storage_write_record + 264)),
    .LD .x10 .x2 (96 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.storage_write_record + 456) (GuestAddrs.storage_write_record + 272)),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.storage_write_record + 88) (GuestAddrs.storage_write_record + 280)),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (1492 : BitVec 12),
    .BGEU .x6 .x7 (brOff (GuestAddrs.storage_write_record + 492) (GuestAddrs.storage_write_record + 292)),
    .MV .x13 .x6,
    .LI .x14 (1 : Word),
    .LI .x15 (0 : Word),
    .JAL .x1 (jalOff GuestAddrs.storage_writes_undo_push (GuestAddrs.storage_write_record + 308)),
    .BNE .x10 .x0 (brOff (GuestAddrs.storage_write_record + 492) (GuestAddrs.storage_write_record + 312)),
    .LD .x10 .x2 (96 : BitVec 12),
    .SLLI .x30 .x6 (7 : BitVec 6),
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
    .BEQ .x16 .x0 (40 : BitVec 13),
    .LD .x7 .x16 (0 : BitVec 12),
    .SD .x30 .x7 (96 : BitVec 12),
    .LD .x7 .x16 (8 : BitVec 12),
    .SD .x30 .x7 (104 : BitVec 12),
    .LD .x7 .x16 (16 : BitVec 12),
    .SD .x30 .x7 (112 : BitVec 12),
    .LD .x7 .x16 (24 : BitVec 12),
    .SD .x30 .x7 (120 : BitVec 12),
    .JAL .x0 (20 : BitVec 21),
    .SD .x30 .x0 (96 : BitVec 12),
    .SD .x30 .x0 (104 : BitVec 12),
    .SD .x30 .x0 (112 : BitVec 12),
    .SD .x30 .x0 (120 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x7 .x12 (0 : BitVec 12),
    .SD .x30 .x7 (64 : BitVec 12),
    .LD .x7 .x12 (8 : BitVec 12),
    .SD .x30 .x7 (72 : BitVec 12),
    .LD .x7 .x12 (16 : BitVec 12),
    .SD .x30 .x7 (80 : BitVec 12),
    .LD .x7 .x12 (24 : BitVec 12),
    .SD .x30 .x7 (88 : BitVec 12),
    .JAL .x0 (32 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.tx_storage_writes_overflow (GuestAddrs.storage_write_record + 492)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_storage_writes_overflow (GuestAddrs.storage_write_record + 492)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.storage_writes_overflow (GuestAddrs.storage_write_record + 508)),
    .ADDI .x5 .x5 (laLo GuestAddrs.storage_writes_overflow (GuestAddrs.storage_write_record + 508)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x5 .x2 (0 : BitVec 12),
    .LD .x6 .x2 (8 : BitVec 12),
    .LD .x7 .x2 (16 : BitVec 12),
    .LD .x28 .x2 (24 : BitVec 12),
    .LD .x29 .x2 (32 : BitVec 12),
    .LD .x30 .x2 (40 : BitVec 12),
    .LD .x31 .x2 (48 : BitVec 12),
    .LD .x1 .x2 (56 : BitVec 12),
    .LD .x13 .x2 (64 : BitVec 12),
    .LD .x14 .x2 (72 : BitVec 12),
    .LD .x15 .x2 (80 : BitVec 12),
    .LD .x16 .x2 (88 : BitVec 12),
    .LD .x10 .x2 (96 : BitVec 12),
    .ADDI .x2 .x2 (112 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `storageWriteRecord_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def storageWriteRecord_relocs : RelocTable :=
  [ (14, .la .x5 "tx_storage_writes_count"),
    (65, .jal .x1 "storage_writes_undo_push"),
    (77, .jal .x1 "storage_writes_undo_push"),
    (123, .la .x5 "tx_storage_writes_overflow"),
    (127, .la .x5 "storage_writes_overflow") ]

def storageWriteRecordFunction : String :=
  "storage_write_record:\n" ++ emitProgramR storageWriteRecord_prog storageWriteRecord_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `storageWriteRecord_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem storageWriteRecordFunction_eq_prog :
    storageWriteRecordFunction = "storage_write_record:\n" ++ emitProgramR storageWriteRecord_prog storageWriteRecord_relocs := rfl

#guard storageWriteRecordFunction.startsWith "storage_write_record:\n"
#guard storageWriteRecord_prog.length = 145

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
def writeSetsIncorporateTx_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.current_block_access_index (GuestAddrs.write_sets_incorporate_tx + 36)),
    .ADDI .x5 .x5 (laLo GuestAddrs.current_block_access_index (GuestAddrs.write_sets_incorporate_tx + 36)),
    .LD .x10 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_emit_storage_changes (GuestAddrs.write_sets_incorporate_tx + 48)),
    .AUIPC .x8 (laHi GuestAddrs.tx_storage_writes_count (GuestAddrs.write_sets_incorporate_tx + 52)),
    .ADDI .x8 .x8 (laLo GuestAddrs.tx_storage_writes_count (GuestAddrs.write_sets_incorporate_tx + 52)),
    .LD .x9 .x8 (0 : BitVec 12),
    .LUI .x18 (20 : BitVec 20),
    .ADDIW .x18 .x18 (1451 : BitVec 12),
    .SLLI .x18 .x18 (15 : BitVec 6),
    .ADDI .x18 .x18 (-320 : BitVec 12),
    .LI .x19 (0 : Word),
    .BGEU .x19 .x9 (40 : BitVec 13),
    .SLLI .x20 .x19 (7 : BitVec 6),
    .ADD .x20 .x18 .x20,
    .MV .x10 .x20,
    .ADDI .x11 .x20 (32 : BitVec 12),
    .ADDI .x12 .x20 (64 : BitVec 12),
    .ADDI .x13 .x20 (96 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.storage_writes_block_upsert (GuestAddrs.write_sets_incorporate_tx + 112)),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (-36 : BitVec 21),
    .SD .x8 .x0 (0 : BitVec 12),
    .AUIPC .x21 (laHi GuestAddrs.tx_storage_writes_overflow (GuestAddrs.write_sets_incorporate_tx + 128)),
    .ADDI .x21 .x21 (laLo GuestAddrs.tx_storage_writes_overflow (GuestAddrs.write_sets_incorporate_tx + 128)),
    .SD .x21 .x0 (0 : BitVec 12),
    .AUIPC .x21 (laHi GuestAddrs.storage_writes_undo_count (GuestAddrs.write_sets_incorporate_tx + 140)),
    .ADDI .x21 .x21 (laLo GuestAddrs.storage_writes_undo_count (GuestAddrs.write_sets_incorporate_tx + 140)),
    .SD .x21 .x0 (0 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `writeSetsIncorporateTx_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def writeSetsIncorporateTx_relocs : RelocTable :=
  [ (9, .la .x5 "current_block_access_index"),
    (12, .jal .x1 "bal_emit_storage_changes"),
    (13, .la .x8 "tx_storage_writes_count"),
    (28, .jal .x1 "storage_writes_block_upsert"),
    (32, .la .x21 "tx_storage_writes_overflow"),
    (35, .la .x21 "storage_writes_undo_count") ]

def writeSetsIncorporateTxFunction : String :=
  "write_sets_incorporate_tx:\n" ++ emitProgramR writeSetsIncorporateTx_prog writeSetsIncorporateTx_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `writeSetsIncorporateTx_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem writeSetsIncorporateTxFunction_eq_prog :
    writeSetsIncorporateTxFunction = "write_sets_incorporate_tx:\n" ++ emitProgramR writeSetsIncorporateTx_prog writeSetsIncorporateTx_relocs := rfl

#guard writeSetsIncorporateTxFunction.startsWith "write_sets_incorporate_tx:\n"
#guard writeSetsIncorporateTx_prog.length = 48
/-! ## Anti-drift guards for the captured baseline -/

-- ⚠️ RESTATED over `storageWriteRecord_prog`, not over the emitted string.
-- These guards used to `splitOn` ABI-named asm lines (`sd t2, 96(t5)`), local
-- labels (`.Lswr_base_zero`) and `j`/`ret` spellings. `emitProgramR` renders
-- NUMERIC registers, one instruction per line, and NO local labels, so every
-- one of those needles is now unmatchable: the presence guards would hard-fail
-- and an absence guard would pass while checking nothing. The Program is the
-- durable object, so each property below is re-expressed as a fact about the
-- instruction list. Register map: t0..t2 = x5..x7, t3..t6 = x28..x31,
-- sp = x2, a0..a6 = x10..x16.
--
-- The baseline is captured on the APPEND path and NOWHERE ELSE. If it ever moves to
-- the hit path, a slot written twice in one transaction loses its baseline and every
-- net-zero test compares a value against what the previous write left -- the filter
-- still runs, still produces a well-formed BAL, and produces the wrong entry count.
-- So: exactly one capture block, and it must sit before the shared store tail
-- (`.Lswr_store`, the `sd t2, 64(t5)` value write) rather than inside it.
#guard (storageWriteRecord_prog.filter (· == .SD .x30 .x7 (96 : BitVec 12))).length == 1
-- `.Lswr_base_zero`: the null-baseline arm writes four zero words at +96..+120.
#guard (storageWriteRecord_prog.filter (fun i => match i with | .SD .x30 .x0 _ => true | _ => false)).length == 4
-- `beqz a6, .Lswr_base_zero`, with its exact 40-byte skip over the copy arm.
#guard (storageWriteRecord_prog.filter (· == .BEQ .x16 .x0 (40 : BitVec 13))).length == 1
-- `bnez a0, .Lswr_overflow` after each of the two undo pushes.
#guard (storageWriteRecord_prog.filter (fun i => match i with | .BNE .x10 .x0 _ => true | _ => false)).length == 2
-- Ordering: the capture precedes the shared value store, i.e. it is not in the tail.
#guard storageWriteRecord_prog.findIdx (· == .SD .x30 .x7 (96 : BitVec 12)) < storageWriteRecord_prog.findIdx (· == .SD .x30 .x7 (64 : BitVec 12))

-- a6 must be saved AND restored, since it has to survive storage_writes_undo_push.
#guard (storageWriteRecord_prog.filter (· == .SD .x2 .x16 (88 : BitVec 12))).length == 1
#guard (storageWriteRecord_prog.filter (· == .LD .x16 .x2 (88 : BitVec 12))).length == 1

-- A value-unchanged hit must bypass the undo push but still join the shared
-- store tail; changed hits retain the journal path. `.Lswr_journal_hit` is the
-- `mv a3, t4` / `addi a5, t5, 64` setup -- the append arm uses `mv a3, t1`
-- instead, so `mv a3, t4` names the journal-hit arm uniquely.
#guard (storageWriteRecord_prog.filter (· == .MV .x13 .x29)).length == 1
#guard (storageWriteRecord_prog.filter (· == .ADDI .x15 .x30 (64 : BitVec 12))).length == 1
-- The two `j .Lswr_store` edges: unconditional jumps whose byte target is the
-- shared store tail at +456 (instruction index 114 of 145).
#guard (storageWriteRecord_prog.zipIdx.filter (fun p => match p.1 with | .JAL .x0 off => (4 * p.2 : Int) + off.toInt == 456 | _ => false)).length == 2

/-! ## `storage_writes_block_upsert`

    The block-level half of the merge, factored out so the promotion boundary
    reads as one loop over one operation. Same upsert discipline as
    `storage_write_record`, targeting `STORAGE_WRITES_AREA`.

      a0 = rowAddress ptr (32 B), a1 = slotKey ptr (32 B), a2 = value ptr (32 B),
      a3 = baseline ptr (32 B), or 0 — value at the start of the interval this
           row represents. On APPEND only: copied into +96 (null → zero). On HIT:
           +96 is left alone so the first-write / pre-block baseline survives
           later overwrites (same APPEND-only rule as `storage_write_record`).

    `execution_map_state_changes` reads block +64 vs +96 to decide MPT apply.
    Dropping +96 on incorporate made zero-clears of nonzero parents look
    unchanged (7251 multi-block residual). -/
def storageWritesBlockUpsert_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x5 (0 : BitVec 12),
    .SD .x2 .x6 (8 : BitVec 12),
    .SD .x2 .x7 (16 : BitVec 12),
    .SD .x2 .x28 (24 : BitVec 12),
    .SD .x2 .x29 (32 : BitVec 12),
    .SD .x2 .x30 (40 : BitVec 12),
    .SD .x2 .x31 (48 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.storage_writes_count (GuestAddrs.storage_writes_block_upsert + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.storage_writes_count (GuestAddrs.storage_writes_block_upsert + 32)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x28 (162 : BitVec 20),
    .ADDIW .x28 .x28 (1333 : BitVec 12),
    .SLLI .x28 .x28 (12 : BitVec 6),
    .ADDI .x28 .x28 (-1600 : BitVec 12),
    .LI .x29 (0 : Word),
    .BGEU .x29 .x6 (brOff (GuestAddrs.storage_writes_block_upsert + 184) (GuestAddrs.storage_writes_block_upsert + 64)),
    .SLLI .x30 .x29 (7 : BitVec 6),
    .ADD .x30 .x28 .x30,
    .LD .x7 .x30 (0 : BitVec 12),
    .LD .x31 .x10 (0 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.storage_writes_block_upsert + 176) (GuestAddrs.storage_writes_block_upsert + 84)),
    .LD .x7 .x30 (8 : BitVec 12),
    .LD .x31 .x10 (8 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.storage_writes_block_upsert + 176) (GuestAddrs.storage_writes_block_upsert + 96)),
    .LD .x7 .x30 (16 : BitVec 12),
    .LD .x31 .x10 (16 : BitVec 12),
    .BNE .x7 .x31 (brOff (GuestAddrs.storage_writes_block_upsert + 176) (GuestAddrs.storage_writes_block_upsert + 108)),
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
    .JAL .x0 (jalOff (GuestAddrs.storage_writes_block_upsert + 332) (GuestAddrs.storage_writes_block_upsert + 172)),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.storage_writes_block_upsert + 64) (GuestAddrs.storage_writes_block_upsert + 180)),
    .LUI .x7 (16 : BitVec 20),
    .ADDIW .x7 .x7 (1130 : BitVec 12),
    .BGEU .x6 .x7 (brOff (GuestAddrs.storage_writes_block_upsert + 368) (GuestAddrs.storage_writes_block_upsert + 192)),
    .SLLI .x30 .x6 (7 : BitVec 6),
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
    .BEQ .x13 .x0 (40 : BitVec 13),
    .LD .x7 .x13 (0 : BitVec 12),
    .SD .x30 .x7 (96 : BitVec 12),
    .LD .x7 .x13 (8 : BitVec 12),
    .SD .x30 .x7 (104 : BitVec 12),
    .LD .x7 .x13 (16 : BitVec 12),
    .SD .x30 .x7 (112 : BitVec 12),
    .LD .x7 .x13 (24 : BitVec 12),
    .SD .x30 .x7 (120 : BitVec 12),
    .JAL .x0 (20 : BitVec 21),
    .SD .x30 .x0 (96 : BitVec 12),
    .SD .x30 .x0 (104 : BitVec 12),
    .SD .x30 .x0 (112 : BitVec 12),
    .SD .x30 .x0 (120 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x7 .x12 (0 : BitVec 12),
    .SD .x30 .x7 (64 : BitVec 12),
    .LD .x7 .x12 (8 : BitVec 12),
    .SD .x30 .x7 (72 : BitVec 12),
    .LD .x7 .x12 (16 : BitVec 12),
    .SD .x30 .x7 (80 : BitVec 12),
    .LD .x7 .x12 (24 : BitVec 12),
    .SD .x30 .x7 (88 : BitVec 12),
    .JAL .x0 (20 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.storage_writes_overflow (GuestAddrs.storage_writes_block_upsert + 368)),
    .ADDI .x5 .x5 (laLo GuestAddrs.storage_writes_overflow (GuestAddrs.storage_writes_block_upsert + 368)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x5 .x2 (0 : BitVec 12),
    .LD .x6 .x2 (8 : BitVec 12),
    .LD .x7 .x2 (16 : BitVec 12),
    .LD .x28 .x2 (24 : BitVec 12),
    .LD .x29 .x2 (32 : BitVec 12),
    .LD .x30 .x2 (40 : BitVec 12),
    .LD .x31 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `storageWritesBlockUpsert_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def storageWritesBlockUpsert_relocs : RelocTable :=
  [ (8, .la .x5 "storage_writes_count"),
    (92, .la .x5 "storage_writes_overflow") ]

def storageWritesBlockUpsertFunction : String :=
  "storage_writes_block_upsert:\n" ++ emitProgramR storageWritesBlockUpsert_prog storageWritesBlockUpsert_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `storageWritesBlockUpsert_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem storageWritesBlockUpsertFunction_eq_prog :
    storageWritesBlockUpsertFunction = "storage_writes_block_upsert:\n" ++ emitProgramR storageWritesBlockUpsert_prog storageWritesBlockUpsert_relocs := rfl

#guard storageWritesBlockUpsertFunction.startsWith "storage_writes_block_upsert:\n"
#guard storageWritesBlockUpsert_prog.length = 105

-- ⚠️ RESTATED over `storageWritesBlockUpsert_prog` for the same reason as the
-- `storage_write_record` guards above: `emitProgramR` renders numeric registers
-- and drops the `.Lswb_*` local labels, so the old `splitOn` needles no longer
-- occur. Register map: t2 = x7, t5 = x30, a3 = x13, a6 = x16.
--
-- Baseline at +96: exactly one capture block, APPEND-only (before shared store).
#guard (storageWritesBlockUpsert_prog.filter (· == .SD .x30 .x7 (96 : BitVec 12))).length == 1
-- `.Lswb_base_zero`: the null-baseline arm writes four zero words at +96..+120.
#guard (storageWritesBlockUpsert_prog.filter (fun i => match i with | .SD .x30 .x0 _ => true | _ => false)).length == 4
-- `beqz a3, .Lswb_base_zero`, with its exact 40-byte skip over the copy arm.
#guard (storageWritesBlockUpsert_prog.filter (· == .BEQ .x13 .x0 (40 : BitVec 13))).length == 1
-- Ordering: the capture precedes the shared value store, i.e. it is not in the tail.
#guard storageWritesBlockUpsert_prog.findIdx (· == .SD .x30 .x7 (96 : BitVec 12)) < storageWritesBlockUpsert_prog.findIdx (· == .SD .x30 .x7 (64 : BitVec 12))
-- Block upsert must not grow an a6 baseline channel (tx record owns a6). This is
-- the ABSENCE guard the conversion would have made VACUOUS: the emitted text no
-- longer spells any register `a6`, so the old `splitOn "a6"` matched nothing and
-- passed for free. Restated on the numeric spelling `emitProgramR` actually
-- renders -- which `storage_write_record`, an a6 consumer, does contain.
#guard (storageWritesBlockUpsertFunction.splitOn "x16").length == 1

/-! ## `storage_writes_undo_push`

    Append one undo record. Called by `storage_write_record` BEFORE a changed
    hit or append mutates, which is what makes the journal a faithful stand-in
    for `take_snapshot`'s dict copy (`state_tracker.py:800-806`).

      a3 = entryIndex
      a4 = wasAbsent (0 = overwrite, 1 = append, 2 = destroy_storage drop)
      a5 = payload ptr:
           wasAbsent=0 → prevValue (32 B)
           wasAbsent=1 → ignored
           wasAbsent=2 → full map row (128 B)

    Record stride is 160 B so wasAbsent=2 can journal the full row (review fix
    for the parked-tail overwrite hole when a later append reuses the slot).

    Preserves `t0`-`t6` so the caller's scan state survives the call.

    The capacity is intentionally bounded. If the journal is full, return
    `a0 = 1` and latch `storage_writes_overflow`; callers must reject rather than
    mutate without a rollback record. Success returns `a0 = 0`. -/
def storageWritesUndoPush_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x5 (0 : BitVec 12),
    .SD .x2 .x6 (8 : BitVec 12),
    .SD .x2 .x7 (16 : BitVec 12),
    .SD .x2 .x28 (24 : BitVec 12),
    .SD .x2 .x29 (32 : BitVec 12),
    .SD .x2 .x30 (40 : BitVec 12),
    .SD .x2 .x31 (48 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.storage_writes_undo_count (GuestAddrs.storage_writes_undo_push + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.storage_writes_undo_count (GuestAddrs.storage_writes_undo_push + 32)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (41 : BitVec 20),
    .ADDIW .x7 .x7 (-284 : BitVec 12),
    .BGEU .x6 .x7 (brOff (GuestAddrs.storage_writes_undo_push + 188) (GuestAddrs.storage_writes_undo_push + 52)),
    .LUI .x28 (188 : BitVec 20),
    .ADDIW .x28 .x28 (-1363 : BitVec 12),
    .SLLI .x28 .x28 (12 : BitVec 6),
    .SLLI .x29 .x6 (7 : BitVec 6),
    .SLLI .x30 .x6 (5 : BitVec 6),
    .ADD .x29 .x29 .x30,
    .ADD .x29 .x28 .x29,
    .SD .x29 .x13 (0 : BitVec 12),
    .SD .x29 .x14 (8 : BitVec 12),
    .BEQ .x14 .x0 (48 : BitVec 13),
    .LI .x30 (2 : Word),
    .BNE .x14 .x30 (brOff (GuestAddrs.storage_writes_undo_push + 172) (GuestAddrs.storage_writes_undo_push + 100)),
    .LI .x7 (0 : Word),
    .LI .x30 (128 : Word),
    .BEQ .x7 .x30 (60 : BitVec 13),
    .ADD .x30 .x15 .x7,
    .LD .x31 .x30 (0 : BitVec 12),
    .ADD .x30 .x29 .x7,
    .SD .x30 .x31 (32 : BitVec 12),
    .ADDI .x7 .x7 (8 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LD .x30 .x15 (0 : BitVec 12),
    .SD .x29 .x30 (32 : BitVec 12),
    .LD .x30 .x15 (8 : BitVec 12),
    .SD .x29 .x30 (40 : BitVec 12),
    .LD .x30 .x15 (16 : BitVec 12),
    .SD .x29 .x30 (48 : BitVec 12),
    .LD .x30 .x15 (24 : BitVec 12),
    .SD .x29 .x30 (56 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (32 : BitVec 21),
    .LI .x10 (1 : Word),
    .AUIPC .x28 (laHi GuestAddrs.tx_storage_writes_overflow (GuestAddrs.storage_writes_undo_push + 192)),
    .ADDI .x28 .x28 (laLo GuestAddrs.tx_storage_writes_overflow (GuestAddrs.storage_writes_undo_push + 192)),
    .SD .x28 .x10 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.storage_writes_overflow (GuestAddrs.storage_writes_undo_push + 204)),
    .ADDI .x28 .x28 (laLo GuestAddrs.storage_writes_overflow (GuestAddrs.storage_writes_undo_push + 204)),
    .SD .x28 .x10 (0 : BitVec 12),
    .LD .x5 .x2 (0 : BitVec 12),
    .LD .x6 .x2 (8 : BitVec 12),
    .LD .x7 .x2 (16 : BitVec 12),
    .LD .x28 .x2 (24 : BitVec 12),
    .LD .x29 .x2 (32 : BitVec 12),
    .LD .x30 .x2 (40 : BitVec 12),
    .LD .x31 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `storageWritesUndoPush_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def storageWritesUndoPush_relocs : RelocTable :=
  [ (8, .la .x5 "storage_writes_undo_count"),
    (48, .la .x28 "tx_storage_writes_overflow"),
    (51, .la .x28 "storage_writes_overflow") ]

def storageWritesUndoPushFunction : String :=
  "storage_writes_undo_push:\n" ++ emitProgramR storageWritesUndoPush_prog storageWritesUndoPush_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `storageWritesUndoPush_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem storageWritesUndoPushFunction_eq_prog :
    storageWritesUndoPushFunction = "storage_writes_undo_push:\n" ++ emitProgramR storageWritesUndoPush_prog storageWritesUndoPush_relocs := rfl

#guard storageWritesUndoPushFunction.startsWith "storage_writes_undo_push:\n"
#guard storageWritesUndoPush_prog.length = 63
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
def writeSetsRestoreFrame_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x5 (0 : BitVec 12),
    .SD .x2 .x6 (8 : BitVec 12),
    .SD .x2 .x7 (16 : BitVec 12),
    .SD .x2 .x28 (24 : BitVec 12),
    .SD .x2 .x29 (32 : BitVec 12),
    .SD .x2 .x30 (40 : BitVec 12),
    .SD .x2 .x31 (48 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.storage_writes_undo_count (GuestAddrs.write_sets_restore_frame + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.storage_writes_undo_count (GuestAddrs.write_sets_restore_frame + 32)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x28 (188 : BitVec 20),
    .ADDIW .x28 .x28 (-1363 : BitVec 12),
    .SLLI .x28 .x28 (12 : BitVec 6),
    .LUI .x31 (20 : BitVec 20),
    .ADDIW .x31 .x31 (1451 : BitVec 12),
    .SLLI .x31 .x31 (15 : BitVec 6),
    .ADDI .x31 .x31 (-320 : BitVec 12),
    .BGEU .x10 .x6 (brOff (GuestAddrs.write_sets_restore_frame + 276) (GuestAddrs.write_sets_restore_frame + 72)),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .SLLI .x29 .x6 (7 : BitVec 6),
    .SLLI .x30 .x6 (5 : BitVec 6),
    .ADD .x29 .x29 .x30,
    .ADD .x29 .x28 .x29,
    .LD .x7 .x29 (8 : BitVec 12),
    .LI .x30 (2 : Word),
    .BEQ .x7 .x30 (brOff (GuestAddrs.write_sets_restore_frame + 188) (GuestAddrs.write_sets_restore_frame + 104)),
    .BNE .x7 .x0 (52 : BitVec 13),
    .LD .x7 .x29 (0 : BitVec 12),
    .SLLI .x30 .x7 (7 : BitVec 6),
    .ADD .x30 .x31 .x30,
    .LD .x7 .x29 (32 : BitVec 12),
    .SD .x30 .x7 (64 : BitVec 12),
    .LD .x7 .x29 (40 : BitVec 12),
    .SD .x30 .x7 (72 : BitVec 12),
    .LD .x7 .x29 (48 : BitVec 12),
    .SD .x30 .x7 (80 : BitVec 12),
    .LD .x7 .x29 (56 : BitVec 12),
    .SD .x30 .x7 (88 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.write_sets_restore_frame + 72) (GuestAddrs.write_sets_restore_frame + 156)),
    .AUIPC .x7 (laHi GuestAddrs.tx_storage_writes_count (GuestAddrs.write_sets_restore_frame + 160)),
    .ADDI .x7 .x7 (laLo GuestAddrs.tx_storage_writes_count (GuestAddrs.write_sets_restore_frame + 160)),
    .LD .x30 .x7 (0 : BitVec 12),
    .BEQ .x30 .x0 (brOff (GuestAddrs.write_sets_restore_frame + 72) (GuestAddrs.write_sets_restore_frame + 172)),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .SD .x7 .x30 (0 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.write_sets_restore_frame + 72) (GuestAddrs.write_sets_restore_frame + 184)),
    .AUIPC .x7 (laHi GuestAddrs.tx_storage_writes_count (GuestAddrs.write_sets_restore_frame + 188)),
    .ADDI .x7 .x7 (laLo GuestAddrs.tx_storage_writes_count (GuestAddrs.write_sets_restore_frame + 188)),
    .LD .x30 .x7 (0 : BitVec 12),
    .SLLI .x5 .x30 (7 : BitVec 6),
    .ADD .x5 .x31 .x5,
    .SD .x2 .x5 (56 : BitVec 12),
    .LI .x7 (0 : Word),
    .LI .x30 (128 : Word),
    .BEQ .x7 .x30 (32 : BitVec 13),
    .ADD .x30 .x29 .x7,
    .LD .x30 .x30 (32 : BitVec 12),
    .LD .x5 .x2 (56 : BitVec 12),
    .ADD .x5 .x5 .x7,
    .SD .x5 .x30 (0 : BitVec 12),
    .ADDI .x7 .x7 (8 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .AUIPC .x7 (laHi GuestAddrs.tx_storage_writes_count (GuestAddrs.write_sets_restore_frame + 252)),
    .ADDI .x7 .x7 (laLo GuestAddrs.tx_storage_writes_count (GuestAddrs.write_sets_restore_frame + 252)),
    .LD .x30 .x7 (0 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .SD .x7 .x30 (0 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.write_sets_restore_frame + 72) (GuestAddrs.write_sets_restore_frame + 272)),
    .AUIPC .x5 (laHi GuestAddrs.storage_writes_undo_count (GuestAddrs.write_sets_restore_frame + 276)),
    .ADDI .x5 .x5 (laLo GuestAddrs.storage_writes_undo_count (GuestAddrs.write_sets_restore_frame + 276)),
    .SD .x5 .x10 (0 : BitVec 12),
    .LD .x5 .x2 (0 : BitVec 12),
    .LD .x6 .x2 (8 : BitVec 12),
    .LD .x7 .x2 (16 : BitVec 12),
    .LD .x28 .x2 (24 : BitVec 12),
    .LD .x29 .x2 (32 : BitVec 12),
    .LD .x30 .x2 (40 : BitVec 12),
    .LD .x31 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `writeSetsRestoreFrame_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def writeSetsRestoreFrame_relocs : RelocTable :=
  [ (8, .la .x5 "storage_writes_undo_count"),
    (40, .la .x7 "tx_storage_writes_count"),
    (47, .la .x7 "tx_storage_writes_count"),
    (63, .la .x7 "tx_storage_writes_count"),
    (69, .la .x5 "storage_writes_undo_count") ]

def writeSetsRestoreFrameFunction : String :=
  "write_sets_restore_frame:\n" ++ emitProgramR writeSetsRestoreFrame_prog writeSetsRestoreFrame_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `writeSetsRestoreFrame_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem writeSetsRestoreFrameFunction_eq_prog :
    writeSetsRestoreFrameFunction = "write_sets_restore_frame:\n" ++ emitProgramR writeSetsRestoreFrame_prog writeSetsRestoreFrame_relocs := rfl

#guard writeSetsRestoreFrameFunction.startsWith "write_sets_restore_frame:\n"
#guard writeSetsRestoreFrame_prog.length = 81
/-! ## `destroy_storage` (GH #10645)

    Spec `state_tracker.py:560-580`: if `address` is in `tx_state.storage_writes`,
    add every key to `storage_reads`, then delete the address's write map.

    ONE shared conversion for every guest site that mirrors a `destroy_storage`
    caller (`process_create_message`, `clear_account_preserving_balance` /
    EIP-6780 delete commit). Do not copy this body into call sites.

    Calling convention:
      a0 = rowAddress ptr (32 B) — same keying as `storage_write_record` /
           `storage_read_record` (frame `env.ADDRESS` LE stack-word form)
      ra = return; no result register

    Rollback: each removed row is swapped to the map tail then dropped with an
    undo record `wasAbsent = 2` that journals the **full 128 B row** (not a bare
    count bump). `write_sets_restore_frame` memcpy's the row back to `map[count]`
    then increments. Existing `0`/`1` undo codes are unchanged.
-/
def destroyStorageFunction : String :=
  "destroy_storage:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd a0, 48(sp)\n" ++
  "  sd t0, 56(sp); sd t1, 64(sp); sd t2, 72(sp); sd t3, 80(sp); sd t4, 88(sp); sd t5, 96(sp); sd t6, 104(sp)\n" ++
  "  la t0, tx_storage_writes_count; ld s0, 0(t0)\n" ++
  "  li s1, " ++ toString storageWritesTxBase ++ "\n" ++
  "  li s2, 0\n" ++
  ".Lds_loop:\n" ++
  "  bgeu s2, s0, .Lds_done\n" ++
  "  slli t0, s2, 7; add s3, s1, t0\n" ++
  "  ld a0, 48(sp)\n" ++
  "  ld t0, 0(s3);  ld t1, 0(a0);  bne t0, t1, .Lds_next\n" ++
  "  ld t0, 8(s3);  ld t1, 8(a0);  bne t0, t1, .Lds_next\n" ++
  "  ld t0, 16(s3); ld t1, 16(a0); bne t0, t1, .Lds_next\n" ++
  "  ld t0, 24(s3); ld t1, 24(a0); bne t0, t1, .Lds_next\n" ++
  -- Reject before the read-set append, swap, or map-count mutation when the
  -- shared undo journal has no slot. The helper's guard is still authoritative,
  -- but this earlier check keeps every destroy side effect behind the capacity
  -- decision, including the non-tail swap.
  "  la t0, storage_writes_undo_count; ld t1, 0(t0); li t2, " ++ toString storageWritesUndoCapacity ++ "; bgeu t1, t2, .Lds_overflow\n" ++
  "  ld a0, 48(sp); addi a1, s3, 32; jal ra, storage_read_record\n" ++
  "  addi s4, s0, -1\n" ++
  "  beq s2, s4, .Lds_drop\n" ++
  "  slli t0, s4, 7; add t0, s1, t0\n" ++
  "  li t1, 0\n" ++
  ".Lds_swap:\n" ++
  "  li t2, 128; beq t1, t2, .Lds_drop\n" ++
  "  add t3, s3, t1; ld t4, 0(t3); add t5, t0, t1; ld t6, 0(t5); sd t6, 0(t3); sd t4, 0(t5); addi t1, t1, 8; j .Lds_swap\n" ++
  ".Lds_drop:\n" ++
  -- Journal full row at tail (destroyed content after swap), then drop count.
  "  slli t0, s4, 7; add a5, s1, t0\n" ++
  "  mv a3, s4; li a4, 2; jal ra, storage_writes_undo_push\n" ++
  "  bnez a0, .Lds_overflow\n" ++
  "  mv s0, s4; la t0, tx_storage_writes_count; sd s0, 0(t0)\n" ++
  "  j .Lds_loop\n" ++
  ".Lds_next:\n" ++
  "  addi s2, s2, 1; j .Lds_loop\n" ++
  ".Lds_overflow:\n" ++
  "  li t1, 1; la t0, tx_storage_writes_overflow; sd t1, 0(t0); la t0, storage_writes_overflow; sd t1, 0(t0); j .Lds_done\n" ++
  ".Lds_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  ld a0, 48(sp); ld t0, 56(sp); ld t1, 64(sp); ld t2, 72(sp); ld t3, 80(sp); ld t4, 88(sp); ld t5, 96(sp); ld t6, 104(sp)\n" ++
  "  addi sp, sp, 112; ret\n"

#guard (destroyStorageFunction.splitOn "destroy_storage:").length == 2
#guard (destroyStorageFunction.splitOn "jal ra, storage_read_record").length == 2
#guard (destroyStorageFunction.splitOn "li a4, 2").length == 2
-- ⚠️ RESTATED over `storageWritesUndoPush_prog`: `emitProgramR` drops the
-- `.Lswup_*` local labels and renders numeric registers, so the two `splitOn`
-- needles below no longer occur in the emitted text. `.Lswup_fail` is the
-- `li a0, 1` fail-closed arm (t1 = x6, t2 = x7, a0 = x10); it is unique --
-- `li a0, 0` is the success arm -- and it sits at instruction index 47, byte 188.
#guard storageWritesUndoPush_prog.findIdx (· == .LI .x10 (1 : Word)) == 47
#guard (storageWritesUndoPush_prog.filter (· == .LI .x10 (1 : Word))).length == 1
-- The bounded-journal check `bgeu t1, t2, .Lswup_fail` is the ONLY `bgeu` here,
-- and it must branch to that fail arm rather than fall through into a push.
#guard (storageWritesUndoPush_prog.zipIdx.filter (fun p => match p.1 with | .BGEU .x6 .x7 off => (4 * p.2 : Int) + off.toInt == 188 | _ => false)).length == 1

/-! ## `write_sets_discard_tx`

    The transaction-level map is dropped WITHOUT being promoted.

    The spec gets this for free: every transaction runs against a **fresh**
    `TransactionState` (`fork.py:1043`), so a transaction whose writes are never
    incorporated simply has them discarded when the object goes away. The guest
    reuses one arena across transactions, so the drop has to be a named
    operation — the same reason `read_sets_discard_tx` exists on the read side
    for `fork.py:745-752`'s throwaway state.

    **Why this is required rather than tidy.** `write_sets_incorporate_tx` runs
    on the account-writes commit path, which the multi-tx loop
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
def writeSetsDiscardTx_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.tx_storage_writes_count (GuestAddrs.write_sets_discard_tx + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_storage_writes_count (GuestAddrs.write_sets_discard_tx + 0)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.tx_storage_writes_overflow (GuestAddrs.write_sets_discard_tx + 12)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_storage_writes_overflow (GuestAddrs.write_sets_discard_tx + 12)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.storage_writes_undo_count (GuestAddrs.write_sets_discard_tx + 24)),
    .ADDI .x5 .x5 (laLo GuestAddrs.storage_writes_undo_count (GuestAddrs.write_sets_discard_tx + 24)),
    .SD .x5 .x0 (0 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `writeSetsDiscardTx_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def writeSetsDiscardTx_relocs : RelocTable :=
  [ (0, .la .x5 "tx_storage_writes_count"),
    (3, .la .x5 "tx_storage_writes_overflow"),
    (6, .la .x5 "storage_writes_undo_count") ]

def writeSetsDiscardTxFunction : String :=
  "write_sets_discard_tx:\n" ++ emitProgramR writeSetsDiscardTx_prog writeSetsDiscardTx_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `writeSetsDiscardTx_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem writeSetsDiscardTxFunction_eq_prog :
    writeSetsDiscardTxFunction = "write_sets_discard_tx:\n" ++ emitProgramR writeSetsDiscardTx_prog writeSetsDiscardTx_relocs := rfl

#guard writeSetsDiscardTxFunction.startsWith "write_sets_discard_tx:\n"
#guard writeSetsDiscardTx_prog.length = 10
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
