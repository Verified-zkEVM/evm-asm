/-
  EvmAsm.Codegen.Programs.AccountWriteUndo

  The transaction-level undo journal for the account-write map.  The journal
  is emitted separately so the map, resolver, and builder code can stay in one
  module while the rollback mechanism remains a cohesive unit.
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

/-- Transaction-local entries and undo records share one fixed capacity. -/
def txAccountWritesCapacity : Nat := 16384

/-! ## `account_writes_undo_push`

    Append one undo entry describing a write about to happen to the tx-level map.

    a5 = entryIndex, a6 = wasAbsent (1 on append, 0 on overwrite).
    On an overwrite the superseded fields are read from the entry itself, so the
    caller does not have to stage them. The journal has the same provisioned
    16384-entry capacity as the transaction map, but the push is separately
    bounded because repeated updates can add undo rows without increasing the
    live map count. The current producer census derives 4294 rows for the
    densest path: two pushes for each EIP-7702 MTx authorization at 7816 regular
    gas, plus six fixed boundary records. This is workload justification for
    retaining the physical reservation, not a replacement for its fail-closed
    bound. On exhaustion it returns `a0 = 1` and latches both overflow flags
    before any out-of-range store; success returns `a0 = 0`. -/
def accountWritesUndoPushFunction : String :=
  "account_writes_undo_push:\n" ++
  -- GH #10810: save t5/t6 as well, so this routine's CONTRACT matches what its callers
  -- already assume.  `account_write_record`'s hit path holds the target row address in t5
  -- ACROSS this call and then stores every field through it -- balance at 32(t5), nonce at
  -- 64(t5), the valid mask at 112(t5) -- without re-establishing it, while the append path
  -- DOES recompute t5 afterwards.  That asymmetry is evidence someone already knew the call
  -- is not t5-safe.  The hit path was correct only because this body happens to use t0..t4
  -- exclusively, whereas the prologue promised only t0..t4 -- i.e. t5 was documented as
  -- clobberable and merely accidentally preserved.
  --
  -- The failure mode if that accident ever ended: a stale t5 sends the fieldwise stores,
  -- INCLUDING the valid-mask `or` at 112(t5), into a DIFFERENT 128-byte row -- one account's
  -- balance or nonce written onto another account's record, and a mask bit set on an account
  -- that never had that component written, with no trap and no error code.  That is the
  -- wrong-row class only a whole-structure hash catches.
  --
  -- Fixing the CALLEE rather than recomputing t5 at the one call site is deliberate: it
  -- protects every future caller instead of leaving the next one to rediscover the hazard.
  -- Frame grows 48 -> 64 to hold the two extra saves (still 16-byte aligned).
  "  addi sp, sp, -64\n" ++
  "  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp); sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)\n" ++
  "  la t0, account_writes_undo_count; ld t1, 0(t0)\n" ++
  "  li t2, " ++ toString txAccountWritesCapacity ++ "; bgeu t1, t2, .Lawu_fail\n" ++
  "  li t2, 0xa2d20000\n" ++                                       -- ACCOUNT_WRITES_UNDO_AREA
  "  slli t3, t1, 7; add t3, t2, t3\n" ++                          -- t3 = &undo[count]
  "  sd a5, 0(t3)\n" ++                                            -- entryIndex
  "  sd a6, 8(t3)\n" ++                                            -- wasAbsent
  "  bnez a6, .Lawu_appended\n" ++
  -- Overwrite: snapshot every non-key word, including the valid mask. The
  -- reverse replay must restore an invalid component as invalid, not merely
  -- restore its payload bytes.
  "  li t2, 0xa2b20000; slli t4, a5, 7; add t4, t2, t4\n" ++       -- t4 = &tx_entry[idx]
  "  ld t2, 32(t4);  sd t2, 16(t3); ld t2, 40(t4);  sd t2, 24(t3); ld t2, 48(t4);  sd t2, 32(t3); ld t2, 56(t4);  sd t2, 40(t3)\n" ++
  "  ld t2, 64(t4);  sd t2, 48(t3); ld t2, 72(t4);  sd t2, 56(t3); ld t2, 80(t4);  sd t2, 64(t3); ld t2, 88(t4);  sd t2, 72(t3)\n" ++
  "  ld t2, 96(t4);  sd t2, 80(t3); ld t2, 104(t4); sd t2, 88(t3); ld t2, 112(t4); sd t2, 96(t3); ld t2, 120(t4); sd t2, 104(t3)\n" ++
  ".Lawu_appended:\n" ++
  "  addi t1, t1, 1; la t0, account_writes_undo_count; sd t1, 0(t0); li a0, 0; j .Lawu_done\n" ++
  ".Lawu_fail:\n" ++
  "  li a0, 1; la t3, tx_account_writes_overflow; sd a0, 0(t3); la t3, account_writes_overflow; sd a0, 0(t3)\n" ++
  ".Lawu_done:\n" ++
  "  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp); ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

/-! ## `account_writes_restore_frame`

    Reverse-replay the undo journal down to a mark, mirroring
    `restore_tx_state` (`state_tracker.py:809-826`) rebinding the snapshot copy.

    a0 = mark (the `account_writes_undo_count` captured on frame entry).

    Reverse order is required, not merely tidy: two writes to the same key leave
    two entries, and replaying forwards would restore the older value last.
    Appended keys are unwound by truncating the map, which is sound because
    nesting is LIFO — a child's appends sit above the parent's mark. A successful
    child's entries are RETAINED so a later parent revert still undoes them,
    matching `frame_return`'s merge-on-success cursor discipline. -/
def accountWritesRestoreFrameFunction : String :=
  "account_writes_restore_frame:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp); sd t4, 32(sp); sd t5, 40(sp)\n" ++
  "  la t0, account_writes_undo_count; ld t1, 0(t0)\n" ++
  ".Lawf_loop:\n" ++
  "  bgeu a0, t1, .Lawf_done\n" ++                                 -- count <= mark: nothing left
  "  addi t1, t1, -1\n" ++                                         -- pop the newest
  "  li t2, 0xa2d20000; slli t3, t1, 7; add t3, t2, t3\n" ++       -- t3 = &undo[count]
  "  ld t4, 0(t3)\n" ++                                            -- entryIndex
  "  ld t5, 8(t3)\n" ++                                            -- wasAbsent
  "  beqz t5, .Lawf_overwrite\n" ++
  -- Appended: drop it by truncating the map to this index.
  "  la t2, tx_account_writes_count; sd t4, 0(t2)\n" ++
  "  j .Lawf_loop\n" ++
  ".Lawf_overwrite:\n" ++
  "  li t2, 0xa2b20000; slli t5, t4, 7; add t5, t2, t5\n" ++       -- t5 = &tx_entry[idx]
  "  ld t2, 16(t3); sd t2, 32(t5); ld t2, 24(t3); sd t2, 40(t5); ld t2, 32(t3); sd t2, 48(t5); ld t2, 40(t3); sd t2, 56(t5)\n" ++
  "  ld t2, 48(t3); sd t2, 64(t5); ld t2, 56(t3); sd t2, 72(t5); ld t2, 64(t3); sd t2, 80(t5); ld t2, 72(t3); sd t2, 88(t5)\n" ++
  "  ld t2, 80(t3); sd t2, 96(t5); ld t2, 88(t3); sd t2, 104(t5); ld t2, 96(t3); sd t2, 112(t5); ld t2, 104(t3); sd t2, 120(t5)\n" ++
  "  j .Lawf_loop\n" ++
  ".Lawf_done:\n" ++
  "  la t0, account_writes_undo_count; sd t1, 0(t0)\n" ++
  "  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp); ld t4, 32(sp); ld t5, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret\n"

/-! Data declaration for the undo journal counter. -/
def accountWritesUndoDataSection : String :=
  "account_writes_undo_count:\n  .zero 8\n"

end EvmAsm.Codegen
