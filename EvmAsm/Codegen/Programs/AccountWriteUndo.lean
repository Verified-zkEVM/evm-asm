/-
  EvmAsm.Codegen.Programs.AccountWriteUndo

  The transaction-level undo journal for the account-write map.  The journal
  is emitted separately so the map, resolver, and builder code can stay in one
  module while the rollback mechanism remains a cohesive unit.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Stateless.MemoryLayout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Transaction-local **map** capacity: DISTINCT accounts written by one
    transaction.

    Derived (GH #11770) against the per-transaction regular-gas ceiling, which
    is `TX_MAX_GAS_LIMIT - intrinsic.regular` = 16,777,216 - 12,000 =
    **16,765,216** (`transactions.py:63`, `fork.py:1099-1100` at `e5a8caf1b`) --
    NOT the 200M block limit, because this map is cleared at transaction
    incorporation (`state_tracker.py:874`). The cheapest way to put a DISTINCT
    account in it is a cold `CALL` into a code-bearing account
    (`COLD_ACCOUNT_ACCESS` = 3000) plus one `SSTORE` (104) plus call setup
    (~17) ~= 3,121 gas, so at most **5,371** distinct keys per transaction.
    16384 is a 3.05x margin -- AMPLE, and deliberately not shrunk. -/
def txAccountWritesCapacity : Nat := 16384

/-- Transaction-local **undo journal** capacity: account-write EVENTS, which is
    a strictly larger quantity than distinct accounts and is why this is no
    longer the same constant as `txAccountWritesCapacity`.

    ⛔ The journal counts WRITES, not accounts: `account_write_record` pushes one
    entry on BOTH arms -- the overwrite hit (`AccountWriteMap.lean:230`) and the
    append (`:234`) -- so a transaction that writes a handful of accounts many
    times consumes a slot per write while the map stays small.

    Derived (GH #11770): the cheapest repeatable event is a warm no-op `SSTORE`,
    which pushes one entry unconditionally via `Storage.lean:664` ->
    `account_write_touch_current`. `sstore` always charges the access cost and
    `WARM_ACCESS` is 100 (`vm/gas.py:69`); the `STORAGE_WRITE` charge is gated on
    `original == current and current != new`, so a no-op pays access only.
    `PUSH0 PUSH0 SSTORE` is 104 gas, hence **16,765,216 / 104 = 161,204** events
    reachable in one transaction. Rounded up to the next power of two.

    ⚠️ Note `check_gas(evm, max(gas_cost, CALL_STIPEND + 1))` = 2301 in `sstore`
    is a LIVENESS CHECK, not a debit -- `charge_gas` takes 100. Deriving from
    the check would under-count the reachable maximum by 23x.

    The superseded justification derived 4,294 rows from EIP-7702
    authorizations at 7,816 regular gas. That arithmetic was right; its producer
    census was incomplete -- it omitted the SSTORE touch, which is 75x cheaper
    per event and is what false-rejected rows 18635, 18637 and 20992. -/
def accountWritesUndoCapacity : Nat := 163840

/-! ## `account_writes_undo_push`

    Append one undo entry describing a write about to happen to the tx-level map.

    a5 = entryIndex, a6 = wasAbsent (1 on append, 0 on overwrite).
    On an overwrite the superseded fields are read from the entry itself, so the
    caller does not have to stage them. The journal is bounded by
    `accountWritesUndoCapacity`, NOT by the map's capacity: repeated updates add
    undo rows without increasing the live map count, so the two count different
    things and are now sized separately (GH #11770). On exhaustion it returns
    `a0 = 1` and latches both overflow flags before any out-of-range store;
    success returns `a0 = 0`. -/
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
  "  li t2, " ++ toString accountWritesUndoCapacity ++ "; bgeu t1, t2, .Lawu_fail\n" ++
  "  li t2, " ++ toString EvmAsm.Stateless.ACCOUNT_WRITES_UNDO_AREA.toNat ++ "\n" ++ -- ACCOUNT_WRITES_UNDO_AREA
  "  slli t3, t1, 7; add t3, t2, t3\n" ++                          -- t3 = &undo[count]
  "  sd a5, 0(t3)\n" ++                                            -- entryIndex
  "  sd a6, 8(t3)\n" ++                                            -- wasAbsent
  "  bnez a6, .Lawu_appended\n" ++
  -- Overwrite: snapshot every non-key word, including the valid mask. The
  -- reverse replay must restore an invalid component as invalid, not merely
  -- restore its payload bytes.
  "  li t2, " ++ toString EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat ++ "; slli t4, a5, 7; add t4, t2, t4\n" ++ -- t4 = &tx_entry[idx]
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
def accountWritesRestoreFrame_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x5 (0 : BitVec 12),
    .SD .x2 .x6 (8 : BitVec 12),
    .SD .x2 .x7 (16 : BitVec 12),
    .SD .x2 .x28 (24 : BitVec 12),
    .SD .x2 .x29 (32 : BitVec 12),
    .SD .x2 .x30 (40 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_undo_count (GuestAddrs.account_writes_restore_frame + 28)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_undo_count (GuestAddrs.account_writes_restore_frame + 28)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BGEU .x10 .x6 (brOff (GuestAddrs.account_writes_restore_frame + 216) (GuestAddrs.account_writes_restore_frame + 40)),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (1991 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .SLLI .x28 .x6 (7 : BitVec 6),
    .ADD .x28 .x7 .x28,
    .LD .x29 .x28 (0 : BitVec 12),
    .LD .x30 .x28 (8 : BitVec 12),
    .BEQ .x30 .x0 (brOff (GuestAddrs.account_writes_restore_frame + 96) (GuestAddrs.account_writes_restore_frame + 76)),
    .AUIPC .x7 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_restore_frame + 80)),
    .ADDI .x7 .x7 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_restore_frame + 80)),
    .SD .x7 .x29 (0 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_restore_frame + 40) (GuestAddrs.account_writes_restore_frame + 92)),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (2031 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .SLLI .x30 .x29 (7 : BitVec 6),
    .ADD .x30 .x7 .x30,
    .LD .x7 .x28 (16 : BitVec 12),
    .SD .x30 .x7 (32 : BitVec 12),
    .LD .x7 .x28 (24 : BitVec 12),
    .SD .x30 .x7 (40 : BitVec 12),
    .LD .x7 .x28 (32 : BitVec 12),
    .SD .x30 .x7 (48 : BitVec 12),
    .LD .x7 .x28 (40 : BitVec 12),
    .SD .x30 .x7 (56 : BitVec 12),
    .LD .x7 .x28 (48 : BitVec 12),
    .SD .x30 .x7 (64 : BitVec 12),
    .LD .x7 .x28 (56 : BitVec 12),
    .SD .x30 .x7 (72 : BitVec 12),
    .LD .x7 .x28 (64 : BitVec 12),
    .SD .x30 .x7 (80 : BitVec 12),
    .LD .x7 .x28 (72 : BitVec 12),
    .SD .x30 .x7 (88 : BitVec 12),
    .LD .x7 .x28 (80 : BitVec 12),
    .SD .x30 .x7 (96 : BitVec 12),
    .LD .x7 .x28 (88 : BitVec 12),
    .SD .x30 .x7 (104 : BitVec 12),
    .LD .x7 .x28 (96 : BitVec 12),
    .SD .x30 .x7 (112 : BitVec 12),
    .LD .x7 .x28 (104 : BitVec 12),
    .SD .x30 .x7 (120 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_restore_frame + 40) (GuestAddrs.account_writes_restore_frame + 212)),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_undo_count (GuestAddrs.account_writes_restore_frame + 216)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_undo_count (GuestAddrs.account_writes_restore_frame + 216)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x5 .x2 (0 : BitVec 12),
    .LD .x6 .x2 (8 : BitVec 12),
    .LD .x7 .x2 (16 : BitVec 12),
    .LD .x28 .x2 (24 : BitVec 12),
    .LD .x29 .x2 (32 : BitVec 12),
    .LD .x30 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountWritesRestoreFrame_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWritesRestoreFrame_relocs : RelocTable :=
  [ (7, .la .x5 "account_writes_undo_count"),
    (20, .la .x7 "tx_account_writes_count"),
    (54, .la .x5 "account_writes_undo_count") ]

def accountWritesRestoreFrameFunction : String :=
  "account_writes_restore_frame:\n" ++ emitProgramR accountWritesRestoreFrame_prog accountWritesRestoreFrame_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWritesRestoreFrame_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWritesRestoreFrameFunction_eq_prog :
    accountWritesRestoreFrameFunction = "account_writes_restore_frame:\n" ++ emitProgramR accountWritesRestoreFrame_prog accountWritesRestoreFrame_relocs := rfl

#guard accountWritesRestoreFrameFunction.startsWith "account_writes_restore_frame:\n"
#guard accountWritesRestoreFrame_prog.length = 65
/-! Data declaration for the undo journal counter. -/
def accountWritesUndoDataSection : String :=
  "account_writes_undo_count:\n  .zero 8\n"

end EvmAsm.Codegen
