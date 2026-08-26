/-
  EvmAsm.Codegen.Programs.AccountWriteMapTail

  Tail of AccountWriteMap split to keep Codegen/Programs files under
  the 1500-line cap. The parent module supplies the shared map declarations.
-/

import EvmAsm.Codegen.Programs.AccountWriteMapTailMutation
import EvmAsm.Codegen.Programs.AccountWriteMap
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.AccountWriteMapResolvers

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## `account_writes_block_upsert`

    Upsert one record into the BLOCK level. Called only by
    `account_writes_incorporate_tx`; the block level has no other writer,
    mirroring the spec where `block.account_writes[address] = account` appears
    only inside `incorporate_tx_into_block` (`state_tracker.py:864-865`).

    An upsert rather than an append, because the block level is a map too. It
    overlays only the valid components from the transaction row; an account
    written in two transactions keeps the earlier final component until a later
    transaction actually writes that same component.

    a0 = &tx_entry (a 128 B fieldwise row). No result register;
    overflow sets `account_writes_overflow`. -/
def accountWritesBlockUpsert_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x5 (0 : BitVec 12),
    .SD .x2 .x6 (8 : BitVec 12),
    .SD .x2 .x7 (16 : BitVec 12),
    .SD .x2 .x28 (24 : BitVec 12),
    .SD .x2 .x29 (32 : BitVec 12),
    .SD .x2 .x30 (40 : BitVec 12),
    .SD .x2 .x31 (48 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.account_writes_block_upsert + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.account_writes_block_upsert + 32)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x28 (95 : BitVec 20),
    .ADDIW .x28 .x28 (-1359 : BitVec 12),
    .SLLI .x28 .x28 (13 : BitVec 6),
    .LI .x29 (0 : Word),
    .BGEU .x29 .x6 (brOff (GuestAddrs.account_writes_block_upsert + 148) (GuestAddrs.account_writes_block_upsert + 60)),
    .SLLI .x30 .x29 (7 : BitVec 6),
    .ADD .x30 .x28 .x30,
    .LI .x31 (20 : Word),
    .MV .x7 .x30,
    .MV .x28 .x10,
    .BEQ .x31 .x0 (brOff (GuestAddrs.account_writes_block_upsert + 268) (GuestAddrs.account_writes_block_upsert + 84)),
    .LBU .x6 .x7 (0 : BitVec 12),
    .LBU .x11 .x28 (0 : BitVec 12),
    .BNE .x6 .x11 (20 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.account_writes_block_upsert + 116)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.account_writes_block_upsert + 116)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x28 (95 : BitVec 20),
    .ADDIW .x28 .x28 (-1359 : BitVec 12),
    .SLLI .x28 .x28 (13 : BitVec 6),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_block_upsert + 60) (GuestAddrs.account_writes_block_upsert + 144)),
    .LUI .x7 (25 : BitVec 20),
    .BGEU .x6 .x7 (brOff (GuestAddrs.account_writes_block_upsert + 400) (GuestAddrs.account_writes_block_upsert + 152)),
    .SLLI .x30 .x6 (7 : BitVec 6),
    .ADD .x30 .x28 .x30,
    .LI .x31 (20 : Word),
    .MV .x7 .x10,
    .BEQ .x31 .x0 (28 : BitVec 13),
    .LBU .x28 .x7 (0 : BitVec 12),
    .SB .x30 .x28 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x30 .x30 (-20 : BitVec 12),
    .SW .x30 .x0 (20 : BitVec 12),
    .SD .x30 .x0 (24 : BitVec 12),
    .SD .x30 .x0 (32 : BitVec 12),
    .SD .x30 .x0 (40 : BitVec 12),
    .SD .x30 .x0 (48 : BitVec 12),
    .SD .x30 .x0 (56 : BitVec 12),
    .SD .x30 .x0 (64 : BitVec 12),
    .SD .x30 .x0 (72 : BitVec 12),
    .SD .x30 .x0 (80 : BitVec 12),
    .SD .x30 .x0 (88 : BitVec 12),
    .SD .x30 .x0 (96 : BitVec 12),
    .SD .x30 .x0 (104 : BitVec 12),
    .SD .x30 .x0 (112 : BitVec 12),
    .SD .x30 .x0 (120 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x7 .x10 (112 : BitVec 12),
    .ANDI .x28 .x7 (1 : BitVec 12),
    .BEQ .x28 .x0 (36 : BitVec 13),
    .LD .x28 .x10 (32 : BitVec 12),
    .SD .x30 .x28 (32 : BitVec 12),
    .LD .x28 .x10 (40 : BitVec 12),
    .SD .x30 .x28 (40 : BitVec 12),
    .LD .x28 .x10 (48 : BitVec 12),
    .SD .x30 .x28 (48 : BitVec 12),
    .LD .x28 .x10 (56 : BitVec 12),
    .SD .x30 .x28 (56 : BitVec 12),
    .ANDI .x28 .x7 (2 : BitVec 12),
    .BEQ .x28 .x0 (12 : BitVec 13),
    .LD .x28 .x10 (64 : BitVec 12),
    .SD .x30 .x28 (64 : BitVec 12),
    .ANDI .x28 .x7 (4 : BitVec 12),
    .BEQ .x28 .x0 (20 : BitVec 13),
    .LD .x28 .x10 (80 : BitVec 12),
    .SD .x30 .x28 (80 : BitVec 12),
    .LD .x28 .x10 (88 : BitVec 12),
    .SD .x30 .x28 (88 : BitVec 12),
    .ANDI .x28 .x7 (8 : BitVec 12),
    .BEQ .x28 .x0 (12 : BitVec 13),
    .LD .x28 .x10 (72 : BitVec 12),
    .SD .x30 .x28 (72 : BitVec 12),
    .ANDI .x28 .x7 (16 : BitVec 12),
    .BEQ .x28 .x0 (12 : BitVec 13),
    .LD .x28 .x10 (96 : BitVec 12),
    .SD .x30 .x28 (96 : BitVec 12),
    .LD .x28 .x30 (112 : BitVec 12),
    .OR .x7 .x7 .x28,
    .SD .x30 .x7 (112 : BitVec 12),
    .JAL .x0 (20 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_overflow (GuestAddrs.account_writes_block_upsert + 400)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_overflow (GuestAddrs.account_writes_block_upsert + 400)),
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

/-- Reloc side-table for `accountWritesBlockUpsert_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWritesBlockUpsert_relocs : RelocTable :=
  [ (8, .la .x5 "account_writes_count"),
    (29, .la .x5 "account_writes_count"),
    (100, .la .x5 "account_writes_overflow") ]

def accountWritesBlockUpsertFunction : String :=
  "account_writes_block_upsert:\n" ++ emitProgramR accountWritesBlockUpsert_prog accountWritesBlockUpsert_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWritesBlockUpsert_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWritesBlockUpsertFunction_eq_prog :
    accountWritesBlockUpsertFunction = "account_writes_block_upsert:\n" ++ emitProgramR accountWritesBlockUpsert_prog accountWritesBlockUpsert_relocs := rfl

#guard accountWritesBlockUpsertFunction.startsWith "account_writes_block_upsert:\n"
#guard accountWritesBlockUpsert_prog.length = 113
/-! ## `account_writes_apply_deletes`

    EIP-6780 records a same-transaction-created SELFDESTRUCT in the deferred
    `account_state_delete` set (the guest's `accounts_to_delete`).  Applied at
    the transaction boundary before the builder walk, matching
    `fork.py:1201-1202` → `clear_account_preserving_balance`.

    Spec shape (`state_tracker.py:536-557` + `modify_state:641-643`): clear
    nonce/code, preserve balance, then if the account is empty destroy it via
    `set_account(..., None)`.  Deletion is therefore **absence in
    `account_writes`** (`optionalState@72 = 0` with STATE valid), not a side
    list entry.  GH #11328.

    On a map miss (delete address never recorded this tx), upsert a STATE=None
    row — same end state as destroy_account after a zero-balance clear.

    Map-row balance alone is insufficient after self-burn: `record_nonstorage_effect`
    derives HAS_BALANCE only from pre≠post, so clear_preserving with pre=post=live
    leaves the write-map bal at the CREATE seed (often 0) **without** HAS_BALANCE.
    When map bal=0 and HAS_BALANCE is clear, resolve the preserved balance through
    the same lower-tier chain as `get_account`: the block map for a prior
    transaction, then the authenticated parent witness.  When map bal=0 **and**
    HAS_BALANCE is set, the zero is authoritative (SELFDESTRUCT drained the
    account); do **not** re-fetch parent pre-balance — that resurrected a
    pre-seeded CREATE address (bal=100) as Present on 01114 and failed NPR.
    Do not use the live AccountState overlay here; it is not a pre-state tier
    and can hide the exact map miss this fallback is meant to resolve (03736
    self_burn).  This is the same correction documented in
    `account_resolve_pre_state` below: its former durable-overlay tier was
    removed because `update_builder_from_tx` had already applied the sender's
    post value before that routine was asked for a pre-state value.  The two
    consumers must therefore share the same map-then-parent precedence, not
    recreate a live overlay tier.

    No arguments; a0 = 0 on success / 1 on bounded-arena failure. -/
def accountWritesApplyDeletes_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.account_state_delete_count (GuestAddrs.account_writes_apply_deletes + 24)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_state_delete_count (GuestAddrs.account_writes_apply_deletes + 24)),
    .LD .x18 .x5 (0 : BitVec 12),
    .LUI .x5 (2 : BitVec 20),
    .BLTU .x5 .x18 (brOff (GuestAddrs.account_writes_apply_deletes + 596) (GuestAddrs.account_writes_apply_deletes + 40)),
    .LI .x9 (0 : Word),
    .BGEU .x9 .x18 (brOff (GuestAddrs.account_writes_apply_deletes + 588) (GuestAddrs.account_writes_apply_deletes + 48)),
    .SLLI .x5 .x9 (5 : BitVec 6),
    .AUIPC .x6 (laHi GuestAddrs.account_state_delete (GuestAddrs.account_writes_apply_deletes + 56)),
    .ADDI .x6 .x6 (laLo GuestAddrs.account_state_delete (GuestAddrs.account_writes_apply_deletes + 56)),
    .ADD .x8 .x6 .x5,
    .LD .x5 .x8 (24 : BitVec 12),
    .BEQ .x5 .x0 (brOff (GuestAddrs.account_writes_apply_deletes + 580) (GuestAddrs.account_writes_apply_deletes + 72)),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_apply_deletes + 76)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_apply_deletes + 76)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (4 : BitVec 20),
    .BLTU .x7 .x6 (brOff (GuestAddrs.account_writes_apply_deletes + 596) (GuestAddrs.account_writes_apply_deletes + 92)),
    .LI .x19 (0 : Word),
    .BGEU .x19 .x6 (brOff (GuestAddrs.account_writes_apply_deletes + 512) (GuestAddrs.account_writes_apply_deletes + 100)),
    .SLLI .x7 .x19 (7 : BitVec 6),
    .LUI .x28 (1 : BitVec 20),
    .ADDIW .x28 .x28 (2031 : BitVec 12),
    .SLLI .x28 .x28 (19 : BitVec 6),
    .ADD .x7 .x28 .x7,
    .MV .x28 .x7,
    .MV .x29 .x8,
    .LI .x30 (20 : Word),
    .BEQ .x30 .x0 (40 : BitVec 13),
    .LBU .x31 .x28 (0 : BitVec 12),
    .LBU .x10 .x29 (0 : BitVec 12),
    .BNE .x31 .x10 (20 : BitVec 13),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_apply_deletes + 100) (GuestAddrs.account_writes_apply_deletes + 172)),
    .MV .x15 .x19,
    .LI .x16 (0 : Word),
    .JAL .x1 (jalOff GuestAddrs.account_writes_undo_push (GuestAddrs.account_writes_apply_deletes + 184)),
    .BNE .x10 .x0 (brOff (GuestAddrs.account_writes_apply_deletes + 596) (GuestAddrs.account_writes_apply_deletes + 188)),
    .SLLI .x5 .x19 (7 : BitVec 6),
    .LUI .x6 (1 : BitVec 20),
    .ADDIW .x6 .x6 (2031 : BitVec 12),
    .SLLI .x6 .x6 (19 : BitVec 6),
    .ADD .x5 .x6 .x5,
    .SD .x5 .x0 (64 : BitVec 12),
    .SD .x5 .x0 (80 : BitVec 12),
    .SD .x5 .x0 (88 : BitVec 12),
    .SD .x5 .x0 (96 : BitVec 12),
    .SD .x5 .x0 (104 : BitVec 12),
    .LD .x6 .x5 (32 : BitVec 12),
    .LD .x7 .x5 (40 : BitVec 12),
    .OR .x6 .x6 .x7,
    .LD .x7 .x5 (48 : BitVec 12),
    .OR .x6 .x6 .x7,
    .LD .x7 .x5 (56 : BitVec 12),
    .OR .x6 .x6 .x7,
    .BNE .x6 .x0 (brOff (GuestAddrs.account_writes_apply_deletes + 488) (GuestAddrs.account_writes_apply_deletes + 260)),
    .LD .x6 .x5 (112 : BitVec 12),
    .ANDI .x6 .x6 (1 : BitVec 12),
    .BNE .x6 .x0 (brOff (GuestAddrs.account_writes_apply_deletes + 448) (GuestAddrs.account_writes_apply_deletes + 272)),
    .SD .x2 .x0 (40 : BitVec 12),
    .SD .x2 .x0 (48 : BitVec 12),
    .SD .x2 .x0 (56 : BitVec 12),
    .SD .x2 .x0 (64 : BitVec 12),
    .SD .x2 .x0 (72 : BitVec 12),
    .MV .x10 .x8,
    .ADDI .x11 .x2 (40 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.account_writes_apply_deletes + 304)),
    .ADDI .x6 .x6 (laLo GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.account_writes_apply_deletes + 304)),
    .LD .x12 .x6 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.sv_pre_rlp_len (GuestAddrs.account_writes_apply_deletes + 316)),
    .ADDI .x6 .x6 (laLo GuestAddrs.sv_pre_rlp_len (GuestAddrs.account_writes_apply_deletes + 316)),
    .LD .x13 .x6 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bv_witness_state_ptr (GuestAddrs.account_writes_apply_deletes + 328)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bv_witness_state_ptr (GuestAddrs.account_writes_apply_deletes + 328)),
    .LD .x14 .x6 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bv_witness_state_len (GuestAddrs.account_writes_apply_deletes + 340)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bv_witness_state_len (GuestAddrs.account_writes_apply_deletes + 340)),
    .LD .x15 .x6 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.account_resolve_pre_state (GuestAddrs.account_writes_apply_deletes + 352)),
    .BNE .x10 .x0 (brOff (GuestAddrs.account_writes_apply_deletes + 596) (GuestAddrs.account_writes_apply_deletes + 356)),
    .LD .x6 .x2 (48 : BitVec 12),
    .LD .x7 .x2 (56 : BitVec 12),
    .OR .x6 .x6 .x7,
    .LD .x7 .x2 (64 : BitVec 12),
    .OR .x6 .x6 .x7,
    .LD .x7 .x2 (72 : BitVec 12),
    .OR .x6 .x6 .x7,
    .BEQ .x6 .x0 (60 : BitVec 13),
    .SLLI .x5 .x19 (7 : BitVec 6),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (2031 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .ADD .x5 .x7 .x5,
    .LD .x6 .x2 (48 : BitVec 12),
    .SD .x5 .x6 (32 : BitVec 12),
    .LD .x6 .x2 (56 : BitVec 12),
    .SD .x5 .x6 (40 : BitVec 12),
    .LD .x6 .x2 (64 : BitVec 12),
    .SD .x5 .x6 (48 : BitVec 12),
    .LD .x6 .x2 (72 : BitVec 12),
    .SD .x5 .x6 (56 : BitVec 12),
    .JAL .x0 (44 : BitVec 21),
    .SLLI .x5 .x19 (7 : BitVec 6),
    .LUI .x6 (1 : BitVec 20),
    .ADDIW .x6 .x6 (2031 : BitVec 12),
    .SLLI .x6 .x6 (19 : BitVec 6),
    .ADD .x5 .x6 .x5,
    .SD .x5 .x0 (72 : BitVec 12),
    .LI .x6 (15 : Word),
    .SD .x5 .x6 (112 : BitVec 12),
    .SD .x5 .x0 (120 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_apply_deletes + 580) (GuestAddrs.account_writes_apply_deletes + 484)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (72 : BitVec 12),
    .LI .x6 (15 : Word),
    .SD .x5 .x6 (112 : BitVec 12),
    .SD .x5 .x0 (120 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_apply_deletes + 580) (GuestAddrs.account_writes_apply_deletes + 508)),
    .SD .x2 .x0 (40 : BitVec 12),
    .SD .x2 .x0 (48 : BitVec 12),
    .SD .x2 .x0 (56 : BitVec 12),
    .SD .x2 .x0 (64 : BitVec 12),
    .MV .x10 .x8,
    .ADDI .x11 .x2 (40 : BitVec 12),
    .LI .x12 (0 : Word),
    .LI .x13 (0 : Word),
    .LI .x14 (0 : Word),
    .LI .x15 (0 : Word),
    .LI .x16 (15 : Word),
    .LI .x17 (0 : Word),
    .JAL .x1 (jalOff GuestAddrs.account_write_record (GuestAddrs.account_writes_apply_deletes + 560)),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_writes_overflow (GuestAddrs.account_writes_apply_deletes + 564)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_writes_overflow (GuestAddrs.account_writes_apply_deletes + 564)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BNE .x5 .x0 (20 : BitVec 13),
    .ADDI .x9 .x9 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_apply_deletes + 48) (GuestAddrs.account_writes_apply_deletes + 584)),
    .LI .x10 (0 : Word),
    .JAL .x0 (36 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_writes_overflow (GuestAddrs.account_writes_apply_deletes + 596)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_writes_overflow (GuestAddrs.account_writes_apply_deletes + 596)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_overflow (GuestAddrs.account_writes_apply_deletes + 612)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_overflow (GuestAddrs.account_writes_apply_deletes + 612)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountWritesApplyDeletes_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWritesApplyDeletes_relocs : RelocTable :=
  [ (6, .la .x5 "account_state_delete_count"),
    (14, .la .x6 "account_state_delete"),
    (19, .la .x5 "tx_account_writes_count"),
    (46, .jal .x1 "account_writes_undo_push"),
    (76, .la .x6 "sv_pre_rlp_ptr"),
    (79, .la .x6 "sv_pre_rlp_len"),
    (82, .la .x6 "bv_witness_state_ptr"),
    (85, .la .x6 "bv_witness_state_len"),
    (88, .jal .x1 "account_resolve_pre_state"),
    (140, .jal .x1 "account_write_record"),
    (141, .la .x5 "tx_account_writes_overflow"),
    (149, .la .x5 "tx_account_writes_overflow"),
    (153, .la .x5 "account_writes_overflow") ]

def accountWritesApplyDeletesFunction : String :=
  "account_writes_apply_deletes:\n" ++ emitProgramR accountWritesApplyDeletes_prog accountWritesApplyDeletes_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWritesApplyDeletes_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWritesApplyDeletesFunction_eq_prog :
    accountWritesApplyDeletesFunction = "account_writes_apply_deletes:\n" ++ emitProgramR accountWritesApplyDeletes_prog accountWritesApplyDeletes_relocs := rfl

#guard accountWritesApplyDeletesFunction.startsWith "account_writes_apply_deletes:\n"
#guard accountWritesApplyDeletes_prog.length = 164
/-! ## `account_writes_incorporate_tx`

    Mirrors the account half of `incorporate_tx_into_block`: merge the
    transaction level into the block level (`state_tracker.py:864-865`), then
    **CLEAR** the transaction level (`:874`).

    The clear is load-bearing. A merge without a clear double-counts across
    transactions, so transaction 2 would re-promote transaction 1's writes. A
    single-transaction smoke test cannot observe this — there is no second
    transaction to double-count into — which is why the storage-side equivalent
    shipped with a defect that only a multi-tx fixture caught. Verified on a
    multi-tx fixture, not inferred.

    Ordering note for the NEXT slice: the spec calls `update_builder_from_tx`
    **before** this merge, because the BAL comparison baseline is the block's
    *pre-merge* cumulative value. Emitting changes after the merge would compare
    a value against itself and record nothing. The emission therefore has to be
    inserted ahead of the merge loop, not appended to it.

    No arguments; no result register. -/

/-! ## `account_writes_emit_builder_tx`

    The guest's transaction-boundary realization of
    `update_builder_from_tx`.  It reads the transaction map *before* its
    incorporation into the block map, because the block map is the spec's
    pre-transaction baseline.  A block-map miss (or a hit whose fieldwise
    overlay lacks the requested component) falls back to the authenticated
    parent-state account; absence expands to `(balance, nonce, code_hash) =
    (0, 0, EMPTY_CODE_HASH)`, not an all-zero code hash.

    The map has one final row per address by its keyed upsert, so this loop
    inherits one builder decision per `(address, block_access_index)` without
    a second search/dedup stage.  The valid mask means only "producer touched
    this component"; equality against the baseline, not the mask, decides
    whether the builder receives an event.

    No arguments.  BAI comes from `current_block_access_index`, maintained as
    `bv_mtx_i + 1` by the multi-tx loop. -/
def accountWritesEmitBuilderTx_prog : Program :=
  [ .ADDI .x2 .x2 (-112 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.current_block_access_index (GuestAddrs.account_writes_emit_builder_tx + 44)),
    .ADDI .x5 .x5 (laLo GuestAddrs.current_block_access_index (GuestAddrs.account_writes_emit_builder_tx + 44)),
    .LD .x23 .x5 (0 : BitVec 12),
    .AUIPC .x8 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_emit_builder_tx + 56)),
    .ADDI .x8 .x8 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_emit_builder_tx + 56)),
    .LD .x9 .x8 (0 : BitVec 12),
    .LUI .x18 (1 : BitVec 20),
    .ADDIW .x18 .x18 (2031 : BitVec 12),
    .SLLI .x18 .x18 (19 : BitVec 6),
    .LI .x19 (0 : Word),
    .BGEU .x19 .x9 (brOff (GuestAddrs.account_writes_emit_builder_tx + 1236) (GuestAddrs.account_writes_emit_builder_tx + 84)),
    .SLLI .x5 .x19 (7 : BitVec 6),
    .ADD .x20 .x18 .x5,
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.account_writes_emit_builder_tx + 96)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.account_writes_emit_builder_tx + 96)),
    .LD .x6 .x5 (0 : BitVec 12),
    -- Block-tier scan base for the BAL emit gate (GH #12616).  The writer
    -- emits at ACCOUNT_WRITES_AREA; the stale 0xbdb80000 reconstruction here
    -- missed every block-tier record, degenerating the cross-tx code
    -- comparison to start-of-block pre-state and dropping delegation-clear
    -- code_changes entries (false reject on 3/26104 full-corpus rows).
    -- Derive the base from the layout constant (encoding guards at the
    -- accountResolvePreState block below), keeping the three-instruction
    -- shape so linked offsets stay stable.
    .LUI .x7 (((EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) >>> 12) : BitVec 20),
    .ADDIW .x7 .x7 (((EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat >>> 12) % 4096) : BitVec 12),
    .SLLI .x7 .x7 (12 : BitVec 6),
    .LI .x28 (0 : Word),
    .LI .x21 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_writes_emit_builder_tx + 200) (GuestAddrs.account_writes_emit_builder_tx + 128)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .LI .x31 (20 : Word),
    .MV .x10 .x30,
    .MV .x11 .x20,
    .BEQ .x31 .x0 (40 : BitVec 13),
    .LBU .x12 .x10 (0 : BitVec 12),
    .LBU .x13 .x11 (0 : BitVec 12),
    .BNE .x12 .x13 (20 : BitVec 13),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .MV .x21 .x30,
    .JAL .x0 (4 : BitVec 21),
    .BNE .x21 .x0 (4 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.account_writes_emit_builder_tx + 204)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.account_writes_emit_builder_tx + 204)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_len (GuestAddrs.account_writes_emit_builder_tx + 216)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_len (GuestAddrs.account_writes_emit_builder_tx + 216)),
    .LD .x11 .x5 (0 : BitVec 12),
    .MV .x12 .x20,
    .LI .x13 (20 : Word),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_ptr (GuestAddrs.account_writes_emit_builder_tx + 236)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_ptr (GuestAddrs.account_writes_emit_builder_tx + 236)),
    .LD .x14 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_len (GuestAddrs.account_writes_emit_builder_tx + 248)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_len (GuestAddrs.account_writes_emit_builder_tx + 248)),
    .LD .x15 .x5 (0 : BitVec 12),
    .AUIPC .x16 (laHi GuestAddrs.account_builder_pre_account (GuestAddrs.account_writes_emit_builder_tx + 260)),
    .ADDI .x16 .x16 (laLo GuestAddrs.account_builder_pre_account (GuestAddrs.account_writes_emit_builder_tx + 260)),
    .JAL .x1 (jalOff GuestAddrs.account_at_header_state_root (GuestAddrs.account_writes_emit_builder_tx + 268)),
    .SD .x2 .x10 (80 : BitVec 12),
    .MV .x10 .x20,
    .AUIPC .x11 (laHi GuestAddrs.account_builder_pre_account (GuestAddrs.account_writes_emit_builder_tx + 280)),
    .ADDI .x11 .x11 (laLo GuestAddrs.account_builder_pre_account (GuestAddrs.account_writes_emit_builder_tx + 280)),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.account_writes_emit_builder_tx + 288)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.account_writes_emit_builder_tx + 288)),
    .LD .x12 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_len (GuestAddrs.account_writes_emit_builder_tx + 300)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_len (GuestAddrs.account_writes_emit_builder_tx + 300)),
    .LD .x13 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_ptr (GuestAddrs.account_writes_emit_builder_tx + 312)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_ptr (GuestAddrs.account_writes_emit_builder_tx + 312)),
    .LD .x14 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_len (GuestAddrs.account_writes_emit_builder_tx + 324)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_len (GuestAddrs.account_writes_emit_builder_tx + 324)),
    .LD .x15 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.account_resolve_pre_state (GuestAddrs.account_writes_emit_builder_tx + 336)),
    .LD .x24 .x20 (112 : BitVec 12),
    .ANDI .x5 .x24 (1 : BitVec 12),
    .BNE .x5 .x0 (8 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_emit_builder_tx + 768) (GuestAddrs.account_writes_emit_builder_tx + 352)),
    .AUIPC .x5 (laHi GuestAddrs.bald_bal_bit_set (GuestAddrs.account_writes_emit_builder_tx + 356)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_bal_bit_set (GuestAddrs.account_writes_emit_builder_tx + 356)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x22 (laHi GuestAddrs.account_builder_pre_account (GuestAddrs.account_writes_emit_builder_tx + 376)),
    .ADDI .x22 .x22 (laLo GuestAddrs.account_builder_pre_account (GuestAddrs.account_writes_emit_builder_tx + 376)),
    .ADDI .x22 .x22 (8 : BitVec 12),
    .LD .x5 .x22 (0 : BitVec 12),
    .LD .x6 .x20 (32 : BitVec 12),
    .BNE .x5 .x6 (brOff (GuestAddrs.account_writes_emit_builder_tx + 608) (GuestAddrs.account_writes_emit_builder_tx + 396)),
    .LD .x5 .x22 (8 : BitVec 12),
    .LD .x6 .x20 (40 : BitVec 12),
    .BNE .x5 .x6 (brOff (GuestAddrs.account_writes_emit_builder_tx + 608) (GuestAddrs.account_writes_emit_builder_tx + 408)),
    .LD .x5 .x22 (16 : BitVec 12),
    .LD .x6 .x20 (48 : BitVec 12),
    .BNE .x5 .x6 (brOff (GuestAddrs.account_writes_emit_builder_tx + 608) (GuestAddrs.account_writes_emit_builder_tx + 420)),
    .LD .x5 .x22 (24 : BitVec 12),
    .LD .x6 .x20 (56 : BitVec 12),
    .BEQ .x5 .x6 (brOff (GuestAddrs.account_writes_emit_builder_tx + 676) (GuestAddrs.account_writes_emit_builder_tx + 432)),
    .LI .x5 (4 : Word),
    .BGEU .x19 .x5 (brOff (GuestAddrs.account_writes_emit_builder_tx + 560) (GuestAddrs.account_writes_emit_builder_tx + 440)),
    .LI .x5 (96 : Word),
    .MUL .x5 .x19 .x5,
    .AUIPC .x6 (laHi GuestAddrs.account_builder_diag_balance_pairs (GuestAddrs.account_writes_emit_builder_tx + 452)),
    .ADDI .x6 .x6 (laLo GuestAddrs.account_builder_diag_balance_pairs (GuestAddrs.account_writes_emit_builder_tx + 452)),
    .ADD .x6 .x6 .x5,
    .LD .x5 .x20 (0 : BitVec 12),
    .SD .x6 .x5 (0 : BitVec 12),
    .LD .x5 .x20 (8 : BitVec 12),
    .SD .x6 .x5 (8 : BitVec 12),
    .LD .x5 .x20 (16 : BitVec 12),
    .SD .x6 .x5 (16 : BitVec 12),
    .LD .x5 .x20 (24 : BitVec 12),
    .SD .x6 .x5 (24 : BitVec 12),
    .LD .x5 .x22 (0 : BitVec 12),
    .SD .x6 .x5 (32 : BitVec 12),
    .LD .x5 .x22 (8 : BitVec 12),
    .SD .x6 .x5 (40 : BitVec 12),
    .LD .x5 .x22 (16 : BitVec 12),
    .SD .x6 .x5 (48 : BitVec 12),
    .LD .x5 .x22 (24 : BitVec 12),
    .SD .x6 .x5 (56 : BitVec 12),
    .LD .x5 .x20 (32 : BitVec 12),
    .SD .x6 .x5 (64 : BitVec 12),
    .LD .x5 .x20 (40 : BitVec 12),
    .SD .x6 .x5 (72 : BitVec 12),
    .LD .x5 .x20 (48 : BitVec 12),
    .SD .x6 .x5 (80 : BitVec 12),
    .LD .x5 .x20 (56 : BitVec 12),
    .SD .x6 .x5 (88 : BitVec 12),
    .LD .x5 .x22 (0 : BitVec 12),
    .LD .x6 .x20 (32 : BitVec 12),
    .BNE .x5 .x6 (40 : BitVec 13),
    .LD .x5 .x22 (8 : BitVec 12),
    .LD .x6 .x20 (40 : BitVec 12),
    .BNE .x5 .x6 (28 : BitVec 13),
    .LD .x5 .x22 (16 : BitVec 12),
    .LD .x6 .x20 (48 : BitVec 12),
    .BNE .x5 .x6 (16 : BitVec 13),
    .LD .x5 .x22 (24 : BitVec 12),
    .LD .x6 .x20 (56 : BitVec 12),
    .BEQ .x5 .x6 (brOff (GuestAddrs.account_writes_emit_builder_tx + 768) (GuestAddrs.account_writes_emit_builder_tx + 604)),
    .AUIPC .x5 (laHi GuestAddrs.bald_bal_differs (GuestAddrs.account_writes_emit_builder_tx + 608)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_bal_differs (GuestAddrs.account_writes_emit_builder_tx + 608)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bald_bal_ne_bai_mask (GuestAddrs.account_writes_emit_builder_tx + 628)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_bal_ne_bai_mask (GuestAddrs.account_writes_emit_builder_tx + 628)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (1 : Word),
    .SLL .x7 .x7 .x23,
    .OR .x6 .x6 .x7,
    .SD .x5 .x6 (0 : BitVec 12),
    .MV .x10 .x20,
    .MV .x11 .x23,
    .ADDI .x12 .x20 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_builder_append_balance (GuestAddrs.account_writes_emit_builder_tx + 668)),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_emit_builder_tx + 768) (GuestAddrs.account_writes_emit_builder_tx + 672)),
    .AUIPC .x5 (laHi GuestAddrs.bald_bal_eq_bai_mask (GuestAddrs.account_writes_emit_builder_tx + 676)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_bal_eq_bai_mask (GuestAddrs.account_writes_emit_builder_tx + 676)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (1 : Word),
    .SLL .x7 .x7 .x23,
    .OR .x6 .x6 .x7,
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x6 .x22 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bald_bal_eq_val_lo (GuestAddrs.account_writes_emit_builder_tx + 708)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_bal_eq_val_lo (GuestAddrs.account_writes_emit_builder_tx + 708)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x6 .x22 (24 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bald_bal_eq_val_hi (GuestAddrs.account_writes_emit_builder_tx + 724)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_bal_eq_val_hi (GuestAddrs.account_writes_emit_builder_tx + 724)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x6 .x20 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bald_bal_eq_addr_a (GuestAddrs.account_writes_emit_builder_tx + 740)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_bal_eq_addr_a (GuestAddrs.account_writes_emit_builder_tx + 740)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x6 .x20 (8 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bald_bal_eq_addr_b (GuestAddrs.account_writes_emit_builder_tx + 756)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_bal_eq_addr_b (GuestAddrs.account_writes_emit_builder_tx + 756)),
    .SD .x5 .x6 (0 : BitVec 12),
    .ANDI .x5 .x24 (2 : BitVec 12),
    .BNE .x5 .x0 (8 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_emit_builder_tx + 1036) (GuestAddrs.account_writes_emit_builder_tx + 776)),
    .AUIPC .x5 (laHi GuestAddrs.bald_non_bit_set (GuestAddrs.account_writes_emit_builder_tx + 780)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_non_bit_set (GuestAddrs.account_writes_emit_builder_tx + 780)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.account_builder_pre_account (GuestAddrs.account_writes_emit_builder_tx + 800)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_builder_pre_account (GuestAddrs.account_writes_emit_builder_tx + 800)),
    .LD .x5 .x5 (0 : BitVec 12),
    .LD .x6 .x20 (64 : BitVec 12),
    .BEQ .x5 .x6 (brOff (GuestAddrs.account_writes_emit_builder_tx + 888) (GuestAddrs.account_writes_emit_builder_tx + 816)),
    .AUIPC .x30 (laHi GuestAddrs.bald_non_differs (GuestAddrs.account_writes_emit_builder_tx + 820)),
    .ADDI .x30 .x30 (laLo GuestAddrs.bald_non_differs (GuestAddrs.account_writes_emit_builder_tx + 820)),
    .LD .x31 .x30 (0 : BitVec 12),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .SD .x30 .x31 (0 : BitVec 12),
    .AUIPC .x30 (laHi GuestAddrs.bald_non_ne_bai_mask (GuestAddrs.account_writes_emit_builder_tx + 840)),
    .ADDI .x30 .x30 (laLo GuestAddrs.bald_non_ne_bai_mask (GuestAddrs.account_writes_emit_builder_tx + 840)),
    .LD .x31 .x30 (0 : BitVec 12),
    .LI .x28 (1 : Word),
    .SLL .x28 .x28 .x23,
    .OR .x31 .x31 .x28,
    .SD .x30 .x31 (0 : BitVec 12),
    .MV .x10 .x20,
    .MV .x11 .x23,
    .MV .x12 .x6,
    .JAL .x1 (jalOff GuestAddrs.bal_builder_append_nonce (GuestAddrs.account_writes_emit_builder_tx + 880)),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_emit_builder_tx + 1036) (GuestAddrs.account_writes_emit_builder_tx + 884)),
    .AUIPC .x7 (laHi GuestAddrs.bald_non_eq_bai_mask (GuestAddrs.account_writes_emit_builder_tx + 888)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bald_non_eq_bai_mask (GuestAddrs.account_writes_emit_builder_tx + 888)),
    .LD .x28 .x7 (0 : BitVec 12),
    .LI .x29 (1 : Word),
    .SLL .x29 .x29 .x23,
    .OR .x28 .x28 .x29,
    .SD .x7 .x28 (0 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.bald_non_eq_val_pre (GuestAddrs.account_writes_emit_builder_tx + 916)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bald_non_eq_val_pre (GuestAddrs.account_writes_emit_builder_tx + 916)),
    .SD .x7 .x5 (0 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.bald_non_eq_val_post (GuestAddrs.account_writes_emit_builder_tx + 928)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bald_non_eq_val_post (GuestAddrs.account_writes_emit_builder_tx + 928)),
    .SD .x7 .x6 (0 : BitVec 12),
    .LI .x7 (4 : Word),
    .BGEU .x19 .x7 (brOff (GuestAddrs.account_writes_emit_builder_tx + 1012) (GuestAddrs.account_writes_emit_builder_tx + 944)),
    .LI .x7 (48 : Word),
    .MUL .x7 .x19 .x7,
    .AUIPC .x28 (laHi GuestAddrs.account_builder_diag_nonce_pairs (GuestAddrs.account_writes_emit_builder_tx + 956)),
    .ADDI .x28 .x28 (laLo GuestAddrs.account_builder_diag_nonce_pairs (GuestAddrs.account_writes_emit_builder_tx + 956)),
    .ADD .x28 .x28 .x7,
    .LD .x7 .x20 (0 : BitVec 12),
    .SD .x28 .x7 (0 : BitVec 12),
    .LD .x7 .x20 (8 : BitVec 12),
    .SD .x28 .x7 (8 : BitVec 12),
    .LD .x7 .x20 (16 : BitVec 12),
    .SD .x28 .x7 (16 : BitVec 12),
    .LD .x7 .x20 (24 : BitVec 12),
    .SD .x28 .x7 (24 : BitVec 12),
    .SD .x28 .x5 (32 : BitVec 12),
    .LD .x7 .x20 (64 : BitVec 12),
    .SD .x28 .x7 (40 : BitVec 12),
    .LD .x6 .x20 (64 : BitVec 12),
    .BEQ .x5 .x6 (20 : BitVec 13),
    .MV .x10 .x20,
    .MV .x11 .x23,
    .MV .x12 .x6,
    .JAL .x1 (jalOff GuestAddrs.bal_builder_append_nonce (GuestAddrs.account_writes_emit_builder_tx + 1032)),
    .ANDI .x5 .x24 (4 : BitVec 12),
    .BNE .x5 .x0 (8 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_emit_builder_tx + 1228) (GuestAddrs.account_writes_emit_builder_tx + 1044)),
    .LD .x10 .x20 (80 : BitVec 12),
    .LD .x11 .x20 (88 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.account_builder_post_code_hash (GuestAddrs.account_writes_emit_builder_tx + 1056)),
    .ADDI .x12 .x12 (laLo GuestAddrs.account_builder_post_code_hash (GuestAddrs.account_writes_emit_builder_tx + 1056)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.account_writes_emit_builder_tx + 1064)),
    .BEQ .x21 .x0 (48 : BitVec 13),
    .LD .x5 .x21 (112 : BitVec 12),
    .ANDI .x5 .x5 (4 : BitVec 12),
    .BEQ .x5 .x0 (36 : BitVec 13),
    .LD .x10 .x21 (80 : BitVec 12),
    .LD .x11 .x21 (88 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.account_builder_block_code_hash (GuestAddrs.account_writes_emit_builder_tx + 1092)),
    .ADDI .x12 .x12 (laLo GuestAddrs.account_builder_block_code_hash (GuestAddrs.account_writes_emit_builder_tx + 1092)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.account_writes_emit_builder_tx + 1100)),
    .AUIPC .x22 (laHi GuestAddrs.account_builder_block_code_hash (GuestAddrs.account_writes_emit_builder_tx + 1104)),
    .ADDI .x22 .x22 (laLo GuestAddrs.account_builder_block_code_hash (GuestAddrs.account_writes_emit_builder_tx + 1104)),
    .JAL .x0 (40 : BitVec 21),
    .LD .x5 .x2 (80 : BitVec 12),
    .LI .x6 (1 : Word),
    .BEQ .x5 .x6 (20 : BitVec 13),
    .AUIPC .x22 (laHi GuestAddrs.account_builder_pre_account (GuestAddrs.account_writes_emit_builder_tx + 1128)),
    .ADDI .x22 .x22 (laLo GuestAddrs.account_builder_pre_account (GuestAddrs.account_writes_emit_builder_tx + 1128)),
    .ADDI .x22 .x22 (72 : BitVec 12),
    .JAL .x0 (12 : BitVec 21),
    .AUIPC .x22 (laHi GuestAddrs.chahsr_empty_code_hash (GuestAddrs.account_writes_emit_builder_tx + 1144)),
    .ADDI .x22 .x22 (laLo GuestAddrs.chahsr_empty_code_hash (GuestAddrs.account_writes_emit_builder_tx + 1144)),
    .AUIPC .x5 (laHi GuestAddrs.account_builder_post_code_hash (GuestAddrs.account_writes_emit_builder_tx + 1152)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_builder_post_code_hash (GuestAddrs.account_writes_emit_builder_tx + 1152)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LD .x7 .x22 (0 : BitVec 12),
    .BNE .x6 .x7 (40 : BitVec 13),
    .LD .x6 .x5 (8 : BitVec 12),
    .LD .x7 .x22 (8 : BitVec 12),
    .BNE .x6 .x7 (28 : BitVec 13),
    .LD .x6 .x5 (16 : BitVec 12),
    .LD .x7 .x22 (16 : BitVec 12),
    .BNE .x6 .x7 (16 : BitVec 13),
    .LD .x6 .x5 (24 : BitVec 12),
    .LD .x7 .x22 (24 : BitVec 12),
    .BEQ .x6 .x7 (24 : BitVec 13),
    .MV .x10 .x20,
    .MV .x11 .x23,
    .LD .x12 .x20 (80 : BitVec 12),
    .LD .x13 .x20 (88 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_builder_append_code (GuestAddrs.account_writes_emit_builder_tx + 1224)),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_emit_builder_tx + 84) (GuestAddrs.account_writes_emit_builder_tx + 1232)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .ADDI .x2 .x2 (112 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountWritesEmitBuilderTx_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWritesEmitBuilderTx_relocs : RelocTable :=
  [ (11, .la .x5 "current_block_access_index"),
    (14, .la .x8 "tx_account_writes_count"),
    (24, .la .x5 "account_writes_count"),
    (51, .la .x5 "sv_pre_rlp_ptr"),
    (54, .la .x5 "sv_pre_rlp_len"),
    (59, .la .x5 "bv_witness_state_ptr"),
    (62, .la .x5 "bv_witness_state_len"),
    (65, .la .x16 "account_builder_pre_account"),
    (67, .jal .x1 "account_at_header_state_root"),
    (70, .la .x11 "account_builder_pre_account"),
    (72, .la .x5 "sv_pre_rlp_ptr"),
    (75, .la .x5 "sv_pre_rlp_len"),
    (78, .la .x5 "bv_witness_state_ptr"),
    (81, .la .x5 "bv_witness_state_len"),
    (84, .jal .x1 "account_resolve_pre_state"),
    (89, .la .x5 "bald_bal_bit_set"),
    (94, .la .x22 "account_builder_pre_account"),
    (113, .la .x6 "account_builder_diag_balance_pairs"),
    (152, .la .x5 "bald_bal_differs"),
    (157, .la .x5 "bald_bal_ne_bai_mask"),
    (167, .jal .x1 "bal_builder_append_balance"),
    (169, .la .x5 "bald_bal_eq_bai_mask"),
    (177, .la .x5 "bald_bal_eq_val_lo"),
    (181, .la .x5 "bald_bal_eq_val_hi"),
    (185, .la .x5 "bald_bal_eq_addr_a"),
    (189, .la .x5 "bald_bal_eq_addr_b"),
    (195, .la .x5 "bald_non_bit_set"),
    (200, .la .x5 "account_builder_pre_account"),
    (205, .la .x30 "bald_non_differs"),
    (210, .la .x30 "bald_non_ne_bai_mask"),
    (220, .jal .x1 "bal_builder_append_nonce"),
    (222, .la .x7 "bald_non_eq_bai_mask"),
    (229, .la .x7 "bald_non_eq_val_pre"),
    (232, .la .x7 "bald_non_eq_val_post"),
    (239, .la .x28 "account_builder_diag_nonce_pairs"),
    (258, .jal .x1 "bal_builder_append_nonce"),
    (264, .la .x12 "account_builder_post_code_hash"),
    (266, .jal .x1 "zkvm_keccak256"),
    (273, .la .x12 "account_builder_block_code_hash"),
    (275, .jal .x1 "zkvm_keccak256"),
    (276, .la .x22 "account_builder_block_code_hash"),
    (282, .la .x22 "account_builder_pre_account"),
    (286, .la .x22 "chahsr_empty_code_hash"),
    (288, .la .x5 "account_builder_post_code_hash"),
    (306, .jal .x1 "bal_builder_append_code") ]

def accountWritesEmitBuilderTxFunction : String :=
  "account_writes_emit_builder_tx:\n" ++ emitProgramR accountWritesEmitBuilderTx_prog accountWritesEmitBuilderTx_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWritesEmitBuilderTx_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWritesEmitBuilderTxFunction_eq_prog :
    accountWritesEmitBuilderTxFunction = "account_writes_emit_builder_tx:\n" ++ emitProgramR accountWritesEmitBuilderTx_prog accountWritesEmitBuilderTx_relocs := rfl

#guard accountWritesEmitBuilderTxFunction.startsWith "account_writes_emit_builder_tx:\n"
#guard accountWritesEmitBuilderTx_prog.length = 321
def accountWritesIncorporateTx_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .AUIPC .x8 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_incorporate_tx + 24)),
    .ADDI .x8 .x8 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_incorporate_tx + 24)),
    .LD .x9 .x8 (0 : BitVec 12),
    .LUI .x18 (1 : BitVec 20),
    .ADDIW .x18 .x18 (2031 : BitVec 12),
    .SLLI .x18 .x18 (19 : BitVec 6),
    .LI .x19 (0 : Word),
    .BGEU .x19 .x9 (24 : BitVec 13),
    .SLLI .x10 .x19 (7 : BitVec 6),
    .ADD .x10 .x18 .x10,
    .JAL .x1 (jalOff GuestAddrs.account_writes_block_upsert (GuestAddrs.account_writes_incorporate_tx + 64)),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .AUIPC .x8 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_incorporate_tx + 76)),
    .ADDI .x8 .x8 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_incorporate_tx + 76)),
    .SD .x8 .x0 (0 : BitVec 12),
    .AUIPC .x8 (laHi GuestAddrs.tx_account_writes_overflow (GuestAddrs.account_writes_incorporate_tx + 88)),
    .ADDI .x8 .x8 (laLo GuestAddrs.tx_account_writes_overflow (GuestAddrs.account_writes_incorporate_tx + 88)),
    .SD .x8 .x0 (0 : BitVec 12),
    .AUIPC .x8 (laHi GuestAddrs.account_writes_undo_count (GuestAddrs.account_writes_incorporate_tx + 100)),
    .ADDI .x8 .x8 (laLo GuestAddrs.account_writes_undo_count (GuestAddrs.account_writes_incorporate_tx + 100)),
    .SD .x8 .x0 (0 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountWritesIncorporateTx_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWritesIncorporateTx_relocs : RelocTable :=
  [ (6, .la .x8 "tx_account_writes_count"),
    (16, .jal .x1 "account_writes_block_upsert"),
    (19, .la .x8 "tx_account_writes_count"),
    (22, .la .x8 "tx_account_writes_overflow"),
    (25, .la .x8 "account_writes_undo_count") ]

def accountWritesIncorporateTxFunction : String :=
  "account_writes_incorporate_tx:\n" ++ emitProgramR accountWritesIncorporateTx_prog accountWritesIncorporateTx_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWritesIncorporateTx_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWritesIncorporateTxFunction_eq_prog :
    accountWritesIncorporateTxFunction = "account_writes_incorporate_tx:\n" ++ emitProgramR accountWritesIncorporateTx_prog accountWritesIncorporateTx_relocs := rfl

#guard accountWritesIncorporateTxFunction.startsWith "account_writes_incorporate_tx:\n"
#guard accountWritesIncorporateTx_prog.length = 35
/-! ## `account_writes_discard_tx` — REMOVED from guest (#11202)

    Never jal'd. Storage twin `write_sets_discard_tx` is live on status=0.
    Account path always `emit`+`incorporate` after presumed body restore.
    Issue #11202 carries the open question (benign dead twin vs missing
    fail-discard wiring). Do not resurrect without wiring a real fail path. -/

/-- Data symbols for the two `account_writes` levels and the undo journal.
    The arenas themselves are NOBITS regions declared in `MemoryLayout`; only
    the counters and flags live in `.data`. -/
def accountWriteMapDataSection : String :=
  "account_writes_count:\n  .zero 8\n" ++
  "account_writes_overflow:\n  .zero 8\n" ++
  "tx_account_writes_count:\n  .zero 8\n" ++
  "tx_account_writes_overflow:\n  .zero 8\n" ++
  accountWritesUndoDataSection

def accountAgreementDataSection : String :=
  -- The production guest carries runtime-only mutation observation inert.
  -- `scripts/spike/standing_controls_sweep.py` arms this word explicitly for
  -- measurement runs. Keep it initialized in .data; a nonzero initializer is
  -- not legal in .bss.
  ".section .data\naccount_agreement_enabled:\n  .dword 0\n"

/-- Runtime-zeroed NOBITS storage used by the account-write map. -/
def accountWriteMapBssSection : String :=
  ".section .bss, \"aw\", @nobits\n" ++
  ".balign 8\n" ++
  -- EIP-7702 authorization code is represented by a 23-byte delegation
  -- designator.  Transaction/account-write rows retain a pointer to those
  -- bytes until the later BAL builder pass, so this must be a block-lifetime
  -- NOBITS arena, not a reusable per-auth scratch.  One slot per possible
  -- authorization tuple is bounded by the regular-gas admission floor.
  "eip7702_auth_code_next:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "eip7702_auth_code_slots:\n  .zero " ++ toString (bvEip7702AuthEntryCapacity * 24) ++ "\n" ++
  -- Mark immediately before authorization preparation.  A preparation
  -- ExceptionalHalt drops accepted auth mutations but retains sender inclusion
  -- and the already-staged transaction debit; a body revert uses the later
  -- body mark and keeps the authorization phase.
  "account_writes_auth_prepare_mark:\n  .zero 8\n" ++
  -- Transaction-boundary builder-walk scratch.  This stays in BSS: it is
  -- runtime-only comparison state, and a data-section addition would shift the
  -- pinned descriptor area for no semantic benefit.
  ".balign 32\n" ++
  "account_builder_pre_account:\n  .zero 104\n" ++
  "account_builder_post_code_hash:\n  .zero 32\n" ++
  "account_builder_block_code_hash:\n  .zero 32\n" ++
  "account_builder_diag_balance_pairs:\n  .zero 384\n" ++
  "account_builder_diag_nonce_pairs:\n  .zero 192\n" ++
  ".balign 8\n" ++
  -- #11329 e2e gate scratch: fixed BE20 + balance word for touch/store/twin/undo.
  "account_write_e2e_addr:\n  .zero 32\n" ++
  "account_write_e2e_bal:\n  .zero 32\n" ++
  -- Runtime-only mutation observations retained for the verdict/control sweep.
  -- The map/overlay comparison counters and event arena were retired with the probe.
  ".balign 32\n" ++
  "account_agreement_mutation_event_count:\n  .zero 8\n" ++
  "account_agreement_mutation_event_overflow:\n  .zero 8\n" ++
  "account_agreement_mutation_events:\n  .zero " ++ toString (accountAgreementMutationEventCapacity * 96) ++ "\n"

/-! ## `account_write_touch_e2e`

    Non-negotiable first-producer gate (#11329): set execFlags+TOUCHED, store,
    second same-addr write (twin sticky), REVERT undo restore, read NON-ZERO.
    Returns via OUTPUT 0xa0010000:
      +0  mask after first write (expect bit5=32 set)
      +8  execFlags after first write (expect 0x33)
      +16 mask after twin balance-only write (expect 32 still sticky)
      +24 mask after undo restore (expect 0 — row gone / truncated)
      +32 status 0 = all checks passed, 1 = fail
    Standalone probe; not linked into stateless_guest. -/
def accountWriteTouchE2eFunction : String :=
  "account_write_touch_e2e:\n" ++
  "  addi sp, sp, -16; sd ra, 0(sp); sd s0, 8(sp)\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, account_write_e2e_addr; li t1, 20\n" ++
  ".Lawe2e_fill:\n" ++
  "  beqz t1, .Lawe2e_filled; li t2, 0xaa; sb t2, 0(t0); addi t0, t0, 1; addi t1, t1, -1; j .Lawe2e_fill\n" ++
  ".Lawe2e_filled:\n" ++
  "  la t0, tx_account_writes_count; sd zero, 0(t0)\n" ++
  "  la t0, account_writes_undo_count; sd zero, 0(t0)\n" ++
  -- 1) set TOUCHED|EXEC_FLAGS with a7=0x33
  "  la a0, account_write_e2e_addr; li a1, 0; li a2, 0; li a3, 0; li a4, 0; li a5, 0\n" ++
  "  li a6, " ++ toString (accountWriteHasTouched + accountWriteHasExecFlags) ++ "; li a7, 0x33\n" ++
  "  jal ra, account_write_record\n" ++
  "  li t3, " ++ toString EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat ++ "; lbu t0, 112(t3); sd t0, 0(s0); ld t0, 96(t3); sd t0, 8(s0)\n" ++
  -- 2) twin same-addr BALANCE-only write (no TOUCHED in mask) — sticky must keep 32
  "  la t0, account_write_e2e_bal; li t1, 7; sb t1, 31(t0)\n" ++
  "  la a0, account_write_e2e_addr; la a1, account_write_e2e_bal; li a2, 0; li a3, 0; li a4, 0; li a5, 0\n" ++
  "  li a6, " ++ toString accountWriteHasBalance ++ "; li a7, 0\n" ++
  "  jal ra, account_write_record\n" ++
  "  li t3, " ++ toString EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat ++ "; lbu t0, 112(t3); sd t0, 16(s0)\n" ++
  -- 3) undo restore to mark 0 — row must disappear (count→0, mask read as 0)
  "  li a0, 0; jal ra, account_writes_restore_frame\n" ++
  "  la t0, tx_account_writes_count; ld t0, 0(t0); sd t0, 24(s0)\n" ++
  -- status: mask1&32, flags==0x33, mask2&32, count==0
  "  li t4, 0\n" ++
  "  ld t0, 0(s0); andi t0, t0, 32; beqz t0, .Lawe2e_fail\n" ++
  "  ld t0, 8(s0); li t1, 0x33; bne t0, t1, .Lawe2e_fail\n" ++
  "  ld t0, 16(s0); andi t0, t0, 32; beqz t0, .Lawe2e_fail\n" ++
  "  ld t0, 24(s0); bnez t0, .Lawe2e_fail\n" ++
  "  j .Lawe2e_ok\n" ++
  ".Lawe2e_fail:\n" ++
  "  li t4, 1\n" ++
  ".Lawe2e_ok:\n" ++
  "  sd t4, 32(s0)\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); addi sp, sp, 16; ret\n"

/-- Every routine in this module, in emission order. `account_write_record`
    calls `account_writes_undo_push`, and `account_writes_incorporate_tx` calls
    `account_writes_block_upsert`, so the complete map helper family is emitted
    together. -/
def accountWriteMapFunctions : String :=
  -- ⚠️ Joiner discipline, now that every member joins with an explicit `"\n"`.
  -- A String-literal member ends with its own `"\n"`, so `member ++ "\n" ++ next`
  -- emits a BLANK line; an `emitProgramR` render ends at its last instruction
  -- with no trailing newline, so the same joiner emits exactly ONE newline.
  -- Transcribing a member therefore REMOVES a blank line and needs no joiner
  -- edit — which is what makes the uniform joiners above the right convention.
  -- `accountWriteRecordFunction` is a render as of this change; the members
  -- still written as String literals each carry a transient blank line until
  -- they are transcribed too. None of this moves `.text` — the assembler
  -- ignores the whitespace — so only the seam guard below observes it.
  accountWriteRecordFunction ++ "\n" ++
  accountWritesLatestBalanceFunction ++ "\n" ++
  accountWritesLatestBalanceBlockFunction ++ "\n" ++
  accountWritesLatestNonceBlockFunction ++ "\n" ++
  accountWritesLatestNonceTxFunction ++ "\n" ++
  accountWritesAuthCurrentFunction ++ "\n" ++
  accountWritesAuthBlockFunction ++ "\n" ++
  accountWritesCreatedContainsFunction ++ "\n" ++
  accountWritesLookupCurrentFunction ++ "\n" ++
  accountWritesTombstoneBalanceZeroFunction ++ "\n" ++
  accountAgreementMutationCheckpointFunction ++ "\n" ++
  accountWritesBlockUpsertFunction ++ "\n" ++
  accountWritesApplyDeletesFunction ++ "\n" ++
  accountWritesCommitPendingFunction ++ "\n" ++
  accountWritesIsAbsentFunction ++ "\n" ++
  accountWritesEmitBuilderTxFunction ++ "\n" ++
  accountWritesIncorporateTxFunction ++ "\n" ++
  accountWritesUndoPushFunction ++ "\n" ++
  accountWritesRestoreFrameFunction ++ "\n" ++
  accountResolvePreStateFunction ++ "\n" ++
  accountResolveExecutionStateFunction

/-! ## Structural guards

    `#guard`s in `EvmAsm.Codegen`, the namespace the definitions above live in --
    NOT the file path. A guard opened on the wrong namespace has its identifiers
    auto-bound as implicits and passes while checking nothing, so the layout
    constants are written FULLY QUALIFIED here rather than via `open ... in`.

    Each guard is a SINGLE LINE. A `#guard` whose expression wraps onto a second
    line parses the continuation as a new command, and the guard silently covers
    only the first line -- which is the same vacuous-pass failure one level down. -/

-- Seam pin for the first member, now that it is a rendered Program rather than
-- a String literal (see the joiner note on `accountWriteMapFunctions`). `= 2` is
-- `splitOn`'s encoding of "occurs exactly once", so it cannot pass by matching
-- nothing. This is the only check that the transcription did not swallow the
-- blank line before `account_writes_latest_balance:` -- the `.text` bytes are
-- identical either way, so byte-identity gates are blind to it.
#guard (accountWriteMapFunctions.splitOn "  jalr x0, 0(x1)\naccount_writes_latest_balance:\n").length == 2
#guard (accountWriteMapFunctions.splitOn accountWriteRecordFunction).length == 2

-- GH #11770 RELOCATION. The block map and the undo journal moved OUT of the
-- scheme-A anchor block into the gap above `.bss`, because they had to grow and
-- the space adjacent to them was 0.88 MiB. These four guards previously asserted
-- the OLD adjacency chain (storage-undo -> block map -> tx map -> undo, all
-- below `.data`); they are rewritten, not deleted, because they are the only
-- thing that would catch a careless move.
--
-- ⚠️ Worth knowing for the next relocation: these guards express adjacency as
-- BASE + SIZE arithmetic, not as a literal block-top address. Grepping for the
-- old block top (0xa2f20000) found nothing and suggested no assumption spanned
-- the block. It did -- here.

-- High pack (GH #11186): the enlarged AW/AU pair is derived from the storage
-- undo end; the transaction map remains at the fixed high base, leaving a
-- checked gap between the undo arena and the transaction map before SSZ.
-- Capacity guards fire BEFORE any store.
#guard EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat + blockAccountWritesCapacity * 128 == EvmAsm.Stateless.ACCOUNT_WRITES_UNDO_AREA.toNat
#guard EvmAsm.Stateless.ACCOUNT_WRITES_UNDO_AREA.toNat + accountWritesUndoCapacity * 128 < EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat
#guard EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat + txAccountWritesCapacity * 128 <= EvmAsm.Stateless.SSZ_SCRATCH_BASE.toNat
#guard EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat - (EvmAsm.Stateless.ACCOUNT_WRITES_UNDO_AREA.toNat + accountWritesUndoCapacity * 128) == 0x19e000
-- High arenas sit above `.bss` / `.state_gas_diag` / storage undo.
#guard 0xa0b70000 < EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat
-- Low storage-write pack ends below the high AW arena.
#guard storageWritesTxBase + txStorageWritesCapacity * 128 <= EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat

-- Capacity x stride must equal the reserved arena exactly: an arena larger than
-- its reservation would run into the next region with nothing objecting.
#guard txAccountWritesCapacity * 128 == 0x200000
#guard blockAccountWritesCapacity * 128 == 0xc80000
#guard accountWritesUndoCapacity * 128 == 0x1400000
-- The transaction account map remains a separate 16384-row container; its
-- capacity is not coupled to the smaller transaction storage map.
#guard txAccountWritesCapacity == 16384
#guard accountWritesCallKeyBound == 15038
#guard accountWritesCallKeyBound <= txAccountWritesCapacity
-- GH #11770 derived bounds: distinct accounts per block, and write EVENTS per
-- transaction. The old `19047 <= blockAccountWritesCapacity` is retired with the
-- derivation that produced it (see `blockAccountWritesCapacity` above).
#guard 101809 <= blockAccountWritesCapacity
#guard 161204 <= accountWritesUndoCapacity
-- The tx map is bounded by DISTINCT accounts and stays at 16384 -- the split.
#guard 5371 <= txAccountWritesCapacity

-- Every routine must actually be emitted. This slice is inert, so nothing calls
-- them yet and a missing one would NOT be a link error -- these guards are the
-- only thing that would catch it.
#guard (accountWriteMapFunctions.splitOn "account_write_record:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_latest_balance:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_latest_balance_block:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_latest_nonce_block:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_latest_nonce_tx:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_auth_current:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_auth_block:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_created_contains:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_lookup_current:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_tombstone_balance_zero:").length == 2
#guard (accountWritesLatestNonceBlockFunction.splitOn "account_state_").length == 1


/-- Standalone e2e probe BuildUnit for #11329 TOUCHED first-producer gate. -/
def accountWriteTouchE2ePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  jal ra, account_write_touch_e2e\n" ++
  "  li x17, 93\n  li x10, 0\n  ecall\n"

def accountWriteTouchE2eProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm :=
    accountWriteTouchE2ePrologue ++
    accountWriteRecordFunction ++ "\n" ++
    accountWritesUndoPushFunction ++ "\n" ++
    accountWritesRestoreFrameFunction ++ "\n" ++
    accountWriteTouchE2eFunction
  dataAsm     :=
    ".section .data\n" ++
    accountWriteMapDataSection ++
    accountAgreementDataSection ++
    accountWriteMapBssSection
}


end EvmAsm.Codegen
