/-
  EvmAsm.Codegen.Programs.AccountWriteMapTail

  Tail of AccountWriteMap split to keep Codegen/Programs files under the 1500-line cap.
  The parent module supplies the shared map declarations.
 -/

import EvmAsm.Codegen.Programs.AccountWriteMap

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! Runtime-only mutation-boundary observations.  The old map/overlay
    agreement probe and per-reader differential are retired; the remaining
    checkpoint records mutation events for the verdict/control sweep. -/

def accountAgreementMutationEventCapacity : Nat := 1024

/-! A mutation-boundary witness for paths that do not naturally read the
    freshly-mutated balance.  This is a debug-only checkpoint: it is inert
    unless the agreement harness is armed, preserves the caller ABI, and
    records the canonical address plus the raw live `env+32` bytes after the
    mutation.  The metadata word is `{ mutation_id, depth }`; the sequence
    word is the zero-based event index.  It intentionally does not alter the
    production account maps or turn a missing natural read into one. -/
def accountAgreementMutationCheckpointFunction : String :=
  "account_agreement_mutation_checkpoint:\n" ++
  "  addi sp, sp, -96; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd a0, 40(sp); sd a1, 48(sp); sd a2, 56(sp); sd a3, 64(sp)\n" ++
  "  la t0, account_agreement_enabled; ld t1, 0(t0); beqz t1, .Laamc_done; mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  la t0, account_agreement_mutation_event_count; ld t1, 0(t0); li t2, " ++ toString accountAgreementMutationEventCapacity ++ "; bgeu t1, t2, .Laamc_overflow\n" ++
  "  slli t2, t1, 5; slli t3, t1, 6; add t2, t2, t3; la t3, account_agreement_mutation_events; add t3, t3, t2\n" ++
  "  mv t0, s0; addi t4, t3, 0; li t5, 20\n" ++
  ".Laamc_addr:\n" ++
  "  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; bnez t5, .Laamc_addr\n" ++
  "  mv t0, s1; addi t4, t3, 32; li t5, 32\n" ++
  ".Laamc_balance:\n" ++
  "  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; bnez t5, .Laamc_balance\n" ++
    "  slli t4, s3, 8; or t4, t4, s2; sd t4, 64(t3); sd t1, 72(t3); addi t1, t1, 1; la t0, account_agreement_mutation_event_count; sd t1, 0(t0); j .Laamc_done\n" ++
  ".Laamc_overflow:\n" ++
  "  la t0, account_agreement_mutation_event_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".Laamc_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld a0, 40(sp); ld a1, 48(sp); ld a2, 56(sp); ld a3, 64(sp); addi sp, sp, 96; ret\n"

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
def accountWritesBlockUpsertFunction : String :=
  "account_writes_block_upsert:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)\n" ++
  "  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)\n" ++
  "  la t0, account_writes_count; ld t1, 0(t0)\n" ++
  "  li t3, 0xbdb80000\n" ++                                      -- ACCOUNT_WRITES_AREA
  "  li t4, 0\n" ++
  ".Lawb_scan:\n" ++
  "  bgeu t4, t1, .Lawb_append; slli t5, t4, 7; add t5, t3, t5; li t6, 20; mv t2, t5; mv t3, a0\n" ++
  ".Lawb_cmp:\n" ++
  "  beqz t6, .Lawb_store; lbu t1, 0(t2); lbu a1, 0(t3); bne t1, a1, .Lawb_next; addi t2, t2, 1; addi t3, t3, 1; addi t6, t6, -1; j .Lawb_cmp\n" ++
  ".Lawb_next:\n" ++
  "  la t0, account_writes_count; ld t1, 0(t0); li t3, 0xbdb80000; addi t4, t4, 1; j .Lawb_scan\n" ++
  ".Lawb_append:\n" ++
  "  li t2, " ++ toString blockAccountWritesCapacity ++ "\n" ++
  "  bgeu t1, t2, .Lawb_overflow\n" ++
  "  slli t5, t1, 7; add t5, t3, t5; li t6, 20; mv t2, a0\n" ++
  ".Lawb_copy_addr:\n" ++
  "  beqz t6, .Lawb_zero; lbu t3, 0(t2); sb t3, 0(t5); addi t2, t2, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lawb_copy_addr\n" ++
  ".Lawb_zero:\n" ++
  "  addi t5, t5, -20; sw zero, 20(t5); sd zero, 24(t5); sd zero, 32(t5); sd zero, 40(t5); sd zero, 48(t5); sd zero, 56(t5); sd zero, 64(t5); sd zero, 72(t5); sd zero, 80(t5); sd zero, 88(t5); sd zero, 96(t5); sd zero, 104(t5); sd zero, 112(t5); sd zero, 120(t5); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  ".Lawb_store:\n" ++
  "  ld t2, 112(a0); andi t3, t2, 1; beqz t3, .Lawb_no_balance; ld t3, 32(a0); sd t3, 32(t5); ld t3, 40(a0); sd t3, 40(t5); ld t3, 48(a0); sd t3, 48(t5); ld t3, 56(a0); sd t3, 56(t5)\n" ++
  ".Lawb_no_balance:\n" ++
  "  andi t3, t2, 2; beqz t3, .Lawb_no_nonce; ld t3, 64(a0); sd t3, 64(t5)\n" ++
  ".Lawb_no_nonce:\n" ++
  "  andi t3, t2, 4; beqz t3, .Lawb_no_code; ld t3, 80(a0); sd t3, 80(t5); ld t3, 88(a0); sd t3, 88(t5)\n" ++
  ".Lawb_no_code:\n" ++
  "  andi t3, t2, 8; beqz t3, .Lawb_no_state; ld t3, 72(a0); sd t3, 72(t5)\n" ++
  ".Lawb_no_state:\n" ++
  -- EXEC_FLAGS VALUE 16: copy execFlags@96 from tx row. Twin of `.Lawr_store`.
  "  andi t3, t2, 16; beqz t3, .Lawb_no_flags; ld t3, 96(a0); sd t3, 96(t5)\n" ++
  ".Lawb_no_flags:\n" ++
  -- TOUCHED VALUE 32 sticky via mask OR (identical to `.Lawr_store`).
  "  ld t3, 112(t5); or t2, t2, t3; sd t2, 112(t5)\n" ++
  "  j .Lawb_done\n" ++
  ".Lawb_overflow:\n" ++
  "  la t0, account_writes_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".Lawb_done:\n" ++
  "  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)\n" ++
  "  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

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
def accountWritesApplyDeletesFunction : String :=
  "account_writes_apply_deletes:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  la t0, account_state_delete_count; ld s2, 0(t0); li t0, " ++ toString accountStateDeleteCapacity ++ "; bgtu s2, t0, .Lawd_overflow\n" ++
  "  li s1, 0\n" ++
  ".Lawd_delete_loop:\n" ++
  "  bgeu s1, s2, .Lawd_ok\n" ++
  "  slli t0, s1, 5; la t1, account_state_delete; add s0, t1, t0; ld t0, 24(s0); beqz t0, .Lawd_delete_next\n" ++
  "  la t0, tx_account_writes_count; ld t1, 0(t0); li t2, " ++ toString txAccountWritesCapacity ++ "; bgtu t1, t2, .Lawd_overflow; li s3, 0\n" ++
  ".Lawd_tx_loop:\n" ++
  "  bgeu s3, t1, .Lawd_miss\n" ++
  "  slli t2, s3, 7; li t3, 0xbf780000; add t2, t3, t2; mv t3, t2; mv t4, s0; li t5, 20\n" ++
  ".Lawd_cmp:\n" ++
  "  beqz t5, .Lawd_hit; lbu t6, 0(t3); lbu a0, 0(t4); bne t6, a0, .Lawd_next; addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lawd_cmp\n" ++
  ".Lawd_next:\n" ++
  "  addi s3, s3, 1; j .Lawd_tx_loop\n" ++
  ".Lawd_hit:\n" ++
  "  mv a5, s3; li a6, 0; jal ra, account_writes_undo_push; bnez a0, .Lawd_overflow\n" ++
  -- PHASE SPLIT (pinned Python authority, not inferred from this Lean mirror):
  -- before transaction finalization, `evm_selfdestruct_destroyed_table` is a
  -- same-transaction marker only: it feeds same-tx read/EXTCODEHASH,
  -- CREATE/CREATE2 collision, and NEW_ACCOUNT semantics.  It must not be
  -- collapsed into a Present-None post-state tombstone here.  The pinned
  -- authority is `vm/__init__.py:184,234`, `vm/interpreter.py:135,151,349`,
  -- `vm/instructions/system.py:691-693`, and `fork.py:1201-1202`.
  -- Lean mirror (not authority): this routine is the transaction-boundary
  -- materializer; every deferred delete must cross this path before it can
  -- become Present-None in `account_writes`.
  -- clear_account_preserving_balance then EIP-161 empty → destroy_account(None).
  "  slli t0, s3, 7; li t1, 0xbf780000; add t0, t1, t0; sd zero, 64(t0); sd zero, 80(t0); sd zero, 88(t0); sd zero, 96(t0); sd zero, 104(t0)\n" ++
  "  ld t1, 32(t0); ld t2, 40(t0); or t1, t1, t2; ld t2, 48(t0); or t1, t1, t2; ld t2, 56(t0); or t1, t1, t2; bnez t1, .Lawd_keep_present\n" ++
  -- Map bal=0 + HAS_BALANCE: authoritative post-drain zero (do not resurrect
  -- parent pre-balance).  GH #11688 / fixture 01114.
  "  ld t1, 112(t0); andi t1, t1, " ++ toString accountWriteHasBalance ++ "; bnez t1, .Lawd_present_none\n" ++
  -- Map bal=0 without HAS_BALANCE: resolve the lower-tier pre-state balance.
  -- Missing balance component means the current balance was never changed
  -- above that tier, so the authenticated parent account is the preserved
  -- value (self-burn / CREATE-seed path).
  "  sd zero, 40(sp); sd zero, 48(sp); sd zero, 56(sp); sd zero, 64(sp); sd zero, 72(sp)\n" ++
  "  mv a0, s0; addi a1, sp, 40; la t1, sv_pre_rlp_ptr; ld a2, 0(t1); la t1, sv_pre_rlp_len; ld a3, 0(t1); la t1, bv_witness_state_ptr; ld a4, 0(t1); la t1, bv_witness_state_len; ld a5, 0(t1); jal ra, account_resolve_pre_state\n" ++
  -- Resolver status 1 is a malformed/unavailable authenticated lookup.  It is
  -- a rejection, never an authenticated zero balance: otherwise a preserved
  -- nonzero balance could be turned into STATE=None and alter EIP-161 deletion.
  "  bnez a0, .Lawd_overflow\n" ++
  "  ld t1, 48(sp); ld t2, 56(sp); or t1, t1, t2; ld t2, 64(sp); or t1, t1, t2; ld t2, 72(sp); or t1, t1, t2; beqz t1, .Lawd_present_none\n" ++
  "  slli t0, s3, 7; li t2, 0xbf780000; add t0, t2, t0\n" ++
  "  ld t1, 48(sp); sd t1, 32(t0); ld t1, 56(sp); sd t1, 40(t0)\n" ++
  "  ld t1, 64(sp); sd t1, 48(t0); ld t1, 72(sp); sd t1, 56(t0)\n" ++
  "  j .Lawd_keep_present\n" ++
  -- A pre-finalization table hit must not take this Present-None branch: doing
  -- so makes EXTCODEHASH/availability observe deletion too early, can admit a
  -- same-tx CREATE collision, or mischarge NEW_ACCOUNT.  Conversely, skipping
  -- this boundary materialization leaves deleted state visible to the next tx.
  ".Lawd_present_none:\n" ++
  "  slli t0, s3, 7; li t1, 0xbf780000; add t0, t1, t0\n" ++
  "  sd zero, 72(t0); li t1, 15; sd t1, 112(t0); sd zero, 120(t0); j .Lawd_delete_next\n" ++
  ".Lawd_keep_present:\n" ++
  "  li t1, 1; sd t1, 72(t0); li t1, 15; sd t1, 112(t0); sd zero, 120(t0); j .Lawd_delete_next\n" ++
  -- Miss: upsert STATE=None (destroy_account). Balance already drained by
  -- SELFDESTRUCT transfer on the EIP-6780 same-tx path. a1 must be a real
  -- 32-byte zero scratch — account_write_record loads balance through the
  -- pointer when HAS_BALANCE is set (null would fault).
  ".Lawd_miss:\n" ++
  "  sd zero, 40(sp); sd zero, 48(sp); sd zero, 56(sp); sd zero, 64(sp)\n" ++
  "  mv a0, s0; addi a1, sp, 40; li a2, 0; li a3, 0; li a4, 0; li a5, 0; li a6, " ++ toString (accountWriteHasBalance + accountWriteHasNonce + accountWriteHasCode + accountWriteHasState) ++ "; li a7, 0; jal ra, account_write_record\n" ++
  "  la t0, tx_account_writes_overflow; ld t0, 0(t0); bnez t0, .Lawd_overflow\n" ++
  ".Lawd_delete_next:\n" ++
  "  addi s1, s1, 1; j .Lawd_delete_loop\n" ++
  ".Lawd_ok:\n" ++
  "  li a0, 0; j .Lawd_ret\n" ++
  ".Lawd_overflow:\n" ++
  "  la t0, tx_account_writes_overflow; li t1, 1; sd t1, 0(t0); la t0, account_writes_overflow; sd t1, 0(t0); li a0, 1\n" ++
  ".Lawd_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); addi sp, sp, 80; ret\n"

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
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (1975 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
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
/-! ## account_resolve_pre_state

    Resolve one account's pre-transaction balance/nonce with the same
    precedence as execution-specs' `_get_pre_tx_account`: the block-cumulative
    `account_writes` map first, then the durable AccountState overlay, then the
    authenticated parent-state witness. The block map is authoritative for
    fields it carries; fieldwise rows may leave the other component unknown.

    a0 = canonical address (20 B), a1 = output account scratch (nonce@0,
    balance@8), a2/a3 = parent header RLP ptr/len, a4/a5 = witness ptr/len.
    Returns a0 = 0 on a resolved account (including authenticated absence,
    represented as zero nonce/balance), or 1 on malformed lookup/error. -/
def accountResolvePreState_prog : Program :=
  [ .ADDI .x2 .x2 (-208 : BitVec 12),
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
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .LI .x23 (0 : Word),
    .SD .x9 .x0 (0 : BitVec 12),
    .SD .x9 .x0 (8 : BitVec 12),
    .SD .x9 .x0 (16 : BitVec 12),
    .SD .x9 .x0 (24 : BitVec 12),
    .SD .x9 .x0 (32 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.account_resolve_pre_state + 92)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.account_resolve_pre_state + 92)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (1975 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_resolve_pre_state + 256) (GuestAddrs.account_resolve_pre_state + 120)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .LI .x31 (20 : Word),
    .MV .x10 .x30,
    .MV .x11 .x8,
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
    .MV .x22 .x30,
    .LD .x5 .x22 (112 : BitVec 12),
    .ANDI .x6 .x5 (1 : BitVec 12),
    .BEQ .x6 .x0 (40 : BitVec 13),
    .LD .x6 .x22 (32 : BitVec 12),
    .SD .x9 .x6 (8 : BitVec 12),
    .LD .x6 .x22 (40 : BitVec 12),
    .SD .x9 .x6 (16 : BitVec 12),
    .LD .x6 .x22 (48 : BitVec 12),
    .SD .x9 .x6 (24 : BitVec 12),
    .LD .x6 .x22 (56 : BitVec 12),
    .SD .x9 .x6 (32 : BitVec 12),
    .ORI .x23 .x23 (1 : BitVec 12),
    .ANDI .x6 .x5 (2 : BitVec 12),
    .BEQ .x6 .x0 (16 : BitVec 13),
    .LD .x6 .x22 (64 : BitVec 12),
    .SD .x9 .x6 (0 : BitVec 12),
    .ORI .x23 .x23 (2 : BitVec 12),
    .LI .x5 (3 : Word),
    .BEQ .x23 .x5 (brOff (GuestAddrs.account_resolve_pre_state + 384) (GuestAddrs.account_resolve_pre_state + 260)),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .MV .x12 .x8,
    .LI .x13 (20 : Word),
    .MV .x14 .x20,
    .MV .x15 .x21,
    .ADDI .x16 .x2 (96 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.account_at_header_state_root_tracked (GuestAddrs.account_resolve_pre_state + 292)),
    .LI .x5 (1 : Word),
    .BLTU .x5 .x10 (brOff (GuestAddrs.account_resolve_pre_state + 392) (GuestAddrs.account_resolve_pre_state + 300)),
    .BEQ .x10 .x0 (8 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.account_resolve_pre_state + 384) (GuestAddrs.account_resolve_pre_state + 308)),
    .ANDI .x6 .x23 (1 : BitVec 12),
    .BNE .x6 .x0 (44 : BitVec 13),
    .ADDI .x5 .x2 (96 : BitVec 12),
    .LD .x6 .x5 (8 : BitVec 12),
    .SD .x9 .x6 (8 : BitVec 12),
    .LD .x6 .x5 (16 : BitVec 12),
    .SD .x9 .x6 (16 : BitVec 12),
    .LD .x6 .x5 (24 : BitVec 12),
    .SD .x9 .x6 (24 : BitVec 12),
    .LD .x6 .x5 (32 : BitVec 12),
    .SD .x9 .x6 (32 : BitVec 12),
    .ORI .x23 .x23 (1 : BitVec 12),
    .ANDI .x6 .x23 (2 : BitVec 12),
    .BNE .x6 .x0 (20 : BitVec 13),
    .ADDI .x5 .x2 (96 : BitVec 12),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x9 .x6 (0 : BitVec 12),
    .ORI .x23 .x23 (2 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
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
    .ADDI .x2 .x2 (208 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountResolvePreState_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountResolvePreState_relocs : RelocTable :=
  [ (23, .la .x5 "account_writes_count"),
    (73, .jal .x1 "account_at_header_state_root_tracked") ]

def accountResolvePreStateFunction : String :=
  "account_resolve_pre_state:\n" ++ emitProgramR accountResolvePreState_prog accountResolvePreState_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountResolvePreState_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountResolvePreStateFunction_eq_prog :
    accountResolvePreStateFunction = "account_resolve_pre_state:\n" ++ emitProgramR accountResolvePreState_prog accountResolvePreState_relocs := rfl

#guard accountResolvePreStateFunction.startsWith "account_resolve_pre_state:\n"
#guard accountResolvePreState_prog.length = 111
/-! ## `account_resolve_execution_state`

    Resolve an execution-time account with the three-tier precedence from
    `state_tracker.py:get_account_optional` (pinned `e5a8caf1b`, lines
    179-203): transaction writes, then the block-cumulative map, then the
    authenticated parent state.  This is deliberately a separate symbol from
    `account_resolve_pre_state`.  The latter implements
    `block_access_lists.py:_get_pre_tx_account` and is called by the BAL builder
    while it is walking `tx_account_writes`; letting that helper see the tx map
    would make the builder compare each row against itself and accept a missing
    BAL entry.

    The resolver records the address before walking its tiers, matching
    Amsterdam's `get_account_optional`; CREATE is the current sole consumer.
    The ABI is:

      a0 = canonical address (20-byte BE)
      a1 = output scratch: nonce@0, balance@8..40, code_ptr@40,
           code_len@48, present@56
      a2/a3 = parent header RLP pointer/length
      a4/a5 = witness.state pointer/length
      a6/a7 = witness.codes pointer/length

    The return is resolver-local state, not an `account_at_header_state_root`
    parser status: 0 absent, 1 live code, 2 present-but-empty, 3 deleted, and
    4 resolver-unavailable (a non-empty code hash missing from witness.codes).
    Status 4 means a valid authenticated account lacks a witness.codes
    preimage: a block may be valid, so a caller's rejection is a false reject
    (FR) caused by witness incompleteness.  A malformed authenticated lookup
    uses 5: that is malformed proof/input evidence, so its rejection is a
    genuine reject rather than a witness-shortfall bail.  Keeping 4 and 5 separate is
    therefore part of the ABI.  A map code row is authoritative and its pointer/length
    is preserved.  Otherwise
    the authenticated account's code_hash is resolved with the RAW
    `witness_codes_lookup_by_hash` helper, never `code_read_fetch`: this path
    materialises state and must not record a code read or alter witness-code
    selection.  Account absence and EMPTY_CODE_HASH are truthful zero-length
    code; a non-empty hash miss is never fabricated as empty.

    EIP-7702 designators are preserved and followed by the existing dispatch
    path, never executed as bytecode.  Marker recognition is by the `ef 01 00`
    prefix after a three-byte length check, not by assuming every 23-byte code
    blob is a marker.  Storage root remains out of scope: the storage path
    derives it with `mpt_bounded_storage_root` (#11385). -/
def accountResolveExecutionState_prog : Program :=
  [ .ADDI .x2 .x2 (-208 : BitVec 12),
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
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .MV .x23 .x17,
    .LI .x24 (0 : Word),
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.account_read_record (GuestAddrs.account_resolve_execution_state + 84)),
    .SD .x9 .x0 (0 : BitVec 12),
    .SD .x9 .x0 (8 : BitVec 12),
    .SD .x9 .x0 (16 : BitVec 12),
    .SD .x9 .x0 (24 : BitVec 12),
    .SD .x9 .x0 (32 : BitVec 12),
    .SD .x9 .x0 (40 : BitVec 12),
    .SD .x9 .x0 (48 : BitVec 12),
    .SD .x9 .x0 (56 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_resolve_execution_state + 120)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_resolve_execution_state + 120)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (2031 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_resolve_execution_state + 340) (GuestAddrs.account_resolve_execution_state + 148)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .LI .x31 (20 : Word),
    .MV .x10 .x30,
    .MV .x11 .x8,
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
    .MV .x31 .x30,
    .LD .x5 .x31 (112 : BitVec 12),
    .ANDI .x6 .x5 (1 : BitVec 12),
    .BEQ .x6 .x0 (40 : BitVec 13),
    .LD .x6 .x31 (32 : BitVec 12),
    .SD .x9 .x6 (8 : BitVec 12),
    .LD .x6 .x31 (40 : BitVec 12),
    .SD .x9 .x6 (16 : BitVec 12),
    .LD .x6 .x31 (48 : BitVec 12),
    .SD .x9 .x6 (24 : BitVec 12),
    .LD .x6 .x31 (56 : BitVec 12),
    .SD .x9 .x6 (32 : BitVec 12),
    .ORI .x24 .x24 (1 : BitVec 12),
    .ANDI .x6 .x5 (2 : BitVec 12),
    .BEQ .x6 .x0 (16 : BitVec 13),
    .LD .x6 .x31 (64 : BitVec 12),
    .SD .x9 .x6 (0 : BitVec 12),
    .ORI .x24 .x24 (2 : BitVec 12),
    .ANDI .x6 .x5 (4 : BitVec 12),
    .BEQ .x6 .x0 (32 : BitVec 13),
    .LD .x6 .x31 (80 : BitVec 12),
    .SD .x9 .x6 (40 : BitVec 12),
    .LD .x6 .x31 (88 : BitVec 12),
    .SD .x9 .x6 (48 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x9 .x6 (56 : BitVec 12),
    .ORI .x24 .x24 (4 : BitVec 12),
    .ANDI .x6 .x5 (8 : BitVec 12),
    .BEQ .x6 .x0 (16 : BitVec 13),
    .LD .x6 .x31 (72 : BitVec 12),
    .SD .x9 .x6 (56 : BitVec 12),
    .ORI .x24 .x24 (8 : BitVec 12),
    .ANDI .x5 .x24 (8 : BitVec 12),
    .BEQ .x5 .x0 (12 : BitVec 13),
    .LD .x6 .x9 (56 : BitVec 12),
    .BEQ .x6 .x0 (brOff (GuestAddrs.account_resolve_execution_state + 1024) (GuestAddrs.account_resolve_execution_state + 352)),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.account_resolve_execution_state + 356)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.account_resolve_execution_state + 356)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (1975 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_resolve_execution_state + 528) (GuestAddrs.account_resolve_execution_state + 384)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .LI .x31 (20 : Word),
    .MV .x10 .x30,
    .MV .x11 .x8,
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
    .MV .x31 .x30,
    .LD .x5 .x31 (112 : BitVec 12),
    .ANDI .x6 .x24 (4 : BitVec 12),
    .BNE .x6 .x0 (40 : BitVec 13),
    .ANDI .x6 .x5 (4 : BitVec 12),
    .BEQ .x6 .x0 (32 : BitVec 13),
    .LD .x6 .x31 (80 : BitVec 12),
    .SD .x9 .x6 (40 : BitVec 12),
    .LD .x6 .x31 (88 : BitVec 12),
    .SD .x9 .x6 (48 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x9 .x6 (56 : BitVec 12),
    .ORI .x24 .x24 (4 : BitVec 12),
    .ANDI .x6 .x24 (8 : BitVec 12),
    .BNE .x6 .x0 (24 : BitVec 13),
    .ANDI .x6 .x5 (8 : BitVec 12),
    .BEQ .x6 .x0 (16 : BitVec 13),
    .LD .x6 .x31 (72 : BitVec 12),
    .SD .x9 .x6 (56 : BitVec 12),
    .ORI .x24 .x24 (8 : BitVec 12),
    .ANDI .x5 .x24 (8 : BitVec 12),
    .BEQ .x5 .x0 (20 : BitVec 13),
    .LD .x6 .x9 (56 : BitVec 12),
    .BEQ .x6 .x0 (brOff (GuestAddrs.account_resolve_execution_state + 1024) (GuestAddrs.account_resolve_execution_state + 540)),
    .ANDI .x5 .x24 (4 : BitVec 12),
    .BNE .x5 .x0 (brOff (GuestAddrs.account_resolve_execution_state + 900) (GuestAddrs.account_resolve_execution_state + 548)),
    .MV .x10 .x8,
    .ADDI .x11 .x2 (96 : BitVec 12),
    .MV .x12 .x18,
    .MV .x13 .x19,
    .MV .x14 .x20,
    .MV .x15 .x21,
    .JAL .x1 (jalOff GuestAddrs.account_resolve_pre_state (GuestAddrs.account_resolve_execution_state + 576)),
    .BNE .x10 .x0 (brOff (GuestAddrs.account_resolve_execution_state + 1056) (GuestAddrs.account_resolve_execution_state + 580)),
    .ANDI .x5 .x24 (1 : BitVec 12),
    .BNE .x5 .x0 (44 : BitVec 13),
    .ADDI .x6 .x2 (96 : BitVec 12),
    .LD .x7 .x6 (8 : BitVec 12),
    .SD .x9 .x7 (8 : BitVec 12),
    .LD .x7 .x6 (16 : BitVec 12),
    .SD .x9 .x7 (16 : BitVec 12),
    .LD .x7 .x6 (24 : BitVec 12),
    .SD .x9 .x7 (24 : BitVec 12),
    .LD .x7 .x6 (32 : BitVec 12),
    .SD .x9 .x7 (32 : BitVec 12),
    .ORI .x24 .x24 (1 : BitVec 12),
    .ANDI .x5 .x24 (2 : BitVec 12),
    .BNE .x5 .x0 (20 : BitVec 13),
    .ADDI .x6 .x2 (96 : BitVec 12),
    .LD .x7 .x6 (0 : BitVec 12),
    .SD .x9 .x7 (0 : BitVec 12),
    .ORI .x24 .x24 (2 : BitVec 12),
    .ANDI .x5 .x24 (4 : BitVec 12),
    .BNE .x5 .x0 (brOff (GuestAddrs.account_resolve_execution_state + 900) (GuestAddrs.account_resolve_execution_state + 660)),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .MV .x12 .x8,
    .LI .x13 (20 : Word),
    .MV .x14 .x20,
    .MV .x15 .x21,
    .ADDI .x16 .x2 (96 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.account_at_header_state_root_tracked (GuestAddrs.account_resolve_execution_state + 692)),
    .BEQ .x10 .x0 (16 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (brOff (GuestAddrs.account_resolve_execution_state + 992) (GuestAddrs.account_resolve_execution_state + 704)),
    .JAL .x0 (jalOff (GuestAddrs.account_resolve_execution_state + 1056) (GuestAddrs.account_resolve_execution_state + 708)),
    .ANDI .x5 .x24 (8 : BitVec 12),
    .BNE .x5 .x0 (60 : BitVec 13),
    .ADDI .x28 .x2 (96 : BitVec 12),
    .LD .x6 .x28 (0 : BitVec 12),
    .SD .x9 .x6 (0 : BitVec 12),
    .LD .x6 .x28 (8 : BitVec 12),
    .SD .x9 .x6 (8 : BitVec 12),
    .LD .x6 .x28 (16 : BitVec 12),
    .SD .x9 .x6 (16 : BitVec 12),
    .LD .x6 .x28 (24 : BitVec 12),
    .SD .x9 .x6 (24 : BitVec 12),
    .LD .x6 .x28 (32 : BitVec 12),
    .SD .x9 .x6 (32 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x9 .x6 (56 : BitVec 12),
    .ORI .x24 .x24 (3 : BitVec 12),
    .ADDI .x28 .x2 (96 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.chahsr_empty_code_hash (GuestAddrs.account_resolve_execution_state + 780)),
    .ADDI .x5 .x5 (laLo GuestAddrs.chahsr_empty_code_hash (GuestAddrs.account_resolve_execution_state + 780)),
    .LD .x6 .x28 (72 : BitVec 12),
    .LD .x7 .x5 (0 : BitVec 12),
    .BNE .x6 .x7 (44 : BitVec 13),
    .LD .x6 .x28 (80 : BitVec 12),
    .LD .x7 .x5 (8 : BitVec 12),
    .BNE .x6 .x7 (32 : BitVec 13),
    .LD .x6 .x28 (88 : BitVec 12),
    .LD .x7 .x5 (16 : BitVec 12),
    .BNE .x6 .x7 (20 : BitVec 13),
    .LD .x6 .x28 (96 : BitVec 12),
    .LD .x7 .x5 (24 : BitVec 12),
    .BNE .x6 .x7 (8 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.account_resolve_execution_state + 976) (GuestAddrs.account_resolve_execution_state + 836)),
    .MV .x10 .x22,
    .MV .x11 .x23,
    .ADDI .x12 .x2 (168 : BitVec 12),
    .ADDI .x13 .x2 (80 : BitVec 12),
    .ADDI .x14 .x2 (88 : BitVec 12),
    .SD .x2 .x0 (80 : BitVec 12),
    .SD .x2 .x0 (88 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.witness_codes_lookup_by_hash (GuestAddrs.account_resolve_execution_state + 868)),
    .BNE .x10 .x0 (brOff (GuestAddrs.account_resolve_execution_state + 1040) (GuestAddrs.account_resolve_execution_state + 872)),
    .LD .x5 .x2 (80 : BitVec 12),
    .ADD .x5 .x22 .x5,
    .SD .x9 .x5 (40 : BitVec 12),
    .LD .x6 .x2 (88 : BitVec 12),
    .SD .x9 .x6 (48 : BitVec 12),
    .JAL .x0 (4 : BitVec 21),
    .LD .x5 .x9 (48 : BitVec 12),
    .LI .x6 (3 : Word),
    .BLTU .x5 .x6 (52 : BitVec 13),
    .LD .x5 .x9 (40 : BitVec 12),
    .LBU .x6 .x5 (0 : BitVec 12),
    .LI .x7 (239 : Word),
    .BNE .x6 .x7 (36 : BitVec 13),
    .LBU .x6 .x5 (1 : BitVec 12),
    .LI .x7 (1 : Word),
    .BNE .x6 .x7 (24 : BitVec 13),
    .LBU .x6 .x5 (2 : BitVec 12),
    .BNE .x6 .x0 (16 : BitVec 13),
    .JAL .x0 (4 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.account_resolve_execution_state + 1068) (GuestAddrs.account_resolve_execution_state + 956)),
    .LD .x5 .x9 (48 : BitVec 12),
    .BEQ .x5 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.account_resolve_execution_state + 1068) (GuestAddrs.account_resolve_execution_state + 972)),
    .SD .x9 .x0 (40 : BitVec 12),
    .SD .x9 .x0 (48 : BitVec 12),
    .LI .x10 (2 : Word),
    .JAL .x0 (jalOff (GuestAddrs.account_resolve_execution_state + 1068) (GuestAddrs.account_resolve_execution_state + 988)),
    .ANDI .x5 .x24 (8 : BitVec 12),
    .BEQ .x5 .x0 (12 : BitVec 13),
    .LD .x6 .x9 (56 : BitVec 12),
    .BNE .x6 .x0 (-28 : BitVec 13),
    .SD .x9 .x0 (40 : BitVec 12),
    .SD .x9 .x0 (48 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (48 : BitVec 21),
    .SD .x9 .x0 (40 : BitVec 12),
    .SD .x9 .x0 (48 : BitVec 12),
    .LI .x10 (3 : Word),
    .JAL .x0 (32 : BitVec 21),
    .SD .x9 .x0 (40 : BitVec 12),
    .SD .x9 .x0 (48 : BitVec 12),
    .LI .x10 (4 : Word),
    .JAL .x0 (16 : BitVec 21),
    .SD .x9 .x0 (40 : BitVec 12),
    .SD .x9 .x0 (48 : BitVec 12),
    .LI .x10 (5 : Word),
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
    .ADDI .x2 .x2 (208 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountResolveExecutionState_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountResolveExecutionState_relocs : RelocTable :=
  [ (21, .jal .x1 "account_read_record"),
    (30, .la .x5 "tx_account_writes_count"),
    (89, .la .x5 "account_writes_count"),
    (144, .jal .x1 "account_resolve_pre_state"),
    (173, .jal .x1 "account_at_header_state_root_tracked"),
    (195, .la .x5 "chahsr_empty_code_hash"),
    (217, .jal .x1 "witness_codes_lookup_by_hash") ]

def accountResolveExecutionStateFunction : String :=
  "account_resolve_execution_state:\n" ++ emitProgramR accountResolveExecutionState_prog accountResolveExecutionState_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountResolveExecutionState_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountResolveExecutionStateFunction_eq_prog :
    accountResolveExecutionStateFunction = "account_resolve_execution_state:\n" ++ emitProgramR accountResolveExecutionState_prog accountResolveExecutionState_relocs := rfl

#guard accountResolveExecutionStateFunction.startsWith "account_resolve_execution_state:\n"
#guard accountResolveExecutionState_prog.length = 279
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
  "  li t3, 0xbf780000; lbu t0, 112(t3); sd t0, 0(s0); ld t0, 96(t3); sd t0, 8(s0)\n" ++
  -- 2) twin same-addr BALANCE-only write (no TOUCHED in mask) — sticky must keep 32
  "  la t0, account_write_e2e_bal; li t1, 7; sb t1, 31(t0)\n" ++
  "  la a0, account_write_e2e_addr; la a1, account_write_e2e_bal; li a2, 0; li a3, 0; li a4, 0; li a5, 0\n" ++
  "  li a6, " ++ toString accountWriteHasBalance ++ "; li a7, 0\n" ++
  "  jal ra, account_write_record\n" ++
  "  li t3, 0xbf780000; lbu t0, 112(t3); sd t0, 16(s0)\n" ++
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
  -- ⚠️ `accountWriteRecordFunction` joins with an EXPLICIT `"\n"`, unlike the
  -- three bare `++` joins further down. It became an `emitProgramR` render in
  -- this change, and a rendered Program ends at its last instruction with NO
  -- trailing newline, where the String literal it replaced ended `"  ret\n"`.
  -- The remaining bare `++` members are still String literals that carry their
  -- own trailing newline; each must gain a `"\n"` at the moment IT is
  -- transcribed, not before. Getting this wrong does not move `.text` — the
  -- assembler ignores the whitespace — so only the seam guard below catches it.
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
  accountAgreementMutationCheckpointFunction ++
  accountWritesBlockUpsertFunction ++
  accountWritesApplyDeletesFunction ++
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

-- High pack (GH #11186): AW + 8 MiB = AU + 20 MiB = TX_AW + 2 MiB = SSZ.
-- Capacity guards fire BEFORE any store.
#guard EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat + 0x800000 == EvmAsm.Stateless.ACCOUNT_WRITES_UNDO_AREA.toNat
#guard EvmAsm.Stateless.ACCOUNT_WRITES_UNDO_AREA.toNat + 0x1400000 == EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat
#guard EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat + 0x200000 == EvmAsm.Stateless.SSZ_SCRATCH_BASE.toNat
-- High arenas sit above `.bss` / `.state_gas_diag` / storage undo.
#guard 0xa0b70000 < EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat
-- Low storage-write pack ends below the high TX account-writes arena.
#guard storageWritesTxBase + txStorageWritesCapacity * 128 <= EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat

-- Capacity x stride must equal the reserved arena exactly: an arena larger than
-- its reservation would run into the next region with nothing objecting.
#guard txAccountWritesCapacity * 128 == 0x200000
#guard blockAccountWritesCapacity * 128 == 0x800000
#guard accountWritesUndoCapacity * 128 == 0x1400000
-- The transaction account map remains a separate 16384-row container; its
-- capacity is not coupled to the smaller transaction storage map.
#guard txAccountWritesCapacity == 16384
#guard accountWritesCallKeyBound == 15038
#guard accountWritesCallKeyBound <= txAccountWritesCapacity
-- GH #11770 derived bounds: distinct accounts per block, and write EVENTS per
-- transaction. The old `19047 <= blockAccountWritesCapacity` is retired with the
-- derivation that produced it (see `blockAccountWritesCapacity` above).
#guard 64035 <= blockAccountWritesCapacity
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
