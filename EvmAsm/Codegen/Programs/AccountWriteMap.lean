/-
  EvmAsm.Codegen.Programs.AccountWriteMap

  The guest's `account_writes` map — the NONSTORAGE half of GH #10695.

  ## Why one container and not three

  #10695 was scoped as "balance, nonce and code lack per-transaction
  attribution", which reads as three gaps and invites three containers. The
  spec's own structure says otherwise. Both levels keep exactly one
  non-storage write container:

      BlockState.account_writes       : Dict[Address, Optional[Account]]   (state_tracker.py:70)
      TransactionState.account_writes : Dict[Address, Optional[Account]]   (state_tracker.py:97)

  and an `Account` carries nonce, balance and code together, so
  `update_builder_from_tx` derives **all three** BAL fields from a single loop
  over that one dict (`block_access_lists.py:637-664`):

      for address, post_account in tx_state.account_writes.items():
          pre_account = _get_pre_tx_account(block_state.account_writes, pre_state, address)
          if pre_balance   != post_balance:   add_balance_change(builder, address, idx, post_balance)
          if pre_nonce     != post_nonce:     add_nonce_change(builder, address, idx, U64(post_nonce))
          if pre_code_hash != post_code_hash: add_code_change(builder, address, idx, post_code)

  So this module is ONE arena pair plus an undo journal, mirroring
  `StorageWriteMap`'s shape (r59nm S2/S5a) rather than tripling it.

  The guest producers do *not* each observe a complete `Optional[Account]`:
  balance/nonce effects and code deposits know different final components. The
  fixed-width row therefore uses a component-valid mask and fieldwise overlay.
  This is a justified mechanism divergence from the spec's whole-account
  assignment: each guest producer writes only what it observed, while an
  upsert preserves earlier final components. The mask means **was written**,
  never **did change**. At the transaction boundary, each valid component is
  still compared with the pre-transaction baseline and emitted only on
  inequality, so net-zero writes are not BAL events.

  ## Why the container shape is the attribution mechanism

  Note what supplies the transaction identity in the spec: `idx =
  builder.block_access_index`, read **once per call**, and
  `update_builder_from_tx` is called **once per transaction**, *before* the
  transaction's writes are merged into the block (`state_tracker.py:855-856`,
  and the docstring says "Must be called before the transaction's writes are
  merged"). There is no index field on any record. The transaction is the
  container, so a change cannot exist unattributed.

  That is the difference between a property and a discipline, and #10697 is the
  evidence: the guest's storage side *did* carry a per-row index field, and it
  was stamped from a global that one dispatch path never wrote, so every
  contract transaction's rows were tagged with an index no transaction had
  written. A field is maintained by hand at every append site and forgettable at
  the next one. A container cannot be forgotten.

  ## What this slice does and does not do

  DOES: establish the two levels, keyed fieldwise upsert, tx→block merge and
  clear helpers, discard helper, overflow latches and frame rollback via a
  reverse-replayed undo journal. `record_nonstorage_effect` and
  `create_record_code_effect` dual-record successful execution facts into the
  transaction map; the MTx body-rollback boundary restores the same undo mark
  as the existing execution-effect logs, then the post-body coinbase effect is
  recorded and the surviving transaction map is incorporated. The
  distinct-account capacity proof covers the block level;
  raw `record_nonstorage_effect`'s 38460-row admission limit is not that proof.

  The builder walk is live. `account_writes_emit_builder_tx` realizes BAL
  changes before incorporation, using the spec's *pre-tx* baseline —
  `_get_pre_tx_account` reads the BLOCK-cumulative value and falls back to
  `pre_state`, NOT the pre-block value — and the three-way field comparison
  whose inequality test makes net-zero filtering automatic. This map therefore
  retains execution facts *and* supplies the transaction-boundary BAL rows;
  it is not a fed-but-unread side arena.

  Producer coverage is path-specific, not a single global omission. The
  current wiring covers execution nonstorage/code effects, the inclusion-time
  sender nonce, and the post-body coinbase fee. The dispatcher sender path also
  stages the process-transaction gas debit from execution-specs
  `fork.py:1105-1108` and publishes it through
  `dispatcher_seed_pending_upfront_sender_balance` before the builder walk.
  A 01306 trace on that path records sender `f6c3...` with pre-balance 10^27
  and post-balance `999999999999999998800000000`, exactly the specified
  `gas_price * gas_limit` debit. Uniform publication across every producer path
  remains a separate audit question; it must not be described as a globally
  missing transition or as an unread map.

  ## The `present` field

  The spec's value type is `Optional[Account]`, and `None` — the account does
  not exist — is a *distinct* state from an account whose balance, nonce and
  code hash all happen to be zero. So `present` is a field, not an
  all-zero-record sentinel. This is the same reasoning as `wasAbsent` on the
  storage side, where zero is a legitimate stored value; both are cases where a
  sentinel would silently invent a state the spec does not have.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.ArenaCapacities
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.StorageWriteMap
import EvmAsm.Stateless.MemoryLayout

namespace EvmAsm.Codegen
open EvmAsm.Rv64

/-- Transaction-local entries. One transaction's CALL-tree bound is 15038, so
    the existing 16384-row map reservation remains sufficient. This is an
    occupancy bound, not an undo-flow bound: a hit updates one map row while
    still pushing a fresh rollback record. The undo-flow workload derivation
    needs 4294 rows on the densest current path, so the 16384-row reservation
    is intentionally retained with roughly 3.8x headroom. -/
def txAccountWritesCapacity : Nat := 16384

/-- Block-lifetime entries. Amsterdam permits at most 9523 minimum-cost plain
    value transfers in a 200M-gas block; distinct senders and recipients plus
    coinbase require 19047 keys. Round to a 2.5 MiB arena. -/
def blockAccountWritesCapacity : Nat := 20480

/-- CALL-tree-only distinct-key bound. A value-bearing internal CALL to a cold
    target costs at least `COLD_ACCOUNT_ACCESS = 3000 + CALL_VALUE = 10300`;
    a call graph with `E` newly distinct targets has at most `E + 1` vertices.
    This deliberately loose bound omits the enclosing transaction's intrinsic
    gas.

    It is NOT the block-level capacity proof: that map accumulates across
    transactions, and the plain-transfer sender+recipient route remains the
    named precondition for producer wiring. The consolidated route enumeration
    lives in GH #10680; raw nonstorage rows (38460) are not distinct map keys. -/
def accountWritesCallKeyBound : Nat := 1 + 200000000 / (3000 + 10300)

/-- The AccountState scan capacity is defined in CreateCodeEffectLog.lean.
    Keep the resolver's emitted bound explicit here and pin it against that
    shared definition in NonstorageEffectLog, which imports both modules. -/
def accountStateResolverCapacity : Nat := 38460

/-- Per-row component-valid bits. A set bit says this transaction observed a
    final value for the component; it does not by itself mean the value differs
    from the transaction's baseline.

    These are **VALUES** (powers of two), not bit indices. Callers and `andi`
    immediates must use the VALUE: EXEC_FLAGS is 16, never 4 (which is CODE). -/
def accountWriteHasBalance : Nat := 1
def accountWriteHasNonce : Nat := 2
def accountWriteHasCode : Nat := 4
def accountWriteHasState : Nat := 8
/-- VALUE 16 = bit index 4. When set, `execFlags@96` carries a full
    AccountState-compatible flags word (see `CreateCodeEffectLog` flags@+88). -/
def accountWriteHasExecFlags : Nat := 16
/-- VALUE 32 = bit index 5. Sticky: once OR'd into the row mask it is never
    cleared by a later write that omits it. Marks execution-touched accounts
    for root enumeration even when no BALANCE/NONCE/CODE delta is present. -/
def accountWriteHasTouched : Nat := 32

/-! The fixed 128-byte row is `{addr_BE20@0, padding@20..31,
balance@32, nonce@64, optionalState@72, codePtr@80, codeLen@88,
execFlags@96, reserved@104..111, validMask@112, reserved@120}`.
The 20-byte key is deliberately identical to the builder's address segment;
the retained stride keeps the arena and its undo journal within their existing
2MiB reservations. `execFlags@96` is a 1:1 mirror of AccountState flags@+88
(occupied/exists/code-present/created-this-tx/delete-pending/code-resolved/
auth-nonce). Undo push/restore already word-copies +96..+120 field-agnostically;
live writers `.Lawr_store` / `.Lawb_store` are twins and must stay field-identical. -/

/-! ## `account_write_record`

    Fieldwise overlay corresponding to `set_account`
    (`state_tracker.py:486`): `tx_state.account_writes[address] = account`.

    Calling convention:
      a0 = address ptr  (canonical 20 B big-endian) — map key
      a1 = balance ptr  (32 B), valid when mask has BALANCE (VALUE 1)
      a2 = nonce        (u64, BY VALUE), valid when mask has NONCE (VALUE 2)
      a3 = code ptr, valid when mask has CODE (VALUE 4)
      a4 = code length, valid when mask has CODE (VALUE 4)
      a5 = account state (1 = `Some Account`, 0 = spec `None`), valid when STATE (VALUE 8)
      a6 = component-valid mask (VALUES 1|2|4|8|16|32)
      a7 = execFlags word, valid when mask has EXEC_FLAGS (VALUE 16); ignored otherwise
      ra = return
      no result register.

    Targets the TRANSACTION level, which is where the spec's assignment points.
    The block level is filled only by `account_writes_incorporate_tx`.

    Clobbers nothing the caller can see: `t0`-`t6`, `ra` and the argument
    registers it forwards are saved and restored, so this is safe to call from a
    handler `preBody` holding live dispatcher state in caller-saved registers —
    the same contract `storage_write_record` relies on to leave verified
    Programs untouched.

    Convention: real producers already provide canonical BE20, so the map and
    builder keep that form end-to-end. The unused older stack-word API had no
    call sites; retaining it would add a BE→LE→BE round trip and a silent sort
    convention split. Bytes 20..31 remain zero padding. -/
def accountWriteRecordFunction : String :=
  "account_write_record:\n" ++
  "  addi sp, sp, -128\n" ++
  "  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp); sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp); sd ra, 56(sp)\n" ++
  "  sd a0, 64(sp); sd a1, 72(sp); sd a2, 80(sp); sd a3, 88(sp); sd a4, 96(sp); sd a5, 104(sp); sd a6, 112(sp); sd a7, 120(sp)\n" ++
  "  la t0, tx_account_writes_count; ld t1, 0(t0); li t3, 0xa2b20000; li t4, 0\n" ++
  ".Lawr_scan:\n" ++
  "  bgeu t4, t1, .Lawr_append; slli t5, t4, 7; add t5, t3, t5; li t6, 20; mv t2, t5; ld t3, 64(sp)\n" ++
  ".Lawr_cmp:\n" ++
  "  beqz t6, .Lawr_hit; lbu a0, 0(t2); lbu a1, 0(t3); bne a0, a1, .Lawr_next; addi t2, t2, 1; addi t3, t3, 1; addi t6, t6, -1; j .Lawr_cmp\n" ++
  ".Lawr_hit:\n" ++
  "  mv a5, t4; li a6, 0; jal ra, account_writes_undo_push; bnez a0, .Lawr_overflow; j .Lawr_store\n" ++
  ".Lawr_next:\n" ++
  "  la t0, tx_account_writes_count; ld t1, 0(t0); li t3, 0xa2b20000; addi t4, t4, 1; j .Lawr_scan\n" ++
  ".Lawr_append:\n" ++
  "  li t2, " ++ toString txAccountWritesCapacity ++ "; bgeu t1, t2, .Lawr_overflow; mv a5, t1; li a6, 1; jal ra, account_writes_undo_push; bnez a0, .Lawr_overflow\n" ++
  "  la t0, tx_account_writes_count; ld t1, 0(t0); li t3, 0xa2b20000; slli t5, t1, 7; add t5, t3, t5; ld t2, 64(sp); li t6, 20\n" ++
  ".Lawr_copy_addr:\n" ++
  "  beqz t6, .Lawr_zero; lbu t3, 0(t2); sb t3, 0(t5); addi t2, t2, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lawr_copy_addr\n" ++
  ".Lawr_zero:\n" ++
  "  addi t5, t5, -20; sw zero, 20(t5); sd zero, 24(t5); sd zero, 32(t5); sd zero, 40(t5); sd zero, 48(t5); sd zero, 56(t5); sd zero, 64(t5); sd zero, 72(t5); sd zero, 80(t5); sd zero, 88(t5); sd zero, 96(t5); sd zero, 104(t5); sd zero, 112(t5); sd zero, 120(t5); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  ".Lawr_store:\n" ++
  "  ld t2, 112(sp); andi t3, t2, 1; beqz t3, .Lawr_no_balance; ld t3, 72(sp); ld t4, 0(t3); sd t4, 32(t5); ld t4, 8(t3); sd t4, 40(t5); ld t4, 16(t3); sd t4, 48(t5); ld t4, 24(t3); sd t4, 56(t5)\n" ++
  ".Lawr_no_balance:\n" ++
  -- Nonce changes are reduced by maximum in execution-specs
  -- (`block_access_lists.py:440-447`).  A transaction can publish its
  -- inclusion nonce before an EIP-7702 authorization, then publish a later
  -- balance/refund record whose nonce is lower.  Keep the authenticated
  -- higher nonce instead of letting that later row erase it.
  "  andi t3, t2, 2; beqz t3, .Lawr_no_nonce; ld t3, 80(sp); ld t4, 64(t5); bltu t3, t4, .Lawr_no_nonce; sd t3, 64(t5)\n" ++
  ".Lawr_no_nonce:\n" ++
  "  andi t3, t2, 4; beqz t3, .Lawr_no_code; ld t3, 88(sp); sd t3, 80(t5); ld t3, 96(sp); sd t3, 88(t5)\n" ++
  ".Lawr_no_code:\n" ++
  "  andi t3, t2, 8; beqz t3, .Lawr_no_state; ld t3, 104(sp); sd t3, 72(t5)\n" ++
  ".Lawr_no_state:\n" ++
  -- EXEC_FLAGS VALUE 16: replace execFlags@96 from a7 (stack slot 120).
  -- Twin of `.Lawb_store` EXEC_FLAGS arm — keep field handling identical.
  "  andi t3, t2, 16; beqz t3, .Lawr_no_flags; ld t3, 120(sp); sd t3, 96(t5)\n" ++
  ".Lawr_no_flags:\n" ++
  -- TOUCHED VALUE 32 is mask-only (sticky via the OR below); no payload.
  "  ld t3, 112(t5); or t2, t2, t3; sd t2, 112(t5); j .Lawr_done\n" ++
  ".Lawr_overflow:\n" ++
  "  la t0, tx_account_writes_overflow; li t1, 1; sd t1, 0(t0); la t0, account_writes_overflow; sd t1, 0(t0)\n" ++
  ".Lawr_done:\n" ++
  "  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp); ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp); ld ra, 56(sp); addi sp, sp, 128\n" ++
  "  ret\n"

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
  "  li t3, 0xa28a0000\n" ++                                      -- ACCOUNT_WRITES_AREA
  "  li t4, 0\n" ++
  ".Lawb_scan:\n" ++
  "  bgeu t4, t1, .Lawb_append; slli t5, t4, 7; add t5, t3, t5; li t6, 20; mv t2, t5; mv t3, a0\n" ++
  ".Lawb_cmp:\n" ++
  "  beqz t6, .Lawb_store; lbu t1, 0(t2); lbu a1, 0(t3); bne t1, a1, .Lawb_next; addi t2, t2, 1; addi t3, t3, 1; addi t6, t6, -1; j .Lawb_cmp\n" ++
  ".Lawb_next:\n" ++
  "  la t0, account_writes_count; ld t1, 0(t0); li t3, 0xa28a0000; addi t4, t4, 1; j .Lawb_scan\n" ++
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
  "  slli t2, s3, 7; li t3, 0xa2b20000; add t2, t3, t2; mv t3, t2; mv t4, s0; li t5, 20\n" ++
  ".Lawd_cmp:\n" ++
  "  beqz t5, .Lawd_hit; lbu t6, 0(t3); lbu a0, 0(t4); bne t6, a0, .Lawd_next; addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lawd_cmp\n" ++
  ".Lawd_next:\n" ++
  "  addi s3, s3, 1; j .Lawd_tx_loop\n" ++
  ".Lawd_hit:\n" ++
  "  mv a5, s3; li a6, 0; jal ra, account_writes_undo_push; bnez a0, .Lawd_overflow\n" ++
  -- clear_account_preserving_balance then EIP-161 empty → destroy_account(None).
  "  slli t0, s3, 7; li t1, 0xa2b20000; add t0, t1, t0; sd zero, 64(t0); sd zero, 80(t0); sd zero, 88(t0); sd zero, 96(t0); sd zero, 104(t0)\n" ++
  "  ld t1, 32(t0); ld t2, 40(t0); or t1, t1, t2; ld t2, 48(t0); or t1, t1, t2; ld t2, 56(t0); or t1, t1, t2; bnez t1, .Lawd_keep_present\n" ++
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

/-! ## `account_writes_is_absent`

    Three-state read of `account_writes` matching
    `get_account_optional` (state_tracker.py:199-203), GH #11328 / PR #11453:

    | map state                         | a0 out | meaning                                      |
    |-----------------------------------|--------|----------------------------------------------|
    | key **missing**                   | 0      | unknown here — caller falls through          |
    | key present, `optionalState@72=0` | 1      | **destroyed** (Present-None tombstone)       |
    | key present, `optionalState@72=1` | 0      | Present Account (or STATE bit unset → not None) |

    Scans tx map first, then block-cumulative.  Only a **present** row with
    STATE valid and `optionalState@72 = 0` returns 1.  Missing row and Present
    Account both return 0 — they are **not** conflated with Present-None.

    **Same-tx completeness (coord Q on #11453):** Present-None is stamped by
    `account_writes_apply_deletes` at the **tx boundary** (spec
    `destroy_account` after `accounts_to_delete`).  Mid-tx create+SD still
    leaves an empty-code account until finalize (EIP-1052 EMPTY_CODE_HASH,
    not 0).  That mid-tx flag is still `evm_selfdestruct_destroyed_table`; it
    is **not** the same fact as Present-None (0 after finalize).  Table stays
    until mid-tx empty-code is carried by Present Account without a side list.
    ANSWER: tombstone read is genuine for Present-None; same-tx EMPTY_CODE_HASH
    is a different obligation — table not yet redundant.

    a0 = address ptr (20 B BE).  Clobbers t0-t6 and a1/a2. -/
def accountWritesIsAbsentFunction : String :=
  "account_writes_is_absent:\n" ++
  "  la t0, tx_account_writes_count; ld t1, 0(t0); li t2, 0xa2b20000; li t3, 0\n" ++
  ".Lawa_tx_scan:\n" ++
  "  bgeu t3, t1, .Lawa_block; slli t4, t3, 7; add t4, t2, t4; li t5, 20; mv t6, t4; mv t0, a0\n" ++
  ".Lawa_tx_cmp:\n" ++
  "  beqz t5, .Lawa_tx_hit; lbu a1, 0(t6); lbu a2, 0(t0); bne a1, a2, .Lawa_tx_next; addi t6, t6, 1; addi t0, t0, 1; addi t5, t5, -1; j .Lawa_tx_cmp\n" ++
  ".Lawa_tx_next:\n" ++
  "  addi t3, t3, 1; j .Lawa_tx_scan\n" ++
  ".Lawa_tx_hit:\n" ++
  "  ld t0, 112(t4); andi t0, t0, 8; beqz t0, .Lawa_no; ld t0, 72(t4); beqz t0, .Lawa_yes; j .Lawa_no\n" ++
  ".Lawa_block:\n" ++
  "  la t0, account_writes_count; ld t1, 0(t0); li t2, 0xa28a0000; li t3, 0\n" ++
  ".Lawa_blk_scan:\n" ++
  "  bgeu t3, t1, .Lawa_no; slli t4, t3, 7; add t4, t2, t4; li t5, 20; mv t6, t4; mv t0, a0\n" ++
  ".Lawa_blk_cmp:\n" ++
  "  beqz t5, .Lawa_blk_hit; lbu a1, 0(t6); lbu a2, 0(t0); bne a1, a2, .Lawa_blk_next; addi t6, t6, 1; addi t0, t0, 1; addi t5, t5, -1; j .Lawa_blk_cmp\n" ++
  ".Lawa_blk_next:\n" ++
  "  addi t3, t3, 1; j .Lawa_blk_scan\n" ++
  ".Lawa_blk_hit:\n" ++
  "  ld t0, 112(t4); andi t0, t0, 8; beqz t0, .Lawa_no; ld t0, 72(t4); beqz t0, .Lawa_yes\n" ++
  ".Lawa_no:\n" ++
  "  li a0, 0; ret\n" ++
  ".Lawa_yes:\n" ++
  "  li a0, 1; ret\n"

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
def accountWritesEmitBuilderTxFunction : String :=
  "account_writes_emit_builder_tx:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  la t0, current_block_access_index; ld s7, 0(t0); la s0, tx_account_writes_count; ld s1, 0(s0); li s2, 0xa2b20000; li s3, 0\n" ++
  ".Laweb_loop:\n" ++
  "  bgeu s3, s1, .Laweb_done; slli t0, s3, 7; add s4, s2, t0\n" ++
  -- Find this address in the block-cumulative map.  A hit may still lack an
  -- individual field, in which case that component keeps the pre-state base.
  "  la t0, account_writes_count; ld t1, 0(t0); li t2, 0xa28a0000; li t3, 0; li s5, 0\n" ++
  ".Laweb_scan:\n" ++
  "  bgeu t3, t1, .Laweb_header; slli t4, t3, 7; add t5, t2, t4; li t6, 20; mv a0, t5; mv a1, s4\n" ++
  ".Laweb_cmp:\n" ++
  "  beqz t6, .Laweb_hit; lbu a2, 0(a0); lbu a3, 0(a1); bne a2, a3, .Laweb_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Laweb_cmp\n" ++
  ".Laweb_next:\n" ++
  "  addi t3, t3, 1; j .Laweb_scan\n" ++
  ".Laweb_hit:\n" ++
  "  mv s5, t5; j .Laweb_header\n" ++
  -- Always materialise the parent-state account.  It is the fallback for a
  -- whole-map miss and for individual components not carried by a fieldwise
  -- block-map overlay.
  ".Laweb_header:\n" ++
  "  bnez s5, .Laweb_parent\n" ++
  ".Laweb_parent:\n" ++
  "  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0); mv a2, s4; li a3, 20; la t0, bv_witness_state_ptr; ld a4, 0(t0); la t0, bv_witness_state_len; ld a5, 0(t0); la a6, account_builder_pre_account; jal ra, account_at_header_state_root; sd a0, 80(sp)\n" ++
  -- The resolver is the single balance/nonce baseline implementation.  The
  -- local scan below remains only to select the block-map code hash record;
  -- code has a different variable-width representation and is not part of
  -- account_resolve_pre_state's fixed account scratch output.
  "  mv a0, s4; la a1, account_builder_pre_account; la t0, sv_pre_rlp_ptr; ld a2, 0(t0); la t0, sv_pre_rlp_len; ld a3, 0(t0); la t0, bv_witness_state_ptr; ld a4, 0(t0); la t0, bv_witness_state_len; ld a5, 0(t0); jal ra, account_resolve_pre_state\n" ++
  "  ld s8, 112(s4)\n" ++
  -- Balance: the resolver has already materialised the block/durable/header
  -- precedence into the shared account scratch.
  "  andi t0, s8, 1; bnez t0, .Laweb_balance_have; j .Laweb_nonce\n" ++
  ".Laweb_balance_have:\n" ++
  -- Diagnostic cell (bald_*): the producer bit as OBSERVED here, one increment
  -- per account-loop iteration whose mask carries balance.  Placed past the
  -- label so it is inside the block the branch selects; t0/t1 are dead (t0 held
  -- the `andi` result already consumed by the `bnez`).
  "  la t0, bald_bal_bit_set; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  la s6, account_builder_pre_account; addi s6, s6, 8\n" ++
  ".Laweb_balance_cmp:\n" ++
  -- The final `beq` is RELABELLED to the witness block rather than having a probe
  -- spliced into the equal path: the branch already exists, so relabelling cannot
  -- change which comparisons are made, and `bit_set = eq + ne` is the built-in
  -- check that the relabel did not lose a path.
  "  ld t0, 0(s6); ld t1, 32(s4); bne t0, t1, .Laweb_balance_emit; ld t0, 8(s6); ld t1, 40(s4); bne t0, t1, .Laweb_balance_emit; ld t0, 16(s6); ld t1, 48(s4); bne t0, t1, .Laweb_balance_emit; ld t0, 24(s6); ld t1, 56(s4); beq t0, t1, .Laweb_bal_eq\n" ++
  "  li t0, 4; bgeu s3, t0, .Laweb_balance_trace_done; li t0, 96; mul t0, s3, t0; la t1, account_builder_diag_balance_pairs; add t1, t1, t0\n" ++
  "  ld t0, 0(s4); sd t0, 0(t1); ld t0, 8(s4); sd t0, 8(t1); ld t0, 16(s4); sd t0, 16(t1); ld t0, 24(s4); sd t0, 24(t1)\n" ++
  "  ld t0, 0(s6); sd t0, 32(t1); ld t0, 8(s6); sd t0, 40(t1); ld t0, 16(s6); sd t0, 48(t1); ld t0, 24(s6); sd t0, 56(t1)\n" ++
  "  ld t0, 32(s4); sd t0, 64(t1); ld t0, 40(s4); sd t0, 72(t1); ld t0, 48(s4); sd t0, 80(t1); ld t0, 56(s4); sd t0, 88(t1)\n" ++
  ".Laweb_balance_trace_done:\n" ++
  "  ld t0, 0(s6); ld t1, 32(s4); bne t0, t1, .Laweb_balance_emit; ld t0, 8(s6); ld t1, 40(s4); bne t0, t1, .Laweb_balance_emit; ld t0, 16(s6); ld t1, 48(s4); bne t0, t1, .Laweb_balance_emit; ld t0, 24(s6); ld t1, 56(s4); beq t0, t1, .Laweb_nonce\n" ++
  ".Laweb_balance_emit:\n" ++
  -- Diagnostic cell: the compare found inequality, so the append is CALLED.
  -- bit_set minus differs is exactly the "compare found equality" population
  -- (cause 2); differs minus builder_count is an append that did not land.
  "  la t0, bald_bal_differs; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  la t0, bald_bal_ne_bai_mask; ld t1, 0(t0); li t2, 1; sll t2, t2, s7; or t1, t1, t2; sd t1, 0(t0)\n" ++
  "  mv a0, s4; mv a1, s7; addi a2, s4, 32; jal ra, bal_builder_append_balance\n" ++
  -- Jump over the witness block; falling through would run it on the append path.
  "  j .Laweb_nonce\n" ++
  ".Laweb_bal_eq:\n" ++
  "  la t0, bald_bal_eq_bai_mask; ld t1, 0(t0); li t2, 1; sll t2, t2, s7; or t1, t1, t2; sd t1, 0(t0)\n" ++
  "  ld t1, 0(s6); la t0, bald_bal_eq_val_lo; sd t1, 0(t0); ld t1, 24(s6); la t0, bald_bal_eq_val_hi; sd t1, 0(t0)\n" ++
  "  ld t1, 0(s4); la t0, bald_bal_eq_addr_a; sd t1, 0(t0); ld t1, 8(s4); la t0, bald_bal_eq_addr_b; sd t1, 0(t0)\n" ++
  -- Nonce: read the resolver's canonical pre-state scratch.
  ".Laweb_nonce:\n" ++
  "  andi t0, s8, 2; bnez t0, .Laweb_nonce_have; j .Laweb_code\n" ++
  ".Laweb_nonce_have:\n" ++
  -- Diagnostic cell, before the `la t0` that this block needs: t1 is dead here
  -- and is reloaded by `.Laweb_nonce_cmp` below.
  "  la t0, bald_non_bit_set; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  la t0, account_builder_pre_account; ld t0, 0(t0)\n" ++
  ".Laweb_nonce_cmp:\n" ++
  -- The nonce differs-cell must sit AFTER the skip-on-equal branch, so it counts
  -- appends and not bit-set accounts.  t5/t6 rather than t0/t1: t0 carries the
  -- resolver's pre-state nonce and t1 the post value passed as a2.
  "  ld t1, 64(s4); beq t0, t1, .Laweb_non_eq; la t5, bald_non_differs; ld t6, 0(t5); addi t6, t6, 1; sd t6, 0(t5); la t5, bald_non_ne_bai_mask; ld t6, 0(t5); li t3, 1; sll t3, t3, s7; or t6, t6, t3; sd t6, 0(t5); mv a0, s4; mv a1, s7; mv a2, t1; jal ra, bal_builder_append_nonce\n" ++
  "  j .Laweb_code\n" ++
  -- Witness block for the equal path.  t0 is the resolver's pre nonce and t1 the
  -- post read from 64(s4); both are published even though they are equal here,
  -- because the pair distinguishes "both zero, so the post was never staged" from
  -- "the pre side already carries the post value".
  ".Laweb_non_eq:\n" ++
  "  la t2, bald_non_eq_bai_mask; ld t3, 0(t2); li t4, 1; sll t4, t4, s7; or t3, t3, t4; sd t3, 0(t2)\n" ++
  "  la t2, bald_non_eq_val_pre; sd t0, 0(t2); la t2, bald_non_eq_val_post; sd t1, 0(t2)\n" ++
  "  li t2, 4; bgeu s3, t2, .Laweb_nonce_trace_done; li t2, 48; mul t2, s3, t2; la t3, account_builder_diag_nonce_pairs; add t3, t3, t2\n" ++
  "  ld t2, 0(s4); sd t2, 0(t3); ld t2, 8(s4); sd t2, 8(t3); ld t2, 16(s4); sd t2, 16(t3); ld t2, 24(s4); sd t2, 24(t3); sd t0, 32(t3); ld t2, 64(s4); sd t2, 40(t3)\n" ++
  ".Laweb_nonce_trace_done:\n" ++
  "  ld t1, 64(s4); beq t0, t1, .Laweb_code; mv a0, s4; mv a1, s7; mv a2, t1; jal ra, bal_builder_append_nonce\n" ++
  -- Code compares hashes, never code pointer/length identity.  The header
  -- reader zeroes its output on authenticated absence, so select the canonical
  -- EMPTY_CODE_HASH in that one case.
  ".Laweb_code:\n" ++
  "  andi t0, s8, 4; bnez t0, .Laweb_code_have; j .Laweb_advance\n" ++
  ".Laweb_code_have:\n" ++
  "  ld a0, 80(s4); ld a1, 88(s4); la a2, account_builder_post_code_hash; jal ra, zkvm_keccak256\n" ++
  "  beqz s5, .Laweb_code_header; ld t0, 112(s5); andi t0, t0, 4; beqz t0, .Laweb_code_header; ld a0, 80(s5); ld a1, 88(s5); la a2, account_builder_block_code_hash; jal ra, zkvm_keccak256; la s6, account_builder_block_code_hash; j .Laweb_code_cmp\n" ++
  ".Laweb_code_header:\n" ++
  "  ld t0, 80(sp); li t1, 1; beq t0, t1, .Laweb_code_absent; la s6, account_builder_pre_account; addi s6, s6, 72; j .Laweb_code_cmp\n" ++
  ".Laweb_code_absent:\n" ++
  "  la s6, chahsr_empty_code_hash\n" ++
  ".Laweb_code_cmp:\n" ++
  "  la t0, account_builder_post_code_hash; ld t1, 0(t0); ld t2, 0(s6); bne t1, t2, .Laweb_code_emit; ld t1, 8(t0); ld t2, 8(s6); bne t1, t2, .Laweb_code_emit; ld t1, 16(t0); ld t2, 16(s6); bne t1, t2, .Laweb_code_emit; ld t1, 24(t0); ld t2, 24(s6); beq t1, t2, .Laweb_advance\n" ++
  ".Laweb_code_emit:\n" ++
  "  mv a0, s4; mv a1, s7; ld a2, 80(s4); ld a3, 88(s4); jal ra, bal_builder_append_code\n" ++
  ".Laweb_advance:\n" ++
  "  addi s3, s3, 1; j .Laweb_loop\n" ++
  ".Laweb_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); addi sp, sp, 112; ret\n"

def accountWritesIncorporateTxFunction : String :=
  "account_writes_incorporate_tx:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  la s0, tx_account_writes_count; ld s1, 0(s0)\n" ++            -- s1 = tx count
  "  li s2, 0xa2b20000\n" ++                                       -- s2 = tx area
  "  li s3, 0\n" ++                                                -- s3 = i
  ".Lawi_loop:\n" ++
  "  bgeu s3, s1, .Lawi_clear\n" ++
  "  slli a0, s3, 7; add a0, s2, a0\n" ++
  ".Lawi_merge:\n" ++
  "  jal ra, account_writes_block_upsert\n" ++
  ".Lawi_next:\n" ++
  "  addi s3, s3, 1; j .Lawi_loop\n" ++
  ".Lawi_clear:\n" ++
  -- state_tracker.py:874 `tx_state.account_writes.clear()`. The undo journal is
  -- reset with it: its entries index the tx-level map, so they are meaningless
  -- once that map is empty, and a stale mark would unwind the NEXT transaction's
  -- writes against the previous one's indices.
  "  la s0, tx_account_writes_count; sd zero, 0(s0)\n" ++
  "  la s0, tx_account_writes_overflow; sd zero, 0(s0)\n" ++
  "  la s0, account_writes_undo_count; sd zero, 0(s0)\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret\n"

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
def accountResolvePreStateFunction : String :=
  "account_resolve_pre_state:\n" ++
  -- Keep a separate frame-local output for the parent lookup.  A sparse
  -- block-map row may already have supplied balance or nonce; using
  -- `account_builder_pre_account` as the header lookup output would clobber
  -- that field before `.Larp_header_found` sees its valid bit.  This is the
  -- same frame-local scratch idiom used by the selfdestruct header fallback.
  "  addi sp, sp, -208\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; li s7, 0\n" ++
  "  sd zero, 0(s1); sd zero, 8(s1); sd zero, 16(s1); sd zero, 24(s1); sd zero, 32(s1)\n" ++
  -- First source: block-cumulative account_writes. It is the pre-tx
  -- baseline for the current transaction, not the immutable parent account.
  "  la t0, account_writes_count; ld t1, 0(t0); li t2, 0xa28a0000; li t3, 0\n" ++
  ".Larp_block_scan:\n" ++
  "  bgeu t3, t1, .Larp_block_done; slli t4, t3, 7; add t5, t2, t4; li t6, 20; mv a0, t5; mv a1, s0\n" ++
  ".Larp_block_cmp:\n" ++
  "  beqz t6, .Larp_block_hit; lbu a2, 0(a0); lbu a3, 0(a1); bne a2, a3, .Larp_block_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Larp_block_cmp\n" ++
  ".Larp_block_next:\n" ++
  "  addi t3, t3, 1; j .Larp_block_scan\n" ++
  ".Larp_block_hit:\n" ++
  "  mv s6, t5; ld t0, 112(s6); andi t1, t0, 1; beqz t1, .Larp_block_nonce; ld t1, 32(s6); sd t1, 8(s1); ld t1, 40(s6); sd t1, 16(s1); ld t1, 48(s6); sd t1, 24(s1); ld t1, 56(s6); sd t1, 32(s1); ori s7, s7, 1\n" ++
  ".Larp_block_nonce:\n" ++
  "  andi t1, t0, 2; beqz t1, .Larp_block_done; ld t1, 64(s6); sd t1, 0(s1); ori s7, s7, 2\n" ++
  ".Larp_block_done:\n" ++
  -- There is NO second source.  `_get_pre_tx_account`
  -- (`block_access_lists.py:583-598`) has exactly TWO tiers -- the cumulative
  -- `pre_tx_accounts` map, then `pre_state.get_account_optional(address)` -- and
  -- `pre_state` is the IMMUTABLE PRE-BLOCK state.
  --
  -- This routine used to consult the durable `AccountState` overlay in between.
  -- That overlay is LIVE MUTATED STATE: `update_builder_from_tx` runs at the
  -- transaction boundary, by which point the sender's gas debit and nonce
  -- increment have already been applied to it.  So for an account with NO
  -- block-map row -- i.e. its first touch in the block -- the overlay returned the
  -- POST value as the "pre" value, the caller's change-compare found equality,
  -- and the row was silently dropped.  Measured on six EIP-7928 fixtures: the
  -- nonce deficit equalled the number of distinct senders on all six, and on
  -- multi-tx-same-sender blocks the sender's LATER rows appended correctly
  -- (`ne_bai_mask = {2,3}`) because from the second transaction on the block map
  -- hits and supplies a genuine pre value.  See GH #10799.
  --
  -- Falling straight through to the authenticated parent witness is what the spec
  -- says and is also correct on its own terms: if no earlier transaction in this
  -- block touched the account, its pre-transaction state IS the parent state.
  ".Larp_header_done:\n" ++
  "  li t0, 3; beq s7, t0, .Larp_ok\n" ++
  -- Final source: authenticated parent witness. Absence is a valid zero
  -- account; only malformed lookup errors fail closed.
  "  mv a0, s2; mv a1, s3; mv a2, s0; li a3, 20; mv a4, s4; mv a5, s5; addi a6, sp, 96; jal ra, account_at_header_state_root_tracked\n" ++
  "  li t0, 1; bgtu a0, t0, .Larp_fail; beqz a0, .Larp_header_found; j .Larp_ok\n" ++
  ".Larp_header_found:\n" ++
  "  andi t1, s7, 1; bnez t1, .Larp_header_nonce; addi t0, sp, 96; ld t1, 8(t0); sd t1, 8(s1); ld t1, 16(t0); sd t1, 16(s1); ld t1, 24(t0); sd t1, 24(s1); ld t1, 32(t0); sd t1, 32(s1); ori s7, s7, 1\n" ++
  ".Larp_header_nonce:\n" ++
  "  andi t1, s7, 2; bnez t1, .Larp_ok; addi t0, sp, 96; ld t1, 0(t0); sd t1, 0(s1); ori s7, s7, 2\n" ++
  ".Larp_ok:\n" ++
  "  li a0, 0; j .Larp_ret\n" ++
  ".Larp_fail:\n" ++
  "  li a0, 1\n" ++
  ".Larp_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); addi sp, sp, 208; ret\n"

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
def accountResolveExecutionStateFunction : String :=
  "account_resolve_execution_state:\n" ++
  "  addi sp, sp, -208\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; mv s6, a6; mv s7, a7; li s8, 0\n" ++
  -- Amsterdam's get_account_optional records the account read before resolving
  -- any of its three tiers.  CREATE is the current sole consumer of this
  -- resolver, so keep the call unconditional at the lookup boundary rather
  -- than attaching it to a particular map-hit or success arm.
  "  mv a0, s0; jal ra, account_read_record\n" ++
  "  sd zero, 0(s1); sd zero, 8(s1); sd zero, 16(s1); sd zero, 24(s1); sd zero, 32(s1); sd zero, 40(s1); sd zero, 48(s1); sd zero, 56(s1)\n" ++
  -- First source: the current transaction's account_writes map.  A valid
  -- component in this keyed overlay is the execution-time value and must win
  -- over both the prior block state and the authenticated parent.
  "  la t0, tx_account_writes_count; ld t1, 0(t0); li t2, 0xa2b20000; li t3, 0\n" ++
  ".Lare_tx_scan:\n" ++
  "  bgeu t3, t1, .Lare_tx_done; slli t4, t3, 7; add t5, t2, t4; li t6, 20; mv a0, t5; mv a1, s0\n" ++
  ".Lare_tx_cmp:\n" ++
  "  beqz t6, .Lare_tx_hit; lbu a2, 0(a0); lbu a3, 0(a1); bne a2, a3, .Lare_tx_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Lare_tx_cmp\n" ++
  ".Lare_tx_next:\n" ++
  "  addi t3, t3, 1; j .Lare_tx_scan\n" ++
  ".Lare_tx_hit:\n" ++
  "  mv t6, t5; ld t0, 112(t6); andi t1, t0, 1; beqz t1, .Lare_tx_nonce; ld t1, 32(t6); sd t1, 8(s1); ld t1, 40(t6); sd t1, 16(s1); ld t1, 48(t6); sd t1, 24(s1); ld t1, 56(t6); sd t1, 32(s1); ori s8, s8, 1\n" ++
  ".Lare_tx_nonce:\n" ++
  "  andi t1, t0, 2; beqz t1, .Lare_tx_code; ld t1, 64(t6); sd t1, 0(s1); ori s8, s8, 2\n" ++
  ".Lare_tx_code:\n" ++
  "  andi t1, t0, 4; beqz t1, .Lare_tx_state; ld t1, 80(t6); sd t1, 40(s1); ld t1, 88(t6); sd t1, 48(s1); li t1, 1; sd t1, 56(s1); ori s8, s8, 4\n" ++
  ".Lare_tx_state:\n" ++
  "  andi t1, t0, 8; beqz t1, .Lare_tx_done; ld t1, 72(t6); sd t1, 56(s1); ori s8, s8, 8\n" ++
  ".Lare_tx_done:\n" ++
  -- A present-None transaction row is a terminal tombstone.  Only a missing
  -- key falls through to the lower tiers; the state bit is therefore checked
  -- before the block/parent scans.
  "  andi t0, s8, 8; beqz t0, .Lare_block_scan\n" ++
  "  ld t1, 56(s1); beqz t1, .Lare_deleted\n" ++
  ".Lare_block_scan:\n" ++
  "  la t0, account_writes_count; ld t1, 0(t0); li t2, 0xa28a0000; li t3, 0\n" ++
  ".Lare_block_loop:\n" ++
  "  bgeu t3, t1, .Lare_block_done; slli t4, t3, 7; add t5, t2, t4; li t6, 20; mv a0, t5; mv a1, s0\n" ++
  ".Lare_block_cmp:\n" ++
  "  beqz t6, .Lare_block_hit; lbu a2, 0(a0); lbu a3, 0(a1); bne a2, a3, .Lare_block_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Lare_block_cmp\n" ++
  ".Lare_block_next:\n" ++
  "  addi t3, t3, 1; j .Lare_block_loop\n" ++
  ".Lare_block_hit:\n" ++
  -- Transaction writes take precedence over block-cumulative writes.  In
  -- particular, do not let a block row overwrite a code or state value that
  -- was already supplied by the current transaction tier.
  "  mv t6, t5; ld t0, 112(t6); andi t1, s8, 4; bnez t1, .Lare_block_state; andi t1, t0, 4; beqz t1, .Lare_block_state; ld t1, 80(t6); sd t1, 40(s1); ld t1, 88(t6); sd t1, 48(s1); li t1, 1; sd t1, 56(s1); ori s8, s8, 4\n" ++
  ".Lare_block_state:\n" ++
  "  andi t1, s8, 8; bnez t1, .Lare_block_done; andi t1, t0, 8; beqz t1, .Lare_block_done; ld t1, 72(t6); sd t1, 56(s1); ori s8, s8, 8\n" ++
  ".Lare_block_done:\n" ++
  "  andi t0, s8, 8; beqz t0, .Lare_parent\n" ++
  "  ld t1, 56(s1); beqz t1, .Lare_deleted\n" ++
  -- A code component in either execution map is already a truthful pointer/
  -- length.  Do not look it up again: the map writer supplied the actual
  -- bytes, including an EF0100 delegation designator when one is present.
  "  andi t0, s8, 4; bnez t0, .Lare_classify_code\n" ++
  ".Lare_parent:\n" ++
  -- The existing pre-state resolver supplies nonce/balance with the BAL
  -- two-tier contract.  Code is resolved separately below from the raw parent
  -- account and witness.codes table.
  "  mv a0, s0; addi a1, sp, 96; mv a2, s2; mv a3, s3; mv a4, s4; mv a5, s5; jal ra, account_resolve_pre_state\n" ++
  "  bnez a0, .Lare_malformed\n" ++
  "  andi t0, s8, 1; bnez t0, .Lare_nonce\n" ++
  "  addi t1, sp, 96; ld t2, 8(t1); sd t2, 8(s1); ld t2, 16(t1); sd t2, 16(s1); ld t2, 24(t1); sd t2, 24(s1); ld t2, 32(t1); sd t2, 32(s1); ori s8, s8, 1\n" ++
  ".Lare_nonce:\n" ++
  "  andi t0, s8, 2; bnez t0, .Lare_code_source; addi t1, sp, 96; ld t2, 0(t1); sd t2, 0(s1); ori s8, s8, 2\n" ++
  -- The authenticated account output is the only source of code_hash.  It is
  -- deliberately the tracked account read, while the code preimage lookup is
  -- the raw witness helper so this resolver does not mutate code_reads.
  ".Lare_code_source:\n" ++
  "  andi t0, s8, 4; bnez t0, .Lare_classify_code\n" ++
  "  mv a0, s2; mv a1, s3; mv a2, s0; li a3, 20; mv a4, s4; mv a5, s5; addi a6, sp, 96; jal ra, account_at_header_state_root_tracked\n" ++
  "  beqz a0, .Lare_parent_found; li t0, 1; beq a0, t0, .Lare_absent; j .Lare_malformed\n" ++
  ".Lare_parent_found:\n" ++
  "  andi t0, s8, 8; bnez t0, .Lare_code_hash; addi t3, sp, 96; ld t1, 0(t3); sd t1, 0(s1); ld t1, 8(t3); sd t1, 8(s1); ld t1, 16(t3); sd t1, 16(s1); ld t1, 24(t3); sd t1, 24(s1); ld t1, 32(t3); sd t1, 32(s1); li t1, 1; sd t1, 56(s1); ori s8, s8, 3\n" ++
  ".Lare_code_hash:\n" ++
  "  addi t3, sp, 96; la t0, chahsr_empty_code_hash; ld t1, 72(t3); ld t2, 0(t0); bne t1, t2, .Lare_hash_nonempty; ld t1, 80(t3); ld t2, 8(t0); bne t1, t2, .Lare_hash_nonempty; ld t1, 88(t3); ld t2, 16(t0); bne t1, t2, .Lare_hash_nonempty; ld t1, 96(t3); ld t2, 24(t0); bne t1, t2, .Lare_hash_nonempty; j .Lare_empty\n" ++
  ".Lare_hash_nonempty:\n" ++
  "  mv a0, s6; mv a1, s7; addi a2, sp, 168; addi a3, sp, 80; addi a4, sp, 88; sd zero, 80(sp); sd zero, 88(sp); jal ra, witness_codes_lookup_by_hash\n" ++
  "  bnez a0, .Lare_unavailable; ld t0, 80(sp); add t0, s6, t0; sd t0, 40(s1); ld t1, 88(sp); sd t1, 48(s1); j .Lare_classify_code\n" ++
  -- Prefix recognition is intentionally independent of length.  Both branches
  -- preserve the returned bytes; dispatch follows EF0100 designators later.
  ".Lare_classify_code:\n" ++
  "  ld t0, 48(s1); li t1, 3; bltu t0, t1, .Lare_classify_plain; ld t0, 40(s1); lbu t1, 0(t0); li t2, 0xef; bne t1, t2, .Lare_classify_plain; lbu t1, 1(t0); li t2, 1; bne t1, t2, .Lare_classify_plain; lbu t1, 2(t0); bnez t1, .Lare_classify_plain; j .Lare_classify_marker\n" ++
  ".Lare_classify_marker:\n" ++
  "  li a0, 1; j .Lare_ret\n" ++
  ".Lare_classify_plain:\n" ++
  "  ld t0, 48(s1); beqz t0, .Lare_empty; li a0, 1; j .Lare_ret\n" ++
  ".Lare_empty:\n" ++
  "  sd zero, 40(s1); sd zero, 48(s1); li a0, 2; j .Lare_ret\n" ++
  ".Lare_absent:\n" ++
  "  andi t0, s8, 8; beqz t0, .Lare_absent_zero; ld t1, 56(s1); bnez t1, .Lare_empty\n" ++
  ".Lare_absent_zero:\n" ++
  "  sd zero, 40(s1); sd zero, 48(s1); li a0, 0; j .Lare_ret\n" ++
  ".Lare_deleted:\n" ++
  "  sd zero, 40(s1); sd zero, 48(s1); li a0, 3; j .Lare_ret\n" ++
  ".Lare_unavailable:\n" ++
  "  sd zero, 40(s1); sd zero, 48(s1); li a0, 4; j .Lare_ret\n" ++
  ".Lare_malformed:\n" ++
  "  sd zero, 40(s1); sd zero, 48(s1); li a0, 5\n" ++
  ".Lare_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); addi sp, sp, 208; ret\n"

/-! ## `account_writes_discard_tx` — REMOVED from guest (#11202)

    Never jal'd. Storage twin `write_sets_discard_tx` is live on status=0.
    Account path always `emit`+`incorporate` after presumed body restore.
    Issue #11202 carries the open question (benign dead twin vs missing
    fail-discard wiring). Do not resurrect without wiring a real fail path. -/

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

/-- Data symbols for the two `account_writes` levels and the undo journal.
    The arenas themselves are NOBITS regions declared in `MemoryLayout`; only
    the counters and flags live in `.data`. -/
def accountWriteMapDataSection : String :=
  "account_writes_count:\n  .zero 8\n" ++
  "account_writes_overflow:\n  .zero 8\n" ++
  "tx_account_writes_count:\n  .zero 8\n" ++
  "tx_account_writes_overflow:\n  .zero 8\n" ++
  "account_writes_undo_count:\n  .zero 8\n"

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
  "account_write_e2e_bal:\n  .zero 32\n"

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
  "  li t3, 0xa2b20000; lbu t0, 112(t3); sd t0, 0(s0); ld t0, 96(t3); sd t0, 8(s0)\n" ++
  -- 2) twin same-addr BALANCE-only write (no TOUCHED in mask) — sticky must keep 32
  "  la t0, account_write_e2e_bal; li t1, 7; sb t1, 31(t0)\n" ++
  "  la a0, account_write_e2e_addr; la a1, account_write_e2e_bal; li a2, 0; li a3, 0; li a4, 0; li a5, 0\n" ++
  "  li a6, " ++ toString accountWriteHasBalance ++ "; li a7, 0\n" ++
  "  jal ra, account_write_record\n" ++
  "  li t3, 0xa2b20000; lbu t0, 112(t3); sd t0, 16(s0)\n" ++
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
    `account_writes_block_upsert`, so all five must be emitted together. -/
def accountWriteMapFunctions : String :=
  accountWriteRecordFunction ++
  accountWritesBlockUpsertFunction ++
  accountWritesApplyDeletesFunction ++
  accountWritesIsAbsentFunction ++
  accountWritesEmitBuilderTxFunction ++
  accountWritesIncorporateTxFunction ++
  accountWritesUndoPushFunction ++
  accountWritesRestoreFrameFunction ++
  accountResolvePreStateFunction ++
  accountResolveExecutionStateFunction

/-! ## Structural guards

    `#guard`s in `EvmAsm.Codegen`, the namespace the definitions above live in --
    NOT the file path. A guard opened on the wrong namespace has its identifiers
    auto-bound as implicits and passes while checking nothing, so the layout
    constants are written FULLY QUALIFIED here rather than via `open ... in`.

    Each guard is a SINGLE LINE. A `#guard` whose expression wraps onto a second
    line parses the continuation as a new command, and the guard silently covers
    only the first line -- which is the same vacuous-pass failure one level down. -/

-- The three arenas are laid end to end and must not overlap.
#guard EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat + 0x280000 == EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat
#guard EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat + 0x200000 == EvmAsm.Stateless.ACCOUNT_WRITES_UNDO_AREA.toNat
-- ...and all three fit below `.data` at 0xa3000000.
#guard EvmAsm.Stateless.ACCOUNT_WRITES_UNDO_AREA.toNat + 0x200000 <= 0xa3000000
-- The block-level arena starts where the storage-write undo journal ends
-- (0xa23a0000 + 5 MiB), so the new regions are contiguous with the existing ones
-- rather than leaving an unaccounted hole in working RAM.
#guard EvmAsm.Stateless.STORAGE_WRITES_UNDO_AREA.toNat + 0x500000 == EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat

-- Capacity x stride must equal the reserved arena exactly: an arena larger than
-- its reservation would run into the next region with nothing objecting.
#guard txAccountWritesCapacity * 128 == 0x200000
#guard blockAccountWritesCapacity * 128 == 0x280000
-- Transaction capacity retains physical parity with the storage map; block
-- capacity follows the independent distinct-account bound below.
#guard txAccountWritesCapacity == storageWritesCapacity
#guard accountWritesCallKeyBound == 15038
#guard accountWritesCallKeyBound <= txAccountWritesCapacity
#guard 19047 <= blockAccountWritesCapacity

-- Every routine must actually be emitted. This slice is inert, so nothing calls
-- them yet and a missing one would NOT be a link error -- these guards are the
-- only thing that would catch it.
#guard (accountWriteMapFunctions.splitOn "account_write_record:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_block_upsert:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_emit_builder_tx:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_incorporate_tx:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_apply_deletes:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_is_absent:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_discard_tx:").length == 1
-- GH #10810: the callee must preserve t5/t6, because `account_write_record`'s hit path holds the
-- target row address in t5 ACROSS this call. Pin the save AND the restore: a prologue-only save
-- would leave the register clobbered on return and read as a fix.
#guard (accountWritesUndoPushFunction.splitOn "sd t5, 40(sp); sd t6, 48(sp)").length == 2
#guard (accountWritesUndoPushFunction.splitOn "ld t5, 40(sp); ld t6, 48(sp)").length == 2
#guard (accountWriteRecordFunction.splitOn "bnez a0, .Lawr_overflow").length == 3
#guard (accountWritesUndoPushFunction.splitOn "bgeu t1, t2, .Lawu_fail").length == 2
#guard (accountWritesUndoPushFunction.splitOn ".Lawu_fail:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_undo_push:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_restore_frame:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_resolve_pre_state:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_resolve_execution_state:").length == 2
-- Part two must use the raw witness-code lookup, not `code_read_fetch`, whose
-- side effect records a code read and therefore changes witness selection.
#guard (accountResolveExecutionStateFunction.splitOn "jal ra, witness_codes_lookup_by_hash").length == 2
#guard (accountResolveExecutionStateFunction.splitOn "code_read_fetch").length == 1
-- Marker recognition is prefix-based and length-guarded; no 23-byte shortcut.
#guard (accountResolveExecutionStateFunction.splitOn "lbu t1, 0(t0); li t2, 0xef").length == 2
#guard (accountResolveExecutionStateFunction.splitOn "li t1, 3; bltu t0, t1").length == 2
-- The BAL builder must retain the two-tier pre-transaction resolver.  Retargeting
-- this call to the execution resolver would let the builder read its own tx map,
-- self-baseline a row, and silently accept a malformed BAL; the emitted bytes can
-- remain self-consistent, so the ordinary build and random A/B gates need not see it.
#guard (accountWritesEmitBuilderTxFunction.splitOn "jal ra, account_resolve_pre_state").length == 2

-- The clear in `incorporate` must reset the undo journal too: its entries index
-- the tx-level map, so a retained mark would unwind the NEXT transaction's writes
-- against the previous one's indices.
#guard (accountWritesIncorporateTxFunction.splitOn "account_writes_undo_count").length == 2

-- account_writes_discard_tx removed from guest (#11202); wiring question on issue.

-- The data section must declare every counter the routines name. Matched as EXACT
-- LINES, not substrings: `account_writes_count:` is a substring of
-- `tx_account_writes_count:`, so a splitOn guard on it counts two hits and fails
-- against correct code. The collision produced a clean, wrong answer rather than
-- an error -- the same shape as every narrow discriminator in this codebase.
#guard (accountWriteMapDataSection.splitOn "\n").count "account_writes_count:" == 1
#guard (accountWriteMapDataSection.splitOn "\n").count "tx_account_writes_count:" == 1
#guard (accountWriteMapDataSection.splitOn "\n").count "account_writes_overflow:" == 1
#guard (accountWriteMapDataSection.splitOn "\n").count "tx_account_writes_overflow:" == 1
#guard (accountWriteMapDataSection.splitOn "\n").count "account_writes_undo_count:" == 1

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
    accountWriteMapBssSection
}

end EvmAsm.Codegen
