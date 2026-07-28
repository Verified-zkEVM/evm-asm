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

  DOES NOT: emit BAL changes. The emission needs the spec's *pre-tx* baseline —
  `_get_pre_tx_account` reads the BLOCK-cumulative value and falls back to
  `pre_state`, NOT the pre-block value — and it needs the three-way field
  comparison whose inequality test is what makes net-zero filtering automatic.
  That serializer/builder walk is deliberately separate: this map retains
  execution facts but does not yet emit BAL rows.

  Known coverage boundary (evm-asm-tdbn0; GH #10717): this initial producer
  wiring covers the execution nonstorage/code effects, the inclusion-time
  sender nonce, and the post-body coinbase fee. It does not yet feed the sender
  gas debit, which is checked by the separate B2.3 running-balance path. The
  container is therefore FED but still UNREAD: it misses the majority of real
  BAL account entries, and a builder reader must not consume it until that
  balance transition is represented too.

  ## The `present` field

  The spec's value type is `Optional[Account]`, and `None` — the account does
  not exist — is a *distinct* state from an account whose balance, nonce and
  code hash all happen to be zero. So `present` is a field, not an
  all-zero-record sentinel. This is the same reasoning as `wasAbsent` on the
  storage side, where zero is a legitimate stored value; both are cases where a
  sentinel would silently invent a state the spec does not have.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.StorageWriteMap
import EvmAsm.Stateless.MemoryLayout

namespace EvmAsm.Codegen

/-- Transaction-local entries. One transaction's CALL-tree bound is 15038, so
    the existing 16384-row reservation remains sufficient. -/
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

/-- Per-row component-valid bits. A set bit says this transaction observed a
    final value for the component; it does not by itself mean the value differs
    from the transaction's baseline. -/
def accountWriteHasBalance : Nat := 1
def accountWriteHasNonce : Nat := 2
def accountWriteHasCode : Nat := 4
def accountWriteHasState : Nat := 8

/-! The fixed 128-byte row is `{addr_BE20@0, padding@20..31,
balance@32, nonce@64, optionalState@72, codePtr@80, codeLen@88,
reserved@96..111, validMask@112}`.  The 20-byte key is deliberately identical
to the builder's address segment; the retained stride keeps the arena and its
undo journal within their existing 2MiB reservations. -/

/-! ## `account_write_record`

    Fieldwise overlay corresponding to `set_account`
    (`state_tracker.py:486`): `tx_state.account_writes[address] = account`.

    Calling convention:
      a0 = address ptr  (canonical 20 B big-endian) — map key
      a1 = balance ptr  (32 B), valid when mask has BALANCE
      a2 = nonce        (u64, BY VALUE), valid when mask has NONCE
      a3 = code ptr, valid when mask has CODE
      a4 = code length, valid when mask has CODE
      a5 = account state (1 = `Some Account`, 0 = spec `None`)
      a6 = component-valid mask
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
  "  sd a0, 64(sp); sd a1, 72(sp); sd a2, 80(sp); sd a3, 88(sp); sd a4, 96(sp); sd a5, 104(sp); sd a6, 112(sp)\n" ++
  "  la t0, tx_account_writes_count; ld t1, 0(t0); li t3, 0xa2720000; li t4, 0\n" ++
  ".Lawr_scan:\n" ++
  "  bgeu t4, t1, .Lawr_append; slli t5, t4, 7; add t5, t3, t5; li t6, 20; mv t2, t5; ld t3, 64(sp)\n" ++
  ".Lawr_cmp:\n" ++
  "  beqz t6, .Lawr_hit; lbu a0, 0(t2); lbu a1, 0(t3); bne a0, a1, .Lawr_next; addi t2, t2, 1; addi t3, t3, 1; addi t6, t6, -1; j .Lawr_cmp\n" ++
  ".Lawr_hit:\n" ++
  "  mv a5, t4; li a6, 0; jal ra, account_writes_undo_push; j .Lawr_store\n" ++
  ".Lawr_next:\n" ++
  "  la t0, tx_account_writes_count; ld t1, 0(t0); li t3, 0xa2720000; addi t4, t4, 1; j .Lawr_scan\n" ++
  ".Lawr_append:\n" ++
  "  li t2, " ++ toString txAccountWritesCapacity ++ "; bgeu t1, t2, .Lawr_overflow; mv a5, t1; li a6, 1; jal ra, account_writes_undo_push\n" ++
  "  la t0, tx_account_writes_count; ld t1, 0(t0); li t3, 0xa2720000; slli t5, t1, 7; add t5, t3, t5; ld t2, 64(sp); li t6, 20\n" ++
  ".Lawr_copy_addr:\n" ++
  "  beqz t6, .Lawr_zero; lbu t3, 0(t2); sb t3, 0(t5); addi t2, t2, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lawr_copy_addr\n" ++
  ".Lawr_zero:\n" ++
  "  addi t5, t5, -20; sw zero, 20(t5); sd zero, 24(t5); sd zero, 32(t5); sd zero, 40(t5); sd zero, 48(t5); sd zero, 56(t5); sd zero, 64(t5); sd zero, 72(t5); sd zero, 80(t5); sd zero, 88(t5); sd zero, 96(t5); sd zero, 104(t5); sd zero, 112(t5); sd zero, 120(t5); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  ".Lawr_store:\n" ++
  "  ld t2, 112(sp); andi t3, t2, 1; beqz t3, .Lawr_no_balance; ld t3, 72(sp); ld t4, 0(t3); sd t4, 32(t5); ld t4, 8(t3); sd t4, 40(t5); ld t4, 16(t3); sd t4, 48(t5); ld t4, 24(t3); sd t4, 56(t5)\n" ++
  ".Lawr_no_balance:\n" ++
  "  andi t3, t2, 2; beqz t3, .Lawr_no_nonce; ld t3, 80(sp); sd t3, 64(t5)\n" ++
  ".Lawr_no_nonce:\n" ++
  "  andi t3, t2, 4; beqz t3, .Lawr_no_code; ld t3, 88(sp); sd t3, 80(t5); ld t3, 96(sp); sd t3, 88(t5)\n" ++
  ".Lawr_no_code:\n" ++
  "  andi t3, t2, 8; beqz t3, .Lawr_no_state; ld t3, 104(sp); sd t3, 72(t5)\n" ++
  ".Lawr_no_state:\n" ++
  "  ld t3, 112(t5); or t2, t2, t3; sd t2, 112(t5); j .Lawr_done\n" ++
  ".Lawr_overflow:\n" ++
  "  la t0, tx_account_writes_overflow; li t1, 1; sd t1, 0(t0)\n" ++
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
  "  li t3, 0xa24a0000\n" ++                                      -- ACCOUNT_WRITES_AREA
  "  li t4, 0\n" ++
  ".Lawb_scan:\n" ++
  "  bgeu t4, t1, .Lawb_append; slli t5, t4, 7; add t5, t3, t5; li t6, 20; mv t2, t5; mv t3, a0\n" ++
  ".Lawb_cmp:\n" ++
  "  beqz t6, .Lawb_store; lbu t1, 0(t2); lbu a1, 0(t3); bne t1, a1, .Lawb_next; addi t2, t2, 1; addi t3, t3, 1; addi t6, t6, -1; j .Lawb_cmp\n" ++
  ".Lawb_next:\n" ++
  "  la t0, account_writes_count; ld t1, 0(t0); li t3, 0xa24a0000; addi t4, t4, 1; j .Lawb_scan\n" ++
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
  "  ld t3, 112(t5); or t2, t2, t3; sd t2, 112(t5)\n" ++
  "  j .Lawb_done\n" ++
  ".Lawb_overflow:\n" ++
  "  la t0, account_writes_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".Lawb_done:\n" ++
  "  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)\n" ++
  "  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"

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
  "  la t0, current_block_access_index; ld s7, 0(t0); la s0, tx_account_writes_count; ld s1, 0(s0); li s2, 0xa2720000; li s3, 0\n" ++
  ".Laweb_loop:\n" ++
  "  bgeu s3, s1, .Laweb_done; slli t0, s3, 7; add s4, s2, t0\n" ++
  -- Find this address in the block-cumulative map.  A hit may still lack an
  -- individual field, in which case that component keeps the pre-state base.
  "  la t0, account_writes_count; ld t1, 0(t0); li t2, 0xa24a0000; li t3, 0; li s5, 0\n" ++
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
  "  ld s8, 112(s4)\n" ++
  -- Balance: baseline is block balance on a valid hit, otherwise header+8.
  "  andi t0, s8, 1; bnez t0, .Laweb_balance_have; j .Laweb_nonce\n" ++
  ".Laweb_balance_have:\n" ++
  "  beqz s5, .Laweb_balance_header; ld t0, 112(s5); andi t0, t0, 1; beqz t0, .Laweb_balance_header; addi s6, s5, 32; j .Laweb_balance_cmp\n" ++
  ".Laweb_balance_header:\n" ++
  "  la s6, account_builder_pre_account; addi s6, s6, 8\n" ++
  ".Laweb_balance_cmp:\n" ++
  "  ld t0, 0(s6); ld t1, 32(s4); bne t0, t1, .Laweb_balance_emit; ld t0, 8(s6); ld t1, 40(s4); bne t0, t1, .Laweb_balance_emit; ld t0, 16(s6); ld t1, 48(s4); bne t0, t1, .Laweb_balance_emit; ld t0, 24(s6); ld t1, 56(s4); beq t0, t1, .Laweb_nonce\n" ++
  ".Laweb_balance_emit:\n" ++
  "  mv a0, s4; mv a1, s7; addi a2, s4, 32; jal ra, bal_builder_append_balance\n" ++
  -- Nonce: baseline is block nonce on a valid hit, otherwise header+0.
  ".Laweb_nonce:\n" ++
  "  andi t0, s8, 2; bnez t0, .Laweb_nonce_have; j .Laweb_code\n" ++
  ".Laweb_nonce_have:\n" ++
  "  beqz s5, .Laweb_nonce_header; ld t0, 112(s5); andi t0, t0, 2; beqz t0, .Laweb_nonce_header; ld t0, 64(s5); j .Laweb_nonce_cmp\n" ++
  ".Laweb_nonce_header:\n" ++
  "  la t0, account_builder_pre_account; ld t0, 0(t0)\n" ++
  ".Laweb_nonce_cmp:\n" ++
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
  "  li s2, 0xa2720000\n" ++                                       -- s2 = tx area
  "  li s3, 0\n" ++                                                -- s3 = i
  ".Lawi_loop:\n" ++
  "  bgeu s3, s1, .Lawi_clear\n" ++
  "  slli a0, s3, 7; add a0, s2, a0\n" ++
  "  jal ra, account_writes_block_upsert\n" ++
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

/-! ## `account_writes_discard_tx`

    A transaction that fails contributes nothing to the block. The spec reaches
    this by never calling `incorporate_tx_into_block`, so the transaction dict is
    simply abandoned — but the guest's arena is reused across transactions, so
    abandoning means explicitly clearing, or the next transaction inherits the
    failed one's writes and `incorporate` promotes them.

    That is not hypothetical: it is the storage-side defect from this same family
    (#10693), where a failed transaction's writes reached the block level because
    the promotion was gated on a coverage flag rather than on transaction status.

    No arguments; no result register. -/
def accountWritesDiscardTxFunction : String :=
  "account_writes_discard_tx:\n" ++
  "  la t0, tx_account_writes_count; sd zero, 0(t0)\n" ++
  "  la t0, tx_account_writes_overflow; sd zero, 0(t0)\n" ++
  "  la t0, account_writes_undo_count; sd zero, 0(t0)\n" ++
  "  ret\n"

/-! ## `account_writes_undo_push`

    Append one undo entry describing a write about to happen to the tx-level map.

    a5 = entryIndex, a6 = wasAbsent (1 on append, 0 on overwrite).
    On an overwrite the superseded fields are read from the entry itself, so the
    caller does not have to stage them. No result register; no overflow path —
    the journal inherits the exec log's already-enforced 16384-row cap. -/
def accountWritesUndoPushFunction : String :=
  "account_writes_undo_push:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp); sd t4, 32(sp)\n" ++
  "  la t0, account_writes_undo_count; ld t1, 0(t0)\n" ++
  "  li t2, 0xa2920000\n" ++                                       -- ACCOUNT_WRITES_UNDO_AREA
  "  slli t3, t1, 7; add t3, t2, t3\n" ++                          -- t3 = &undo[count]
  "  sd a5, 0(t3)\n" ++                                            -- entryIndex
  "  sd a6, 8(t3)\n" ++                                            -- wasAbsent
  "  bnez a6, .Lawu_appended\n" ++
  -- Overwrite: snapshot every non-key word, including the valid mask. The
  -- reverse replay must restore an invalid component as invalid, not merely
  -- restore its payload bytes.
  "  li t2, 0xa2720000; slli t4, a5, 7; add t4, t2, t4\n" ++       -- t4 = &tx_entry[idx]
  "  ld t2, 32(t4);  sd t2, 16(t3); ld t2, 40(t4);  sd t2, 24(t3); ld t2, 48(t4);  sd t2, 32(t3); ld t2, 56(t4);  sd t2, 40(t3)\n" ++
  "  ld t2, 64(t4);  sd t2, 48(t3); ld t2, 72(t4);  sd t2, 56(t3); ld t2, 80(t4);  sd t2, 64(t3); ld t2, 88(t4);  sd t2, 72(t3)\n" ++
  "  ld t2, 96(t4);  sd t2, 80(t3); ld t2, 104(t4); sd t2, 88(t3); ld t2, 112(t4); sd t2, 96(t3); ld t2, 120(t4); sd t2, 104(t3)\n" ++
  ".Lawu_appended:\n" ++
  "  addi t1, t1, 1; la t0, account_writes_undo_count; sd t1, 0(t0)\n" ++
  "  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp); ld t4, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
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
  "  li t2, 0xa2920000; slli t3, t1, 7; add t3, t2, t3\n" ++       -- t3 = &undo[count]
  "  ld t4, 0(t3)\n" ++                                            -- entryIndex
  "  ld t5, 8(t3)\n" ++                                            -- wasAbsent
  "  beqz t5, .Lawf_overwrite\n" ++
  -- Appended: drop it by truncating the map to this index.
  "  la t2, tx_account_writes_count; sd t4, 0(t2)\n" ++
  "  j .Lawf_loop\n" ++
  ".Lawf_overwrite:\n" ++
  "  li t2, 0xa2720000; slli t5, t4, 7; add t5, t2, t5\n" ++       -- t5 = &tx_entry[idx]
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

/-- The per-frame undo marks are runtime-zeroed NOBITS, not ordinary `.data`.
    Keeping this array out of the address-pinned PROGBITS section is essential:
    it is an execution journal, while fixed Bn254 proof anchors live later in
    `.data`. -/
def accountWriteMapBssSection : String :=
  ".section .bss, \"aw\", @nobits\n" ++
  ".balign 8\n" ++
  -- Per-depth transaction-map undo mark.  A child REVERT restores account
  -- writes, unlike storage reads: reverted balance, nonce, and code mutations
  -- are not BAL events at all.  Kept alongside the storage-write checkpoint
  -- rather than in the packed frame ABI.
  "account_writes_undo_checkpoint:\n  .zero " ++ toString (1025 * 8) ++ "\n" ++
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
  ".balign 8\n"

/-- Every routine in this module, in emission order. `account_write_record`
    calls `account_writes_undo_push`, and `account_writes_incorporate_tx` calls
    `account_writes_block_upsert`, so all five must be emitted together. -/
def accountWriteMapFunctions : String :=
  accountWriteRecordFunction ++
  accountWritesBlockUpsertFunction ++
  accountWritesEmitBuilderTxFunction ++
  accountWritesIncorporateTxFunction ++
  accountWritesDiscardTxFunction ++
  accountWritesUndoPushFunction ++
  accountWritesRestoreFrameFunction

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
-- (0xa23a0000 + 1 MiB), so the new regions are contiguous with the existing ones
-- rather than leaving an unaccounted hole in working RAM.
#guard EvmAsm.Stateless.STORAGE_WRITES_UNDO_AREA.toNat + 0x100000 == EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat

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
#guard (accountWriteMapFunctions.splitOn "account_writes_discard_tx:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_undo_push:").length == 2
#guard (accountWriteMapFunctions.splitOn "account_writes_restore_frame:").length == 2

-- The clear in `incorporate` must reset the undo journal too: its entries index
-- the tx-level map, so a retained mark would unwind the NEXT transaction's writes
-- against the previous one's indices.
#guard (accountWritesIncorporateTxFunction.splitOn "account_writes_undo_count").length == 2

-- `discard` must clear exactly what `incorporate` clears. A discard that forgets a
-- counter leaves a failed transaction's writes visible to the next one, which is
-- the storage-side defect in #10693.
#guard (accountWritesDiscardTxFunction.splitOn "tx_account_writes_count").length == 2
#guard (accountWritesDiscardTxFunction.splitOn "tx_account_writes_overflow").length == 2
#guard (accountWritesDiscardTxFunction.splitOn "account_writes_undo_count").length == 2

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

end EvmAsm.Codegen
