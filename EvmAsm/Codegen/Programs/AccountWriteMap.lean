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
  raw `record_nonstorage_effect`'s 38476-row admission limit is not that proof.

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
import EvmAsm.Codegen.Programs.AccountWriteUndo
import EvmAsm.Codegen.Programs.AccountWriteMapDeletes
import EvmAsm.Stateless.MemoryLayout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen
open EvmAsm.Rv64

/-- Block-lifetime entries: DISTINCT accounts written anywhere in the block.

    ⛔ The superseded derivation said "Amsterdam permits at most 9523
    minimum-cost plain value transfers in a 200M-gas block; distinct senders and
    recipients plus coinbase require 19047 keys". Its arithmetic was internally
    consistent -- 200M/21,000 = 9,523 and 2x9,523+1 = 19,047 -- which is exactly
    why it read as derived. **Both inputs were wrong** (GH #11770):

    * There is no 21,000 intrinsic in Amsterdam. EIP-2780 decomposed it
      (`transactions.py:690-703`): `TX_BASE` 12,000 + `COLD_ACCOUNT_ACCESS`
      3,000, plus `TRANSFER_LOG_COST` 1,756 and `TX_VALUE_COST` 4,244 only when
      `value > 0`, and 0 recipient cost for a self-transfer. 21,000 is one
      transaction shape, not a constant.
    * Transfers are not the producer set. `account_writes_incorporate_tx`
      (below) copies EVERY transaction-map row into this map at each transaction
      boundary, so the block key set is the UNION over transactions of the tx
      maps -- every account-write publication site feeds it, not just
      transaction-level transfers.

    Derived: 200M IS the right divisor here (block lifetime). The cheapest way
    to add a distinct key is a cold `CALL` into a code-bearing account
    (`COLD_ACCOUNT_ACCESS` = 3000) whose body is `PUSH0 PUSH0 SSTORE` (104),
    plus call setup (~17) ~= 3,121 gas. A 200M block needs >= 12 transactions to
    spend it (each capped at `TX_MAX_GAS_LIMIT`), costing 12 x 12,000 in
    intrinsics: (200,000,000 - 144,000) / 3,121 = **64,035** distinct keys.
    Rounded up to the next power of two, 8.0 MiB. -/
def blockAccountWritesCapacity : Nat := 65536

/-- CALL-tree-only distinct-key bound. A value-bearing internal CALL to a cold
    target costs at least `COLD_ACCOUNT_ACCESS = 3000 + CALL_VALUE = 10300`;
    a call graph with `E` newly distinct targets has at most `E + 1` vertices.
    This deliberately loose bound omits the enclosing transaction's intrinsic
    gas.

    It is NOT the block-level capacity proof: that map accumulates across
    transactions, and the plain-transfer sender+recipient route remains the
    named precondition for producer wiring. The consolidated route enumeration
    lives in GH #10680; raw nonstorage rows (38476) are not distinct map keys. -/
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
/-- VALUE 16 = bit index 4. A **components-mask** value living at `+112`, NOT a
    payload value: when set it gates whether `execFlags@96` is stored
    (`.Lawr_no_flags`) or copied from the tx row (`.Lawb_no_flags`).

    ## `execFlags@+96` — what this structure's flag word means (GH #11706)

    Structure: `account_writes` rows, base `0xbdb80000` (block map) and
    `tx_account_writes`, base `0xbf780000` (tx map). **Stride 128.** Flag word at
    `+96`; components mask at `+112`. Values below are **VALUES, never indices** —
    every mask cited is an emitted `andi` immediate.

    | value | meaning | readers (emitted masks) |
    |-------|---------|--------------------------|
    | 2  | **live** — zero means present-dead or deleted | `.Lawa_tx_key` / `.Lawa_block_key`, `.Lawab_key`, `.Lawlc_*` (all `andi …, 2` on the `+96` word) |
    | 8  | **created-this-tx** | `account_writes_created_contains` `.Lawc_key`: `ld t1, 96(t5); andi t1, t1, 8` |
    | 1, 4, 32 | no `+96` reader mask exists | — |

    **Value 8 is created-this-tx, established from the WRITERS rather than from any
    consumer's variable name.** The only three call sites that put value 8 into
    `+96` are all CREATE paths, each passing `a7 = 27` (= 16+8+2+1):
    `BlockVerdictCreationStage` (`bv_create_addr`), `CreateCodeEffectLog` (the CREATE
    code publication) and `CreateFrameDescend` (`create_address_be`). The one
    non-create exec-flags writer passes `a7 = 0x33` (= 51 = 32+16+2+1), which does
    **not** contain value 8.

    ⛔ **Do not carry `AccountState flags@+88` constants into this field.** They are a
    different structure with overlapping values: `account_state_record_code` seeds
    `+88` with **27**, or **31** when the code length is nonzero, and *both contain
    value 8* — so storing either here sets the bit `.Lawc_key` reads as
    created-this-tx. A value derived from `+96`'s own readers is what belongs here
    (e.g. `a7 = 2` for a live, not-created row). GH #11697's first fix took `a7`
    from the `+88` seed and broke five rows. -/
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
  "  la t0, tx_account_writes_count; ld t1, 0(t0); li t3, 0xbf780000; li t4, 0\n" ++
  ".Lawr_scan:\n" ++
  "  bgeu t4, t1, .Lawr_append; slli t5, t4, 7; add t5, t3, t5; li t6, 20; mv t2, t5; ld t3, 64(sp)\n" ++
  ".Lawr_cmp:\n" ++
  "  beqz t6, .Lawr_hit; lbu a0, 0(t2); lbu a1, 0(t3); bne a0, a1, .Lawr_next; addi t2, t2, 1; addi t3, t3, 1; addi t6, t6, -1; j .Lawr_cmp\n" ++
  ".Lawr_hit:\n" ++
  "  mv a5, t4; li a6, 0; jal ra, account_writes_undo_push; bnez a0, .Lawr_overflow; j .Lawr_store\n" ++
  ".Lawr_next:\n" ++
  "  la t0, tx_account_writes_count; ld t1, 0(t0); li t3, 0xbf780000; addi t4, t4, 1; j .Lawr_scan\n" ++
  ".Lawr_append:\n" ++
  "  li t2, " ++ toString txAccountWritesCapacity ++ "; bgeu t1, t2, .Lawr_overflow; mv a5, t1; li a6, 1; jal ra, account_writes_undo_push; bnez a0, .Lawr_overflow\n" ++
  "  la t0, tx_account_writes_count; ld t1, 0(t0); li t3, 0xbf780000; slli t5, t1, 7; add t5, t3, t5; ld t2, 64(sp); li t6, 20\n" ++
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

/-! ## `account_writes_latest_balance`

    Read the current balance from the spec-shaped account-write maps.  The
    transaction map is checked first because block-level producers can append
    several effects before the transaction map is incorporated; the
    block-cumulative map is checked second.  A matching row without the
    BALANCE-valid bit is not a balance hit, so a code/nonce/touch-only row does
    not erase the caller's authenticated fallback.  Both maps are keyed
    upserts, hence each hit is already the latest write for that tier.

    a0 = canonical 20-byte BE address pointer
    a1 = 32-byte BE balance output, written only on a BALANCE hit
    returns a0 = 1 on hit and 0 on miss. -/
def accountWritesLatestBalance_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.account_read_record (GuestAddrs.account_writes_latest_balance + 28)),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_latest_balance + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_latest_balance + 32)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (2031 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_writes_latest_balance + 144) (GuestAddrs.account_writes_latest_balance + 60)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .MV .x10 .x30,
    .MV .x11 .x8,
    .LI .x31 (20 : Word),
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
    .LD .x5 .x30 (112 : BitVec 12),
    .ANDI .x5 .x5 (1 : BitVec 12),
    .BNE .x5 .x0 (brOff (GuestAddrs.account_writes_latest_balance + 256) (GuestAddrs.account_writes_latest_balance + 132)),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_latest_balance + 60) (GuestAddrs.account_writes_latest_balance + 140)),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.account_writes_latest_balance + 144)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.account_writes_latest_balance + 144)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (1975 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_writes_latest_balance + 296) (GuestAddrs.account_writes_latest_balance + 172)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .MV .x10 .x30,
    .MV .x11 .x8,
    .LI .x31 (20 : Word),
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
    .LD .x5 .x30 (112 : BitVec 12),
    .ANDI .x5 .x5 (1 : BitVec 12),
    .BNE .x5 .x0 (12 : BitVec 13),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_latest_balance + 172) (GuestAddrs.account_writes_latest_balance + 252)),
    .LD .x5 .x30 (32 : BitVec 12),
    .SD .x9 .x5 (0 : BitVec 12),
    .LD .x5 .x30 (40 : BitVec 12),
    .SD .x9 .x5 (8 : BitVec 12),
    .LD .x5 .x30 (48 : BitVec 12),
    .SD .x9 .x5 (16 : BitVec 12),
    .LD .x5 .x30 (56 : BitVec 12),
    .SD .x9 .x5 (24 : BitVec 12),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountWritesLatestBalance_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWritesLatestBalance_relocs : RelocTable :=
  [ (7, .jal .x1 "account_read_record"),
    (8, .la .x5 "tx_account_writes_count"),
    (36, .la .x5 "account_writes_count") ]

def accountWritesLatestBalanceFunction : String :=
  "account_writes_latest_balance:\n" ++ emitProgramR accountWritesLatestBalance_prog accountWritesLatestBalance_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWritesLatestBalance_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWritesLatestBalanceFunction_eq_prog :
    accountWritesLatestBalanceFunction = "account_writes_latest_balance:\n" ++ emitProgramR accountWritesLatestBalance_prog accountWritesLatestBalance_relocs := rfl

#guard accountWritesLatestBalanceFunction.startsWith "account_writes_latest_balance:\n"
#guard accountWritesLatestBalance_prog.length = 80
/-! ## `account_writes_latest_balance_block`

    Block-only balance lookup.  This is intentionally separate from
    `account_writes_latest_balance`: reader 17 is a block-tier reader and must
    not observe a pending transaction row.  A row without the BALANCE-valid
    component is a miss, including a nonce/code/state-only row.

    a0 = canonical 20-byte BE address, a1 = 32-byte BE output.
    Returns a0 = 1 on a block-map balance hit, 0 otherwise. -/
def accountWritesLatestBalanceBlock_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.account_read_record (GuestAddrs.account_writes_latest_balance_block + 28)),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.account_writes_latest_balance_block + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.account_writes_latest_balance_block + 32)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (1975 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_writes_latest_balance_block + 176) (GuestAddrs.account_writes_latest_balance_block + 60)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .MV .x10 .x30,
    .MV .x11 .x8,
    .LI .x31 (20 : Word),
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
    .LD .x5 .x30 (112 : BitVec 12),
    .ANDI .x5 .x5 (1 : BitVec 12),
    .BEQ .x5 .x0 (-16 : BitVec 13),
    .LD .x5 .x30 (32 : BitVec 12),
    .SD .x9 .x5 (0 : BitVec 12),
    .LD .x5 .x30 (40 : BitVec 12),
    .SD .x9 .x5 (8 : BitVec 12),
    .LD .x5 .x30 (48 : BitVec 12),
    .SD .x9 .x5 (16 : BitVec 12),
    .LD .x5 .x30 (56 : BitVec 12),
    .SD .x9 .x5 (24 : BitVec 12),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountWritesLatestBalanceBlock_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWritesLatestBalanceBlock_relocs : RelocTable :=
  [ (7, .jal .x1 "account_read_record"),
    (8, .la .x5 "account_writes_count") ]

def accountWritesLatestBalanceBlockFunction : String :=
  "account_writes_latest_balance_block:\n" ++ emitProgramR accountWritesLatestBalanceBlock_prog accountWritesLatestBalanceBlock_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWritesLatestBalanceBlock_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWritesLatestBalanceBlockFunction_eq_prog :
    accountWritesLatestBalanceBlockFunction = "account_writes_latest_balance_block:\n" ++ emitProgramR accountWritesLatestBalanceBlock_prog accountWritesLatestBalanceBlock_relocs := rfl

#guard accountWritesLatestBalanceBlockFunction.startsWith "account_writes_latest_balance_block:\n"
#guard accountWritesLatestBalanceBlock_prog.length = 50
/-! ## `account_writes_latest_nonce_block`

    Block-map-only nonce lookup, with canonical BE20 `a0`, u64 output pointer
    `a1`, and hit/miss in `a0`.  It requires mask value 2 at row `+112`, reads
    nonce at `+64`, never falls back to AccountState, and leaves all readers
    untouched.  This is the block-level `account_writes` contract described by
    Amsterdam `state_tracker.py:137-142` and `block_access_lists.py:637-650`. -/
def accountWritesLatestNonceBlock_prog : Program :=
  [ .ADDI .x2 .x2 (-24 : BitVec 12),
    .SD .x2 .x8 (0 : BitVec 12),
    .SD .x2 .x9 (8 : BitVec 12),
    .SD .x2 .x1 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.account_read_record (GuestAddrs.account_writes_latest_nonce_block + 28)),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.account_writes_latest_nonce_block + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.account_writes_latest_nonce_block + 32)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (1975 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_writes_latest_nonce_block + 152) (GuestAddrs.account_writes_latest_nonce_block + 60)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x29 .x7 .x29,
    .MV .x30 .x29,
    .MV .x31 .x8,
    .LI .x12 (20 : Word),
    .BEQ .x12 .x0 (40 : BitVec 13),
    .LBU .x13 .x30 (0 : BitVec 12),
    .LBU .x14 .x31 (0 : BitVec 12),
    .BNE .x13 .x14 (20 : BitVec 13),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .ADDI .x12 .x12 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .LD .x5 .x29 (112 : BitVec 12),
    .ANDI .x5 .x5 (2 : BitVec 12),
    .BEQ .x5 .x0 (-16 : BitVec 13),
    .LD .x5 .x29 (64 : BitVec 12),
    .SD .x9 .x5 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x8 .x2 (0 : BitVec 12),
    .LD .x9 .x2 (8 : BitVec 12),
    .LD .x1 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (24 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountWritesLatestNonceBlock_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWritesLatestNonceBlock_relocs : RelocTable :=
  [ (7, .jal .x1 "account_read_record"),
    (8, .la .x5 "account_writes_count") ]

def accountWritesLatestNonceBlockFunction : String :=
  "account_writes_latest_nonce_block:\n" ++ emitProgramR accountWritesLatestNonceBlock_prog accountWritesLatestNonceBlock_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWritesLatestNonceBlock_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWritesLatestNonceBlockFunction_eq_prog :
    accountWritesLatestNonceBlockFunction = "account_writes_latest_nonce_block:\n" ++ emitProgramR accountWritesLatestNonceBlock_prog accountWritesLatestNonceBlock_relocs := rfl

#guard accountWritesLatestNonceBlockFunction.startsWith "account_writes_latest_nonce_block:\n"
#guard accountWritesLatestNonceBlock_prog.length = 44
/-! ## `account_writes_latest_nonce_tx`

    Transaction-only nonce lookup.  This is the counterpart to the existing
    BLOCK-only nonce contract and is used by reader 16, whose current
    transaction state must not be replaced by a prior block row.

    a0 = canonical 20-byte BE address, a1 = u64 output pointer.
    Returns a0 = 1 on a transaction-map nonce hit, 0 otherwise. -/
def accountWritesLatestNonceTx_prog : Program :=
  [ .ADDI .x2 .x2 (-24 : BitVec 12),
    .SD .x2 .x8 (0 : BitVec 12),
    .SD .x2 .x9 (8 : BitVec 12),
    .SD .x2 .x1 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.account_read_record (GuestAddrs.account_writes_latest_nonce_tx + 28)),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_latest_nonce_tx + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_latest_nonce_tx + 32)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (2031 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_writes_latest_nonce_tx + 152) (GuestAddrs.account_writes_latest_nonce_tx + 60)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x29 .x7 .x29,
    .MV .x30 .x29,
    .MV .x31 .x8,
    .LI .x12 (20 : Word),
    .BEQ .x12 .x0 (40 : BitVec 13),
    .LBU .x13 .x30 (0 : BitVec 12),
    .LBU .x14 .x31 (0 : BitVec 12),
    .BNE .x13 .x14 (20 : BitVec 13),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .ADDI .x12 .x12 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .LD .x5 .x29 (112 : BitVec 12),
    .ANDI .x5 .x5 (2 : BitVec 12),
    .BEQ .x5 .x0 (-16 : BitVec 13),
    .LD .x5 .x29 (64 : BitVec 12),
    .SD .x9 .x5 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x8 .x2 (0 : BitVec 12),
    .LD .x9 .x2 (8 : BitVec 12),
    .LD .x1 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (24 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountWritesLatestNonceTx_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWritesLatestNonceTx_relocs : RelocTable :=
  [ (7, .jal .x1 "account_read_record"),
    (8, .la .x5 "tx_account_writes_count") ]

def accountWritesLatestNonceTxFunction : String :=
  "account_writes_latest_nonce_tx:\n" ++ emitProgramR accountWritesLatestNonceTx_prog accountWritesLatestNonceTx_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWritesLatestNonceTx_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWritesLatestNonceTxFunction_eq_prog :
    accountWritesLatestNonceTxFunction = "account_writes_latest_nonce_tx:\n" ++ emitProgramR accountWritesLatestNonceTx_prog accountWritesLatestNonceTx_relocs := rfl

#guard accountWritesLatestNonceTxFunction.startsWith "account_writes_latest_nonce_tx:\n"
#guard accountWritesLatestNonceTx_prog.length = 44
/-! ## Account-write AUTH and CREATED contracts

    AUTH uses the map's explicit EXEC_FLAGS field rather than inferring
    delegation from a code pointer.  The current lookup checks TX then BLOCK;
    the block-only companion is used for `delegated_before_tx`.  Both require
    a valid nonce, state, and EXEC_FLAGS component, so a balance-only or
    sender-inclusion row cannot mask the authenticated header fallback.

    CREATED is transaction-only and checks the explicit `created-this-tx` bit
    in EXEC_FLAGS.  It is not inferred from code presence: an authorization
    row and a normal CREATE row have different provenance even when both carry
    code bytes.

    AUTH ABI: a0 = address, a1 = nonce output, a2 = flags output;
    return 0 = miss, 1 = present/live, 2 = present/dead. -/
def accountWritesAuthCurrent_prog : Program :=
  [ .ADDI .x2 .x2 (-40 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.account_read_record (GuestAddrs.account_writes_auth_current + 40)),
    .LI .x19 (0 : Word),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_auth_current + 48)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_auth_current + 48)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (2031 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_writes_auth_current + 172) (GuestAddrs.account_writes_auth_current + 76)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .MV .x10 .x30,
    .MV .x11 .x8,
    .LI .x31 (20 : Word),
    .BEQ .x31 .x0 (40 : BitVec 13),
    .LBU .x13 .x10 (0 : BitVec 12),
    .LBU .x14 .x11 (0 : BitVec 12),
    .BNE .x13 .x14 (20 : BitVec 13),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .LD .x5 .x30 (112 : BitVec 12),
    .ANDI .x6 .x5 (2 : BitVec 12),
    .BEQ .x6 .x0 (-16 : BitVec 13),
    .ANDI .x6 .x5 (8 : BitVec 12),
    .BEQ .x6 .x0 (-24 : BitVec 13),
    .ANDI .x6 .x5 (16 : BitVec 12),
    .BEQ .x6 .x0 (-32 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_auth_current + 296) (GuestAddrs.account_writes_auth_current + 168)),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.account_writes_auth_current + 172)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.account_writes_auth_current + 172)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (1975 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_writes_auth_current + 336) (GuestAddrs.account_writes_auth_current + 200)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .MV .x10 .x30,
    .MV .x11 .x8,
    .LI .x31 (20 : Word),
    .BEQ .x31 .x0 (40 : BitVec 13),
    .LBU .x13 .x10 (0 : BitVec 12),
    .LBU .x14 .x11 (0 : BitVec 12),
    .BNE .x13 .x14 (20 : BitVec 13),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .LD .x5 .x30 (112 : BitVec 12),
    .ANDI .x6 .x5 (2 : BitVec 12),
    .BEQ .x6 .x0 (-16 : BitVec 13),
    .ANDI .x6 .x5 (8 : BitVec 12),
    .BEQ .x6 .x0 (-24 : BitVec 13),
    .ANDI .x6 .x5 (16 : BitVec 12),
    .BEQ .x6 .x0 (-32 : BitVec 13),
    .JAL .x0 (4 : BitVec 21),
    .LD .x6 .x30 (64 : BitVec 12),
    .SD .x9 .x6 (0 : BitVec 12),
    .LD .x6 .x30 (96 : BitVec 12),
    .SD .x18 .x6 (0 : BitVec 12),
    .ANDI .x6 .x6 (2 : BitVec 12),
    .BNE .x6 .x0 (12 : BitVec 13),
    .LI .x10 (2 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (40 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountWritesAuthCurrent_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWritesAuthCurrent_relocs : RelocTable :=
  [ (10, .jal .x1 "account_read_record"),
    (12, .la .x5 "tx_account_writes_count"),
    (43, .la .x5 "account_writes_count") ]

def accountWritesAuthCurrentFunction : String :=
  "account_writes_auth_current:\n" ++ emitProgramR accountWritesAuthCurrent_prog accountWritesAuthCurrent_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWritesAuthCurrent_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWritesAuthCurrentFunction_eq_prog :
    accountWritesAuthCurrentFunction = "account_writes_auth_current:\n" ++ emitProgramR accountWritesAuthCurrent_prog accountWritesAuthCurrent_relocs := rfl

#guard accountWritesAuthCurrentFunction.startsWith "account_writes_auth_current:\n"
#guard accountWritesAuthCurrent_prog.length = 92
/-! Block-only AUTH additionally returns the matched row's code pointer and
    code length in a1/a2 on return.  These registers replace the input scratch
    pointers after the nonce and flags have been written; a row without a CODE
    component returns zeroes there. -/
def accountWritesAuthBlock_prog : Program :=
  [ .ADDI .x2 .x2 (-40 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.account_read_record (GuestAddrs.account_writes_auth_block + 36)),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.account_writes_auth_block + 40)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.account_writes_auth_block + 40)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (1975 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_writes_auth_block + 232) (GuestAddrs.account_writes_auth_block + 68)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .MV .x10 .x30,
    .MV .x11 .x8,
    .LI .x31 (20 : Word),
    .BEQ .x31 .x0 (40 : BitVec 13),
    .LBU .x13 .x10 (0 : BitVec 12),
    .LBU .x14 .x11 (0 : BitVec 12),
    .BNE .x13 .x14 (20 : BitVec 13),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .LD .x5 .x30 (112 : BitVec 12),
    .ANDI .x6 .x5 (2 : BitVec 12),
    .BEQ .x6 .x0 (-16 : BitVec 13),
    .ANDI .x6 .x5 (8 : BitVec 12),
    .BEQ .x6 .x0 (-24 : BitVec 13),
    .ANDI .x6 .x5 (16 : BitVec 12),
    .BEQ .x6 .x0 (-32 : BitVec 13),
    .LD .x6 .x30 (64 : BitVec 12),
    .SD .x9 .x6 (0 : BitVec 12),
    .LD .x6 .x30 (96 : BitVec 12),
    .SD .x18 .x6 (0 : BitVec 12),
    .ANDI .x6 .x5 (4 : BitVec 12),
    .BEQ .x6 .x0 (16 : BitVec 13),
    .LD .x11 .x30 (80 : BitVec 12),
    .LD .x12 .x30 (88 : BitVec 12),
    .JAL .x0 (12 : BitVec 21),
    .LI .x11 (0 : Word),
    .LI .x12 (0 : Word),
    .LD .x6 .x30 (96 : BitVec 12),
    .ANDI .x6 .x6 (2 : BitVec 12),
    .BNE .x6 .x0 (12 : BitVec 13),
    .LI .x10 (2 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (0 : Word),
    .LI .x11 (0 : Word),
    .LI .x12 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (40 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountWritesAuthBlock_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWritesAuthBlock_relocs : RelocTable :=
  [ (9, .jal .x1 "account_read_record"),
    (10, .la .x5 "account_writes_count") ]

def accountWritesAuthBlockFunction : String :=
  "account_writes_auth_block:\n" ++ emitProgramR accountWritesAuthBlock_prog accountWritesAuthBlock_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWritesAuthBlock_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWritesAuthBlockFunction_eq_prog :
    accountWritesAuthBlockFunction = "account_writes_auth_block:\n" ++ emitProgramR accountWritesAuthBlock_prog accountWritesAuthBlock_relocs := rfl

#guard accountWritesAuthBlockFunction.startsWith "account_writes_auth_block:\n"
#guard accountWritesAuthBlock_prog.length = 67
/-! Transaction-local CREATED membership from the explicit map EXEC_FLAGS
    field.  The map must carry this bit on the CREATE code publication; the
    contract deliberately does not treat every code row as created. -/
def accountWritesCreatedContains_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .MV .x8 .x10,
    .AUIPC .x5 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_created_contains + 16)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_created_contains + 16)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (2031 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_writes_created_contains + 144) (GuestAddrs.account_writes_created_contains + 44)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .MV .x10 .x30,
    .MV .x11 .x8,
    .LI .x31 (20 : Word),
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
    .LD .x5 .x30 (112 : BitVec 12),
    .ANDI .x6 .x5 (16 : BitVec 12),
    .BEQ .x6 .x0 (-16 : BitVec 13),
    .LD .x6 .x30 (96 : BitVec 12),
    .ANDI .x6 .x6 (8 : BitVec 12),
    .BNE .x6 .x0 (8 : BitVec 13),
    .JAL .x0 (-32 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountWritesCreatedContains_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWritesCreatedContains_relocs : RelocTable :=
  [ (4, .la .x5 "tx_account_writes_count") ]

def accountWritesCreatedContainsFunction : String :=
  "account_writes_created_contains:\n" ++ emitProgramR accountWritesCreatedContains_prog accountWritesCreatedContains_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWritesCreatedContains_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWritesCreatedContainsFunction_eq_prog :
    accountWritesCreatedContainsFunction = "account_writes_created_contains:\n" ++ emitProgramR accountWritesCreatedContains_prog accountWritesCreatedContains_relocs := rfl

#guard accountWritesCreatedContainsFunction.startsWith "account_writes_created_contains:\n"
#guard accountWritesCreatedContains_prog.length = 41
/-! Current execution-code/status lookup over the account-write tiers.

    This preserves the ABI of `account_state_lookup_current` so existing
    callers can switch independently: a0 = 0 absent/miss, 1 live code with
    a1/a2 = pointer/length, 2 present but empty, 3 present-but-deleted.  A
    transaction row wins over the block row when it carries STATE; the
    delete-finalization row deliberately carries STATE without EXEC_FLAGS,
    while component-only balance/nonce/touch rows are deliberately skipped so
    they cannot mask a lower-tier code row or the caller's witness fallback. -/
def accountWritesLookupCurrent_prog : Program :=
  [ .ADDI .x2 .x2 (-24 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .MV .x8 .x10,
    .AUIPC .x5 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_lookup_current + 16)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_lookup_current + 16)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (2031 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_writes_lookup_current + 176) (GuestAddrs.account_writes_lookup_current + 44)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .MV .x10 .x30,
    .MV .x11 .x8,
    .LI .x31 (20 : Word),
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
    .LD .x5 .x30 (112 : BitVec 12),
    .ANDI .x6 .x5 (8 : BitVec 12),
    .BEQ .x6 .x0 (-16 : BitVec 13),
    .LD .x6 .x30 (72 : BitVec 12),
    .BEQ .x6 .x0 (brOff (GuestAddrs.account_writes_lookup_current + 352) (GuestAddrs.account_writes_lookup_current + 124)),
    .ANDI .x6 .x5 (16 : BitVec 12),
    .BEQ .x6 .x0 (brOff (GuestAddrs.account_writes_lookup_current + 336) (GuestAddrs.account_writes_lookup_current + 132)),
    .LD .x6 .x30 (96 : BitVec 12),
    .ANDI .x6 .x6 (2 : BitVec 12),
    .BEQ .x6 .x0 (brOff (GuestAddrs.account_writes_lookup_current + 352) (GuestAddrs.account_writes_lookup_current + 144)),
    .ANDI .x6 .x5 (4 : BitVec 12),
    .BEQ .x6 .x0 (brOff (GuestAddrs.account_writes_lookup_current + 336) (GuestAddrs.account_writes_lookup_current + 152)),
    .LD .x11 .x30 (80 : BitVec 12),
    .LD .x12 .x30 (88 : BitVec 12),
    .BEQ .x12 .x0 (brOff (GuestAddrs.account_writes_lookup_current + 336) (GuestAddrs.account_writes_lookup_current + 164)),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_lookup_current + 380) (GuestAddrs.account_writes_lookup_current + 172)),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.account_writes_lookup_current + 176)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.account_writes_lookup_current + 176)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (1975 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_writes_lookup_current + 368) (GuestAddrs.account_writes_lookup_current + 204)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .MV .x10 .x30,
    .MV .x11 .x8,
    .LI .x31 (20 : Word),
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
    .LD .x5 .x30 (112 : BitVec 12),
    .ANDI .x6 .x5 (8 : BitVec 12),
    .BEQ .x6 .x0 (-16 : BitVec 13),
    .LD .x6 .x30 (72 : BitVec 12),
    .BEQ .x6 .x0 (brOff (GuestAddrs.account_writes_lookup_current + 352) (GuestAddrs.account_writes_lookup_current + 284)),
    .ANDI .x6 .x5 (16 : BitVec 12),
    .BEQ .x6 .x0 (44 : BitVec 13),
    .LD .x6 .x30 (96 : BitVec 12),
    .ANDI .x6 .x6 (2 : BitVec 12),
    .BEQ .x6 .x0 (48 : BitVec 13),
    .ANDI .x6 .x5 (4 : BitVec 12),
    .BEQ .x6 .x0 (24 : BitVec 13),
    .LD .x11 .x30 (80 : BitVec 12),
    .LD .x12 .x30 (88 : BitVec 12),
    .BEQ .x12 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (48 : BitVec 21),
    .LI .x10 (2 : Word),
    .LI .x11 (0 : Word),
    .LI .x12 (0 : Word),
    .JAL .x0 (32 : BitVec 21),
    .LI .x10 (3 : Word),
    .LI .x11 (0 : Word),
    .LI .x12 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (0 : Word),
    .LI .x11 (0 : Word),
    .LI .x12 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .ADDI .x2 .x2 (24 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountWritesLookupCurrent_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWritesLookupCurrent_relocs : RelocTable :=
  [ (4, .la .x5 "tx_account_writes_count"),
    (44, .la .x5 "account_writes_count") ]

def accountWritesLookupCurrentFunction : String :=
  "account_writes_lookup_current:\n" ++ emitProgramR accountWritesLookupCurrent_prog accountWritesLookupCurrent_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWritesLookupCurrent_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWritesLookupCurrentFunction_eq_prog :
    accountWritesLookupCurrentFunction = "account_writes_lookup_current:\n" ++ emitProgramR accountWritesLookupCurrent_prog accountWritesLookupCurrent_relocs := rfl

#guard accountWritesLookupCurrentFunction.startsWith "account_writes_lookup_current:\n"
#guard accountWritesLookupCurrent_prog.length = 99
/-! Balance/nonce-zero predicate for an empty current account.

    This is the map-side replacement for `account_state_tombstone_balance_zero`.
    It keeps the old caller ABI, but obtains missing balance/nonce components
    from the pre-transaction map/parent resolver.  That matters for AUTH and
    code-only rows: a map row without a BALANCE bit does not authorize zero.
    The transaction-level `account_state_created` set is authoritative for
    created-this-transaction membership: unlike the row-local EXEC_FLAGS field,
    it also answers for an account before any map row exists.  A set-overflow
    status is treated as fail-closed by the caller. -/
def accountWritesTombstoneBalanceZero_prog : Program :=
  [ .ADDI .x2 .x2 (-160 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .LI .x9 (0 : Word),
    .LI .x18 (0 : Word),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_tombstone_balance_zero + 44)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_tombstone_balance_zero + 44)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (2031 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_writes_tombstone_balance_zero + 144) (GuestAddrs.account_writes_tombstone_balance_zero + 72)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .MV .x10 .x30,
    .MV .x11 .x8,
    .LI .x31 (20 : Word),
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
    .MV .x9 .x30,
    .JAL .x0 (4 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.account_writes_tombstone_balance_zero + 144)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.account_writes_tombstone_balance_zero + 144)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (1975 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_writes_tombstone_balance_zero + 240) (GuestAddrs.account_writes_tombstone_balance_zero + 172)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x30 .x7 .x29,
    .MV .x10 .x30,
    .MV .x11 .x8,
    .LI .x31 (20 : Word),
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
    .MV .x18 .x30,
    .BEQ .x9 .x0 (16 : BitVec 13),
    .LD .x5 .x9 (112 : BitVec 12),
    .ANDI .x6 .x5 (8 : BitVec 12),
    .BNE .x6 .x0 (28 : BitVec 13),
    .BEQ .x18 .x0 (brOff (GuestAddrs.account_writes_tombstone_balance_zero + 684) (GuestAddrs.account_writes_tombstone_balance_zero + 256)),
    .LD .x5 .x18 (112 : BitVec 12),
    .ANDI .x6 .x5 (8 : BitVec 12),
    .BEQ .x6 .x0 (brOff (GuestAddrs.account_writes_tombstone_balance_zero + 684) (GuestAddrs.account_writes_tombstone_balance_zero + 268)),
    .MV .x19 .x18,
    .JAL .x0 (8 : BitVec 21),
    .MV .x19 .x9,
    .LD .x5 .x19 (72 : BitVec 12),
    .BEQ .x5 .x0 (brOff (GuestAddrs.account_writes_tombstone_balance_zero + 676) (GuestAddrs.account_writes_tombstone_balance_zero + 288)),
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.account_state_created_contains (GuestAddrs.account_writes_tombstone_balance_zero + 296)),
    .BNE .x10 .x0 (brOff (GuestAddrs.account_writes_tombstone_balance_zero + 684) (GuestAddrs.account_writes_tombstone_balance_zero + 300)),
    .LD .x6 .x19 (112 : BitVec 12),
    .ANDI .x7 .x6 (4 : BitVec 12),
    .BEQ .x7 .x0 (12 : BitVec 13),
    .LD .x28 .x19 (88 : BitVec 12),
    .BNE .x28 .x0 (brOff (GuestAddrs.account_writes_tombstone_balance_zero + 684) (GuestAddrs.account_writes_tombstone_balance_zero + 320)),
    .LI .x20 (0 : Word),
    .LI .x21 (0 : Word),
    .BEQ .x9 .x0 (brOff (GuestAddrs.account_writes_tombstone_balance_zero + 404) (GuestAddrs.account_writes_tombstone_balance_zero + 332)),
    .LD .x5 .x9 (112 : BitVec 12),
    .ANDI .x6 .x5 (1 : BitVec 12),
    .BEQ .x6 .x0 (40 : BitVec 13),
    .LD .x7 .x9 (32 : BitVec 12),
    .SD .x2 .x7 (128 : BitVec 12),
    .LD .x7 .x9 (40 : BitVec 12),
    .SD .x2 .x7 (136 : BitVec 12),
    .LD .x7 .x9 (48 : BitVec 12),
    .SD .x2 .x7 (144 : BitVec 12),
    .LD .x7 .x9 (56 : BitVec 12),
    .SD .x2 .x7 (152 : BitVec 12),
    .LI .x20 (1 : Word),
    .ANDI .x6 .x5 (2 : BitVec 12),
    .BEQ .x6 .x0 (16 : BitVec 13),
    .LD .x7 .x9 (64 : BitVec 12),
    .SD .x2 .x7 (120 : BitVec 12),
    .LI .x21 (1 : Word),
    .BEQ .x18 .x0 (brOff (GuestAddrs.account_writes_tombstone_balance_zero + 484) (GuestAddrs.account_writes_tombstone_balance_zero + 404)),
    .LD .x5 .x18 (112 : BitVec 12),
    .BNE .x20 .x0 (48 : BitVec 13),
    .ANDI .x6 .x5 (1 : BitVec 12),
    .BEQ .x6 .x0 (40 : BitVec 13),
    .LD .x7 .x18 (32 : BitVec 12),
    .SD .x2 .x7 (128 : BitVec 12),
    .LD .x7 .x18 (40 : BitVec 12),
    .SD .x2 .x7 (136 : BitVec 12),
    .LD .x7 .x18 (48 : BitVec 12),
    .SD .x2 .x7 (144 : BitVec 12),
    .LD .x7 .x18 (56 : BitVec 12),
    .SD .x2 .x7 (152 : BitVec 12),
    .LI .x20 (1 : Word),
    .BNE .x21 .x0 (24 : BitVec 13),
    .ANDI .x6 .x5 (2 : BitVec 12),
    .BEQ .x6 .x0 (16 : BitVec 13),
    .LD .x7 .x18 (64 : BitVec 12),
    .SD .x2 .x7 (120 : BitVec 12),
    .LI .x21 (1 : Word),
    .BNE .x20 .x0 (8 : BitVec 13),
    .JAL .x0 (12 : BitVec 21),
    .BNE .x21 .x0 (brOff (GuestAddrs.account_writes_tombstone_balance_zero + 584) (GuestAddrs.account_writes_tombstone_balance_zero + 492)),
    .JAL .x0 (4 : BitVec 21),
    .SD .x2 .x0 (80 : BitVec 12),
    .SD .x2 .x0 (88 : BitVec 12),
    .SD .x2 .x0 (96 : BitVec 12),
    .SD .x2 .x0 (104 : BitVec 12),
    .SD .x2 .x0 (112 : BitVec 12),
    .MV .x10 .x8,
    .ADDI .x11 .x2 (80 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.account_writes_tombstone_balance_zero + 528)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.account_writes_tombstone_balance_zero + 528)),
    .LD .x12 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_len (GuestAddrs.account_writes_tombstone_balance_zero + 540)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_len (GuestAddrs.account_writes_tombstone_balance_zero + 540)),
    .LD .x13 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_ptr (GuestAddrs.account_writes_tombstone_balance_zero + 552)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_ptr (GuestAddrs.account_writes_tombstone_balance_zero + 552)),
    .LD .x14 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_len (GuestAddrs.account_writes_tombstone_balance_zero + 564)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_len (GuestAddrs.account_writes_tombstone_balance_zero + 564)),
    .LD .x15 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.account_resolve_pre_state (GuestAddrs.account_writes_tombstone_balance_zero + 576)),
    .BNE .x10 .x0 (brOff (GuestAddrs.account_writes_tombstone_balance_zero + 684) (GuestAddrs.account_writes_tombstone_balance_zero + 580)),
    .BEQ .x20 .x0 (36 : BitVec 13),
    .LD .x5 .x2 (128 : BitVec 12),
    .SD .x2 .x5 (88 : BitVec 12),
    .LD .x5 .x2 (136 : BitVec 12),
    .SD .x2 .x5 (96 : BitVec 12),
    .LD .x5 .x2 (144 : BitVec 12),
    .SD .x2 .x5 (104 : BitVec 12),
    .LD .x5 .x2 (152 : BitVec 12),
    .SD .x2 .x5 (112 : BitVec 12),
    .BEQ .x21 .x0 (12 : BitVec 13),
    .LD .x5 .x2 (120 : BitVec 12),
    .SD .x2 .x5 (80 : BitVec 12),
    .LD .x5 .x2 (80 : BitVec 12),
    .BNE .x5 .x0 (48 : BitVec 13),
    .LD .x5 .x2 (88 : BitVec 12),
    .LD .x6 .x2 (96 : BitVec 12),
    .OR .x5 .x5 .x6,
    .LD .x6 .x2 (104 : BitVec 12),
    .OR .x5 .x5 .x6,
    .LD .x6 .x2 (112 : BitVec 12),
    .OR .x5 .x5 .x6,
    .BNE .x5 .x0 (16 : BitVec 13),
    .JAL .x0 (4 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (160 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountWritesTombstoneBalanceZero_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWritesTombstoneBalanceZero_relocs : RelocTable :=
  [ (11, .la .x5 "tx_account_writes_count"),
    (36, .la .x5 "account_writes_count"),
    (74, .jal .x1 "account_state_created_contains"),
    (132, .la .x5 "sv_pre_rlp_ptr"),
    (135, .la .x5 "sv_pre_rlp_len"),
    (138, .la .x5 "bv_witness_state_ptr"),
    (141, .la .x5 "bv_witness_state_len"),
    (144, .jal .x1 "account_resolve_pre_state") ]

def accountWritesTombstoneBalanceZeroFunction : String :=
  "account_writes_tombstone_balance_zero:\n" ++ emitProgramR accountWritesTombstoneBalanceZero_prog accountWritesTombstoneBalanceZero_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWritesTombstoneBalanceZero_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWritesTombstoneBalanceZeroFunction_eq_prog :
    accountWritesTombstoneBalanceZeroFunction = "account_writes_tombstone_balance_zero:\n" ++ emitProgramR accountWritesTombstoneBalanceZero_prog accountWritesTombstoneBalanceZero_relocs := rfl

#guard accountWritesTombstoneBalanceZeroFunction.startsWith "account_writes_tombstone_balance_zero:\n"
#guard accountWritesTombstoneBalanceZero_prog.length = 181
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
