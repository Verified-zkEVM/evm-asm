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
def accountWriteRecord_prog : Program :=
  [ .ADDI .x2 .x2 (-128 : BitVec 12),
    .SD .x2 .x5 (0 : BitVec 12),
    .SD .x2 .x6 (8 : BitVec 12),
    .SD .x2 .x7 (16 : BitVec 12),
    .SD .x2 .x28 (24 : BitVec 12),
    .SD .x2 .x29 (32 : BitVec 12),
    .SD .x2 .x30 (40 : BitVec 12),
    .SD .x2 .x31 (48 : BitVec 12),
    .SD .x2 .x1 (56 : BitVec 12),
    .SD .x2 .x10 (64 : BitVec 12),
    .SD .x2 .x11 (72 : BitVec 12),
    .SD .x2 .x12 (80 : BitVec 12),
    .SD .x2 .x13 (88 : BitVec 12),
    .SD .x2 .x14 (96 : BitVec 12),
    .SD .x2 .x15 (104 : BitVec 12),
    .SD .x2 .x16 (112 : BitVec 12),
    .SD .x2 .x17 (120 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_write_record + 68)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_write_record + 68)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x28 (1 : BitVec 20),
    .ADDIW .x28 .x28 (2031 : BitVec 12),
    .SLLI .x28 .x28 (19 : BitVec 6),
    .LI .x29 (0 : Word),
    .BGEU .x29 .x6 (brOff (GuestAddrs.account_write_record + 204) (GuestAddrs.account_write_record + 96)),
    .SLLI .x30 .x29 (7 : BitVec 6),
    .ADD .x30 .x28 .x30,
    .LI .x31 (20 : Word),
    .MV .x7 .x30,
    .LD .x28 .x2 (64 : BitVec 12),
    .BEQ .x31 .x0 (32 : BitVec 13),
    .LBU .x10 .x7 (0 : BitVec 12),
    .LBU .x11 .x28 (0 : BitVec 12),
    .BNE .x10 .x11 (40 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .MV .x15 .x29,
    .LI .x16 (0 : Word),
    .JAL .x1 (jalOff GuestAddrs.account_writes_undo_push (GuestAddrs.account_write_record + 160)),
    .BNE .x10 .x0 (brOff (GuestAddrs.account_write_record + 508) (GuestAddrs.account_write_record + 164)),
    .JAL .x0 (jalOff (GuestAddrs.account_write_record + 364) (GuestAddrs.account_write_record + 168)),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_write_record + 172)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_write_record + 172)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x28 (1 : BitVec 20),
    .ADDIW .x28 .x28 (2031 : BitVec 12),
    .SLLI .x28 .x28 (19 : BitVec 6),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.account_write_record + 96) (GuestAddrs.account_write_record + 200)),
    .LUI .x7 (4 : BitVec 20),
    .BGEU .x6 .x7 (brOff (GuestAddrs.account_write_record + 508) (GuestAddrs.account_write_record + 208)),
    .MV .x15 .x6,
    .LI .x16 (1 : Word),
    .JAL .x1 (jalOff GuestAddrs.account_writes_undo_push (GuestAddrs.account_write_record + 220)),
    .BNE .x10 .x0 (brOff (GuestAddrs.account_write_record + 508) (GuestAddrs.account_write_record + 224)),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_write_record + 228)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_write_record + 228)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x28 (1 : BitVec 20),
    .ADDIW .x28 .x28 (2031 : BitVec 12),
    .SLLI .x28 .x28 (19 : BitVec 6),
    .SLLI .x30 .x6 (7 : BitVec 6),
    .ADD .x30 .x28 .x30,
    .LD .x7 .x2 (64 : BitVec 12),
    .LI .x31 (20 : Word),
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
    .LD .x7 .x2 (112 : BitVec 12),
    .ANDI .x28 .x7 (1 : BitVec 12),
    .BEQ .x28 .x0 (40 : BitVec 13),
    .LD .x28 .x2 (72 : BitVec 12),
    .LD .x29 .x28 (0 : BitVec 12),
    .SD .x30 .x29 (32 : BitVec 12),
    .LD .x29 .x28 (8 : BitVec 12),
    .SD .x30 .x29 (40 : BitVec 12),
    .LD .x29 .x28 (16 : BitVec 12),
    .SD .x30 .x29 (48 : BitVec 12),
    .LD .x29 .x28 (24 : BitVec 12),
    .SD .x30 .x29 (56 : BitVec 12),
    .ANDI .x28 .x7 (2 : BitVec 12),
    .BEQ .x28 .x0 (20 : BitVec 13),
    .LD .x28 .x2 (80 : BitVec 12),
    .LD .x29 .x30 (64 : BitVec 12),
    .BLTU .x28 .x29 (8 : BitVec 13),
    .SD .x30 .x28 (64 : BitVec 12),
    .ANDI .x28 .x7 (4 : BitVec 12),
    .BEQ .x28 .x0 (20 : BitVec 13),
    .LD .x28 .x2 (88 : BitVec 12),
    .SD .x30 .x28 (80 : BitVec 12),
    .LD .x28 .x2 (96 : BitVec 12),
    .SD .x30 .x28 (88 : BitVec 12),
    .ANDI .x28 .x7 (8 : BitVec 12),
    .BEQ .x28 .x0 (12 : BitVec 13),
    .LD .x28 .x2 (104 : BitVec 12),
    .SD .x30 .x28 (72 : BitVec 12),
    .ANDI .x28 .x7 (16 : BitVec 12),
    .BEQ .x28 .x0 (12 : BitVec 13),
    .LD .x28 .x2 (120 : BitVec 12),
    .SD .x30 .x28 (96 : BitVec 12),
    .LD .x28 .x30 (112 : BitVec 12),
    .OR .x7 .x7 .x28,
    .SD .x30 .x7 (112 : BitVec 12),
    .JAL .x0 (32 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.tx_account_writes_overflow (GuestAddrs.account_write_record + 508)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_writes_overflow (GuestAddrs.account_write_record + 508)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_overflow (GuestAddrs.account_write_record + 524)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_overflow (GuestAddrs.account_write_record + 524)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x5 .x2 (0 : BitVec 12),
    .LD .x6 .x2 (8 : BitVec 12),
    .LD .x7 .x2 (16 : BitVec 12),
    .LD .x28 .x2 (24 : BitVec 12),
    .LD .x29 .x2 (32 : BitVec 12),
    .LD .x30 .x2 (40 : BitVec 12),
    .LD .x31 .x2 (48 : BitVec 12),
    .LD .x1 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (128 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountWriteRecord_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWriteRecord_relocs : RelocTable :=
  [ (17, .la .x5 "tx_account_writes_count"),
    (40, .jal .x1 "account_writes_undo_push"),
    (43, .la .x5 "tx_account_writes_count"),
    (55, .jal .x1 "account_writes_undo_push"),
    (57, .la .x5 "tx_account_writes_count"),
    (127, .la .x5 "tx_account_writes_overflow"),
    (131, .la .x5 "account_writes_overflow") ]

def accountWriteRecordFunction : String :=
  "account_write_record:\n" ++ emitProgramR accountWriteRecord_prog accountWriteRecord_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWriteRecord_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWriteRecordFunction_eq_prog :
    accountWriteRecordFunction = "account_write_record:\n" ++ emitProgramR accountWriteRecord_prog accountWriteRecord_relocs := rfl

#guard accountWriteRecordFunction.startsWith "account_write_record:\n"
#guard accountWriteRecord_prog.length = 144
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

end EvmAsm.Codegen
