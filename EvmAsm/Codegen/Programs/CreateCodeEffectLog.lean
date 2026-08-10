/-
  EvmAsm.Codegen.Programs.CreateCodeEffectLog

  Per-created-account CODE-effect log + record/lookup helpers (bead
  fhsxz.2.4.2.61.8b, the CREATE deposit slice — step .8b-1).

  When CREATE/CREATE2 deploys a contract, execution has the deployed code bytes
  (create_child_code / create_child_code_len, create_child_status == 2). The
  block verdict's all-accounts CODE comparator `bal_account_code_consistent`
  (#8591, c2's i3djw) validates each BAL account's declared `code_changes` bytes
  against an execution-derived CODE-effect record. This module is the PRODUCER +
  LOOKUP for those records, keyed by the created account's 20-byte big-endian
  address (NOT keccak — same keying as c2's non-storage effect record, per c2#5).

  Per-created-account record layout (variable stride, 8-aligned), agreed with c2
  (c2#11):
    +0   addr            (20-byte BE address in the low/first 20 bytes, padded to 32 — the key)
    +32  has_code_change (u64; always 1 for a deployed record)
    +40  code_len        (u64)
    +48  code bytes      (the deployed bytecode, code_len bytes)
  The all-accounts wrapper passes `a2 = record+32` to `bal_account_code_consistent`
  (whose record is exactly the +32.. tail: has_code_change / code_len / code bytes).

  ## Retention boundary

  This physical arena currently combines two logically distinct things: the
  append-only CODE-effect *rows* and the copied deployed-code *bytes* at
  `record+48`.  The rows are legacy comparison evidence and are slated for
  retirement after the BlockAccessListBuilder takes over.  The bytes are not a
  log: `AccountState` and same-block code lookup retain pointers into them, and
  the BAL's `CodeChange.new_code` must copy those bytes unchanged.  Therefore a
  future retirement must first move the byte heap into its own retained code
  store, or preserve it verbatim; deleting/reusing this arena with live
  AccountState/BAL pointers is invalid.  This module deliberately does not
  perform that layout split, because the current variable-stride cursor and the
  retained AccountState/code-byte readers use the packed record base.

  The CREATE-tail deposit call site (`create_record_code_effect(create_address_be,
  create_child_code, create_child_code_len)`) + EIP-3541 / MAX_CODE_SIZE / nonce
  updates land in step .8b-2; this slice is the log + helpers + a known-answer probe.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.AccountWriteMap
import EvmAsm.Codegen.ArenaCapacities

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Capacity (bytes) of the code-effect log heap. Each entry is
    `round8(48 + code_len)` with per-code `code_len ≤ MAX_CODE_SIZE = 65536`
    (Amsterdam EIP-7907 / `CreateDeployedCodeValid.maxDeployedCodeSize`).

    This is a gas-derived TOTAL arena, not a fixed per-code buffer: entry size
    is computed dynamically from the live `code_len`. The former prose claim
    "deployed code ≤ 32768" was a half-migrated EIP-7907 constant (same class
    as the EXTCODECOPY length clamp fixed in #11608) and is not a live sizing
    assumption here.

    Gas-derived bound for the full 200M block target. Code deposit charges
    `CODE_DEPOSIT_PER_BYTE = 200` gas/byte, so the total deployed bytecode in a
    `bsrStateRootBlockGasLimit`-gas block is at most `200M / 200 = 1,000,000`
    bytes. Accounting for the 32,000-gas CREATE base (which lowers the realized
    byte budget) and the per-record `+48` overhead, the worst case is reached by
    ~15 near-max (65,536-byte) deploys: `Σcᵢ ≤ 200M/200 - 160·N` still keeps
    arena `Σ round8(48+cᵢ)` under the 1.0 MiB absolute ceiling; the EIP-7907
    large-code extra gas only lowers this, and the empty-CREATE / EIP-7702
    delegation marker paths (48-byte records) are less arena-bytes-per-gas-efficient
    so cannot exceed it. The cap therefore reserves the exact 1.0 MiB ceiling.
    For nonempty code, `round8(48 + code_len) ≤ code_len + 55` while the CREATE
    base charge makes every additional record reduce the available code-byte
    budget by 160 bytes; empty CREATE/delegation records are bounded more tightly
    by their fixed per-event gas.  Thus neither form can reach the one-mebibyte
    reservation.

    On overflow the producer sets `exec_code_effect_overflow`; block_verdict
    consumes that flag as a rejection. -/
def execCodeEffectLogCap : Nat := 1048576

/-! ## Legacy CodeState source helpers (not emitted)

    `exec_code_effect_log` is an append-only comparison record: BAL's code
    comparator needs to see every execution-produced code change.  It is not a
    model of Ethereum account state (in particular, a later CREATE for the
    same address must replace an earlier one, and EIP-6780 deletion is scoped
    to the transaction which created the account).

    The historical `code_state_find`/`code_state_upsert` family below described
    a separate fixed table.  Those source strings are retained only as
    migration scaffolding; the emitted execution path uses AccountState.  Do
    not read these legacy constants as a live runtime container. -/
def codeStateEntryBytes : Nat := 64
def codeStateEntryCapacity : Nat := 8192
def codeStateTableBytes : Nat := codeStateEntryBytes * codeStateEntryCapacity

/-! ## Bounded execution AccountState (pending/durable journal retired, #11978)

    AccountState was the emitted execution model: a complete account snapshot
    per execution mutation, with a per-transaction pending journal and a
    durable latest-state map.  The account-writes migration (2ce981df8) moved
    transaction boundaries to `account_writes_*`, and #11978 deleted the
    journal outright: `account_state_pending_count`, `account_state_scratch`,
    and `account_state_durable` had zero references in the guest `.text`, and
    their consumers (`account_state_commit_pending`,
    `account_state_upsert_durable`, `account_state_publish_sender_inclusion`,
    `code_state_final_balance_nonzero`) were linked into no image.  What
    survives in the guest: the created/delete sets, the live counts and
    resolver scratch in `codeStateData`, and the EIP-7702 delegation resolver.
    The capacity constants remain because `nonstorageEffectSharedScratch`
    derives the created/delete table offsets from them and the (currently
    unlinked, #11987) probe scaffolding names them.

    38,460 entries is the gas-derived bound.  The lowest-cost operation that
    changes two accounts is a value transfer; the existing 200M-gas bound is
    38,460 raw effects.  SELFDESTRUCT additionally pays its account-access
    cost, keeping its two-account writes below this cap. -/
def accountStateEntryBytes : Nat := 128
def accountStateEntryCapacity : Nat := 38460
def accountStateTableBytes : Nat := accountStateEntryBytes * accountStateEntryCapacity
-- `accountStateCreatedCapacity` moved to `EvmAsm.Codegen.ArenaCapacities` (imported
-- above) so the two sites that mark `created_accounts` can both name it; unchanged at 8192.

/-! AccountState entry layout (all fields are fixed-width and 8-byte aligned):

      +0   address (20-byte BE, zero-padded to 32)
      +32  balance (32-byte BE)
      +64  nonce (u64)
      +72  code pointer (u64)
      +80  code length (u64)
      +88  flags (occupied, exists, code-present, created-this-tx, delete-pending,
                  code-resolved, auth-nonce)
      +96  reserved (32 bytes; retained so future state fields do not change stride)

    This record shape is retained for the probe-side snapshot producers
    (`account_state_record_nonstorage`, `code_state_record_code_effect`).  The
    pending-journal semantics the shape was designed for — append-only
    snapshots with high-water-mark rollback, plus a durable real-address
    upsert map — were retired in #11978 together with the journal cells. -/

/-! ## account_state_find

    a0 = canonical 20-byte BE address pointer
    a1 = fixed 128-byte AccountState table base
    a2 = populated entry count
    a3 = entry capacity
    returns a0 = latest matching occupied entry, or zero.

    The forward scan intentionally records the final hit.  Pending is a journal
    and can contain several snapshots for one address; latest-wins is therefore
    the state semantics rather than merely a defensive duplicate policy. -/
def accountStateFindFunction : String :=
  "account_state_find:\n" ++
  "  addi sp, sp, -16; sd a3, 0(sp)\n" ++
  "  bgtu a2, a3, .Lasf_miss\n" ++
  "  mv t0, a1; li t1, 0; li t2, 0\n" ++
  ".Lasf_entry:\n" ++
  "  bgeu t1, a2, .Lasf_done\n" ++
  "  li t3, 0\n" ++
  ".Lasf_bytes:\n" ++
  "  li t4, 20; beq t3, t4, .Lasf_hit; add t4, a0, t3; lbu t5, 0(t4); add t4, t0, t3; lbu t6, 0(t4); bne t5, t6, .Lasf_next; addi t3, t3, 1; j .Lasf_bytes\n" ++
  ".Lasf_hit:\n" ++
  "  ld t4, 88(t0); andi t4, t4, 1; beqz t4, .Lasf_next; mv t2, t0\n" ++
  ".Lasf_next:\n" ++
  "  addi t0, t0, 128; addi t1, t1, 1; j .Lasf_entry\n" ++
  ".Lasf_done:\n" ++
  "  mv a0, t2; ld a3, 0(sp); addi sp, sp, 16; ret\n" ++
  ".Lasf_miss:\n" ++
  "  li a0, 0; ld a3, 0(sp); addi sp, sp, 16; ret"

/-! ## account_state_copy

    a0 = 128-byte source snapshot, a1 = 128-byte destination snapshot.
    Snapshot copying is deliberately whole-record: a balance-only writer cannot
    accidentally discard nonce/code/existence owned by another execution path. -/
def accountStateCopyFunction : String :=
  "account_state_copy:\n" ++
  "  li t0, 0\n" ++
  ".Lasc_loop:\n" ++
  "  li t1, 128; beq t0, t1, .Lasc_done; add t2, a0, t0; ld t3, 0(t2); add t2, a1, t0; sd t3, 0(t2); addi t0, t0, 8; j .Lasc_loop\n" ++
  ".Lasc_done:\n" ++
  "  ret"

/-! ## account_state_append_pending

    a0 = full AccountState snapshot, a1 = pending base, a2 = count pointer,
    a3 = capacity.  Returns zero on append and one on a capacity/count error.
    This is the only pending writer: callers must first resolve a full snapshot,
    modify their owned fields, then journal the result through this helper. -/
def accountStateAppendPendingFunction : String :=
  "account_state_append_pending:\n" ++
  "  addi sp, sp, -32; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd a3, 24(sp); mv s0, a0; mv s1, a1\n" ++
  "  ld t0, 0(a2); bgtu t0, a3, .Lasap_over; bgeu t0, a3, .Lasap_over; slli t1, t0, 7; add a1, s1, t1; mv a0, s0; jal ra, account_state_copy; ld t0, 0(a2); addi t0, t0, 1; sd t0, 0(a2); li a0, 0; j .Lasap_ret\n" ++
  ".Lasap_over:\n" ++
  "  li a0, 1\n" ++
  ".Lasap_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld a3, 24(sp); addi sp, sp, 32; ret"

/-! ## account_state_record_nonstorage

    Adapt the existing non-storage producer ABI to a complete AccountState
    snapshot.  The raw producer remains the comparison trace; this helper is
    the execution-state mirror of the same transition.  It clones an existing
    pending/durable snapshot when available, overwrites the balance only when
    the producer changed it, and merges the supplied nonce monotonically.  Thus
    a balance mutation preserves the code/existence fields written by CREATE,
    while a nonce-only mutation does not claim authority over a balance it did
    not change.

    a0 = address, a1 = pre-balance (comparison-only), a2 = post-balance,
    a3 = pre-nonce (comparison-only), a4 = post-nonce.  It returns zero on
    success and one on bounded-arena failure. -/
def accountStateRecordNonstorageFunction : String :=
  "account_state_record_nonstorage:\n" ++
  "  addi sp, sp, -64; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd a3, 32(sp); sd a4, 40(sp)\n" ++
  -- Equal balance operands are used by the CREATE pre-descent nonce-only
  -- record.  That transition must preserve the cloned balance rather than
  -- replacing it with the post-debit scratch value.  Remember whether this
  -- producer actually changes balance before the lookup helpers clobber a1/a2.
  "  li t0, 0\n" ++
  "  ld t1, 0(a1); ld t2, 0(a2); bne t1, t2, .Lasrn_balance_changed\n" ++
  "  ld t1, 8(a1); ld t2, 8(a2); bne t1, t2, .Lasrn_balance_changed\n" ++
  "  ld t1, 16(a1); ld t2, 16(a2); bne t1, t2, .Lasrn_balance_changed\n" ++
  "  ld t1, 24(a1); ld t2, 24(a2); beq t1, t2, .Lasrn_balance_cmp_done\n" ++
  ".Lasrn_balance_changed:\n" ++
  "  li t0, 1\n" ++
  ".Lasrn_balance_cmp_done:\n" ++
  "  sd t0, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a2; mv s2, a4\n" ++
  "  la a1, account_state_pending; la t0, account_state_pending_count; ld a2, 0(t0); li a3, " ++ toString accountStateEntryCapacity ++ "; jal ra, account_state_find; bnez a0, .Lasrn_clone\n" ++
  "  mv a0, s0; la a1, account_state_durable; la t0, account_state_durable_count; ld a2, 0(t0); li a3, " ++ toString accountStateEntryCapacity ++ "; jal ra, account_state_find; bnez a0, .Lasrn_clone\n" ++
  "  la t0, account_state_scratch; li t1, 0\n" ++
  ".Lasrn_zero:\n" ++
  "  li t2, 128; beq t1, t2, .Lasrn_fields; add t3, t0, t1; sd zero, 0(t3); addi t1, t1, 8; j .Lasrn_zero\n" ++
  ".Lasrn_clone:\n" ++
  "  la a1, account_state_scratch; jal ra, account_state_copy\n" ++
  ".Lasrn_fields:\n" ++
  "  la t0, account_state_scratch; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0); li t1, 0\n" ++
  ".Lasrn_addr:\n" ++
  "  li t2, 20; beq t1, t2, .Lasrn_balance; add t2, s0, t1; lbu t3, 0(t2); add t2, t0, t1; sb t3, 0(t2); addi t1, t1, 1; j .Lasrn_addr\n" ++
  ".Lasrn_balance:\n" ++
  -- Bit 5 records that balance is authoritative.  Code-only
  -- snapshots deliberately leave it clear: they must not turn an unknown
  -- account balance/nonce into an authoritative zero before the companion
  -- non-storage effect is published.
  -- A later non-storage producer may change only balance (notably the
  -- sender-is-coinbase fee credit).  Preserve an already-authoritative nonce
  -- when that producer's nonce is unchanged, but seed the producer's nonce
  -- when this is the first authoritative snapshot for the address.  Nonces
  -- only advance during a transaction, so a later publisher carrying a stale
  -- transition must not overwrite an already-recorded authorization increment.
  -- When balance is unchanged, retain the cloned balance bytes.  A nonce-only
  -- effect must not make a debited pre-descent balance authoritative after a
  -- failed CREATE restores the runtime env but rolls back the child transfer.
  "  ld t1, 56(sp); beqz t1, .Lasrn_balance_preserved\n" ++
  "  ld t1, 0(s1); sd t1, 32(t0); ld t1, 8(s1); sd t1, 40(t0); ld t1, 16(s1); sd t1, 48(t0); ld t1, 24(s1); sd t1, 56(t0)\n" ++
  ".Lasrn_balance_preserved:\n" ++
  "  ld t1, 88(t0); ld t2, 32(sp); bne t2, s2, .Lasrn_write_nonce; andi t3, t1, 96; bnez t3, .Lasrn_nonce_unchanged\n" ++
  ".Lasrn_write_nonce:\n" ++
  -- Monotonic nonce merge. When this producer publishes a real nonce
  -- transition (pre≠post), also set bit 6 so account_state_latest_nonce
  -- trusts the field. Bit 5 alone is balance-present (#10619 split): a
  -- balance-only snapshot with dummy equal nonces must NOT set bit 6 or a
  -- zero nonce would shadow authenticated pre-state. Creator CREATE/CREATE2
  -- bumps (pin system.py generic_create increment_nonce at BOTH the collide
  -- :118 and deployable :132 sites — unconditional w.r.t. deployability)
  -- rely on bit 6 so a later tx seeds create_nonce from the durable
  -- post-nonce. 01087 factory: writer DID fire (nonce field written) but
  -- missing the BIT (ori 35 only), not a missing writer branch.
  "  ld t2, 64(t0); bgeu t2, s2, .Lasrn_nonce_mark; sd s2, 64(t0)\n" ++
  ".Lasrn_nonce_mark:\n" ++
  "  ld t2, 32(sp); beq t2, s2, .Lasrn_nonce_unchanged; ori t1, t1, 64\n" ++
  ".Lasrn_nonce_unchanged:\n" ++
  "  ld t2, 56(sp); beqz t2, .Lasrn_no_balance_mark; ori t1, t1, 32\n" ++
  ".Lasrn_no_balance_mark:\n" ++
  "  ori t1, t1, 3; sd t1, 88(t0)\n" ++
  "  la a0, account_state_scratch; la a1, account_state_pending; la a2, account_state_pending_count; li a3, " ++ toString accountStateEntryCapacity ++ "; jal ra, account_state_append_pending; beqz a0, .Lasrn_ret; la t0, account_state_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".Lasrn_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld a3, 32(sp); ld a4, 40(sp); addi sp, sp, 64; ret"

/-! ## account_state_record_code

    Mirror a successful CREATE code deposit into the complete AccountState
    journal.  It has the same clone-then-overwrite discipline as the
    non-storage adapter, preserving a prior balance/nonce snapshot while
    updating code/existence.  `created-this-tx` is retained as an explicit
    bit for EIP-6780 finalization after the source switch.

    a0 = address, a1 = retained code pointer, a2 = code length, a3 = optional
    execution-state resolver output (zero for the standalone probe).
    Returns zero on success and one on bounded-arena failure. -/
def accountStateRecordCodeFunction : String :=
  "account_state_record_code:\n" ++
  "  addi sp, sp, -48; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd a3, 32(sp); mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  la a1, account_state_pending; la t0, account_state_pending_count; ld a2, 0(t0); li a3, " ++ toString accountStateEntryCapacity ++ "; jal ra, account_state_find; bnez a0, .Lasrc_clone\n" ++
  "  mv a0, s0; la a1, account_state_durable; la t0, account_state_durable_count; ld a2, 0(t0); li a3, " ++ toString accountStateEntryCapacity ++ "; jal ra, account_state_find; bnez a0, .Lasrc_clone\n" ++
  "  la t0, account_state_scratch; li t1, 0\n" ++
  ".Lasrc_zero:\n" ++
  "  li t2, 128; beq t1, t2, .Lasrc_seed; add t3, t0, t1; sd zero, 0(t3); addi t1, t1, 8; j .Lasrc_zero\n" ++
  -- Seed only the pre-state fields when the CREATE target was absent from
  -- both execution overlays.  These fields are a baseline for the later
  -- non-storage producer, not authoritative execution components, so the
  -- code row keeps its existing mask.  A zero a3 preserves the standalone
  -- probe's old contract.
  ".Lasrc_seed:\n" ++
  "  ld t4, 32(sp); beqz t4, .Lasrc_fields; ld t1, 8(t4); sd t1, 32(t0); ld t1, 16(t4); sd t1, 40(t0); ld t1, 24(t4); sd t1, 48(t0); ld t1, 32(t4); sd t1, 56(t0); ld t1, 0(t4); sd t1, 64(t0); j .Lasrc_fields\n" ++
  ".Lasrc_clone:\n" ++
  "  la a1, account_state_scratch; jal ra, account_state_copy\n" ++
  ".Lasrc_fields:\n" ++
  "  la t0, account_state_scratch; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0); li t1, 0\n" ++
  ".Lasrc_addr:\n" ++
  "  li t2, 20; beq t1, t2, .Lasrc_code; add t2, s0, t1; lbu t3, 0(t2); add t2, t0, t1; sb t3, 0(t2); addi t1, t1, 1; j .Lasrc_addr\n" ++
  ".Lasrc_code:\n" ++
  -- AccountState `flags@+88` (GH #11706). VALUES, never indices — the seed below
  -- is literal 27 = 16 + 8 + 2 + 1, and `ori t1, t1, 4` raises it to 31:
  --   VALUE 16 = code is KNOWN, so a balance-only snapshot never masks
  --              authenticated pre-block code (always set by this writer);
  --   VALUE  4 = code is NONEMPTY (added only when the length `s2` is nonzero).
  -- The distinction is code-known versus code-nonempty; an earlier wording gave
  -- these as "bit 4" and "bit 2", which are the INDICES of 16 and 4 — read as
  -- values that sentence self-contradicts, because 27 already contains value 2
  -- yet is the zero-length-code seed.
  --
  -- ⛔ These constants belong to `flags@+88` in THIS structure and must not be
  -- carried into `account_writes`' `execFlags@+96` (stride 128, base 0xbdb80000 /
  -- 0xbf780000): 27 and 31 both contain VALUE 8, which at +96 is the
  -- created-this-tx bit read by `account_writes_created_contains` (.Lawc_key:
  -- `ld t1, 96(t5); andi t1, t1, 8`). See `accountWriteHasExecFlags` in
  -- `AccountWriteMap.lean` for the +96 value table.
  "  sd s1, 72(t0); sd s2, 80(t0); li t1, 27; beqz s2, .Lasrc_flags; ori t1, t1, 4\n" ++
  ".Lasrc_flags:\n" ++
  "  sd t1, 88(t0); la a0, account_state_scratch; la a1, account_state_pending; la a2, account_state_pending_count; li a3, " ++ toString accountStateEntryCapacity ++ "; jal ra, account_state_append_pending; beqz a0, .Lasrc_ret; la t0, account_state_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".Lasrc_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld a3, 32(sp); addi sp, sp, 48; ret"

/-! ## account_write_touch_current

    First TOUCHED producer (#11329 / entry6). Publishes a TOUCHED-only
    transaction-map row (VALUE 32 sticky-OR'd), so root enumeration sees the
    address even when no BALANCE/NONCE/CODE delta is present. Existing map
    components are preserved by `account_write_record`'s fieldwise upsert.

    a0 = canonical 20-byte BE address pointer.
    Does NOT call `account_read_record` (touch is a write-side fact, not a read).
    The helper never reads the retired pending/durable AccountState arrays.
    Missing map components remain missing and are resolved by the map-side
    builder fallback at the transaction boundary.

    Clobbers only what `account_write_record` already restores. -/
def accountWriteTouchCurrentFunction : String :=
  "account_write_touch_current:\n" ++
  -- Preserve full arg set: SSTORE callers hold x13=mem (a3) live across this call.
  "  addi sp, sp, -80; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  sd a0, 24(sp); sd a1, 32(sp); sd a2, 40(sp); sd a3, 48(sp); sd a4, 56(sp); sd a5, 64(sp); sd a6, 72(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv a0, s0; li a1, 0; li a2, 0; li a3, 0; li a4, 0; li a5, 0; li a6, " ++ toString accountWriteHasTouched ++ "; li a7, 0; jal ra, account_write_record\n" ++
  ".Lawtc_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  ld a0, 24(sp); ld a1, 32(sp); ld a2, 40(sp); ld a3, 48(sp); ld a4, 56(sp); ld a5, 64(sp); ld a6, 72(sp)\n" ++
  "  addi sp, sp, 80; ret\n"

/-! Transaction-local EIP-6780 membership query.  This reads only the
    AccountState `created_accounts` set, never the durable map: an account
    created in a prior transaction must remain live after SELFDESTRUCT. -/
def accountStateCreatedContainsFunction : String :=
  "account_state_created_contains:\n" ++
  "  la t0, account_state_overflow; ld t1, 0(t0); bnez t1, .Lascc_overflow\n" ++
  "  la t0, account_state_created_count; ld t1, 0(t0); li t2, " ++ toString accountStateCreatedCapacity ++ "; bgtu t1, t2, .Lascc_no; li t2, 0; la t3, account_state_created\n" ++
  ".Lascc_entry:\n" ++
  "  bgeu t2, t1, .Lascc_no; li t4, 0\n" ++
  ".Lascc_bytes:\n" ++
  "  li t5, 20; beq t4, t5, .Lascc_yes; add t5, a0, t4; lbu t6, 0(t5); add t5, t3, t4; lbu a1, 0(t5); bne t6, a1, .Lascc_next; addi t4, t4, 1; j .Lascc_bytes\n" ++
  ".Lascc_next:\n" ++
  "  addi t3, t3, 32; addi t2, t2, 1; j .Lascc_entry\n" ++
  ".Lascc_yes:\n" ++
  "  li a0, 1; ret\n" ++
  ".Lascc_no:\n" ++
  "  li a0, 0; ret\n" ++
  ".Lascc_overflow:\n" ++
  "  li a0, 2; ret"

/-! ## codeStateStatusIsLiveAsm

    Coarse status→live map: status ∈ {1,2} → 1, else 0. This is **not** full
    pin `is_account_alive` (state_tracker.py:445-463 = account ≠ EMPTY_ACCOUNT).
    Status 2 conflates funded EOAs / bal-preserved tombstones (alive) with
    bal-zero EIP-6780 tombstones (EMPTY after nonce clear). Every NEW_ACCOUNT
    consumer must gate status-2 through balance (and nonce where relevant)
    before trusting this helper — see ChildFrameHandlers nacc/ibnacc,
    Selfdestruct beneficiary surcharge, and ChildFrameCreateTail
    (balance_live_else_header_state_root + nonce). -/
def codeStateStatusIsLiveAsm (statusReg : String) : String :=
  "  addi t0, " ++ statusReg ++ ", -1\n" ++
  "  sltiu " ++ statusReg ++ ", t0, 2\n"

/-! ## code_state_address_set_insert

    Bounded 32-byte-address set used for transaction-local `created_accounts`
    and deferred EIP-6780 deletes.  The first 20 bytes are the canonical BE
    address; the zero padding is maintained by the caller-owned static arena.
    a0 = address, a1 = set base, a2 = count pointer, a3 = capacity.
    Returns 0 when already present/inserted, 1 on capacity failure. -/
def codeStateAddressSetInsertFunction : String :=
  "code_state_address_set_insert:\n" ++
  "  addi sp, sp, -16; sd a3, 0(sp)\n" ++
  "  ld t0, 0(a2); bgtu t0, a3, .Lcsasi_over; li t1, 0; mv t2, a1\n" ++
  ".Lcsasi_scan:\n" ++
  "  bgeu t1, t0, .Lcsasi_append; li t3, 0\n" ++
  ".Lcsasi_cmp:\n" ++
  "  li t4, 20; beq t3, t4, .Lcsasi_ok; add t4, a0, t3; lbu t5, 0(t4); add t4, t2, t3; lbu t6, 0(t4); bne t5, t6, .Lcsasi_next; addi t3, t3, 1; j .Lcsasi_cmp\n" ++
  ".Lcsasi_next:\n" ++
  "  addi t2, t2, 32; addi t1, t1, 1; j .Lcsasi_scan\n" ++
  ".Lcsasi_append:\n" ++
  "  bgeu t0, a3, .Lcsasi_over; slli t1, t0, 5; add t2, a1, t1; sd zero, 0(t2); sd zero, 8(t2); sd zero, 16(t2); sd zero, 24(t2); li t3, 0\n" ++
  ".Lcsasi_copy:\n" ++
  "  li t4, 20; beq t3, t4, .Lcsasi_inc; add t4, a0, t3; lbu t5, 0(t4); add t4, t2, t3; sb t5, 0(t4); addi t3, t3, 1; j .Lcsasi_copy\n" ++
  ".Lcsasi_inc:\n" ++
  "  addi t0, t0, 1; sd t0, 0(a2)\n" ++
  ".Lcsasi_ok:\n" ++
  "  li a0, 0; ld a3, 0(sp); addi sp, sp, 16; ret\n" ++
  ".Lcsasi_over:\n" ++
  "  li a0, 1; ld a3, 0(sp); addi sp, sp, 16; ret"

/-! ## code_state_address_set_flag

    Set the 64-bit flag at +24 in a 32-byte address-set entry.  The delete
    set uses it as an active deferred-delete bit: CREATE cancels a prior
    same-transaction delete by clearing it, while SELFDESTRUCT sets it.  This
    preserves ordering without making code visibility disappear before tx end.
    a0 = address, a1 = set base, a2 = count pointer, a3 = capacity, a4 = flag.
    Returns 0 on a matching entry, 1 on a malformed/missing entry. -/
def codeStateAddressSetFlagFunction : String :=
  "code_state_address_set_flag:\n" ++
  "  addi sp, sp, -16; sd a3, 0(sp)\n" ++
  "  ld t0, 0(a2); bgtu t0, a3, .Lcsasf_miss; li t1, 0; mv t2, a1\n" ++
  ".Lcsasf_scan:\n" ++
  "  bgeu t1, t0, .Lcsasf_miss; li t3, 0\n" ++
  ".Lcsasf_cmp:\n" ++
  "  li t4, 20; beq t3, t4, .Lcsasf_hit; add t4, a0, t3; lbu t5, 0(t4); add t4, t2, t3; lbu t6, 0(t4); bne t5, t6, .Lcsasf_next; addi t3, t3, 1; j .Lcsasf_cmp\n" ++
  ".Lcsasf_next:\n" ++
  "  addi t2, t2, 32; addi t1, t1, 1; j .Lcsasf_scan\n" ++
  ".Lcsasf_hit:\n" ++
  "  sd a4, 24(t2); li a0, 0; ld a3, 0(sp); addi sp, sp, 16; ret\n" ++
  ".Lcsasf_miss:\n" ++
  "  li a0, 1; ld a3, 0(sp); addi sp, sp, 16; ret"

/-! Fixed static data for the AccountState execution overlay.  The `created`
    and `delete` sets use the same 32-byte padded-address key representation. -/
def codeStateData : String :=
  ".balign 8\n" ++
  -- Reserved compatibility cell.  The universal transaction loop and
  -- callable dispatcher deliberately leave it unread and unwritten.
  "runtime_mtx_active:\n  .zero 8\n" ++
  -- tqj1m: AccountState is the sole execution-state source.  The old
  -- CodeState tables were retired after the atomic reader cutover.
  -- #11978: account_state_pending_count was deleted outright (zero guest
  -- .text references); account_state_durable_count remains as a
  -- compatibility cell for the retained comparison-record producer.
  "account_state_durable_count:\n  .zero 8\n" ++
  "account_state_created_count:\n  .zero 8\n" ++
  "account_state_delete_count:\n  .zero 8\n" ++
  "account_state_overflow:\n  .zero 8\n" ++
  -- BAL final-account scratch for the EIP-161 deferred-delete decision.
  "account_resolver_pre_acct:\n  .zero 48\n" ++
  -- account_resolve_execution_state output for CREATE code publication:
  -- nonce@0, balance@8..40, code pointer@40, code length@48, present@56.
  ".balign 8\n" ++
  "create_resolved_account_state:\n  .zero 64\n"

/-! ## create_record_code_effect

    Append one deployed-code record to the code-effect log.

    Calling convention:
      a0 = 20-byte big-endian address ptr (the created account)
      a1 = deployed code ptr
      a2 = deployed code length (bytes)
    Returns:
      a0 = 0 appended ok / 1 capacity overflow (record NOT written; overflow flag set)
    Clobbers t0-t6, a0; preserves s-regs (saved). -/
def createRecordCodeEffectFunction (resolveExecutionState : Bool := true) : String :=
  "create_record_code_effect:\n" ++
  -- Record empty-code CREATEs with has_code_change=0 so that EXTCODEHASH/EXTCODESIZE
  -- (#9525 fix) can find the address and return keccak("")/0 respectively, while the
  -- bv_fail=46 code-consistency comparator skips records with has_code_change=0.
  ".Lcrce_nonempty:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp); sd s3, 24(sp); sd ra, 32(sp)\n" ++
  "  mv s0, a0                   # addr ptr (20B BE)\n" ++
  "  mv s1, a1                   # code ptr\n" ++
  "  mv s2, a2                   # code_len\n" ++
  "  la t0, exec_code_effect_next; ld s3, 0(t0)        # s3 = current free offset\n" ++
  "  addi t0, s2, 55; andi t0, t0, -8                  # t0 = round8(48 + code_len)\n" ++
  "  add t1, s3, t0                                    # t1 = new free offset\n" ++
  "  li t2, " ++ toString execCodeEffectLogCap ++ "\n" ++
  "  bgtu t1, t2, .Lcrce_overflow\n" ++
  (if resolveExecutionState then
    -- Resolve the complete execution account before publishing either the code
    -- effect row or its AccountState mirror.  Status 4 is witness
    -- incompleteness (a valid block may lack a code preimage); status 5 is a
    -- malformed authenticated lookup.  Neither status may fall back to
    -- fabricated empty code or append a partial row.
    "  la a1, create_resolved_account_state; la t0, sv_pre_rlp_ptr; ld a2, 0(t0); la t0, sv_pre_rlp_len; ld a3, 0(t0); la t0, bv_witness_state_ptr; ld a4, 0(t0); la t0, bv_witness_state_len; ld a5, 0(t0); la t0, svf_codes_ptr; ld a6, 0(t0); la t0, svf_codes_len; ld a7, 0(t0); mv a0, s0; jal ra, account_resolve_execution_state\n" ++
    "  li t0, 4; beq a0, t0, .Lcrce_resolver_unavailable; li t0, 5; beq a0, t0, .Lcrce_resolver_malformed\n"
  else "") ++
  "  la t3, exec_code_effect_log; add t3, t3, s3       # t3 = entry base\n" ++
  "  sd x0, 0(t3); sd x0, 8(t3); sd x0, 16(t3); sd x0, 24(t3)   # zero 32B addr field\n" ++
  "  mv t4, s0; mv t5, t3; li t6, 20\n" ++
  ".Lcrce_cpa:\n" ++
  "  beqz t6, .Lcrce_cpa_d\n" ++
  "  lbu a0, 0(t4); sb a0, 0(t5); addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lcrce_cpa\n" ++
  ".Lcrce_cpa_d:\n" ++
  "  li t4, 0; beqz s2, .Lcrce_hcc; li t4, 1\n" ++
  ".Lcrce_hcc:\n" ++
  "  sd t4, 32(t3)                           # has_code_change = (code_len != 0) ? 1 : 0\n" ++
  "  sd s2, 40(t3)                                     # code_len\n" ++
  "  addi t5, t3, 48; mv t4, s1; mv t6, s2\n" ++
  ".Lcrce_cpc:\n" ++
  "  beqz t6, .Lcrce_cpc_d\n" ++
  "  lbu a0, 0(t4); sb a0, 0(t5); addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lcrce_cpc\n" ++
  ".Lcrce_cpc_d:\n" ++
  "  la t0, exec_code_effect_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  la t0, exec_code_effect_next; addi t1, s2, 55; andi t1, t1, -8; add t1, s3, t1; sd t1, 0(t0)\n" ++
  -- GH #10784 cut 2: the `created_accounts` mark MOVED OUT of this routine to the
  -- pre-body position the spec uses (`vm/interpreter.py:208`, before `process_message`
  -- at :212).  Both live callers now mark before the initcode runs — the nested route
  -- in `create_frame_descend`, the top-level route in `BlockVerdictCreationStage` —
  -- so an insert here was redundant on one path and too late on the other.  The
  -- population is two: `jal ra, create_record_code_effect` occurs exactly twice in
  -- `gen-out/regionmap/stateless_guest.s` (the self-test call sites at the bottom of
  -- this file are not emitted).  A successful deposit is still an AccountState code
  -- event, which is the `account_state_record_code` call above and is unchanged.
  -- ⚠️ GH #10976: THIS CALL IS A NO-OP TODAY AND IS KEPT DELIBERATELY.  It runs on every
  -- successful deposit and its miss return is ignored, so it will never show up as
  -- unexecuted in a coverage or reachability analysis — only the precondition finds it.
  --
  -- Its stated purpose is that a successful later CREATE at the same address is the latest
  -- transaction state and cancels an earlier same-transaction EIP-6780 delete request.
  -- **That CREATE cannot succeed.**  `account_deployable` requires nonce 0 and empty code;
  -- SELFDESTRUCT clears neither mid-transaction (the clearing is at `fork.py:1201`, after
  -- execution); and the `modify_state` destroy-cascade that might otherwise have rescued it
  -- needs nonce 0 too (`account_exists_and_is_empty`).  So there is never a delete row here
  -- to cancel, and the flag-clear always misses.
  --
  -- WHY IT STAYS RATHER THAN BEING DELETED.  The delete set is an IN-PLACE editor whose
  -- rollback is a HIGH-WATER MARK, which is the one cell of the append-versus-in-place ×
  -- mark-versus-journal grid that is actually unsound (GH #10966).  This call is the only
  -- barrier between a future reachability change and that combination: if anything ever makes
  -- a same-transaction re-CREATE at a destroyed address succeed, the cancel must already be
  -- here or a stale delete request survives into commit.  One instruction on the
  -- successful-deposit path is a fair price for that, and unlike a dead SYMBOL a no-op CALL
  -- does not pollute any allocation census.
  --
  -- WHAT WOULD MAKE IT LIVE: any change that lets `account_deployable` admit an address with a
  -- pending same-transaction delete — e.g. clearing nonce/code at SELFDESTRUCT time rather than
  -- at `fork.py:1201`, or a destroy-cascade that no longer requires nonce 0.  If you are
  -- editing either, this line is load-bearing and its miss return should start being checked.
  "  mv a0, s0; la a1, account_state_delete; la a2, account_state_delete_count; li a3, " ++ toString accountStateDeleteCapacity ++ "; li a4, 0; jal ra, code_state_address_set_flag\n" ++
  -- CREATE writes code, existence, and nonce=1 into the transaction-local map.
  -- Balance remains absent here: value flow owns its own nonstorage record.
  --
  -- GH #10887: THE CODE POINTER IS THE RETAINED HEAP COPY, NOT `s1`.  `s1` is
  -- `create_child_code` — the reusable create-child scratch, which lives in
  -- `evm_memory_pool` — and the `account_state_record_code` call above already says
  -- in as many words to publish "from the retained heap copy, never from the
  -- reusable create-child scratch".  This call did not, and the account-write row
  -- carries its `a3` straight through to `bal_builder_append_code`
  -- (`AccountWriteMap.lean` `+80`/`+88`), so the BAL's `code_changes` value was a
  -- pointer into EVM memory.
  --
  -- MEASURED, on 12925: the bytes ARE written there (`extcodecopy_at_header_state_root`
  -- stores `30 60 00 52 60 20 60 00 f3`), then `h_STATICCALL` zeroes the window when
  -- the next call frame clears its memory — correct EVM behaviour — and the
  -- serializer reads nine zeros 590k commits later.  The length was always right
  -- because the length is copied by value; only the bytes were aliased.
  --
  -- The heap copy is the one the module's header requires: "the BAL's
  -- `CodeChange.new_code` must copy those bytes unchanged", and `AccountState`
  -- already retains pointers into it, which is why it may not be reused or deleted.
  -- Same expression as the sibling call, recomputed rather than carried because
  -- `account_state_record_code` and the two set helpers between them may clobber
  -- `t0`; `s3` is the entry offset and survives (callees preserve `s`).
  "  mv a0, s0; li a1, 0; li a2, 1; la t0, exec_code_effect_log; add t0, t0, s3; addi a3, t0, 48; mv a4, s2; li a5, 1; li a6, " ++ toString (accountWriteHasNonce + accountWriteHasCode + accountWriteHasState + accountWriteHasExecFlags + accountWriteHasTouched) ++ "; li a7, 27; jal ra, account_write_record\n" ++
  "  li a0, 0\n" ++
  "  j .Lcrce_ret\n" ++
  (if resolveExecutionState then
    ".Lcrce_resolver_unavailable:\n" ++
    "  la t0, create_deposit_witness_incomplete_flag; li t1, 1; sd t1, 0(t0); li a0, 2; j .Lcrce_ret\n" ++
    ".Lcrce_resolver_malformed:\n" ++
    "  la t0, create_deposit_malformed_flag; li t1, 1; sd t1, 0(t0); li a0, 3; j .Lcrce_ret\n"
  else "") ++
  ".Lcrce_overflow:\n" ++
  "  la t0, exec_code_effect_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  "  li a0, 1\n" ++
  ".Lcrce_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp); ld ra, 32(sp); addi sp, sp, 40\n" ++
  "  ret"

-- The two guards below sit HERE, beside the routine they constrain, and NOT after
-- `findCodeEffectByAddressFunction` where I first put them: that def, its
-- correspondence theorem and its own guards are ONE GENERATED BLOCK that
-- `scripts/asm_to_program.py` matches VERBATIM, so inserting anything between them
-- is source drift.  `lake build` passes either way -- the drift check is a separate
-- CI gate -- which is exactly why the placement has to be deliberate.
--
-- GH #10887: NEGATIVE guard.  The code pointer handed to `account_write_record`
-- must NOT be `s1` -- that is the reusable create-child scratch in
-- `evm_memory_pool`, and the BAL's `code_changes` value is this pointer.  Pinned
-- negatively because `mv a3, s1` is well-formed, produces a correct LENGTH, and
-- fails only in the bytes, 590k commits later, at equal serialized length.
#guard (createRecordCodeEffectFunction.splitOn "mv a3, s1").length == 1
-- And positively that it is the retained heap copy, pinned WITH the offset: the
-- record's bytes start at +48, so a pointer to the record base would serialize the
-- 20-byte address and the length fields as if they were code.
#guard (createRecordCodeEffectFunction.splitOn
  "la t0, exec_code_effect_log; add t0, t0, s3; addi a3, t0, 48").length == 2

/-! ## find_code_effect_by_address

    Locate the code-effect record for an account by its 20-byte BE address.

    Calling convention:
      a0 = code-effect log base ptr
      a1 = entry count
      a2 = 20-byte big-endian address ptr
    Returns:
      a0 = record ptr (at the +0 addr field; pass record+32 to
           bal_account_code_consistent) or 0 if not found.
    Walks variable-stride entries (round8(48 + code_len)). Clobbers t0-t6, a0. -/
def findCodeEffectByAddress_prog : Program :=
  [ .MV .x5 .x10,
    .MV .x6 .x11,
    .BEQ .x6 .x0 (80 : BitVec 13),
    .MV .x7 .x5,
    .MV .x28 .x12,
    .LI .x29 (20 : Word),
    .BEQ .x29 .x0 (56 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .LBU .x31 .x28 (0 : BitVec 12),
    .BNE .x30 .x31 (20 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LD .x30 .x5 (40 : BitVec 12),
    .ADDI .x30 .x30 (55 : BitVec 12),
    .ANDI .x30 .x30 (-8 : BitVec 12),
    .ADD .x5 .x5 .x30,
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-68 : BitVec 21),
    .MV .x10 .x5,
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def findCodeEffectByAddressFunction : String :=
  "find_code_effect_by_address:\n" ++ emitProgram findCodeEffectByAddress_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `findCodeEffectByAddress_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem findCodeEffectByAddressFunction_eq_prog :
    findCodeEffectByAddressFunction = "find_code_effect_by_address:\n" ++ emitProgram findCodeEffectByAddress_prog := rfl

#guard findCodeEffectByAddressFunction.startsWith "find_code_effect_by_address:\n"
#guard findCodeEffectByAddress_prog.length = 24

/-! ## find_code_effect_by_hash

    Spec `code_writes` is `Dict[Hash32, Bytes]` (state_tracker get_code): a hit
    on **hash**, not address, returns without recording a code_read. CREATE of
    code C then CALL to a different pre-state account with the same bytecode
    (eip8025 `witness_codes_create_same_hash_then_read`) must not demand C in
    witness.codes — GH #11542 bv11 / 02274.

    Calling convention:
      a0 = code-effect log base
      a1 = entry count
      a2 = 32-byte code-hash ptr
    Returns a0 = matching record ptr or 0.
    Walks variable-stride entries; keccak256(code@+48, code_len@+40) vs a2. -/
def findCodeEffectByHashFunction : String :=
  "find_code_effect_by_hash:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # cursor\n" ++
  "  mv s1, a1                   # remaining\n" ++
  "  mv s2, a2                   # want hash ptr\n" ++
  ".Lfceh_loop:\n" ++
  "  beqz s1, .Lfceh_miss\n" ++
  "  ld a1, 40(s0)               # code_len\n" ++
  "  addi a0, s0, 48             # code bytes\n" ++
  "  addi a2, sp, 48             # 32-byte out on stack\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li t0, 0\n" ++
  ".Lfceh_cmp:\n" ++
  "  li t1, 32\n" ++
  "  beq t0, t1, .Lfceh_hit\n" ++
  "  add t2, sp, t0\n" ++
  "  lbu t2, 48(t2)\n" ++
  "  add t3, s2, t0\n" ++
  "  lbu t3, 0(t3)\n" ++
  "  bne t2, t3, .Lfceh_next\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lfceh_cmp\n" ++
  ".Lfceh_next:\n" ++
  "  ld t0, 40(s0)\n" ++
  "  addi t0, t0, 55\n" ++
  "  andi t0, t0, -8\n" ++
  "  add s0, s0, t0\n" ++
  "  addi s1, s1, -1\n" ++
  "  j .Lfceh_loop\n" ++
  ".Lfceh_hit:\n" ++
  "  mv a0, s0\n" ++
  "  j .Lfceh_ret\n" ++
  ".Lfceh_miss:\n" ++
  "  li a0, 0\n" ++
  ".Lfceh_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret\n"

/-- Data region for the code-effect log (linked wherever CREATE deposit runs;
    included in this probe and, in step .8b-2, the runtime dispatcher data). -/
def createCodeEffectLogData : String :=
  ".balign 8\n" ++
  "exec_code_effect_count:\n  .zero 8\n" ++
  "exec_code_effect_next:\n  .zero 8\n" ++
  "exec_code_effect_overflow:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "exec_code_effect_log:\n  .zero " ++ toString execCodeEffectLogCap ++ "\n"

/-- `zisk_create_code_effect_log`: known-answer probe. Appends two records
    (addr A = 0x11*20, code = {0x60,0xff}; addr B = 0x22*20, code = {0x00}), then
    looks up A, B, and a missing addr C = 0x33*20, surfacing the found fields and
    the miss to OUTPUT (0xa0010000):
      +0 find(A)!=0    +8 A.has_code_change  +16 A.code_len  +24 A.code[0]  +32 A.code[1]
      +40 B.code_len   +48 B.code[0]         +56 find(C)==0  +64 count -/
def ziskCreateCodeEffectLogPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- Build addr A (0x11*20), addr B (0x22*20), addr C (0x33*20), code A {0x60,0xff}, code B {0x00}.
  "  la t0, ccel_addr_a; li t1, 20\n" ++
  "1:\n  li t2, 0x11; sb t2, 0(t0); addi t0, t0, 1; addi t1, t1, -1; bnez t1, 1b\n" ++
  "  la t0, ccel_addr_b; li t1, 20\n" ++
  "2:\n  li t2, 0x22; sb t2, 0(t0); addi t0, t0, 1; addi t1, t1, -1; bnez t1, 2b\n" ++
  "  la t0, ccel_addr_c; li t1, 20\n" ++
  "3:\n  li t2, 0x33; sb t2, 0(t0); addi t0, t0, 1; addi t1, t1, -1; bnez t1, 3b\n" ++
  "  la t0, ccel_code_a; li t1, 0x60; sb t1, 0(t0); li t1, 0xff; sb t1, 1(t0)\n" ++
  "  la t0, ccel_code_b; sb x0, 0(t0)\n" ++
  -- Append A (len 2) and B (len 1).
  "  la a0, ccel_addr_a; la a1, ccel_code_a; li a2, 2; jal ra, create_record_code_effect\n" ++
  "  la a0, ccel_addr_b; la a1, ccel_code_b; li a2, 1; jal ra, create_record_code_effect\n" ++
  -- Look up A.
  "  la a0, exec_code_effect_log; la t0, exec_code_effect_count; ld a1, 0(t0); la a2, ccel_addr_a\n" ++
  "  jal ra, find_code_effect_by_address\n" ++
  "  snez t1, a0; sd t1, 0(s0)\n" ++                 -- find(A)!=0
  "  beqz a0, 4f\n" ++
  "  ld t1, 32(a0); sd t1, 8(s0)\n" ++               -- A.has_code_change
  "  ld t1, 40(a0); sd t1, 16(s0)\n" ++              -- A.code_len
  "  lbu t1, 48(a0); sd t1, 24(s0)\n" ++             -- A.code[0]
  "  lbu t1, 49(a0); sd t1, 32(s0)\n" ++             -- A.code[1]
  "4:\n" ++
  -- Look up B.
  "  la a0, exec_code_effect_log; la t0, exec_code_effect_count; ld a1, 0(t0); la a2, ccel_addr_b\n" ++
  "  jal ra, find_code_effect_by_address\n" ++
  "  beqz a0, 5f\n" ++
  "  ld t1, 40(a0); sd t1, 40(s0)\n" ++              -- B.code_len
  "  lbu t1, 48(a0); sd t1, 48(s0)\n" ++             -- B.code[0]
  "5:\n" ++
  -- Look up missing C.
  "  la a0, exec_code_effect_log; la t0, exec_code_effect_count; ld a1, 0(t0); la a2, ccel_addr_c\n" ++
  "  jal ra, find_code_effect_by_address\n" ++
  "  seqz t1, a0; sd t1, 56(s0)\n" ++                -- find(C)==0
  "  la t0, exec_code_effect_count; ld t1, 0(t0); sd t1, 64(s0)\n" ++  -- count
  "  li x17, 93\n  li x10, 0\n  ecall\n" ++
  "  j .Lccel_done\n" ++
  createRecordCodeEffectFunction false ++ "\n" ++
  accountStateFindFunction ++ "\n" ++
  accountStateCopyFunction ++ "\n" ++
  accountStateAppendPendingFunction ++ "\n" ++
  accountStateRecordCodeFunction ++ "\n" ++
  codeStateAddressSetInsertFunction ++ "\n" ++
  codeStateAddressSetFlagFunction ++ "\n" ++
  findCodeEffectByAddressFunction ++ "\n" ++
  findCodeEffectByHashFunction ++ "\n" ++
  ".Lccel_done:"

def ziskCreateCodeEffectLogDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ccel_addr_a:\n  .zero 20\n" ++
  "ccel_addr_b:\n  .zero 20\n" ++
  "ccel_addr_c:\n  .zero 20\n" ++
  "ccel_code_a:\n  .zero 8\n" ++
  "ccel_code_b:\n  .zero 8\n" ++
  createCodeEffectLogData ++
  codeStateData

def ziskCreateCodeEffectLogProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCreateCodeEffectLogPrologue
  dataAsm     := ziskCreateCodeEffectLogDataSection
}

end EvmAsm.Codegen
