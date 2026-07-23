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

  The CREATE-tail deposit call site (`create_record_code_effect(create_address_be,
  create_child_code, create_child_code_len)`) + EIP-3541 / MAX_CODE_SIZE / nonce
  updates land in step .8b-2; this slice is the log + helpers + a known-answer probe.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Capacity (bytes) of the code-effect log heap. Each entry is
    `round8(48 + code_len)`; deployed code is ≤ 32768 (Amsterdam EIP-7907).

    Gas-derived bound for the full 200M block target. Code deposit charges
    `CODE_DEPOSIT_PER_BYTE = 200` gas/byte, so the total deployed bytecode in a
    `bsrStateRootBlockGasLimit`-gas block is at most `200M / 200 = 1,000,000`
    bytes. Accounting for the 32,000-gas CREATE base (which lowers the realized
    byte budget) and the per-record `+48` overhead, the worst case is reached by
    ~30 near-max (32,768-byte) deploys: `Σcᵢ ≤ 200M/200 - 160·N` gives
    `Σcᵢ ≈ 983,040` and arena `Σ round8(48+cᵢ) ≈ 984 KiB` (~0.94 MiB realized,
    1.0 MiB absolute ceiling); the EIP-7907 large-code extra gas only lowers
    this, and the empty-CREATE / EIP-7702 delegation marker paths (48-byte
    records) are less arena-bytes-per-gas-efficient so cannot exceed it. The
    cap therefore reserves 1.5 MiB (≈50% margin over the 1.0 MiB ceiling).

    On overflow the producer sets `exec_code_effect_overflow`; block_verdict
    consumes that flag as a rejection. -/
def execCodeEffectLogCap : Nat := 1572864

/-! ## Bounded execution CodeState

    `exec_code_effect_log` is an append-only comparison record: BAL's code
    comparator needs to see every execution-produced code change.  It is not a
    model of Ethereum account state (in particular, a later CREATE for the
    same address must replace an earlier one, and EIP-6780 deletion is scoped
    to the transaction which created the account).

    The multi-transaction runtime therefore keeps its execution-facing code
    state in fixed, real-address keyed tables.  A table entry is 64 bytes:

      +0  address (20-byte BE, zero-padded to 32)
      +32 code pointer
      +40 code length
      +48 flags (bit 0: occupied; bit 1: account exists; bit 2: code is available)
      +56 reserved

    There are separate pending and durable tables.  Pending entries are the
    current transaction overlay; successful transaction finalization merges
    them into durable state, while a failed transaction discards the pending
    count.  The capacity is gas bounded: CREATE costs at least 32,000 gas, so
    a 200M-gas block can create at most 6,250 accounts; 8,192 leaves margin
    without scaling memory with untrusted input. -/
def codeStateEntryBytes : Nat := 64
def codeStateEntryCapacity : Nat := 8192
def codeStateTableBytes : Nat := codeStateEntryBytes * codeStateEntryCapacity

/-! ## code_state_find

    a0 = 20-byte BE address pointer
    a1 = fixed 64-byte-entry table base
    a2 = populated entry count
    a3 = entry capacity
    returns a0 = entry pointer, or zero on no match / malformed count.

    The table is intentionally scanned to completion and returns the latest
    matching entry.  Upsert normally prevents duplicates, but latest-wins
    makes the helper robust at the state boundary and is the required semantic
    for a recreate sequence. -/
def codeStateFindFunction : String :=
  "code_state_find:\n" ++
  -- a3 aliases the guest's x13 stack cursor at several runtime call sites.
  -- Preserve it even though it is an argument to this leaf helper.
  "  addi sp, sp, -16; sd a3, 0(sp)\n" ++
  "  bgtu a2, a3, .Lcsf_miss\n" ++
  "  mv t0, a1; li t1, 0; li t2, 0\n" ++
  ".Lcsf_entry:\n" ++
  "  bgeu t1, a2, .Lcsf_done\n" ++
  "  li t3, 0\n" ++
  ".Lcsf_bytes:\n" ++
  "  li t4, 20; beq t3, t4, .Lcsf_hit\n" ++
  "  add t4, a0, t3; lbu t5, 0(t4); add t4, t0, t3; lbu t6, 0(t4); bne t5, t6, .Lcsf_next\n" ++
  "  addi t3, t3, 1; j .Lcsf_bytes\n" ++
  ".Lcsf_hit:\n" ++
  "  ld t4, 48(t0); andi t4, t4, 1; beqz t4, .Lcsf_next; mv t2, t0\n" ++
  ".Lcsf_next:\n" ++
  "  addi t0, t0, 64; addi t1, t1, 1; j .Lcsf_entry\n" ++
  ".Lcsf_done:\n" ++
  "  mv a0, t2; ld a3, 0(sp); addi sp, sp, 16; ret\n" ++
  ".Lcsf_miss:\n" ++
  "  li a0, 0; ld a3, 0(sp); addi sp, sp, 16; ret"

/-! ## code_state_upsert

    a0 = address pointer, a1 = code pointer, a2 = code length,
    a3 = table base, a4 = count pointer, a5 = capacity, a6 = flags.
    Returns a0 = 0 on success, 1 on capacity/count failure.  The address is
    matched as its canonical 20-byte BE form.  The routine is deliberately
    fixed-arena only: it never allocates and never dereferences a dynamic
    bucket. -/
def codeStateUpsertFunction : String :=
  "code_state_upsert:\n" ++
  "  addi sp, sp, -80; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd a3, 64(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; mv s6, a6\n" ++
  "  ld t0, 0(s4); bgtu t0, s5, .Lcsu_over\n" ++
  "  mv a0, s0; mv a1, s3; mv a2, t0; mv a3, s5; jal ra, code_state_find\n" ++
  "  bnez a0, .Lcsu_write\n" ++
  "  ld t0, 0(s4); bgeu t0, s5, .Lcsu_over; slli t1, t0, 6; add a0, s3, t1; addi t0, t0, 1; sd t0, 0(s4)\n" ++
  ".Lcsu_write:\n" ++
  "  mv t0, a0; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0); li t1, 0\n" ++
  ".Lcsu_copy:\n" ++
  "  li t2, 20; beq t1, t2, .Lcsu_finish; add t2, s0, t1; lbu t3, 0(t2); add t2, t0, t1; sb t3, 0(t2); addi t1, t1, 1; j .Lcsu_copy\n" ++
  ".Lcsu_finish:\n" ++
  "  sd s1, 32(t0); sd s2, 40(t0); sd s6, 48(t0); li a0, 0; j .Lcsu_ret\n" ++
  ".Lcsu_over:\n" ++
  "  li a0, 1; j .Lcsu_ret\n" ++
  ".Lcsu_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld a3, 64(sp); addi sp, sp, 80; ret"

/-! ## code_state_final_balance_nonzero

    Resolve the authoritative BAL final balance for a deferred SELFDESTRUCT
    deletion.  EIP-161 prunes only an empty final account: a same-transaction
    CREATE followed by SELFDESTRUCT to itself may have no code but must remain
    an existing empty account when its final balance is nonzero.

    a0 = canonical 20-byte BE address
    returns a0 = 0 final balance is zero, 1 final balance is nonzero,
                 2 BAL is absent/malformed/unavailable.

    A missing BAL balance field is not malformed: it means the balance is
    unchanged from the authenticated pre-block account.  In that case the
    helper reads the header/witness account balance; an absent pre-block account
    is zero.  Only genuine BAL or witness parse errors remain fail-closed. -/
def codeStateFinalBalanceNonzeroFunction : String :=
  "code_state_final_balance_nonzero:\n" ++
  "  addi sp, sp, -40; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd a3, 24(sp); sd a4, 32(sp); mv s0, a0\n" ++
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0); mv a2, s0; la a3, code_state_bal_acct_ptr; la a4, code_state_bal_acct_len; jal ra, bal_find_account_by_address; bnez a0, .Lcsfb_unavailable\n" ++
  "  la t0, code_state_bal_acct_ptr; ld a0, 0(t0); la t0, code_state_bal_acct_len; ld a1, 0(t0); la a2, code_state_bal_bytes; la a3, code_state_bal_len; la a4, code_state_bal_nonce; la a5, code_state_bal_nonce_len; jal ra, bal_account_post_fields; bnez a0, .Lcsfb_unavailable\n" ++
  "  la t0, code_state_bal_len; ld s1, 0(t0); li t1, -1; beq s1, t1, .Lcsfb_preblock; li t1, 32; bgtu s1, t1, .Lcsfb_unavailable\n" ++
  "  li t2, 0\n" ++
  ".Lcsfb_scan:\n" ++
  "  bgeu t2, s1, .Lcsfb_zero; la t3, code_state_bal_bytes; add t3, t3, t2; lbu t4, 0(t3); bnez t4, .Lcsfb_nonzero; addi t2, t2, 1; j .Lcsfb_scan\n" ++
  ".Lcsfb_zero:\n" ++
  "  la t0, code_state_last_delete_balance_status; sd zero, 0(t0); li a0, 0; j .Lcsfb_ret\n" ++
  ".Lcsfb_nonzero:\n" ++
  "  la t0, code_state_last_delete_balance_status; li t1, 1; sd t1, 0(t0); li a0, 1; j .Lcsfb_ret\n" ++
  -- No balance_changes entry means the final balance is inherited unchanged
  -- from the authenticated pre-block state.  This is the normal same-tx
  -- CREATE+SELFDESTRUCT case: the address is absent pre-block, therefore its
  -- final balance is zero and EIP-161 prunes it at transaction finalization.
  ".Lcsfb_preblock:\n" ++
  "  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0); mv a2, s0; li a3, 20; la t0, bv_witness_state_ptr; ld a4, 0(t0); la t0, bv_witness_state_len; ld a5, 0(t0); la a6, code_state_pre_acct; jal ra, account_at_header_state_root\n" ++
  "  beqz a0, .Lcsfb_pre_found; li t0, 1; bne a0, t0, .Lcsfb_unavailable; li a0, 0; j .Lcsfb_zero\n" ++
  ".Lcsfb_pre_found:\n" ++
  "  li t2, 0\n" ++
  ".Lcsfb_pre_scan:\n" ++
  "  li t1, 32; beq t2, t1, .Lcsfb_zero; la t3, code_state_pre_acct; addi t3, t3, 8; add t3, t3, t2; lbu t4, 0(t3); bnez t4, .Lcsfb_nonzero; addi t2, t2, 1; j .Lcsfb_pre_scan\n" ++
  ".Lcsfb_unavailable:\n" ++
  "  la t0, code_state_last_delete_balance_status; li t1, 2; sd t1, 0(t0); li a0, 2\n" ++
  ".Lcsfb_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld a3, 24(sp); ld a4, 32(sp); addi sp, sp, 40; ret"

/-! ## code_state_commit_pending

    Merge the current transaction overlay into block-durable state.  A pending
    entry with `exists=0` is deliberately committed too: it masks an earlier
    durable/pre-block code entry after a same-transaction EIP-6780 deletion.
    Returns a0 = 0 on success, 1 on fixed-arena overflow. -/
def codeStateCommitPendingFunction : String :=
  "code_state_commit_pending:\n" ++
  "  addi sp, sp, -48; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd a3, 32(sp)\n" ++
  "  la t0, code_state_pending_count; ld s0, 0(t0); li t0, " ++ toString codeStateEntryCapacity ++ "; bgtu s0, t0, .Lcscp_over\n" ++
  "  li s1, 0\n" ++
  ".Lcscp_loop:\n" ++
  "  bgeu s1, s0, .Lcscp_done\n" ++
  "  slli t0, s1, 6; la s2, code_state_pending; add s2, s2, t0; ld t1, 48(s2); andi t1, t1, 1; beqz t1, .Lcscp_next\n" ++
  "  mv a0, s2; ld a1, 32(s2); ld a2, 40(s2); la a3, code_state_durable; la a4, code_state_durable_count; li a5, " ++ toString codeStateEntryCapacity ++ "; ld a6, 48(s2); jal ra, code_state_upsert; bnez a0, .Lcscp_over\n" ++
  ".Lcscp_next:\n" ++
  "  addi s1, s1, 1; j .Lcscp_loop\n" ++
  ".Lcscp_done:\n" ++
  -- Apply EIP-6780 deletes only at successful transaction finalization.  A
  -- later same-tx recreate is an existing pending entry and therefore cancels
  -- the queued delete (latest state wins without an append-log special case).
  "  la t0, code_state_delete_count; ld s0, 0(t0); li t0, " ++ toString codeStateEntryCapacity ++ "; bgtu s0, t0, .Lcscp_over; li s1, 0\n" ++
  ".Lcscp_delete_loop:\n" ++
  "  bgeu s1, s0, .Lcscp_clear\n" ++
  "  slli t0, s1, 5; la s2, code_state_delete; add s2, s2, t0; ld t0, 24(s2); beqz t0, .Lcscp_delete_next\n" ++
  ".Lcscp_delete_apply:\n" ++
  -- EIP-161 distinguishes an empty account (which remains existent when it
  -- has a final nonzero balance) from a prunable final-zero account.  The BAL
  -- is the authenticated final-state authority for this decision.
  "  mv a0, s2; jal ra, code_state_final_balance_nonzero; li t1, 2; beq a0, t1, .Lcscp_over; li a6, 1; beqz a0, .Lcscp_delete_write; li a6, 3\n" ++
  ".Lcscp_delete_write:\n" ++
  "  mv a0, s2; li a1, 0; li a2, 0; la a3, code_state_durable; la a4, code_state_durable_count; li a5, " ++ toString codeStateEntryCapacity ++ "; jal ra, code_state_upsert; bnez a0, .Lcscp_over\n" ++
  ".Lcscp_delete_next:\n" ++
  "  addi s1, s1, 1; j .Lcscp_delete_loop\n" ++
  ".Lcscp_clear:\n" ++
  "  la t0, code_state_pending_count; sd zero, 0(t0); la t0, code_state_created_count; sd zero, 0(t0); la t0, code_state_delete_count; sd zero, 0(t0); li a0, 0; j .Lcscp_ret\n" ++
  ".Lcscp_over:\n" ++
  "  la t0, code_state_overflow; li t1, 1; sd t1, 0(t0); li a0, 1; j .Lcscp_ret\n" ++
  ".Lcscp_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld a3, 32(sp); addi sp, sp, 48; ret"

/-! ## code_state_lookup_current

    Shared execution-read resolver for the CodeState layers.

    a0 = canonical 20-byte BE address pointer
    returns a0 = 0 absent from both overlays, 1 existing with code,
                 2 existing with empty code, 3 explicitly deleted;
            a1 = code pointer, a2 = code length for status 1.

    Callers fall back to the authenticated header/witness only on status 0.
    This is deliberately the one shared state resolver used by CALL, NACC,
    EXTCODE*, collision, and SELFDESTRUCT consumers; it prevents a per-opcode
    recreation of the old log-vs-state divergence. -/
def codeStateLookupCurrentFunction : String :=
  "code_state_lookup_current:\n" ++
  "  addi sp, sp, -32; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd a3, 24(sp); mv s0, a0\n" ++
  "  la a1, code_state_pending; la t0, code_state_pending_count; ld a2, 0(t0); li a3, " ++ toString codeStateEntryCapacity ++ "; jal ra, code_state_find; bnez a0, .Lcslc_entry\n" ++
  "  mv a0, s0; la a1, code_state_durable; la t0, code_state_durable_count; ld a2, 0(t0); li a3, " ++ toString codeStateEntryCapacity ++ "; jal ra, code_state_find; beqz a0, .Lcslc_absent\n" ++
  ".Lcslc_entry:\n" ++
  "  mv s1, a0; ld t0, 48(s1); andi t1, t0, 2; beqz t1, .Lcslc_deleted; andi t1, t0, 4; beqz t1, .Lcslc_empty; ld a1, 32(s1); ld a2, 40(s1); li a0, 1; j .Lcslc_ret\n" ++
  ".Lcslc_empty:\n" ++
  "  li a0, 2; li a1, 0; li a2, 0; j .Lcslc_ret\n" ++
  ".Lcslc_deleted:\n" ++
  "  li a0, 3; li a1, 0; li a2, 0; j .Lcslc_ret\n" ++
  ".Lcslc_absent:\n" ++
  "  li a0, 0; li a1, 0; li a2, 0\n" ++
  ".Lcslc_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld a3, 24(sp); addi sp, sp, 32; ret"

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

/-! ## code_state_pending_contains

    Transaction-local created-account membership: unlike the layered resolver,
    this intentionally consults the pending table only. -/
def codeStatePendingContainsFunction : String :=
  "code_state_pending_contains:\n" ++
  "  addi sp, sp, -24; sd ra, 0(sp); sd s0, 8(sp); sd a3, 16(sp); mv s0, a0\n" ++
  "  la a1, code_state_pending; la t0, code_state_pending_count; ld a2, 0(t0); li a3, " ++ toString codeStateEntryCapacity ++ "; jal ra, code_state_find; beqz a0, .Lcspc_no; ld t0, 48(a0); andi t0, t0, 2; beqz t0, .Lcspc_no; li a0, 1; j .Lcspc_ret\n" ++
  ".Lcspc_no:\n" ++
  "  li a0, 0\n" ++
  ".Lcspc_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld a3, 16(sp); addi sp, sp, 24; ret"

/-- Fixed static data for the execution CodeState overlay.  `created` and
    `delete` sets use the same 32-byte padded-address key representation. -/
def codeStateData : String :=
  ".balign 8\n" ++
  "code_state_pending_count:\n  .zero 8\n" ++
  "code_state_durable_count:\n  .zero 8\n" ++
  "code_state_created_count:\n  .zero 8\n" ++
  "code_state_delete_count:\n  .zero 8\n" ++
  "code_state_overflow:\n  .zero 8\n" ++
  "code_state_mtx_active:\n  .zero 8\n" ++
  -- BAL final-account scratch for the EIP-161 deferred-delete decision.
  "code_state_bal_acct_ptr:\n  .zero 8\n" ++
  "code_state_bal_acct_len:\n  .zero 8\n" ++
  "code_state_bal_len:\n  .zero 8\n" ++
  "code_state_bal_nonce_len:\n  .zero 8\n" ++
  "code_state_last_delete_balance_status:\n  .zero 8\n" ++
  "code_state_bal_bytes:\n  .zero 32\n" ++
  "code_state_bal_nonce:\n  .zero 32\n" ++
  "code_state_pre_acct:\n  .zero 48\n" ++
  -- Frame-local high-water marks for the transaction overlay.  The execution
  -- journal is nested: a reverted child must discard only changes made below
  -- its own entry, never its parent's pending CREATE or SELFDESTRUCT work.
  -- The depth is capped at 1024 by the EVM frame gate, hence 1025 slots
  -- including depth zero.  These are counts, not input-sized allocations.
  "code_state_pending_checkpoint:\n  .zero " ++ toString (1025 * 8) ++ "\n" ++
  "code_state_created_checkpoint:\n  .zero " ++ toString (1025 * 8) ++ "\n" ++
  "code_state_delete_checkpoint:\n  .zero " ++ toString (1025 * 8) ++ "\n" ++
  ".balign 32\n" ++
  "code_state_pending:\n  .zero " ++ toString codeStateTableBytes ++ "\n" ++
  ".balign 32\n" ++
  "code_state_durable:\n  .zero " ++ toString codeStateTableBytes ++ "\n" ++
  ".balign 32\n" ++
  "code_state_created:\n  .zero " ++ toString (codeStateEntryCapacity * 32) ++ "\n" ++
  ".balign 32\n" ++
  "code_state_delete:\n  .zero " ++ toString (codeStateEntryCapacity * 32) ++ "\n"

/-! ## create_record_code_effect

    Append one deployed-code record to the code-effect log.

    Calling convention:
      a0 = 20-byte big-endian address ptr (the created account)
      a1 = deployed code ptr
      a2 = deployed code length (bytes)
    Returns:
      a0 = 0 appended ok / 1 capacity overflow (record NOT written; overflow flag set)
    Clobbers t0-t6, a0; preserves s-regs (saved). -/
def createRecordCodeEffectFunction : String :=
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
  -- Publish execution state from the retained heap copy, never from the
  -- reusable create-child scratch.  This helper is reached only by successful
  -- CREATE deposit tails, so reverted child creation cannot enter CodeState.
  "  mv a0, s0; addi a1, t3, 48; mv a2, s2; la a3, code_state_pending; la a4, code_state_pending_count; li a5, " ++ toString codeStateEntryCapacity ++ "; li a6, 3; beqz s2, .Lcrce_state_upsert; ori a6, a6, 4\n" ++
  ".Lcrce_state_upsert:\n" ++
  "  jal ra, code_state_upsert; beqz a0, .Lcrce_state_ok\n" ++
  "  la t0, code_state_overflow; li t1, 1; sd t1, 0(t0); j .Lcrce_overflow\n" ++
  ".Lcrce_state_ok:\n" ++
  "  mv a0, s0; la a1, code_state_created; la a2, code_state_created_count; li a3, " ++ toString codeStateEntryCapacity ++ "; jal ra, code_state_address_set_insert; beqz a0, .Lcrce_state_created_ok\n" ++
  "  la t0, code_state_overflow; li t1, 1; sd t1, 0(t0); j .Lcrce_overflow\n" ++
  ".Lcrce_state_created_ok:\n" ++
  -- A successful later CREATE at the same address is the latest transaction
  -- state and cancels an earlier same-transaction EIP-6780 delete request.
  "  mv a0, s0; la a1, code_state_delete; la a2, code_state_delete_count; li a3, " ++ toString codeStateEntryCapacity ++ "; li a4, 0; jal ra, code_state_address_set_flag\n" ++
  "  li a0, 0\n" ++
  "  j .Lcrce_ret\n" ++
  ".Lcrce_overflow:\n" ++
  "  la t0, exec_code_effect_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  "  li a0, 1\n" ++
  ".Lcrce_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp); ld ra, 32(sp); addi sp, sp, 40\n" ++
  "  ret"

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
  createRecordCodeEffectFunction ++ "\n" ++
  codeStateFindFunction ++ "\n" ++
  codeStateUpsertFunction ++ "\n" ++
  codeStateFinalBalanceNonzeroFunction ++ "\n" ++
  codeStateAddressSetInsertFunction ++ "\n" ++
  codeStateAddressSetFlagFunction ++ "\n" ++
  findCodeEffectByAddressFunction ++ "\n" ++
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
