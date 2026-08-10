/-
  EvmAsm.Codegen.Programs.NonstorageEffectLog

  Per-account NON-STORAGE exec-effect producer (bead bmvmx.1.6.4.4 / i3djw) — the
  execution-derived balance/nonce effect records used by live runtime state paths.
  The record layout (c2#5, keyed by the plain 20-byte big-endian address — NOT
  keccak):
    +0   addr            (20-byte BE in the low/first 20 bytes, padded to 32)
    +32  pre_balance     (32B BE)
    +64  post_balance    (32B BE)
    +96  pre_nonce       (u64)
    +104 post_nonce      (u64)
    = 112 B (fixed stride)

  This module is the PRODUCER: execution appends one record per touched non-recipient
  account (CREATE-created accounts, CALL value-transfer callees, SELFDESTRUCT
  beneficiaries). The call sites that append (CREATE deposit, CALL value-transfer
  .61.6.8) use this log for runtime state threading; this slice is the log + producer
  + a known-answer probe. {sender, recipient} are not recorded here; the coinbase
  fee credit IS recorded, by blockVerdictMtxCoinbaseFeeEffect
  (EvmAsm/Codegen/Programs/BlockVerdictMtxCoinbase.lean).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.CreateCodeEffectLog
import EvmAsm.Codegen.Programs.AccountWriteMap

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Capacity (entries) of the non-storage effect log — touched non-recipient accounts per tx.
    Set to 65536 (bmvmx.5.5.7.3, final capacity-chain slice): now that BOTH exec-vs-BAL
    comparators are linear — the FORWARD binary-searches the sorted agg (#9018) and the REVERSE
    _covers uses a matched-bitmap over the sorted agg (#9021) — there is no remaining super-linear
    consumer, so the cap can cover the full 200M-gas worst case.

    Worst-case bound: a nonzero value-CALL appends TWO raw records, the caller debit and the callee
    credit (ChildFrameHandlers .61.6.8), while its cheapest regular-gas charge is an existing warm
    account: GAS_WARM_ACCESS(100) + GAS_CALL_VALUE(10300) = 10400. Thus execution contributes
      2 * floor(200_000_000 / 10400) = 38_460
    raw records. CREATE and SELFDESTRUCT producer paths are more expensive per emitted effect.
    `block_verdict_withdrawal_nonstorage_effects` appends withdrawals to this SAME raw log, and
    withdrawals are bounded separately to 16 records, so the full stream bound is
      38_460 + 16 = 38_476.
    This uses the regular-gas budget only: EIP-7928 state gas is a separate block budget and cannot
    reduce the execution bound. The withdrawal contributor is named here because "separately
    bounded" is true of its count, but false of the storage it shares. The overflow flag remains a
    fail-closed runtime guard, rather than a verdict assumption.

    Cost: live consumers iterate over the recorded `count`, never `cap`, so a larger cap is
    pure reserved BSS. The exec_nonstorage_effect_log and shared radix-sort buffers are sized
    from this cap, so they scale automatically. -/
def nonstorageEffectLogCap : Nat := 38476

/-- The resolver in AccountWriteMap emits the same AccountState capacity as
    CreateCodeEffectLog. Keep the cross-module fact kernel-checked so a future
    capacity change cannot silently leave the resolver's scan bound stale. -/
theorem accountStateResolverCapacity_eq :
    accountStateResolverCapacity = accountStateEntryCapacity := by decide

/-! The 32-byte address field stores a 20-byte address followed by twelve
padding bytes. Byte 20 is a component-validity mask: it is outside the key
used by every address comparison and radix pass, so the fixed 112-byte layout
can represent the spec's independent balance and nonce changes without a
parallel log. -/
def nonstorageEffectHasBalance : Nat := 1
def nonstorageEffectHasNonce : Nat := 2

/-! ## record_nonstorage_effect
    Append one per-account balance/nonce effect record (c2#5 layout, 112 B fixed).
    a0 = 20-byte big-endian address ptr   a1 = pre_balance ptr (32B BE)
    a2 = post_balance ptr (32B BE)        a3 = pre_nonce (u64)   a4 = post_nonce (u64)
    Returns a0 = 0 appended / 1 overflow (not written; exec_nonstorage_effect_overflow set).
    Clobbers t0-t6, a0; preserves s-regs (saved).

    `record_nonstorage_effect_after_account_state` is retained as an ABI alias
    for callers that used to perform an AccountState mutation first.  It now
    emits the same raw effect and AccountWrite publication without a second
    execution-state append.

    `record_nonstorage_effect_nonce_only_after_account_state` is the EIP-7702
    authorization variant.  It carries an honest nonce-only raw mask while
    retaining the AccountWrite publication at the authorization's current BAI.

    Raw component mask (byte 20) is derived from actual pre/post deltas — the same
    rule AccountWrite already used — so balance-only producers that pass equal
    dummy nonces (notably `record_message_value_transfer` with a3=a4=0) do not
    publish a stale nonce-0 component. -/
def recordNonstorageEffectFunction : String :=
  "record_nonstorage_effect:\n  li a5, 0\n  j .Lrnse_entry\n" ++
  "record_nonstorage_effect_after_account_state:\n  li a5, 1\n" ++
  "record_nonstorage_effect_nonce_only_after_account_state:\n  li a5, 2\n" ++
  ".Lrnse_entry:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp); sd s3, 24(sp); sd s4, 32(sp); sd ra, 40(sp)\n" ++
  "  mv s0, a0                   # addr ptr\n" ++
  "  mv s1, a1                   # pre_balance ptr\n" ++
  "  mv s2, a2                   # post_balance ptr\n" ++
  "  mv s3, a3                   # pre_nonce\n" ++
  "  mv s4, a4                   # post_nonce\n" ++
  "  la t0, exec_nonstorage_effect_count; ld t1, 0(t0)\n" ++
  "  li t2, " ++ toString nonstorageEffectLogCap ++ "\n" ++
  "  bgeu t1, t2, .Lrnse_overflow\n" ++
  "  li t2, 112; mul t2, t1, t2; la t3, exec_nonstorage_effect_log; add t3, t3, t2   # entry base\n" ++
  "  sd x0, 0(t3); sd x0, 8(t3); sd x0, 16(t3); sd x0, 24(t3)   # zero 32B addr\n" ++
  "  mv t4, s0; mv t5, t3; li t6, 20\n" ++
  ".Lrnse_cpa:\n" ++
  "  beqz t6, .Lrnse_cpa_d\n" ++
  "  lbu a0, 0(t4); sb a0, 0(t5); addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lrnse_cpa\n" ++
  ".Lrnse_cpa_d:\n" ++
  -- a5=2: force nonce-only (EIP-7702 auth). Else derive mask from real deltas so
  -- balance-only callers that pass equal dummy nonces do not set hasNonce.
  "  li t5, 2; beq a5, t5, .Lrnse_mask_nonce_only\n" ++
  "  li t4, 0\n" ++
  "  ld t0, 0(s1); ld t1, 0(s2); bne t0, t1, .Lrnse_mask_bal\n" ++
  "  ld t0, 8(s1); ld t1, 8(s2); bne t0, t1, .Lrnse_mask_bal\n" ++
  "  ld t0, 16(s1); ld t1, 16(s2); bne t0, t1, .Lrnse_mask_bal\n" ++
  "  ld t0, 24(s1); ld t1, 24(s2); beq t0, t1, .Lrnse_mask_nonce\n" ++
  ".Lrnse_mask_bal:\n" ++
  "  ori t4, t4, " ++ toString nonstorageEffectHasBalance ++ "\n" ++
  ".Lrnse_mask_nonce:\n" ++
  "  beq s3, s4, .Lrnse_mask_ready; ori t4, t4, " ++ toString nonstorageEffectHasNonce ++ "; j .Lrnse_mask_ready\n" ++
  ".Lrnse_mask_nonce_only:\n" ++
  "  li t4, " ++ toString nonstorageEffectHasNonce ++ "\n" ++
  ".Lrnse_mask_ready:\n" ++
  "  sb t4, 20(t3)\n" ++
  "  ld t4, 0(s1); sd t4, 32(t3); ld t4, 8(s1); sd t4, 40(t3); ld t4, 16(s1); sd t4, 48(t3); ld t4, 24(s1); sd t4, 56(t3)\n" ++  -- pre_balance
  "  ld t4, 0(s2); sd t4, 64(t3); ld t4, 8(s2); sd t4, 72(t3); ld t4, 16(s2); sd t4, 80(t3); ld t4, 24(s2); sd t4, 88(t3)\n" ++  -- post_balance
  "  sd s3, 96(t3)               # pre_nonce\n" ++
  "  sd s4, 104(t3)              # post_nonce\n" ++
  "  la t0, exec_nonstorage_effect_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  -- Preserve this successful execution effect in the transaction-local map.
  -- It is a fieldwise overlay: a balance-only effect must not overwrite a
  -- prior nonce increment merely because this generic record also carries a
  -- nonce word. The builder still decides emission from its block-cumulative
  -- baseline; these bits only select components whose post differs here.
  "  li a6, 0; ld t0, 0(s1); ld t1, 0(s2); bne t0, t1, .Lrnse_aw_balance; ld t0, 8(s1); ld t1, 8(s2); bne t0, t1, .Lrnse_aw_balance; ld t0, 16(s1); ld t1, 16(s2); bne t0, t1, .Lrnse_aw_balance; ld t0, 24(s1); ld t1, 24(s2); beq t0, t1, .Lrnse_aw_nonce\n" ++
  ".Lrnse_aw_balance:\n" ++
  "  ori a6, a6, " ++ toString accountWriteHasBalance ++ "\n" ++
  ".Lrnse_aw_nonce:\n" ++
  "  beq s3, s4, .Lrnse_aw_record; ori a6, a6, " ++ toString accountWriteHasNonce ++ "\n" ++
  ".Lrnse_aw_record:\n" ++
  -- #11329: every nonstorage effect is an execution touch (TOUCHED sticky).
  "  ori a6, a6, " ++ toString accountWriteHasTouched ++ "\n" ++
  "  mv a0, s0; mv a1, s2; mv a2, s4; li a3, 0; li a4, 0; li a5, 0; jal ra, account_write_record\n" ++
  "  li a0, 0\n" ++
  "  j .Lrnse_ret\n" ++
  ".Lrnse_overflow:\n" ++
  "  la t0, exec_nonstorage_effect_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  "  li a0, 1\n" ++
  ".Lrnse_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp); ld s4, 32(sp); ld ra, 40(sp); addi sp, sp, 48\n" ++
  "  ret"

/-! ## `nonstorage_apply_destroyed_norm` (fc44 multi-tx SUCCESS selfdestruct)

    Spec stage (execution-specs e5a8caf1b): `clear_account_preserving_balance` /
    `destroy_account` run during the transaction; `incorporate_tx_into_block`
    then sees the cleared account (`fork.py:1201-1202`, `system.py:692-693`).
    Nonce is forced to 0 at clear; BAL emits a nonce change only when pre≠post
    (`block_access_lists.py:478-489`).

    Guest disease: destroyed-norm lived only inside block-end
    `nonstorage_effect_aggregate`. Multi-tx blocks wipe
    `evm_selfdestruct_destroyed_count` at the next user
    `runtime_dispatcher_call` (mode=0; #11147 only preserves across system
    re-entry), so the table is empty when aggregate runs. CREATE's transient
    nonce 0→1 then survives MAX-post fold → phantom hasNonce vs BAL empty →
    bv_fail=44 (corpus fc44 eip8246 success initcode, n=68).

    Fix: apply destroyed-norm to every RAW log record for each destroyed
    address at **transaction finalize**, while the table is still live.
    Afterward clear the table so the next-tx wipe is a no-op and block-end
    aggregate is idempotent.

    ONE RULE (clear_account_preserving_balance, state_tracker.py:536-557):
    clear zeroes nonce/code/storage and **keeps balance**. Self vs distinct
    differ only in whether move_ether drained the originator first
    (system.py:685-693); the clear itself never wipes balance. So the raw
    transform is identical for meta=0 and meta=1:

      1. Drop hasNonce on every matching raw record (post_nonce := pre_nonce).
      2. Leave balance limbs alone (post_send and move_ether stay visible).
      3. After the per-addr scan: if first-pre balance equals last-post
         balance across hasBalance records (net-zero, e.g. CREATE endowment
         then SD drain with no post_send), clear hasBalance on those records
         so the fold does not emit a phantom 0→0 balance row vs BAL empty.

    (#11306: #11304 distinct arm zeroed every raw component and wiped
    post_send bal post=1 on success-eoa/precompile.) -/
def nonstorageApplyDestroyedNormFunction : String :=
  -- Frame layout (112 B):
  --   +0 ra, +8 s0, +16 s1, +24 s2, +32 s3, +40 s4
  --   +48 first-pre bal (32 B), +80 last-post bal (32 B)
  "nonstorage_apply_destroyed_norm:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  la t0, evm_selfdestruct_destroyed_overflow; ld t0, 0(t0); bnez t0, .Lnaddn_ret\n" ++
  "  la t0, evm_selfdestruct_destroyed_count; ld s0, 0(t0)\n" ++
  "  beqz s0, .Lnaddn_ret\n" ++
  "  la s1, evm_selfdestruct_destroyed_table\n" ++
  "  la t0, exec_nonstorage_effect_count; ld s2, 0(t0)\n" ++
  "  beqz s2, .Lnaddn_clear\n" ++
  "  la s3, exec_nonstorage_effect_log\n" ++
  ".Lnaddn_dloop:\n" ++
  "  beqz s0, .Lnaddn_clear\n" ++
  -- Pass 1: drop nonce on every matching raw record (self and distinct).
  "  li t6, 0\n" ++
  ".Lnaddn_rloop:\n" ++
  "  bgeu t6, s2, .Lnaddn_netzero\n" ++
  "  li t0, 112; mul t0, t6, t0; add t1, s3, t0\n" ++
  "  mv t2, s1; mv t3, t1; li t4, 20\n" ++
  ".Lnaddn_cmp:\n" ++
  "  beqz t4, .Lnaddn_hit\n" ++
  "  lbu t5, 0(t2); lbu a0, 0(t3); bne t5, a0, .Lnaddn_rnext\n" ++
  "  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lnaddn_cmp\n" ++
  ".Lnaddn_hit:\n" ++
  "  ld t0, 96(t1); sd t0, 104(t1)\n" ++
  "  lbu t0, 20(t1); andi t0, t0, " ++ toString nonstorageEffectHasBalance ++ "; sb t0, 20(t1)\n" ++
  ".Lnaddn_rnext:\n" ++
  "  addi t6, t6, 1; j .Lnaddn_rloop\n" ++
  -- Pass 2: first-pre vs last-post balance; net-zero → drop hasBalance.
  ".Lnaddn_netzero:\n" ++
  "  li s4, 0\n" ++
  "  li t6, 0\n" ++
  ".Lnaddn_nz_scan:\n" ++
  "  bgeu t6, s2, .Lnaddn_nz_decide\n" ++
  "  li t0, 112; mul t0, t6, t0; add t1, s3, t0\n" ++
  "  mv t2, s1; mv t3, t1; li t4, 20\n" ++
  ".Lnaddn_nz_cmp:\n" ++
  "  beqz t4, .Lnaddn_nz_hit\n" ++
  "  lbu t5, 0(t2); lbu a0, 0(t3); bne t5, a0, .Lnaddn_nz_next\n" ++
  "  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lnaddn_nz_cmp\n" ++
  ".Lnaddn_nz_hit:\n" ++
  "  lbu t0, 20(t1); andi t0, t0, " ++ toString nonstorageEffectHasBalance ++ "; beqz t0, .Lnaddn_nz_next\n" ++
  "  bnez s4, .Lnaddn_nz_last\n" ++
  "  ld t0, 32(t1); sd t0, 48(sp); ld t0, 40(t1); sd t0, 56(sp)\n" ++
  "  ld t0, 48(t1); sd t0, 64(sp); ld t0, 56(t1); sd t0, 72(sp)\n" ++
  "  li s4, 1\n" ++
  ".Lnaddn_nz_last:\n" ++
  "  ld t0, 64(t1); sd t0, 80(sp); ld t0, 72(t1); sd t0, 88(sp)\n" ++
  "  ld t0, 80(t1); sd t0, 96(sp); ld t0, 88(t1); sd t0, 104(sp)\n" ++
  ".Lnaddn_nz_next:\n" ++
  "  addi t6, t6, 1; j .Lnaddn_nz_scan\n" ++
  ".Lnaddn_nz_decide:\n" ++
  "  beqz s4, .Lnaddn_dnext\n" ++
  "  ld t0, 48(sp); ld t1, 80(sp); bne t0, t1, .Lnaddn_dnext\n" ++
  "  ld t0, 56(sp); ld t1, 88(sp); bne t0, t1, .Lnaddn_dnext\n" ++
  "  ld t0, 64(sp); ld t1, 96(sp); bne t0, t1, .Lnaddn_dnext\n" ++
  "  ld t0, 72(sp); ld t1, 104(sp); bne t0, t1, .Lnaddn_dnext\n" ++
  "  li t6, 0\n" ++
  ".Lnaddn_nz_clear:\n" ++
  "  bgeu t6, s2, .Lnaddn_dnext\n" ++
  "  li t0, 112; mul t0, t6, t0; add t1, s3, t0\n" ++
  "  mv t2, s1; mv t3, t1; li t4, 20\n" ++
  ".Lnaddn_nz_ccmp:\n" ++
  "  beqz t4, .Lnaddn_nz_chit\n" ++
  "  lbu t5, 0(t2); lbu a0, 0(t3); bne t5, a0, .Lnaddn_nz_cnext\n" ++
  "  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lnaddn_nz_ccmp\n" ++
  ".Lnaddn_nz_chit:\n" ++
  "  ld t0, 32(t1); sd t0, 64(t1); ld t0, 40(t1); sd t0, 72(t1)\n" ++
  "  ld t0, 48(t1); sd t0, 80(t1); ld t0, 56(t1); sd t0, 88(t1)\n" ++
  "  lbu t0, 20(t1); andi t0, t0, " ++ toString nonstorageEffectHasNonce ++ "; sb t0, 20(t1)\n" ++
  ".Lnaddn_nz_cnext:\n" ++
  "  addi t6, t6, 1; j .Lnaddn_nz_clear\n" ++
  ".Lnaddn_dnext:\n" ++
  "  addi s1, s1, 32; addi s0, s0, -1; j .Lnaddn_dloop\n" ++
  ".Lnaddn_clear:\n" ++
  "  la t0, evm_selfdestruct_destroyed_count; sd zero, 0(t0)\n" ++
  "  la t0, evm_selfdestruct_destroyed_overflow; sd zero, 0(t0)\n" ++
  ".Lnaddn_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-! ## nonstorage_effect_latest_balance (yisv8 .spine.1)
    Scan the non-storage effect log from the start, keeping the LAST (most-recent-write-wins)
    record whose 20-byte address matches, and surface its post_balance. This is the BALANCE
    live-value read: an account's current balance during execution = its latest recorded
    post_balance, falling back to the pre-state when no value transfer touched it. Mirrors
    exec_log_latest_value (storage) at the 112-byte non-storage stride.
    a0 = address ptr (20-byte BE key in bytes 0..19; bytes 20..31 are ignored because
      record byte 20 is the component-validity mask)   a1 = out ptr (32B BE post_balance, written only on a hit).
    Returns a0 = 1 found / 0 not found (out left untouched on a miss). Leaf; only t-regs + a0-a2. -/
def nonstorageEffectLatestBalance_prog : Program :=
  [ .LI .x31 (0 : Word),
    .AUIPC .x30 (laHi GuestAddrs.exec_nonstorage_effect_count (GuestAddrs.nonstorage_effect_latest_balance + 4)),
    .ADDI .x30 .x30 (laLo GuestAddrs.exec_nonstorage_effect_count (GuestAddrs.nonstorage_effect_latest_balance + 4)),
    .LD .x30 .x30 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.exec_nonstorage_effect_log (GuestAddrs.nonstorage_effect_latest_balance + 16)),
    .ADDI .x12 .x12 (laLo GuestAddrs.exec_nonstorage_effect_log (GuestAddrs.nonstorage_effect_latest_balance + 16)),
    .LI .x5 (0 : Word),
    .BEQ .x5 .x30 (108 : BitVec 13),
    .LI .x6 (112 : Word),
    .MUL .x6 .x5 .x6,
    .ADD .x7 .x12 .x6,
    .LD .x28 .x7 (0 : BitVec 12),
    .LD .x29 .x10 (0 : BitVec 12),
    .BNE .x28 .x29 (76 : BitVec 13),
    .LD .x28 .x7 (8 : BitVec 12),
    .LD .x29 .x10 (8 : BitVec 12),
    .BNE .x28 .x29 (64 : BitVec 13),
    .LWU .x28 .x7 (16 : BitVec 12),
    .LWU .x29 .x10 (16 : BitVec 12),
    .BNE .x28 .x29 (52 : BitVec 13),
    .ADDI .x0 .x0 (0 : BitVec 12),
    .ADDI .x0 .x0 (0 : BitVec 12),
    .ADDI .x0 .x0 (0 : BitVec 12),
    .LD .x28 .x7 (64 : BitVec 12),
    .SD .x11 .x28 (0 : BitVec 12),
    .LD .x28 .x7 (72 : BitVec 12),
    .SD .x11 .x28 (8 : BitVec 12),
    .LD .x28 .x7 (80 : BitVec 12),
    .SD .x11 .x28 (16 : BitVec 12),
    .LD .x28 .x7 (88 : BitVec 12),
    .SD .x11 .x28 (24 : BitVec 12),
    .LI .x31 (1 : Word),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-104 : BitVec 21),
    .MV .x10 .x31,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `nonstorageEffectLatestBalance_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def nonstorageEffectLatestBalance_relocs : RelocTable :=
  [ (1, .la .x30 "exec_nonstorage_effect_count"),
    (4, .la .x12 "exec_nonstorage_effect_log") ]

def nonstorageEffectLatestBalanceFunction : String :=
  "nonstorage_effect_latest_balance:\n" ++ emitProgramR nonstorageEffectLatestBalance_prog nonstorageEffectLatestBalance_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `nonstorageEffectLatestBalance_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem nonstorageEffectLatestBalanceFunction_eq_prog :
    nonstorageEffectLatestBalanceFunction = "nonstorage_effect_latest_balance:\n" ++ emitProgramR nonstorageEffectLatestBalance_prog nonstorageEffectLatestBalance_relocs := rfl

#guard nonstorageEffectLatestBalanceFunction.startsWith "nonstorage_effect_latest_balance:\n"
#guard nonstorageEffectLatestBalance_prog.length = 36

/-- `nonstorage_effect_latest_nonce`: bmvmx.5.5.10 — nonce analog of
`nonstorage_effect_latest_balance`. Sequential multi-tx CREATE address
derivation seeds `create_nonce` from the PRE-state witness
(`nonce_at_header_state_root`, ChildFrameCreateTail), and the per-tx
`create_creator_nonce_table` resets at every dispatch (`.61.8a`), so a
contract that CREATEs in tx i and again in tx j would re-derive with the
pre-state nonce. The non-storage effect log already records every creator
nonce bump (NoopHalt drj99.1 5a: pre=create_nonce, post=+1) and every
created-account record (post_nonce=1); the log persists across txs on the
mtx lane (truncated only for FAILED txs, whose nonce bumps revert per
protocol). This reader returns the log's latest post_nonce for an address
(last-write-wins over the whole log); the CREATE seed site consults it
between the witness seed and `create_creator_nonce_use`, so a hit overrides
the pre-state seed and a miss keeps today's behavior. ABI: a0 = address
pointer (only the first 20 bytes are compared — the log record's addr
field is 20B + 12 zero pad), a1 = out-u64 pointer; returns a0 = 1 + latest
post_nonce stored, or 0 when the log has no record. Clobbers a0-a2/t0-t6
(caller saves x10/x12/x13 per the ChildFrameCreateTail idiom). Plain
string (no `_eq_prog` guard): mirrors `nonstorageEffectLatestBalance_prog`'s
scan, last-write-wins by writing on every match. -/
def nonstorageEffectLatestNonceFunction : String :=
  "# a0 = addr ptr (20B compared), a1 = out u64 ptr -> a0 = 1/0\n" ++
  "nonstorage_effect_latest_nonce:\n" ++
  "  la t0, exec_nonstorage_effect_log\n" ++
  "  la t1, exec_nonstorage_effect_count\n  ld t1, 0(t1)\n" ++
  "  li t2, 112\n  mul t1, t1, t2\n  add t1, t0, t1\n" ++
  "  li a2, 0\n" ++
  ".Lneln_scan:\n" ++
  "  beq t0, t1, .Lneln_done\n" ++
  "  ld t3, 0(t0); ld t4, 0(a0); bne t3, t4, .Lneln_next\n" ++
  "  ld t3, 8(t0); ld t4, 8(a0); bne t3, t4, .Lneln_next\n" ++
  "  lw t3, 16(t0); lw t4, 16(a0); bne t3, t4, .Lneln_next\n" ++
  "  ld t3, 104(t0); sd t3, 0(a1)\n" ++
  "  li a2, 1\n" ++
  ".Lneln_next:\n" ++
  "  addi t0, t0, 112\n" ++
  "  j .Lneln_scan\n" ++
  ".Lneln_done:\n" ++
  "  mv a0, a2\n" ++
  "  ret\n"

/-- Data for the non-storage effect log (linked into the dispatcher data section when
    the CREATE/CALL-value append sites land, co-located with the CREATE child data). -/
def nonstorageEffectLogData : String :=
  ".balign 8\n" ++
  "exec_nonstorage_effect_count:\n  .zero 8\n" ++
  "exec_nonstorage_effect_overflow:\n  .zero 8\n" ++
  -- bmvmx.5.5.10: out cell for nonstorage_effect_latest_nonce (CREATE seed consult).
  "create_nonce_latest:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "exec_nonstorage_effect_log:\n  .zero " ++ toString (nonstorageEffectLogCap * 112) ++ "\n"

/-- `zisk_nonstorage_effect_log`: known-answer probe. Appends two records and reads
    them back, surfacing to OUTPUT (0xa0010000):
      A = addr 0x11*20, pre_bal 10, post_bal 20, pre_nonce 1, post_nonce 2
      B = addr 0x22*20, pre_bal 0,  post_bal 5,  pre_nonce 0, post_nonce 1
      +0 count(2)  +8 A.pre_bal[31](10)  +16 A.post_bal[31](20)  +24 A.pre_nonce(1)
      +32 A.post_nonce(2)  +40 A.addr[0](0x11)  +48 B.post_bal[31](5)  +56 B.post_nonce(1) -/
def ziskNonstorageEffectLogPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, exec_nonstorage_effect_count; sd x0, 0(t0)\n" ++
  -- build addr A=0x11*20, B=0x22*20, and the four balance buffers.
  "  la t0, nsel_addr_a; li t1, 20\n" ++
  "1:\n  li t2, 0x11; sb t2, 0(t0); addi t0, t0, 1; addi t1, t1, -1; bnez t1, 1b\n" ++
  "  la t0, nsel_addr_b; li t1, 20\n" ++
  "2:\n  li t2, 0x22; sb t2, 0(t0); addi t0, t0, 1; addi t1, t1, -1; bnez t1, 2b\n" ++
  "  la t0, nsel_pa; sd x0,0(t0); sd x0,8(t0); sd x0,16(t0); li t1,10; sb t1,31(t0)\n" ++   -- pre_bal A = 10 (BE low byte)
  "  la t0, nsel_qa; sd x0,0(t0); sd x0,8(t0); sd x0,16(t0); li t1,20; sb t1,31(t0)\n" ++   -- post_bal A = 20
  "  la t0, nsel_pb; sd x0,0(t0); sd x0,8(t0); sd x0,16(t0); sd x0,24(t0)\n" ++              -- pre_bal B = 0
  "  la t0, nsel_qb; sd x0,0(t0); sd x0,8(t0); sd x0,16(t0); li t1,5; sb t1,31(t0)\n" ++     -- post_bal B = 5
  "  la a0, nsel_addr_a; la a1, nsel_pa; la a2, nsel_qa; li a3, 1; li a4, 2\n" ++
  "  jal ra, record_nonstorage_effect\n" ++
  "  la a0, nsel_addr_b; la a1, nsel_pb; la a2, nsel_qb; li a3, 0; li a4, 1\n" ++
  "  jal ra, record_nonstorage_effect\n" ++
  -- read back.
  "  la t0, exec_nonstorage_effect_count; ld t1, 0(t0); sd t1, 0(s0)\n" ++   -- count
  "  la t0, exec_nonstorage_effect_log\n" ++                                  -- record A @ +0
  "  lbu t1, 63(t0); sd t1, 8(s0)\n" ++                                       -- A.pre_balance[31] = 10
  "  lbu t1, 95(t0); sd t1, 16(s0)\n" ++                                      -- A.post_balance[31] = 20
  "  ld t1, 96(t0); sd t1, 24(s0)\n" ++                                       -- A.pre_nonce = 1
  "  ld t1, 104(t0); sd t1, 32(s0)\n" ++                                      -- A.post_nonce = 2
  "  lbu t1, 0(t0); sd t1, 40(s0)\n" ++                                       -- A.addr[0] = 0x11
  "  addi t0, t0, 112\n" ++                                                   -- record B @ +112
  "  lbu t1, 95(t0); sd t1, 48(s0)\n" ++                                      -- B.post_balance[31] = 5
  "  ld t1, 104(t0); sd t1, 56(s0)\n" ++                                      -- B.post_nonce = 1
  "  li x17, 93\n  li x10, 0\n  ecall\n" ++
  "  j .Lnsel_done\n" ++
  recordNonstorageEffectFunction ++ "\n" ++
  accountStateFindFunction ++ "\n" ++
  accountStateCopyFunction ++ "\n" ++
  accountStateAppendPendingFunction ++ "\n" ++
  accountStateRecordNonstorageFunction ++ "\n" ++
  ".Lnsel_done:"

def ziskNonstorageEffectLogDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "nsel_addr_a:\n  .zero 20\n" ++
  "nsel_addr_b:\n  .zero 20\n" ++
  ".balign 32\n" ++
  "nsel_pa:\n  .zero 32\n" ++
  "nsel_qa:\n  .zero 32\n" ++
  "nsel_pb:\n  .zero 32\n" ++
  "nsel_qb:\n  .zero 32\n" ++
  nonstorageEffectLogData ++
  codeStateData

def ziskNonstorageEffectLogProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskNonstorageEffectLogPrologue
  dataAsm     := ziskNonstorageEffectLogDataSection
}

/-- Shared AccountState and radix-sort scratch used by live dispatcher paths. -/
def nonstorageEffectSharedScratch : String :=
  -- This is runtime scratch, not initialized input data.  Name the section
  -- explicitly because the main dispatcher appends it while emitting `.data`.
  -- In particular, AccountState's phase alias must cover both radix buffers
  -- in the same NOBITS region.
  ".section .bss, \"aw\", @nobits\n" ++
  ".balign 8\n" ++
  -- The per-transaction AccountState journal and sender-count radix buffers share
  -- this NOBITS region; both are live dispatcher storage.
  "account_state_pending:\nnea_sort_a:\n  .zero " ++ toString (nonstorageEffectLogCap * 112) ++ "\n" ++
  "nea_sort_b:\n  .zero " ++ toString (nonstorageEffectLogCap * 112) ++ "\n" ++
  ".set account_state_created, account_state_pending + " ++ toString accountStateTableBytes ++ "\n" ++
  ".set account_state_delete, account_state_pending + " ++ toString (accountStateTableBytes + accountStateCreatedCapacity * 32) ++ "\n" ++
  -- Callers append initialized dispatcher storage after this shared scratch.
  ".section .data\n"

end EvmAsm.Codegen
