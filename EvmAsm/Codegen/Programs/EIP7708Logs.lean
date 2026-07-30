/-
  EvmAsm.Codegen.Programs.EIP7708Logs

  Synthetic Amsterdam EIP-7708 Transfer/Burn event-log descriptor helpers.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

private def copyWordAsm (src : String) (dstOff : Nat) : String :=
  "  ld t3, 0(" ++ src ++ ")\n" ++
  "  sd t3, " ++ toString dstOff ++ "(t2)\n" ++
  "  ld t3, 8(" ++ src ++ ")\n" ++
  "  sd t3, " ++ toString (dstOff + 8) ++ "(t2)\n" ++
  "  ld t3, 16(" ++ src ++ ")\n" ++
  "  sd t3, " ++ toString (dstOff + 16) ++ "(t2)\n" ++
  "  ld t3, 24(" ++ src ++ ")\n" ++
  "  sd t3, " ++ toString (dstOff + 24) ++ "(t2)\n"

/-! ## EIP-7708 synthetic event-log descriptors

    `eip7708_append_synthetic_log` appends one descriptor in the same bounded
    256-byte shape used by the runtime LOG0..LOG4 capture path:

      +0   topic count (2 for Burn, 3 for Transfer)
      +8   memory offset low u64 (0 for synthetic logs)
      +16  memory size low u64 (32)
      +24  copied data length (32)
      +32  topic0 hash
      +64  topic1 account/sender word
      +96  topic2 recipient word for Transfer
      +160 32-byte amount data, canonical big-endian
      +192 SYSTEM_ADDRESS context word

    Calling convention:

      x20        : env ptr whose +472 cell is the event-log descriptor count
      a0         : topic count, 2 or 3
      a1         : topic0 ptr, descriptor word order
      a2         : topic1 ptr, descriptor word order
      a3         : topic2 ptr, descriptor word order; ignored for topic count 2
      a4         : amount EVM-word ptr, descriptor word order
      a0 output  : 0 success/no-op, 1 descriptor buffer overflow,
                   2 invalid topic count

    Amount zero is a successful no-op, matching execution-specs'
    `emit_transfer_log` / `emit_burn_log` early return. -/
def eip7708SyntheticLogFunctions : String :=
  "eip7708_append_synthetic_log:\n" ++
  "  ld t0, 0(a4)\n" ++
  "  ld t1, 8(a4)\n" ++
  "  or t0, t0, t1\n" ++
  "  ld t1, 16(a4)\n" ++
  "  or t0, t0, t1\n" ++
  "  ld t1, 24(a4)\n" ++
  "  or t0, t0, t1\n" ++
  "  beqz t0, .Leip7708_success\n" ++
  "  li t0, 2\n" ++
  "  bltu a0, t0, .Leip7708_bad_topic_count\n" ++
  "  li t0, 3\n" ++
  "  bgtu a0, t0, .Leip7708_bad_topic_count\n" ++
  "  ld t0, 472(x20)\n" ++
  "  li t1, 4096\n" ++               -- v0.6.0: descriptor cap raised with evm_event_logs
  "  bgeu t0, t1, .Leip7708_overflow\n" ++
  "  la t2, evm_event_logs\n" ++
  "  slli t1, t0, 8\n" ++
  "  add t2, t2, t1\n" ++
  "  mv t0, t2\n" ++
  "  li t1, 32\n" ++
  ".Leip7708_zero_loop:\n" ++
  "  sd x0, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .Leip7708_zero_loop\n" ++
  "  sd a0, 0(t2)\n" ++
  "  li t0, 32\n" ++
  "  sd t0, 16(t2)\n" ++
  "  sd t0, 24(t2)\n" ++
  copyWordAsm "a1" 32 ++
  copyWordAsm "a2" 64 ++
  "  li t0, 3\n" ++
  "  bne a0, t0, .Leip7708_amount_data\n" ++
  copyWordAsm "a3" 96 ++
  ".Leip7708_amount_data:\n" ++
  "  addi t0, a4, 31\n" ++
  "  addi t1, t2, 160\n" ++
  "  li t3, 32\n" ++
  ".Leip7708_amount_rev:\n" ++
  "  lbu t4, 0(t0)\n" ++
  "  sb t4, 0(t1)\n" ++
  "  addi t0, t0, -1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t3, t3, -1\n" ++
  "  bnez t3, .Leip7708_amount_rev\n" ++
  -- log_records_encode_rlp consumes descriptor+192 as canonical 20-byte BE.
  "  li t0, -1\n" ++
  "  sd t0, 192(t2)\n" ++
  "  li t0, -1\n" ++
  "  sd t0, 200(t2)\n" ++
  "  li t0, 0xfeffffff\n" ++
  "  sd t0, 208(t2)\n" ++
  "  sd x0, 216(t2)\n" ++
  "  sd x0, 224(t2)\n" ++
  "  sd x0, 232(t2)\n" ++
  "  sd x0, 240(t2)\n" ++
  "  sd x0, 248(t2)\n" ++
  -- .63.1.6.2.1: ALSO record the 32-byte amount in the FULL-data surface
  -- (evm_log_data + evm_log_data_meta) like the LOG0..4 capture path does.
  -- Synthetic logs previously left their meta slot stale, so any meta-based
  -- consumer (the per-tx log-window snapshot / logs-RLP encoder) would read
  -- garbage data for them. On full-data overflow set the existing
  -- evm_log_data_overflow flag and record a zero-length slot (consumers stay
  -- conservative), mirroring the LOG handlers.
  "  ld t0, 472(x20)              # descriptor index for the meta slot\n" ++
  "  slli t0, t0, 4\n" ++
  "  la t1, evm_log_data_meta\n" ++
  "  add t1, t1, t0\n" ++
  "  la t0, evm_log_data_used\n" ++
  "  ld t3, 0(t0)\n" ++
  "  addi t4, t3, 32\n" ++
  "  li t0, 1048576\n" ++
  "  bleu t4, t0, .Leip7708_data_fits\n" ++
  "  la t0, evm_log_data_overflow\n" ++
  "  li t4, 1\n" ++
  "  sd t4, 0(t0)\n" ++
  "  sd x0, 0(t1)\n" ++
  "  sd x0, 8(t1)\n" ++
  "  j .Leip7708_data_done\n" ++
  ".Leip7708_data_fits:\n" ++
  "  sd t3, 0(t1)                 # meta = {offset = used, len = 32}\n" ++
  "  li t0, 32\n" ++
  "  sd t0, 8(t1)\n" ++
  "  la t0, evm_log_data\n" ++
  "  add t0, t0, t3\n" ++
  "  ld t1, 160(t2)               # canonical BE amount from the descriptor\n" ++
  "  sd t1, 0(t0)\n" ++
  "  ld t1, 168(t2)\n" ++
  "  sd t1, 8(t0)\n" ++
  "  ld t1, 176(t2)\n" ++
  "  sd t1, 16(t0)\n" ++
  "  ld t1, 184(t2)\n" ++
  "  sd t1, 24(t0)\n" ++
  "  la t0, evm_log_data_used\n" ++
  "  sd t4, 0(t0)\n" ++
  ".Leip7708_data_done:\n" ++
  "  ld t0, 472(x20)\n" ++
  "  addi t0, t0, 1\n" ++
  "  sd t0, 472(x20)\n" ++
  ".Leip7708_success:\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Leip7708_overflow:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Leip7708_bad_topic_count:\n" ++
  "  li a0, 2\n" ++
  "  ret\n" ++
  "\n" ++
  "eip7708_append_transfer_log:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  li a0, 3\n" ++
  "  la a1, eip7708_transfer_topic\n" ++
  "  mv a2, s0\n" ++
  "  mv a3, s1\n" ++
  "  mv a4, s2\n" ++
  "  jal ra, eip7708_append_synthetic_log\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret\n" ++
  "\n" ++
  "eip7708_append_burn_log:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  li a0, 2\n" ++
  "  la a1, eip7708_burn_topic\n" ++
  "  mv a2, s0\n" ++
  "  mv a3, x0\n" ++
  "  mv a4, s1\n" ++
  "  jal ra, eip7708_append_synthetic_log\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret\n" ++
  -- bmvmx.5.5.2.2.ln9ly: re-emit a block_verdict-staged top-level EIP-7708 transfer log AFTER the
  -- dispatcher's per-tx event-log reset (env.eventLogLengthOff=0), so it survives as log 0 (spec
  -- order: top-level value move first, then recipient-code logs). Without this, the single-tx
  -- contract path's pre-dispatch emit (bv_emit_single_tx_tl7708) is wiped by the reset -> receipt
  -- has 0 logs vs expected 1 -> bv_fail=53 (set_code_to_sstore tx_value_1 false reject). Gated on
  -- bv_pending_tl_flag (set ONLY by the single-tx contract emit; 0 for simple-transfer, multi-tx,
  -- system txs, non-block_verdict callers -> no-op). Preserves ALL caller regs (the call site
  -- mid-setup has a live x5/x6/x7 input cursor + x20=env); clears the flag (one-shot per dispatch).
  -- checkpoint stays 0 (correct: a top-level transfer reverts with the recipient).
  "dispatcher_reemit_pending_tl:\n" ++
  "  addi sp, sp, -144\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd t0, 8(sp); sd t1, 16(sp); sd t2, 24(sp); sd t3, 32(sp); sd t4, 40(sp); sd t5, 48(sp); sd t6, 56(sp)\n" ++
  "  sd a0, 64(sp); sd a1, 72(sp); sd a2, 80(sp); sd a3, 88(sp); sd a4, 96(sp); sd a5, 104(sp); sd a6, 112(sp); sd a7, 120(sp)\n" ++
  "  sd x20, 128(sp)\n" ++
  "  la t0, bv_pending_tl_flag; ld t0, 0(t0); beqz t0, .Ldrpt_done\n" ++
  "  la x20, evm_env\n" ++
  "  la a0, eip7708_tl_from32; la a1, eip7708_tl_to32; la a2, eip7708_tl_val32\n" ++
  "  jal ra, eip7708_append_transfer_log\n" ++
  "  la t0, bv_pending_tl_flag; sd x0, 0(t0)\n" ++
  ".Ldrpt_done:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld t0, 8(sp); ld t1, 16(sp); ld t2, 24(sp); ld t3, 32(sp); ld t4, 40(sp); ld t5, 48(sp); ld t6, 56(sp)\n" ++
  "  ld a0, 64(sp); ld a1, 72(sp); ld a2, 80(sp); ld a3, 88(sp); ld a4, 96(sp); ld a5, 104(sp); ld a6, 112(sp); ld a7, 120(sp)\n" ++
  "  ld x20, 128(sp)\n" ++
  "  addi sp, sp, 144\n" ++
  "  ret\n" ++
  -- EIP-4844 blob-fee subtraction tests require BALANCE(ORIGIN) during recipient
  -- execution to observe the sender after the upfront gas/blob/value debit but
  -- before the post-execution gas refund. The dispatcher setup resets per-call
  -- runtime state, so the full dispatcher stages this one-shot record and the
  -- setup emits it after those resets.  The MTx EOA shortcut instead crosses
  -- the callable dispatch reset, so it publishes its upfront debit directly
  -- to the durable AccountState overlay. Preserves every caller register: setup still
  -- has a live input cursor in t0/t1/t2 and env in x20.
  "dispatcher_seed_pending_upfront_balance:\n" ++
  "  addi sp, sp, -144\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd t0, 8(sp); sd t1, 16(sp); sd t2, 24(sp); sd t3, 32(sp); sd t4, 40(sp); sd t5, 48(sp); sd t6, 56(sp)\n" ++
  "  sd a0, 64(sp); sd a1, 72(sp); sd a2, 80(sp); sd a3, 88(sp); sd a4, 96(sp); sd a5, 104(sp); sd a6, 112(sp); sd a7, 120(sp)\n" ++
  "  sd x20, 128(sp)\n" ++
  "  la t0, bv_pending_upfront_balance_flag; ld t0, 0(t0); beqz t0, .Ldpub_recipient\n" ++
  "  la a0, bv_pending_upfront_sender_addr\n" ++
  "  la a1, bv_pending_upfront_sender_pre\n" ++
  "  la a2, bv_pending_upfront_sender_post\n" ++
  "  la t0, bv_pending_upfront_sender_nonce; ld a3, 0(t0); mv a4, a3\n" ++
  "  jal ra, record_nonstorage_effect\n" ++
  "  la t0, bv_pending_upfront_balance_flag; sd x0, 0(t0)\n" ++
  ".Ldpub_recipient:\n" ++
  "  la t0, bv_pending_recipient_credit_flag; ld t0, 0(t0); beqz t0, .Ldpub_done\n" ++
  "  la a0, bv_pending_recipient_addr\n" ++
  "  la a1, bv_pending_recipient_pre\n" ++
  "  la a2, bv_pending_recipient_post\n" ++
  "  la t0, bv_pending_recipient_nonce; ld a3, 0(t0); mv a4, a3\n" ++
  "  jal ra, record_nonstorage_effect\n" ++
  "  la t0, bv_pending_recipient_credit_flag; sd x0, 0(t0)\n" ++
  ".Ldpub_done:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld t0, 8(sp); ld t1, 16(sp); ld t2, 24(sp); ld t3, 32(sp); ld t4, 40(sp); ld t5, 48(sp); ld t6, 56(sp)\n" ++
  "  ld a0, 64(sp); ld a1, 72(sp); ld a2, 80(sp); ld a3, 88(sp); ld a4, 96(sp); ld a5, 104(sp); ld a6, 112(sp); ld a7, 120(sp)\n" ++
  "  ld x20, 128(sp)\n" ++
  "  addi sp, sp, 144\n" ++
  "  ret\n"

def eip7708SyntheticLogTopicData : String :=
  ".balign 8\n" ++
  "eip7708_transfer_topic:\n" ++
  "  .quad 0x28f55a4df523b3ef, 0x952ba7f163c4a116\n" ++
  "  .quad 0x69c2b068fc378daa, 0xddf252ad1be2c89b\n" ++
  "eip7708_burn_topic:\n" ++
  "  .quad 0x71a0fdb75d397ca5, 0x6cffcc184412cf7a\n" ++
  "  .quad 0x815c1ee09dbd0673, 0xcc16f5dbb4873280\n" ++
  -- fhsxz.2.4.2.63.1.6.2.6: 32B right-aligned scratch for the CALL value-transfer log's
  -- `to` topic (callee 20 bytes copied into the low bytes [+12..+32], high 12 zeroed).
  ".balign 8\n" ++
  "eip7708_cd_to32:\n  .zero 32\n" ++
  -- fhsxz.2.4.2.63.1.6.2.6 Part 2: top-level tx transfer-log scratch. The verdict-side
  -- sender/recipient/value are big-endian; these hold them reversed into the LE stack-word
  -- form the log materializer consumes (it byte-reverses each topic slot back to canonical BE;
  -- the appender reverses the value back to BE at descriptor+160).
  ".balign 8\n" ++
  "eip7708_tl_from32:\n  .zero 32\n" ++
  "eip7708_tl_to32:\n  .zero 32\n" ++
  "eip7708_tl_val32:\n  .zero 32\n" ++
  -- bmvmx.5.5.2.2.ln9ly: 1 = a single-tx contract-path top-level transfer log is staged for the
  -- next dispatch to re-emit post-reset (see dispatcher_reemit_pending_tl). Cleared by the dispatcher.
  "bv_pending_tl_flag:\n  .zero 8\n" ++
  -- One-shot sender upfront-balance and recipient-credit seeds, consumed by dispatcher_seed_pending_upfront_balance.
  "bv_pending_upfront_balance_flag:\n  .zero 8\n" ++
  "bv_pending_upfront_sender_nonce:\n  .zero 8\n" ++
  "bv_pending_recipient_credit_flag:\n  .zero 8\n" ++
  "bv_pending_recipient_nonce:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bv_pending_upfront_sender_addr:\n  .zero 32\n" ++
  "bv_pending_upfront_sender_pre:\n  .zero 32\n" ++
  "bv_pending_upfront_sender_post:\n  .zero 32\n" ++
  "bv_pending_recipient_addr:\n  .zero 32\n" ++
  "bv_pending_recipient_pre:\n  .zero 32\n" ++
  "bv_pending_recipient_post:\n  .zero 32\n" ++
  -- GH #10892: the sender's post-transfer balance (`staged_balance - tx.value`), the
  -- `post` operand of the transfer-site `record_nonstorage_effect` that supplies the
  -- missing half of `move_ether`.  A separate cell because `u256_sub_be` clobbers its
  -- destination before returning the borrow, so subtracting into the staged balance
  -- would corrupt it on the borrow path that must leave it untouched.
  "bv_xfer_sender_bal:\n  .zero 32\n"

def eip7708SyntheticLogDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "evm_env:\n" ++
  "  .zero 624\n" ++
  ".balign 8\n" ++
  "evm_event_logs:\n" ++
  "  .zero 1048576\n" ++   -- 4096 × 256-byte LOG event descriptors
  -- .63.1.6.2.1: the synthetic-log appender now records its amount in the
  -- full-data surface too; the standalone probe needs the labels.
  ".balign 8\n" ++
  "evm_log_data:\n  .zero 1048576\n" ++
  "evm_log_data_meta:\n  .zero 65536\n" ++
  "evm_log_data_used:\n  .zero 8\n" ++
  "evm_log_data_overflow:\n  .zero 8\n" ++
  eip7708SyntheticLogTopicData ++
  "eip7708_probe_sender:\n" ++
  "  .quad 0x1111111111111111, 0x1111111111111111, 0x0000000011111111, 0\n" ++
  "eip7708_probe_recipient:\n" ++
  "  .quad 0x2222222222222222, 0x2222222222222222, 0x0000000022222222, 0\n" ++
  "eip7708_probe_account:\n" ++
  "  .quad 0x3333333333333333, 0x3333333333333333, 0x0000000033333333, 0\n" ++
  "eip7708_probe_amount_transfer:\n" ++
  "  .quad 0x8877665544332211, 0xffeeddccbbaa9900, 0x0123456789abcdef, 0xfedcba9876543210\n" ++
  "eip7708_probe_amount_burn:\n" ++
  "  .quad 0x0000000000000005, 0, 0, 0\n" ++
  "eip7708_probe_amount_zero:\n" ++
  "  .zero 32\n"

/-- `zisk_eip7708_synthetic_logs`: probe BuildUnit.

    The first input byte at `INPUT_ADDR + 16` selects mode:
      0/default : append one Transfer log and output its 256-byte descriptor
      1         : append one Burn log and output its 256-byte descriptor
      2         : call the zero-amount Transfer helper and output
                  `{status:u64, descriptor_count:u64}`.

    The split modes keep each check within ziskemu's fixed 256-byte public
    output while still validating the full descriptor shape. -/
def ziskEip7708SyntheticLogsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la x20, evm_env\n" ++
  "  li t0, 0x40000010\n" ++
  "  lbu t1, 0(t0)\n" ++
  "  li t2, 1\n" ++
  "  beq t1, t2, .Leip7708_probe_burn\n" ++
  "  li t2, 2\n" ++
  "  beq t1, t2, .Leip7708_probe_zero\n" ++
  "  la a0, eip7708_probe_sender\n" ++
  "  la a1, eip7708_probe_recipient\n" ++
  "  la a2, eip7708_probe_amount_transfer\n" ++
  "  jal ra, eip7708_append_transfer_log\n" ++
  "  j .Leip7708_probe_copy_desc\n" ++
  ".Leip7708_probe_burn:\n" ++
  "  la a0, eip7708_probe_account\n" ++
  "  la a1, eip7708_probe_amount_burn\n" ++
  "  jal ra, eip7708_append_burn_log\n" ++
  "  j .Leip7708_probe_copy_desc\n" ++
  ".Leip7708_probe_zero:\n" ++
  "  la a0, eip7708_probe_sender\n" ++
  "  la a1, eip7708_probe_recipient\n" ++
  "  la a2, eip7708_probe_amount_zero\n" ++
  "  jal ra, eip7708_append_transfer_log\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  ld t1, 472(x20)\n" ++
  "  sd t1, 8(t0)\n" ++
  "  j .Leip7708_probe_done\n" ++
  ".Leip7708_probe_copy_desc:\n" ++
  "  li t0, 0xa0010000\n" ++
  "  la t1, evm_event_logs\n" ++
  "  li t2, 32\n" ++
  ".Leip7708_probe_copy:\n" ++
  "  ld t3, 0(t1)\n" ++
  "  sd t3, 0(t0)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Leip7708_probe_copy\n" ++
  "  j .Leip7708_probe_done\n" ++
  eip7708SyntheticLogFunctions ++
  ".Leip7708_probe_done:"

def ziskEip7708SyntheticLogsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskEip7708SyntheticLogsPrologue
  dataAsm     := eip7708SyntheticLogDataSection
}

end EvmAsm.Codegen
