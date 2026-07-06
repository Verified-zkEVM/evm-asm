/-
  EvmAsm.Codegen.Programs.BlockVerdictContractStorage

  Recipient storage-key enumeration for contract-recipient runtime execution
  (evm-asm-fhsxz.2.4.2.57.11.6.4.3.1). To build the M22 storage-preload that
  stage_runtime_payload_code consumes (so SLOAD/SSTORE compute correct
  EIP-2200/3529 gas), the wiring needs the recipient's accessed storage slot
  keys. This helper enumerates the slot keys from the recipient's BAL
  AccountChanges entry [address, storage_changes, storage_reads, ...]: each
  storage_changes entry is RLP [slot_key, [ (tx_index,new_value) ... ]], so the
  slot key is item 0 (a <=32-byte big-endian value, left-padded to 32 bytes).
  The .6.4.3.2 wiring pairs each key with its ORIGINAL pre-block value via
  slot_at_header_state_root (StateCompose.lean) to form the (key,value) preload.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_recipient_storage_keys

    Enumerate a recipient's BAL storage_changes slot keys.

    Calling convention:
      a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
      a2 = out keys ptr (count x 32-byte big-endian slot keys; caller buffer must hold
           bsrAccountSlotCap entries)
    Returns:
      a0 = entry count (0 on parse failure — conservative). Keys are written only when
           the count is <= 512 (the caller-buffer cap); if it exceeds 512, NOTHING is
           written and the true count is returned so the caller can bail conservatively.

    Reads item 1 (storage_changes) of the AccountChanges list; for each entry,
    reads item 0 (the slot key) and writes it left-padded to 32 bytes. -/
def balRecipientStorageKeysFunction : String :=
  "bal_recipient_storage_keys:\n" ++
  "  addi sp, sp, -72\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                    # account ptr\n" ++
  "  mv s1, a1                    # account len\n" ++
  "  mv s2, a2                    # out keys ptr\n" ++
  -- storage_changes = account item 1.
  "  mv a0, s0; mv a1, s1; li a2, 1; la a3, brsk_off; la a4, brsk_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbrsk_fail\n" ++
  "  la t0, brsk_off; ld t0, 0(t0); add s3, s0, t0   # sc_ptr\n" ++
  "  la t0, brsk_len; ld s4, 0(t0)                   # sc_len\n" ++
  "  mv a0, s3; mv a1, s4; la a2, brsk_cnt\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbrsk_fail\n" ++
  "  la t0, brsk_cnt; ld s5, 0(t0)                   # entry count\n" ++
  -- bmvmx.1.7.3 / fhsxz.2.4.2.66.1.2: cap the write at the caller KEY-buffer size —
  -- bvcd_keys, csce_keys and sps_keys are all sized bsrAccountSlotCap*32. The cap is
  -- gas-derived (= bsrMaxBalItems: one account's changes+reads can absorb the whole
  -- 200M BAL budget; the former 512 cap false-rejected queue-heavy blocks far below
  -- 200M). If the BAL declares MORE storage_changes than fit, write NOTHING and return
  -- the true count so the caller bails conservatively (.Ldtrc_unsupported /
  -- skip-account / requests-hash fail) instead of overflowing into adjacent .data. The
  -- regular-tx callers still bail at their own >128 thresholds (bvcd_preload and the
  -- callee-seed table stay 128-sized); only the system-call preload path consumes
  -- large counts.
  "  li t0, " ++ toString bsrAccountSlotCap ++ "; bgtu s5, t0, .Lbrsk_done            # count > cap -> return count, write nothing\n" ++
  "  mv s6, zero                  # i\n" ++
  "  mv s7, s2                    # out cursor\n" ++
  ".Lbrsk_loop:\n" ++
  "  beq s6, s5, .Lbrsk_done\n" ++
  -- entry = nth(storage_changes, i).
  "  mv a0, s3; mv a1, s4; mv a2, s6; la a3, brsk_eoff; la a4, brsk_elen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbrsk_fail\n" ++
  "  la t0, brsk_eoff; ld t0, 0(t0); add t1, s3, t0  # entry ptr\n" ++
  "  la t0, brsk_elen; ld t2, 0(t0)                  # entry len\n" ++
  -- slot key = nth(entry, 0).
  "  mv a0, t1; mv a1, t2; li a2, 0; la a3, brsk_soff; la a4, brsk_slen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbrsk_fail\n" ++
  "  la t0, brsk_eoff; ld t0, 0(t0); add t1, s3, t0  # recompute entry ptr\n" ++
  "  la t0, brsk_soff; ld t3, 0(t0); add t1, t1, t3  # slot bytes ptr\n" ++
  "  la t0, brsk_slen; ld t4, 0(t0)                  # slot byte length\n" ++
  "  li t5, 32; bgtu t4, t5, .Lbrsk_fail\n" ++
  -- zero the 32-byte output slot, then right-align the slot bytes.
  "  mv t0, s7; li t5, 32\n" ++
  ".Lbrsk_zero:\n" ++
  "  beqz t5, .Lbrsk_zero_done\n" ++
  "  sb zero, 0(t0); addi t0, t0, 1; addi t5, t5, -1; j .Lbrsk_zero\n" ++
  ".Lbrsk_zero_done:\n" ++
  "  li t5, 32; sub t5, t5, t4; add t0, s7, t5       # dst = cursor + (32 - slen)\n" ++
  ".Lbrsk_copy:\n" ++
  "  beqz t4, .Lbrsk_copy_done\n" ++
  "  lbu t5, 0(t1); sb t5, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t4, t4, -1; j .Lbrsk_copy\n" ++
  ".Lbrsk_copy_done:\n" ++
  "  addi s7, s7, 32; addi s6, s6, 1; j .Lbrsk_loop\n" ++
  ".Lbrsk_done:\n" ++
  "  mv a0, s5\n" ++
  "  j .Lbrsk_ret\n" ++
  ".Lbrsk_fail:\n" ++
  "  li a0, 0\n" ++
  ".Lbrsk_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 72\n" ++
  "  ret"

/-- `bal_recipient_storage_reads_keys` (fhsxz.2.4.2.57.11.6.5 revert fix) — enumerate a
    recipient's BAL `storage_reads` (AccountChanges item 2): slots ACCESSED but not
    net-changed (e.g. a reverting tx writes-then-reverts -> the slot is a read, not a change,
    so `storage_changes` is empty and the recipient preload misses it -> SSTORE-clears
    undercharge). Each `storage_reads` entry IS a slot key (RLP-minimal big-endian U256,
    unlike `storage_changes` whose entry is `[key, [...]]`). Appends right-aligned 32-byte BE
    keys to the out buffer (same encoding as `bal_recipient_storage_keys`, so the caller's
    BE->LE preload re-tag applies identically).

    Calling convention:
      a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP len
      a2 = out keys ptr             a3 = max slots to write (remaining buffer capacity)
    Returns a0 = storage_reads count. If count > a3 (or > 512) writes NOTHING and returns the
    true count so the caller bails conservatively instead of overflowing. Empty/absent
    storage_reads or any parse failure returns 0 (conservative). -/
def balRecipientStorageReadsKeysFunction : String :=
  "bal_recipient_storage_reads_keys:\n" ++
  "  addi sp, sp, -72\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                    # AccountChanges ptr\n" ++
  "  mv s1, a1                    # AccountChanges len\n" ++
  "  mv s2, a2                    # out keys ptr\n" ++
  "  mv s3, a3                    # max slots (remaining capacity)\n" ++
  -- storage_reads = AccountChanges item 2.
  "  mv a0, s0; mv a1, s1; li a2, 2; la a3, brsk_off; la a4, brsk_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbrsrk_zero\n" ++                     -- absent/fail -> 0 reads (conservative)
  "  la t0, brsk_off; ld t0, 0(t0); add s4, s0, t0   # sr_ptr\n" ++
  "  la t0, brsk_len; ld s5, 0(t0)                   # sr_len\n" ++
  "  mv a0, s4; mv a1, s5; la a2, brsk_cnt\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbrsrk_zero\n" ++
  "  la t0, brsk_cnt; ld s6, 0(t0)                   # sr count\n" ++
  -- fhsxz.2.4.2.66.1.2: absolute clamp = bsrAccountSlotCap, in lockstep with the key
  -- buffers; the real per-caller bound is a3 (remaining capacity), which every caller passes.
  "  li t0, " ++ toString bsrAccountSlotCap ++ "; bgtu s6, t0, .Lbrsrk_done           # > cap -> count, write nothing\n" ++
  "  bgtu s6, s3, .Lbrsrk_done                       # > remaining capacity -> count, write nothing\n" ++
  "  li s7, 0                     # i (SAVED reg: rlp_list_nth_item clobbers t-regs)\n" ++
  ".Lbrsrk_loop:\n" ++
  "  beq s7, s6, .Lbrsrk_done\n" ++
  -- entry = nth(storage_reads, i); the entry IS the slot key bytes.
  "  mv a0, s4; mv a1, s5; mv a2, s7; la a3, brsk_eoff; la a4, brsk_elen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbrsrk_zero\n" ++
  "  la t0, brsk_eoff; ld t0, 0(t0); add t1, s4, t0  # key bytes ptr\n" ++
  "  la t0, brsk_elen; ld t4, 0(t0)                  # key byte length\n" ++
  "  li t5, 32; bgtu t4, t5, .Lbrsrk_zero\n" ++
  -- dst entry = out + i*32; zero it, then right-align the key bytes.
  "  slli t0, s7, 5; add t2, s2, t0                  # dst entry ptr\n" ++
  "  mv t0, t2; li t5, 32\n" ++
  ".Lbrsrk_zw:\n" ++
  "  beqz t5, .Lbrsrk_zwd\n" ++
  "  sb zero, 0(t0); addi t0, t0, 1; addi t5, t5, -1; j .Lbrsrk_zw\n" ++
  ".Lbrsrk_zwd:\n" ++
  "  li t5, 32; sub t5, t5, t4; add t0, t2, t5       # dst = entry + (32 - keylen)\n" ++
  ".Lbrsrk_cp:\n" ++
  "  beqz t4, .Lbrsrk_cpd\n" ++
  "  lbu t5, 0(t1); sb t5, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t4, t4, -1; j .Lbrsrk_cp\n" ++
  ".Lbrsrk_cpd:\n" ++
  "  addi s7, s7, 1; j .Lbrsrk_loop\n" ++
  ".Lbrsrk_done:\n" ++
  "  mv a0, s6\n" ++
  "  j .Lbrsrk_ret\n" ++
  ".Lbrsrk_zero:\n" ++
  "  li a0, 0\n" ++
  ".Lbrsrk_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 72\n" ++
  "  ret"

/-- `zisk_bal_recipient_storage_keys`: validation probe over a hand-encoded
    AccountChanges with one storage_changes entry whose slot key low byte is
    0x07. RLP layout (63 bytes): f8 3d [94 ++ 20*00] [e3 e2 (a0 ++ 31*00 ++ 07) c0] c0 c0 c0 c0.
    Output: +0 count (expect 1); +8 slot key byte 31 (expect 0x07); +16 slot key
    byte 0 (expect 0x00, left-pad). -/
def ziskBalRecipientStorageKeysPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la a0, brsk_acct\n" ++
  "  li a1, 63\n" ++
  "  la a2, brsk_out\n" ++
  "  jal ra, bal_recipient_storage_keys\n" ++
  "  li s0, 0xa0010000\n" ++
  "  sd a0, 0(s0)\n" ++
  "  la t0, brsk_out\n" ++
  "  lbu t1, 31(t0); sd t1, 8(s0)\n" ++
  "  lbu t1, 0(t0); sd t1, 16(s0)\n" ++
  "  j .Lbrskp_done\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  balRecipientStorageKeysFunction ++ "\n" ++
  ".Lbrskp_done:"

def ziskBalRecipientStorageKeysDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "brsk_off:\n  .zero 8\n" ++
  "brsk_len:\n  .zero 8\n" ++
  "brsk_cnt:\n  .zero 8\n" ++
  "brsk_eoff:\n  .zero 8\n" ++
  "brsk_elen:\n  .zero 8\n" ++
  "brsk_soff:\n  .zero 8\n" ++
  "brsk_slen:\n  .zero 8\n" ++
  "brsk_out:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "brsk_acct:\n" ++
  "  .byte 0xf8, 0x3d\n" ++
  "  .byte 0x94\n" ++
  "  .zero 20\n" ++
  "  .byte 0xe3, 0xe2, 0xa0\n" ++
  "  .zero 31\n" ++
  "  .byte 0x07\n" ++
  "  .byte 0xc0\n" ++
  "  .byte 0xc0, 0xc0, 0xc0, 0xc0\n"

def ziskBalRecipientStorageKeysProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalRecipientStorageKeysPrologue
  dataAsm     := ziskBalRecipientStorageKeysDataSection
}

end EvmAsm.Codegen
