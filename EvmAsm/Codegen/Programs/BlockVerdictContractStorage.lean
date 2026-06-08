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

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_recipient_storage_keys

    Enumerate a recipient's BAL storage_changes slot keys.

    Calling convention:
      a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
      a2 = out keys ptr (count x 32-byte big-endian slot keys)
    Returns:
      a0 = count of slot keys written (0 on parse failure — conservative).

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
