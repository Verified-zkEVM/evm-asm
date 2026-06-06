/-
  EvmAsm.Codegen.Programs.SimpleTransferRecipient

  BAL-facing recipient value-credit checker for the simple transfer path.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Account
import EvmAsm.Codegen.Programs.BalAccountPostFields
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.U256

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## simple_transfer_recipient_bal_verify

    Locate the recipient AccountChanges row in a BAL account list, read the
    corresponding pre-account record, and verify that the BAL final balance
    equals `pre.balance + tx.value`.

    Calling convention:
      a0 = recipient address ptr (20 bytes)
      a1 = tx value ptr (32-byte BE)
      a2 = BAL AccountChanges list ptr
      a3 = BAL AccountChanges list len
      a4 = pre-account record array ptr, 24 bytes per BAL row:
             +0 account RLP ptr, +8 account RLP len, +16 is_insert flag
      a5 = output ptr

    Output:
      +0   status
             0  ok
             10 malformed BAL/list row
             11 recipient BAL row missing
             20 pre-account balance extraction failed
             21 recipient balance credit overflow
             30 BAL post-field extraction failed
             31 recipient BAL post balance absent
             32 recipient BAL post balance mismatch
      +8   BAL row index, or UINT64_MAX
      +16  pre-account RLP ptr
      +24  pre-account RLP len
      +32  pre-account record is_insert flag
      +40  post balance raw length
      +48  recipient address (20 bytes)
      +80  pre balance, u256 BE
      +112 tx value, u256 BE
      +144 expected post balance, u256 BE
      +176 normalized BAL post balance, u256 BE
-/
def simpleTransferRecipientBalVerifyFunction : String :=
  "simple_transfer_recipient_bal_verify:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra,   0(sp)\n" ++
  "  sd s0,   8(sp); sd s1,  16(sp); sd s2,  24(sp); sd s3,  32(sp)\n" ++
  "  sd s4,  40(sp); sd s5,  48(sp); sd s6,  56(sp); sd s7,  64(sp)\n" ++
  "  sd s8,  72(sp); sd s9,  80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # recipient address ptr\n" ++
  "  mv s1, a1                   # tx value ptr\n" ++
  "  mv s2, a2                   # BAL ptr\n" ++
  "  mv s3, a3                   # BAL len\n" ++
  "  mv s4, a4                   # pre-account record array\n" ++
  "  mv s5, a5                   # output ptr\n" ++
  "  # Clear 208 bytes of output and install absent sentinels.\n" ++
  "  mv t0, s5; li t1, 26\n" ++
  ".Lstrv_clear:\n" ++
  "  beqz t1, .Lstrv_clear_done\n" ++
  "  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1\n" ++
  "  j .Lstrv_clear\n" ++
  ".Lstrv_clear_done:\n" ++
  "  li t0, -1; sd t0, 8(s5); sd t0, 40(s5)\n" ++
  "  # Copy diagnostics: recipient address and value.\n" ++
  "  mv t0, s0; addi t1, s5, 48; li t2, 20\n" ++
  ".Lstrv_addr_copy:\n" ++
  "  beqz t2, .Lstrv_value_copy_start\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1\n" ++
  "  j .Lstrv_addr_copy\n" ++
  ".Lstrv_value_copy_start:\n" ++
  "  mv t0, s1; addi t1, s5, 112; li t2, 32\n" ++
  ".Lstrv_value_copy:\n" ++
  "  beqz t2, .Lstrv_count\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1\n" ++
  "  j .Lstrv_value_copy\n" ++
  ".Lstrv_count:\n" ++
  "  mv a0, s2; mv a1, s3; la a2, strv_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lstrv_malformed\n" ++
  "  la t0, strv_count; ld s6, 0(t0) # BAL row count\n" ++
  "  li s7, 0                    # row index\n" ++
  ".Lstrv_row_loop:\n" ++
  "  bgeu s7, s6, .Lstrv_missing\n" ++
  "  mv a0, s2; mv a1, s3; mv a2, s7; la a3, strv_row_off; la a4, strv_row_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lstrv_malformed\n" ++
  "  la t0, strv_row_off; ld t1, 0(t0); add s8, s2, t1\n" ++
  "  la t0, strv_row_len; ld s9, 0(t0)\n" ++
  "  mv a0, s8; mv a1, s9; li a2, 0; la a3, strv_addr_off; la a4, strv_addr_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lstrv_malformed\n" ++
  "  la t0, strv_addr_len; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lstrv_next_row\n" ++
  "  la t0, strv_addr_off; ld t0, 0(t0); add t0, s8, t0\n" ++
  "  mv t1, s0; li t2, 20\n" ++
  ".Lstrv_cmp_addr:\n" ++
  "  beqz t2, .Lstrv_found\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lstrv_next_row\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1\n" ++
  "  j .Lstrv_cmp_addr\n" ++
  ".Lstrv_next_row:\n" ++
  "  addi s7, s7, 1\n" ++
  "  j .Lstrv_row_loop\n" ++
  ".Lstrv_found:\n" ++
  "  sd s7, 8(s5)\n" ++
  "  slli t0, s7, 4; slli t1, s7, 3; add t0, t0, t1; add s10, s4, t0\n" ++
  "  ld t2, 0(s10); sd t2, 16(s5)\n" ++
  "  ld t3, 8(s10); sd t3, 24(s5)\n" ++
  "  ld t4, 16(s10); sd t4, 32(s5)\n" ++
  "  mv a0, t2; mv a1, t3; addi a2, s5, 80\n" ++
  "  jal ra, account_extract_balance\n" ++
  "  bnez a0, .Lstrv_pre_balance_fail\n" ++
  "  addi a0, s5, 80; mv a1, s1; addi a2, s5, 144\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lstrv_overflow\n" ++
  "  mv a0, s8; mv a1, s9; la a2, strv_post_raw; la a3, strv_post_len\n" ++
  "  la a4, strv_nonce_raw; la a5, strv_nonce_len\n" ++
  "  jal ra, bal_account_post_fields\n" ++
  "  bnez a0, .Lstrv_post_fail\n" ++
  "  la t0, strv_post_len; ld s11, 0(t0); sd s11, 40(s5)\n" ++
  "  li t1, -1; beq s11, t1, .Lstrv_post_absent\n" ++
  "  # Normalize raw canonical BE bytes into a right-aligned u256 at +176.\n" ++
  "  addi t0, s5, 176; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  li t1, 32; sub t1, t1, s11; add t1, t0, t1\n" ++
  "  la t2, strv_post_raw; mv t3, s11\n" ++
  ".Lstrv_norm_post:\n" ++
  "  beqz t3, .Lstrv_compare\n" ++
  "  lbu t4, 0(t2); sb t4, 0(t1)\n" ++
  "  addi t2, t2, 1; addi t1, t1, 1; addi t3, t3, -1\n" ++
  "  j .Lstrv_norm_post\n" ++
  ".Lstrv_compare:\n" ++
  "  addi a0, s5, 144; addi a1, s5, 176\n" ++
  "  jal ra, u256_eq\n" ++
  "  beqz a0, .Lstrv_mismatch\n" ++
  "  sd zero, 0(s5); j .Lstrv_ret\n" ++
  ".Lstrv_malformed:\n" ++
  "  li t0, 10; sd t0, 0(s5); j .Lstrv_ret\n" ++
  ".Lstrv_missing:\n" ++
  "  li t0, 11; sd t0, 0(s5); j .Lstrv_ret\n" ++
  ".Lstrv_pre_balance_fail:\n" ++
  "  li t0, 20; sd t0, 0(s5); j .Lstrv_ret\n" ++
  ".Lstrv_overflow:\n" ++
  "  li t0, 21; sd t0, 0(s5); j .Lstrv_ret\n" ++
  ".Lstrv_post_fail:\n" ++
  "  li t0, 30; sd t0, 0(s5); j .Lstrv_ret\n" ++
  ".Lstrv_post_absent:\n" ++
  "  li t0, 31; sd t0, 0(s5); j .Lstrv_ret\n" ++
  ".Lstrv_mismatch:\n" ++
  "  li t0, 32; sd t0, 0(s5)\n" ++
  ".Lstrv_ret:\n" ++
  "  ld ra,   0(sp)\n" ++
  "  ld s0,   8(sp); ld s1,  16(sp); ld s2,  24(sp); ld s3,  32(sp)\n" ++
  "  ld s4,  40(sp); ld s5,  48(sp); ld s6,  56(sp); ld s7,  64(sp)\n" ++
  "  ld s8,  72(sp); ld s9,  80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/- Probe input:
      +8   BAL AccountChanges list len
      +16  account record count
      +24  recipient address, 20 bytes
      +48  value, 32-byte BE
      +80  BAL AccountChanges list bytes
      align8, account table: repeated (u64 account_len, u64 is_insert)
      align8, account RLP blobs in BAL-row order.

   Output is the 208-byte `simple_transfer_recipient_bal_verify` record.
-/
def ziskSimpleTransferRecipientBalVerifyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  ld s1, 8(s0)                # BAL len\n" ++
  "  ld s2, 16(s0)               # account count\n" ++
  "  addi s3, s0, 24             # recipient address ptr\n" ++
  "  addi s4, s0, 48             # value ptr\n" ++
  "  addi s5, s0, 80             # BAL ptr\n" ++
  "  add t0, s5, s1; addi t0, t0, 7; li t1, -8; and s6, t0, t1 # account table\n" ++
  "  slli t0, s2, 4; add s7, s6, t0 # account blob cursor\n" ++
  "  la s8, strv_records\n" ++
  "  li s9, 0\n" ++
  ".Lstrvp_records:\n" ++
  "  bgeu s9, s2, .Lstrvp_call\n" ++
  "  slli t0, s9, 4; add t1, s6, t0; ld t2, 0(t1); ld t3, 8(t1)\n" ++
  "  slli t4, s9, 4; slli t5, s9, 3; add t4, t4, t5; add t4, s8, t4\n" ++
  "  sd s7, 0(t4); sd t2, 8(t4); sd t3, 16(t4)\n" ++
  "  add s7, s7, t2; addi s7, s7, 7; li t6, -8; and s7, s7, t6\n" ++
  "  addi s9, s9, 1\n" ++
  "  j .Lstrvp_records\n" ++
  ".Lstrvp_call:\n" ++
  "  mv a0, s3; mv a1, s4; mv a2, s5; mv a3, s1; mv a4, s8\n" ++
  "  li a5, 0xa0010000\n" ++
  "  jal ra, simple_transfer_recipient_bal_verify\n" ++
  "  j .Lstrvp_done\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256EqFunction ++ "\n" ++
  simpleTransferRecipientBalVerifyFunction ++ "\n" ++
  ".Lstrvp_done:"

def ziskSimpleTransferRecipientBalVerifyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "strv_count:\n  .zero 8\n" ++
  "strv_row_off:\n  .zero 8\n" ++
  "strv_row_len:\n  .zero 8\n" ++
  "strv_addr_off:\n  .zero 8\n" ++
  "strv_addr_len:\n  .zero 8\n" ++
  "strv_post_len:\n  .zero 8\n" ++
  "strv_nonce_len:\n  .zero 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  "bpf_list_off:\n  .zero 8\n" ++
  "bpf_list_len:\n  .zero 8\n" ++
  "bpf_list_ptr:\n  .zero 8\n" ++
  "bpf_count:\n  .zero 8\n" ++
  "bpf_item_off:\n  .zero 8\n" ++
  "bpf_item_len:\n  .zero 8\n" ++
  "bpf_item_ptr:\n  .zero 8\n" ++
  "bpf_val_off:\n  .zero 8\n" ++
  "bpf_val_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "strv_post_raw:\n  .zero 32\n" ++
  "strv_nonce_raw:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "strv_records:\n  .zero 4096\n"

def ziskSimpleTransferRecipientBalVerifyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSimpleTransferRecipientBalVerifyPrologue
  dataAsm     := ziskSimpleTransferRecipientBalVerifyDataSection
}

end EvmAsm.Codegen
