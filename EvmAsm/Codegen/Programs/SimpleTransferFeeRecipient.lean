/-
  EvmAsm.Codegen.Programs.SimpleTransferFeeRecipient

  BAL-facing fee-recipient priority-fee checker for the simple transfer path.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Account
import EvmAsm.Codegen.Programs.BalAccountPostFields
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.U256

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## simple_transfer_fee_recipient_bal_verify

    Compute the priority-fee credit for a parse-supported simple transfer
    (`gas_used = 21000`), locate the fee-recipient AccountChanges row, and
    verify that its BAL final balance equals `pre.balance + credit`.

    Calling convention:
      a0 = fee-recipient address ptr (20 bytes)
      a1 = tx ptr
      a2 = tx len
      a3 = base_fee_per_gas ptr (32-byte BE)
      a4 = BAL AccountChanges list ptr
      a5 = BAL AccountChanges list len
      a6 = pre-account record array ptr, 24 bytes per BAL row
      a7 = output ptr

    Output:
      +0   status
             0  ok, including zero priority-credit with no BAL row required
             10 tx effective gas-pricing failed
             11 priority-credit multiplication overflowed
             20 malformed BAL/list row
             21 fee-recipient BAL row missing while credit is nonzero
             30 pre-account balance extraction failed
             31 credit addition overflowed
             40 BAL post-field extraction failed
             41 fee-recipient BAL post balance absent
             42 fee-recipient BAL post balance mismatch
      +8   tx_effective_gas_pricing status
      +16  BAL row index, or UINT64_MAX
      +24  pre-account RLP ptr
      +32  pre-account RLP len
      +40  pre-account record is_insert flag
      +48  post balance raw length
      +56  fee recipient address (20 bytes)
      +80  priority_fee_per_gas, u256 BE
      +112 priority credit, u256 BE
      +144 pre balance, u256 BE
      +176 expected post balance, u256 BE
      +208 normalized BAL post balance, u256 BE
-/
def simpleTransferFeeRecipientBalVerifyFunction : String :=
  "simple_transfer_fee_recipient_bal_verify:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra,   0(sp)\n" ++
  "  sd s0,   8(sp); sd s1,  16(sp); sd s2,  24(sp); sd s3,  32(sp)\n" ++
  "  sd s4,  40(sp); sd s5,  48(sp); sd s6,  56(sp); sd s7,  64(sp)\n" ++
  "  sd s8,  72(sp); sd s9,  80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # fee-recipient address ptr\n" ++
  "  mv s1, a1                   # tx ptr\n" ++
  "  mv s2, a2                   # tx len\n" ++
  "  mv s3, a3                   # base fee ptr\n" ++
  "  mv s4, a4                   # BAL ptr\n" ++
  "  mv s5, a5                   # BAL len\n" ++
  "  mv s6, a6                   # pre-account record array\n" ++
  "  mv s7, a7                   # output ptr\n" ++
  "  mv t0, s7; li t1, 30\n" ++
  ".Lstfv_clear:\n" ++
  "  beqz t1, .Lstfv_clear_done\n" ++
  "  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1\n" ++
  "  j .Lstfv_clear\n" ++
  ".Lstfv_clear_done:\n" ++
  "  li t0, -1; sd t0, 16(s7); sd t0, 48(s7)\n" ++
  "  mv t0, s0; addi t1, s7, 56; li t2, 20\n" ++
  ".Lstfv_addr_copy:\n" ++
  "  beqz t2, .Lstfv_price\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1\n" ++
  "  j .Lstfv_addr_copy\n" ++
  ".Lstfv_price:\n" ++
  "  mv a0, s1; mv a1, s2; mv a2, s3; la a3, stfv_effective_gas_price; addi a4, s7, 80\n" ++
  "  jal ra, tx_effective_gas_pricing\n" ++
  "  sd a0, 8(s7)\n" ++
  "  beqz a0, .Lstfv_have_price\n" ++
  "  li t0, 10; sd t0, 0(s7); j .Lstfv_ret\n" ++
  ".Lstfv_have_price:\n" ++
  "  addi a0, s7, 80; li a1, 21000; addi a2, s7, 112\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  beqz a0, .Lstfv_have_credit\n" ++
  "  li t0, 11; sd t0, 0(s7); j .Lstfv_ret\n" ++
  ".Lstfv_have_credit:\n" ++
  "  addi a0, s7, 112\n" ++
  "  jal ra, u256_is_zero\n" ++
  "  bnez a0, .Lstfv_ok\n" ++
  "  mv a0, s4; mv a1, s5; la a2, stfv_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lstfv_malformed\n" ++
  "  la t0, stfv_count; ld s8, 0(t0) # BAL row count\n" ++
  "  li s9, 0                    # row index\n" ++
  ".Lstfv_row_loop:\n" ++
  "  bgeu s9, s8, .Lstfv_missing\n" ++
  "  mv a0, s4; mv a1, s5; mv a2, s9; la a3, stfv_row_off; la a4, stfv_row_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lstfv_malformed\n" ++
  "  la t0, stfv_row_off; ld t1, 0(t0); add s10, s4, t1\n" ++
  "  la t0, stfv_row_len; ld s11, 0(t0)\n" ++
  "  mv a0, s10; mv a1, s11; li a2, 0; la a3, stfv_addr_off; la a4, stfv_addr_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lstfv_malformed\n" ++
  "  la t0, stfv_addr_len; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lstfv_next_row\n" ++
  "  la t0, stfv_addr_off; ld t0, 0(t0); add t0, s10, t0\n" ++
  "  mv t1, s0; li t2, 20\n" ++
  ".Lstfv_cmp_addr:\n" ++
  "  beqz t2, .Lstfv_found\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lstfv_next_row\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1\n" ++
  "  j .Lstfv_cmp_addr\n" ++
  ".Lstfv_next_row:\n" ++
  "  addi s9, s9, 1\n" ++
  "  j .Lstfv_row_loop\n" ++
  ".Lstfv_found:\n" ++
  "  sd s9, 16(s7)\n" ++
  "  slli t0, s9, 4; slli t1, s9, 3; add t0, t0, t1; add t0, s6, t0\n" ++
  "  ld t2, 0(t0); sd t2, 24(s7)\n" ++
  "  ld t3, 8(t0); sd t3, 32(s7)\n" ++
  "  ld t4, 16(t0); sd t4, 40(s7)\n" ++
  "  mv a0, t2; mv a1, t3; addi a2, s7, 144\n" ++
  "  jal ra, account_extract_balance\n" ++
  "  bnez a0, .Lstfv_pre_balance_fail\n" ++
  "  addi a0, s7, 144; addi a1, s7, 112; addi a2, s7, 176\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lstfv_add_overflow\n" ++
  "  mv a0, s10; mv a1, s11; la a2, stfv_post_raw; la a3, stfv_post_len\n" ++
  "  la a4, stfv_nonce_raw; la a5, stfv_nonce_len\n" ++
  "  jal ra, bal_account_post_fields\n" ++
  "  bnez a0, .Lstfv_post_fail\n" ++
  "  la t0, stfv_post_len; ld t1, 0(t0); sd t1, 48(s7)\n" ++
  "  li t2, -1; beq t1, t2, .Lstfv_post_absent\n" ++
  "  addi t0, s7, 208; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  li t2, 32; sub t2, t2, t1; add t2, t0, t2\n" ++
  "  la t3, stfv_post_raw; mv t4, t1\n" ++
  ".Lstfv_norm_post:\n" ++
  "  beqz t4, .Lstfv_compare\n" ++
  "  lbu t5, 0(t3); sb t5, 0(t2)\n" ++
  "  addi t3, t3, 1; addi t2, t2, 1; addi t4, t4, -1\n" ++
  "  j .Lstfv_norm_post\n" ++
  ".Lstfv_compare:\n" ++
  "  addi a0, s7, 176; addi a1, s7, 208\n" ++
  "  jal ra, u256_eq\n" ++
  "  beqz a0, .Lstfv_mismatch\n" ++
  ".Lstfv_ok:\n" ++
  "  sd zero, 0(s7); j .Lstfv_ret\n" ++
  ".Lstfv_malformed:\n" ++
  "  li t0, 20; sd t0, 0(s7); j .Lstfv_ret\n" ++
  ".Lstfv_missing:\n" ++
  "  li t0, 21; sd t0, 0(s7); j .Lstfv_ret\n" ++
  ".Lstfv_pre_balance_fail:\n" ++
  "  li t0, 30; sd t0, 0(s7); j .Lstfv_ret\n" ++
  ".Lstfv_add_overflow:\n" ++
  "  li t0, 31; sd t0, 0(s7); j .Lstfv_ret\n" ++
  ".Lstfv_post_fail:\n" ++
  "  li t0, 40; sd t0, 0(s7); j .Lstfv_ret\n" ++
  ".Lstfv_post_absent:\n" ++
  "  li t0, 41; sd t0, 0(s7); j .Lstfv_ret\n" ++
  ".Lstfv_mismatch:\n" ++
  "  li t0, 42; sd t0, 0(s7)\n" ++
  ".Lstfv_ret:\n" ++
  "  ld ra,   0(sp)\n" ++
  "  ld s0,   8(sp); ld s1,  16(sp); ld s2,  24(sp); ld s3,  32(sp)\n" ++
  "  ld s4,  40(sp); ld s5,  48(sp); ld s6,  56(sp); ld s7,  64(sp)\n" ++
  "  ld s8,  72(sp); ld s9,  80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/- Probe input:
      +8   tx len
      +16  BAL AccountChanges list len
      +24  account record count
      +32  base_fee_per_gas, 32-byte BE
      +64  fee-recipient address, 20 bytes
      +88  tx bytes
      align8, BAL AccountChanges list bytes
      align8, account table: repeated (u64 account_len, u64 is_insert)
      align8, account RLP blobs in BAL-row order.

   Output is the 240-byte `simple_transfer_fee_recipient_bal_verify` record.
-/
def ziskSimpleTransferFeeRecipientBalVerifyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  ld s1, 8(s0)                # tx len\n" ++
  "  ld s2, 16(s0)               # BAL len\n" ++
  "  ld s3, 24(s0)               # account count\n" ++
  "  addi s4, s0, 32             # base fee ptr\n" ++
  "  addi s5, s0, 64             # fee recipient ptr\n" ++
  "  addi s6, s0, 88             # tx ptr\n" ++
  "  add t0, s6, s1; addi t0, t0, 7; li t1, -8; and s7, t0, t1 # BAL ptr\n" ++
  "  add t0, s7, s2; addi t0, t0, 7; li t1, -8; and s8, t0, t1 # account table\n" ++
  "  slli t0, s3, 4; add s9, s8, t0 # account blob cursor\n" ++
  "  la s10, stfv_records\n" ++
  "  li s11, 0\n" ++
  ".Lstfvp_records:\n" ++
  "  bgeu s11, s3, .Lstfvp_call\n" ++
  "  slli t0, s11, 4; add t1, s8, t0; ld t2, 0(t1); ld t3, 8(t1)\n" ++
  "  slli t4, s11, 4; slli t5, s11, 3; add t4, t4, t5; add t4, s10, t4\n" ++
  "  sd s9, 0(t4); sd t2, 8(t4); sd t3, 16(t4)\n" ++
  "  add s9, s9, t2; addi s9, s9, 7; li t6, -8; and s9, s9, t6\n" ++
  "  addi s11, s11, 1\n" ++
  "  j .Lstfvp_records\n" ++
  ".Lstfvp_call:\n" ++
  "  mv a0, s5; mv a1, s6; mv a2, s1; mv a3, s4; mv a4, s7; mv a5, s2; mv a6, s10\n" ++
  "  li a7, 0xa0010000\n" ++
  "  jal ra, simple_transfer_fee_recipient_bal_verify\n" ++
  "  j .Lstfvp_done\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractGasPricingFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256MinFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  priorityFeePerGasEip1559Function ++ "\n" ++
  txEffectiveGasPricingFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  u256EqFunction ++ "\n" ++
  simpleTransferFeeRecipientBalVerifyFunction ++ "\n" ++
  ".Lstfvp_done:"

def ziskSimpleTransferFeeRecipientBalVerifyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "stfv_count:\n  .zero 8\n" ++
  "stfv_row_off:\n  .zero 8\n" ++
  "stfv_row_len:\n  .zero 8\n" ++
  "stfv_addr_off:\n  .zero 8\n" ++
  "stfv_addr_len:\n  .zero 8\n" ++
  "stfv_post_len:\n  .zero 8\n" ++
  "stfv_nonce_len:\n  .zero 8\n" ++
  "tegp_type:\n  .zero 8\n" ++
  "tegp_inner_off:\n  .zero 8\n" ++
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
  "tefgp_max_priority:\n  .zero 32\n" ++
  "tefgp_max_fee:\n  .zero 32\n" ++
  "tefgp_tmp:\n  .zero 32\n" ++
  "stfv_effective_gas_price:\n  .zero 32\n" ++
  "stfv_post_raw:\n  .zero 32\n" ++
  "stfv_nonce_raw:\n  .zero 32\n" ++
  "u256m_acc:\n  .zero 40\n" ++
  ".balign 8\n" ++
  "stfv_records:\n  .zero 4096\n"

def ziskSimpleTransferFeeRecipientBalVerifyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSimpleTransferFeeRecipientBalVerifyPrologue
  dataAsm     := ziskSimpleTransferFeeRecipientBalVerifyDataSection
}

end EvmAsm.Codegen
