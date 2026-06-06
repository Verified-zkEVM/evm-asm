/-
  EvmAsm.Codegen.Programs.BlockVerdictSimpleTransfer

  Shared extraction helper for the parse-supported one-transaction simple
  value-transfer path used by block_verdict.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxExtract

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## simple_transfer_tx_context

    Read the transaction-list/public-key globals prepared by block_verdict and
    materialize the stable per-transaction context needed by later BAL
    descriptor writers.

    Calling convention:
      a0 = output ptr

    Reads:
      bv_tx_count, bv_tx_list_ptr, bv_tx_list_len, bv_tx_item_start,
      bv_public_keys_ptr, bv_public_keys_len, bv_exec_p.

    Output:
      +0   status
             0  ok: single tx, 65-byte pubkey, non-creation, empty calldata
             1  transaction count is not exactly one
             2  public key bundle is not exactly 65 bytes
             3  tx item start exceeds tx list length
             4  tx item is empty
             20 nonce/gas extraction failed
             21 type inner offset exceeds tx length
             30 to-address extraction failed
             40 value extraction failed
             50 data-section extraction failed
             60 contract creation transaction
             61 non-empty calldata/initcode
             62 EIP-4844 blob transaction; this helper does not yet account
                for blob-fee precharge
             63 EIP-7702 set-code transaction; this helper does not yet
                account for authorization-list gas/processing
      +8   tx ptr
      +16  tx len
      +24  selected pubkey ptr (64-byte x||y tail)
      +32  base_fee_per_gas ptr (32-byte BE in execution payload)
      +40  tx gas limit u64
      +48  is_creation flag
      +56  data ptr
      +64  data len
      +72  recipient address, 20 bytes
      +96  value, 32-byte BE
      +128 nonce/gas extractor status
      +136 to-address extractor status
      +144 value extractor status
      +152 data-section extractor status
      +160 tx type (0 legacy, 1 EIP-2930, 2 EIP-1559, 3 EIP-4844,
           4 EIP-7702)
      +168 tx inner offset
      +176 tx inner ptr
      +184 tx inner len
-/
def simpleTransferTxContextFunction : String :=
  "simple_transfer_tx_context:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # output ptr\n" ++
  "  sd zero,   0(s0); sd zero,   8(s0); sd zero,  16(s0); sd zero,  24(s0)\n" ++
  "  sd zero,  32(s0); sd zero,  40(s0); sd zero,  48(s0); sd zero,  56(s0)\n" ++
  "  sd zero,  64(s0); sd zero,  72(s0); sd zero,  80(s0); sd zero,  88(s0)\n" ++
  "  sd zero,  96(s0); sd zero, 104(s0); sd zero, 112(s0); sd zero, 120(s0)\n" ++
  "  sd zero, 128(s0); sd zero, 136(s0); sd zero, 144(s0); sd zero, 152(s0)\n" ++
  "  sd zero, 160(s0); sd zero, 168(s0); sd zero, 176(s0); sd zero, 184(s0)\n" ++
  "  la t0, bv_tx_count; ld t1, 0(t0); li t2, 1; beq t1, t2, .Lsttc_count_ok\n" ++
  "  li t0, 1; sd t0, 0(s0); j .Lsttc_ret\n" ++
  ".Lsttc_count_ok:\n" ++
  "  la t0, bv_public_keys_len; ld t1, 0(t0); li t2, 65; beq t1, t2, .Lsttc_pubkey_ok\n" ++
  "  li t0, 2; sd t0, 0(s0); j .Lsttc_ret\n" ++
  ".Lsttc_pubkey_ok:\n" ++
  "  la t0, bv_tx_list_ptr; ld s1, 0(t0)\n" ++
  "  la t0, bv_tx_list_len; ld s2, 0(t0)\n" ++
  "  la t0, bv_tx_item_start; ld s3, 0(t0)\n" ++
  "  bltu s2, s3, .Lsttc_item_oob\n" ++
  "  beq s2, s3, .Lsttc_item_empty\n" ++
  "  add s1, s1, s3              # tx ptr\n" ++
  "  sub s2, s2, s3              # tx len\n" ++
  "  sd s1, 8(s0); sd s2, 16(s0)\n" ++
  "  la t0, bv_public_keys_ptr; ld t1, 0(t0); addi t1, t1, 1; sd t1, 24(s0)\n" ++
  "  la t0, bv_exec_p; ld t1, 0(t0); addi t1, t1, 160; sd t1, 32(s0)\n" ++
  "  mv a0, s1; mv a1, s2; la a2, tea_type; la a3, tea_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Lsttc_type_ok\n" ++
  "  li t0, 20; sd t0, 0(s0); j .Lsttc_ret\n" ++
  ".Lsttc_type_ok:\n" ++
  "  la t0, tea_type; ld t1, 0(t0); sd t1, 160(s0)\n" ++
  "  la t0, tea_inner_off; ld t3, 0(t0); sd t3, 168(s0)\n" ++
  "  bltu s2, t3, .Lsttc_inner_oob\n" ++
  "  add t4, s1, t3; sd t4, 176(s0)\n" ++
  "  sub t4, s2, t3; sd t4, 184(s0)\n" ++
  "  li t2, 3; bne t1, t2, .Lsttc_not_blob_tx\n" ++
  "  li t0, 62; sd t0, 0(s0); j .Lsttc_ret\n" ++
  ".Lsttc_not_blob_tx:\n" ++
  "  li t2, 4; bne t1, t2, .Lsttc_not_set_code_tx\n" ++
  "  li t0, 63; sd t0, 0(s0); j .Lsttc_ret\n" ++
  ".Lsttc_not_set_code_tx:\n" ++
  "  mv a0, s1; mv a1, s2; la a2, sttc_nonce; addi a3, s0, 40\n" ++
  "  jal ra, tx_extract_nonce_and_gas\n" ++
  "  sd a0, 128(s0)\n" ++
  "  beqz a0, .Lsttc_gas_ok\n" ++
  "  li t0, 20; sd t0, 0(s0); j .Lsttc_ret\n" ++
  ".Lsttc_gas_ok:\n" ++
  "  mv a0, s1; mv a1, s2; addi a2, s0, 72; addi a3, s0, 48\n" ++
  "  jal ra, tx_extract_to_address\n" ++
  "  sd a0, 136(s0)\n" ++
  "  beqz a0, .Lsttc_to_ok\n" ++
  "  li t0, 30; sd t0, 0(s0); j .Lsttc_ret\n" ++
  ".Lsttc_to_ok:\n" ++
  "  mv a0, s1; mv a1, s2; addi a2, s0, 96\n" ++
  "  jal ra, tx_extract_value\n" ++
  "  sd a0, 144(s0)\n" ++
  "  beqz a0, .Lsttc_value_ok\n" ++
  "  li t0, 40; sd t0, 0(s0); j .Lsttc_ret\n" ++
  ".Lsttc_value_ok:\n" ++
  "  mv a0, s1; mv a1, s2; addi a2, s0, 56; addi a3, s0, 64\n" ++
  "  jal ra, tx_extract_data_section\n" ++
  "  sd a0, 152(s0)\n" ++
  "  beqz a0, .Lsttc_data_ok\n" ++
  "  li t0, 50; sd t0, 0(s0); j .Lsttc_ret\n" ++
  ".Lsttc_data_ok:\n" ++
  "  ld t0, 48(s0); beqz t0, .Lsttc_not_creation\n" ++
  "  li t1, 60; sd t1, 0(s0); j .Lsttc_ret\n" ++
  ".Lsttc_not_creation:\n" ++
  "  ld t0, 64(s0); beqz t0, .Lsttc_ok\n" ++
  "  li t1, 61; sd t1, 0(s0); j .Lsttc_ret\n" ++
  ".Lsttc_ok:\n" ++
  "  sd zero, 0(s0); j .Lsttc_ret\n" ++
  ".Lsttc_item_oob:\n" ++
  "  li t0, 3; sd t0, 0(s0); j .Lsttc_ret\n" ++
  ".Lsttc_item_empty:\n" ++
  "  li t0, 4; sd t0, 0(s0)\n" ++
  "  j .Lsttc_ret\n" ++
  ".Lsttc_inner_oob:\n" ++
  "  li t0, 21; sd t0, 0(s0)\n" ++
  ".Lsttc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def blockVerdictSimpleTransferDataSection : String :=
  ".balign 8\n" ++
  "sttc_nonce:\n  .zero 8\n" ++
  "tea_type:\n  .zero 8\n" ++
  "tea_inner_off:\n  .zero 8\n" ++
  "tea_field_off:\n  .zero 8\n" ++
  "tea_field_len:\n  .zero 8\n" ++
  "tev_type:\n  .zero 8\n" ++
  "tev_inner_off:\n  .zero 8\n" ++
  "teds_type:\n  .zero 8\n" ++
  "teds_inner_off:\n  .zero 8\n" ++
  "teds_field_off:\n  .zero 8\n" ++
  "teds_field_len:\n  .zero 8\n" ++
  "t48_offset:\n  .zero 8\n" ++
  "t48_length:\n  .zero 8\n" ++
  "bv_simple_transfer_tx:\n  .zero 192\n"

def blockVerdictTxGasPrechargeDataSection : String :=
  ".balign 8\n" ++
  "tgsbl_tmp_off:\n  .zero 8\n" ++
  "tgsbl_tmp_len:\n  .zero 8\n" ++
  "tgsbl_count:\n  .zero 8\n" ++
  "tgsbl_row_off:\n  .zero 8\n" ++
  "tgsbl_row_len:\n  .zero 8\n" ++
  "tgsbl_addr_off:\n  .zero 8\n" ++
  "tgsbl_addr_len:\n  .zero 8\n" ++
  "teng_type:\n  .zero 8\n" ++
  "teng_inner_off:\n  .zero 8\n" ++
  "tegp_type:\n  .zero 8\n" ++
  "tegp_inner_off:\n  .zero 8\n" ++
  blockVerdictSimpleTransferDataSection ++
  ".balign 32\n" ++
  "tefgp_max_priority:\n  .zero 32\n" ++
  "tefgp_max_fee:\n  .zero 32\n" ++
  "tefgp_tmp:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "txup_nonce:\n  .zero 8\n" ++
  "txup_gas_limit:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "txup_effective_gas_price:\n  .zero 32\n" ++
  "txup_priority_fee:\n  .zero 32\n" ++
  "acpg_gas_fee:\n  .zero 32\n" ++
  "tgbpv_balance:\n  .zero 32\n" ++
  "tgbpv_refund:\n  .zero 32\n" ++
  "tgbpv_expected_balance:\n  .zero 32\n" ++
  "tgbpv_post_balance:\n  .zero 32\n" ++
  "tgbpv_value:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "tgbpv_nonce:\n  .zero 8\n" ++
  "tgbpv_lookup:\n  .zero 168\n" ++
  "tgbpv_records:\n  .zero 4096\n" ++
  "bv_tx_gas_precharge:\n  .zero 224\n"

/- Probe input:
      +8   tx_list_len
      +16  tx_item_start
      +24  tx_count
      +32  public_keys_len
      +64  fake execution payload (base_fee starts at +160)
      +320 public keys blob
      +448 transaction-list bytes

   Output is the 192-byte simple_transfer_tx_context record.
-/
def ziskSimpleTransferTxContextPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  addi t0, s0, 64; la t1, bv_exec_p; sd t0, 0(t1)\n" ++
  "  addi t0, s0, 320; la t1, bv_public_keys_ptr; sd t0, 0(t1)\n" ++
  "  ld t0, 32(s0); la t1, bv_public_keys_len; sd t0, 0(t1)\n" ++
  "  addi t0, s0, 448; la t1, bv_tx_list_ptr; sd t0, 0(t1)\n" ++
  "  ld t0, 8(s0); la t1, bv_tx_list_len; sd t0, 0(t1)\n" ++
  "  ld t0, 16(s0); la t1, bv_tx_item_start; sd t0, 0(t1)\n" ++
  "  ld t0, 24(s0); la t1, bv_tx_count; sd t0, 0(t1)\n" ++
  "  li a0, 0xa0010000\n" ++
  "  jal ra, simple_transfer_tx_context\n" ++
  "  j .Lsttcp_done\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractNonceAndGasFunction ++ "\n" ++
  txExtractToAddressFunction ++ "\n" ++
  txExtractValueFunction ++ "\n" ++
  txExtractDataSectionFunction ++ "\n" ++
  simpleTransferTxContextFunction ++ "\n" ++
  ".Lsttcp_done:"

def ziskSimpleTransferTxContextDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bv_exec_p:\n  .zero 8\n" ++
  "bv_tx_list_ptr:\n  .zero 8\n" ++
  "bv_tx_list_len:\n  .zero 8\n" ++
  "bv_tx_count:\n  .zero 8\n" ++
  "bv_tx_item_start:\n  .zero 8\n" ++
  "bv_public_keys_ptr:\n  .zero 8\n" ++
  "bv_public_keys_len:\n  .zero 8\n" ++
  "teng_type:\n  .zero 8\n" ++
  "teng_inner_off:\n  .zero 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  blockVerdictSimpleTransferDataSection

def ziskSimpleTransferTxContextProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSimpleTransferTxContextPrologue
  dataAsm     := ziskSimpleTransferTxContextDataSection
}

end EvmAsm.Codegen
