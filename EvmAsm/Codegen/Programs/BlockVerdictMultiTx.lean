/-
  EvmAsm.Codegen.Programs.BlockVerdictMultiTx

  Per-INDEX transaction context extractor for the multi-transaction dispatch
  spine (evm-asm-fhsxz.2.4.2.57.11.6). `simple_transfer_tx_context` only
  supports a single-transaction block (it bails when bv_tx_count != 1). This
  helper extracts the i-th transaction of an N-transaction SSZ transaction
  list, materializing the same 192-byte per-transaction context record so a
  multi-tx dispatch loop can run each transaction through the runtime.

  The SSZ `transactions` list is a list of variable-length elements: a u32
  little-endian offset table (4 bytes per element) followed by the concatenated
  element bytes. The element count is offset[0] / 4, and element i spans
  [offset[i], offset[i+1]) (the final element ends at the list length). This is
  the same encoding walked by block_receipt_records_materialize
  (BlockVerdictReceiptRecords.lean). Once tx[i]'s [ptr,len) is located, the
  extraction tail is identical to simple_transfer_tx_context.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransfer

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## multi_tx_nth_context

    Extract the i-th transaction of the SSZ transaction list prepared by
    block_verdict into a 192-byte per-transaction context record.

    Calling convention:
      a0 = output record ptr (same 192-byte layout as simple_transfer_tx_context;
           see BlockVerdictSimpleTransfer.lean for field offsets)
      a1 = transaction index i

    Reads bv_tx_list_ptr / bv_tx_list_len. Unlike simple_transfer_tx_context it
    does NOT read bv_tx_count / bv_tx_item_start / bv_public_keys_* / bv_exec_p:
    sender public key (record +24) and base_fee (record +32) are per-call inputs
    supplied by the multi-tx dispatch loop, so this helper leaves them zero and
    populates only the transaction-intrinsic fields.

    Status (record +0):
      0  ok: classified creation or non-creation, legacy/2930/1559/blob/7702 tx
      3  malformed transaction list (too short / offset table not 4-aligned /
         offset out of range)
      4  transaction item is empty
      5  index >= transaction count
      20 type dispatch or nonce/gas extraction failed
      21 type inner offset exceeds tx length
      30 to-address extraction failed
      40 value extraction failed
      50 data-section extraction failed
      60 reserved (formerly contract creation transaction)
      61 reserved (formerly non-empty calldata/initcode)
      62 reserved (formerly EIP-4844 blob unsupported)
      63 reserved (formerly EIP-7702 set-code unsupported) -/
def multiTxNthContextFunction : String :=
  "multi_tx_nth_context:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # output record ptr\n" ++
  "  mv s4, a1                   # transaction index i\n" ++
  "  mv t0, s0; li t1, 24\n" ++
  ".Lmtx_zero:\n" ++
  "  beqz t1, .Lmtx_zero_done\n" ++
  "  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; j .Lmtx_zero\n" ++
  ".Lmtx_zero_done:\n" ++
  "  la t0, bv_tx_list_ptr; ld s1, 0(t0)   # SSZ tx list ptr\n" ++
  "  la t0, bv_tx_list_len; ld s2, 0(t0)   # tx list len\n" ++
  "  li t0, 4; bltu s2, t0, .Lmtx_malformed\n" ++
  "  mv a0, s1; jal ra, bgv_u32le           # offset[0]\n" ++
  "  andi t0, a0, 3; bnez t0, .Lmtx_malformed\n" ++
  "  srli s3, a0, 2                         # tx count = offset[0] / 4\n" ++
  "  bgeu s4, s3, .Lmtx_oob\n" ++
  "  slli t0, s4, 2; add a0, s1, t0; jal ra, bgv_u32le\n" ++
  "  mv s5, a0                              # offset[i]\n" ++
  "  addi t0, s4, 1; beq t0, s3, .Lmtx_last\n" ++
  "  slli t1, t0, 2; add a0, s1, t1; jal ra, bgv_u32le\n" ++
  "  mv s6, a0                              # offset[i+1]\n" ++
  "  j .Lmtx_have_next\n" ++
  ".Lmtx_last:\n" ++
  "  mv s6, s2                              # final tx ends at list end\n" ++
  ".Lmtx_have_next:\n" ++
  "  slli t0, s3, 2; bltu s5, t0, .Lmtx_malformed   # offset[i] must be past table\n" ++
  "  bltu s6, s5, .Lmtx_malformed\n" ++
  "  bgtu s6, s2, .Lmtx_malformed\n" ++
  "  add s1, s1, s5                         # tx ptr\n" ++
  "  sub s2, s6, s5                         # tx len\n" ++
  "  beqz s2, .Lmtx_item_empty\n" ++
  "  sd s1, 8(s0); sd s2, 16(s0)\n" ++
  "  mv a0, s1; mv a1, s2; la a2, tea_type; la a3, tea_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Lmtx_type_ok\n" ++
  "  li t0, 20; sd t0, 0(s0); j .Lmtx_ret\n" ++
  ".Lmtx_type_ok:\n" ++
  "  la t0, tea_type; ld t1, 0(t0); sd t1, 160(s0)\n" ++
  "  la t0, tea_inner_off; ld t3, 0(t0); sd t3, 168(s0)\n" ++
  "  bltu s2, t3, .Lmtx_inner_oob\n" ++
  "  add t4, s1, t3; sd t4, 176(s0)\n" ++
  "  sub t4, s2, t3; sd t4, 184(s0)\n" ++
  "  mv a0, s1; mv a1, s2; la a2, sttc_nonce; addi a3, s0, 40\n" ++
  "  jal ra, tx_extract_nonce_and_gas\n" ++
  "  sd a0, 128(s0)\n" ++
  "  beqz a0, .Lmtx_gas_ok\n" ++
  "  li t0, 20; sd t0, 0(s0); j .Lmtx_ret\n" ++
  ".Lmtx_gas_ok:\n" ++
  "  mv a0, s1; mv a1, s2; addi a2, s0, 72; addi a3, s0, 48\n" ++
  "  jal ra, tx_extract_to_address\n" ++
  "  sd a0, 136(s0)\n" ++
  "  beqz a0, .Lmtx_to_ok\n" ++
  "  li t0, 30; sd t0, 0(s0); j .Lmtx_ret\n" ++
  ".Lmtx_to_ok:\n" ++
  "  mv a0, s1; mv a1, s2; addi a2, s0, 96\n" ++
  "  jal ra, tx_extract_value\n" ++
  "  sd a0, 144(s0)\n" ++
  "  beqz a0, .Lmtx_value_ok\n" ++
  "  li t0, 40; sd t0, 0(s0); j .Lmtx_ret\n" ++
  ".Lmtx_value_ok:\n" ++
  "  mv a0, s1; mv a1, s2; addi a2, s0, 56; addi a3, s0, 64\n" ++
  "  jal ra, tx_extract_data_section\n" ++
  "  sd a0, 152(s0)\n" ++
  "  beqz a0, .Lmtx_data_ok\n" ++
  "  li t0, 50; sd t0, 0(s0); j .Lmtx_ret\n" ++
  ".Lmtx_data_ok:\n" ++
  ".Lmtx_not_creation:\n" ++
  -- fhsxz.2.4.2.57.11.6.5 (experiment): allow calldata-bearing txs. ctx+56/+64 hold
  -- the calldata ptr/len (tx_extract_data_section); dispatch's stage_runtime_payload_code
  -- stages both, so a non-empty-calldata call dispatches like any self-contained recipient.
  ".Lmtx_ok:\n" ++
  "  sd zero, 0(s0); j .Lmtx_ret\n" ++
  ".Lmtx_malformed:\n" ++
  "  li t0, 3; sd t0, 0(s0); j .Lmtx_ret\n" ++
  ".Lmtx_oob:\n" ++
  "  li t0, 5; sd t0, 0(s0); j .Lmtx_ret\n" ++
  ".Lmtx_item_empty:\n" ++
  "  li t0, 4; sd t0, 0(s0); j .Lmtx_ret\n" ++
  ".Lmtx_inner_oob:\n" ++
  "  li t0, 21; sd t0, 0(s0)\n" ++
  ".Lmtx_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_multi_tx_nth_context`: focused probe for the per-index extractor.
    Input at INPUT_ADDR (0x40000000):
      +8   tx_list_len
      +16  transaction index i
      +640 SSZ transaction-list bytes (u32 offset table + concatenated txs)
    Output at 0xa0010000: the 192-byte multi_tx_nth_context record. -/
def ziskMultiTxNthContextPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  addi t0, s0, 640; la t1, bv_tx_list_ptr; sd t0, 0(t1)\n" ++
  "  ld t0, 8(s0); la t1, bv_tx_list_len; sd t0, 0(t1)\n" ++
  "  ld a1, 16(s0)               # transaction index\n" ++
  "  li a0, 0xa0010000\n" ++
  "  jal ra, multi_tx_nth_context\n" ++
  "  j .Lmtxp_done\n" ++
  bgvU32leFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractNonceAndGasFunction ++ "\n" ++
  txExtractToAddressFunction ++ "\n" ++
  txExtractValueFunction ++ "\n" ++
  txExtractDataSectionFunction ++ "\n" ++
  multiTxNthContextFunction ++ "\n" ++
  ".Lmtxp_done:"

def ziskMultiTxNthContextDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bv_tx_list_ptr:\n  .zero 8\n" ++
  "bv_tx_list_len:\n  .zero 8\n" ++
  "teng_type:\n  .zero 8\n" ++
  "teng_inner_off:\n  .zero 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  blockVerdictSimpleTransferDataSection

def ziskMultiTxNthContextProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMultiTxNthContextPrologue
  dataAsm     := ziskMultiTxNthContextDataSection
}

end EvmAsm.Codegen
