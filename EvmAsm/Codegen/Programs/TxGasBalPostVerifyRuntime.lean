/-
  EvmAsm.Codegen.Programs.TxGasBalPostVerifyRuntime

  Execution-derived sender BAL post-balance verifier for a CONTRACT-recipient
  transaction (bead bmvmx.1.6.3, balance slice).

  The EOA verifier `tx_gas_bal_post_verify` (TxGasBalPostVerify.lean) hardcodes
  the simple-transfer settlement (21000 intrinsic, full unused-gas refund). A
  contract recipient instead consumes runtime gas, so the sender's settlement is

      sender_post = sender_pre - receipt_inc * effective_gas_price - blob_fee - value

  where `blob_fee` is nonzero only for EIP-4844 transactions, computed as
  `blob_gas_used * blob_gas_price`, and `receipt_inc` is the EIP-3529-refunded, EIP-7623-floored gas (the `a2`
  output of `tx_gas_result_increments`), i.e. exactly `sender_debit_from_gas`
  (#8583) with the now-real per-tx refund counter (#8590). This helper composes:

    1. `tx_gas_sender_bal_lookup`  -> sender BAL row, pre-balance, post-balance
    2. `tx_effective_gas_pricing`  -> effective_gas_price
    3. `tx_extract_value`          -> value
    4. `sender_debit_from_gas`     -> gas_debit = receipt_inc * eff_gas_price, then
                                      add the EIP-4844 blob fee when tx type = 3
                                      (value passed as 0 so the value netting is
                                      applied separately, honoring self-transfer)
    5. `expected = pre - gas_debit`, then `-= value` unless the recipient IS the
       sender (EIP-7708 transfer_to_self: the value returns within the tx)
    6. compare `expected` against the BAL's declared sender post balance.

  SOUNDNESS NOTE (for the verdict wiring, next slice): this is exact ONLY when
  execution cannot move value to/from the sender beyond the initial `value`
  debit. `bytecode_is_self_contained` no longer rejects CALL/CALLCODE/SELFDESTRUCT,
  so the verdict caller must additionally gate on "recipient bytecode has no
  value-moving opcode" and "sender is neither the coinbase nor a withdrawal
  recipient" before treating a mismatch as a reject. This helper performs no such
  gating itself — it is the arithmetic kernel; the caller stays conservative.

  Runtime gas inputs are read from the global block `tgbpvr_in` (4 u64, LE):
    +0 gas_limit  +8 gas_left  +16 refund_counter  +24 calldata_floor_gas_cost
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Account
import EvmAsm.Codegen.Programs.Address
import EvmAsm.Codegen.Programs.BalAccountPostFields
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.TxGasSenderBalLookup
import EvmAsm.Codegen.Programs.TxDecode4844
import EvmAsm.Codegen.Programs.U256GasPricing
import EvmAsm.Codegen.Programs.SenderBalanceDebit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## tx_gas_bal_post_verify_runtime

    Calling convention:
      a0 = tx ptr
      a1 = tx len
      a2 = base_fee_per_gas ptr (32 B BE)
      a3 = selected sender public key ptr (64 B x||y)
      a4 = BAL AccountChanges list ptr
      a5 = BAL AccountChanges list len
      a6 = pre-account record array ptr (24 B per BAL row)
      a7 = output ptr
      (runtime gas read from the global block `tgbpvr_in`)

    Output:
      +0   status
             0  ok (sender post balance matches expected)
             10 sender BAL lookup failed
             33 sender BAL post balance absent / >32 bytes
             37 tx value extraction failed
             38 sender final balance underflow (pre < debit, or < value)
             39 effective gas pricing inconclusive (extract-fail / overflow) -> caller skips
             40 sender BAL post balance mismatch
             50 fee invalid (max_fee < base_fee, or priority > max_fee) -> caller rejects (bmvmx.4)
      +8   sender address (20 B)
      +32  pre balance, u256 BE
      +64  gas_debit = receipt_inc * effective_gas_price + blob_fee, u256 BE
      +96  expected post balance, u256 BE
      +128 normalized BAL post balance, u256 BE
      +160 tx value, u256 BE -/
def txGasBalPostVerifyRuntimeFunction : String :=
  "tx_gas_bal_post_verify_runtime:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra,   0(sp)\n" ++
  "  sd s0,   8(sp); sd s1,  16(sp); sd s2,  24(sp); sd s3,  32(sp)\n" ++
  "  sd s4,  40(sp); sd s5,  48(sp); sd s6,  56(sp); sd s7,  64(sp)\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx len\n" ++
  "  mv s2, a2                   # base fee ptr\n" ++
  "  mv s3, a3                   # pubkey ptr\n" ++
  "  mv s4, a4                   # BAL ptr\n" ++
  "  mv s5, a5                   # BAL len\n" ++
  "  mv s6, a6                   # pre-account records ptr\n" ++
  "  mv s7, a7                   # output ptr\n" ++
  "  # Clear the 192-byte output window.\n" ++
  "  mv t0, s7; li t1, 24\n" ++
  ".Ltgbpvr_clear:\n" ++
  "  beqz t1, .Ltgbpvr_cleared\n" ++
  "  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; j .Ltgbpvr_clear\n" ++
  ".Ltgbpvr_cleared:\n" ++
  "  # 1. Locate sender BAL row + pre/post scalar fields.\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s3; mv a3, s4; mv a4, s5; mv a5, s6\n" ++
  "  la a6, tgbpvr_lookup\n" ++
  "  jal ra, tx_gas_sender_bal_lookup\n" ++
  "  la t0, tgbpvr_lookup; ld t1, 0(t0); beqz t1, .Ltgbpvr_have_lookup\n" ++
  "  li t0, 10; sd t0, 0(s7); j .Ltgbpvr_ret\n" ++
  ".Ltgbpvr_have_lookup:\n" ++
  "  # Copy sender address (lookup+16, 20 B) -> out+8.\n" ++
  "  la t0, tgbpvr_lookup; addi t2, t0, 16; addi t3, s7, 8; li t4, 20\n" ++
  ".Ltgbpvr_copy_addr:\n" ++
  "  beqz t4, .Ltgbpvr_after_addr\n" ++
  "  lbu t5, 0(t2); sb t5, 0(t3); addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1\n" ++
  "  j .Ltgbpvr_copy_addr\n" ++
  ".Ltgbpvr_after_addr:\n" ++
  "  # Copy pre balance (lookup+48, 32 B BE) -> tgbpvr_pre and out+32.\n" ++
  "  la t0, tgbpvr_lookup; addi t2, t0, 48; la t3, tgbpvr_pre; addi t4, s7, 32\n" ++
  "  ld t5,  0(t2); sd t5, 0(t3); sd t5, 0(t4)\n" ++
  "  ld t5,  8(t2); sd t5, 8(t3); sd t5, 8(t4)\n" ++
  "  ld t5, 16(t2); sd t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t2); sd t5, 24(t3); sd t5, 24(t4)\n" ++
  "  # 2. Post balance present and <=32 bytes?\n" ++
  "  la t0, tgbpvr_lookup; ld t1, 88(t0)\n" ++
  "  li t2, -1; bne t1, t2, .Ltgbpvr_post_present\n" ++
  "  li t0, 33; sd t0, 0(s7); j .Ltgbpvr_ret\n" ++
  ".Ltgbpvr_post_present:\n" ++
  "  li t2, 32; bleu t1, t2, .Ltgbpvr_post_len_ok\n" ++
  "  li t0, 33; sd t0, 0(s7); j .Ltgbpvr_ret\n" ++
  ".Ltgbpvr_post_len_ok:\n" ++
  "  # Normalize the BAL post balance (right-align len bytes) into tgbpvr_post.\n" ++
  "  la t0, tgbpvr_post; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t1, tgbpvr_lookup; ld t2, 88(t1); addi t3, t1, 96\n" ++
  "  la t4, tgbpvr_post; li t5, 32; sub t5, t5, t2; add t4, t4, t5\n" ++
  "  mv t5, t2\n" ++
  ".Ltgbpvr_post_copy:\n" ++
  "  beqz t5, .Ltgbpvr_post_done\n" ++
  "  lbu t6, 0(t3); sb t6, 0(t4); addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1\n" ++
  "  j .Ltgbpvr_post_copy\n" ++
  ".Ltgbpvr_post_done:\n" ++
  "  la t0, tgbpvr_post; addi t4, s7, 128\n" ++
  "  ld t5, 0(t0); sd t5, 0(t4); ld t5, 8(t0); sd t5, 8(t4)\n" ++
  "  ld t5, 16(t0); sd t5, 16(t4); ld t5, 24(t0); sd t5, 24(t4)\n" ++
  "  # 3. effective_gas_price.\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; la a3, tgbpvr_egp; la a4, tgbpvr_prio\n" ++
  "  jal ra, tx_effective_gas_pricing\n" ++
  "  beqz a0, .Ltgbpvr_egp_ok\n" ++
  -- bmvmx.4: tx_effective_gas_pricing returns 2 = priority_fee > max_fee
  -- (PriorityFeeGreaterThanMaxFeeError) and 3 = max_fee < base_fee
  -- (InsufficientMaxFeePerGasError) -- check_transaction conditions the spec
  -- REJECTS on. Surface those as a distinct status 50 so the verdict rejects
  -- (not skips). The other non-zero returns (1 extract-fail, 4 eff-price
  -- overflow) stay status 39 = conservative skip (can't cleanly determine).
  "  li t1, 2; beq a0, t1, .Ltgbpvr_fee_invalid\n" ++
  "  li t1, 3; beq a0, t1, .Ltgbpvr_fee_invalid\n" ++
  "  li t0, 39; sd t0, 0(s7); j .Ltgbpvr_ret\n" ++
  ".Ltgbpvr_fee_invalid:\n" ++
  "  li t0, 50; sd t0, 0(s7); j .Ltgbpvr_ret\n" ++
  ".Ltgbpvr_egp_ok:\n" ++
  "  # 4. value.\n" ++
  "  mv a0, s0; mv a1, s1; la a2, tgbpvr_value\n" ++
  "  jal ra, tx_extract_value\n" ++
  "  beqz a0, .Ltgbpvr_value_ok\n" ++
  "  li t0, 37; sd t0, 0(s7); j .Ltgbpvr_ret\n" ++
  ".Ltgbpvr_value_ok:\n" ++
  "  la t0, tgbpvr_value; addi t4, s7, 160\n" ++
  "  ld t5, 0(t0); sd t5, 0(t4); ld t5, 8(t0); sd t5, 8(t4)\n" ++
  "  ld t5, 16(t0); sd t5, 16(t4); ld t5, 24(t0); sd t5, 24(t4)\n" ++
  "  # 5. gas_debit = receipt_inc * eff_gas_price, plus blob fee for type-3 txs.\n" ++
  "  la t0, tgbpvr_in; ld a0, 0(t0); ld a1, 8(t0); ld a2, 16(t0); ld a3, 24(t0)\n" ++
  "  la a4, tgbpvr_egp; la a5, tgbpvr_zero; la a6, tgbpvr_gasdebit\n" ++
  "  jal ra, sender_debit_from_gas\n" ++
  "  mv a0, s0; mv a1, s1; la a2, tgbpvr_tx_type; la a3, tgbpvr_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Ltgbpvr_blob_inconclusive\n" ++
  "  la t0, tgbpvr_tx_type; ld t1, 0(t0); li t2, 3; bne t1, t2, .Ltgbpvr_blob_done\n" ++
  "  la t0, tgbpvr_inner_off; ld t3, 0(t0); bltu s1, t3, .Ltgbpvr_blob_inconclusive\n" ++
  "  add a0, s0, t3; sub a1, s1, t3; la a2, tcbg_struct\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Ltgbpvr_blob_inconclusive\n" ++
  "  la t0, tcbg_struct; lwu t1, 168(t0); lwu t2, 172(t0)\n" ++
  "  la t3, tgbpvr_inner_off; ld t3, 0(t3); add t3, s0, t3; add a0, t3, t1; mv a1, t2; la a2, tgbpvr_blob_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Ltgbpvr_blob_inconclusive\n" ++
  "  la t0, tgbpvr_blob_count; ld a1, 0(t0); beqz a1, .Ltgbpvr_blob_inconclusive\n" ++
  "  li t2, 6; bgtu a1, t2, .Ltgbpvr_blob_inconclusive\n" ++
  "  slli a1, a1, 17\n" ++
  "  la a0, bsg_blob_price_be; la a2, tgbpvr_blobdebit\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Ltgbpvr_blob_overflow\n" ++
  "  la a0, tgbpvr_gasdebit; la a1, tgbpvr_blobdebit; la a2, tgbpvr_gasdebit\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Ltgbpvr_blob_overflow\n" ++
  "  j .Ltgbpvr_blob_done\n" ++
  ".Ltgbpvr_blob_inconclusive:\n" ++
  "  li t0, 39; sd t0, 0(s7); j .Ltgbpvr_ret\n" ++
  ".Ltgbpvr_blob_overflow:\n" ++
  "  li t0, 38; sd t0, 0(s7); j .Ltgbpvr_ret\n" ++
  ".Ltgbpvr_blob_done:\n" ++
  "  la t0, tgbpvr_gasdebit; addi t4, s7, 64\n" ++
  "  ld t5, 0(t0); sd t5, 0(t4); ld t5, 8(t0); sd t5, 8(t4)\n" ++
  "  ld t5, 16(t0); sd t5, 16(t4); ld t5, 24(t0); sd t5, 24(t4)\n" ++
  "  # 6. expected = pre - gas_debit.\n" ++
  "  la a0, tgbpvr_pre; la a1, tgbpvr_gasdebit; la a2, tgbpvr_expected\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  beqz a0, .Ltgbpvr_sub_gas_ok\n" ++
  "  li t0, 38; sd t0, 0(s7); j .Ltgbpvr_ret\n" ++
  ".Ltgbpvr_sub_gas_ok:\n" ++
  "  # 7. Value netting, skipped on a transfer-to-self recipient (EIP-7708).\n" ++
  "  mv a0, s0; mv a1, s1; la a2, tgbpvr_to; la a3, tgbpvr_iscreation\n" ++
  "  jal ra, tx_extract_to_address\n" ++
  "  bnez a0, .Ltgbpvr_value_subtract\n" ++
  "  la t0, tgbpvr_iscreation; ld t1, 0(t0); bnez t1, .Ltgbpvr_value_subtract\n" ++
  "  la t0, tgbpvr_to; la t1, tgbpvr_lookup; addi t1, t1, 16; li t2, 20\n" ++
  ".Ltgbpvr_self_cmp:\n" ++
  "  beqz t2, .Ltgbpvr_skip_value\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Ltgbpvr_value_subtract\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Ltgbpvr_self_cmp\n" ++
  ".Ltgbpvr_value_subtract:\n" ++
  "  la a0, tgbpvr_expected; la a1, tgbpvr_value; la a2, tgbpvr_expected\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  beqz a0, .Ltgbpvr_skip_value\n" ++
  "  li t0, 38; sd t0, 0(s7); j .Ltgbpvr_ret\n" ++
  ".Ltgbpvr_skip_value:\n" ++
  "  la t0, tgbpvr_expected; addi t4, s7, 96\n" ++
  "  ld t5, 0(t0); sd t5, 0(t4); ld t5, 8(t0); sd t5, 8(t4)\n" ++
  "  ld t5, 16(t0); sd t5, 16(t4); ld t5, 24(t0); sd t5, 24(t4)\n" ++
  "  # 8. Compare expected vs BAL post.\n" ++
  "  la a0, tgbpvr_expected; la a1, tgbpvr_post\n" ++
  "  jal ra, u256_eq\n" ++
  "  li t0, 1; beq a0, t0, .Ltgbpvr_ok\n" ++
  "  li t0, 40; sd t0, 0(s7); j .Ltgbpvr_ret\n" ++
  ".Ltgbpvr_ok:\n" ++
  "  sd zero, 0(s7)\n" ++
  ".Ltgbpvr_ret:\n" ++
  "  ld ra,   0(sp)\n" ++
  "  ld s0,   8(sp); ld s1,  16(sp); ld s2,  24(sp); ld s3,  32(sp)\n" ++
  "  ld s4,  40(sp); ld s5,  48(sp); ld s6,  56(sp); ld s7,  64(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/- Probe input (same layout as `tx_gas_bal_post_verify`):
      +8   tx_len
      +16  BAL len
      +24  account count
      +32  base_fee_per_gas, 32 B BE
      +64  sender pubkey, 64 B
      +128 tx bytes
      align8, BAL bytes
      align8, account length table (u64 each), account RLP blobs align8 each.
   Runtime gas (gas_limit, gas_left, refund, floor) is hardcoded in the prologue
   (the check script's expected computation mirrors these constants). -/
def ziskTxGasBalPostVerifyRuntimePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  ld s1, 8(s0)                # tx_len\n" ++
  "  ld s2, 16(s0)               # BAL len\n" ++
  "  ld s3, 24(s0)               # account count\n" ++
  "  addi s4, s0, 32             # base_fee ptr\n" ++
  "  addi s5, s0, 64             # pubkey ptr\n" ++
  "  addi s6, s0, 128            # tx ptr\n" ++
  "  add t0, s6, s1; addi t0, t0, 7; li t1, -8; and s7, t0, t1 # BAL ptr\n" ++
  "  add t0, s7, s2; addi t0, t0, 7; li t1, -8; and s8, t0, t1 # length table\n" ++
  "  slli t0, s3, 3; add s9, s8, t0   # account blob cursor\n" ++
  "  la s10, tgbpvr_records\n" ++
  "  li s11, 0\n" ++
  ".Ltgbpvrp_records:\n" ++
  "  bgeu s11, s3, .Ltgbpvrp_gas\n" ++
  "  slli t0, s11, 3; add t1, s8, t0; ld t2, 0(t1) # account len\n" ++
  "  slli t3, s11, 4; add t4, t3, t0; add t4, s10, t4\n" ++
  "  sd s9, 0(t4); sd t2, 8(t4); sd zero, 16(t4)\n" ++
  "  add s9, s9, t2; addi s9, s9, 7; li t5, -8; and s9, s9, t5\n" ++
  "  addi s11, s11, 1\n" ++
  "  j .Ltgbpvrp_records\n" ++
  ".Ltgbpvrp_gas:\n" ++
  "  # Runtime gas: gas_limit=100000, gas_left=40000, refund=5000, floor=21000.\n" ++
  "  # before_refund=60000, applied_refund=min(5000, 60000/5)=5000,\n" ++
  "  # after_refund=55000, receipt_inc=max(55000,21000)=55000.\n" ++
  "  la t0, tgbpvr_in\n" ++
  "  li t1, 100000; sd t1, 0(t0)\n" ++
  "  li t1, 40000;  sd t1, 8(t0)\n" ++
  "  li t1, 5000;   sd t1, 16(t0)\n" ++
  "  li t1, 21000;  sd t1, 24(t0)\n" ++
  "  mv a0, s6; mv a1, s1; mv a2, s4; mv a3, s5; mv a4, s7; mv a5, s2; mv a6, s10\n" ++
  "  li a7, 0xa0010000\n" ++
  "  jal ra, tx_gas_bal_post_verify_runtime\n" ++
  "  j .Ltgbpvrp_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  addressFromPubkeyFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  accountExtractNonceFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  txGasSenderBalLookupFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractNonceAndGasFunction ++ "\n" ++
  txExtractValueFunction ++ "\n" ++
  txExtractToAddressFunction ++ "\n" ++
  txExtractGasPricingFunction ++ "\n" ++
  -- cursor-walk helpers (closure-drift fix for rewritten decoders)
  rlpWalkHelpersClosure ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256EqFunction ++ "\n" ++
  u256MinFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  priorityFeePerGasEip1559Function ++ "\n" ++
  txEffectiveGasPricingFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  txGasResultIncrementsFunction ++ "\n" ++
  senderDebitFromGasFunction ++ "\n" ++
  txGasBalPostVerifyRuntimeFunction ++ "\n" ++
  ".Ltgbpvrp_done:"

def ziskTxGasBalPostVerifyRuntimeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "tgsbl_tmp_off:\n  .zero 8\n" ++
  "tgsbl_tmp_len:\n  .zero 8\n" ++
  "tgsbl_count:\n  .zero 8\n" ++
  "tgsbl_row_off:\n  .zero 8\n" ++
  "tgsbl_row_len:\n  .zero 8\n" ++
  "tgsbl_addr_off:\n  .zero 8\n" ++
  "tgsbl_addr_len:\n  .zero 8\n" ++
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
  "teng_type:\n  .zero 8\n" ++
  "teng_inner_off:\n  .zero 8\n" ++
  "tev_type:\n  .zero 8\n" ++
  "tev_inner_off:\n  .zero 8\n" ++
  "tea_type:\n  .zero 8\n" ++
  "tea_inner_off:\n  .zero 8\n" ++
  "tea_field_off:\n  .zero 8\n" ++
  "tea_field_len:\n  .zero 8\n" ++
  "t48_offset:\n  .zero 8\n" ++
  "t48_length:\n  .zero 8\n" ++
  "tegp_type:\n  .zero 8\n" ++
  "tegp_inner_off:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "afp_digest:\n  .zero 32\n" ++
  "zk3_state:\n  .zero 200\n" ++
  ".balign 32\n" ++
  "tefgp_max_priority:\n  .zero 32\n" ++
  "tefgp_max_fee:\n  .zero 32\n" ++
  "tefgp_tmp:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n  .zero 40\n" ++
  ".balign 32\n" ++
  "sdfg_gascost:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "tgbpvr_in:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "tgbpvr_pre:\n  .zero 32\n" ++
  "tgbpvr_post:\n  .zero 32\n" ++
  "tgbpvr_egp:\n  .zero 32\n" ++
  "tgbpvr_prio:\n  .zero 32\n" ++
  "tgbpvr_value:\n  .zero 32\n" ++
  "tgbpvr_gasdebit:\n  .zero 32\n" ++
  "tgbpvr_expected:\n  .zero 32\n" ++
  "tgbpvr_zero:\n  .zero 32\n" ++
  "tgbpvr_blobdebit:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "tgbpvr_to:\n  .zero 24\n" ++
  "tgbpvr_iscreation:\n  .zero 8\n" ++
  "tgbpvr_tx_type:\n  .zero 8\n" ++
  "tgbpvr_inner_off:\n  .zero 8\n" ++
  "tgbpvr_blob_count:\n  .zero 8\n" ++
  "tcbg_struct:\n  .zero 248\n" ++
  ".balign 32\n" ++
  "tcbg_blob_fee_be:\n  .zero 32\n" ++
  "bsg_blob_price_be:\n  .zero 32\n" ++
  "tgbpvr_lookup:\n  .zero 168\n" ++
  "tgbpvr_records:\n  .zero 4096"

def ziskTxGasBalPostVerifyRuntimeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxGasBalPostVerifyRuntimePrologue
  dataAsm     := ziskTxGasBalPostVerifyRuntimeDataSection
}

end EvmAsm.Codegen
