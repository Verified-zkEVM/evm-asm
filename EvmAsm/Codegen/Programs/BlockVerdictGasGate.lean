/-
  EvmAsm.Codegen.Programs.BlockVerdictGasGate

  EIP-8037 transaction gas inclusion gate split out from BlockVerdict.lean
  to keep the verdict module under the file-size cap.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.TxDecode4844
import EvmAsm.Codegen.Programs.IntrinsicGas
import EvmAsm.Codegen.Programs.AmsterdamSystemTx

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## eip8037_tx_gas_gate -- conservative legacy transaction inclusion gate.
    a0 = exec_payload ptr   a1 = BAL ptr   a2 = BAL len   a3 = block_gas_limit
    a0 (output) = 0 ok/unsupported, 1 regular overflow, 2 state overflow,
                  3 validate_transaction gas failure.

    This mirrors the gas portion of Prague `validate_transaction` for legacy,
    EIP-2930, EIP-1559, EIP-4844, and EIP-7702 transactions that this gate can
    parse cheaply: `max(intrinsic_gas, calldata_floor_gas_cost) <= tx.gas`.
    The EIP-8037 `TX_MAX_GAS_LIMIT` cap is also enforced as a
    transaction-validity rule. Malformed tx lists, unknown tx types. The gate
    also mirrors the execution-spec pre-execution block-gas
    availability check when it can prove rejection from the intrinsic/floor gas
    lower bound of prior transactions. Single-transaction overflow is always
    invalid. Multi-transaction worst-regular overflow is not a safe
    pre-runtime rejection because prior transactions may return unused gas; it
    is deferred to the post-runtime exact gas-used check for supported rows. -/
def eip8037TxGasGateFunction : String :=
  "eip8037_state_used_before_tx:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                   # BAL ptr\n" ++
  "  mv s1, a1                   # BAL len\n" ++
  "  mv s2, a2                   # target tx index (1-based)\n" ++
  "  mv s3, a3                   # out ptr\n" ++
  "  sd zero, 0(s3)\n" ++
  "  mv a0, s0; mv a1, s1; la a2, bsg_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lesub_ok\n" ++
  "  la t0, bsg_count; ld s4, 0(t0)        # account count\n" ++
  "  li s5, 0                              # account i\n" ++
  ".Lesub_acct_loop:\n" ++
  "  beq s5, s4, .Lesub_ok\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s5; la a3, bsg_off; la a4, bsg_len\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  bnez a0, .Lesub_ok\n" ++
  "  la t0, bsg_off; ld t1, 0(t0); add s6, s0, t1     # account ptr\n" ++
  "  la t0, bsg_len; ld s7, 0(t0)                     # account len\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 1; la a3, bsg_off; la a4, bsg_len\n" ++
  "  jal ra, rlp_item_span                              # storage_changes list\n" ++
  "  bnez a0, .Lesub_next_acct\n" ++
  "  la t0, bsg_off; ld t1, 0(t0); add s8, s6, t1      # storage_changes ptr\n" ++
  "  la t0, bsg_len; ld s9, 0(t0)                      # storage_changes len\n" ++
  "  mv a0, s8; mv a1, s9; la a2, bsg_slot_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lesub_next_acct\n" ++
  "  la t0, bsg_slot_count; ld s10, 0(t0)\n" ++
  "  li s6, 0                                          # slot i\n" ++
  ".Lesub_slot_loop:\n" ++
  "  beq s6, s10, .Lesub_next_acct\n" ++
  "  mv a0, s8; mv a1, s9; mv a2, s6; la a3, bsg_slot_off; la a4, bsg_slot_len\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  bnez a0, .Lesub_next_slot\n" ++
  "  la t0, bsg_slot_off; ld t1, 0(t0); add t2, s8, t1 # slot-change ptr\n" ++
  "  la t0, bsg_slot_len; ld t3, 0(t0)                 # slot-change len\n" ++
  "  la t0, bsg_slot_ptr; sd t2, 0(t0); la t0, bsg_slot_item_len; sd t3, 0(t0)\n" ++
  "  mv a0, t2; mv a1, t3; li a2, 1; la a3, bsg_changes_off; la a4, bsg_changes_len\n" ++
  "  jal ra, rlp_item_span                              # per-slot changes list\n" ++
  "  bnez a0, .Lesub_next_slot\n" ++
  "  la t0, bsg_slot_ptr; ld t2, 0(t0); la t0, bsg_changes_off; ld t1, 0(t0); add t2, t2, t1\n" ++
  "  la t0, bsg_changes_ptr; sd t2, 0(t0)\n" ++
  "  la t0, bsg_changes_len; ld t3, 0(t0)\n" ++
  "  mv a0, t2; mv a1, t3; la a2, bsg_change_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lesub_next_slot\n" ++
  "  la t0, bsg_change_count; ld t4, 0(t0); beqz t4, .Lesub_next_slot\n" ++
  "  addi t4, t4, -1                                  # final change only\n" ++
  "  la t0, bsg_changes_ptr; ld a0, 0(t0); la t0, bsg_changes_len; ld a1, 0(t0); mv a2, t4; la a3, bsg_change_off; la a4, bsg_change_len\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  bnez a0, .Lesub_next_slot\n" ++
  "  la t0, bsg_changes_ptr; ld t2, 0(t0); la t0, bsg_change_off; ld t1, 0(t0); add t2, t2, t1\n" ++
  "  la t0, bsg_change_len; ld t3, 0(t0)\n" ++
  "  la t0, bsg_change_ptr; sd t2, 0(t0); la t0, bsg_change_item_len; sd t3, 0(t0)\n" ++
  "  mv a0, t2; mv a1, t3; li a2, 0; la a3, bsg_idx_off; la a4, bsg_idx_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lesub_next_slot\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); li a2, 0; la a3, bsg_index\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lesub_next_slot\n" ++
  "  la t0, bsg_index; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lesub_next_slot                         # system writes do not spend tx state gas\n" ++
  "  bgeu t1, s2, .Lesub_next_slot\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); li a2, 1; la a3, bsg_value_off; la a4, bsg_value_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lesub_next_slot\n" ++
  "  la t0, bsg_value_len; ld t1, 0(t0); beqz t1, .Lesub_next_slot\n" ++
  "  ld t2, 0(s3);" ++ liAmsterdamStorageSetStateGas "t3" ++
  "  add t2, t2, t3; sd t2, 0(s3)\n" ++
  ".Lesub_next_slot:\n" ++
  "  addi s6, s6, 1; j .Lesub_slot_loop\n" ++
  ".Lesub_next_acct:\n" ++
  "  addi s5, s5, 1; j .Lesub_acct_loop\n" ++
  ".Lesub_ok:\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret\n" ++
  "eip8037_prior_state_used_exact:\n" ++
  "  # a0 = prior tx count (0-based current tx index), a1 = out ptr.\n" ++
  "  # Returns a0=0 when the execution-derived prior-state sum is exact, else 1.\n" ++
  "  sd zero, 0(a1)\n" ++
  "  beqz a0, .Lepse_ok\n" ++
  "  la t0, bsg_exact_state_ok; ld t0, 0(t0); beqz t0, .Lepse_fail\n" ++
  "  la t0, bvgr_runtime_count; ld t0, 0(t0); bltu t0, a0, .Lepse_fail\n" ++
  "  li t0, 16; bgtu a0, t0, .Lepse_fail\n" ++
  "  mv t0, a0                   # prior count\n" ++
  "  li t1, 0                    # i\n" ++
  "  li t2, 0                    # accumulated state gas\n" ++
  ".Lepse_loop:\n" ++
  "  beq t1, t0, .Lepse_store\n" ++
  "  slli t3, t1, 3\n" ++
  "  la t4, bvgr_tx_state_gas; add t4, t4, t3; ld t5, 0(t4)\n" ++
  "  add t6, t2, t5; bltu t6, t2, .Lepse_fail; mv t2, t6\n" ++
  "  la t4, bv_tx_status_arr; add t4, t4, t3; ld t5, 0(t4); beqz t5, .Lepse_next\n" ++
  "  la t4, bvgr_tx_exec_state_gas; add t4, t4, t3; ld t5, 0(t4)\n" ++
  "  add t6, t2, t5; bltu t6, t2, .Lepse_fail; mv t2, t6\n" ++
  ".Lepse_next:\n" ++
  "  addi t1, t1, 1; j .Lepse_loop\n" ++
  ".Lepse_store:\n" ++
  "  sd t2, 0(a1)\n" ++
  ".Lepse_ok:\n" ++
  "  li a0, 0; ret\n" ++
  ".Lepse_fail:\n" ++
  "  li a0, 1; ret\n" ++
  "eip8037_tx_gas_gate:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # exec_payload\n" ++
  "  mv s1, a1                   # BAL ptr\n" ++
  "  mv s2, a2                   # BAL len\n" ++
  "  mv s3, a3                   # gas_limit\n" ++
  "  li s4, 0                    # accumulated worst regular gas\n" ++
  "  la t0, bsg_min_block_gas; sd zero, 0(t0)\n" ++
  "  la t0, bsg_exact_state_ok; sd zero, 0(t0)\n" ++
  "  addi a0, s0, 504; jal ra, bgv_u32le\n" ++
  "  add s5, s0, a0              # tx list ptr\n" ++
  "  addi a0, s0, 508; jal ra, bgv_u32le\n" ++
  "  sub s6, a0, a0              # clear before bounds checks\n" ++
  "  add t0, s0, a0              # withdrawals ptr\n" ++
  "  sub s6, t0, s5              # tx list len\n" ++
  "  bltu t0, s5, .Letg_ok\n" ++
  "  beqz s6, .Letg_ok\n" ++
  "  mv a0, s5; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Letg_ok\n" ++
  "  srli s7, a0, 2              # tx_count = first offset / 4\n" ++
  "  beqz s7, .Letg_ok\n" ++
  "  li t0, 16; bgtu s7, t0, .Letg_ok\n" ++
  "  mv a0, s5; mv a1, s6; mv a2, s7; la a3, bvgr_tx_state_gas\n" ++
  "  li a4, 0; li a5, 0; li a6, 0      # pre-runtime gate has no BAL refund context\n" ++
  "  jal ra, block_verdict_tx_state_gas_array\n" ++
  "  bnez a0, .Letg_state_array_ready\n" ++
  "  la t0, bsg_exact_state_ok; li t1, 1; sd t1, 0(t0)\n" ++
  ".Letg_state_array_ready:\n" ++
  "  li s8, 0                    # tx index, 0-based\n" ++
  "  la t0, bsg_blob_gas_accum; sd zero, 0(t0)\n" ++
  ".Letg_tx_loop:\n" ++
  "  beq s8, s7, .Letg_ok\n" ++
  "  slli t0, s8, 2; add t1, s5, t0; mv a0, t1; jal ra, bgv_u32le\n" ++
  "  mv s9, a0                   # item_off\n" ++
  "  addi t0, s8, 1\n" ++
  "  beq t0, s7, .Letg_last_tx\n" ++
  "  slli t1, t0, 2; add t1, s5, t1; mv a0, t1; jal ra, bgv_u32le\n" ++
  "  j .Letg_have_next\n" ++
  ".Letg_last_tx:\n" ++
  "  mv a0, s6\n" ++
  ".Letg_have_next:\n" ++
  "  bltu a0, s9, .Letg_ok\n" ++
  "  sub s10, a0, s9             # tx len\n" ++
  "  add s9, s5, s9              # tx ptr\n" ++
  "  mv a0, s9; mv a1, s10; la a2, bsg_tx_type; la a3, bsg_tx_inner\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Letg_ok\n" ++
  "  la t0, bsg_tx_inner; ld t2, 0(t0)\n" ++
  "  bgtu t2, s10, .Letg_ok\n" ++
  "  add s9, s9, t2              # inner RLP ptr (typed txs skip type byte)\n" ++
  "  sub s10, s10, t2            # inner RLP len\n" ++
  "  la t0, bsg_tx_type; ld t1, 0(t0)\n" ++
  "  li t0, 1; beq t1, t0, .Letg_type_2930\n" ++
  "  li t0, 2; beq t1, t0, .Letg_type_1559\n" ++
  "  li t0, 3; beq t1, t0, .Letg_type_4844\n" ++
  "  li t0, 4; beq t1, t0, .Letg_type_7702\n" ++
  "  beqz t1, .Letg_type_legacy\n" ++
  "  j .Letg_ok\n" ++
  ".Letg_type_legacy:\n" ++
  "  li t0, 2; la t1, bsg_gas_field; sd t0, 0(t1)\n" ++
  "  li t0, 3; la t1, bsg_to_field; sd t0, 0(t1)\n" ++
  "  li t0, 4; la t1, bsg_value_field; sd t0, 0(t1)\n" ++
  "  li t0, 5; la t1, bsg_data_field; sd t0, 0(t1)\n" ++
  "  li t0, -1; la t1, bsg_access_field; sd t0, 0(t1); la t1, bsg_auth_field; sd t0, 0(t1)\n" ++
  "  j .Letg_have_fields\n" ++
  ".Letg_type_2930:\n" ++
  "  li t0, 3; la t1, bsg_gas_field; sd t0, 0(t1)\n" ++
  "  li t0, 4; la t1, bsg_to_field; sd t0, 0(t1)\n" ++
  "  li t0, 5; la t1, bsg_value_field; sd t0, 0(t1)\n" ++
  "  li t0, 6; la t1, bsg_data_field; sd t0, 0(t1)\n" ++
  "  li t0, 7; la t1, bsg_access_field; sd t0, 0(t1)\n" ++
  "  li t0, -1; la t1, bsg_auth_field; sd t0, 0(t1)\n" ++
  "  j .Letg_have_fields\n" ++
  ".Letg_type_1559:\n" ++
  ".Letg_type_4844:\n" ++
  "  li t0, 4; la t1, bsg_gas_field; sd t0, 0(t1)\n" ++
  "  li t0, 5; la t1, bsg_to_field; sd t0, 0(t1)\n" ++
  "  li t0, 6; la t1, bsg_value_field; sd t0, 0(t1)\n" ++
  "  li t0, 7; la t1, bsg_data_field; sd t0, 0(t1)\n" ++
  "  li t0, 8; la t1, bsg_access_field; sd t0, 0(t1)\n" ++
  "  li t0, -1; la t1, bsg_auth_field; sd t0, 0(t1)\n" ++
  "  j .Letg_have_fields\n" ++
  ".Letg_type_7702:\n" ++
  "  li t0, 4; la t1, bsg_gas_field; sd t0, 0(t1)\n" ++
  "  li t0, 5; la t1, bsg_to_field; sd t0, 0(t1)\n" ++
  "  li t0, 6; la t1, bsg_value_field; sd t0, 0(t1)\n" ++
  "  li t0, 7; la t1, bsg_data_field; sd t0, 0(t1)\n" ++
  "  li t0, 8; la t1, bsg_access_field; sd t0, 0(t1)\n" ++
  "  li t0, 9; la t1, bsg_auth_field; sd t0, 0(t1)\n" ++
  ".Letg_have_fields:\n" ++
  "  la t0, bsg_gas_field; ld a2, 0(t0); mv a0, s9; mv a1, s10; la a3, bsg_tx_gas\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Letg_ok\n" ++
  "  la t0, bsg_tx_gas; ld t1, 0(t0)\n" ++
  "  la t0, bsg_value_field; ld a2, 0(t0); mv a0, s9; mv a1, s10; la a3, bsg_value_off; la a4, bsg_value_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Letg_ok\n" ++
  "  la t0, bsg_data_field; ld a2, 0(t0); mv a0, s9; mv a1, s10; la a3, bsg_data_off; la a4, bsg_data_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Letg_ok\n" ++
  "  la t0, bsg_data_off; ld t1, 0(t0); add t1, s9, t1\n" ++
  "  la t0, bsg_data_ptr; sd t1, 0(t0)\n" ++
  "  la t0, bsg_to_field; ld a2, 0(t0); mv a0, s9; mv a1, s10; la a3, bsg_to_off; la a4, bsg_to_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Letg_ok\n" ++
  "  la t0, bsg_to_len; ld t1, 0(t0); bnez t1, .Letg_after_initcode_limit\n" ++
  "  # Amsterdam/EIP-7954 MAX_INIT_CODE_SIZE = 2 * MAX_CODE_SIZE = 65536.\n" ++
  "  la t0, bsg_data_len; ld t1, 0(t0); li t2, 65536; bgtu t1, t2, .Letg_validate_fail\n" ++
  ".Letg_after_initcode_limit:\n" ++
  "  la t0, bsg_access_addrs; sd zero, 0(t0)\n" ++
  "  la t0, bsg_access_slots; sd zero, 0(t0)\n" ++
  "  la t0, bsg_auth_count; sd zero, 0(t0)\n" ++
  "  la t0, bsg_access_field; ld t1, 0(t0); li t2, -1; beq t1, t2, .Letg_after_access\n" ++
  "  mv a0, s9; mv a1, s10; mv a2, t1; la a3, bsg_access_off; la a4, bsg_access_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Letg_ok\n" ++
  "  la t0, bsg_access_off; ld t1, 0(t0); add a0, s9, t1\n" ++
  "  la t0, bsg_access_len; ld a1, 0(t0)\n" ++
  "  la a2, bsg_access_addrs; la a3, bsg_access_slots\n" ++
  "  jal ra, access_list_count\n" ++
  "  bnez a0, .Letg_ok\n" ++
  ".Letg_after_access:\n" ++
  "  la t0, bsg_auth_field; ld t1, 0(t0); li t2, -1; beq t1, t2, .Letg_after_auth\n" ++
  "  mv a0, s9; mv a1, s10; mv a2, t1; la a3, bsg_auth_off; la a4, bsg_auth_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Letg_ok\n" ++
  "  la t0, bsg_auth_off; ld t1, 0(t0); add a0, s9, t1\n" ++
  "  la t0, bsg_auth_len; ld a1, 0(t0); la a2, bsg_auth_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Letg_ok\n" ++
  ".Letg_after_auth:\n" ++
  "  la t0, bsg_tx_type; ld t1, 0(t0); li t2, 3; bne t1, t2, .Letg_after_blob_precheck\n" ++
  "  mv a0, s9; mv a1, s10; la a2, tcbg_struct\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Letg_validate_fail\n" ++
  "  la t0, tcbg_struct; lwu t1, 168(t0); lwu t2, 172(t0)\n" ++
  "  add a0, s9, t1; mv a1, t2; la a2, bsg_blob_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Letg_validate_fail\n" ++
  "  la t0, bsg_blob_count; ld t1, 0(t0); beqz t1, .Letg_validate_fail\n" ++
  "  li t2, 6; bgtu t1, t2, .Letg_validate_fail\n" ++
  "  slli t1, t1, 17\n" ++
  "  la t0, bsg_blob_gas_accum; ld t2, 0(t0); add t2, t2, t1\n" ++
  "  li t3, 2752512             # Amsterdam MAX_BLOB_GAS_PER_BLOCK\n" ++
  "  bgtu t2, t3, .Letg_validate_fail\n" ++
  "  la t0, bsg_blob_gas_accum; sd t2, 0(t0)\n" ++
  "  addi a0, s0, 520; jal ra, bgv_u64le       # header excess_blob_gas (u64)\n" ++
  "  la a1, bsg_blob_price_be; jal ra, amsterdam_blob_gas_price_u256  # price (u256 BE)\n" ++
  "  bnez a0, .Letg_validate_fail              # u256 overflow (unreachable for valid blocks)\n" ++
  "  # EIP-8037: reject iff max_fee_per_blob_gas < blob_gas_price. Compared in u256:\n" ++
  "  # in the >328M excess regime both exceed u64, so the old u64 amsterdam_blob_gas_price\n" ++
  "  # overflowed and false-rejected valid blob txs (evm-asm-lcx60.1).\n" ++
  "  la a0, tcbg_blob_fee_be; la a1, bsg_blob_price_be; la a2, bsg_blob_lt_out\n" ++
  "  jal ra, u256_lt_be                        # *out = 1 iff max_fee < price\n" ++
  "  la t0, bsg_blob_lt_out; ld t0, 0(t0); bnez t0, .Letg_validate_fail\n" ++
  "  # EIP-4844 versioned-hash validity: every blob_versioned_hash must be 32\n" ++
  "  # bytes and start with the KZG version byte 0x01 (VERSIONED_HASH_VERSION_KZG,\n" ++
  "  # spec fork.py check_transaction). The inline precheck above validates blob\n" ++
  "  # count and gas only, so call K139 here to reject a bad version byte\n" ++
  "  # (status 6) or malformed item (status 5). s9/s10 are preserved by K139.\n" ++
  "  mv a0, s9; mv a1, s10; li a2, 6; la a3, bsg_blob_count\n" ++
  "  jal ra, tx_eip4844_validate_blob_hashes\n" ++
  "  bnez a0, .Letg_validate_fail\n" ++
  ".Letg_after_blob_precheck:\n" ++
  "  # p6ggi: EIP-4844 (type 3) and EIP-7702 (type 4) forbid contract creation:\n" ++
  "  # an empty 'to' raises TransactionTypeContractCreationError (fork.py:664-666).\n" ++
  "  # Type 4 additionally requires a non-empty authorization_list, else\n" ++
  "  # EmptyAuthorizationListError (fork.py:668-670). Both are InvalidBlock on the\n" ++
  "  # block-validation path, so a block carrying such a tx is rejected. to_len and\n" ++
  "  # auth_count here are the same reliably-parsed fields the gate already branches\n" ++
  "  # on (init-code limit, CREATE/auth state gas); a valid type-3/4 tx has a 20-byte\n" ++
  "  # 'to' and a valid type-4 tx has >=1 authorization, so neither is false-rejected.\n" ++
  "  la t0, bsg_tx_type; ld t1, 0(t0)\n" ++
  "  li t2, 4; beq t1, t2, .Letg_type47_auth_check\n" ++
  "  li t2, 3; beq t1, t2, .Letg_type34_create_check\n" ++
  "  j .Letg_after_type34_checks\n" ++
  ".Letg_type47_auth_check:\n" ++
  "  la t0, bsg_auth_count; ld t2, 0(t0); beqz t2, .Letg_validate_fail\n" ++
  ".Letg_type34_create_check:\n" ++
  "  la t0, bsg_to_len; ld t2, 0(t0); beqz t2, .Letg_validate_fail\n" ++
  ".Letg_after_type34_checks:\n" ++
  "  la t0, bsg_data_ptr; ld a0, 0(t0)\n" ++
  "  la t0, bsg_data_len; ld a1, 0(t0)\n" ++
  "  la t0, bsg_to_len; ld a2, 0(t0); seqz a2, a2\n" ++
  "  la t0, bsg_access_addrs; ld a3, 0(t0)\n" ++
  "  la t0, bsg_access_slots; ld a4, 0(t0)\n" ++
  "  la t0, bsg_auth_count; ld a5, 0(t0)\n" ++
  "  la a6, bsg_intrinsic_gas; la a7, bsg_floor_gas\n" ++
  "  jal ra, intrinsic_gas_amsterdam_counts\n" ++
  "  bnez a0, .Letg_ok\n" ++
  "  la t0, bsg_floor_gas; ld t1, 0(t0)\n" ++
  "  slli t2, s8, 3; la t3, bv_mtx_calldata; add t3, t3, t2; ld t4, 0(t3)\n" ++
  "  bgeu t4, t1, .Letg_floor_stored\n" ++
  "  sd t1, 0(t3)\n" ++
  ".Letg_floor_stored:\n" ++
  "  # EIP-8037 intrinsic.state gas: CREATE new-account reserve plus EIP-7702\n" ++
  "  # authorization reserve (calculate_intrinsic_cost). Computed once here and\n" ++
  "  # consumed by both the per-tx sufficiency test and the 2D block accounting.\n" ++
  "  li t6, 0\n" ++
  "  la t0, bsg_to_len; ld t2, 0(t0); bnez t2, .Letg_after_create_state\n" ++
  liAmsterdamNewAccountStateGas "t6" ++
  ".Letg_after_create_state:\n" ++
  "  la t0, bsg_auth_count; ld t2, 0(t0); beqz t2, .Letg_intrinsic_done\n" ++
  liAmsterdamAuthStateGas "t3" ++
  "  mul t2, t2, t3; add t6, t6, t2\n" ++
  ".Letg_intrinsic_done:\n" ++
  "  la t0, bsg_state_gas; sd t6, 0(t0)\n" ++
  "  la t0, bsg_intrinsic_gas; ld s11, 0(t0)\n" ++
  "  la t0, bsg_tx_gas; ld t1, 0(t0)\n" ++
  "  la t0, bsg_floor_gas; ld t6, 0(t0)\n" ++
  "  mv t0, s11; bgeu t0, t6, .Letg_required_have\n" ++
  "  mv t0, t6\n" ++
  ".Letg_required_have:\n" ++
  "  li t4, 16777216\n" ++
  "  # TX_MAX_GAS_LIMIT test (spec transactions.py:590) uses max(regular, floor),\n" ++
  "  # no state component.\n" ++
  "  bgtu t0, t4, .Letg_validate_fail\n" ++
  "  # Per-tx 'insufficient gas' test (spec transactions.py:587-588) uses\n" ++
  "  # max(intrinsic.regular + intrinsic.state, calldata_floor): fold the state\n" ++
  "  # component into the regular term before comparing against tx.gas.\n" ++
  "  la t4, bsg_state_gas; ld t4, 0(t4); add t4, s11, t4\n" ++
  "  bgeu t4, t6, .Letg_suff_have\n" ++
  "  mv t4, t6\n" ++
  ".Letg_suff_have:\n" ++
  "  bltu t1, t4, .Letg_validate_fail\n" ++
  "  la t5, bsg_min_block_gas; ld t2, 0(t5)\n" ++
  "  bltu s3, t2, .Letg_regular_reject\n" ++
  "  sub t3, s3, t2\n" ++
  "  # EIP-8037 permits the declared tx gas limit to exceed regular remaining\n" ++
  "  # when the 2D regular/state split still fits; only the required minimum\n" ++
  "  # gas is a safe pre-execution block availability rejection here.\n" ++
  "  bgtu t0, t3, .Letg_regular_reject\n" ++
  "  add t2, t2, t0; sd t2, 0(t5)\n" ++
  "  la t0, bsg_state_gas; ld t6, 0(t0)\n" ++
  "  li t2, 0\n" ++
  "  bltu t1, t6, .Letg_regular_have\n" ++
  "  sub t2, t1, t6              # tx.gas - intrinsic.state\n" ++
  "  li t3, 16777216\n" ++
  "  bleu t2, t3, .Letg_regular_have\n" ++
  "  mv t2, t3\n" ++
  ".Letg_regular_have:\n" ++
  "  bltu s3, s4, .Letg_regular_fail\n" ++
  "  sub t4, s3, s4\n" ++
  "  bgtu t2, t4, .Letg_regular_fail\n" ++
  "  add s4, s4, t2\n" ++
  "  bltu t1, s11, .Letg_ok\n" ++
  "  sub t2, t1, s11             # tx.gas - intrinsic.regular\n" ++
  "  la t0, bsg_worst_state; sd t2, 0(t0)\n" ++
  "  mv a0, s8; la a1, bsg_prior_state\n" ++
  "  jal ra, eip8037_prior_state_used_exact\n" ++
  "  beqz a0, .Letg_prior_state_have\n" ++
  "  addi a2, s8, 1\n" ++
  "  mv a0, s1; mv a1, s2; la a3, bsg_prior_state\n" ++
  "  jal ra, eip8037_state_used_before_tx\n" ++
  ".Letg_prior_state_have:\n" ++
  "  la t0, bsg_worst_state; ld t2, 0(t0)\n" ++
  "  la t0, bsg_prior_state; ld t3, 0(t0)\n" ++
  "  bltu s3, t3, .Letg_state_fail\n" ++
  "  sub t4, s3, t3\n" ++
  "  bgtu t2, t4, .Letg_state_fail\n" ++
  "  addi s8, s8, 1; j .Letg_tx_loop\n" ++
  ".Letg_regular_fail:\n" ++
  "  li t0, 1; beq s7, t0, .Letg_regular_reject\n" ++
  "  # Multi-tx worst-regular overflow is only an upper bound before runtime.\n" ++
  "  # Supported rows are checked exactly after gas-result arena materializes.\n" ++
  "  j .Letg_ok\n" ++
  ".Letg_regular_reject:\n" ++
  "  li a0, 1; j .Letg_ret\n" ++
  ".Letg_state_fail:\n" ++
  "  li a0, 2; j .Letg_ret\n" ++
  ".Letg_validate_fail:\n" ++
  "  li a0, 3; j .Letg_ret\n" ++
  ".Letg_ok:\n" ++
  "  li a0, 0\n" ++
  ".Letg_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

end EvmAsm.Codegen
