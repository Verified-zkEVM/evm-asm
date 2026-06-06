/-
  EvmAsm.Codegen.Programs.BlockVerdictGasGate

  EIP-8037 transaction gas inclusion gate split out from BlockVerdict.lean
  to keep the verdict module under the file-size cap.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.IntrinsicGas

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## eip8037_tx_gas_gate -- conservative legacy transaction inclusion gate.
    a0 = exec_payload ptr   a1 = BAL ptr   a2 = BAL len   a3 = block_gas_limit
    a0 (output) = 0 ok/unsupported, 1 regular overflow, 2 state overflow,
                  3 validate_transaction gas failure.

    This mirrors the gas portion of Prague `validate_transaction` for legacy,
    EIP-2930, EIP-1559, EIP-4844, and EIP-7702 transactions that this gate can
    parse cheaply: `max(intrinsic_gas, calldata_floor_gas_cost) <= tx.gas`.
    The EIP-8037 `TX_MAX_GAS_LIMIT` cap is applied only to the worst-regular-gas
    bound below, not as a transaction-validity rule. Malformed tx lists, unknown
    tx types. The gate also mirrors the execution-spec pre-execution block-gas
    availability check when it can prove rejection from the intrinsic/floor gas
    lower bound of prior transactions. Single-transaction overflow is always
    invalid. Multi-transaction regular overflow is rejected only when the
    accumulated worst-regular gas before the overflowing transaction agrees with
    the block header's final `gas_used`; otherwise this conservative bound may
    be above execution-spec `block_gas_used` because prior transactions returned
    unused gas, so the gate fails open. -/
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
  "  ld t2, 0(s3); li t3, 97920; add t2, t2, t3; sd t2, 0(s3)\n" ++
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
  "  addi a0, s0, 420; jal ra, bgv_u64le       # header gas_used\n" ++
  "  la t0, bsg_header_gas_used; sd a0, 0(t0)\n" ++
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
  "  li s8, 0                    # tx index, 0-based\n" ++
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
  "  li t0, 5; la t1, bsg_data_field; sd t0, 0(t1)\n" ++
  "  li t0, -1; la t1, bsg_access_field; sd t0, 0(t1); la t1, bsg_auth_field; sd t0, 0(t1)\n" ++
  "  j .Letg_have_fields\n" ++
  ".Letg_type_2930:\n" ++
  "  li t0, 3; la t1, bsg_gas_field; sd t0, 0(t1)\n" ++
  "  li t0, 4; la t1, bsg_to_field; sd t0, 0(t1)\n" ++
  "  li t0, 6; la t1, bsg_data_field; sd t0, 0(t1)\n" ++
  "  li t0, 7; la t1, bsg_access_field; sd t0, 0(t1)\n" ++
  "  li t0, -1; la t1, bsg_auth_field; sd t0, 0(t1)\n" ++
  "  j .Letg_have_fields\n" ++
  ".Letg_type_1559:\n" ++
  ".Letg_type_4844:\n" ++
  "  li t0, 4; la t1, bsg_gas_field; sd t0, 0(t1)\n" ++
  "  li t0, 5; la t1, bsg_to_field; sd t0, 0(t1)\n" ++
  "  li t0, 7; la t1, bsg_data_field; sd t0, 0(t1)\n" ++
  "  li t0, 8; la t1, bsg_access_field; sd t0, 0(t1)\n" ++
  "  li t0, -1; la t1, bsg_auth_field; sd t0, 0(t1)\n" ++
  "  j .Letg_have_fields\n" ++
  ".Letg_type_7702:\n" ++
  "  li t0, 4; la t1, bsg_gas_field; sd t0, 0(t1)\n" ++
  "  li t0, 5; la t1, bsg_to_field; sd t0, 0(t1)\n" ++
  "  li t0, 7; la t1, bsg_data_field; sd t0, 0(t1)\n" ++
  "  li t0, 8; la t1, bsg_access_field; sd t0, 0(t1)\n" ++
  "  li t0, 9; la t1, bsg_auth_field; sd t0, 0(t1)\n" ++
  ".Letg_have_fields:\n" ++
  "  la t0, bsg_gas_field; ld a2, 0(t0); mv a0, s9; mv a1, s10; la a3, bsg_tx_gas\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
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
  "  la t0, bsg_data_ptr; ld a0, 0(t0)\n" ++
  "  la t0, bsg_data_len; ld a1, 0(t0)\n" ++
  "  la t0, bsg_to_len; ld a2, 0(t0); seqz a2, a2\n" ++
  "  la t0, bsg_access_addrs; ld a3, 0(t0)\n" ++
  "  la t0, bsg_access_slots; ld a4, 0(t0)\n" ++
  "  la t0, bsg_auth_count; ld a5, 0(t0)\n" ++
  "  la a6, bsg_intrinsic_gas; la a7, bsg_floor_gas\n" ++
  "  jal ra, intrinsic_gas_amsterdam_counts\n" ++
  "  bnez a0, .Letg_ok\n" ++
  "  la t0, bsg_tx_gas; ld t1, 0(t0)\n" ++
  "  la t0, bsg_intrinsic_gas; ld s11, 0(t0)\n" ++
  "  la t0, bsg_floor_gas; ld t6, 0(t0)\n" ++
  "  mv t0, s11; bgeu t0, t6, .Letg_required_have\n" ++
  "  mv t0, t6\n" ++
  ".Letg_required_have:\n" ++
  "  bltu t1, t0, .Letg_validate_fail\n" ++
  "  la t5, bsg_min_block_gas; ld t2, 0(t5)\n" ++
  "  bltu s3, t2, .Letg_regular_reject\n" ++
  "  sub t3, s3, t2\n" ++
  "  # EIP-8037 permits the declared tx gas limit to exceed regular remaining\n" ++
  "  # when the 2D regular/state split still fits; only the required minimum\n" ++
  "  # gas is a safe pre-execution block availability rejection here.\n" ++
  "  bgtu t0, t3, .Letg_regular_reject\n" ++
  "  add t2, t2, t0; sd t2, 0(t5)\n" ++
  "  # EIP-8037 state reservoir split is currently modeled only for creation.\n" ++
  "  # Non-creation txs have zero intrinsic state here.\n" ++
  "  li t6, 0\n" ++
  "  la t0, bsg_to_len; ld t2, 0(t0); bnez t2, .Letg_intrinsic_done\n" ++
  "  li t6, 183600\n" ++
  ".Letg_intrinsic_done:\n" ++
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
  "  addi a2, s8, 1\n" ++
  "  mv a0, s1; mv a1, s2; la a3, bsg_prior_state\n" ++
  "  jal ra, eip8037_state_used_before_tx\n" ++
  "  la t0, bsg_worst_state; ld t2, 0(t0)\n" ++
  "  la t0, bsg_prior_state; ld t3, 0(t0)\n" ++
  "  bltu s3, t3, .Letg_state_fail\n" ++
  "  sub t4, s3, t3\n" ++
  "  bgtu t2, t4, .Letg_state_fail\n" ++
  "  addi s8, s8, 1; j .Letg_tx_loop\n" ++
  ".Letg_regular_fail:\n" ++
  "  li t0, 1; beq s7, t0, .Letg_regular_reject\n" ++
  "  la t0, bsg_header_gas_used; ld t0, 0(t0)\n" ++
  "  beq s4, t0, .Letg_regular_reject\n" ++
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
