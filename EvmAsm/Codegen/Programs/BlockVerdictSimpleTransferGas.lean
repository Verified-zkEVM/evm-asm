/-
  EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferGas

  Simple-transfer gas publication helper for block_verdict.
-/

namespace EvmAsm.Codegen

/-! Compute Amsterdam intrinsic regular gas and calldata floor for the non-creation
    simple-transfer shortcut. This mirrors the runtime dispatcher setup path but
    reads calldata/access-list fields from the already extracted simple-transfer
    context, because the shortcut does not call the runtime dispatcher.

    a0 = simple_transfer_tx_context ptr
    returns a0=status, a1=intrinsic_regular, a2=calldata_floor, a3=intrinsic_state. -/
def simpleTransferIntrinsicGasFunction : String :=
  "simple_transfer_intrinsic_gas:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0\n" ++
  "  li s1, 23000                 # intrinsic regular = legacy base + Amsterdam recipient access delta\n" ++
  "  li s2, 21000                 # calldata floor base\n" ++
  "  ld s3, 56(s0)                # calldata ptr\n" ++
  "  ld s4, 64(s0)                # calldata len\n" ++
  ".Lstig_data_loop:\n" ++
  "  beqz s4, .Lstig_access_list\n" ++
  "  lbu t0, 0(s3)\n" ++
  "  beqz t0, .Lstig_zero_byte\n" ++
  "  addi s1, s1, 16\n" ++
  "  addi s2, s2, 64\n" ++
  "  j .Lstig_data_step\n" ++
  ".Lstig_zero_byte:\n" ++
  "  addi s1, s1, 4\n" ++
  "  addi s2, s2, 64\n" ++
  ".Lstig_data_step:\n" ++
  "  addi s3, s3, 1\n" ++
  "  addi s4, s4, -1\n" ++
  "  j .Lstig_data_loop\n" ++
  ".Lstig_access_list:\n" ++
  "  la t0, runtime_tx_access_list_address_count; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_access_list_storage_key_count; sd zero, 0(t0)\n" ++
  "  ld t0, 160(s0)\n" ++
  "  beqz t0, .Lstig_store_done\n" ++
  "  li a2, 7; li t1, 1; beq t0, t1, .Lstig_access_field\n" ++
  "  li a2, 8; li t1, 2; beq t0, t1, .Lstig_access_field\n" ++
  "  li t1, 3; beq t0, t1, .Lstig_access_field\n" ++
  "  li t1, 4; beq t0, t1, .Lstig_access_field\n" ++
  "  j .Lstig_store_done\n" ++
  ".Lstig_access_field:\n" ++
  "  ld a0, 176(s0); ld a1, 184(s0); la a3, bsg_access_off; la a4, bsg_access_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lstig_fail\n" ++
  "  ld t0, 176(s0); la t1, bsg_access_off; ld t1, 0(t1); add a0, t0, t1\n" ++
  "  la t1, bsg_access_len; ld a1, 0(t1)\n" ++
  "  la a2, runtime_tx_access_list_address_count; la a3, runtime_tx_access_list_storage_key_count\n" ++
  "  jal ra, access_list_count\n" ++
  "  bnez a0, .Lstig_fail\n" ++
  "  la t0, runtime_tx_access_list_address_count; ld t1, 0(t0)\n" ++
  ".Lstig_addr_loop:\n" ++
  "  beqz t1, .Lstig_slot_count\n" ++
  "  li t2, 4280\n" ++
  "  add s1, s1, t2\n" ++
  "  li t2, 1280\n" ++
  "  add s2, s2, t2\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lstig_addr_loop\n" ++
  ".Lstig_slot_count:\n" ++
  "  la t0, runtime_tx_access_list_storage_key_count; ld t1, 0(t0)\n" ++
  ".Lstig_slot_loop:\n" ++
  "  beqz t1, .Lstig_store_done\n" ++
  "  li t2, 5048\n" ++
  "  add s1, s1, t2\n" ++
  "  li t2, 2048\n" ++
  "  add s2, s2, t2\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lstig_slot_loop\n" ++
  ".Lstig_store_done:\n" ++
  "  ld t0, 160(s0); li t1, 4; bne t0, t1, .Lstig_auth_done\n" ++
  "  ld a0, 176(s0); ld a1, 184(s0); li a2, 9; la a3, bsg_access_off; la a4, bsg_access_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lstig_fail\n" ++
  "  ld t0, 176(s0); la t1, bsg_access_off; ld t1, 0(t1); add a0, t0, t1\n" ++
  "  la t1, bsg_access_len; ld a1, 0(t1); la a2, teer_auth_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lstig_fail\n" ++
  "  la t0, teer_auth_count; ld t1, 0(t0); li t2, 15816; mul t1, t1, t2; add s1, s1, t1\n" ++
  ".Lstig_auth_done:\n" ++
  "  la t0, runtime_tx_calldata_floor; sd s2, 0(t0)\n" ++
  "  la t0, runtime_tx_intrinsic_regular; sd s1, 0(t0)\n" ++
  "  sd s1, 48(sp); sd s2, 56(sp)\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); la a2, bv_runtime_intrinsic_state_gas\n" ++
  "  jal ra, tx_intrinsic_state_gas\n" ++
  "  bnez a0, .Lstig_fail\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0)\n" ++
  "  la t0, bv_bal_start; ld a2, 0(t0); la t0, bv_bal_len; ld a3, 0(t0)\n" ++
  "  la t0, teer_records_ptr; la t1, basr_records; sd t1, 0(t0)\n" ++
  "  la t0, bv_chain_id; ld a4, 0(t0); li a5, 1\n" ++
  "  jal ra, tx_eip7702_existing_authority_refund\n" ++
  "  la t0, bv_runtime_intrinsic_state_gas; ld t1, 0(t0)\n" ++
  "  bltu t1, a0, .Lstig_state_zero\n" ++
  "  sub t1, t1, a0; sd t1, 0(t0); j .Lstig_state_done\n" ++
  ".Lstig_state_zero:\n" ++
  "  li t1, 0; sd zero, 0(t0)\n" ++
  ".Lstig_state_done:\n" ++
  "  ld s1, 48(sp); ld s2, 56(sp)\n" ++
  "  li a0, 0; mv a1, s1; mv a2, s2; mv a3, t1\n" ++
  "  j .Lstig_ret\n" ++
  ".Lstig_fail:\n" ++
  "  li a0, 1; li a1, 0; li a2, 0; li a3, 0\n" ++
  ".Lstig_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"


end EvmAsm.Codegen
