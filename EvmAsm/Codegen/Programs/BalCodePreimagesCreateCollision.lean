/-
  EvmAsm.Codegen.Programs.BalCodePreimagesCreateCollision

  CREATE/CREATE2 collision helper assembly for BAL code-preimage checks.
-/

namespace EvmAsm.Codegen

/-- Assembly helpers used by `balCodePreimagesValidFunction` for CREATE and
CREATE2 collision BAL touch exceptions. Split out to keep the main Codegen
program module below the filesize guardrail. -/
def balCodePreimagesCreateCollisionFunctions : String :=
  "# Return 1 iff target equals CREATE(tx.to, 0) for a legacy tx and witness\n" ++
  "# bytecode contains a CREATE opcode. This recognizes CREATE-collision BAL\n" ++
  "# touches, which read account metadata but not the bytecode preimage.\n" ++
  "bal_txs_contains_create_collision_touch:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                  # 20-byte target address ptr\n" ++
  "  mv s1, a1                  # witness.codes ptr\n" ++
  "  mv s2, a2                  # witness.codes len\n" ++
  "  la t0, bv_exec_p; ld s3, 0(t0)\n" ++
  "  la t0, bv_tx_off; ld s4, 0(t0)\n" ++
  "  beqz s3, .Lbcc_no\n" ++
  "  add s5, s3, s4             # tx list ptr\n" ++
  "  addi a0, s3, 508; jal ra, bgv_u32le\n" ++
  "  bleu a0, s4, .Lbcc_no\n" ++
  "  sub s6, a0, s4             # tx list len\n" ++
  "  li t0, 4; bltu s6, t0, .Lbcc_no\n" ++
  "  mv a0, s5; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbcc_no\n" ++
  "  srli s7, a0, 2             # tx count\n" ++
  "  beqz s7, .Lbcc_no\n" ++
  "  li t0, 16; bgtu s7, t0, .Lbcc_no\n" ++
  "  slli t0, s7, 2; bgtu t0, s6, .Lbcc_no\n" ++
  "  li s8, 0                   # tx index\n" ++
  ".Lbcc_tx_loop:\n" ++
  "  beq s8, s7, .Lbcc_no\n" ++
  "  slli t0, s8, 2; add a0, s5, t0; jal ra, bgv_u32le\n" ++
  "  mv s9, a0                  # item offset\n" ++
  "  addi t0, s8, 1\n" ++
  "  beq t0, s7, .Lbcc_last_tx\n" ++
  "  slli t1, t0, 2; add a0, s5, t1; jal ra, bgv_u32le\n" ++
  "  j .Lbcc_have_next\n" ++
  ".Lbcc_last_tx:\n" ++
  "  mv a0, s6\n" ++
  ".Lbcc_have_next:\n" ++
  "  bltu a0, s9, .Lbcc_next_tx\n" ++
  "  sub t2, a0, s9             # tx len\n" ++
  "  add t3, s5, s9             # tx ptr\n" ++
  "  la t0, bsg_change_ptr; sd t3, 0(t0); la t0, bsg_change_item_len; sd t2, 0(t0)\n" ++
  "  mv a0, t3; mv a1, t2; la a2, bsg_tx_type; la a3, bsg_tx_inner\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Lbcc_next_tx\n" ++
  "  la t0, bsg_tx_type; ld t1, 0(t0); bnez t1, .Lbcc_next_tx\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0)\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbcc_next_tx\n" ++
  "  la t0, bsg_change_ptr; sd a0, 0(t0); la t0, bsg_change_item_len; sd a1, 0(t0)\n" ++
  "  # field 0 = nonce; save content bounds, decode only for top-level creation.\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbcc_next_tx\n" ++
  "  la t0, bsg_change_ptr; sd a0, 0(t0); sub t1, a0, a2; la t0, bsg_data_off; sd t1, 0(t0); la t0, bsg_data_len; sd a2, 0(t0)\n" ++
  "  # skip fields 1 and 2, then read field 3 = to.\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbcc_next_tx; la t0, bsg_change_ptr; sd a0, 0(t0)\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbcc_next_tx; la t0, bsg_change_ptr; sd a0, 0(t0)\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbcc_next_tx\n" ++
  "  sub t1, a0, a2; la t0, bsg_to_off; sd t1, 0(t0); la t0, bsg_to_len; sd a2, 0(t0)\n" ++
  "  la t0, bsg_to_len; ld t1, 0(t0); li t2, 20; beq t1, t2, .Lbcc_internal_create\n" ++
  "  bnez t1, .Lbcc_next_tx\n" ++
  "  # Top-level legacy contract creation: compare target with CREATE(sender, nonce).\n" ++
  "  la t0, bv_public_keys_ptr; ld t4, 0(t0)\n" ++
  "  la t0, bv_public_keys_len; ld t5, 0(t0)\n" ++
  "  beqz t4, .Lbcc_next_tx\n" ++
  "  li t0, 65; mul t1, s8, t0; add t2, t1, t0; bgtu t2, t5, .Lbcc_next_tx\n" ++
  "  add a0, t4, t1; addi a0, a0, 1       # skip SEC1 0x04 prefix\n" ++
  "  la a1, bbcv_sender_addr; jal ra, address_from_pubkey\n" ++
  "  la t0, bsg_data_off; ld a0, 0(t0); la t0, bsg_data_len; ld a1, 0(t0)\n" ++
  "  jal ra, rlp_content_to_u64_strict\n" ++
  "  bnez a1, .Lbcc_next_tx\n" ++
  "  la t0, bsg_tx_nonce; sd a0, 0(t0)\n" ++
  "  la a0, bbcv_sender_addr; la t0, bsg_tx_nonce; ld a1, 0(t0); la a2, bbcv_create_addr\n" ++
  "  jal ra, address_compute_create\n" ++
  "  la t0, bbcv_create_addr; li t1, 0\n" ++
  ".Lbcc_cmp_top_create_addr:\n" ++
  "  li t2, 20; beq t1, t2, .Lbcc_yes\n" ++
  "  add t3, t0, t1; lbu t3, 0(t3)\n" ++
  "  add t4, s0, t1; lbu t4, 0(t4)\n" ++
  "  bne t3, t4, .Lbcc_next_tx\n" ++
  "  addi t1, t1, 1; j .Lbcc_cmp_top_create_addr\n" ++
  ".Lbcc_internal_create:\n" ++
  "  jal ra, bal_codes_contains_create_opcode\n" ++
  "  beqz a0, .Lbcc_next_tx\n" ++
  "  la t0, bsg_to_off; ld t3, 0(t0)\n" ++
  "  la t0, bsr_kbuf            # RLP([to, 0]) buffer\n" ++
  "  li t1, 0xd6; sb t1, 0(t0)\n" ++
  "  li t1, 0x94; sb t1, 1(t0)\n" ++
  "  li t1, 0\n" ++
  ".Lbcc_copy_to:\n" ++
  "  li t2, 20; beq t1, t2, .Lbcc_hash_create\n" ++
  "  add t4, t3, t1; lbu t4, 0(t4)\n" ++
  "  add t5, t0, t1; sb t4, 2(t5)\n" ++
  "  addi t1, t1, 1; j .Lbcc_copy_to\n" ++
  ".Lbcc_hash_create:\n" ++
  "  li t1, 0x80; sb t1, 22(t0)\n" ++
  "  mv a0, t0; li a1, 23; la a2, bbcv_code_hash; jal ra, zkvm_keccak256\n" ++
  "  la t0, bbcv_code_hash; addi t0, t0, 12\n" ++
  "  li t1, 0\n" ++
  ".Lbcc_cmp_addr:\n" ++
  "  li t2, 20; beq t1, t2, .Lbcc_yes\n" ++
  "  add t3, t0, t1; lbu t3, 0(t3)\n" ++
  "  add t4, s0, t1; lbu t4, 0(t4)\n" ++
  "  bne t3, t4, .Lbcc_next_tx\n" ++
  "  addi t1, t1, 1; j .Lbcc_cmp_addr\n" ++
  ".Lbcc_next_tx:\n" ++
  "  addi s8, s8, 1; j .Lbcc_tx_loop\n" ++
  ".Lbcc_yes:\n" ++
  "  li a0, 1; j .Lbcc_ret\n" ++
  ".Lbcc_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbcc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff target equals CREATE2(CREATE(sender, nonce), salt, initcode)\n" ++
  "# for a top-level legacy contract-creation tx with simple literal initcode.\n" ++
  "bal_txs_contains_top_create2_collision_touch:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                  # 20-byte target address ptr\n" ++
  "  la t0, bv_exec_p; ld s1, 0(t0)\n" ++
  "  la t0, bv_tx_off; ld s2, 0(t0)\n" ++
  "  beqz s1, .Lbctc2_no\n" ++
  "  add s3, s1, s2             # tx list ptr\n" ++
  "  addi a0, s1, 508; jal ra, bgv_u32le\n" ++
  "  bleu a0, s2, .Lbctc2_no\n" ++
  "  sub s4, a0, s2             # tx list len\n" ++
  "  li t0, 4; bltu s4, t0, .Lbctc2_no\n" ++
  "  mv a0, s3; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbctc2_no\n" ++
  "  srli s5, a0, 2             # tx count\n" ++
  "  beqz s5, .Lbctc2_no\n" ++
  "  li t0, 16; bgtu s5, t0, .Lbctc2_no\n" ++
  "  slli t0, s5, 2; bgtu t0, s4, .Lbctc2_no\n" ++
  "  li s6, 0                   # tx index\n" ++
  ".Lbctc2_tx_loop:\n" ++
  "  beq s6, s5, .Lbctc2_no\n" ++
  "  slli t0, s6, 2; add a0, s3, t0; jal ra, bgv_u32le\n" ++
  "  mv s7, a0                  # item offset\n" ++
  "  addi t0, s6, 1\n" ++
  "  beq t0, s5, .Lbctc2_last_tx\n" ++
  "  slli t1, t0, 2; add a0, s3, t1; jal ra, bgv_u32le\n" ++
  "  j .Lbctc2_have_next\n" ++
  ".Lbctc2_last_tx:\n" ++
  "  mv a0, s4\n" ++
  ".Lbctc2_have_next:\n" ++
  "  bltu a0, s7, .Lbctc2_next_tx\n" ++
  "  sub s8, a0, s7             # tx len\n" ++
  "  add s9, s3, s7             # tx ptr\n" ++
  "  la t0, bsg_change_ptr; sd s9, 0(t0); la t0, bsg_change_item_len; sd s8, 0(t0)\n" ++
  "  mv a0, s9; mv a1, s8; la a2, bsg_tx_type; la a3, bsg_tx_inner\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Lbctc2_next_tx\n" ++
  "  la t0, bsg_tx_type; ld t1, 0(t0); bnez t1, .Lbctc2_next_tx\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0)\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbctc2_next_tx\n" ++
  "  la t0, bsg_change_ptr; sd a0, 0(t0); la t0, bsg_change_item_len; sd a1, 0(t0)\n" ++
  "  # field 0 = nonce; save content bounds for CREATE(sender, nonce).\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbctc2_next_tx\n" ++
  "  la t0, bsg_change_ptr; sd a0, 0(t0); sub t1, a0, a2; la t0, bsg_data_off; sd t1, 0(t0); la t0, bsg_data_len; sd a2, 0(t0)\n" ++
  "  # skip fields 1 and 2, then require field 3 = to to be empty.\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbctc2_next_tx; la t0, bsg_change_ptr; sd a0, 0(t0)\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbctc2_next_tx; la t0, bsg_change_ptr; sd a0, 0(t0)\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbctc2_next_tx\n" ++
  "  bnez a2, .Lbctc2_next_tx; la t0, bsg_change_ptr; sd a0, 0(t0)\n" ++
  "  la t0, bv_public_keys_ptr; ld t4, 0(t0)\n" ++
  "  la t0, bv_public_keys_len; ld t5, 0(t0)\n" ++
  "  beqz t4, .Lbctc2_next_tx\n" ++
  "  li t0, 65; mul t1, s6, t0; add t2, t1, t0; bgtu t2, t5, .Lbctc2_next_tx\n" ++
  "  add a0, t4, t1; addi a0, a0, 1\n" ++
  "  la a1, bbcv_sender_addr; jal ra, address_from_pubkey\n" ++
  "  la t0, bsg_data_off; ld a0, 0(t0); la t0, bsg_data_len; ld a1, 0(t0)\n" ++
  "  jal ra, rlp_content_to_u64_strict\n" ++
  "  bnez a1, .Lbctc2_next_tx\n" ++
  "  la t0, bsg_tx_nonce; sd a0, 0(t0)\n" ++
  "  la a0, bbcv_sender_addr; la t0, bsg_tx_nonce; ld a1, 0(t0); la a2, bbcv_create_addr\n" ++
  "  jal ra, address_compute_create\n" ++
  "  # skip field 4, then read field 5 = data/initcode.\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbctc2_next_tx; la t0, bsg_change_ptr; sd a0, 0(t0)\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbctc2_next_tx\n" ++
  "  sub s10, a0, a2; mv s11, a2\n" ++
  "  mv a0, s0; la a1, bbcv_create_addr; mv a2, s10; mv a3, s11\n" ++
  "  jal ra, bal_tx_initcode_contains_create2_target\n" ++
  "  bnez a0, .Lbctc2_yes\n" ++
  ".Lbctc2_next_tx:\n" ++
  "  addi s6, s6, 1; j .Lbctc2_tx_loop\n" ++
  ".Lbctc2_yes:\n" ++
  "  li a0, 1; j .Lbctc2_ret\n" ++
  ".Lbctc2_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbctc2_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret\n" ++
  "\n" ++
  "# Match simple top-level initcode CREATE2 patterns from create2collision_code.\n" ++
  "bal_tx_initcode_contains_create2_target:\n" ++
  "  addi sp, sp, -88\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                  # target address ptr\n" ++
  "  mv s1, a1                  # CREATE deployer ptr\n" ++
  "  mv s2, a2                  # tx initcode ptr\n" ++
  "  mv s3, a3                  # tx initcode len\n" ++
  "  li s4, 0                   # scan offset\n" ++
  ".Lbti_scan:\n" ++
  "  beq s4, s3, .Lbti_no\n" ++
  "  add t0, s2, s4; lbu t1, 0(t0); li t2, 0xf5; bne t1, t2, .Lbti_advance\n" ++
  "  li t2, 8; bltu s4, t2, .Lbti_advance\n" ++
  "  addi s5, t0, -8            # four PUSH1 args before CREATE2\n" ++
  "  lbu t1, 0(s5); li t2, 0x60; bne t1, t2, .Lbti_advance\n" ++
  "  lbu t1, 2(s5); bne t1, t2, .Lbti_advance\n" ++
  "  lbu t1, 4(s5); bne t1, t2, .Lbti_advance\n" ++
  "  lbu t1, 6(s5); bne t1, t2, .Lbti_advance\n" ++
  "  la s6, bbcv_create2_salt\n" ++
  "  sd zero, 0(s6); sd zero, 8(s6); sd zero, 16(s6); sw zero, 24(s6)\n" ++
  "  lbu t1, 1(s5); sb t1, 31(s6)  # salt byte\n" ++
  "  lbu s7, 3(s5)              # initcode size byte\n" ++
  "  beqz s7, .Lbti_empty_init\n" ++
  "  li t1, 33; bgtu s7, t1, .Lbti_advance\n" ++
  "  lbu t1, 0(s2); li t2, 0x60; bltu t1, t2, .Lbti_advance\n" ++
  "  li t2, 0x7f; bgtu t1, t2, .Lbti_advance\n" ++
  "  addi t1, t1, -0x5f         # PUSHn literal length\n" ++
  "  bne t1, s7, .Lbti_advance\n" ++
  "  addi t2, s7, 1; bgtu t2, s3, .Lbti_advance\n" ++
  "  addi s8, s2, 1; mv s9, s7\n" ++
  "  j .Lbti_compute\n" ++
  ".Lbti_empty_init:\n" ++
  "  mv s8, s2; li s9, 0\n" ++
  ".Lbti_compute:\n" ++
  "  mv a0, s1; mv a1, s6; mv a2, s8; mv a3, s9; la a4, bbcv_sender_addr\n" ++
  "  jal ra, address_compute_create2\n" ++
  "  la t0, bbcv_sender_addr; li t1, 0\n" ++
  ".Lbti_cmp:\n" ++
  "  li t2, 20; beq t1, t2, .Lbti_yes\n" ++
  "  add t3, t0, t1; lbu t3, 0(t3)\n" ++
  "  add t4, s0, t1; lbu t4, 0(t4)\n" ++
  "  bne t3, t4, .Lbti_advance\n" ++
  "  addi t1, t1, 1; j .Lbti_cmp\n" ++
  ".Lbti_advance:\n" ++
  "  addi s4, s4, 1; j .Lbti_scan\n" ++
  ".Lbti_yes:\n" ++
  "  li a0, 1; j .Lbti_ret\n" ++
  ".Lbti_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbti_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 88\n" ++
  "  ret\n"

end EvmAsm.Codegen
