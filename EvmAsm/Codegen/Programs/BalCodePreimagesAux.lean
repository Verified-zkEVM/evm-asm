/-
  EvmAsm.Codegen.Programs.BalCodePreimagesAux

  Tail helpers for the BAL-scoped witness.codes preimage gate:
  bal_contains_internal_create_collision_touch and bal_codes_contains_create_opcode.
  Carved out of BalCodePreimages.lean to stay within the 1500-line file-size cap.
-/

namespace EvmAsm.Codegen

def balCodePreimagesAuxFunctions : String :=
  "\n" ++
  "# Return 1 iff target equals CREATE(creator, pre_nonce) for a BAL creator\n" ++
  "# row whose nonce increases and witness bytecode contains CREATE. This covers\n" ++
  "# internal CREATE collision metadata touches without requiring code preimage.\n" ++
  "bal_contains_internal_create_collision_touch:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                  # 20-byte target address ptr\n" ++
  "  mv s1, a1                  # witness.codes ptr\n" ++
  "  mv s2, a2                  # witness.codes len\n" ++
  "  mv s3, a3                  # BAL ptr\n" ++
  "  mv s4, a4                  # BAL len\n" ++
  "  jal ra, bal_codes_contains_create_opcode\n" ++
  "  beqz a0, .Lbicc_no\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbicc_no\n" ++
  "  mv s5, a0                 # BAL row cursor\n" ++
  "  mv s6, a1                 # BAL row end\n" ++
  ".Lbicc_row_loop:\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next\n" ++
  "  li t0, 2; beq a1, t0, .Lbicc_no\n" ++
  "  bnez a1, .Lbicc_no\n" ++
  "  mv s5, a0; sub s7, a0, a2 # row ptr\n" ++
  "  mv s8, a2                 # row len\n" ++
  "  mv a0, s7; mv a1, s8; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbicc_next_row\n" ++
  "  mv s10, a0                # row field cursor\n" ++
  "  mv s11, a1                # row field end\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbicc_next_row\n" ++
  "  li t2, 20; bne a2, t2, .Lbicc_next_row\n" ++
  "  sub s9, a0, a2            # creator address ptr\n" ++
  "  mv s10, a0; li s8, 3\n" ++
  ".Lbicc_skip_to_nonce_changes:\n" ++
  "  beqz s8, .Lbicc_nonce_changes_ready\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbicc_next_row\n" ++
  "  mv s10, a0; addi s8, s8, -1; j .Lbicc_skip_to_nonce_changes\n" ++
  ".Lbicc_nonce_changes_ready:\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbicc_next_row\n" ++
  "  sub s10, a0, a2           # nonce_changes ptr\n" ++
  "  mv s11, a2                # nonce_changes len\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbicc_next_row\n" ++
  "  mv s10, a0; mv s11, a1\n" ++
  "  # Use the first nonce change: [block_access_index, new_nonce].\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbicc_next_row\n" ++
  "  sub s10, a0, a2; mv s11, a2\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbicc_next_row\n" ++
  "  mv s10, a0; mv s11, a1\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbicc_next_row\n" ++
  "  mv s10, a0\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbicc_next_row\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lbicc_next_row\n" ++
  "  mv a1, a0; beqz a1, .Lbicc_next_row\n" ++
  "  addi a1, a1, -1           # pre_nonce = new_nonce - 1\n" ++
  "  mv a0, s9; la a2, bbcv_create_addr\n" ++
  "  jal ra, address_compute_create\n" ++
  "  la t0, bbcv_create_addr; li t1, 0\n" ++
  ".Lbicc_cmp_addr:\n" ++
  "  li t2, 20; beq t1, t2, .Lbicc_yes\n" ++
  "  add t3, t0, t1; lbu t3, 0(t3)\n" ++
  "  add t4, s0, t1; lbu t4, 0(t4)\n" ++
  "  bne t3, t4, .Lbicc_next_row\n" ++
  "  addi t1, t1, 1; j .Lbicc_cmp_addr\n" ++
  ".Lbicc_next_row:\n" ++
  "  j .Lbicc_row_loop\n" ++
  ".Lbicc_yes:\n" ++
  "  li a0, 1; j .Lbicc_ret\n" ++
  ".Lbicc_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbicc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff witness bytecode exposes a literal CREATE2 salt and a BAL\n" ++
  "# creator row with nonce/storage activity produces target for some witness\n" ++
  "# code element used as copied initcode.\n" ++
  "bal_contains_internal_create2_collision_touch:\n" ++
  "  addi sp, sp, -104\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                  # 20-byte target address ptr\n" ++
  "  mv s1, a1                  # witness.codes ptr\n" ++
  "  mv s2, a2                  # witness.codes len\n" ++
  "  mv s3, a3                  # BAL ptr\n" ++
  "  mv s4, a4                  # BAL len\n" ++
  "  mv a0, s1; mv a1, s2; la a2, bbcv_create2_salt\n" ++
  "  jal ra, bal_codes_find_create2_push4_salt\n" ++
  "  beqz a0, .Lbic2_no\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbic2_no\n" ++
  "  mv s5, a0                 # BAL row cursor\n" ++
  "  mv s6, a1                 # BAL row end\n" ++
  ".Lbic2_row_loop:\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next\n" ++
  "  li t0, 2; beq a1, t0, .Lbic2_no\n" ++
  "  bnez a1, .Lbic2_no\n" ++
  "  mv s5, a0; sub s7, a0, a2 # row ptr\n" ++
  "  mv s8, a2                 # row len\n" ++
  "  mv a0, s7; mv a1, s8; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbic2_next_row\n" ++
  "  mv s10, a0                # row field cursor\n" ++
  "  mv s11, a1                # row field end\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbic2_next_row\n" ++
  "  li t2, 20; bne a2, t2, .Lbic2_next_row\n" ++
  "  sub s9, a0, a2            # creator address ptr\n" ++
  "  mv s10, a0\n" ++
  "  # Check field 4 nonce_changes first.\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbic2_next_row\n" ++
  "  mv s10, a0\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbic2_check_storage\n" ++
  "  sub s7, a0, a2; mv s8, a2 # storage_changes ptr/len for fallback\n" ++
  "  mv s10, a0\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbic2_next_row\n" ++
  "  mv s10, a0\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbic2_check_storage\n" ++
  "  mv s10, a0\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbic2_check_storage\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbic2_check_storage\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  beqz a1, .Lbic2_try_creator\n" ++
  "  j .Lbic2_check_storage\n" ++
  ".Lbic2_check_storage:\n" ++
  "  mv a0, s7; mv a1, s8; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbic2_next_row\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  li t0, 2; beq a1, t0, .Lbic2_next_row\n" ++
  "  bnez a1, .Lbic2_next_row\n" ++
  ".Lbic2_try_creator:\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s9; la a4, bbcv_create2_salt\n" ++
  "  jal ra, bal_try_create2_initcodes\n" ++
  "  bnez a0, .Lbic2_yes\n" ++
  ".Lbic2_next_row:\n" ++
  "  j .Lbic2_row_loop\n" ++
  ".Lbic2_yes:\n" ++
  "  li a0, 1; j .Lbic2_ret\n" ++
  ".Lbic2_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbic2_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 104\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 after writing a 32-byte salt when a code element contains\n" ++
  "# PUSH4 <salt>; ...; CREATE2. The PUSH4 literal is zero-extended to BE32.\n" ++
  "bal_codes_find_create2_push4_salt:\n" ++
  "  addi sp, sp, -88\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                  # witness.codes ptr\n" ++
  "  mv s1, a1                  # witness.codes len\n" ++
  "  mv s2, a2                  # 32-byte salt output\n" ++
  "  beqz s1, .Lbc2s_no\n" ++
  "  mv a0, s0; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbc2s_no\n" ++
  "  srli s3, a0, 2             # code count\n" ++
  "  beqz s3, .Lbc2s_no\n" ++
  "  li s4, 0                   # code index\n" ++
  ".Lbc2s_elem_loop:\n" ++
  "  beq s4, s3, .Lbc2s_no\n" ++
  "  slli t0, s4, 2; add a0, s0, t0; jal ra, bgv_u32le\n" ++
  "  mv s5, a0                  # element offset\n" ++
  "  addi t0, s4, 1\n" ++
  "  beq t0, s3, .Lbc2s_last\n" ++
  "  slli t1, t0, 2; add a0, s0, t1; jal ra, bgv_u32le\n" ++
  "  j .Lbc2s_have_end\n" ++
  ".Lbc2s_last:\n" ++
  "  mv a0, s1\n" ++
  ".Lbc2s_have_end:\n" ++
  "  bltu a0, s5, .Lbc2s_next_elem\n" ++
  "  add s6, s0, s5; sub s7, a0, s5\n" ++
  "  li t0, 6; bltu s7, t0, .Lbc2s_next_elem\n" ++
  "  sub s8, s7, t0             # max PUSH4 offset with one following byte\n" ++
  "  li s9, 0                   # scan offset\n" ++
  ".Lbc2s_scan_loop:\n" ++
  "  bgtu s9, s8, .Lbc2s_next_elem\n" ++
  "  add t1, s6, s9\n" ++
  "  lbu t2, 0(t1); li t3, 0x63; bne t2, t3, .Lbc2s_advance_scan\n" ++
  "  addi t4, s9, 5             # search after PUSH4 immediate\n" ++
  ".Lbc2s_find_create2:\n" ++
  "  beq t4, s7, .Lbc2s_advance_scan\n" ++
  "  add t5, s6, t4; lbu t5, 0(t5); li t6, 0xf5; beq t5, t6, .Lbc2s_write_salt\n" ++
  "  addi t4, t4, 1; j .Lbc2s_find_create2\n" ++
  ".Lbc2s_write_salt:\n" ++
  "  sd zero, 0(s2); sd zero, 8(s2); sd zero, 16(s2); sw zero, 24(s2)\n" ++
  "  lbu t0, 1(t1); sb t0, 28(s2)\n" ++
  "  lbu t0, 2(t1); sb t0, 29(s2)\n" ++
  "  lbu t0, 3(t1); sb t0, 30(s2)\n" ++
  "  lbu t0, 4(t1); sb t0, 31(s2)\n" ++
  "  li a0, 1; j .Lbc2s_ret\n" ++
  ".Lbc2s_advance_scan:\n" ++
  "  addi s9, s9, 1; j .Lbc2s_scan_loop\n" ++
  ".Lbc2s_next_elem:\n" ++
  "  addi s4, s4, 1; j .Lbc2s_elem_loop\n" ++
  ".Lbc2s_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbc2s_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 88\n" ++
  "  ret\n" ++
  "\n" ++
  "# Try every witness code element as copied initcode for CREATE2.\n" ++
  "bal_try_create2_initcodes:\n" ++
  "  addi sp, sp, -88\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                  # target address ptr\n" ++
  "  mv s1, a1                  # witness.codes ptr\n" ++
  "  mv s2, a2                  # witness.codes len\n" ++
  "  mv s3, a3                  # creator address ptr\n" ++
  "  mv s4, a4                  # salt ptr\n" ++
  "  beqz s2, .Lbtci_no\n" ++
  "  mv a0, s1; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbtci_no\n" ++
  "  srli s5, a0, 2             # code count\n" ++
  "  beqz s5, .Lbtci_no\n" ++
  "  li s6, 0                   # code index\n" ++
  ".Lbtci_elem_loop:\n" ++
  "  beq s6, s5, .Lbtci_no\n" ++
  "  slli t0, s6, 2; add a0, s1, t0; jal ra, bgv_u32le\n" ++
  "  mv s7, a0                  # element offset\n" ++
  "  addi t0, s6, 1\n" ++
  "  beq t0, s5, .Lbtci_last\n" ++
  "  slli t1, t0, 2; add a0, s1, t1; jal ra, bgv_u32le\n" ++
  "  j .Lbtci_have_end\n" ++
  ".Lbtci_last:\n" ++
  "  mv a0, s2\n" ++
  ".Lbtci_have_end:\n" ++
  "  bltu a0, s7, .Lbtci_next_elem\n" ++
  "  add s8, s1, s7; sub s9, a0, s7\n" ++
  "  mv a0, s3; mv a1, s4; mv a2, s8; mv a3, s9; la a4, bbcv_create_addr\n" ++
  "  jal ra, address_compute_create2\n" ++
  "  la t0, bbcv_create_addr; li t1, 0\n" ++
  ".Lbtci_cmp_addr:\n" ++
  "  li t2, 20; beq t1, t2, .Lbtci_yes\n" ++
  "  add t3, t0, t1; lbu t3, 0(t3)\n" ++
  "  add t4, s0, t1; lbu t4, 0(t4)\n" ++
  "  bne t3, t4, .Lbtci_next_elem\n" ++
  "  addi t1, t1, 1; j .Lbtci_cmp_addr\n" ++
  ".Lbtci_next_elem:\n" ++
  "  addi s6, s6, 1; j .Lbtci_elem_loop\n" ++
  ".Lbtci_yes:\n" ++
  "  li a0, 1; j .Lbtci_ret\n" ++
  ".Lbtci_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbtci_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 88\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff any witness code byte is CREATE (0xf0).\n" ++
  "bal_codes_contains_create_opcode:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra, 0(sp); sd s3, 8(sp); sd s4, 16(sp); sd s5, 24(sp)\n" ++
  "  sd s6, 32(sp); sd s7, 40(sp)\n" ++
  "  beqz s2, .Lbcco_no\n" ++
  "  mv a0, s1; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbcco_no\n" ++
  "  srli s3, a0, 2             # code count\n" ++
  "  beqz s3, .Lbcco_no\n" ++
  "  li s4, 0                   # code index\n" ++
  ".Lbcco_elem_loop:\n" ++
  "  beq s4, s3, .Lbcco_no\n" ++
  "  slli t3, s4, 2; add a0, s1, t3; jal ra, bgv_u32le\n" ++
  "  mv s5, a0                  # element offset\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lbcco_last\n" ++
  "  slli t5, t3, 2; add a0, s1, t5; jal ra, bgv_u32le\n" ++
  "  j .Lbcco_have_end\n" ++
  ".Lbcco_last:\n" ++
  "  mv a0, s2\n" ++
  ".Lbcco_have_end:\n" ++
  "  bltu a0, s5, .Lbcco_next_elem\n" ++
  "  add s6, s1, s5; sub s7, a0, s5\n" ++
  ".Lbcco_scan:\n" ++
  "  beqz s7, .Lbcco_next_elem\n" ++
  "  lbu a0, 0(s6); li t3, 0xf0; beq a0, t3, .Lbcco_yes\n" ++
  "  addi s6, s6, 1; addi s7, s7, -1; j .Lbcco_scan\n" ++
  ".Lbcco_next_elem:\n" ++
  "  addi s4, s4, 1; j .Lbcco_elem_loop\n" ++
  ".Lbcco_yes:\n" ++
  "  li a0, 1; j .Lbcco_ret\n" ++
  ".Lbcco_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbcco_ret:\n" ++
  "  ld ra, 0(sp); ld s3, 8(sp); ld s4, 16(sp); ld s5, 24(sp)\n" ++
  "  ld s6, 32(sp); ld s7, 40(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

end EvmAsm.Codegen
