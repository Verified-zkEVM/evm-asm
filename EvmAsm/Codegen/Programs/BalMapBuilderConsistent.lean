/-
  EvmAsm.Codegen.Programs.BalMapBuilderConsistent

  Attribution-preserving BAL check for the account-write map.  The map is the
  execution source of the builder rows; the builder rows retain the
  (address, block_access_index, value) key that the final account map does not.
  This check is deliberately alongside the raw execution-effect comparators:
  it compares both directions against the surviving balance/nonce/code builder
  rows and therefore cannot be replaced by a final-state or digest check.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.BlockAccessListBuilder

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! `bal_map_builder_has_row` searches the builder stream selected by `a3`:
    1 = balance (64-byte rows), 2 = nonce (40-byte rows), 3 = code (64-byte
    rows).  The caller supplies the canonical BE20 address, BAI, and value
    pointer/length. -/
def balMapBuilderHasRowFunction : String :=
  "bal_map_builder_has_row:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1; bne s4, t0, .Lbamh_nonce; li t0, 32; bne s3, t0, .Lbamh_miss\n" ++
  "  la t0, bal_builder_balance_count; ld s4, 0(t0); la s5, bal_builder_balance_changes; li t0, 0\n" ++
  ".Lbamh_bal_loop:\n" ++
  "  bgeu t0, s4, .Lbamh_miss\n" ++
  "  slli t1, t0, 6; add t2, s5, t1; li t3, 0\n" ++
  ".Lbamh_bal_addr:\n" ++
  "  li t4, 20; beq t3, t4, .Lbamh_bal_bai; add t4, t2, t3; add t5, s0, t3; lbu t6, 0(t4); lbu a4, 0(t5); bne t6, a4, .Lbamh_bal_next; addi t3, t3, 1; j .Lbamh_bal_addr\n" ++
  ".Lbamh_bal_bai:\n" ++
  "  ld t1, 24(t2); bne t1, s1, .Lbamh_bal_next\n" ++
  "  ld t1, 32(t2); ld t3, 0(s2); bne t1, t3, .Lbamh_bal_next; ld t1, 40(t2); ld t3, 8(s2); bne t1, t3, .Lbamh_bal_next; ld t1, 48(t2); ld t3, 16(s2); bne t1, t3, .Lbamh_bal_next; ld t1, 56(t2); ld t3, 24(s2); bne t1, t3, .Lbamh_bal_next; li a0, 0; j .Lbamh_ret\n" ++
  ".Lbamh_bal_next:\n" ++
  "  addi t0, t0, 1; j .Lbamh_bal_loop\n" ++
  ".Lbamh_nonce:\n" ++
  "  li t0, 2; bne s4, t0, .Lbamh_code; li t0, 8; bne s3, t0, .Lbamh_miss\n" ++
  "  la t0, bal_builder_nonce_count; ld s4, 0(t0); la s5, bal_builder_nonce_changes; li t0, 0\n" ++
  ".Lbamh_non_loop:\n" ++
  "  bgeu t0, s4, .Lbamh_miss\n" ++
  "  slli t1, t0, 5; slli t3, t0, 3; add t1, t1, t3; add t2, s5, t1; li t3, 0\n" ++
  ".Lbamh_non_addr:\n" ++
  "  li t4, 20; beq t3, t4, .Lbamh_non_bai; add t4, t2, t3; add t5, s0, t3; lbu t6, 0(t4); lbu a4, 0(t5); bne t6, a4, .Lbamh_non_next; addi t3, t3, 1; j .Lbamh_non_addr\n" ++
  ".Lbamh_non_bai:\n" ++
  "  ld t1, 24(t2); bne t1, s1, .Lbamh_non_next; ld t1, 32(t2); ld t3, 0(s2); bne t1, t3, .Lbamh_non_next; li a0, 0; j .Lbamh_ret\n" ++
  ".Lbamh_non_next:\n" ++
  "  addi t0, t0, 1; j .Lbamh_non_loop\n" ++
  ".Lbamh_code:\n" ++
  "  la t0, bal_builder_code_count; ld s4, 0(t0); la s5, bal_builder_code_changes; li t0, 0\n" ++
  ".Lbamh_code_loop:\n" ++
  "  bgeu t0, s4, .Lbamh_miss; slli t1, t0, 6; add t2, s5, t1; li t3, 0\n" ++
  ".Lbamh_code_addr:\n" ++
  "  li t4, 20; beq t3, t4, .Lbamh_code_bai; add t4, t2, t3; add t5, s0, t3; lbu t6, 0(t4); lbu a4, 0(t5); bne t6, a4, .Lbamh_code_next; addi t3, t3, 1; j .Lbamh_code_addr\n" ++
  ".Lbamh_code_bai:\n" ++
  "  ld t1, 24(t2); bne t1, s1, .Lbamh_code_next; ld t1, 40(t2); bne t1, s3, .Lbamh_code_next; ld t1, 32(t2); mv t3, s2; li t4, 0\n" ++
  ".Lbamh_code_bytes:\n" ++
  "  beq t4, s3, .Lbamh_hit; add t5, t1, t4; add t6, t3, t4; lbu a4, 0(t5); lbu a5, 0(t6); bne a4, a5, .Lbamh_code_next; addi t4, t4, 1; j .Lbamh_code_bytes\n" ++
  ".Lbamh_code_next:\n" ++
  "  addi t0, t0, 1; j .Lbamh_code_loop\n" ++
  ".Lbamh_hit:\n  li a0, 0; j .Lbamh_ret\n" ++
  ".Lbamh_miss:\n  li a0, 1\n" ++
  ".Lbamh_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); addi sp, sp, 64; ret\n"

/-! Parse one AccountChanges item and check every tuple in one selected field
    against the builder.  Empty fields are accepted; malformed RLP is rejected. -/
def balMapCheckAccountFieldFunction : String :=
  "bal_map_check_account_field:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init; bnez a2, .Lbmacf_parse\n" ++
  "  sd a0, 40(sp); sd a1, 48(sp)\n" ++
  "  ld a0, 40(sp); ld a1, 48(sp); jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; sd a0, 40(sp)\n" ++
  "  ld a0, 40(sp); ld a1, 48(sp); jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; sd a0, 40(sp)\n" ++
  "  ld a0, 40(sp); ld a1, 48(sp); jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; sd a0, 40(sp)\n" ++
  "  ld a0, 40(sp); ld a1, 48(sp); jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; sd a0, 40(sp); mv t0, a0; sub t0, t0, a2; mv t1, a2\n" ++
  "  li t2, 1; beq s3, t2, .Lbmacf_field\n" ++
  "  ld a0, 40(sp); ld a1, 48(sp); jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; sd a0, 40(sp); mv t0, a0; sub t0, t0, a2; mv t1, a2\n" ++
  "  li t2, 2; beq s3, t2, .Lbmacf_field\n" ++
  "  ld a0, 40(sp); ld a1, 48(sp); jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; sd a0, 40(sp); mv t0, a0; sub t0, t0, a2; mv t1, a2\n" ++
  ".Lbmacf_field:\n" ++
  "  mv a0, t0; mv a1, t1; jal ra, rlp_walk_init; bnez a2, .Lbmacf_parse; mv s0, a0; mv s1, a1\n" ++
  ".Lbmacf_loop:\n" ++
  "  beq s0, s1, .Lbmacf_ok; mv a0, s0; mv a1, s1; jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; mv s0, a0; sub t0, a0, a2; mv t1, a2; sd s0, 40(sp); sd s1, 48(sp)\n" ++
  "  mv a0, t0; mv a1, t1; jal ra, rlp_walk_init; bnez a2, .Lbmacf_parse; mv s0, a0; mv s1, a1; sd s0, 56(sp); sd s1, 64(sp)\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; mv s0, a0; sub t0, a0, a2; mv t1, a2; mv a0, t0; mv a1, t1; jal ra, rlp_content_to_u64; bnez a1, .Lbmacf_parse; sd a0, 72(sp)\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; mv s0, a0; sub t0, a0, a2; mv t1, a2\n" ++
  "  li t2, 3; beq s3, t2, .Lbmacf_code\n" ++
  "  li t2, 1; bne s3, t2, .Lbmacf_nonce; mv a0, t0; mv a1, t1; la a2, bame_value; jal ra, rlp_content_to_u256_be; bnez a0, .Lbmacf_parse; mv a0, s2; ld a1, 72(sp); la a2, bame_value; li a3, 32; li a4, 1; jal ra, bal_map_builder_has_row; bnez a0, .Lbmacf_bad\n" ++
  "  j .Lbmacf_next_tuple\n" ++
  ".Lbmacf_nonce:\n" ++
  "  mv a0, t0; mv a1, t1; jal ra, rlp_content_to_u64; bnez a1, .Lbmacf_parse; la t2, bame_nonce; sd a0, 0(t2); mv a0, s2; ld a1, 72(sp); mv a2, t2; li a3, 8; li a4, 2; jal ra, bal_map_builder_has_row; bnez a0, .Lbmacf_bad\n" ++
  "  j .Lbmacf_next_tuple\n" ++
  ".Lbmacf_code:\n" ++
  "  mv a0, s2; ld a1, 72(sp); mv a2, t0; mv a3, t1; li a4, 3; jal ra, bal_map_builder_has_row; bnez a0, .Lbmacf_bad\n" ++
  ".Lbmacf_next_tuple:\n" ++
  "  ld s0, 40(sp); ld s1, 48(sp); j .Lbmacf_loop\n" ++
  ".Lbmacf_bad:\n  li a0, 1; j .Lbmacf_ret\n" ++
  ".Lbmacf_ok:\n  li a0, 0; j .Lbmacf_ret\n" ++
  ".Lbmacf_parse:\n  li a0, 2\n" ++
  ".Lbmacf_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); addi sp, sp, 80; ret\n"

/-! Search the supplied BAL for one exact builder row. -/
def balMapFindSuppliedFunction : String :=
  "bal_map_find_supplied:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; mv s6, a6\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_init; bnez a2, .Lbmfs_parse\n" ++
  "  sd a0, 64(sp); sd a1, 72(sp)\n" ++
  ".Lbmfs_loop:\n" ++
  "  ld t0, 64(sp); ld t1, 72(sp); beq t0, t1, .Lbmfs_miss; mv a0, t0; mv a1, t1; jal ra, rlp_walk_next; bnez a1, .Lbmfs_parse; sd a0, 64(sp); sub t2, a0, a2; mv t3, a2\n" ++
  "  mv a0, t2; mv a1, t3; mv a2, s0; mv a3, s1; mv a4, s2; mv a5, s3; mv a6, s4; jal ra, bal_map_account_matches; beqz a0, .Lbmfs_hit; li t4, 2; beq a0, t4, .Lbmfs_parse; j .Lbmfs_loop\n" ++
  ".Lbmfs_hit:\n  li a0, 0; j .Lbmfs_ret\n" ++
  ".Lbmfs_miss:\n  li a0, 1; j .Lbmfs_ret\n" ++
  ".Lbmfs_parse:\n  li a0, 2\n" ++
  ".Lbmfs_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); addi sp, sp, 96; ret\n"

/-! Account matcher used by the builder→supplied direction. -/
def balMapAccountMatchesFunction : String :=
  "bal_map_account_matches:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; mv s6, a6\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init; bnez a2, .Lbmam_parse; sd a0, 64(sp); sd a1, 72(sp)\n" ++
  "  ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; li t0, 20; bne a2, t0, .Lbmam_miss; sub t0, a0, a2; li t1, 0\n" ++
  ".Lbmam_addr:\n  li t6, 20; beq t1, t6, .Lbmam_addr_done; add t2, t0, t1; add t3, s2, t1; lbu t4, 0(t2); lbu t5, 0(t3); bne t4, t5, .Lbmam_miss; addi t1, t1, 1; j .Lbmam_addr\n" ++
  ".Lbmam_addr_done:\n" ++
  "  sd a0, 64(sp); ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; sd a0, 64(sp); ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; sd a0, 64(sp); ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; sd a0, 64(sp); mv t0, a0; sub t0, t0, a2; mv t1, a2\n" ++
  "  li t2, 1; beq s6, t2, .Lbmam_field\n" ++
  "  ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; sd a0, 64(sp); mv t0, a0; sub t0, t0, a2; mv t1, a2; li t2, 2; beq s6, t2, .Lbmam_field\n" ++
  "  ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; sd a0, 64(sp); mv t0, a0; sub t0, t0, a2; mv t1, a2\n" ++
  ".Lbmam_field:\n" ++
  "  mv a0, t0; mv a1, t1; jal ra, rlp_walk_init; bnez a2, .Lbmam_parse; mv s0, a0; mv s1, a1\n" ++
  ".Lbmam_loop:\n" ++
  "  beq s0, s1, .Lbmam_miss; mv a0, s0; mv a1, s1; jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; mv s0, a0; sub t0, a0, a2; mv t1, a2; sd s0, 64(sp); sd s1, 72(sp); mv a0, t0; mv a1, t1; jal ra, rlp_walk_init; bnez a2, .Lbmam_parse; mv s0, a0; mv s1, a1; sd s0, 80(sp); sd s1, 88(sp)\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; mv s0, a0; sub t0, a0, a2; mv t1, a2; mv a0, t0; mv a1, t1; jal ra, rlp_content_to_u64; bnez a1, .Lbmam_parse; bne a0, s3, .Lbmam_next_tuple\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; mv s0, a0; sub t0, a0, a2; mv t1, a2; li t2, 1; beq s6, t2, .Lbmam_balance; li t2, 2; beq s6, t2, .Lbmam_nonce\n" ++
  "  bne t1, s5, .Lbmam_next_tuple; li t2, 0\n" ++
  ".Lbmam_code_cmp:\n  beq t2, s5, .Lbmam_hit; add t3, t0, t2; add t4, s4, t2; lbu t5, 0(t3); lbu t6, 0(t4); bne t5, t6, .Lbmam_next_tuple; addi t2, t2, 1; j .Lbmam_code_cmp\n" ++
  ".Lbmam_balance:\n  mv a0, t0; mv a1, t1; la a2, bame_value; jal ra, rlp_content_to_u256_be; bnez a0, .Lbmam_parse; la t6, bame_value; ld t2, 0(t6); ld t3, 0(s4); bne t2, t3, .Lbmam_next_tuple; ld t2, 8(t6); ld t3, 8(s4); bne t2, t3, .Lbmam_next_tuple; ld t2, 16(t6); ld t3, 16(s4); bne t2, t3, .Lbmam_next_tuple; ld t2, 24(t6); ld t3, 24(s4); bne t2, t3, .Lbmam_next_tuple; j .Lbmam_hit\n" ++
  ".Lbmam_nonce:\n  mv a0, t0; mv a1, t1; jal ra, rlp_content_to_u64; bnez a1, .Lbmam_parse; ld t2, 0(s4); beq a0, t2, .Lbmam_hit\n" ++
  ".Lbmam_next_tuple:\n  ld s0, 64(sp); ld s1, 72(sp); j .Lbmam_loop\n" ++
  ".Lbmam_hit:\n  li a0, 0; j .Lbmam_ret\n" ++
  ".Lbmam_miss:\n  li a0, 1; j .Lbmam_ret\n" ++
  ".Lbmam_parse:\n  li a0, 2\n" ++
  ".Lbmam_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); addi sp, sp, 112; ret\n"

/-! Map-side value check.  The block map is authoritative for final values, but
    it has no BAI field.  The builder remains the attribution source; this
    routine only checks that each surviving builder row carries the map value
    for the same address and component. -/
def balMapAccountWriteMatchesFunction : String :=
  "bal_map_account_write_matches:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; la t0, account_writes_count; ld s4, 0(t0); li t0, 0; li t1, 0xa28a0000\n" ++
  ".Lbamw_scan:\n  bgeu t0, s4, .Lbamw_miss; slli t2, t0, 7; add t3, t1, t2; li t4, 20; mv t5, t3; mv t6, s0\n" ++
  ".Lbamw_addr:\n  beqz t4, .Lbamw_hit; lbu a4, 0(t5); lbu a5, 0(t6); bne a4, a5, .Lbamw_next; addi t5, t5, 1; addi t6, t6, 1; addi t4, t4, -1; j .Lbamw_addr\n" ++
  ".Lbamw_next:\n  addi t0, t0, 1; j .Lbamw_scan\n" ++
  ".Lbamw_hit:\n  li t2, 1; beq s1, t2, .Lbamw_balance; li t2, 2; beq s1, t2, .Lbamw_nonce; li t2, 3; bne s1, t2, .Lbamw_miss; j .Lbamw_code\n" ++
  ".Lbamw_balance:\n  li t2, 1; ld t4, 112(t3); and t4, t4, t2; beqz t4, .Lbamw_miss; li t2, 32; bne s3, t2, .Lbamw_miss; ld t4, 32(t3); ld t5, 0(s2); bne t4, t5, .Lbamw_miss; ld t4, 40(t3); ld t5, 8(s2); bne t4, t5, .Lbamw_miss; ld t4, 48(t3); ld t5, 16(s2); bne t4, t5, .Lbamw_miss; ld t4, 56(t3); ld t5, 24(s2); bne t4, t5, .Lbamw_miss; j .Lbamw_ok\n" ++
  ".Lbamw_nonce:\n  li t2, 2; ld t4, 112(t3); and t4, t4, t2; beqz t4, .Lbamw_miss; li t2, 8; bne s3, t2, .Lbamw_miss; ld t4, 64(t3); ld t5, 0(s2); bne t4, t5, .Lbamw_miss; j .Lbamw_ok\n" ++
  ".Lbamw_code:\n  li t2, 4; ld t4, 112(t3); and t4, t4, t2; beqz t4, .Lbamw_miss; ld t4, 88(t3); bne t4, s3, .Lbamw_miss; ld t4, 80(t3); li t5, 0\n" ++
  ".Lbamw_code_bytes:\n  beq t5, s3, .Lbamw_ok; add t6, t4, t5; add a4, s2, t5; lbu a5, 0(t6); lbu a6, 0(a4); bne a5, a6, .Lbamw_miss; addi t5, t5, 1; j .Lbamw_code_bytes\n" ++
  ".Lbamw_ok:\n  li a0, 0; j .Lbamw_ret\n" ++
  ".Lbamw_miss:\n  li a0, 1\n" ++
  ".Lbamw_ret:\n  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); addi sp, sp, 64; ret\n"

/-! Top-level bidirectional check.  First every surviving builder row must be
    present in the supplied BAL; then every supplied balance/nonce/code tuple
    must be present in the builder stream. -/
def balMapBuilderConsistentFunction : String :=
  "bal_map_builder_consistent:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0; mv s1, a1; la t0, bal_builder_balance_changes; mv s3, t0; la t0, bal_builder_balance_count; ld s2, 0(t0); li t0, 0; sd t0, 72(sp)\n" ++
  ".Lbmb_bal:\n  ld t0, 72(sp); bgeu t0, s2, .Lbmb_nonce; slli t1, t0, 6; add t2, s3, t1; mv a0, t2; li a1, 1; addi a2, t2, 32; li a3, 32; jal ra, bal_map_account_write_matches; bnez a0, .Lbmb_fail; ld t0, 72(sp); slli t1, t0, 6; add t2, s3, t1; ld a1, 24(t2); addi a2, t2, 32; mv a0, t2; li a3, 32; li a4, 1; mv a5, s0; mv a6, s1; jal ra, bal_map_find_supplied; bnez a0, .Lbmb_fail; ld t0, 72(sp); addi t0, t0, 1; sd t0, 72(sp); j .Lbmb_bal\n" ++
  ".Lbmb_nonce:\n  la t0, bal_builder_nonce_changes; mv s5, t0; la t0, bal_builder_nonce_count; ld s4, 0(t0); li t0, 0; sd t0, 72(sp)\n" ++
  ".Lbmb_non:\n  ld t0, 72(sp); bgeu t0, s4, .Lbmb_code; slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; add t2, s5, t1; mv a0, t2; li a1, 2; addi a2, t2, 32; li a3, 8; jal ra, bal_map_account_write_matches; bnez a0, .Lbmb_fail; ld t0, 72(sp); slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; add t2, s5, t1; ld a1, 24(t2); addi a2, t2, 32; mv a0, t2; li a3, 8; li a4, 2; mv a5, s0; mv a6, s1; jal ra, bal_map_find_supplied; bnez a0, .Lbmb_fail; ld t0, 72(sp); addi t0, t0, 1; sd t0, 72(sp); j .Lbmb_non\n" ++
  ".Lbmb_code:\n  la t0, bal_builder_code_changes; mv s7, t0; la t0, bal_builder_code_count; ld s6, 0(t0); li t0, 0; sd t0, 72(sp)\n" ++
  ".Lbmb_cod:\n  ld t0, 72(sp); bgeu t0, s6, .Lbmb_supplied; slli t1, t0, 6; add t2, s7, t1; ld a3, 40(t2); ld a2, 32(t2); mv a0, t2; li a1, 3; jal ra, bal_map_account_write_matches; bnez a0, .Lbmb_fail; ld t0, 72(sp); slli t1, t0, 6; add t2, s7, t1; ld a1, 24(t2); ld a2, 32(t2); ld a3, 40(t2); li a4, 3; mv a0, t2; mv a5, s0; mv a6, s1; jal ra, bal_map_find_supplied; bnez a0, .Lbmb_fail; ld t0, 72(sp); addi t0, t0, 1; sd t0, 72(sp); j .Lbmb_cod\n" ++
  ".Lbmb_supplied:\n  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init; bnez a2, .Lbmb_fail; sd a0, 72(sp); sd a1, 80(sp)\n" ++
  ".Lbmb_accts:\n  ld t0, 72(sp); ld t1, 80(sp); beq t0, t1, .Lbmb_ok; mv a0, t0; mv a1, t1; jal ra, rlp_walk_next; bnez a1, .Lbmb_fail; sd a0, 72(sp); sub t2, a0, a2; mv t3, a2; mv a0, t2; mv a1, t3; jal ra, bal_map_account_check; bnez a0, .Lbmb_fail; j .Lbmb_accts\n" ++
  ".Lbmb_ok:\n  li a0, 0; j .Lbmb_ret\n" ++
  ".Lbmb_fail:\n  li a0, 1\n" ++
  ".Lbmb_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 96; ret\n"

/-! Account-side reverse direction. -/
def balMapAccountCheckFunction : String :=
  "bal_map_account_check:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a0; mv s3, a1; mv a0, s0; mv a1, s1; jal ra, rlp_walk_init; bnez a2, .Lbmacc_fail; sd a0, 40(sp); sd a1, 48(sp)\n" ++
  "  ld a0, 40(sp); ld a1, 48(sp); jal ra, rlp_walk_next; bnez a1, .Lbmacc_fail; li t0, 20; bne a2, t0, .Lbmacc_fail; sub t0, a0, a2; sd t0, 56(sp)\n" ++
  "  mv a0, s0; mv a1, s1; ld a2, 56(sp); li a3, 1; jal ra, bal_map_check_account_field; bnez a0, .Lbmacc_fail\n" ++
  "  mv a0, s0; mv a1, s1; ld a2, 56(sp); li a3, 2; jal ra, bal_map_check_account_field; bnez a0, .Lbmacc_fail\n" ++
  "  mv a0, s0; mv a1, s1; ld a2, 56(sp); li a3, 3; jal ra, bal_map_check_account_field; bnez a0, .Lbmacc_fail; li a0, 0; j .Lbmacc_ret\n" ++
  ".Lbmacc_fail:\n  li a0, 1\n" ++
  ".Lbmacc_ret:\n  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); addi sp, sp, 64; ret\n"

def balMapBuilderConsistentFunctions : String :=
  balMapBuilderHasRowFunction ++ "\n" ++
  balMapCheckAccountFieldFunction ++ "\n" ++
  balMapFindSuppliedFunction ++ "\n" ++
  balMapAccountMatchesFunction ++ "\n" ++
  balMapAccountWriteMatchesFunction ++ "\n" ++
  balMapBuilderConsistentFunction ++ "\n" ++
  balMapAccountCheckFunction

def balMapBuilderConsistentDataSection : String :=
  ".balign 8\n" ++
  "bame_value:\n  .zero 32\n" ++
  "bame_nonce:\n  .zero 8\n"

/-! Probe: one balance tuple is accepted, then a value and a BAI mutation are
    each rejected.  The row is populated through the same builder arena used by
    the guest, so the negative controls exercise address+BAI attribution rather
    than a detached arithmetic predicate. -/
def ziskBalMapBuilderConsistentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, bal_builder_balance_changes; li t1, 0x11; li t2, 20\n" ++
  ".Lbmprobe_addr:\n  beqz t2, .Lbmprobe_addr_done; sb t1, 0(t0); addi t0, t0, 1; addi t2, t2, -1; j .Lbmprobe_addr\n" ++
  ".Lbmprobe_addr_done:\n" ++
  "  la t0, bal_builder_balance_changes; li t1, 1; sd zero, 32(t0); sd zero, 40(t0); sd zero, 48(t0); sb t1, 63(t0); sd t1, 24(t0)\n" ++
  "  la t0, bal_builder_balance_count; sd t1, 0(t0)\n" ++
  "  li t0, 0xa28a0000; la t2, bal_builder_balance_changes; li t3, 20\n" ++
  ".Lbmprobe_map_addr:\n  beqz t3, .Lbmprobe_map_fields; lbu t4, 0(t2); sb t4, 0(t0); addi t2, t2, 1; addi t0, t0, 1; addi t3, t3, -1; j .Lbmprobe_map_addr\n" ++
  ".Lbmprobe_map_fields:\n  li t0, 0xa28a0000; sd zero, 32(t0); sd zero, 40(t0); sd zero, 48(t0); sb t1, 63(t0); li t2, 1; sd t2, 112(t0); la t0, account_writes_count; sd t2, 0(t0)\n" ++
  "  li t0, 0x40000080; li t1, 0xde; sb t1, 0(t0); li t1, 0xdd; sb t1, 1(t0); li t1, 0x94; sb t1, 2(t0); li t1, 0x11; li t2, 20; addi t3, t0, 3\n" ++
  ".Lbmprobe_copy:\n  beqz t2, .Lbmprobe_fields; sb t1, 0(t3); addi t3, t3, 1; addi t2, t2, -1; j .Lbmprobe_copy\n" ++
  ".Lbmprobe_fields:\n" ++
  "  li t1, 0xc0; sb t1, 23(t0); sb t1, 24(t0); li t1, 0xc3; sb t1, 25(t0); li t1, 0xc2; sb t1, 26(t0); li t1, 1; sb t1, 27(t0); sb t1, 28(t0); li t1, 0xc0; sb t1, 29(t0); sb t1, 30(t0)\n" ++
  "  mv a0, t0; li a1, 31; jal ra, bal_map_builder_consistent; li t1, 0xa0010000; sd a0, 0(t1)\n" ++
  "  li t0, 0x40000080; li t1, 2; sb t1, 28(t0); mv a0, t0; li a1, 31; jal ra, bal_map_builder_consistent; li t1, 0xa0010000; sd a0, 8(t1)\n" ++
  "  li t1, 0x40000080; li t0, 1; sb t0, 28(t1); li t0, 2; sb t0, 27(t1); mv a0, t1; li a1, 31; jal ra, bal_map_builder_consistent; li t1, 0xa0010000; sd a0, 16(t1)\n" ++
  "  j .Lbmprobe_done\n" ++
  balMapBuilderConsistentFunctions ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  ".Lbmprobe_done:"

def ziskBalMapBuilderConsistentDataSection : String :=
  ".balign 8\n" ++
  "account_writes_count:\n  .zero 8\n" ++
  "bal_builder_balance_count:\n  .zero 8\n" ++
  "bal_builder_balance_changes:\n  .zero 64\n" ++
  "bal_builder_nonce_count:\n  .zero 8\n" ++
  "bal_builder_nonce_changes:\n  .zero 40\n" ++
  "bal_builder_code_count:\n  .zero 8\n" ++
  "bal_builder_code_changes:\n  .zero 64\n" ++
  balMapBuilderConsistentDataSection

def ziskBalMapBuilderConsistentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalMapBuilderConsistentPrologue
  dataAsm     := ziskBalMapBuilderConsistentDataSection
}

#guard (balMapBuilderConsistentFunctions.splitOn "bal_map_builder_consistent:").length == 2
#guard (balMapBuilderConsistentFunctions.splitOn "bal_map_builder_has_row:").length == 2
#guard (balMapBuilderConsistentFunctions.splitOn "bal_map_account_write_matches:").length == 2
#guard ziskBalMapBuilderConsistentPrologue.contains "bal_map_builder_consistent"

end EvmAsm.Codegen
