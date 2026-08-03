/-
  EvmAsm.Codegen.Programs.BalStorageMap

  Consumers for the map-derived storage tuple stream.  The persistent
  `storage_writes` map is diffed at incorporation by `bal_emit_storage_changes`
  (BlockAccessListBuilder.lean, mirroring block_access_lists.py:667-676).  Its
  rows are canonical BE20 address, BAI, BE32 slot and LE post-value.  These
  helpers deliberately consume that stream directly; the append-only SSTORE
  effect log remains available to the focused probes while the production BAL
  validators move to the spec-shaped producer.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BlockAccessListBuilder
import EvmAsm.Codegen.Programs.BalStorageChangeValues

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## Per-account forward/reverse checks over map-derived rows

The two checks mirror `bal_storage_matches_exec_log` and
`bal_storage_covers_exec_log`, but use the already net-filtered builder rows.
The map producer has removed transaction-net-zero writes, so every matching row
is a required tuple and no `original` field is needed here.
-/

def balStorageMatchesMapFunction : String :=
  "bal_storage_matches_map:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                    # account address, BE20\n" ++
  "  mv s1, a1                    # AccountChanges\n" ++
  "  mv s2, a2                    # AccountChanges length\n" ++
  "  mv a0, s1; mv a1, s2; la a2, bsme_keys; la a3, bsme_vals\n" ++
  "  jal ra, bal_storage_change_values\n" ++
  "  mv s5, a0                    # parsed BAL change count\n" ++
  "  li s6, 0\n" ++
  ".Lbsm_map_loop:\n" ++
  "  beq s6, s5, .Lbsm_map_ok\n" ++
  "  slli t0, s6, 5; la t1, bsme_keys; add t1, t1, t0\n" ++
  "  la t2, bsme_vals; add t2, t2, t0\n" ++
  "  mv s3, t1\n" ++
  "  la t0, bsme_vrev; addi t1, t2, 31; li t3, 32\n" ++
  ".Lbsm_map_rev:\n" ++
  "  beqz t3, .Lbsm_map_rev_done; lbu t4, 0(t1); sb t4, 0(t0); addi t1, t1, -1; addi t0, t0, 1; addi t3, t3, -1; j .Lbsm_map_rev\n" ++
  ".Lbsm_map_rev_done:\n" ++
  "  la t0, bal_builder_storage_change_count; ld t0, 0(t0); li t1, 0\n" ++
  ".Lbsm_map_scan:\n" ++
  "  bgeu t1, t0, .Lbsm_map_fail\n" ++
  "  li t2, 96; mul t2, t1, t2; la t3, bal_builder_storage_changes; add t3, t3, t2\n" ++
  "  li t4, 0; mv t5, t3; mv t6, s0\n" ++
  ".Lbsm_map_addr:\n" ++
  "  li a0, 20; beq t4, a0, .Lbsm_map_slot\n" ++
  "  lbu a0, 0(t5); lbu a1, 0(t6); bne a0, a1, .Lbsm_map_next\n" ++
  "  addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, 1; j .Lbsm_map_addr\n" ++
  ".Lbsm_map_slot:\n" ++
  "  ld a0, 32(t3); ld a1, 0(s3); bne a0, a1, .Lbsm_map_next\n" ++
  "  ld a0, 40(t3); ld a1, 8(s3); bne a0, a1, .Lbsm_map_next\n" ++
  "  ld a0, 48(t3); ld a1, 16(s3); bne a0, a1, .Lbsm_map_next\n" ++
  "  ld a0, 56(t3); ld a1, 24(s3); bne a0, a1, .Lbsm_map_next\n" ++
  "  la a1, bsme_vrev\n" ++
  "  ld a0, 64(t3); ld a1, 0(a1); bne a0, a1, .Lbsm_map_fail\n" ++
  "  ld a0, 72(t3); la a1, bsme_vrev; ld a1, 8(a1); bne a0, a1, .Lbsm_map_fail\n" ++
  "  ld a0, 80(t3); la a1, bsme_vrev; ld a1, 16(a1); bne a0, a1, .Lbsm_map_fail\n" ++
  "  ld a0, 88(t3); la a1, bsme_vrev; ld a1, 24(a1); bne a0, a1, .Lbsm_map_fail\n" ++
  "  j .Lbsm_map_next_key\n" ++
  ".Lbsm_map_next:\n" ++
  "  addi t1, t1, 1; j .Lbsm_map_scan\n" ++
  ".Lbsm_map_next_key:\n" ++
  "  addi s6, s6, 1; j .Lbsm_map_loop\n" ++
  ".Lbsm_map_ok:\n" ++
  "  li a0, 0; j .Lbsm_map_ret\n" ++
  ".Lbsm_map_fail:\n" ++
  "  la t0, bsr_map_fail_map_index; sd t1, 0(t0); la t0, bsr_map_fail_bal_index; sd s6, 0(t0)\n" ++
  "  la t0, bsr_map_fail_row; mv t2, t3; li t4, 12\n" ++
  ".Lbsm_save_row:\n" ++
  "  beqz t4, .Lbsm_save_key; ld t5, 0(t2); sd t5, 0(t0); addi t2, t2, 8; addi t0, t0, 8; addi t4, t4, -1; j .Lbsm_save_row\n" ++
  ".Lbsm_save_key:\n" ++
  "  la t0, bsr_map_fail_key; mv t2, s3; li t4, 4\n" ++
  ".Lbsm_save_key_loop:\n" ++
  "  beqz t4, .Lbsm_save_val; ld t5, 0(t2); sd t5, 0(t0); addi t2, t2, 8; addi t0, t0, 8; addi t4, t4, -1; j .Lbsm_save_key_loop\n" ++
  ".Lbsm_save_val:\n" ++
  "  la t0, bsr_map_fail_val; la t2, bsme_vrev; li t4, 4\n" ++
  ".Lbsm_save_val_loop:\n" ++
  "  beqz t4, .Lbsm_save_done; ld t5, 0(t2); sd t5, 0(t0); addi t2, t2, 8; addi t0, t0, 8; addi t4, t4, -1; j .Lbsm_save_val_loop\n" ++
  ".Lbsm_save_done:\n" ++
  "  li a0, 1\n" ++
  ".Lbsm_map_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); addi sp, sp, 64; ret\n"

def balStorageCoversMapFunction : String :=
  "bal_storage_covers_map:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  mv a0, s1; mv a1, s2; la a2, bsme_keys; la a3, bsme_vals\n" ++
  "  jal ra, bal_storage_change_values\n" ++
  "  mv s3, a0                    # BAL change count\n" ++
  "  la t0, bal_builder_storage_change_count; ld s4, 0(t0); li s5, 0\n" ++
  ".Lbsc_map_row:\n" ++
  "  beq s5, s4, .Lbsc_map_ok\n" ++
  "  li t0, 96; mul t0, s5, t0; la t1, bal_builder_storage_changes; add s6, t1, t0\n" ++
  "  li t0, 0; mv t1, s6; mv t2, s0\n" ++
  ".Lbsc_map_addr:\n" ++
  "  li t3, 20; beq t0, t3, .Lbsc_map_key_start\n" ++
  "  lbu t3, 0(t1); lbu t4, 0(t2); bne t3, t4, .Lbsc_map_next_row\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, 1; j .Lbsc_map_addr\n" ++
  ".Lbsc_map_key_start:\n" ++
  "  li s7, 0\n" ++
  ".Lbsc_map_key:\n" ++
  "  bgeu s7, s3, .Lbsc_map_fail\n" ++
  "  slli t0, s7, 5; la t1, bsme_keys; add t1, t1, t0\n" ++
  "  ld t0, 32(s6); ld t2, 0(t1); bne t0, t2, .Lbsc_map_key_next\n" ++
  "  ld t0, 40(s6); ld t2, 8(t1); bne t0, t2, .Lbsc_map_key_next\n" ++
  "  ld t0, 48(s6); ld t2, 16(t1); bne t0, t2, .Lbsc_map_key_next\n" ++
  "  ld t0, 56(s6); ld t2, 24(t1); bne t0, t2, .Lbsc_map_key_next\n" ++
  "  slli t0, s7, 5; la t2, bsme_vals; add t2, t2, t0; la t3, bsme_vrev; addi t1, t2, 31; li t4, 32\n" ++
  ".Lbsc_map_rev:\n" ++
  "  beqz t4, .Lbsc_map_rev_done; lbu t5, 0(t1); sb t5, 0(t3); addi t1, t1, -1; addi t3, t3, 1; addi t4, t4, -1; j .Lbsc_map_rev\n" ++
  ".Lbsc_map_rev_done:\n" ++
  "  la t1, bsme_vrev; ld t0, 64(s6); ld t2, 0(t1); bne t0, t2, .Lbsc_map_fail\n" ++
  "  ld t0, 72(s6); ld t2, 8(t1); bne t0, t2, .Lbsc_map_fail\n" ++
  "  ld t0, 80(s6); ld t2, 16(t1); bne t0, t2, .Lbsc_map_fail\n" ++
  "  ld t0, 88(s6); ld t2, 24(t1); bne t0, t2, .Lbsc_map_fail\n" ++
  "  j .Lbsc_map_next_row\n" ++
  ".Lbsc_map_key_next:\n" ++
  "  addi s7, s7, 1; j .Lbsc_map_key\n" ++
  ".Lbsc_map_next_row:\n" ++
  "  addi s5, s5, 1; j .Lbsc_map_row\n" ++
  ".Lbsc_map_ok:\n" ++
  "  li a0, 0; j .Lbsc_map_ret\n" ++
  ".Lbsc_map_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbsc_map_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 80; ret\n"

/-! ## All-account wrapper over the map rows -/

def balAllAccountsStorageConsistentMapFunction : String :=
  "bal_all_accounts_storage_consistent_map:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init; bnez a2, .Lbasm_parse_fail\n" ++
  "  mv s4, a0; mv s5, a1\n" ++
  ".Lbasm_loop:\n" ++
  "  beq s4, s5, .Lbasm_ok\n" ++
  "  mv a0, s4; mv a1, s5; jal ra, rlp_walk_next; bnez a1, .Lbasm_parse_fail\n" ++
  "  mv s4, a0; sub s6, a0, a2; mv s7, a2\n" ++
  "  mv a0, s6; mv a1, s7; jal ra, rlp_walk_init; bnez a2, .Lbasm_parse_fail\n" ++
  "  jal ra, rlp_walk_next; bnez a1, .Lbasm_parse_fail; li t0, 20; bne a2, t0, .Lbasm_parse_fail\n" ++
  "  sub s8, a0, a2; li t0, 0\n" ++
  ".Lbasm_skip_outer:\n" ++
  "  beq t0, s3, .Lbasm_check\n" ++
  "  slli t1, t0, 5; add t1, s2, t1; li t2, 0\n" ++
  ".Lbasm_skip_cmp:\n" ++
  "  li t3, 20; beq t2, t3, .Lbasm_next\n" ++
  "  add t3, s8, t2; lbu t3, 0(t3); add t4, t1, t2; lbu t4, 0(t4); bne t3, t4, .Lbasm_skip_adv\n" ++
  "  addi t2, t2, 1; j .Lbasm_skip_cmp\n" ++
  ".Lbasm_skip_adv:\n" ++
  "  addi t0, t0, 1; j .Lbasm_skip_outer\n" ++
  ".Lbasm_check:\n" ++
  "  mv a0, s8; mv a1, s6; mv a2, s7; jal ra, bal_storage_matches_map; beqz a0, .Lbasm_match_ok\n" ++
  "  la t0, bsr_map_matches_fail_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lbasm_match_fail\n" ++
  ".Lbasm_match_ok:\n" ++
  "  mv a0, s8; mv a1, s6; mv a2, s7; jal ra, bal_storage_covers_map; beqz a0, .Lbasm_covers_ok\n" ++
  "  la t0, bsr_map_covers_fail_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lbasm_covers_fail\n" ++
  ".Lbasm_covers_ok:\n" ++
  ".Lbasm_next:\n" ++
  "  j .Lbasm_loop\n" ++
  ".Lbasm_ok:\n" ++
  "  li a0, 0; j .Lbasm_ret\n" ++
  ".Lbasm_parse_fail:\n" ++
  "  la t0, bsr_map_parse_fail_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  li a0, 2; j .Lbasm_ret\n" ++
  ".Lbasm_match_fail:\n" ++
  "  li a0, 3; j .Lbasm_ret\n" ++
  ".Lbasm_covers_fail:\n" ++
  "  li a0, 4; j .Lbasm_ret\n" ++
  ".Lbasm_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbasm_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)\n" ++
  "  ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp); addi sp, sp, 112; ret\n"

/-! ## Tuple sequence reconstruction from map rows

The map producer upserts one row per `(address, slot, block_access_index)` and
emits rows in incorporation order.  Unlike the append log, rows are already
net-filtered, so reconstruction is a straight filtered copy. -/

def mapStorageSlotTuplesFunction : String :=
  "map_storage_slot_tuples:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; li s5, 0; li s6, 0\n" ++
  ".Lmss_loop:\n" ++
  "  bgeu s5, s3, .Lmss_done\n" ++
  "  li t0, 96; mul t0, s5, t0; add t1, s2, t0; li t2, 0; mv t3, t1; mv t4, s0\n" ++
  ".Lmss_addr:\n" ++
  "  li t5, 20; beq t2, t5, .Lmss_slot\n" ++
  "  lbu t5, 0(t3); lbu t6, 0(t4); bne t5, t6, .Lmss_next\n" ++
  "  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, 1; j .Lmss_addr\n" ++
  ".Lmss_slot:\n" ++
  "  ld t5, 32(t1); ld t6, 0(s1); bne t5, t6, .Lmss_next\n" ++
  "  ld t5, 40(t1); ld t6, 8(s1); bne t5, t6, .Lmss_next\n" ++
  "  ld t5, 48(t1); ld t6, 16(s1); bne t5, t6, .Lmss_next\n" ++
  "  ld t5, 56(t1); ld t6, 24(s1); bne t5, t6, .Lmss_next\n" ++
  "  li t5, " ++ toString bsrMaxTuplesPerSlot ++ "; bgeu s6, t5, .Lmss_count_only\n" ++
  "  li t5, 40; mul t5, s6, t5; add t6, s4, t5; ld t5, 24(t1); sd t5, 0(t6)\n" ++
  "  ld t5, 64(t1); sd t5, 8(t6); ld t5, 72(t1); sd t5, 16(t6); ld t5, 80(t1); sd t5, 24(t6); ld t5, 88(t1); sd t5, 32(t6)\n" ++
  ".Lmss_count_only:\n" ++
  "  addi s6, s6, 1\n" ++
  ".Lmss_next:\n" ++
  "  addi s5, s5, 1; j .Lmss_loop\n" ++
  ".Lmss_done:\n" ++
  "  mv a0, s6\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); addi sp, sp, 64; ret\n"

end EvmAsm.Codegen
