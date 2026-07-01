/-
  EvmAsm.Codegen.Programs.RuntimeSameBlockCode

  Runtime helper for EIP-7702 same-block code observations. EXTCODESIZE,
  EXTCODEHASH, and EXTCODECOPY observe an account's current code. During a
  set-code transaction, that current code can be the BAL's final
  0xef0100||address delegation marker even though the pre-state trie still has
  empty code.
-/

import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

/-! ## runtime_same_block_delegation_code

    Calling convention:
      a0 = 20-byte address ptr
      runtime_current_bal_ptr/runtime_current_bal_len name the current BAL section
    Returns:
      a0 = 0 if the BAL has a final code change for this account and that final
           code is exactly a 23-byte EIP-7702 delegation marker; in that case
           rsbd_code_ptr/rsbd_code_len name the marker bytes.
      a0 = 1 otherwise.
-/
def runtimeSameBlockDelegationCodeFunction : String :=
  "runtime_same_block_delegation_code:
" ++
  "  addi sp, sp, -80
" ++
  "  sd ra, 0(sp)
" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
" ++
  "  mv s0, a0                    # target address ptr
" ++
  "  la t0, runtime_current_bal_ptr; ld s1, 0(t0)
" ++
  "  la t0, runtime_current_bal_len; ld s2, 0(t0)
" ++
  "  beqz s1, .Lrsbd_no_bal_ptr
" ++
  "  beqz s2, .Lrsbd_no_bal_len
" ++
  "  mv a0, s1; mv a1, s2; la a2, rsbd_count
" ++
  "  jal ra, rlp_list_count_items
" ++
  "  bnez a0, .Lrsbd_no_count
" ++
  "  la t0, rsbd_count; ld s3, 0(t0)
" ++
  "  li s4, 0
" ++
  ".Lrsbd_loop:
" ++
  "  beq s4, s3, .Lrsbd_no_notfound
" ++
  "  mv a0, s1; mv a1, s2; mv a2, s4; la a3, rsbd_acct_off; la a4, rsbd_acct_len
" ++
  "  jal ra, rlp_item_span
" ++
  "  bnez a0, .Lrsbd_no_span
" ++
  "  la t0, rsbd_acct_off; ld t1, 0(t0); add s5, s1, t1
" ++
  "  la t0, rsbd_acct_len; ld s6, 0(t0)
" ++
  "  mv a0, s5; mv a1, s6; li a2, 0; la a3, rsbd_field_off; la a4, rsbd_field_len
" ++
  "  jal ra, rlp_list_nth_item
" ++
  "  bnez a0, .Lrsbd_next
" ++
  "  la t0, rsbd_field_len; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lrsbd_next
" ++
  "  la t0, rsbd_field_off; ld t1, 0(t0); add t1, s5, t1
" ++
  "  mv t2, s0; li t3, 20
" ++
  ".Lrsbd_addr_cmp:
" ++
  "  beqz t3, .Lrsbd_addr_match
" ++
  "  lbu t4, 0(t1); lbu t5, 0(t2); bne t4, t5, .Lrsbd_next
" ++
  "  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lrsbd_addr_cmp
" ++
  ".Lrsbd_addr_match:
" ++
  "  mv a0, s5; mv a1, s6; li a2, 5; la a3, rsbd_field_off; la a4, rsbd_field_len
" ++
  "  jal ra, rlp_list_nth_item                  # code_changes
" ++
  "  bnez a0, .Lrsbd_no_code_item
" ++
  "  la t0, rsbd_field_off; ld t1, 0(t0); add s7, s5, t1
" ++
  "  la t0, rsbd_field_len; ld t1, 0(t0)
" ++
  "  mv a0, s7; mv a1, t1; la a2, rsbd_code_count
" ++
  "  jal ra, rlp_list_count_items
" ++
  "  bnez a0, .Lrsbd_no_code_count
" ++
  "  la t0, rsbd_code_count; ld t1, 0(t0); beqz t1, .Lrsbd_no_empty_code_changes
" ++
  "  addi t1, t1, -1
" ++
  "  la t0, rsbd_field_len; ld a1, 0(t0)
" ++
  "  mv a0, s7; mv a2, t1; la a3, rsbd_tuple_off; la a4, rsbd_tuple_len
" ++
  "  jal ra, rlp_list_nth_item
" ++
  "  bnez a0, .Lrsbd_no_tuple
" ++
  "  la t0, rsbd_tuple_off; ld t1, 0(t0); add t1, s7, t1
" ++
  "  la t0, rsbd_tuple_len; ld t2, 0(t0)
" ++
  "  mv a0, t1; mv a1, t2; li a2, 1; la a3, rsbd_code_off; la a4, rsbd_code_len_cell
" ++
  "  jal ra, rlp_list_nth_item
" ++
  "  bnez a0, .Lrsbd_no_code_field
" ++
  "  la t0, rsbd_code_len_cell; ld t2, 0(t0); li t3, 23; bne t2, t3, .Lrsbd_no_code_len
" ++
  "  la t0, rsbd_tuple_off; ld t1, 0(t0); add t1, s7, t1
" ++
  "  la t0, rsbd_code_off; ld t2, 0(t0); add t1, t1, t2
" ++
  "  lbu t3, 0(t1); li t4, 0xef; bne t3, t4, .Lrsbd_no_marker0
" ++
  "  lbu t3, 1(t1); li t4, 0x01; bne t3, t4, .Lrsbd_no_marker1
" ++
  "  lbu t3, 2(t1); bnez t3, .Lrsbd_no_marker2
" ++
  "  la t0, rsbd_code_ptr; sd t1, 0(t0)
" ++
  "  la t0, rsbd_code_len; li t1, 23; sd t1, 0(t0)
" ++
  "  li a0, 0; j .Lrsbd_ret
" ++
  ".Lrsbd_next:
" ++
  "  addi s4, s4, 1; j .Lrsbd_loop
" ++
  ".Lrsbd_no:
" ++
  "  li a0, 1
" ++
  "  j .Lrsbd_ret
" ++
  ".Lrsbd_no_bal_ptr:
" ++
  "  j .Lrsbd_no
" ++
  ".Lrsbd_no_bal_len:
" ++
  "  j .Lrsbd_no
" ++
  ".Lrsbd_no_count:
" ++
  "  j .Lrsbd_no
" ++
  ".Lrsbd_no_notfound:
" ++
  "  j .Lrsbd_no
" ++
  ".Lrsbd_no_span:
" ++
  "  j .Lrsbd_no
" ++
  ".Lrsbd_no_code_item:
" ++
  "  j .Lrsbd_no
" ++
  ".Lrsbd_no_code_count:
" ++
  "  j .Lrsbd_no
" ++
  ".Lrsbd_no_empty_code_changes:
" ++
  "  j .Lrsbd_no
" ++
  ".Lrsbd_no_tuple:
" ++
  "  j .Lrsbd_no
" ++
  ".Lrsbd_no_code_field:
" ++
  "  j .Lrsbd_no
" ++
  ".Lrsbd_no_code_len:
" ++
  "  j .Lrsbd_no
" ++
  ".Lrsbd_no_marker0:
" ++
  "  j .Lrsbd_no
" ++
  ".Lrsbd_no_marker1:
" ++
  "  j .Lrsbd_no
" ++
  ".Lrsbd_no_marker2:
" ++
  "  j .Lrsbd_no
" ++
  ".Lrsbd_ret:
" ++
  "  ld ra, 0(sp)
" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
" ++
  "  addi sp, sp, 80
" ++
  "  ret"

def runtimeSameBlockDelegationCodeData : String :=
  ".balign 8
" ++
  "runtime_current_bal_ptr:
  .zero 8
" ++
  "runtime_current_bal_len:
  .zero 8
" ++
  "rsbd_count:
  .zero 8
" ++
  "rsbd_acct_off:
  .zero 8
" ++
  "rsbd_acct_len:
  .zero 8
" ++
  "rsbd_field_off:
  .zero 8
" ++
  "rsbd_field_len:
  .zero 8
" ++
  "rsbd_code_count:
  .zero 8
" ++
  "rsbd_tuple_off:
  .zero 8
" ++
  "rsbd_tuple_len:
  .zero 8
" ++
  "rsbd_code_off:
  .zero 8
" ++
  "rsbd_code_len_cell:
  .zero 8
" ++
  "rsbd_code_ptr:
  .zero 8
" ++
  "rsbd_code_len:
  .zero 8
" ++
  "rsbd_hash:
  .zero 32
" ++
  "eahsr_same_tx_empty_flag:
  .zero 8
" ++
  "ecc_old_active:
  .zero 8
" ++
  "ecc_same_block_hit:
  .zero 8
"

end EvmAsm.Codegen
