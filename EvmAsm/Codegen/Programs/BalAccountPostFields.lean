/-
  EvmAsm.Codegen.Programs.BalAccountPostFields

  BAL AccountChanges post-value extraction for state-root replay.

  AccountChanges RLP =
    [address, storage_changes, storage_reads, balance_changes, nonce_changes, code_changes]

  For state replay we need the final post-value for each account field. The BAL
  lists are ordered by blockAccessIndex, so the final account balance/nonce is
  the last entry in each corresponding change list. This helper extracts those
  two optional integers as raw canonical big-endian byte strings.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_post_fields -- BAL AccountChanges -> optional post balance/nonce

    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
    a2 = out balance bytes ptr (capacity 32)
    a3 = out balance length ptr (u64, UINT64_MAX means absent)
    a4 = out nonce bytes ptr (capacity 32)
    a5 = out nonce length ptr (u64, UINT64_MAX means absent)
    a0 (output) = 0 ok / 1 parse fail or value length > 32.

    For each nonempty change list, extracts the final item and then field 1 of
    that item. A zero post-value is represented by length 0, distinct from the
    absent sentinel. -/
def balAccountPostFieldsFunction : String :=
  "bal_account_post_fields:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # account-change ptr\n" ++
  "  mv s1, a1                   # account-change len\n" ++
  "  mv s2, a2                   # balance out ptr\n" ++
  "  mv s3, a3                   # balance len ptr\n" ++
  "  mv s4, a4                   # nonce out ptr\n" ++
  "  mv s5, a5                   # nonce len ptr\n" ++
  "  li t0, -1; sd t0, 0(s3); sd t0, 0(s5)\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbpf_fail\n" ++
  "  sd a0, 56(sp); sd a1, 64(sp)\n" ++
  "  # Skip address, storage_changes, storage_reads.\n" ++
  "  ld a0, 56(sp); ld a1, 64(sp); jal ra, rlp_walk_next; bnez a1, .Lbpf_fail; sd a0, 56(sp)\n" ++
  "  ld a0, 56(sp); ld a1, 64(sp); jal ra, rlp_walk_next; bnez a1, .Lbpf_fail; sd a0, 56(sp)\n" ++
  "  ld a0, 56(sp); ld a1, 64(sp); jal ra, rlp_walk_next; bnez a1, .Lbpf_fail; sd a0, 56(sp)\n" ++
  "  # balance_changes is field 3.\n" ++
  "  ld a0, 56(sp); ld a1, 64(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbpf_fail\n" ++
  "  sd a0, 56(sp); sub t0, a0, a2; mv t1, a2\n" ++
  "  mv a0, t0; mv a1, t1; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbpf_fail\n" ++
  "  beq a0, a1, .Lbpf_nonce\n" ++
  "  sd a0, 72(sp); sd a1, 80(sp)\n" ++
  ".Lbpf_bal_last_loop:\n" ++
  "  ld t0, 72(sp); ld t1, 80(sp); beq t0, t1, .Lbpf_bal_have_last\n" ++
  "  mv a0, t0; mv a1, t1; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbpf_fail\n" ++
  "  sd a0, 72(sp); sub t0, a0, a2; sd t0, 88(sp); sd a2, 96(sp)\n" ++
  "  j .Lbpf_bal_last_loop\n" ++
  ".Lbpf_bal_have_last:\n" ++
  "  ld a0, 88(sp); ld a1, 96(sp); jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbpf_fail\n" ++
  "  sd a0, 72(sp); sd a1, 80(sp)\n" ++
  "  ld a0, 72(sp); ld a1, 80(sp); jal ra, rlp_walk_next; bnez a1, .Lbpf_fail; sd a0, 72(sp)\n" ++
  "  ld a0, 72(sp); ld a1, 80(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbpf_fail\n" ++
  "  sub t0, a0, a2; mv t2, a2; li t3, 32; bgtu t2, t3, .Lbpf_fail\n" ++
  "  sd t2, 0(s3)\n" ++
  "  mv t4, s2\n" ++
  ".Lbpf_bal_cp:\n" ++
  "  beqz t2, .Lbpf_nonce\n" ++
  "  lbu t5, 0(t0); sb t5, 0(t4)\n" ++
  "  addi t0, t0, 1; addi t4, t4, 1; addi t2, t2, -1\n" ++
  "  j .Lbpf_bal_cp\n" ++
  ".Lbpf_nonce:\n" ++
  "  # nonce_changes is field 4.\n" ++
  "  ld a0, 56(sp); ld a1, 64(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbpf_fail\n" ++
  "  sub t0, a0, a2; mv t1, a2\n" ++
  "  mv a0, t0; mv a1, t1; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbpf_fail\n" ++
  "  beq a0, a1, .Lbpf_ok\n" ++
  "  sd a0, 72(sp); sd a1, 80(sp)\n" ++
  ".Lbpf_nonce_last_loop:\n" ++
  "  ld t0, 72(sp); ld t1, 80(sp); beq t0, t1, .Lbpf_nonce_have_last\n" ++
  "  mv a0, t0; mv a1, t1; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbpf_fail\n" ++
  "  sd a0, 72(sp); sub t0, a0, a2; sd t0, 88(sp); sd a2, 96(sp)\n" ++
  "  j .Lbpf_nonce_last_loop\n" ++
  ".Lbpf_nonce_have_last:\n" ++
  "  ld a0, 88(sp); ld a1, 96(sp); jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbpf_fail\n" ++
  "  sd a0, 72(sp); sd a1, 80(sp)\n" ++
  "  ld a0, 72(sp); ld a1, 80(sp); jal ra, rlp_walk_next; bnez a1, .Lbpf_fail; sd a0, 72(sp)\n" ++
  "  ld a0, 72(sp); ld a1, 80(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbpf_fail\n" ++
  "  sub t0, a0, a2; mv t2, a2; li t3, 32; bgtu t2, t3, .Lbpf_fail\n" ++
  "  sd t2, 0(s5)\n" ++
  "  mv t4, s4\n" ++
  ".Lbpf_nonce_cp:\n" ++
  "  beqz t2, .Lbpf_ok\n" ++
  "  lbu t5, 0(t0); sb t5, 0(t4)\n" ++
  "  addi t0, t0, 1; addi t4, t4, 1; addi t2, t2, -1\n" ++
  "  j .Lbpf_nonce_cp\n" ++
  ".Lbpf_ok:\n" ++
  "  li a0, 0; j .Lbpf_ret\n" ++
  ".Lbpf_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbpf_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_bal_account_post_fields`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  AccountChanges RLP length (u64)
      +16 AccountChanges RLP bytes
    Output layout:
      OUTPUT+0  : status
      OUTPUT+8  : balance length (UINT64_MAX absent, 0 zero, otherwise byte len)
      OUTPUT+16 : balance bytes (32-byte capacity, only first len significant)
      OUTPUT+48 : nonce length (UINT64_MAX absent, 0 zero, otherwise byte len)
      OUTPUT+56 : nonce bytes (32-byte capacity, only first len significant) -/
def ziskBalAccountPostFieldsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  sd zero, 32(t0); sd zero, 40(t0); sd zero, 48(t0); sd zero, 56(t0)\n" ++
  "  sd zero, 64(t0); sd zero, 72(t0); sd zero, 80(t0)\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # account-change RLP length\n" ++
  "  addi a0, t0, 16             # account-change RLP ptr\n" ++
  "  li a2, 0xa0010010           # balance bytes at OUTPUT+16\n" ++
  "  li a3, 0xa0010008           # balance length at OUTPUT+8\n" ++
  "  li a4, 0xa0010038           # nonce bytes at OUTPUT+56\n" ++
  "  li a5, 0xa0010030           # nonce length at OUTPUT+48\n" ++
  "  jal ra, bal_account_post_fields\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)   # status at OUTPUT+0\n" ++
  "  j .Lbpf_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  ".Lbpf_pdone:"

def ziskBalAccountPostFieldsDataSection : String :=
  ""

def ziskBalAccountPostFieldsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountPostFieldsPrologue
  dataAsm     := ziskBalAccountPostFieldsDataSection
}

end EvmAsm.Codegen
