/-
  EvmAsm.Codegen.Programs.Eip7702NonceReuseGuard

  Conservative EIP-7702 transaction-order guard for stateless EEST verdicts.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.Address

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## enrg_u32le -- local unaligned u32 little-endian reader. -/
def enrgU32le_prog : Program :=
  [ .LBU .x5 .x10 (0 : BitVec 12),
    .LBU .x6 .x10 (1 : BitVec 12),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x10 (2 : BitVec 12),
    .SLLI .x6 .x6 (16 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x10 (3 : BitVec 12),
    .SLLI .x6 .x6 (24 : BitVec 6),
    .OR .x10 .x5 .x6,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def enrgU32leFunction : String :=
  "enrg_u32le:\n" ++ emitProgram enrgU32le_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `enrgU32le_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem enrgU32leFunction_eq_prog :
    enrgU32leFunction = "enrg_u32le:\n" ++ emitProgram enrgU32le_prog := rfl

#guard enrgU32leFunction.startsWith "enrg_u32le:\n"
#guard enrgU32le_prog.length = 11
/-! ## eip7702_nonce_reuse_guard -- reject tx nonce below prior BAL nonce.
    a0 = exec_payload ptr   a1 = SSZ_BASE   a2 = BAL ptr   a3 = BAL len
    a0 (output) = 0 ok/unsupported, 1 invalid nonce reuse.

    For each transaction, derive its sender from `public_keys[i]`, then scan BAL
    nonce changes for that account.  If an earlier nonce-change value is greater
    than the transaction nonce, the executable spec rejects the transaction as
    nonce-too-low.  Malformed or unsupported shapes fail open. -/
def eip7702NonceReuseGuardFunction : String :=
  "eip7702_nonce_reuse_guard:\n" ++
  "  addi sp, sp, -128\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # exec_payload\n" ++
  "  mv s1, a1                   # SSZ_BASE\n" ++
  "  mv s2, a2                   # BAL ptr\n" ++
  "  mv s3, a3                   # BAL len\n" ++
  "  addi a0, s0, 504; jal ra, enrg_u32le\n" ++
  "  add s4, s0, a0              # tx list ptr\n" ++
  "  addi a0, s0, 508; jal ra, enrg_u32le\n" ++
  "  add t0, s0, a0              # withdrawals ptr\n" ++
  "  bltu t0, s4, .Lenrg_ok\n" ++
  "  sub s5, t0, s4              # tx list len\n" ++
  "  beqz s5, .Lenrg_ok\n" ++
  "  mv a0, s4; jal ra, enrg_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lenrg_ok\n" ++
  "  srli s6, a0, 2              # tx_count\n" ++
  "  beqz s6, .Lenrg_ok\n" ++
  "  li t0, 16; bgtu s6, t0, .Lenrg_ok\n" ++
  "  addi a0, s1, 12; jal ra, enrg_u32le\n" ++
  "  add s7, s1, a0              # public_keys ptr\n" ++
  "  li s8, 0                    # tx index\n" ++
  ".Lenrg_tx_loop:\n" ++
  "  beq s8, s6, .Lenrg_ok\n" ++
  "  slli t0, s8, 2; add t1, s4, t0; mv a0, t1; jal ra, enrg_u32le\n" ++
  "  mv s9, a0                   # tx item offset\n" ++
  "  addi t0, s8, 1\n" ++
  "  beq t0, s6, .Lenrg_last_tx\n" ++
  "  slli t1, t0, 2; add t1, s4, t1; mv a0, t1; jal ra, enrg_u32le\n" ++
  "  j .Lenrg_have_next\n" ++
  ".Lenrg_last_tx:\n" ++
  "  mv a0, s5\n" ++
  ".Lenrg_have_next:\n" ++
  "  bltu a0, s9, .Lenrg_ok\n" ++
  "  sub s10, a0, s9             # tx len\n" ++
  "  add s9, s4, s9              # tx ptr\n" ++
  "  mv a0, s9; mv a1, s10; la a2, enrg_tx_type; la a3, enrg_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Lenrg_next_tx\n" ++
  "  la t0, enrg_tx_type; ld t1, 0(t0)\n" ++
  "  la t0, enrg_inner_off; ld t2, 0(t0)\n" ++
  "  add s11, s9, t2             # inner ptr\n" ++
  "  bltu s10, t2, .Lenrg_next_tx\n" ++
  "  sub t3, s10, t2             # inner len\n" ++
  "  beqz t1, .Lenrg_legacy_nonce\n" ++
  "  li t4, 4; bgtu t1, t4, .Lenrg_next_tx\n" ++
  "  li a2, 1; j .Lenrg_read_nonce\n" ++
  ".Lenrg_legacy_nonce:\n" ++
  "  li a2, 0\n" ++
  ".Lenrg_read_nonce:\n" ++
  "  mv a0, s11; mv a1, t3; la a3, enrg_tx_nonce\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lenrg_next_tx\n" ++
  "  li t0, 65; mul t1, s8, t0; add t1, s7, t1; addi a0, t1, 1\n" ++
  "  la a1, enrg_sender_addr; jal ra, address_from_pubkey\n" ++
  "  mv a0, s2; mv a1, s3; la a2, enrg_bal_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lenrg_next_tx\n" ++
  "  la t0, enrg_bal_index; sd zero, 0(t0)\n" ++
  ".Lenrg_bal_loop:\n" ++
  "  la t0, enrg_bal_index; ld t5, 0(t0)\n" ++
  "  la t0, enrg_bal_count; ld t6, 0(t0)\n" ++
  "  beq t5, t6, .Lenrg_next_tx\n" ++
  "  mv a0, s2; mv a1, s3; mv a2, t5; la a3, enrg_item_off; la a4, enrg_item_len\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  bnez a0, .Lenrg_next_bal\n" ++
  "  la t0, enrg_item_off; ld t0, 0(t0); add t0, s2, t0; la t1, enrg_acct_ptr; sd t0, 0(t1)\n" ++
  "  la t1, enrg_item_len; ld t1, 0(t1); la t2, enrg_acct_len; sd t1, 0(t2)\n" ++
  "  mv a0, t0; mv a1, t1; li a2, 0; la a3, enrg_addr_off; la a4, enrg_addr_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lenrg_next_bal\n" ++
  "  la t0, enrg_addr_len; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lenrg_next_bal\n" ++
  "  la t0, enrg_acct_ptr; ld t0, 0(t0); la t1, enrg_addr_off; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  la t2, enrg_sender_addr; li t3, 20\n" ++
  ".Lenrg_addr_cmp:\n" ++
  "  beqz t3, .Lenrg_addr_match\n" ++
  "  lbu t4, 0(t0); lbu a7, 0(t2); bne t4, a7, .Lenrg_next_bal\n" ++
  "  addi t0, t0, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lenrg_addr_cmp\n" ++
  ".Lenrg_addr_match:\n" ++
  "  la t0, enrg_acct_ptr; ld a0, 0(t0); la t0, enrg_acct_len; ld a1, 0(t0); li a2, 4; la a3, enrg_nonce_off; la a4, enrg_nonce_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lenrg_next_bal\n" ++
  "  la t0, enrg_acct_ptr; ld t0, 0(t0); la t1, enrg_nonce_off; ld t1, 0(t1); add t0, t0, t1; la t2, enrg_nonce_list_ptr; sd t0, 0(t2)\n" ++
  "  la t0, enrg_nonce_len; ld a1, 0(t0); la t0, enrg_nonce_list_ptr; ld a0, 0(t0); la a2, enrg_nonce_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lenrg_next_bal\n" ++
  "  la t0, enrg_nonce_index; sd zero, 0(t0)\n" ++
  ".Lenrg_nonce_loop:\n" ++
  "  la t0, enrg_nonce_index; ld t3, 0(t0)\n" ++
  "  la t0, enrg_nonce_count; ld t4, 0(t0)\n" ++
  "  beq t3, t4, .Lenrg_next_bal\n" ++
  "  la t0, enrg_nonce_list_ptr; ld a0, 0(t0); la t0, enrg_nonce_len; ld a1, 0(t0); mv a2, t3; la a3, enrg_change_off; la a4, enrg_change_len\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  bnez a0, .Lenrg_next_nonce\n" ++
  "  la t0, enrg_nonce_list_ptr; ld t0, 0(t0); la t1, enrg_change_off; ld t1, 0(t1); add t0, t0, t1; la t2, enrg_change_ptr; sd t0, 0(t2)\n" ++
  "  la t1, enrg_change_len; ld t1, 0(t1); la t2, enrg_change_item_len; sd t1, 0(t2)\n" ++
  "  mv a0, t0; mv a1, t1; li a2, 0; la a3, enrg_change_index\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lenrg_next_nonce\n" ++
  "  la t0, enrg_change_index; ld t0, 0(t0); addi t1, s8, 1; bgeu t0, t1, .Lenrg_next_nonce\n" ++
  "  la t0, enrg_change_ptr; ld a0, 0(t0); la t0, enrg_change_item_len; ld a1, 0(t0); li a2, 1; la a3, enrg_change_value\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lenrg_next_nonce\n" ++
  "  la t0, enrg_change_value; ld t0, 0(t0); la t1, enrg_tx_nonce; ld t1, 0(t1); bgtu t0, t1, .Lenrg_fail\n" ++
  ".Lenrg_next_nonce:\n" ++
  "  la t0, enrg_nonce_index; ld t3, 0(t0); addi t3, t3, 1; sd t3, 0(t0); j .Lenrg_nonce_loop\n" ++
  ".Lenrg_next_bal:\n" ++
  "  la t0, enrg_bal_index; ld t5, 0(t0); addi t5, t5, 1; sd t5, 0(t0); j .Lenrg_bal_loop\n" ++
  ".Lenrg_next_tx:\n" ++
  "  addi s8, s8, 1; j .Lenrg_tx_loop\n" ++
  ".Lenrg_ok:\n" ++
  "  li a0, 0; j .Lenrg_ret\n" ++
  ".Lenrg_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lenrg_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 128\n" ++
  "  ret"

def eip7702NonceReuseGuardDataSection : String :=
  ".balign 8\n" ++
  "enrg_tx_type:\n  .zero 8\n" ++
  "enrg_inner_off:\n  .zero 8\n" ++
  "enrg_tx_nonce:\n  .zero 8\n" ++
  "enrg_bal_count:\n  .zero 8\n" ++
  "enrg_bal_index:\n  .zero 8\n" ++
  "enrg_item_off:\n  .zero 8\n" ++
  "enrg_item_len:\n  .zero 8\n" ++
  "enrg_acct_ptr:\n  .zero 8\n" ++
  "enrg_acct_len:\n  .zero 8\n" ++
  "enrg_addr_off:\n  .zero 8\n" ++
  "enrg_addr_len:\n  .zero 8\n" ++
  "enrg_nonce_off:\n  .zero 8\n" ++
  "enrg_nonce_len:\n  .zero 8\n" ++
  "enrg_nonce_list_ptr:\n  .zero 8\n" ++
  "enrg_nonce_count:\n  .zero 8\n" ++
  "enrg_nonce_index:\n  .zero 8\n" ++
  "enrg_change_off:\n  .zero 8\n" ++
  "enrg_change_len:\n  .zero 8\n" ++
  "enrg_change_ptr:\n  .zero 8\n" ++
  "enrg_change_item_len:\n  .zero 8\n" ++
  "enrg_change_index:\n  .zero 8\n" ++
  "enrg_change_value:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "enrg_sender_addr:\n  .zero 32\n" ++
  "afp_digest:\n  .zero 32\n"

end EvmAsm.Codegen
