/-
  EvmAsm.Codegen.Programs.BalAccountRecordArray

  Derive the pre-account record table that `bal_account_state_root` consumes:
  for each BAL AccountChanges item, walk the pre-state trie to find the account
  RLP, or use the canonical empty-account RLP when the account is absent.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BalAccountHasStateChange
import EvmAsm.Codegen.Programs.BalAccountPath
import EvmAsm.Codegen.Programs.BalModeledSystem
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.MptSet

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_record_array -- BAL list -> pre-account records

    a0 = root_hash ptr        a1 = witness ptr       a2 = witness length
    a3 = BAL list ptr         a4 = BAL list length   a5 = n records/items
    a6 = records out ptr      a7 = account arena out ptr
    a0 (output) = 0 ok / 1 conservative failure.

    Record layout matches `bal_account_descriptor_array`:
      +0 account_ptr | +8 account_len | +16 is_insert.

    Found accounts are copied into the caller-provided arena with is_insert=0.
    Missing accounts use the canonical empty account RLP with is_insert=1.
    Read-only BAL rows are recorded as the canonical empty account RLP with
    is_insert=3 so descriptor construction can skip re-classifying them.

    If `bara_skip_modeled_system` is nonzero, EIP-2935/EIP-4788 rows are also
    recorded with is_insert=3 because the verdict path has already replayed
    those system writes explicitly. The flag defaults to zero for standalone
    BAL state-root callers. -/
def balAccountRecordArrayFunction : String :=
  "bal_account_record_array:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                   # root hash ptr\n" ++
  "  mv s1, a1                   # witness ptr\n" ++
  "  mv s2, a2                   # witness len\n" ++
  "  mv s3, a3                   # BAL list ptr\n" ++
  "  mv s4, a4                   # BAL list len\n" ++
  "  mv s5, a5                   # n\n" ++
  "  mv s6, a6                   # records out base\n" ++
  "  mv s7, a7                   # account arena cursor\n" ++
  "  add t0, s3, s4              # BAL end\n" ++
  "  la t1, bara_bal_end; sd t0, 0(t1)\n" ++
  "  bgeu s3, t0, .Lbara_fail\n" ++
  "  lbu t2, 0(s3); li t3, 0xc0; bltu t2, t3, .Lbara_fail\n" ++
  "  li t3, 0xf8; bltu t2, t3, .Lbara_short_outer\n" ++
  "  li t3, 0xf7; sub t4, t2, t3; addi t4, t4, 1; add s9, s3, t4; j .Lbara_have_cursor\n" ++
  ".Lbara_short_outer:\n" ++
  "  addi s9, s3, 1\n" ++
  ".Lbara_have_cursor:\n" ++
  "  li s8, 0                    # i\n" ++
  ".Lbara_loop:\n" ++
  "  beq s8, s5, .Lbara_ok\n" ++
  "  la t0, bara_bal_end; ld t0, 0(t0); bgeu s9, t0, .Lbara_fail\n" ++
  "  mv a0, s9; jal ra, rlp_item_size; mv t6, a0\n" ++
  "  add t0, s9, t6; la t1, bara_bal_end; ld t1, 0(t1); bgtu t0, t1, .Lbara_fail\n" ++
  "  la t1, bara_next_item; sd t0, 0(t1)\n" ++
  "  la t1, bara_item_len; sd t6, 0(t1)\n" ++
  "  mv a0, s9; mv a1, t6\n" ++
  "  jal ra, bal_account_has_state_change\n" ++
  "  li t0, 1; beq a0, t0, .Lbara_changed\n" ++
  "  bnez a0, .Lbara_fail\n" ++
  "  la s9, bara_empty_account; li t1, 70; li t2, 3; j .Lbara_record\n" ++
  ".Lbara_changed:\n" ++
  "  la t0, bara_skip_modeled_system; ld t0, 0(t0); beqz t0, .Lbara_walk_changed\n" ++
  "  mv a0, s9; la t0, bara_item_len; ld a1, 0(t0)\n" ++
  "  jal ra, bal_account_is_modeled_system\n" ++
  "  li t0, 1; beq a0, t0, .Lbara_modeled_system\n" ++
  "  li t0, 2; beq a0, t0, .Lbara_modeled_system\n" ++
  "  bnez a0, .Lbara_fail\n" ++
  ".Lbara_walk_changed:\n" ++
  "  mv a0, s9; la t0, bara_item_len; ld a1, 0(t0)\n" ++
  "  la a2, bara_path\n" ++
  "  jal ra, bal_account_path\n" ++
  "  bnez a0, .Lbara_fail\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; la a3, bara_path; li a4, 64\n" ++
  "  la a5, bara_acct; la a6, bara_acct_len\n" ++
  "  jal ra, mpt_walk\n" ++
  "  beqz a0, .Lbara_found\n" ++
  "  li t0, 1; bne a0, t0, .Lbara_fail\n" ++
  "  la s9, bara_empty_account\n" ++
  "  li t1, 70\n" ++
  "  li t2, 1                    # is_insert\n" ++
  "  j .Lbara_record\n" ++
  ".Lbara_found:\n" ++
  "  la s9, bara_acct\n" ++
  "  la t0, bara_acct_len; ld t1, 0(t0)\n" ++
  "  li t0, 256; bgtu t1, t0, .Lbara_fail\n" ++
  "  li t2, 0                    # modify existing\n" ++
  "  j .Lbara_record\n" ++
  ".Lbara_modeled_system:\n" ++
  "  la s9, bara_empty_account; li t1, 70; li t2, 3\n" ++
  ".Lbara_record:\n" ++
  "  mv a0, s7; mv a1, s9; mv a2, t1\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  slli t0, s8, 4; slli t3, s8, 3; add t0, t0, t3; add t0, s6, t0\n" ++
  "  sd s7, 0(t0); sd t1, 8(t0); sd t2, 16(t0)\n" ++
  "  add s7, s7, t1; addi s7, s7, 7; andi s7, s7, -8\n" ++
  "  la t0, bara_next_item; ld s9, 0(t0)\n" ++
  "  addi s8, s8, 1\n" ++
  "  j .Lbara_loop\n" ++
  ".Lbara_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbara_ret\n" ++
  ".Lbara_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbara_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_bal_account_record_array`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  witness length (u64)
      +16 n (u64)
      +24 BAL list length (u64)
      +32 root hash (32 bytes)
      +64 BAL AccountChanges list bytes, padded to 8 bytes
      then witness section
    Output layout:
      OUTPUT+0  = status
      OUTPUT+8  = records
      OUTPUT+64 = account arena. -/
def ziskBalAccountRecordArrayPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # witness len\n" ++
  "  ld a5, 16(t0)               # n\n" ++
  "  ld a4, 24(t0)               # BAL list len\n" ++
  "  addi a0, t0, 32             # root hash ptr\n" ++
  "  addi a3, t0, 64             # BAL list ptr\n" ++
  "  add t1, a3, a4; addi t1, t1, 7; andi t1, t1, -8\n" ++
  "  mv a1, t1                   # witness ptr\n" ++
  "  li a6, 0xa0010008           # records out\n" ++
  "  li a7, 0xa0010040           # account arena out\n" ++
  "  jal ra, bal_account_record_array\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  j .Lbara_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  balAccountHasStateChangeFunction ++ "\n" ++
  balAccountIsModeledSystemFunction ++ "\n" ++
  balAccountPathFunction ++ "\n" ++
  balAccountRecordArrayFunction ++ "\n" ++
  ".Lbara_pdone:"

def ziskBalAccountRecordArrayDataSection : String :=
  ziskMptWalkDataSection ++ "\n" ++
  ziskBalAccountHasStateChangeDataSection ++ "\n" ++
  ziskBalAccountIsModeledSystemDataSection ++ "\n" ++
  ".balign 8\n" ++
  "bara_skip_modeled_system:\n  .zero 8\n" ++
  "bara_item_off:\n  .zero 8\n" ++
  "bara_item_len:\n  .zero 8\n" ++
  "bara_acct_len:\n  .zero 8\n" ++
  "bara_bal_end:\n  .zero 8\n" ++
  "bara_next_item:\n  .zero 8\n" ++
  "bacp_off:\n  .zero 8\n" ++
  "bacp_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bacp_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bara_path:\n  .zero 64\n" ++
  "bara_acct:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "bara_empty_account:\n" ++
  "  .byte 0xf8,0x44,0x80,0x80,0xa0\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  "  .byte 0xa0\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  ".balign 8\n" ++
  "bara_pad:\n  .zero 8"

def ziskBalAccountRecordArrayProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountRecordArrayPrologue
  dataAsm     := ziskBalAccountRecordArrayDataSection
}

end EvmAsm.Codegen
