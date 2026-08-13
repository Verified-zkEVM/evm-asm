/-
  EvmAsm.Codegen.Programs.BlockEmpty

  Empty-block receipt-root validator carved out of
  `EvmAsm.Codegen.Programs.BlockValidate` per the file-size hard cap.
  Hosts:

    K181  block_validate_empty_receipts_root

  Composes header and RLP helpers plus the Keccak bridge.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.HeaderChain
import EvmAsm.Codegen.Programs.Block

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_validate_empty_receipts_root -- PR-K181

    Header field 5 (`receipts_root`) equals `EMPTY_TRIE_ROOT`
    iff the block has zero transactions (since receipts only
    arise from txs -- withdrawals do not generate receipts).
    This primitive checks the predicate directly.

    Used by:
      * Empty-block validators (composed with K179 + K161 + K177).
      * Sanity-check on stateless inputs that claim zero txs.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out (is_valid: 1 if root matches the constant)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : header parse failure / field 5 missing
        2 : field 5 length != 32 -/
def blockValidateEmptyReceiptsRootFunction : String :=
  "block_validate_empty_receipts_root:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # header_rlp ptr\n" ++
  "  mv s1, a1                   # header_rlp len\n" ++
  "  mv s2, a2                   # is_valid out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # ---- Extract header.receipts_root (field 5) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, bverr_offset; la a4, bverr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbverr_parse_fail\n" ++
  "  la t0, bverr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lbverr_size_fail\n" ++
  "  la t0, bverr_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  la t4, bverr_empty_trie_root\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lbverr_neq\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lbverr_neq\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lbverr_neq\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lbverr_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbverr_ret\n" ++
  ".Lbverr_neq:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbverr_ret\n" ++
  ".Lbverr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbverr_ret\n" ++
  ".Lbverr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbverr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_validate_empty_receipts_root`: probe BuildUnit.
    Input layout:
      bytes 0..8 : header_rlp_len
      bytes 8..  : header_rlp
    Output layout:
      bytes 0..8  : status (0..2)
      bytes 8..16 : is_valid -/
def ziskBlockValidateEmptyReceiptsRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  addi a0, a7, 16             # header_rlp ptr\n" ++
  "  li a2, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_validate_empty_receipts_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbverr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  blockValidateEmptyReceiptsRootFunction ++ "\n" ++
  ".Lbverr_pdone:"

def ziskBlockValidateEmptyReceiptsRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bverr_offset:\n" ++
  "  .zero 8\n" ++
  "bverr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bverr_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21"


end EvmAsm.Codegen
