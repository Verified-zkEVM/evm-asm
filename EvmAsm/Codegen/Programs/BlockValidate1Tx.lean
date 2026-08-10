/-
  EvmAsm.Codegen.Programs.BlockValidate1Tx

  One-transaction block validation probe.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Block
import EvmAsm.Codegen.Programs.TxRoot
import EvmAsm.Codegen.Programs.HeaderChain

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

def blockValidate1txFullFunction : String :=
  "block_validate_1tx_full:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # parent\n" ++
  "  mv s2, a2; mv s3, a3                # header\n" ++
  "  mv s4, a4; mv s5, a5                # tx0\n" ++
  "  mv s6, a6                            # is_valid out\n" ++
  "  sd zero, 0(s6)\n" ++
  "  # ---- (A) Header pair check ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s2; mv a3, s3\n" ++
  "  la a4, bv1f_pair_valid\n" ++
  "  jal ra, validate_header_pair\n" ++
  "  beqz a0, .Lbv1f_pair_status_ok\n" ++
  "  j .Lbv1f_ret                  # propagate pair status 1..4\n" ++
  ".Lbv1f_pair_status_ok:\n" ++
  "  la t0, bv1f_pair_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lbv1f_pred_false\n" ++
  "  # ---- (B) 1-tx tx_root check ----\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  mv a2, s4; mv a3, s5\n" ++
  "  la a4, bv1f_tx_root_valid\n" ++
  "  jal ra, block_validate_transactions_root_one_tx\n" ++
  "  beqz a0, .Lbv1f_tx_root_status_ok\n" ++
  "  addi a0, a0, 10               # remap 1..2 -> 11..12\n" ++
  "  j .Lbv1f_ret\n" ++
  ".Lbv1f_tx_root_status_ok:\n" ++
  "  la t0, bv1f_tx_root_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lbv1f_pred_false\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbv1f_ret\n" ++
  ".Lbv1f_pred_false:\n" ++
  "  sd zero, 0(s6)\n" ++
  "  li a0, 0\n" ++
  ".Lbv1f_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_block_validate_1tx_full`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : parent_rlp_len
      bytes  8..16 : header_rlp_len
      bytes 16..24 : tx0_len
      bytes 24..   : parent_rlp || header_rlp || tx0
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_valid -/
def ziskBlockValidate1txFullPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1,  8(a7)                # parent_rlp_len\n" ++
  "  ld a3, 16(a7)                # header_rlp_len\n" ++
  "  ld a5, 24(a7)                # tx0_len\n" ++
  "  addi a0, a7, 32              # parent_rlp ptr\n" ++
  "  add a2, a0, a1               # header_rlp ptr\n" ++
  "  add a4, a2, a3               # tx0 ptr\n" ++
  "  li a6, 0xa0010008            # is_valid out\n" ++
  "  jal ra, block_validate_1tx_full\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbv1f_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptOneLeafRootIndexedFunction ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  blockValidateTransactionsRootOneTxFunction ++ "\n" ++
  blockValidate1txFullFunction ++ "\n" ++
  ".Lbv1f_pdone:"

def ziskBlockValidate1txFullDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "vphl_offset:\n" ++
  "  .zero 8\n" ++
  "vphl_length:\n" ++
  "  .zero 8\n" ++
  "vphl_claimed:\n" ++
  "  .zero 32\n" ++
  "vphl_computed:\n" ++
  "  .zero 32\n" ++
  "vhp_link_valid:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_number:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vhp_child_number:\n" ++
  "  .zero 8\n" ++
  "vhp_child_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_child_gas_limit:\n" ++
  "  .zero 8\n" ++
  "mlnen_field_len:\n" ++
  "  .zero 8\n" ++
  "mlnen_hp_len:\n" ++
  "  .zero 8\n" ++
  "mlnen_cursor:\n" ++
  "  .zero 8\n" ++
  "mlnen_total_payload:\n" ++
  "  .zero 8\n" ++
  "mlnen_hp_buf:\n" ++
  "  .zero 1024\n" ++
  "mlnen_payload_buf:\n" ++
  "  .zero 16384\n" ++
  "mtoli_nibbles:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "mtoli_leaf_len:\n" ++
  "  .zero 8\n" ++
  "mtoli_leaf_buf:\n" ++
  "  .zero 16384\n" ++
  "bvtr1_offset:\n" ++
  "  .zero 8\n" ++
  "bvtr1_length:\n" ++
  "  .zero 8\n" ++
  "bvtr1_claimed_root:\n" ++
  "  .zero 32\n" ++
  "bvtr1_computed_root:\n" ++
  "  .zero 32\n" ++
  "bv1f_pair_valid:\n" ++
  "  .zero 8\n" ++
  "bv1f_tx_root_valid:\n" ++
  "  .zero 8"

def ziskBlockValidate1txFullProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidate1txFullPrologue
  dataAsm     := ziskBlockValidate1txFullDataSection
}

end EvmAsm.Codegen
