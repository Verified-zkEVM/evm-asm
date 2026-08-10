/-
  EvmAsm.Codegen.Programs.Block

  Block hash helper lifted out of `EvmAsm.Codegen.Programs`
  per the file-size hard cap.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxBlobGas
import EvmAsm.Codegen.Programs.TxDecode
import EvmAsm.Codegen.Programs.TxBlobGas
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Programs.Header

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def blockComputeTxHashesFunction : String :=
  "block_compute_tx_hashes:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # txs_list ptr\n" ++
  "  mv s1, a1                   # txs_len\n" ++
  "  mv s2, a2                   # out hashes buffer\n" ++
  "  mv s3, a3                   # out count ptr\n" ++
  "  # Step 1: validate the list and initialize its cursor.\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  beqz a2, .Lbcth_loop_init\n" ++
  "  li a0, 101\n" ++
  "  j .Lbcth_ret\n" ++
  ".Lbcth_loop_init:\n" ++
  "  mv s4, a0                   # cursor\n" ++
  "  mv s5, a1                   # end\n" ++
  "  li s6, 0                    # N = tx_count\n" ++
  ".Lbcth_loop:\n" ++
  "  beq s4, s5, .Lbcth_done\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  beqz a1, .Lbcth_after_next\n" ++
  "  li a0, 201\n" ++
  "  j .Lbcth_ret\n" ++
  ".Lbcth_after_next:\n" ++
  "  mv s4, a0                   # preserve advanced cursor\n" ++
  "  sub a0, a0, a2              # tx_ptr = advanced - content_len\n" ++
  "  mv a1, a2                   # tx_len\n" ++
  "  slli t0, s6, 5              # i × 32\n" ++
  "  add a2, s2, t0              # &out[i*32]\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lbcth_loop\n" ++
  ".Lbcth_done:\n" ++
  "  sd s6, 0(s3)                # *count = N\n" ++
  "  li a0, 0\n" ++
  ".Lbcth_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_block_compute_tx_hashes`: probe BuildUnit. Reads
    (txs_list_len, txs_list_bytes) from host input, writes
    (status, count, N × 32-byte hashes) to OUTPUT. The host caller
    must size OUTPUT for at least 16 + N × 32 bytes.
    Input layout:
      bytes  0.. 8 : txs_list_len
      bytes  8..   : txs_list RLP bytes
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : count (u64 LE)
      bytes 16..   : N concatenated 32-byte hashes -/
def ziskBlockComputeTxHashesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # txs_list_len\n" ++
  "  addi a0, a4, 16             # txs_list ptr\n" ++
  "  li a2, 0xa0010010           # hashes buffer (OUTPUT + 16)\n" ++
  "  li a3, 0xa0010008           # count ptr (OUTPUT + 8)\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, block_compute_tx_hashes\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbcth_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  blockComputeTxHashesFunction ++ "\n" ++
  ".Lbcth_pdone:"

def ziskBlockComputeTxHashesDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "bcth_count:\n" ++
  "  .zero 8\n" ++
  "bcth_item_off:\n" ++
  "  .zero 8\n" ++
  "bcth_item_len:\n" ++
  "  .zero 8"

def ziskBlockComputeTxHashesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockComputeTxHashesPrologue
  dataAsm     := ziskBlockComputeTxHashesDataSection
}

end EvmAsm.Codegen
