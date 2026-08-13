/-
  EvmAsm.Codegen.Programs.WithdrawalsRootAtBlockNumber

  Number-keyed `header.withdrawals_root` extractor (RLP
  field 16, 32 bytes -- the post-Shanghai consensus-layer
  withdrawals trie root). Composes K233 + the existing
  `header_extract_withdrawals_root` (from HeaderFields.lean).

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.HeaderU64
import EvmAsm.Codegen.Programs.HeaderFields

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## withdrawals_root_at_block_number

    Number-keyed extractor for
    `header.block.withdrawals_root` (RLP field 16, 32 bytes
    -- introduced in Shanghai for beacon-chain withdrawals).

    Pipeline (composes K233 scan + existing
    header_extract_withdrawals_root; no new helpers):
      witness.headers ∋ ?h with h.block.number == target  [K233]
      h -> header_extract_withdrawals_root -> 32 B

    Use cases:
      * Withdrawal-trie attestation: caller has an external
        merkle root for the block's beacon-chain
        withdrawals set; verify against the on-chain root.
      * Future withdrawal-inclusion proofs (e.g. for a
        validator proving their unstaking was finalized):
        pair with the existing MPT walk primitives.
      * Empty-withdrawals detection (rare; the EMPTY_TRIE
        case at this position is canonical for blocks with
        no withdrawals).

    Calling convention (4 args):
      a0 (input)  : target_block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : 32-byte withdrawals_root out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (withdrawals_root written)
        1 = no header with target block_number
        2 = K233 parse failure during scan
        3 = matched header withdrawals_root extraction failed
            (RLP malformed / field 16 size != 32)
-/
def withdrawalsRootAtBlockNumberFunction : String :=
  "withdrawals_root_at_block_number:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # target_block_number\n" ++
  "  mv s1, a1                  # headers ptr\n" ++
  "  mv s2, a2                  # headers len\n" ++
  "  mv s3, a3                  # withdrawals_root out (32 B)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li s8, 0                   # saw_parse_fail\n" ++
  "  beqz s2, .Lwrbn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s4, t0, 2             # N\n" ++
  "  li s5, 0                   # i\n" ++
  ".Lwrbn_loop:\n" ++
  "  beq s5, s4, .Lwrbn_finish\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s6, s1, t2             # header start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lwrbn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lwrbn_have_end\n" ++
  ".Lwrbn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lwrbn_have_end:\n" ++
  "  sub s7, t4, s6\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  la a2, wrbn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Lwrbn_parse_fail\n" ++
  "  la t0, wrbn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Lwrbn_hit\n" ++
  "  j .Lwrbn_step\n" ++
  ".Lwrbn_parse_fail:\n" ++
  "  li s8, 1\n" ++
  ".Lwrbn_step:\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lwrbn_loop\n" ++
  ".Lwrbn_hit:\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_withdrawals_root\n" ++
  "  beqz a0, .Lwrbn_ret\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li a0, 3\n" ++
  "  j .Lwrbn_ret\n" ++
  ".Lwrbn_finish:\n" ++
  "  bnez s8, .Lwrbn_parse_status\n" ++
  ".Lwrbn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Lwrbn_ret\n" ++
  ".Lwrbn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Lwrbn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_withdrawals_root_at_block_number`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : target_block_number (u64 LE)
      bytes 24..   : witness.headers
    Output layout (40 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..40 : withdrawals_root (32 B; 0 on failure) -/
def ziskWithdrawalsRootAtBlockNumberPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a0, 16(t4)               # target_block_number\n" ++
  "  addi a1, t4, 24             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # 32 B withdrawals_root out\n" ++
  "  jal ra, withdrawals_root_at_block_number\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwrbn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  headerExtractWithdrawalsRootFunction ++ "\n" ++
  withdrawalsRootAtBlockNumberFunction ++ "\n" ++
  ".Lwrbn_pdone:"

def ziskWithdrawalsRootAtBlockNumberDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "hewr_offset:\n" ++
  "  .zero 8\n" ++
  "hewr_length:\n" ++
  "  .zero 8\n" ++
  "wrbn_number_scratch:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
