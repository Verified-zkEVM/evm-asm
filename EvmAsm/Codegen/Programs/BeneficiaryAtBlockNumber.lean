/-
  EvmAsm.Codegen.Programs.BeneficiaryAtBlockNumber

  Number-keyed `header.beneficiary` extractor (RLP field 2,
  20 bytes -- the block proposer/miner address). Composes
  K233 + the existing `header_extract_beneficiary` (from
  HeaderFields.lean).

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

/-! ## beneficiary_at_block_number

    Number-keyed extractor for
    `header.block.beneficiary` (RLP field 2, 20 bytes -- the
    address that receives block rewards / priority fees /
    MEV).

    Pipeline (composes K233 scan + existing
    header_extract_beneficiary; no new helpers):
      witness.headers ∋ ?h with h.block.number == target  [K233]
      h -> header_extract_beneficiary -> 20 B

    Use cases:
      * Block-proposer attribution: who actually sealed
        block N? Useful for MEV attribution / staking
        rewards audit.
      * Coinbase opcode replay: callers replaying an EVM
        execution against a historical block need
        `block.coinbase` to evaluate `COINBASE`-opcode
        equivalence.
      * Post-merge fee-recipient audit: combined with
        gas_used + base_fee + priority_fee data, callers
        can verify total reward delta.

    Calling convention (4 args):
      a0 (input)  : target_block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : 20-byte beneficiary out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (beneficiary written)
        1 = no header with target block_number
        2 = K233 parse failure during scan
        3 = matched header beneficiary extraction failed
            (RLP malformed / field 2 size != 20)
-/
def beneficiaryAtBlockNumberFunction : String :=
  "beneficiary_at_block_number:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # target_block_number\n" ++
  "  mv s1, a1                  # headers ptr\n" ++
  "  mv s2, a2                  # headers len\n" ++
  "  mv s3, a3                  # beneficiary out (20 B)\n" ++
  "  # Pre-zero output byte-by-byte (20 bytes; 2x u64 + 1x u32).\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sw zero, 16(s3)\n" ++
  "  li s8, 0                   # saw_parse_fail\n" ++
  "  beqz s2, .Lbnbn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s4, t0, 2             # N\n" ++
  "  li s5, 0                   # i\n" ++
  ".Lbnbn_loop:\n" ++
  "  beq s5, s4, .Lbnbn_finish\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s6, s1, t2             # header start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lbnbn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lbnbn_have_end\n" ++
  ".Lbnbn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lbnbn_have_end:\n" ++
  "  sub s7, t4, s6\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  la a2, bnbn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Lbnbn_parse_fail\n" ++
  "  la t0, bnbn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Lbnbn_hit\n" ++
  "  j .Lbnbn_step\n" ++
  ".Lbnbn_parse_fail:\n" ++
  "  li s8, 1\n" ++
  ".Lbnbn_step:\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lbnbn_loop\n" ++
  ".Lbnbn_hit:\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_beneficiary\n" ++
  "  beqz a0, .Lbnbn_ret\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sw zero, 16(s3)\n" ++
  "  li a0, 3\n" ++
  "  j .Lbnbn_ret\n" ++
  ".Lbnbn_finish:\n" ++
  "  bnez s8, .Lbnbn_parse_status\n" ++
  ".Lbnbn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbnbn_ret\n" ++
  ".Lbnbn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Lbnbn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_beneficiary_at_block_number`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : target_block_number (u64 LE)
      bytes 24..   : witness.headers
    Output layout (28 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..28 : beneficiary (20 B; 0 on failure) -/
def ziskBeneficiaryAtBlockNumberPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a0, 16(t4)               # target_block_number\n" ++
  "  addi a1, t4, 24             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # 20 B beneficiary out\n" ++
  "  jal ra, beneficiary_at_block_number\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbnbn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  headerExtractBeneficiaryFunction ++ "\n" ++
  beneficiaryAtBlockNumberFunction ++ "\n" ++
  ".Lbnbn_pdone:"

def ziskBeneficiaryAtBlockNumberDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "hebe_offset:\n" ++
  "  .zero 8\n" ++
  "hebe_length:\n" ++
  "  .zero 8\n" ++
  "bnbn_number_scratch:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
