/-
  EvmAsm.Codegen.Programs.NumberTimestampPairAtBlockHash

  Hash-keyed `(block.number, block.timestamp)` pair
  extractor (RLP fields 8 & 11, both u64). Composite that
  halves the keccak cost vs. calling
  `block_number_at_block_hash` and
  `timestamp_at_block_hash` separately.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderU64
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## number_timestamp_pair_at_block_hash

    Hash-keyed extractor for the
    `(block.number, block.timestamp)` pair (RLP fields 8 &
    11; both u64).

    Pipeline (composes K19 + existing K210 + K232; no new
    asm helpers):
      witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
      h -> header_extract_number    -> u64 (field 8)
      h -> header_extract_timestamp -> u64 (field 11)

    Why a composite over two singletons:
      Cross-chain replay-protection oracles, staleness
      windows ("is this block_hash newer than X seconds
      old?"), and CL <-> EL block-pinning routinely need
      both (number, timestamp) together. The two
      hash-keyed singletons would pay two keccak256s over
      the matched header; this pair shares the walk.

    Calling convention (4 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : 16-byte pair out ptr
                    out[0..8]  = block.number    (u64 LE)
                    out[8..16] = block.timestamp (u64 LE)
      ra (input)  : return

      a0 (output) :
        0 = success
        1 = block_hash not in witness.headers
        2 = block.number (field 8) extraction failed
        3 = block.timestamp (field 11) extraction failed
-/
def numberTimestampPairAtBlockHashFunction : String :=
  "number_timestamp_pair_at_block_hash:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # 16 B pair out\n" ++
  "  sd zero, 0(s3); sd zero, 8(s3)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, ntpbh_match_offset\n" ++
  "  la a4, ntpbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lntpbh_no_match\n" ++
  "  la t0, ntpbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s4, s1, t1\n" ++
  "  la t0, ntpbh_match_length\n" ++
  "  ld s5, 0(t0)\n" ++
  "  # Extract field 8 -> out[0..8]\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_number\n" ++
  "  beqz a0, .Lntpbh_ts\n" ++
  "  sd zero, 0(s3); sd zero, 8(s3)\n" ++
  "  li a0, 2\n" ++
  "  j .Lntpbh_ret\n" ++
  ".Lntpbh_ts:\n" ++
  "  # Extract field 11 -> out[8..16]\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  addi a2, s3, 8\n" ++
  "  jal ra, header_extract_timestamp\n" ++
  "  beqz a0, .Lntpbh_done\n" ++
  "  sd zero, 0(s3); sd zero, 8(s3)\n" ++
  "  li a0, 3\n" ++
  "  j .Lntpbh_ret\n" ++
  ".Lntpbh_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lntpbh_ret\n" ++
  ".Lntpbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lntpbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_number_timestamp_pair_at_block_hash`: probe BuildUnit.
    Output layout (24 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..16 : block.number    u64 LE (0 on failure)
      bytes 16..24 : block.timestamp u64 LE (0 on failure) -/
def ziskNumberTimestampPairAtBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  addi a0, t4, 16             # block_hash ptr\n" ++
  "  addi a1, t4, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # 16 B pair out\n" ++
  "  jal ra, number_timestamp_pair_at_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lntpbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  headerExtractTimestampFunction ++ "\n" ++
  numberTimestampPairAtBlockHashFunction ++ "\n" ++
  ".Lntpbh_pdone:"

def ziskNumberTimestampPairAtBlockHashDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "ntpbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "ntpbh_match_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
