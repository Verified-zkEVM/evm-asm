/-
  EvmAsm.Codegen.Programs.LogsBloomKeccakAtBlockHash

  Hash-keyed `keccak256(logs_bloom)` extractor. Mirror of
  the just-opened `logs_bloom_keccak_at_block_number`
  (PR 7524) but takes a `block_hash` as the key instead of
  block_number.

  Like the number-keyed sibling, returns a 32-byte hash
  rather than the raw 256-byte bloom to sidestep ziskemu's
  practical 256-byte OUTPUT cap.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.Bloom

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## logs_bloom_keccak_at_block_hash

    Hash-keyed primitive returning `keccak256(logs_bloom)`
    at a specific historical block, looked up by block_hash.

    Pipeline:
      witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
      h -> header_extract_logs_bloom -> 256 B scratch    [K_LB]
      keccak256(bloom) -> 32 B output                    [K3]

    Distinguishes from `logs_bloom_keccak_at_block_number`
    (PR 7524) in the keying path: K19 by hash is O(N) keccak
    operations on the header bytes, whereas K233 by number
    is O(N) header_extract_number RLP parses. Caller picks
    the cheaper path based on which key they have.

    Use cases:
      * Bridge-driven bloom attestation: caller has a known
        block_hash (e.g. from a parent header chain) and
        wants a compact commitment to its bloom.
      * Cross-witness consistency: compare logs_bloom_keccak
        across two witnesses that share a block_hash.

    Calling convention (4 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : 32-byte keccak out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (32 B keccak written)
        1 = block_hash not in witness.headers
        2 = matched header logs_bloom extraction failed
            (RLP malformed / field 6 not exactly 256 B)
-/
def logsBloomKeccakAtBlockHashFunction : String :=
  "logs_bloom_keccak_at_block_hash:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # output ptr (32 B)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, lbkbh_match_offset\n" ++
  "  la a4, lbkbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Llbkbh_no_match\n" ++
  "  la t0, lbkbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s6, s1, t1\n" ++
  "  la t0, lbkbh_match_length\n" ++
  "  ld s7, 0(t0)\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  la a2, lbkbh_bloom_scratch\n" ++
  "  jal ra, header_extract_logs_bloom\n" ++
  "  beqz a0, .Llbkbh_keccak\n" ++
  "  li a0, 2\n" ++
  "  j .Llbkbh_ret\n" ++
  ".Llbkbh_keccak:\n" ++
  "  la a0, lbkbh_bloom_scratch\n" ++
  "  li a1, 256\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  j .Llbkbh_ret\n" ++
  ".Llbkbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Llbkbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_logs_bloom_keccak_at_block_hash`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..48 : block_hash (32 bytes)
      bytes 48..   : witness.headers
    Output layout (40 bytes):
      bytes  0.. 8 : status (0..2)
      bytes  8..40 : keccak256(logs_bloom) (32 B; 0 on failure) -/
def ziskLogsBloomKeccakAtBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  addi a0, t4, 16             # block_hash ptr\n" ++
  "  addi a1, t4, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # 32 B output ptr\n" ++
  "  jal ra, logs_bloom_keccak_at_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Llbkbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractLogsBloomFunction ++ "\n" ++
  logsBloomKeccakAtBlockHashFunction ++ "\n" ++
  ".Llbkbh_pdone:"

def ziskLogsBloomKeccakAtBlockHashDataSection : String :=
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
  "helb_offset:\n" ++
  "  .zero 8\n" ++
  "helb_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "lbkbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "lbkbh_match_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "lbkbh_bloom_scratch:\n" ++
  "  .zero 256"


end EvmAsm.Codegen
