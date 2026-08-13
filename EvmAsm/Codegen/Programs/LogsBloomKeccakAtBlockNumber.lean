/-
  EvmAsm.Codegen.Programs.LogsBloomKeccakAtBlockNumber

  Number-keyed `keccak256(logs_bloom)` extractor for a
  historical block. Reuses the existing
  `header_extract_logs_bloom` (from `Bloom.lean`) + K233
  (header_extract_number) + K3 (zkvm_keccak256).

  Returns a 32-byte hash rather than the raw 256-byte
  bloom, sidestepping the ziskemu OUTPUT region's
  practical 256-byte cap while keeping a verifiable
  bloom-attestation primitive useful for light-client
  log-filter routing.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.HeaderU64
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.Bloom

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## logs_bloom_keccak_at_block_number

    Number-keyed primitive returning `keccak256(logs_bloom)`
    at a specific historical block.

    Pipeline:
      witness.headers ∋ ?h with h.block.number == target  [K233]
      h -> header_extract_logs_bloom -> 256 B scratch     [K_LB]
      keccak256(bloom) -> 32 B output                     [K3]

    Why hash instead of raw bloom: ziskemu's OUTPUT region
    is practically capped near 256 bytes. The raw bloom
    alone fills that, leaving no room for status. By
    returning keccak256 we get a compact 32 B summary that
    callers can verify by re-keccaking their independent
    copy of the bloom.

    Use cases:
      * Bloom-attestation oracle: caller has a candidate
        bloom from off-chain; ask this primitive whether
        its keccak matches the on-chain bloom at block N.
      * Bloom-equality across blocks: chain two calls with
        different numbers and compare returned hashes to
        detect whether the bloom (and thus the log
        topic-set) changed.
      * Compact commitment to bloom-history for downstream
        light-client routing.

    Calling convention (4 args):
      a0 (input)  : target_block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : 32-byte keccak out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (32 B keccak written)
        1 = no header with target block_number
        2 = K233 parse failure during scan
        3 = matched header logs_bloom extraction failed
            (RLP malformed / wrong field size)
-/
def logsBloomKeccakAtBlockNumberFunction : String :=
  "logs_bloom_keccak_at_block_number:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # target_block_number\n" ++
  "  mv s1, a1                  # headers ptr\n" ++
  "  mv s2, a2                  # headers len\n" ++
  "  mv s3, a3                  # output ptr (32 B)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li s8, 0                   # saw_parse_fail\n" ++
  "  beqz s2, .Llbkbn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s4, t0, 2             # N\n" ++
  "  li s5, 0                   # i\n" ++
  ".Llbkbn_loop:\n" ++
  "  beq s5, s4, .Llbkbn_finish\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s6, s1, t2             # header start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Llbkbn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Llbkbn_have_end\n" ++
  ".Llbkbn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Llbkbn_have_end:\n" ++
  "  sub s7, t4, s6\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  la a2, lbkbn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Llbkbn_parse_fail\n" ++
  "  la t0, lbkbn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Llbkbn_hit\n" ++
  "  j .Llbkbn_step\n" ++
  ".Llbkbn_parse_fail:\n" ++
  "  li s8, 1\n" ++
  ".Llbkbn_step:\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Llbkbn_loop\n" ++
  ".Llbkbn_hit:\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  la a2, lbkbn_bloom_scratch\n" ++
  "  jal ra, header_extract_logs_bloom\n" ++
  "  beqz a0, .Llbkbn_keccak\n" ++
  "  li a0, 3\n" ++
  "  j .Llbkbn_ret\n" ++
  ".Llbkbn_keccak:\n" ++
  "  la a0, lbkbn_bloom_scratch\n" ++
  "  li a1, 256\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  j .Llbkbn_ret\n" ++
  ".Llbkbn_finish:\n" ++
  "  bnez s8, .Llbkbn_parse_status\n" ++
  ".Llbkbn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Llbkbn_ret\n" ++
  ".Llbkbn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Llbkbn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_logs_bloom_keccak_at_block_number`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : target_block_number (u64 LE)
      bytes 24..   : witness.headers
    Output layout (40 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..40 : keccak256(logs_bloom) (32 B; 0 on failure) -/
def ziskLogsBloomKeccakAtBlockNumberPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a0, 16(t4)               # target_block_number\n" ++
  "  addi a1, t4, 24             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # 32 B output ptr\n" ++
  "  jal ra, logs_bloom_keccak_at_block_number\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Llbkbn_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  headerExtractLogsBloomFunction ++ "\n" ++
  logsBloomKeccakAtBlockNumberFunction ++ "\n" ++
  ".Llbkbn_pdone:"

def ziskLogsBloomKeccakAtBlockNumberDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
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
  "lbkbn_number_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "lbkbn_bloom_scratch:\n" ++
  "  .zero 256"


end EvmAsm.Codegen
