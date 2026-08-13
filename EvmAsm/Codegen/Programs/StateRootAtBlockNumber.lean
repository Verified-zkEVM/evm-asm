/-
  EvmAsm.Codegen.Programs.StateRootAtBlockNumber

  Number-keyed state_root extractor. Scans witness.headers
  for the header matching target_block_number, then
  extracts its state_root field.

  Bridges block heights (which appear in logs/events/EIP
  references) and state_roots (the canonical input to the
  inclusion-proof family).

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.HeaderU64
import EvmAsm.Codegen.Programs.HeaderFields

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## state_root_at_block_number

    Linear scan of witness.headers; for each entry extract
    its block.number via K233 and compare against target.
    On first match, extract its state_root via K201.

    Use cases:
      * EIP-2935 / system-contract emulation: caller has a
        block_number from a precompile / log and wants the
        state_root at that height to verify storage claims.
      * Bridge audit at height N: feed the returned
        state_root into #7193/#7197/etc.
      * Replay validation: caller wants state_root at
        block_number to validate that a state-dependent
        transaction would have seen the expected state.

    Distinct from siblings:
      | PR     | key            | output       |
      |--------|----------------|--------------|
      | #7271  | header_idx     | state_root   |
      | this   | block_number   | state_root   |

    Calling convention (4 args):
      a0 (input)  : target_block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : 32-byte state_root out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (state_root written)
        1 = no header has that block_number
        2 = K233 RLP parse failure during scan
        3 = state_root field size unexpected on the matched
            header
-/
def stateRootAtBlockNumberFunction : String :=
  "state_root_at_block_number:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # target block_number\n" ++
  "  mv s1, a1                  # section ptr\n" ++
  "  mv s2, a2                  # section_len\n" ++
  "  mv s3, a3                  # state_root out (32 B)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3)\n" ++
  "  sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li s7, 0                   # saw_parse_fail flag\n" ++
  "  beqz s2, .Lsrbn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s4, t0, 2             # N\n" ++
  "  li s5, 0                   # i\n" ++
  ".Lsrbn_loop:\n" ++
  "  beq s5, s4, .Lsrbn_finish\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s6, s1, t2             # el_i_start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lsrbn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lsrbn_have_end\n" ++
  ".Lsrbn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lsrbn_have_end:\n" ++
  "  sub s8, t4, s6             # el_i_len\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s8\n" ++
  "  la a2, srbn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Lsrbn_parse_fail\n" ++
  "  la t0, srbn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Lsrbn_hit\n" ++
  "  j .Lsrbn_step\n" ++
  ".Lsrbn_parse_fail:\n" ++
  "  li s7, 1\n" ++
  ".Lsrbn_step:\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lsrbn_loop\n" ++
  ".Lsrbn_hit:\n" ++
  "  # K201 on matched header -> state_root.\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s8\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lsrbn_done\n" ++
  "  li a0, 3\n" ++
  "  j .Lsrbn_ret\n" ++
  ".Lsrbn_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lsrbn_ret\n" ++
  ".Lsrbn_finish:\n" ++
  "  bnez s7, .Lsrbn_parse_status\n" ++
  ".Lsrbn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Lsrbn_ret\n" ++
  ".Lsrbn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Lsrbn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_state_root_at_block_number`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : target_block_number (u64 LE)
      bytes 24..   : witness.headers section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..40 : state_root (32 B; zero on miss) -/
def ziskStateRootAtBlockNumberPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a2, 8(a6)                # witness_headers_len\n" ++
  "  ld a0, 16(a6)               # target_block_number\n" ++
  "  addi a1, a6, 24             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # state_root out\n" ++
  "  jal ra, state_root_at_block_number\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsrbn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  stateRootAtBlockNumberFunction ++ "\n" ++
  ".Lsrbn_pdone:"

def ziskStateRootAtBlockNumberDataSection : String :=
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
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "srbn_number_scratch:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
