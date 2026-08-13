/-
  EvmAsm.Codegen.Programs.BlockNumberAtStateRoot

  Reverse lookup: given a state_root, find the matching
  header in witness.headers and return its block.number.

  Inverse of #7380 (block_number -> state_root).

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

/-! ## block_number_at_state_root

    Linear scan over witness.headers; for each entry extract
    its state_root via K201 and compare against the target.
    On the first match, extract its block.number via K233
    and return.

    Use cases:
      * Pegging external trust: caller has a state_root from
        a bridge / oracle and wants to know which block height
        it corresponds to in this witness.
      * State-root provenance audit: verify a claimed
        state_root really matches a specific block by height.
      * Multi-witness reconciliation: caller has a state_root
        from witness A and wants to find it in witness B
        without re-scanning by hash.

    Inverse of #7380 (block_number -> state_root). Together
    they form a bidirectional bridge between block heights and
    state_roots in the witness.

    Calling convention (4 args):
      a0 (input)  : state_root ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : u64 block_number out ptr
      ra (input)  : return

      a0 (output) :
        0 = success
        1 = no header has that state_root
        2 = state_root extract failed on some header during
            scan (only surfaces if no match found)
        3 = matched header block.number RLP decode failure
-/
def blockNumberAtStateRootFunction : String :=
  "block_number_at_state_root:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # state_root ptr (target)\n" ++
  "  mv s1, a1                  # section ptr\n" ++
  "  mv s2, a2                  # section_len\n" ++
  "  mv s3, a3                  # u64 block_number out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s7, 0                   # saw_parse_fail\n" ++
  "  beqz s2, .Lbnsr_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s4, t0, 2             # N\n" ++
  "  li s5, 0                   # i\n" ++
  ".Lbnsr_loop:\n" ++
  "  beq s5, s4, .Lbnsr_finish\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s6, s1, t2             # el_i_start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lbnsr_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lbnsr_have_end\n" ++
  ".Lbnsr_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lbnsr_have_end:\n" ++
  "  sub s8, t4, s6             # el_i_len\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s8\n" ++
  "  la a2, bnsr_state_root_scratch\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  bnez a0, .Lbnsr_parse_fail\n" ++
  "  # Compare extracted state_root vs target.\n" ++
  "  la t0, bnsr_state_root_scratch\n" ++
  "  mv t1, s0\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lbnsr_step\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lbnsr_step\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lbnsr_step\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lbnsr_step\n" ++
  "  # Match -> extract number from this header.\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s8\n" ++
  "  mv a2, s3                  # u64 out (caller's buffer)\n" ++
  "  jal ra, header_extract_number\n" ++
  "  beqz a0, .Lbnsr_done\n" ++
  "  li a0, 3\n" ++
  "  j .Lbnsr_ret\n" ++
  ".Lbnsr_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbnsr_ret\n" ++
  ".Lbnsr_parse_fail:\n" ++
  "  li s7, 1\n" ++
  ".Lbnsr_step:\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lbnsr_loop\n" ++
  ".Lbnsr_finish:\n" ++
  "  bnez s7, .Lbnsr_parse_status\n" ++
  ".Lbnsr_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbnsr_ret\n" ++
  ".Lbnsr_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Lbnsr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_block_number_at_state_root`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..48 : state_root (32 bytes)
      bytes 48..   : witness.headers section bytes
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..16 : block_number (u64) -/
def ziskBlockNumberAtStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a2, 8(a6)                # witness_headers_len\n" ++
  "  addi a0, a6, 16             # state_root ptr\n" ++
  "  addi a1, a6, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # u64 block_number out\n" ++
  "  jal ra, block_number_at_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbnsr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  blockNumberAtStateRootFunction ++ "\n" ++
  ".Lbnsr_pdone:"

def ziskBlockNumberAtStateRootDataSection : String :=
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
  ".balign 32\n" ++
  "bnsr_state_root_scratch:\n" ++
  "  .zero 32"


end EvmAsm.Codegen
