/-
  EvmAsm.Codegen.Programs.BlockHashAtStateRoot

  Reverse-direction conversion: given a state_root, find
  the matching header in witness.headers and return its
  block_hash (= keccak of that header's RLP bytes).

  Closes the state_root ↔ block_hash direction of the
  conversion grid.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_hash_at_state_root

    Linear scan: for each entry in witness.headers, extract
    its state_root via K201 and compare against target. On
    the first match, compute keccak of that header's bytes
    and return it as the block_hash.

    Use cases:
      * Trust transformation: caller has a state_root from a
        snapshot / oracle / bridge and wants the
        corresponding block_hash for use with primitives
        that expect a hash key (#7307, #7312, #7314, etc).
      * Cross-witness consistency: caller has state_root S
        from witness A; this primitive locates the
        corresponding block_hash within witness B (if any).

    Closes the state_root → block_hash direction within the
    conversion grid:

      state_root ↔ block_number (via #7380, #7429)
      block_hash ↔ block_number (via #7370, #7375)
      state_root ↔ block_hash   (via THIS, and the trivial
                                 reverse: block_hash → header
                                 via #7309 then header
                                 state_root extract)

    Calling convention (4 args):
      a0 (input)  : state_root ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : 32-byte block_hash out ptr
      ra (input)  : return

      a0 (output) :
        0 = success
        1 = no header has that state_root
        2 = state_root extract failed on some header during
            scan (only surfaces if no match found)
-/
def blockHashAtStateRootFunction : String :=
  "block_hash_at_state_root:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # target state_root\n" ++
  "  mv s1, a1                  # section ptr\n" ++
  "  mv s2, a2                  # section_len\n" ++
  "  mv s3, a3                  # block_hash out (32 B)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3)\n" ++
  "  sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li s7, 0                   # saw_parse_fail\n" ++
  "  beqz s2, .Lbhsr_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s4, t0, 2             # N\n" ++
  "  li s5, 0                   # i\n" ++
  ".Lbhsr_loop:\n" ++
  "  beq s5, s4, .Lbhsr_finish\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s6, s1, t2             # el_i_start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lbhsr_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lbhsr_have_end\n" ++
  ".Lbhsr_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lbhsr_have_end:\n" ++
  "  sub s8, t4, s6             # el_i_len\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s8\n" ++
  "  la a2, bhsr_state_root_scratch\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  bnez a0, .Lbhsr_parse_fail\n" ++
  "  la t0, bhsr_state_root_scratch\n" ++
  "  mv t1, s0\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lbhsr_step\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lbhsr_step\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lbhsr_step\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lbhsr_step\n" ++
  "  # Match -> keccak the matched header.\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s8\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  j .Lbhsr_ret\n" ++
  ".Lbhsr_parse_fail:\n" ++
  "  li s7, 1\n" ++
  ".Lbhsr_step:\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lbhsr_loop\n" ++
  ".Lbhsr_finish:\n" ++
  "  bnez s7, .Lbhsr_parse_status\n" ++
  ".Lbhsr_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbhsr_ret\n" ++
  ".Lbhsr_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Lbhsr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_block_hash_at_state_root`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..48 : state_root (32 bytes)
      bytes 48..   : witness.headers section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status (0..2)
      bytes  8..40 : block_hash (32 B) -/
def ziskBlockHashAtStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a2, 8(a6)                # witness_headers_len\n" ++
  "  addi a0, a6, 16             # state_root ptr\n" ++
  "  addi a1, a6, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # block_hash out\n" ++
  "  jal ra, block_hash_at_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbhsr_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  blockHashAtStateRootFunction ++ "\n" ++
  ".Lbhsr_pdone:"

def ziskBlockHashAtStateRootDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "bhsr_state_root_scratch:\n" ++
  "  .zero 32"


end EvmAsm.Codegen
