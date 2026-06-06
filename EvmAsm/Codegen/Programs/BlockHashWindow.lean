/-
  EvmAsm.Codegen.Programs.BlockHashWindow

  BLOCKHASH window helpers split out of BlockHashPredicates.lean.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BlockHashPredicates

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## blockhash_opcode_windowed

    Full witness-side implementation of the EVM `BLOCKHASH(n)`
    opcode -- with the spec-mandated 256-block window check.

    Distinct from PR #7147 `blockhash_from_witness_headers`,
    which is just the raw lookup (caller already knows the
    target is in range). This primitive does the WHOLE opcode:

      1. Extract the executing block's number `cur` from the
         caller-supplied current header RLP.
      2. Apply the EVM window check:
           - target >= cur          -> return 0
             (BLOCKHASH(self/future) is undefined)
           - cur > 0 and target + 256 < cur
             (equivalently target < cur - 256)
             -> return 0           (older than the window)
           - else: in-window; continue.
      3. Look up the matching header in witness.headers by
         number (reuses the iteration from PR #7147).
      4. Return keccak256(matched_header).

    Returning 0 for out-of-window queries (rather than failing)
    is the spec-defining edge case. A naive
    `blockhash_from_witness_headers` would happily return 0 for
    those simply because the witness doesn't contain `cur` or
    far-past blocks, but that masks the real bug -- the EVM
    spec says BLOCKHASH must return 0 even when the witness
    HAPPENS to contain the relevant header (e.g. BLOCKHASH(self)
    returns 0 even with the current header in witness).

    Calling convention:
      a0 (input)  : current header_rlp ptr
      a1 (input)  : current header_rlp_len
      a2 (input)  : target block number (u64)
      a3 (input)  : witness.headers section ptr
      a4 (input)  : witness.headers section_len
      a5 (input)  : 32-byte output ptr (block hash)
      ra (input)  : return

      a0 (output) :
        0 = success (output filled per BLOCKHASH semantic;
            may be all zeros for out-of-window queries)
        4 = current header parse / number extract fail
        5 = in-window but target not found in witness.headers
            (witness integrity violation)

    The BLOCKHASH window is hard-coded to 256 blocks here. For
    EIP-2935's larger window in Amsterdam+, callers wrap this
    primitive with the configured cap.
-/
def blockhashOpcodeWindowedFunction : String :=
  "blockhash_opcode_windowed:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                  # current header_rlp ptr\n" ++
  "  mv s1, a1                  # current header_rlp_len\n" ++
  "  mv s2, a2                  # target block number\n" ++
  "  mv s3, a3                  # witness.headers ptr\n" ++
  "  mv s4, a4                  # witness.headers len\n" ++
  "  mv s5, a5                  # 32-byte output ptr\n" ++
  "  # Pre-zero output (covers all return-zero paths).\n" ++
  "  sd zero,  0(s5); sd zero,  8(s5); sd zero, 16(s5); sd zero, 24(s5)\n" ++
  "  # Step 1: extract current block number.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, bhow_cur_num\n" ++
  "  jal ra, header_extract_number\n" ++
  "  beqz a0, .Lbhow_step2\n" ++
  "  li a0, 4\n" ++
  "  j .Lbhow_ret\n" ++
  ".Lbhow_step2:\n" ++
  "  la t0, bhow_cur_num\n" ++
  "  ld s6, 0(t0)                # s6 = cur\n" ++
  "  # Step 2a: if target >= cur -> return 0.\n" ++
  "  bgeu s2, s6, .Lbhow_zero_success\n" ++
  "  # Step 2b: if cur - target > 256 -> return 0.\n" ++
  "  sub s7, s6, s2              # s7 = cur - target (> 0 here)\n" ++
  "  li t0, 256\n" ++
  "  bgtu s7, t0, .Lbhow_zero_success\n" ++
  "  # Step 3: in-window. Look up target in witness.headers.\n" ++
  "  mv a0, s2                   # target block number\n" ++
  "  mv a1, s3                   # witness.headers ptr\n" ++
  "  mv a2, s4                   # witness.headers len\n" ++
  "  mv a3, s5                   # block hash output\n" ++
  "  la a4, bhow_match_offset\n" ++
  "  la a5, bhow_match_length\n" ++
  "  jal ra, blockhash_from_witness_headers\n" ++
  "  beqz a0, .Lbhow_ret         # hit -> output filled, status 0\n" ++
  "  # 1 = miss (in-window but absent) -> status 5\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lbhow_integrity\n" ++
  "  # 2 = parse fail -> status 5 (witness has bad header in window)\n" ++
  "  li a0, 5\n" ++
  "  # Re-zero output in case blockhash_from_witness_headers wrote partial.\n" ++
  "  sd zero,  0(s5); sd zero,  8(s5); sd zero, 16(s5); sd zero, 24(s5)\n" ++
  "  j .Lbhow_ret\n" ++
  ".Lbhow_integrity:\n" ++
  "  li a0, 5\n" ++
  "  j .Lbhow_ret\n" ++
  ".Lbhow_zero_success:\n" ++
  "  # Out-of-window queries return 0 per spec, status 0.\n" ++
  "  li a0, 0\n" ++
  ".Lbhow_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-! ## witness_headers_max_block_number

    Walk an SSZ `witness.headers` list section and compute the
    maximum `block.number` across all entries. Returns the
    maximum as a u64, or 0 on an empty section.
-/
def witnessHeadersMaxBlockNumberFunction : String :=
  "witness_headers_max_block_number:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # max_out ptr\n" ++
  "  mv s3, a3                  # n_processed out ptr\n" ++
  "  li s7, 0                   # s7 = running max (init to 0)\n" ++
  "  sd s7, 0(s2)\n" ++
  "  sd zero, 0(s3)\n" ++
  "  beqz s1, .Lwhmax_ok          # empty section ⇒ max = 0\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s4, t0, 2               # s4 = N\n" ++
  "  li s5, 0                     # s5 = i\n" ++
  ".Lwhmax_loop:\n" ++
  "  beq s5, s4, .Lwhmax_ok\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add a0, s0, t2               # el_i_start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lwhmax_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4\n" ++
  "  j .Lwhmax_have_end\n" ++
  ".Lwhmax_use_end:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lwhmax_have_end:\n" ++
  "  sub a1, t4, a0               # el_i_len\n" ++
  "  la a2, whmax_num_buf\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Lwhmax_parse_fail\n" ++
  "  la t0, whmax_num_buf\n" ++
  "  ld t1, 0(t0)\n" ++
  "  bleu t1, s7, .Lwhmax_skip   # current <= running max\n" ++
  "  mv s7, t1\n" ++
  ".Lwhmax_skip:\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lwhmax_loop\n" ++
  ".Lwhmax_parse_fail:\n" ++
  "  sd s5, 0(s3)\n" ++
  "  li a0, 2\n" ++
  "  j .Lwhmax_ret\n" ++
  ".Lwhmax_ok:\n" ++
  "  sd s7, 0(s2)                 # write max\n" ++
  "  sd s4, 0(s3)                 # n_processed = N (= 0 for empty)\n" ++
  "  li a0, 0\n" ++
  ".Lwhmax_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_blockhash_opcode_windowed`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : current_header_rlp_len (u64 LE)
      bytes 16..24 : witness_headers_len    (u64 LE)
      bytes 24..32 : target_block_number    (u64 LE)
      bytes 32..32+H              : current header_rlp
      bytes 32+H..32+H+WH         : witness.headers section
    Output layout:
      bytes  0.. 8 : status (0 / 4 / 5)
      bytes  8..40 : block hash (32 bytes; zeros for out-of-window
                     OR window-OK miss / error) -/
def ziskBlockhashOpcodeWindowedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # cur_header_len\n" ++
  "  ld t3, 16(t1)               # witness_headers_len\n" ++
  "  ld a2, 24(t1)               # target block number\n" ++
  "  addi a0, t1, 32             # cur_header ptr\n" ++
  "  mv a1, t2\n" ++
  "  add a3, a0, t2              # witness.headers ptr\n" ++
  "  mv a4, t3                   # witness_headers_len\n" ++
  "  li a5, 0xa0010008           # 32 B output\n" ++
  "  jal ra, blockhash_opcode_windowed\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbhow_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  blockhashFromWitnessHeadersFunction ++ "\n" ++
  blockhashOpcodeWindowedFunction ++ "\n" ++
  ".Lbhow_pdone:"

def ziskBlockhashOpcodeWindowedDataSection : String :=
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
  "bhfwh_number_buf:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bhow_cur_num:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bhow_match_offset:\n" ++
  "  .zero 8\n" ++
  "bhow_match_length:\n" ++
  "  .zero 8"

def ziskBlockhashOpcodeWindowedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockhashOpcodeWindowedPrologue
  dataAsm     := ziskBlockhashOpcodeWindowedDataSection
}

/-- `zisk_witness_headers_max_block_number`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : section_len (u64 LE)
      bytes 16..   : witness.headers section
    Output layout:
      bytes  0.. 8 : status (0 ok / 2 parse fail)
      bytes  8..16 : max_block_number (0 on empty section)
      bytes 16..24 : n_processed (= N on success;
                     failing index on fail) -/
def ziskWitnessHeadersMaxBlockNumberPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # section_len\n" ++
  "  addi a0, a5, 16             # section ptr\n" ++
  "  li a2, 0xa0010008\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, witness_headers_max_block_number\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwhmax_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  witnessHeadersMaxBlockNumberFunction ++ "\n" ++
  ".Lwhmax_pdone:"

def ziskWitnessHeadersMaxBlockNumberDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "whmax_num_buf:\n" ++
  "  .zero 8"

def ziskWitnessHeadersMaxBlockNumberProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessHeadersMaxBlockNumberPrologue
  dataAsm     := ziskWitnessHeadersMaxBlockNumberDataSection
}

end EvmAsm.Codegen
