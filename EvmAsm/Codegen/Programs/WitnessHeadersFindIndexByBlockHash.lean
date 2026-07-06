/-
  EvmAsm.Codegen.Programs.WitnessHeadersFindIndexByBlockHash

  Pure search primitive: given a block_hash and
  witness.headers, return the index i such that
  keccak256(witness.headers[i]) == block_hash, or signal
  not-found.

  Hash -> index inverse of #7304 (which is index -> hash).
  Useful building block for hash-keyed flows that need to
  know the position (e.g. for downstream chain-link checks
  against neighbouring indices).

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.MptWitnessLookup

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## witness_headers_find_index_by_block_hash

    Resolve the header through `witness_lookup_by_hash`, then translate the
    returned SSZ element offset back to its list index. If the caller has built
    a `witness.headers` index with `witness_index_build`, the hash resolution is
    binary-search based and this helper only walks the offset table.

    On miss, sets index to 0 and returns status 1; caller
    distinguishes via status, not via the written index
    (so the output buffer's contents on miss aren't
    semantically meaningful).

    Inverse of #7304: that returns hash for a given index;
    this returns index for a given hash.

    Use cases:
      * Translate a hash-keyed query into an index-keyed
        downstream call (e.g. caller has block_hash, wants
        to chain into #7283 / #7296 which take indices).
      * Detect whether a claimed block_hash is in the
        witness chain without doing the full account walk
        of #7307.
      * Audit: find which position in the chain the trusted
        anchor block sits at.

    Calling convention (4 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : u64 index out ptr
      ra (input)  : return

      a0 (output) :
        0 = found (index written)
        1 = block_hash not in witness.headers
-/
def witnessHeadersFindIndexByBlockHashFunction : String :=
  "witness_headers_find_index_by_block_hash:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # section ptr\n" ++
  "  mv s2, a2                  # section_len\n" ++
  "  mv s3, a3                  # index out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd zero, 64(sp)            # matched offset scratch\n" ++
  "  sd zero, 72(sp)            # matched length scratch\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  addi a3, sp, 64\n" ++
  "  addi a4, sp, 72\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lwhfi_miss\n" ++
  "  ld s4, 64(sp)              # matched element offset within section\n" ++
  "  li t0, 4\n" ++
  "  bltu s2, t0, .Lwhfi_miss\n" ++
  "  lwu t0, 0(s1)              # first offset = 4 * N\n" ++
  "  andi t1, t0, 3\n" ++
  "  bnez t1, .Lwhfi_miss\n" ++
  "  bgtu t0, s2, .Lwhfi_miss\n" ++
  "  srli s5, t0, 2             # s5 = N\n" ++
  "  li s6, 0                   # s6 = i\n" ++
  ".Lwhfi_loop:\n" ++
  "  beq s6, s5, .Lwhfi_miss\n" ++
  "  slli t0, s6, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)              # offset_i\n" ++
  "  bgtu t2, s2, .Lwhfi_miss\n" ++
  "  beq t2, s4, .Lwhfi_found\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lwhfi_loop\n" ++
  ".Lwhfi_found:\n" ++
  "  sd s6, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lwhfi_ret\n" ++
  ".Lwhfi_miss:\n" ++
  "  li a0, 1\n" ++
  ".Lwhfi_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_witness_headers_find_index_by_block_hash`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..48 : block_hash (32 bytes)
      bytes 48..   : witness.headers section bytes
    The probe pre-builds the `witness.headers` index before calling the helper.
    Output layout (64 bytes):
      bytes  0.. 8 : status (0 = found, 1 = miss)
      bytes  8..16 : index (u64; 0 on miss)
      bytes 16..24 : index build status
      bytes 24..32 : witness_lookup_by_hash call count
      bytes 32..40 : indexed lookup call count
      bytes 40..48 : linear lookup call count
      bytes 48..56 : linear lookup iteration count
      bytes 56..64 : index build entry count -/
def ziskWitnessHeadersFindIndexByBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a2, 8(a6)                # witness_headers_len\n" ++
  "  addi a0, a6, 16             # block_hash ptr\n" ++
  "  addi a1, a6, 48             # witness.headers ptr\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, witness_index_build\n" ++
  "  li t0, 0xa0010010\n" ++
  "  sd a0, 0(t0)                # index build status\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s2\n" ++
  "  li a3, 0xa0010008           # index out\n" ++
  "  jal ra, witness_headers_find_index_by_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, wlh_lookup_calls; ld t2, 0(t1); sd t2, 24(t0)\n" ++
  "  la t1, wlh_indexed_calls; ld t2, 0(t1); sd t2, 32(t0)\n" ++
  "  la t1, wlh_linear_calls; ld t2, 0(t1); sd t2, 40(t0)\n" ++
  "  la t1, wlh_linear_iterations; ld t2, 0(t1); sd t2, 48(t0)\n" ++
  "  la t1, widx_build_count; ld t2, 0(t1); sd t2, 56(t0)\n" ++
  "  j .Lwhfi_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessHeadersFindIndexByBlockHashFunction ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  ".Lwhfi_pdone:"

def ziskWitnessHeadersFindIndexByBlockHashDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32"

def ziskWitnessHeadersFindIndexByBlockHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessHeadersFindIndexByBlockHashPrologue
  dataAsm     := ziskWitnessHeadersFindIndexByBlockHashDataSection
}

end EvmAsm.Codegen
