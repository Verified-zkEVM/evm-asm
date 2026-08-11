/-
  EvmAsm.Codegen.Programs.BaseFeePerGasAtBlockHash

  Hash-keyed `header.base_fee_per_gas` extractor. Mirror of
  `base_fee_per_gas_at_block_number` (PR 7639) but takes a
  block_hash key. Reuses the same
  `header_extract_base_fee_u64` helper introduced there.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderU64

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## header_extract_base_fee_u64_bh

    Local helper duplicating the same RLP-field-15 extract
    pattern (rebadged to avoid def collision with the
    sibling block_number PR). Once both land, one can be
    removed in a follow-up.
-/
def headerExtractBaseFeeU64BhFunction : String :=
  "header_extract_base_fee_u64_bh:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  mv a3, a2\n" ++
  "  li a2, 15\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-! ## base_fee_per_gas_at_block_hash

    Hash-keyed extractor for
    `header.block.base_fee_per_gas` (RLP field 15, u64 BE
    in practice; Uint in spec).

    Pipeline (composes K19 + the
    `header_extract_base_fee_u64` helper from
    BaseFeePerGasAtBlockNumber.lean; no other new helpers):
      witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
      h -> header_extract_base_fee_u64 -> u64

    Use cases:
      * Bridge-driven base-fee oracle: caller has a known
        block_hash + an off-chain claim about base_fee;
        verify directly.
      * Cross-witness consistency: two witnesses sharing a
        block_hash must agree on base_fee.
      * Reorg detection: two block_hashes claiming the same
        block.number but differing base_fee point to a
        chain split.

    Calling convention (4 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : u64 base_fee_per_gas out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (base_fee written)
        1 = block_hash not in witness.headers
        2 = matched header base_fee extraction failed
            (RLP malformed / field 15 > 8 bytes / pre-1559
            header)
-/
def baseFeePerGasAtBlockHashFunction : String :=
  "base_fee_per_gas_at_block_hash:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # base_fee u64 out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, bfbh_match_offset\n" ++
  "  la a4, bfbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lbfbh_no_match\n" ++
  "  la t0, bfbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s4, s1, t1\n" ++
  "  la t0, bfbh_match_length\n" ++
  "  ld s5, 0(t0)\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_base_fee_u64_bh\n" ++
  "  beqz a0, .Lbfbh_ret\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 2\n" ++
  "  j .Lbfbh_ret\n" ++
  ".Lbfbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lbfbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_base_fee_per_gas_at_block_hash`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..48 : block_hash (32 bytes)
      bytes 48..   : witness.headers
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..2)
      bytes  8..16 : base_fee_per_gas (u64; 0 on failure) -/
def ziskBaseFeePerGasAtBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  addi a0, t4, 16             # block_hash ptr\n" ++
  "  addi a1, t4, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # u64 base_fee out\n" ++
  "  jal ra, base_fee_per_gas_at_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbfbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  headerExtractBaseFeeU64BhFunction ++ "\n" ++
  baseFeePerGasAtBlockHashFunction ++ "\n" ++
  ".Lbfbh_pdone:"

def ziskBaseFeePerGasAtBlockHashDataSection : String :=
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
  "bfbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "bfbh_match_length:\n" ++
  "  .zero 8"

def ziskBaseFeePerGasAtBlockHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBaseFeePerGasAtBlockHashPrologue
  dataAsm     := ziskBaseFeePerGasAtBlockHashDataSection
}

end EvmAsm.Codegen
