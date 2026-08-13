/-
  EvmAsm.Codegen.Programs.ExtraDataAtBlockHash

  Hash-keyed `header.extra_data` extractor (RLP field 12,
  variable length up to 32 bytes per EIP-3675). Mirror of
  the number-keyed `extra_data_at_block_number` probe but
  takes a 32-byte block_hash key.

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

/-! ## extra_data_at_block_hash

    Hash-keyed extractor for `header.block.extra_data`
    (RLP field 12, ≤ 32 B per EIP-3675).

    Pipeline (composes K19 + existing
    header_extract_extra_data; no new helpers):
      witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
      h -> header_extract_extra_data -> (length, ≤32 bytes)

    Use cases unique to the hash-keyed variant:
      * Proposer-tag attestation -- block_hash is known
        (e.g. from a finality proof) and the off-chain
        observer wants the validator-signed proposer
        identification bytes.
      * EIP-3675 size invariant audit at a specific
        block_hash without first translating to a number.
      * Cross-witness extra_data consistency.

    Calling convention (5 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : extra_data bytes out ptr (≥ 32 B)
      a4 (input)  : u64 out (extra_data length)
      ra (input)  : return

      a0 (output) :
        0 = success (length written; bytes copied)
        1 = block_hash not in witness.headers
        2 = matched header extra_data extraction failed
            (RLP malformed / field 12 length > 32)
-/
def extraDataAtBlockHashFunction : String :=
  "extra_data_at_block_hash:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # extra_data bytes out\n" ++
  "  mv s7, a4                  # u64 length out\n" ++
  "  sd zero, 0(s7)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, edbh_match_offset\n" ++
  "  la a4, edbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Ledbh_no_match\n" ++
  "  la t0, edbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s4, s1, t1\n" ++
  "  la t0, edbh_match_length\n" ++
  "  ld s5, 0(t0)\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  mv a2, s3\n" ++
  "  mv a3, s7\n" ++
  "  jal ra, header_extract_extra_data\n" ++
  "  beqz a0, .Ledbh_ret\n" ++
  "  sd zero, 0(s7)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li a0, 2\n" ++
  "  j .Ledbh_ret\n" ++
  ".Ledbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Ledbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_extra_data_at_block_hash`: probe BuildUnit.
    Output layout (48 bytes):
      bytes  0.. 8 : status (0..2)
      bytes  8..16 : extra_data length (u64 LE)
      bytes 16..48 : extra_data bytes (≤ 32, zero-padded) -/
def ziskExtraDataAtBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  addi a0, t4, 16             # block_hash ptr\n" ++
  "  addi a1, t4, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010010           # 32 B extra_data bytes out\n" ++
  "  li a4, 0xa0010008           # u64 length out\n" ++
  "  jal ra, extra_data_at_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ledbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractExtraDataFunction ++ "\n" ++
  extraDataAtBlockHashFunction ++ "\n" ++
  ".Ledbh_pdone:"

def ziskExtraDataAtBlockHashDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "heed_offset:\n" ++
  "  .zero 8\n" ++
  "heed_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "edbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "edbh_match_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
