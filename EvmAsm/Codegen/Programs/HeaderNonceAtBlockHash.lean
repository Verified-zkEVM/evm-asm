/-
  EvmAsm.Codegen.Programs.HeaderNonceAtBlockHash

  Hash-keyed `header.nonce` extractor (RLP field 14, exactly
  8 bytes BE). Mirror of the number-keyed
  `header_nonce_at_block_number` probe but takes a
  block_hash key.

  Per EIP-3675, post-merge canonical headers MUST have
  `header.nonce = 0` (8-byte zero); this lets a bridge
  verify the post-merge invariant directly from block_hash.

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

/-! ## header_nonce_at_block_hash

    Hash-keyed extractor for `header.block.nonce`
    (RLP field 14, 8 bytes BE).

    Pipeline (composes K19 + existing
    header_extract_nonce; no new helpers):
      witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
      h -> header_extract_nonce -> u64 (8 BE bytes -> u64 LE)

    Spec-defining check: per EIP-3675 (the Merge),
    every post-merge canonical header satisfies
    `header.nonce == 0` (eight zero bytes BE). Reading
    header.nonce hash-keyed lets a bridge / light-client
    verify that invariant directly from a block_hash.

    Calling convention (4 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : u64 nonce out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (header.nonce u64 written)
        1 = block_hash not in witness.headers
        2 = matched header nonce extraction failed
            (RLP malformed / field 14 size != 8)
-/
def headerNonceAtBlockHashFunction : String :=
  "header_nonce_at_block_hash:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # nonce u64 out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, hnbh_match_offset\n" ++
  "  la a4, hnbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lhnbh_no_match\n" ++
  "  la t0, hnbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s4, s1, t1\n" ++
  "  la t0, hnbh_match_length\n" ++
  "  ld s5, 0(t0)\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_nonce\n" ++
  "  beqz a0, .Lhnbh_ret\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 2\n" ++
  "  j .Lhnbh_ret\n" ++
  ".Lhnbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lhnbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_header_nonce_at_block_hash`: probe BuildUnit.
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..2)
      bytes  8..16 : header.nonce u64 (BE-decoded; 0 on failure) -/
def ziskHeaderNonceAtBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  addi a0, t4, 16             # block_hash ptr\n" ++
  "  addi a1, t4, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # u64 nonce out\n" ++
  "  jal ra, header_nonce_at_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhnbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractNonceFunction ++ "\n" ++
  headerNonceAtBlockHashFunction ++ "\n" ++
  ".Lhnbh_pdone:"

def ziskHeaderNonceAtBlockHashDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "hen_offset:\n" ++
  "  .zero 8\n" ++
  "hen_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "hnbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "hnbh_match_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
