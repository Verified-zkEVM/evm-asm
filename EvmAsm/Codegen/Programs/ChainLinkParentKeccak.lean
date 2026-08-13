/-
  EvmAsm.Codegen.Programs.ChainLinkParentKeccak

  Multi-block chain-link hash consistency primitive: given
  a parent block's RLP and a child block's header RLP, check
  whether keccak256(parent_rlp) equals the child header's
  parent_hash field.

  Fundamental primitive for building multi-block trusted
  chains: lets a caller verify that two consecutive headers
  are actually linked by the canonical chain rule before
  using either's state_root for downstream verification.

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

/-! ## parent_keccak_matches_child_parent_hash

    Given a parent block's RLP and a child block's header
    RLP, check `keccak256(parent_rlp) == child.parent_hash`.

    The "parent RLP" here is the full canonical RLP-encoded
    block header (the same bytes whose keccak gives the
    block hash). The "child header" is the next block's
    header from which we extract field 0 (parent_hash).

    Use cases:
      * Multi-block trusted chains: caller has a sequence
        of headers; this primitive verifies each consecutive
        pair is linked, building a chain of trust from a
        single trusted root.
      * Light-client header sync: validate each newly
        received header against the most recent trusted
        header before accepting its state_root.
      * Stateless guest: this is the same check the python
        spec's chain_validate_full performs internally; we
        expose it standalone so callers can validate a single
        link without paying for the full chain validator.

    Composes:
      * K202 `header_extract_parent_hash` -- extract field 0
      * K3 `zkvm_keccak256` -- hash parent_rlp
      * 32-byte compare

    Calling convention:
      a0 (input)  : parent_block_rlp ptr
      a1 (input)  : parent_block_rlp len
      a2 (input)  : child_header_rlp ptr
      a3 (input)  : child_header_rlp len
      a4 (input)  : u64 out ptr (is_valid)
      ra (input)  : return

      a0 (output) :
        0 = success (is_valid set; 1 if linked, 0 if not)
        1 = child header parse failure (parent_hash field
            could not be extracted)
        2 = child parent_hash size unexpected (not 32 B)
-/
def parentKeccakMatchesChildParentHashFunction : String :=
  "parent_keccak_matches_child_parent_hash:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # parent_rlp ptr\n" ++
  "  mv s1, a1                  # parent_rlp len\n" ++
  "  mv s2, a2                  # child_header_rlp ptr\n" ++
  "  mv s3, a3                  # child_header_rlp len\n" ++
  "  mv s4, a4                  # is_valid out\n" ++
  "  sd zero, 0(s4)\n" ++
  "  # Step 1: extract child.parent_hash into pkmc_child_ph.\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s3\n" ++
  "  la a2, pkmc_child_ph\n" ++
  "  jal ra, header_extract_parent_hash\n" ++
  "  bnez a0, .Lpkmc_ret      # status 1 (parse) or 2 (size) propagate.\n" ++
  "  # Step 2: keccak256(parent_rlp) into pkmc_parent_keccak.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, pkmc_parent_keccak\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Step 3: 32-byte compare.\n" ++
  "  la t0, pkmc_child_ph\n" ++
  "  la t1, pkmc_parent_keccak\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lpkmc_diff\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lpkmc_diff\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lpkmc_diff\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lpkmc_diff\n" ++
  "  li t4, 1\n" ++
  "  sd t4, 0(s4)\n" ++
  ".Lpkmc_diff:\n" ++
  "  li a0, 0\n" ++
  ".Lpkmc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_parent_keccak_matches_child_parent_hash`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : parent_rlp_len (u64 LE)
      bytes 16..24 : child_header_rlp_len (u64 LE)
      bytes 24..   : parent_rlp ++ child_header_rlp
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..2)
      bytes  8..16 : is_valid (u64 0 or 1) -/
def ziskParentKeccakMatchesChildParentHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # parent_rlp_len\n" ++
  "  ld a3, 16(a6)               # child_header_rlp_len\n" ++
  "  addi a0, a6, 24             # parent_rlp ptr\n" ++
  "  add  a2, a0, a1             # child_header_rlp ptr\n" ++
  "  li a4, 0xa0010008           # is_valid out\n" ++
  "  jal ra, parent_keccak_matches_child_parent_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lpkmc_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractParentHashFunction ++ "\n" ++
  parentKeccakMatchesChildParentHashFunction ++ "\n" ++
  ".Lpkmc_pdone:"

def ziskParentKeccakMatchesChildParentHashDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "heph_offset:\n" ++
  "  .zero 8\n" ++
  "heph_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "pkmc_child_ph:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "pkmc_parent_keccak:\n" ++
  "  .zero 32"


end EvmAsm.Codegen
