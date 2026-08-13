/-
  EvmAsm.Codegen.Programs.ChainLinkExtract

  Composite of #7222 (`parent_keccak_matches_child_parent_hash`)
  and K201 (`header_extract_state_root`): in one call, both
  verify the chain link between parent and child AND extract
  the parent's state_root for downstream verification.

  Useful when a caller has a trusted child header and wants
  to extend trust backwards to the parent's state_root in
  the same primitive (avoiding the host round-trip of
  feeding parent_state_root extracted by a separate call).

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

/-! ## chain_link_verify_and_extract_parent_state_root

    One-call composite: verify chain link `keccak256(parent_rlp)
    == child.parent_hash` AND extract `parent.state_root` for
    the caller.

    Why fuse this with #7222: a common trust-chain pattern is
      1. Caller has trusted child header.
      2. Verify parent header against child via #7222.
      3. Use parent.state_root for state-trie verification.

    With #7222 alone, step 3 needs a separate K201 call --
    which means re-passing parent_rlp across the host
    boundary. This primitive does both in one call: parent
    state_root is extracted UNCONDITIONALLY on success
    (regardless of is_valid), so the caller can branch on
    is_valid without losing the extracted root.

    Calling convention (6 args):
      a0 (input)  : parent_block_rlp ptr
      a1 (input)  : parent_block_rlp len
      a2 (input)  : child_header_rlp ptr
      a3 (input)  : child_header_rlp len
      a4 (input)  : 32-byte parent_state_root_out ptr
      a5 (input)  : u64 is_valid_out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (is_valid set; parent_state_root written)
        1 = child header parse failure (parent_hash field
            could not be extracted)
        2 = child parent_hash size unexpected (not 32 B)
        3 = parent header parse failure (state_root could
            not be extracted; chain-link check was still
            performed and is_valid is meaningful but
            parent_state_root output is zeroed)
        4 = parent state_root size unexpected
-/
def chainLinkVerifyAndExtractParentStateRootFunction : String :=
  "chain_link_verify_and_extract_parent_state_root:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # parent_rlp ptr\n" ++
  "  mv s1, a1                  # parent_rlp len\n" ++
  "  mv s2, a2                  # child_header_rlp ptr\n" ++
  "  mv s3, a3                  # child_header_rlp len\n" ++
  "  mv s4, a4                  # parent_state_root_out ptr (32 B)\n" ++
  "  mv s5, a5                  # is_valid_out ptr\n" ++
  "  # Pre-zero outputs so caller sees deterministic zero on early-out.\n" ++
  "  sd zero, 0(s5)\n" ++
  "  sd zero,  0(s4); sd zero,  8(s4); sd zero, 16(s4); sd zero, 24(s4)\n" ++
  "  # Step 1: extract child.parent_hash into clve_child_ph.\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s3\n" ++
  "  la a2, clve_child_ph\n" ++
  "  jal ra, header_extract_parent_hash\n" ++
  "  bnez a0, .Lclve_ret      # status 1 (parse) or 2 (size) propagate.\n" ++
  "  # Step 2: keccak256(parent_rlp) into clve_parent_keccak.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, clve_parent_keccak\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Step 3: 32-byte compare -> is_valid.\n" ++
  "  la t0, clve_child_ph\n" ++
  "  la t1, clve_parent_keccak\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lclve_link_diff\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lclve_link_diff\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lclve_link_diff\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lclve_link_diff\n" ++
  "  li t4, 1\n" ++
  "  sd t4, 0(s5)\n" ++
  ".Lclve_link_diff:\n" ++
  "  # Step 4: extract parent.state_root into caller's output buffer.\n" ++
  "  # Done UNCONDITIONALLY so callers can branch on is_valid without\n" ++
  "  # losing the extracted root (or, more importantly, learn that\n" ++
  "  # parent_rlp is itself unparseable even when is_valid would be 0).\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lclve_done\n" ++
  "  # header_extract_state_root: 1 = parse fail, 2 = size unexpected.\n" ++
  "  # Remap to our status: 1 -> 3, 2 -> 4.\n" ++
  "  addi a0, a0, 2\n" ++
  "  j .Lclve_ret\n" ++
  ".Lclve_done:\n" ++
  "  li a0, 0\n" ++
  ".Lclve_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_chain_link_verify_and_extract_parent_state_root`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : parent_rlp_len (u64 LE)
      bytes 16..24 : child_header_rlp_len (u64 LE)
      bytes 24..   : parent_rlp ++ child_header_rlp
    Output layout (48 bytes):
      bytes  0.. 8 : status (0..4)
      bytes  8..16 : is_valid (u64; 0 or 1)
      bytes 16..48 : parent_state_root (32 B; zero on early-out) -/
def ziskChainLinkVerifyAndExtractParentStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # parent_rlp_len\n" ++
  "  ld a3, 16(a6)               # child_header_rlp_len\n" ++
  "  addi a0, a6, 24             # parent_rlp ptr\n" ++
  "  add  a2, a0, a1             # child_header_rlp ptr\n" ++
  "  li a4, 0xa0010010           # parent_state_root_out (OUTPUT + 16)\n" ++
  "  li a5, 0xa0010008           # is_valid out (OUTPUT + 8)\n" ++
  "  jal ra, chain_link_verify_and_extract_parent_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lclve_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractParentHashFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  chainLinkVerifyAndExtractParentStateRootFunction ++ "\n" ++
  ".Lclve_pdone:"

def ziskChainLinkVerifyAndExtractParentStateRootDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "heph_offset:\n" ++
  "  .zero 8\n" ++
  "heph_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "clve_child_ph:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "clve_parent_keccak:\n" ++
  "  .zero 32"


end EvmAsm.Codegen
