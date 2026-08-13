/-
  EvmAsm.Codegen.Programs.StateExtractNonce

  Pure field extractor: walk the state trie to find an
  address's u64 nonce. Spec-default 0 on miss.

  Fourth and final per-field extract primitive, alongside
  #7233 (storage_root), #7240 (code_hash), #7246 (balance).
  Together: one extractor per field of the account RLP
  struct.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.State

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## state_extract_nonce_for_address

    Given (state_root, address, witness.state), walk the MPT
    and return the matching account's `nonce` field (u64 LE,
    8 bytes from struct offset +0).

    Output is written via a caller-supplied u64 pointer so
    the calling convention matches the other extract
    siblings.

    On absent: write 0 (spec default = fresh EOA nonce);
    status = 1.

    Use cases:
      * Replay-protection check: caller has a transaction
        signed with claimed nonce N; this primitive returns
        the chain's actual nonce so the caller can compare.
      * EIP-7702 / account abstraction: validate the
        sender's nonce equals expected before processing
        the transaction.
      * "Is this a fresh account?" -- if extracted nonce is
        0 AND status is 1, the address has never been used.

    Sibling shape: same calling convention as #7233/#7240/#7246
    except the output is 8 bytes (u64) not 32 bytes.

    Calling convention:
      a0 (input)  : state_root ptr (32 bytes)
      a1 (input)  : address ptr (20 bytes)
      a2 (input)  : witness.state ptr
      a3 (input)  : witness.state len
      a4 (input)  : u64 out ptr (8 bytes)
      ra (input)  : return

      a0 (output) :
        0 = present (walked nonce written)
        1 = absent (0 written -- spec default)
        2 = mpt_walk parse error (out zeroed)
        3 = account RLP decode failure (out zeroed)
-/
def stateExtractNonceForAddressFunction : String :=
  "state_extract_nonce_for_address:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # state_root ptr\n" ++
  "  mv s1, a1                  # address ptr\n" ++
  "  mv s2, a4                  # u64 output ptr\n" ++
  "  sd zero, 0(s2)\n" ++
  "  mv a4, a3                  # witness_len\n" ++
  "  mv a3, a2                  # witness_ptr\n" ++
  "  mv a2, s0                  # state_root_ptr\n" ++
  "  mv a0, s1                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  la a5, senon_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsenon_present\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsenon_absent\n" ++
  "  j .Lsenon_ret\n" ++
  ".Lsenon_present:\n" ++
  "  la t0, senon_walked_struct\n" ++
  "  ld t2, 0(t0)               # nonce u64 LE at offset +0\n" ++
  "  sd t2, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lsenon_ret\n" ++
  ".Lsenon_absent:\n" ++
  "  # Output already zero -- spec default for nonce.\n" ++
  "  li a0, 1\n" ++
  ".Lsenon_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_state_extract_nonce_for_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_state_len (u64 LE)
      bytes 16..48 : state_root (32 bytes)
      bytes 48..68 : address (20 bytes)
      bytes 68..   : witness.state section bytes
    Output layout (16 bytes):
      bytes  0.. 8 : status
      bytes  8..16 : nonce (u64 LE) -/
def ziskStateExtractNonceForAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a3, 8(a6)                # witness_state_len\n" ++
  "  addi a0, a6, 16             # state_root ptr\n" ++
  "  addi a1, a6, 48             # address ptr\n" ++
  "  addi a2, a6, 68             # witness.state ptr\n" ++
  "  li a4, 0xa0010008           # u64 nonce out\n" ++
  "  jal ra, state_extract_nonce_for_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsenon_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  stateExtractNonceForAddressFunction ++ "\n" ++
  ".Lsenon_pdone:"

def ziskStateExtractNonceForAddressDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aa_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 32\n" ++
  "senon_walked_struct:\n" ++
  "  .zero 104"


end EvmAsm.Codegen
