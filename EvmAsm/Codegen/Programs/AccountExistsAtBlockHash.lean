/-
  EvmAsm.Codegen.Programs.AccountExistsAtBlockHash

  Hash-keyed account presence predicate. Mirrors the
  StatePredicates `account_exists_at_header_state_root`
  but keyed by `block_hash` instead of by raw header bytes.

  Pipeline:
    witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
    h -> header_extract_state_root                     [K201]
    state_root + address -> account_at_address         [K28]
    walked_status==0  -> predicate = 1
    walked_status==1  -> predicate = 0 (account absent)

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.State

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## account_exists_at_block_hash_address

    Hash-keyed presence predicate -- distinct from per-field
    extractors (#7326 balance, #7320 code_hash, #7331 nonce,
    #7314 storage_root) in two ways:

      1. Single-bit output rather than a 32 B / 8 B field.
      2. The absence path is the "success" path -- callers
         use this predicate as the gating check before any
         per-field extraction, so getting `predicate=0` is
         a normal, informative outcome (not an error).

    Use cases:
      * Gate per-field calls: only call balance/nonce/etc.
        when the account is known to exist; saves wasted
        MPT walks against fresh / never-funded addresses.
      * Light-client membership oracle: prove an address
        was non-empty at a specific historical block keyed
        by hash (e.g. for sanctions/blacklist checks).
      * Compose with #7307 state_account_at_block_hash:
        callers wanting both presence + contents in one
        call can use the larger primitive; callers wanting
        only the bit get the smaller / cheaper one.

    Composes K19 (witness_lookup_by_hash) + K201
    (header_extract_state_root) + K28 (account_at_address).
    No new helpers.

    Calling convention (7 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : witness.state ptr
      a5 (input)  : witness.state len
      a6 (input)  : u64 predicate out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (predicate written; 0 = absent, 1 = present)
        1 = block_hash not in witness.headers
        2 = matched header parse failure
        3 = state_root size unexpected
        4 = state-trie mpt parse error
        5 = account RLP decode failure

      predicate :
        0 on absent / not in trie (success path; not a failure)
        1 on present
        0 also on any non-zero status (predicate is only
                                       meaningful when a0==0)
-/
def accountExistsAtBlockHashAddressFunction : String :=
  "account_exists_at_block_hash_address:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # witness.state ptr\n" ++
  "  mv s5, a5                  # witness.state len\n" ++
  "  mv s6, a6                  # predicate out (u64)\n" ++
  "  sd zero, 0(s6)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, aebh_match_offset\n" ++
  "  la a4, aebh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Laebh_no_match\n" ++
  "  la t0, aebh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s7, s1, t1\n" ++
  "  la t0, aebh_match_length\n" ++
  "  ld s8, 0(t0)\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  la a2, aebh_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Laebh_walk\n" ++
  "  addi a0, a0, 1\n" ++
  "  j .Laebh_ret\n" ++
  ".Laebh_walk:\n" ++
  "  mv a0, s3\n" ++
  "  li a1, 20\n" ++
  "  la a2, aebh_state_root\n" ++
  "  mv a3, s4\n" ++
  "  mv a4, s5\n" ++
  "  la a5, aebh_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Laebh_present\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Laebh_absent\n" ++
  "  addi a0, a0, 3\n" ++
  "  j .Laebh_ret\n" ++
  ".Laebh_present:\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Laebh_ret\n" ++
  ".Laebh_absent:\n" ++
  "  # predicate already 0; success path.\n" ++
  "  li a0, 0\n" ++
  "  j .Laebh_ret\n" ++
  ".Laebh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Laebh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_account_exists_at_block_hash_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..56 : block_hash (32 bytes)
      bytes 56..76 : address (20 bytes)
      bytes 76..   : witness.headers ++ witness.state
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..5)
      bytes  8..16 : predicate (u64; 0 = absent, 1 = present) -/
def ziskAccountExistsAtBlockHashAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a5, 16(t4)               # witness_state_len\n" ++
  "  addi a0, t4, 24             # block_hash ptr\n" ++
  "  addi a3, t4, 56             # address ptr\n" ++
  "  addi a1, t4, 76             # witness.headers ptr\n" ++
  "  add  a4, a1, a2             # witness.state ptr\n" ++
  "  li a6, 0xa0010008           # predicate out\n" ++
  "  jal ra, account_exists_at_block_hash_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laebh_pdone\n" ++
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
  headerExtractStateRootFunction ++ "\n" ++
  accountExistsAtBlockHashAddressFunction ++ "\n" ++
  ".Laebh_pdone:"

def ziskAccountExistsAtBlockHashAddressDataSection : String :=
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
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aebh_match_offset:\n" ++
  "  .zero 8\n" ++
  "aebh_match_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aebh_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "aebh_walked_struct:\n" ++
  "  .zero 104"


end EvmAsm.Codegen
