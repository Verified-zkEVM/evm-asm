/-
  EvmAsm.Codegen.Programs.StateExtractBalance

  Pure field extractor: walk the state trie to find an
  address's u256 balance (BE 32 bytes). Spec-default 0
  (32 zero bytes) on miss.

  Third in the extract family alongside #7233
  (storage_root) and #7240 (code_hash). Together with a
  forthcoming nonce extractor they form the per-field
  extract family complementary to the inclusion-proof
  family (#7197/#7206/#7209/#7212).

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

/-! ## state_extract_balance_for_address

    Given (state_root, address, witness.state), walk the MPT
    and write the matching account's `balance` field (32
    bytes big-endian u256) to the caller's output buffer.

    On absent: write 32 zero bytes (spec default = 0 balance);
    status = 1.

    Use cases:
      * BALANCE-opcode-style queries against a trusted
        state snapshot. Returns the chain-anchored balance
        without materialising the full struct.
      * Bridge audit / accounting: total a list of balances
        across N addresses by chaining N calls + an
        accumulator on the host side.
      * Snapshot freshness check: caller knows the expected
        balance from off-chain bookkeeping and runs the
        extract + their own compare (cheaper than
        #7209 if the caller has many addresses and only
        wants one balance comparison at the end).

    Sibling of:
      * #7233 state_extract_storage_root_for_address
        (field +40, default EMPTY_TRIE_ROOT)
      * #7240 state_extract_code_hash_for_address
        (field +72, default EMPTY_CODE_HASH)
    This one: field +8, default 32 zero bytes.

    Calling convention:
      a0 (input)  : state_root ptr (32 bytes)
      a1 (input)  : address ptr (20 bytes)
      a2 (input)  : witness.state ptr
      a3 (input)  : witness.state len
      a4 (input)  : 32-byte balance_be out buffer ptr
      ra (input)  : return

      a0 (output) :
        0 = present (walked balance written, BE u256)
        1 = absent (32 zero bytes written -- spec default)
        2 = mpt_walk parse error (buffer zeroed)
        3 = account RLP decode failure (buffer zeroed)
-/
def stateExtractBalanceForAddressFunction : String :=
  "state_extract_balance_for_address:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # state_root ptr\n" ++
  "  mv s1, a1                  # address ptr\n" ++
  "  mv s2, a4                  # output buffer (32 B)\n" ++
  "  # Zero the output buffer (also serves as the absent default).\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  mv a4, a3                  # witness_len\n" ++
  "  mv a3, a2                  # witness_ptr\n" ++
  "  mv a2, s0                  # state_root_ptr\n" ++
  "  mv a0, s1                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  la a5, sebal_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsebal_present\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsebal_absent\n" ++
  "  j .Lsebal_ret\n" ++
  ".Lsebal_present:\n" ++
  "  la t0, sebal_walked_struct\n" ++
  "  ld t2,  8(t0); sd t2,  0(s2)\n" ++
  "  ld t2, 16(t0); sd t2,  8(s2)\n" ++
  "  ld t2, 24(t0); sd t2, 16(s2)\n" ++
  "  ld t2, 32(t0); sd t2, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lsebal_ret\n" ++
  ".Lsebal_absent:\n" ++
  "  # Buffer already zero -- spec default for balance.\n" ++
  "  li a0, 1\n" ++
  ".Lsebal_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_state_extract_balance_for_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_state_len (u64 LE)
      bytes 16..48 : state_root (32 bytes)
      bytes 48..68 : address (20 bytes)
      bytes 68..   : witness.state section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status
      bytes  8..40 : balance (32 B BE) -/
def ziskStateExtractBalanceForAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a3, 8(a6)                # witness_state_len\n" ++
  "  addi a0, a6, 16             # state_root ptr\n" ++
  "  addi a1, a6, 48             # address ptr\n" ++
  "  addi a2, a6, 68             # witness.state ptr\n" ++
  "  li a4, 0xa0010008           # balance out (32 B)\n" ++
  "  jal ra, state_extract_balance_for_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsebal_pdone\n" ++
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
  stateExtractBalanceForAddressFunction ++ "\n" ++
  ".Lsebal_pdone:"

def ziskStateExtractBalanceForAddressDataSection : String :=
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
  "sebal_walked_struct:\n" ++
  "  .zero 104"


end EvmAsm.Codegen
