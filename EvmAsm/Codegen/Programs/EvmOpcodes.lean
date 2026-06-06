/-
  EvmAsm.Codegen.Programs.EvmOpcodes

  Witness-side implementations of EVM opcode semantics carved
  out of `EvmAsm.Codegen.Programs.State` per the file-size hard
  cap. Hosts probes that translate a stateless witness +
  parent-header tuple into the value an EVM frame would push
  onto the stack for a given opcode, applying the opcode's
  spec-correct edge cases (e.g. EIP-1052's "empty-account → 0"
  rule for EXTCODEHASH).

  These compose K201 `header_extract_state_root`, K28
  `account_at_address`, and friends from
  `EvmAsm.Codegen.Programs.State` -- they add the
  opcode-specific edge-case handling layered on top of the
  trie walk.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.State
import EvmAsm.Codegen.Programs.EvmNonce

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## extcodehash_at_header_state_root  (EIP-1052)

    Witness-side implementation of the EVM `EXTCODEHASH` opcode
    semantics. Given a parent header RLP, an address, and an SSZ
    `witness.state` list section, return the 32-byte hash an
    EXTCODEHASH(addr) frame would push onto the stack.

    Per EIP-1052, EXTCODEHASH returns:
      * 0 if the account does not exist OR is "empty"
        (an empty account has nonce = 0, balance = 0,
         code_hash = keccak("") = EMPTY_CODE_HASH).
      * the account's `code_hash` otherwise.

    Distinct from PR-K? `code_at_header_state_root`, which
    resolves `account.code_hash` against `witness.codes`.
    EXTCODEHASH only reads the state trie's account record --
    it does NOT touch `witness.codes`; it just inspects the
    four account fields and applies the EIP-1052
    zero-on-empty rule.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : 32-byte output ptr (the EXTCODEHASH result)
      ra (input)  : return

      a0 (output) :
        0 = success (output filled per EIP-1052 semantics)
        2 = state-trie mpt parse error  (output zeroed)
        3 = account_decode failure      (output zeroed)
        4 = header parse / state_root size fail (output zeroed)

      Note: "account not in trie" returns SUCCESS with 32 zeros
      (NOT a separate status), matching EIP-1052 exactly. Pure
      RLP/MPT structural failures still propagate as 2/3.

    Composes K201 `header_extract_state_root` + K28
    `account_at_address` + 4 u64 compares against the
    pre-baked EMPTY_CODE_HASH constant.
-/
def extcodehashAtHeaderStateRootFunction : String :=
  "extcodehash_at_header_state_root:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_rlp_len\n" ++
  "  mv s2, a2                  # address ptr\n" ++
  "  mv s3, a3                  # witness.state ptr\n" ++
  "  mv s4, a4                  # witness.state len\n" ++
  "  mv s5, a5                  # 32-byte output ptr\n" ++
  "  # Pre-zero output (covers the EIP-1052 zero cases).\n" ++
  "  sd zero,  0(s5); sd zero,  8(s5); sd zero, 16(s5); sd zero, 24(s5)\n" ++
  "  # Step 1: header.state_root -> eahsr_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, eahsr_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Leahsr_step2\n" ++
  "  li a0, 4\n" ++
  "  j .Leahsr_ret\n" ++
  ".Leahsr_step2:\n" ++
  "  # Step 2: account_at_address -> eahsr_acct_struct.\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 20\n" ++
  "  la a2, eahsr_state_root\n" ++
  "  mv a3, s3\n" ++
  "  mv a4, s4\n" ++
  "  la s6, eahsr_acct_struct\n" ++
  "  mv a5, s6\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Leahsr_check_empty\n" ++
  "  # status 1 (not in trie) -> EIP-1052 returns 0 (output already zero).\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Leahsr_success_zero\n" ++
  "  # status 2/3 -> propagate.\n" ++
  "  j .Leahsr_ret\n" ++
  ".Leahsr_success_zero:\n" ++
  "  li a0, 0\n" ++
  "  j .Leahsr_ret\n" ++
  ".Leahsr_check_empty:\n" ++
  "  # nonce == 0 ?\n" ++
  "  ld t1, 0(s6)\n" ++
  "  bnez t1, .Leahsr_write_code_hash\n" ++
  "  # balance == 0 ?  (4 x u64 at struct+8..40; zero-check is endian-blind)\n" ++
  "  ld t1,  8(s6); bnez t1, .Leahsr_write_code_hash\n" ++
  "  ld t1, 16(s6); bnez t1, .Leahsr_write_code_hash\n" ++
  "  ld t1, 24(s6); bnez t1, .Leahsr_write_code_hash\n" ++
  "  ld t1, 32(s6); bnez t1, .Leahsr_write_code_hash\n" ++
  "  # code_hash == EMPTY_CODE_HASH ?\n" ++
  "  la t0, eahsr_empty_code_hash\n" ++
  "  ld t1,  0(t0); ld t2, 72(s6); bne t1, t2, .Leahsr_write_code_hash\n" ++
  "  ld t1,  8(t0); ld t2, 80(s6); bne t1, t2, .Leahsr_write_code_hash\n" ++
  "  ld t1, 16(t0); ld t2, 88(s6); bne t1, t2, .Leahsr_write_code_hash\n" ++
  "  ld t1, 24(t0); ld t2, 96(s6); bne t1, t2, .Leahsr_write_code_hash\n" ++
  "  # All three empty-conditions hold; output stays zero, return 0.\n" ++
  "  li a0, 0\n" ++
  "  j .Leahsr_ret\n" ++
  ".Leahsr_write_code_hash:\n" ++
  "  # Account is non-empty; copy code_hash to output.\n" ++
  "  ld t1, 72(s6); sd t1,  0(s5)\n" ++
  "  ld t1, 80(s6); sd t1,  8(s5)\n" ++
  "  ld t1, 88(s6); sd t1, 16(s5)\n" ++
  "  ld t1, 96(s6); sd t1, 24(s5)\n" ++
  "  li a0, 0\n" ++
  ".Leahsr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_extcodehash_at_header_state_root`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..44 : address (20 bytes)
      bytes 44..44+H              : header_rlp
      bytes 44+H..44+H+WS         : witness.state
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4)
      bytes  8..40 : EXTCODEHASH result (per EIP-1052) -/
def ziskExtcodehashAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  addi a2, t1, 24             # address ptr\n" ++
  "  addi a0, t1, 44             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # witness.state ptr\n" ++
  "  mv a4, t3                   # witness_state_len\n" ++
  "  li a5, 0xa0010008           # 32 B output\n" ++
  "  jal ra, extcodehash_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Leahsr_pdone\n" ++
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
  extcodehashAtHeaderStateRootFunction ++ "\n" ++
  ".Leahsr_pdone:"

def ziskExtcodehashAtHeaderStateRootDataSection : String :=
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
  ".balign 32\n" ++
  "eahsr_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "eahsr_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "eahsr_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"

def ziskExtcodehashAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskExtcodehashAtHeaderStateRootPrologue
  dataAsm     := ziskExtcodehashAtHeaderStateRootDataSection
}

/-! ## balance_at_header_state_root  (EVM BALANCE opcode)

    Witness-side implementation of the EVM `BALANCE` opcode.
    Given a parent header RLP, an address, and an SSZ
    `witness.state` list section, return the u256 balance an
    `BALANCE(addr)` frame would push.

    BALANCE has the same "absent → 0" flattening as SLOAD: a
    missing account returns balance 0 without any error
    signalling. That's the natural EVM-semantic of "all addresses
    are conceptually defined; uninitialised ones have zero
    balance".

    Composes K201 `header_extract_state_root` + K28
    `account_at_address`, then extracts the 32-byte balance
    field (struct + 8 .. + 40) and flattens status 1 to (0, 0).

    Distinct from `account_at_header_state_root` which surfaces
    the missing-account case as status 1: BALANCE callers
    shouldn't have to special-case absence.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : 32-byte u256 BE output ptr
      ra (input)  : return

      a0 (output) :
        0 = success (balance written to output; 0 for absent)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail

      (Code 1 is intentionally absent: missing accounts map to
      `status=0, balance=0` per the EVM BALANCE semantic.)
-/
def balanceAtHeaderStateRootFunction : String :=
  "balance_at_header_state_root:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_rlp_len\n" ++
  "  mv s2, a2                  # address ptr\n" ++
  "  mv s3, a3                  # witness.state ptr\n" ++
  "  mv s4, a4                  # witness.state len\n" ++
  "  mv s5, a5                  # 32-byte u256 BE output ptr\n" ++
  "  # Pre-zero output -- BALANCE default value.\n" ++
  "  sd zero,  0(s5); sd zero,  8(s5); sd zero, 16(s5); sd zero, 24(s5)\n" ++
  "  # Step 1: header.state_root -> bal_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, bal_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lbal_step2\n" ++
  "  li a0, 4\n" ++
  "  j .Lbal_ret\n" ++
  ".Lbal_step2:\n" ++
  "  # Step 2: account_at_address -> bal_acct_struct.\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 20\n" ++
  "  la a2, bal_state_root\n" ++
  "  mv a3, s3\n" ++
  "  mv a4, s4\n" ++
  "  la s6, bal_acct_struct\n" ++
  "  mv a5, s6\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lbal_copy_balance\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lbal_absent  # 1 -> BALANCE returns 0\n" ++
  "  # 2/3 propagate; output already zeroed.\n" ++
  "  j .Lbal_ret\n" ++
  ".Lbal_absent:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbal_ret\n" ++
  ".Lbal_copy_balance:\n" ++
  "  # Account found; copy balance (struct + 8 .. + 40) to output.\n" ++
  "  ld t1,  8(s6); sd t1,  0(s5)\n" ++
  "  ld t1, 16(s6); sd t1,  8(s5)\n" ++
  "  ld t1, 24(s6); sd t1, 16(s5)\n" ++
  "  ld t1, 32(s6); sd t1, 24(s5)\n" ++
  "  li a0, 0\n" ++
  ".Lbal_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_balance_at_header_state_root`: probe BuildUnit.

    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len    (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..44 : address (20 bytes)
      bytes 44..44+H              : header_rlp
      bytes 44+H..44+H+WS         : witness.state
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4)
      bytes  8..40 : balance (u256 BE; 0 on absent) -/
def ziskBalanceAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  addi a2, t1, 24             # address ptr\n" ++
  "  addi a0, t1, 44             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # witness.state ptr\n" ++
  "  mv a4, t3                   # witness_state_len\n" ++
  "  li a5, 0xa0010008           # 32 B output\n" ++
  "  jal ra, balance_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbal_pdone\n" ++
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
  balanceAtHeaderStateRootFunction ++ "\n" ++
  ".Lbal_pdone:"

def ziskBalanceAtHeaderStateRootDataSection : String :=
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
  ".balign 32\n" ++
  "bal_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "bal_acct_struct:\n" ++
  "  .zero 104"

def ziskBalanceAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalanceAtHeaderStateRootPrologue
  dataAsm     := ziskBalanceAtHeaderStateRootDataSection
}


/-! ## sload_at_header_state_root  (EVM SLOAD opcode)

    Witness-side implementation of the EVM `SLOAD` opcode. Given
    a parent header RLP, an address, a 32-byte slot index, an
    SSZ `witness.state` list, and an SSZ `witness.storage` list,
    return the u256 value an `SLOAD(slot)` frame in `addr`'s
    context would push.

    Per the spec, SLOAD returns 0 if:
      * the account is not present in the state trie, OR
      * `account.storage_root == EMPTY_TRIE_ROOT`
        (mpt_walk -> "not found" inside `slot_at_index`), OR
      * the storage slot is simply not present in the trie
        (any uninitialised slot is implicitly zero).

    This is the SLOAD-side complement of PR
    `slot_at_header_state_root` (which surfaces those "not
    found" cases as distinct statuses 1 and 5). The EVM-level
    semantic flattens both into "value = 0, status = 0";
    callers using this primitive shouldn't have to special-case
    absence. Structural failures (mpt parse, RLP decode, header
    parse) still propagate so witness integrity can be checked.

    Calling convention (8 args, fits in a0..a7):
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : slot_idx ptr (32-byte BE u256)
      a4 (input)  : witness.state ptr
      a5 (input)  : witness.state len
      a6 (input)  : witness.storage ptr
      a7 (input)  : witness.storage len
      ra (input)  : return

      a0 (output) :
        0 = success (slot value at `sload_u256`; may be 0)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail
        6 = storage-trie mpt parse error
        7 = slot RLP decode failure

      (Codes 1 and 5 are intentionally absent: those map to
      `status=0, value=0` per SLOAD semantics.)

    The probe BuildUnit copies `sload_u256` (32 B BE) to
    OUTPUT + 8.
-/
def sloadAtHeaderStateRootFunction : String :=
  "sload_at_header_state_root:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_rlp_len\n" ++
  "  mv s2, a2                  # address ptr\n" ++
  "  mv s3, a3                  # slot_idx ptr\n" ++
  "  mv s4, a4                  # witness.state ptr\n" ++
  "  mv s5, a5                  # witness.state len\n" ++
  "  mv s6, a6                  # witness.storage ptr\n" ++
  "  mv s7, a7                  # witness.storage len\n" ++
  "  # Pre-zero the 32-byte output -- SLOAD default value.\n" ++
  "  la t0, sload_u256\n" ++
  "  sd zero,  0(t0); sd zero,  8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  # Step 1: header.state_root -> sload_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, sload_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lsload_step2\n" ++
  "  li a0, 4\n" ++
  "  j .Lsload_ret\n" ++
  ".Lsload_step2:\n" ++
  "  # Step 2: account_at_address.\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 20\n" ++
  "  la a2, sload_state_root\n" ++
  "  mv a3, s4\n" ++
  "  mv a4, s5\n" ++
  "  la s8, sload_acct_struct\n" ++
  "  mv a5, s8\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsload_step3\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsload_missing_acct  # 1 -> SLOAD returns 0\n" ++
  "  j .Lsload_ret                     # 2/3 propagate\n" ++
  ".Lsload_missing_acct:\n" ++
  "  li a0, 0\n" ++
  "  j .Lsload_ret\n" ++
  ".Lsload_step3:\n" ++
  "  # Step 3: slot_at_index over witness.storage with acct.storage_root.\n" ++
  "  mv a0, s3                  # slot_idx ptr\n" ++
  "  li a1, 32                  # slot_idx_len\n" ++
  "  addi a2, s8, 40            # &acct.storage_root\n" ++
  "  mv a3, s6                  # witness.storage ptr\n" ++
  "  mv a4, s7                  # witness.storage len\n" ++
  "  la a5, sload_u256          # u256 BE out\n" ++
  "  jal ra, slot_at_index\n" ++
  "  beqz a0, .Lsload_ret       # 0 -> value at sload_u256\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsload_missing_slot # 1 -> SLOAD returns 0\n" ++
  "  # 2 -> 6, 3 -> 7\n" ++
  "  addi a0, a0, 4\n" ++
  "  # value buffer was zeroed by slot_at_index on failure.\n" ++
  "  j .Lsload_ret\n" ++
  ".Lsload_missing_slot:\n" ++
  "  li a0, 0\n" ++
  ".Lsload_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_sload_at_header_state_root`: probe BuildUnit.

    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len      (u64 LE)
      bytes 16..24 : witness_state_len   (u64 LE)
      bytes 24..32 : witness_storage_len (u64 LE)
      bytes 32..64 : slot_idx (32-byte BE u256)
      bytes 64..84 : address (20 bytes)
      bytes 84..84+H              : header_rlp
      bytes 84+H..84+H+WS         : witness.state
      bytes 84+H+WS..             : witness.storage
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4 / 6 / 7)
      bytes  8..40 : slot value (u256 BE; 0 on missing/absent) -/
def ziskSloadAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  ld t4, 24(t1)               # witness_storage_len\n" ++
  "  addi a3, t1, 32             # slot_idx ptr\n" ++
  "  addi a2, t1, 64             # address ptr\n" ++
  "  addi a0, t1, 84             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a4, a0, t2              # witness.state ptr\n" ++
  "  mv a5, t3                   # witness_state_len\n" ++
  "  add a6, a4, t3              # witness.storage ptr\n" ++
  "  mv a7, t4                   # witness_storage_len\n" ++
  "  jal ra, sload_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  # Copy sload_u256 (32 B) to OUTPUT + 8.\n" ++
  "  la t1, sload_u256\n" ++
  "  ld t2,  0(t1); sd t2,  8(t0)\n" ++
  "  ld t2,  8(t1); sd t2, 16(t0)\n" ++
  "  ld t2, 16(t1); sd t2, 24(t0)\n" ++
  "  ld t2, 24(t1); sd t2, 32(t0)\n" ++
  "  j .Lsload_pdone\n" ++
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
  slotDecodeU256Function ++ "\n" ++
  slotAtIndexFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  sloadAtHeaderStateRootFunction ++ "\n" ++
  ".Lsload_pdone:"

def ziskSloadAtHeaderStateRootDataSection : String :=
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
  "si_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "si_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "sload_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sload_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "sload_u256:\n" ++
  "  .zero 32"

def ziskSloadAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSloadAtHeaderStateRootPrologue
  dataAsm     := ziskSloadAtHeaderStateRootDataSection
}
end EvmAsm.Codegen
