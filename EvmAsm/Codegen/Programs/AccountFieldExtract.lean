/-
  EvmAsm.Codegen.Programs.AccountFieldExtract

  Ethereum-account RLP field extractors split out of `Account.lean`.

  Hosts:
    K121  account_extract_nonce    (field 0, u64)
    K120  account_extract_balance  (field 1, u256 BE)

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## account_extract_nonce -- PR-K121

    Extract the u64 `nonce` field (RLP field 0) from a fully
    RLP-encoded Ethereum account:

      account = [nonce, balance, storage_root, code_hash]

    The nonce counts the number of outbound transactions an EOA
    has issued (or contract creations for a contract). EIP-2681
    caps it at `2^64 - 1` so a u64 fits.

    K27 `account_decode` already extracts the full account record;
    this narrower accessor avoids the 96-byte struct when only the
    nonce is needed (e.g., the tx-replay-protection check inside
    `check_transaction`, or to thread the nonce-mismatch error path
    without unpacking balance / storage_root / code_hash).

    Composes the existing `rlp_field_to_u64` helper (which in turn
    uses PR-K20 `rlp_list_nth_item`).

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : u64 output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 0 missing / > 64 bits -/
def accountExtractNonceFunction : String :=
  "account_extract_nonce:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a2                   # u64 out ptr (stash)\n" ++
  "  sd zero, 0(s0)\n" ++
  "  # a0, a1 still hold (account_ptr, account_len).\n" ++
  "  li a2, 0\n" ++
  "  mv a3, s0\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  beqz a0, .Laen_ret\n" ++
  "  sd zero, 0(s0)\n" ++
  "  li a0, 1\n" ++
  ".Laen_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_account_extract_nonce`: probe BuildUnit. Reads
    (account_len, account_bytes), writes (status, nonce u64) to
    OUTPUT (16 bytes). -/
def ziskAccountExtractNoncePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # account_rlp_len\n" ++
  "  addi a0, a3, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # nonce out\n" ++
  "  jal ra, account_extract_nonce\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laen_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  accountExtractNonceFunction ++ "\n" ++
  ".Laen_pdone:"

def ziskAccountExtractNonceDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskAccountExtractNonceProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountExtractNoncePrologue
  dataAsm     := ziskAccountExtractNonceDataSection
}

/-! ## account_extract_balance -- PR-K120

    Extract the u256 BE `balance` field (RLP field 1) from a fully
    RLP-encoded Ethereum account:

      account = [nonce, balance, storage_root, code_hash]

    The balance is the account's wei holdings, ranged in
    `[0, 2^256)`. Direct input to balance-check predicates
    (`balance >= value + gas_cost`), priority-fee credit, and
    the trie-rebuild path after value transfers.

    K27 `account_decode` already extracts the full account record;
    K120 (with PR-K119 `account_extract_storage_root`) is the
    narrower accessor for callers that only need a single field.

    Composes the existing `rlp_field_to_u256_be` helper (which in
    turn uses PR-K20 `rlp_list_nth_item`).

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : 32-byte output ptr (u256 BE)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 1 missing / > 256 bits -/
def accountExtractBalanceFunction : String :=
  "account_extract_balance:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a2                   # output 32B ptr (stash)\n" ++
  "  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)\n" ++
  "  # a0, a1 still hold (account_ptr, account_len).\n" ++
  "  li a2, 1\n" ++
  "  mv a3, s0\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  beqz a0, .Laeb_ret\n" ++
  "  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)\n" ++
  "  li a0, 1\n" ++
  ".Laeb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_account_extract_balance`: probe BuildUnit. Reads
    (account_len, account_bytes), writes (status, 32-byte balance
    BE) to OUTPUT (40 bytes). -/
def ziskAccountExtractBalancePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # account_rlp_len\n" ++
  "  addi a0, a3, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # 32B u256 output\n" ++
  "  jal ra, account_extract_balance\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laeb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  ".Laeb_pdone:"

def ziskAccountExtractBalanceDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t48_offset:\n" ++
  "  .zero 8\n" ++
  "t48_length:\n" ++
  "  .zero 8"

def ziskAccountExtractBalanceProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountExtractBalancePrologue
  dataAsm     := ziskAccountExtractBalanceDataSection
}

end EvmAsm.Codegen
