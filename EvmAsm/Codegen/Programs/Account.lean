/-
  EvmAsm.Codegen.Programs.Account

  Ethereum-account RLP accessors and predicates carved out of
  `EvmAsm.Codegen.Programs.Tx` per the file-size hard cap. Hosts:

    K121  account_extract_nonce    (field 0, u64)
    K120  account_extract_balance  (field 1, u256 BE)
    K123  account_is_empty         (EIP-161 emptiness)

  All three compose `rlp_field_to_u64` (K34), `rlp_field_to_u256_be`
  (K35), and `rlp_list_nth_item` (K20) — which remain in
  `Programs/Tx.lean` and `Programs/RlpRead.lean`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.U256GasPricing

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

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

/-! ## account_is_empty -- PR-K123

    EIP-161 "empty" predicate. An account is empty iff all three:
    - `nonce == 0`
    - `balance == 0`
    - `code_hash == EMPTY_CODE_HASH`

    The `storage_root` field is **not** part of the empty check —
    storage that's unreachable due to empty code is considered to
    not exist for this purpose. (Compare against `EMPTY_TRIE_ROOT`
    is a stricter invariant maintained by the state machine, not
    by this predicate.)

    Used by:
    - state-cleanup pass post-tx (delete-empty rule from EIP-161)
    - `account_exists_and_is_empty` in
      `forks/amsterdam/state_tracker.py`
    - beneficiary credit (a coinbase with no priority fee &
      previously empty becomes alive again only if balance > 0)

    EMPTY_CODE_HASH (keccak256(b'')) is hard-coded as a 32-byte
    constant in `.data`:

      0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    Composes:
      - PR-K20 `rlp_list_nth_item`         — field bounds
      - existing `rlp_field_to_u64`        — nonce
      - existing `rlp_field_to_u256_be`    — balance

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : u64 out ptr (1 if empty, 0 if non-empty)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written to *out
        1 : RLP parse failure / field missing / wrong width

    Uses 8 + 32 + 8 + 8 + 32 = 88 bytes of `.data` scratch
    (`aie_nonce` u64, `aie_balance` 32 B, `aie_offset` + `aie_length`,
    `aie_empty_code_hash` constant). -/
def accountIsEmptyFunction : String :=
  "account_is_empty:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # out u64 ptr\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Step 1: nonce (field 0) → aie_nonce.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  li a2, 0\n" ++
  "  la a3, aie_nonce\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Laie_parse_fail\n" ++
  "  la t0, aie_nonce; ld t1, 0(t0)\n" ++
  "  bnez t1, .Laie_not_empty\n" ++
  "  # Step 2: balance (field 1, u256 BE) → aie_balance.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  li a2, 1\n" ++
  "  la a3, aie_balance\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Laie_parse_fail\n" ++
  "  la t0, aie_balance\n" ++
  "  ld t1,  0(t0); bnez t1, .Laie_not_empty\n" ++
  "  ld t1,  8(t0); bnez t1, .Laie_not_empty\n" ++
  "  ld t1, 16(t0); bnez t1, .Laie_not_empty\n" ++
  "  ld t1, 24(t0); bnez t1, .Laie_not_empty\n" ++
  "  # Step 3: code_hash (field 3) compared against EMPTY_CODE_HASH.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  li a2, 3\n" ++
  "  la a3, aie_offset; la a4, aie_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Laie_parse_fail\n" ++
  "  la t0, aie_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Laie_parse_fail\n" ++
  "  la t0, aie_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  la t4, aie_empty_code_hash\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Laie_not_empty\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Laie_not_empty\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Laie_not_empty\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Laie_not_empty\n" ++
  "  # Empty.\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Laie_ret\n" ++
  ".Laie_not_empty:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Laie_ret\n" ++
  ".Laie_parse_fail:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 1\n" ++
  ".Laie_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_account_is_empty`: probe BuildUnit. Reads
    (account_len, account_bytes), writes (status, is_empty) to
    OUTPUT (16 bytes). -/
def ziskAccountIsEmptyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # account_rlp_len\n" ++
  "  addi a0, a3, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # is_empty out\n" ++
  "  jal ra, account_is_empty\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laie_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  accountIsEmptyFunction ++ "\n" ++
  ".Laie_pdone:"

def ziskAccountIsEmptyDataSection : String :=
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
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aie_nonce:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aie_balance:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "aie_offset:\n" ++
  "  .zero 8\n" ++
  "aie_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aie_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"

def ziskAccountIsEmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountIsEmptyPrologue
  dataAsm     := ziskAccountIsEmptyDataSection
}

/-! ## account_validate_code_hash_empty -- PR-K234

    Predicate: `account.code_hash == EMPTY_CODE_HASH` where
    `EMPTY_CODE_HASH = keccak256(b'') =
        0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470`

    This is the "is EOA / contract has no code" check. Useful
    as a standalone predicate without the balance/nonce
    constraints of K123 `account_is_empty` — e.g., to decide
    whether to skip the EVM call into a contract during static
    analysis, or to test the EIP-7702 delegation-clear path.

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : u64 out (1 if code_hash == EMPTY_CODE_HASH)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse failure / field 3 missing
        2 : field 3 length != 32 -/
def accountValidateCodeHashEmptyFunction : String :=
  "account_validate_code_hash_empty:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # out u64 ptr\n" ++
  "  sd zero, 0(s2)\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  li a2, 3\n" ++
  "  la a3, avche_offset; la a4, avche_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lavche_parse_fail\n" ++
  "  la t0, avche_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lavche_size_fail\n" ++
  "  la t0, avche_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  la t4, avche_empty_code_hash\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lavche_not_empty\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lavche_not_empty\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lavche_not_empty\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lavche_not_empty\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  ".Lavche_not_empty:\n" ++
  "  li a0, 0\n" ++
  "  j .Lavche_ret\n" ++
  ".Lavche_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lavche_ret\n" ++
  ".Lavche_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lavche_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def ziskAccountValidateCodeHashEmptyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)\n" ++
  "  addi a0, a3, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, account_validate_code_hash_empty\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lavche_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountValidateCodeHashEmptyFunction ++ "\n" ++
  ".Lavche_pdone:"

def ziskAccountValidateCodeHashEmptyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "avche_offset:\n" ++
  "  .zero 8\n" ++
  "avche_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "avche_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"

def ziskAccountValidateCodeHashEmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountValidateCodeHashEmptyPrologue
  dataAsm     := ziskAccountValidateCodeHashEmptyDataSection
}

/-! ## account_validate_storage_root_empty -- PR-K235

    Predicate: `account.storage_root == EMPTY_TRIE_ROOT` where
    `EMPTY_TRIE_ROOT = keccak256(rlp(b'')) =
        0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421`

    The "account has no storage" check. Used as a constituent
    of "fresh account / dust prune" decisions and as a quick
    skip predicate when iterating accounts for state-root
    recomputation.

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : u64 out (1 if storage_root == EMPTY_TRIE_ROOT)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse failure / field 2 missing
        2 : field 2 length != 32 -/
def accountValidateStorageRootEmptyFunction : String :=
  "account_validate_storage_root_empty:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # out u64 ptr\n" ++
  "  sd zero, 0(s2)\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  li a2, 2\n" ++
  "  la a3, avsre_offset; la a4, avsre_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lavsre_parse_fail\n" ++
  "  la t0, avsre_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lavsre_size_fail\n" ++
  "  la t0, avsre_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  la t4, avsre_empty_trie_root\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lavsre_not_empty\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lavsre_not_empty\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lavsre_not_empty\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lavsre_not_empty\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  ".Lavsre_not_empty:\n" ++
  "  li a0, 0\n" ++
  "  j .Lavsre_ret\n" ++
  ".Lavsre_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lavsre_ret\n" ++
  ".Lavsre_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lavsre_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def ziskAccountValidateStorageRootEmptyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)\n" ++
  "  addi a0, a3, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, account_validate_storage_root_empty\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lavsre_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountValidateStorageRootEmptyFunction ++ "\n" ++
  ".Lavsre_pdone:"

def ziskAccountValidateStorageRootEmptyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "avsre_offset:\n" ++
  "  .zero 8\n" ++
  "avsre_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "avsre_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21"

def ziskAccountValidateStorageRootEmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountValidateStorageRootEmptyPrologue
  dataAsm     := ziskAccountValidateStorageRootEmptyDataSection
}

/-! ## account_validate_nonce_zero -- PR-K242

    Predicate: `account.nonce == 0`. RLP canonical zero is the
    empty byte string, so this is the predicate
    `length(field 0) == 0`. Useful for fresh-account / dust-prune
    detection; complements K234 (code_hash empty) and K235
    (storage_root empty).

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : u64 out (1 if nonce == 0)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse failure / field 0 missing -/
def accountValidateNonceZeroFunction : String :=
  "account_validate_nonce_zero:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp)\n" ++
  "  mv s0, a2                      # is_valid out\n" ++
  "  sd zero, 0(s0)\n" ++
  "  li a2, 0                       # field 0 = nonce\n" ++
  "  la a3, avnz_offset; la a4, avnz_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lavnz_parse_fail\n" ++
  "  la t0, avnz_length; ld t1, 0(t0)\n" ++
  "  bnez t1, .Lavnz_nonzero\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s0)\n" ++
  ".Lavnz_nonzero:\n" ++
  "  li a0, 0\n" ++
  "  j .Lavnz_ret\n" ++
  ".Lavnz_parse_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lavnz_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

def ziskAccountValidateNonceZeroPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)\n" ++
  "  addi a0, a3, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, account_validate_nonce_zero\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lavnz_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountValidateNonceZeroFunction ++ "\n" ++
  ".Lavnz_pdone:"

def ziskAccountValidateNonceZeroDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "avnz_offset:\n" ++
  "  .zero 8\n" ++
  "avnz_length:\n" ++
  "  .zero 8"

def ziskAccountValidateNonceZeroProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountValidateNonceZeroPrologue
  dataAsm     := ziskAccountValidateNonceZeroDataSection
}

/-! ## account_charge_gas_pre_exec -- PR-K81

    Apply the pre-EVM sender-account mutation per Python's
    `process_transaction`:

      sender.balance -= effective_gas_price * gas_limit
      sender.nonce   += 1

    Mirrors the upfront max-gas-fee withdrawal in Python:

      sender_account.balance -= effective_gas_price * tx.gas
      sender_account.nonce   += 1

    Note: tx.value is NOT deducted here — it's transferred
    internally by the EVM via CALL/CREATE semantics. This helper
    only handles the gas-fee deduction + nonce bump.

    Post-execution, the caller refunds unused gas via:

      sender.balance += remaining_gas * effective_gas_price

    Composes:
      - PR-K54 `u256_mul_u64_be` — compute gas_fee
      - PR-K52 `u256_sub_be`     — deduct from balance

    The caller passes the current nonce via an in-out `nonce_ptr`
    (u64); this helper reads it, then writes back `nonce + 1`.
    The balance is modified in place.

    Calling convention:
      a0 (input)  : balance ptr (32 B u256 BE; modified in place)
      a1 (input)  : effective_gas_price ptr (32 B u256 BE)
      a2 (input)  : gas_limit (u64)
      a3 (input)  : nonce ptr (u64; in-out; receives nonce+1)
      ra (input)  : return
      a0 (output) :
        0  : success — balance reduced, nonce incremented
        1  : gas_fee computation overflowed u256
        2  : balance < gas_fee (caller should have already
             rejected via PR-K79 `validate_transaction_balance`,
             but the underflow is reported as a safety net)

    Uses 32 bytes of `.data` scratch (`acpg_gas_fee`) plus the
    40-byte `u256m_acc` scratch from PR-K54. -/
def accountChargeGasPreExecFunction : String :=
  "account_charge_gas_pre_exec:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0                   # balance ptr\n" ++
  "  mv s1, a3                   # nonce ptr (in-out)\n" ++
  "  # gas_fee = effective_gas_price × gas_limit\n" ++
  "  mv a0, a1\n" ++
  "  mv a1, a2\n" ++
  "  la a2, acpg_gas_fee\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lacpg_fail_mul\n" ++
  "  # balance -= gas_fee\n" ++
  "  mv a0, s0\n" ++
  "  la a1, acpg_gas_fee\n" ++
  "  mv a2, s0\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  bnez a0, .Lacpg_fail_sub\n" ++
  "  # *nonce_ptr += 1\n" ++
  "  ld t0, 0(s1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  sd t0, 0(s1)\n" ++
  "  li a0, 0\n" ++
  "  j .Lacpg_ret\n" ++
  ".Lacpg_fail_mul:\n" ++
  "  li a0, 1\n" ++
  "  j .Lacpg_ret\n" ++
  ".Lacpg_fail_sub:\n" ++
  "  li a0, 2\n" ++
  ".Lacpg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret"

/-- `zisk_account_charge_gas_pre_exec`: probe BuildUnit. Reads
    (32B balance, 32B egp, 8B gas_limit LE, 8B nonce LE) from
    host input; copies them into OUTPUT-resident buffers; calls
    the helper; writes (status, new_balance, new_nonce) to
    OUTPUT (8 + 32 + 8 = 48 bytes). -/
def ziskAccountChargeGasPreExecPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  # Copy balance to OUTPUT + 8 (in-place mutation target)\n" ++
  "  li a0, 0xa0010008\n" ++
  "  addi t1, a4, 8\n" ++
  "  ld t2,  0(t1); sd t2,  0(a0)\n" ++
  "  ld t2,  8(t1); sd t2,  8(a0)\n" ++
  "  ld t2, 16(t1); sd t2, 16(a0)\n" ++
  "  ld t2, 24(t1); sd t2, 24(a0)\n" ++
  "  # egp ptr → input region\n" ++
  "  addi a1, a4, 40             # egp ptr at file offset 32\n" ++
  "  ld a2, 72(a4)               # gas_limit\n" ++
  "  # Copy nonce to OUTPUT + 40 (8 B in-out scratch)\n" ++
  "  li a3, 0xa0010028\n" ++
  "  ld t2, 80(a4)\n" ++
  "  sd t2, 0(a3)\n" ++
  "  jal ra, account_charge_gas_pre_exec\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lacpg_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  accountChargeGasPreExecFunction ++ "\n" ++
  ".Lacpg_pdone:"

def ziskAccountChargeGasPreExecDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "acpg_gas_fee:\n" ++
  "  .zero 32"

def ziskAccountChargeGasPreExecProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountChargeGasPreExecPrologue
  dataAsm     := ziskAccountChargeGasPreExecDataSection
}

/-! ## tx_upfront_precharge -- compose transaction gas pricing + pre-charge

    Standalone pre-execution gas mutation for one encoded transaction:

      1. parse tx.nonce and tx.gas_limit,
      2. compute effective_gas_price and priority_fee_per_gas from the tx and
         block base_fee_per_gas,
      3. call `account_charge_gas_pre_exec` to deduct
         effective_gas_price * tx.gas_limit and increment the sender nonce.

    This helper intentionally works on caller-supplied balance and nonce
    buffers. BAL/state lookup and stateless-verdict wiring are separate slices.

    Calling convention:
      a0 (input)  : tx bytes ptr
      a1 (input)  : tx byte length
      a2 (input)  : base_fee_per_gas ptr (32 B BE)
      a3 (input)  : sender balance ptr (32 B BE; modified in place)
      a4 (input)  : sender nonce ptr (u64; modified in place on success)
      ra (input)  : return
      a0 (output) :
        0  : success
        10 : tx nonce/gas extraction failed
        20 : effective gas pricing failed
        31 : gas_fee multiplication overflowed u256
        32 : balance < gas_fee

    On success and pricing success, `txup_effective_gas_price`,
    `txup_priority_fee`, and `txup_gas_limit` are populated for callers that
    need post-execution settlement. -/
def txUpfrontPrechargeFunction : String :=
  "tx_upfront_precharge:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx len\n" ++
  "  mv s2, a2                   # base_fee ptr\n" ++
  "  mv s3, a3                   # sender balance ptr\n" ++
  "  mv s4, a4                   # sender nonce ptr\n" ++
  "  la t0, txup_nonce; sd zero, 0(t0)\n" ++
  "  la t0, txup_gas_limit; sd zero, 0(t0)\n" ++
  "  la t0, txup_effective_gas_price\n" ++
  "  sd zero,  0(t0); sd zero,  8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t0, txup_priority_fee\n" ++
  "  sd zero,  0(t0); sd zero,  8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  # Step 1: parse nonce and gas_limit.\n" ++
  "  mv a0, s0; mv a1, s1; la a2, txup_nonce; la a3, txup_gas_limit\n" ++
  "  jal ra, tx_extract_nonce_and_gas\n" ++
  "  beqz a0, .Ltxup_have_gas\n" ++
  "  li a0, 10\n" ++
  "  j .Ltxup_ret\n" ++
  ".Ltxup_have_gas:\n" ++
  "  # Step 2: compute effective gas price and priority fee.\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2\n" ++
  "  la a3, txup_effective_gas_price; la a4, txup_priority_fee\n" ++
  "  jal ra, tx_effective_gas_pricing\n" ++
  "  beqz a0, .Ltxup_have_pricing\n" ++
  "  li a0, 20\n" ++
  "  j .Ltxup_ret\n" ++
  ".Ltxup_have_pricing:\n" ++
  "  # Step 3: deduct effective_gas_price * gas_limit and increment nonce.\n" ++
  "  mv a0, s3; la a1, txup_effective_gas_price\n" ++
  "  la t0, txup_gas_limit; ld a2, 0(t0)\n" ++
  "  mv a3, s4\n" ++
  "  jal ra, account_charge_gas_pre_exec\n" ++
  "  beqz a0, .Ltxup_ok\n" ++
  "  li t0, 1; beq a0, t0, .Ltxup_fail_mul\n" ++
  "  li a0, 32\n" ++
  "  j .Ltxup_ret\n" ++
  ".Ltxup_fail_mul:\n" ++
  "  li a0, 31\n" ++
  "  j .Ltxup_ret\n" ++
  ".Ltxup_ok:\n" ++
  "  li a0, 0\n" ++
  ".Ltxup_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_tx_upfront_precharge`: probe BuildUnit. Reads
    (32B base_fee, 32B balance, 8B nonce, 8B tx_len, tx_bytes), copies balance
    and nonce to OUTPUT-resident mutable buffers, calls `tx_upfront_precharge`,
    then writes:

      OUTPUT+0   : status
      OUTPUT+8   : sender balance (32 B BE)
      OUTPUT+40  : sender nonce (u64 LE)
      OUTPUT+48  : tx gas_limit (u64 LE)
      OUTPUT+56  : effective_gas_price (32 B BE)
      OUTPUT+88  : priority_fee_per_gas (32 B BE) -/
def ziskTxUpfrontPrechargePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  # Copy sender balance to OUTPUT + 8 (in-place mutation target).\n" ++
  "  li a3, 0xa0010008\n" ++
  "  addi t1, a5, 40\n" ++
  "  ld t2,  0(t1); sd t2,  0(a3)\n" ++
  "  ld t2,  8(t1); sd t2,  8(a3)\n" ++
  "  ld t2, 16(t1); sd t2, 16(a3)\n" ++
  "  ld t2, 24(t1); sd t2, 24(a3)\n" ++
  "  # Copy sender nonce to OUTPUT + 40 (in-out scratch).\n" ++
  "  li a4, 0xa0010028\n" ++
  "  ld t2, 72(a5)\n" ++
  "  sd t2, 0(a4)\n" ++
  "  addi a2, a5, 8              # base_fee ptr\n" ++
  "  ld a1, 80(a5)               # tx_len\n" ++
  "  addi a0, a5, 88             # tx ptr\n" ++
  "  jal ra, tx_upfront_precharge\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, txup_gas_limit; ld t2, 0(t1); sd t2, 48(t0)\n" ++
  "  la t1, txup_effective_gas_price\n" ++
  "  ld t2,  0(t1); sd t2,  56(t0)\n" ++
  "  ld t2,  8(t1); sd t2,  64(t0)\n" ++
  "  ld t2, 16(t1); sd t2,  72(t0)\n" ++
  "  ld t2, 24(t1); sd t2,  80(t0)\n" ++
  "  la t1, txup_priority_fee\n" ++
  "  ld t2,  0(t1); sd t2,  88(t0)\n" ++
  "  ld t2,  8(t1); sd t2,  96(t0)\n" ++
  "  ld t2, 16(t1); sd t2, 104(t0)\n" ++
  "  ld t2, 24(t1); sd t2, 112(t0)\n" ++
  "  j .Ltxup_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractNonceAndGasFunction ++ "\n" ++
  txExtractGasPricingFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256MinFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  priorityFeePerGasEip1559Function ++ "\n" ++
  txEffectiveGasPricingFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  accountChargeGasPreExecFunction ++ "\n" ++
  txUpfrontPrechargeFunction ++ "\n" ++
  ".Ltxup_pdone:"

def ziskTxUpfrontPrechargeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "teng_type:\n" ++
  "  .zero 8\n" ++
  "teng_inner_off:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "tegp_type:\n" ++
  "  .zero 8\n" ++
  "tegp_inner_off:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "tefgp_max_priority:\n" ++
  "  .zero 32\n" ++
  "tefgp_max_fee:\n" ++
  "  .zero 32\n" ++
  "tefgp_tmp:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "txup_nonce:\n" ++
  "  .zero 8\n" ++
  "txup_gas_limit:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "txup_effective_gas_price:\n" ++
  "  .zero 32\n" ++
  "txup_priority_fee:\n" ++
  "  .zero 32\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "acpg_gas_fee:\n" ++
  "  .zero 32"

def ziskTxUpfrontPrechargeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxUpfrontPrechargePrologue
  dataAsm     := ziskTxUpfrontPrechargeDataSection
}

/-! ## account_refund_gas_post_exec -- PR-K82

    Apply the post-EVM gas accounting mutations per Python's
    `process_transaction`:

      gas_refund    = remaining_gas * effective_gas_price
      sender.balance   += gas_refund
      priority_credit  = gas_used * priority_fee_per_gas
      coinbase.balance += priority_credit

    Where `priority_fee_per_gas = effective_gas_price - base_fee_per_gas`
    (the pre-computed result from PR-K62
    `priority_fee_per_gas_eip1559`).

    Sister to PR-K81 `account_charge_gas_pre_exec`. Together they
    bracket `execute_message`:

      pre:  K81 → sender.balance -= max_gas_fee; sender.nonce++
      ...   EVM run
      post: K82 → sender.balance += gas_refund;
                 coinbase.balance += priority_credit

    Composes:
      - PR-K54 `u256_mul_u64_be` × 2 (sender_refund + coinbase_credit)
      - PR-K51 `u256_add_be` × 2

    Calling convention:
      a0 (input)  : sender.balance ptr (32 B u256 BE; mod in place)
      a1 (input)  : coinbase.balance ptr (32 B u256 BE; mod in place)
      a2 (input)  : effective_gas_price ptr (32 B u256 BE)
      a3 (input)  : priority_fee_per_gas ptr (32 B u256 BE)
      a4 (input)  : gas_used (u64)
      a5 (input)  : remaining_gas (u64)
      ra (input)  : return
      a0 (output) :
        0  : success — both balances updated
        1  : mul overflow on refund or credit
        2  : add overflow on either balance

    Uses 64 bytes of `.data` scratch (`arg_sender_refund` +
    `arg_coinbase_credit`) plus the 40-byte `u256m_acc`. -/
def accountRefundGasPostExecFunction : String :=
  "account_refund_gas_post_exec:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # sender ptr\n" ++
  "  mv s1, a1                   # coinbase ptr\n" ++
  "  mv s2, a3                   # priority_fee ptr (saved for step 2)\n" ++
  "  mv s3, a4                   # gas_used (saved for step 2)\n" ++
  "  mv s4, a2                   # egp ptr (also saved; step 1 uses)\n" ++
  "  # Step 1: sender_refund = remaining_gas × egp\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, a5\n" ++
  "  la a2, arg_sender_refund\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Largpe_fail_mul\n" ++
  "  # Step 2: coinbase_credit = gas_used × priority_fee\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s3\n" ++
  "  la a2, arg_coinbase_credit\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Largpe_fail_mul\n" ++
  "  # Step 3: sender.balance += sender_refund\n" ++
  "  mv a0, s0\n" ++
  "  la a1, arg_sender_refund\n" ++
  "  mv a2, s0\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Largpe_fail_add\n" ++
  "  # Step 4: coinbase.balance += coinbase_credit\n" ++
  "  mv a0, s1\n" ++
  "  la a1, arg_coinbase_credit\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Largpe_fail_add\n" ++
  "  li a0, 0\n" ++
  "  j .Largpe_ret\n" ++
  ".Largpe_fail_mul:\n" ++
  "  li a0, 1\n" ++
  "  j .Largpe_ret\n" ++
  ".Largpe_fail_add:\n" ++
  "  li a0, 2\n" ++
  ".Largpe_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_account_refund_gas_post_exec`: probe BuildUnit. Reads
    (32B sender_bal, 32B coinbase_bal, 32B egp, 32B priority_fee,
    8B gas_used, 8B remaining_gas) from host input. Copies the
    two balances to OUTPUT-resident scratch buffers, calls the
    helper, then writes (status, new_sender, new_coinbase) to
    OUTPUT. Total OUTPUT bytes: 8 + 32 + 32 = 72. -/
def ziskAccountRefundGasPostExecPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  # Copy sender balance to OUTPUT + 8\n" ++
  "  li a0, 0xa0010008\n" ++
  "  addi t1, a6, 8\n" ++
  "  ld t2,  0(t1); sd t2,  0(a0)\n" ++
  "  ld t2,  8(t1); sd t2,  8(a0)\n" ++
  "  ld t2, 16(t1); sd t2, 16(a0)\n" ++
  "  ld t2, 24(t1); sd t2, 24(a0)\n" ++
  "  # Copy coinbase balance to OUTPUT + 40\n" ++
  "  li a1, 0xa0010028\n" ++
  "  addi t1, a6, 40\n" ++
  "  ld t2,  0(t1); sd t2,  0(a1)\n" ++
  "  ld t2,  8(t1); sd t2,  8(a1)\n" ++
  "  ld t2, 16(t1); sd t2, 16(a1)\n" ++
  "  ld t2, 24(t1); sd t2, 24(a1)\n" ++
  "  addi a2, a6, 72             # egp ptr\n" ++
  "  addi a3, a6, 104            # priority_fee ptr\n" ++
  "  ld a4, 136(a6)              # gas_used\n" ++
  "  ld a5, 144(a6)              # remaining_gas\n" ++
  "  jal ra, account_refund_gas_post_exec\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Largpe_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  accountRefundGasPostExecFunction ++ "\n" ++
  ".Largpe_pdone:"

def ziskAccountRefundGasPostExecDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "arg_sender_refund:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "arg_coinbase_credit:\n" ++
  "  .zero 32"

def ziskAccountRefundGasPostExecProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountRefundGasPostExecPrologue
  dataAsm     := ziskAccountRefundGasPostExecDataSection
}

/-! ## tx_post_exec_gas_settlement

    Transaction-level post-execution gas settlement wrapper. The lower-level
    `account_refund_gas_post_exec` helper takes `gas_used` and
    `remaining_gas`; callers that bracket one transaction naturally have
    `tx.gas_limit` from pre-charge plus the interpreter's final
    `remaining_gas`. This wrapper computes:

      gas_used = tx_gas_limit - remaining_gas

    rejects the impossible underflow shape, then applies the sender refund and
    coinbase priority-fee credit through `account_refund_gas_post_exec`.

    Calling convention:
      a0 (input)  : sender.balance ptr (32 B u256 BE; modified in place)
      a1 (input)  : coinbase.balance ptr (32 B u256 BE; modified in place)
      a2 (input)  : effective_gas_price ptr (32 B u256 BE)
      a3 (input)  : priority_fee_per_gas ptr (32 B u256 BE)
      a4 (input)  : tx_gas_limit (u64)
      a5 (input)  : remaining_gas after execution (u64)
      ra (input)  : return
      a0 (output) :
        0  : success — both balances updated
        1  : mul overflow on refund or credit
        2  : add overflow on either balance
        3  : remaining_gas > tx_gas_limit

    On success, `txpost_gas_used` is populated for receipt/cumulative-gas
    materialization. -/
def txPostExecGasSettlementFunction : String :=
  "tx_post_exec_gas_settlement:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # sender ptr\n" ++
  "  mv s1, a1                   # coinbase ptr\n" ++
  "  mv s2, a2                   # effective gas price ptr\n" ++
  "  mv s3, a3                   # priority fee ptr\n" ++
  "  mv s4, a4                   # tx gas limit\n" ++
  "  mv s5, a5                   # remaining gas\n" ++
  "  la t0, txpost_gas_used; sd zero, 0(t0)\n" ++
  "  bgtu s5, s4, .Ltxpost_bad_remaining\n" ++
  "  sub a4, s4, s5              # gas_used\n" ++
  "  la t0, txpost_gas_used; sd a4, 0(t0)\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; mv a5, s5\n" ++
  "  jal ra, account_refund_gas_post_exec\n" ++
  "  j .Ltxpost_ret\n" ++
  ".Ltxpost_bad_remaining:\n" ++
  "  li a0, 3\n" ++
  ".Ltxpost_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_tx_post_exec_gas_settlement`: probe BuildUnit. Reads
    (32B sender_bal, 32B coinbase_bal, 32B egp, 32B priority_fee,
    8B tx_gas_limit, 8B remaining_gas) from host input. Copies the
    two balances to OUTPUT-resident scratch buffers, calls the
    wrapper, then writes:

      OUTPUT+0   : status
      OUTPUT+8   : sender balance (32 B BE)
      OUTPUT+40  : coinbase balance (32 B BE)
      OUTPUT+72  : gas_used (u64 LE) -/
def ziskTxPostExecGasSettlementPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  # Copy sender balance to OUTPUT + 8\n" ++
  "  li a0, 0xa0010008\n" ++
  "  addi t1, a6, 8\n" ++
  "  ld t2,  0(t1); sd t2,  0(a0)\n" ++
  "  ld t2,  8(t1); sd t2,  8(a0)\n" ++
  "  ld t2, 16(t1); sd t2, 16(a0)\n" ++
  "  ld t2, 24(t1); sd t2, 24(a0)\n" ++
  "  # Copy coinbase balance to OUTPUT + 40\n" ++
  "  li a1, 0xa0010028\n" ++
  "  addi t1, a6, 40\n" ++
  "  ld t2,  0(t1); sd t2,  0(a1)\n" ++
  "  ld t2,  8(t1); sd t2,  8(a1)\n" ++
  "  ld t2, 16(t1); sd t2, 16(a1)\n" ++
  "  ld t2, 24(t1); sd t2, 24(a1)\n" ++
  "  addi a2, a6, 72             # egp ptr\n" ++
  "  addi a3, a6, 104            # priority_fee ptr\n" ++
  "  ld a4, 136(a6)              # tx_gas_limit\n" ++
  "  ld a5, 144(a6)              # remaining_gas\n" ++
  "  jal ra, tx_post_exec_gas_settlement\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  la t1, txpost_gas_used; ld t2, 0(t1); sd t2, 72(t0)\n" ++
  "  j .Ltxpost_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  accountRefundGasPostExecFunction ++ "\n" ++
  txPostExecGasSettlementFunction ++ "\n" ++
  ".Ltxpost_pdone:"

def ziskTxPostExecGasSettlementDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "arg_sender_refund:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "arg_coinbase_credit:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "txpost_gas_used:\n" ++
  "  .zero 8"

def ziskTxPostExecGasSettlementProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxPostExecGasSettlementPrologue
  dataAsm     := ziskTxPostExecGasSettlementDataSection
}

/-! ## tx_gas_result_increments

    EIP-7623/EIP-7778 gas increments derived from execution results.
    This is the scalar post-execution formula used by Amsterdam
    `process_transaction` before block-output and receipt updates:

      before_refund = tx.gas - tx_output.gas_left
      refund        = min(before_refund / 5, tx_output.refund_counter)
      after_refund  = before_refund - refund
      receipt_inc   = max(after_refund, calldata_floor_gas_cost)
      block_inc     = max(before_refund, calldata_floor_gas_cost)

    Calling convention:
      a0 (input)  : tx_gas_limit u64
      a1 (input)  : gas_left after execution u64
      a2 (input)  : refund_counter u64
      a3 (input)  : calldata_floor_gas_cost u64
      ra (input)  : return
      a0 (output) : status, 0 ok; 1 if gas_left > tx_gas_limit
      a1 (output) : block_gas_used_in_tx
      a2 (output) : receipt gas increment
      a3 (output) : tx_gas_used_before_refund
      a4 (output) : applied refund
-/
def txGasResultIncrementsFunction : String :=
  "tx_gas_result_increments:\n" ++
  "  bgtu a1, a0, .Ltgri_bad_remaining\n" ++
  "  sub t0, a0, a1              # before_refund\n" ++
  "  li t1, 5\n" ++
  "  divu t2, t0, t1             # refund cap = before_refund / 5\n" ++
  "  mv t3, a2                   # refund_counter\n" ++
  "  bleu t3, t2, .Ltgri_refund_min_done\n" ++
  "  mv t3, t2\n" ++
  ".Ltgri_refund_min_done:\n" ++
  "  sub t4, t0, t3              # after_refund\n" ++
  "  mv t5, t0                   # block_inc = max(before_refund, floor)\n" ++
  "  bleu a3, t5, .Ltgri_block_max_done\n" ++
  "  mv t5, a3\n" ++
  ".Ltgri_block_max_done:\n" ++
  "  mv t6, t4                   # receipt_inc = max(after_refund, floor)\n" ++
  "  bleu a3, t6, .Ltgri_receipt_max_done\n" ++
  "  mv t6, a3\n" ++
  ".Ltgri_receipt_max_done:\n" ++
  "  li a0, 0\n" ++
  "  mv a1, t5\n" ++
  "  mv a2, t6\n" ++
  "  mv a3, t0\n" ++
  "  mv a4, t3\n" ++
  "  ret\n" ++
  ".Ltgri_bad_remaining:\n" ++
  "  li a0, 1\n" ++
  "  li a1, 0\n" ++
  "  li a2, 0\n" ++
  "  li a3, 0\n" ++
  "  li a4, 0\n" ++
  "  ret"

/-- `zisk_tx_gas_result_increments`: focused probe for the scalar
    post-execution gas increment formula. Input payload after zisk's length
    prefix is four u64s: tx_gas_limit, gas_left, refund_counter,
    calldata_floor_gas_cost. Output is five u64s: status, block increment,
    receipt increment, before-refund gas, applied refund. -/
def ziskTxGasResultIncrementsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  ld a0,  8(s0)              # tx_gas_limit\n" ++
  "  ld a1, 16(s0)              # gas_left\n" ++
  "  ld a2, 24(s0)              # refund_counter\n" ++
  "  ld a3, 32(s0)              # calldata_floor_gas_cost\n" ++
  "  jal ra, tx_gas_result_increments\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0,  0(t0)\n" ++
  "  sd a1,  8(t0)\n" ++
  "  sd a2, 16(t0)\n" ++
  "  sd a3, 24(t0)\n" ++
  "  sd a4, 32(t0)\n" ++
  "  j .Ltgri_probe_done\n" ++
  txGasResultIncrementsFunction ++ "\n" ++
  ".Ltgri_probe_done:"

def ziskTxGasResultIncrementsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxGasResultIncrementsPrologue
  dataAsm     := ".section .data\n.balign 8\n"
}

/-! ## account_validate_balance_zero -- PR-K259

    Predicate: `account.balance == 0`. RLP canonical zero is the
    empty byte string, so this is the predicate
    `length(field 1) == 0`. Mirror of K242
    `account_validate_nonce_zero`; completes the
    nonce/balance/storage_root/code_hash zero-predicates pair
    needed for EIP-161 emptiness checks.

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : u64 out (1 if balance == 0)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse failure / field 1 missing -/
def accountValidateBalanceZeroFunction : String :=
  "account_validate_balance_zero:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp)\n" ++
  "  mv s0, a2                      # is_valid out\n" ++
  "  sd zero, 0(s0)\n" ++
  "  li a2, 1                       # field 1 = balance\n" ++
  "  la a3, avbz_offset; la a4, avbz_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lavbz_parse_fail\n" ++
  "  la t0, avbz_length; ld t1, 0(t0)\n" ++
  "  bnez t1, .Lavbz_nonzero\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s0)\n" ++
  ".Lavbz_nonzero:\n" ++
  "  li a0, 0\n" ++
  "  j .Lavbz_ret\n" ++
  ".Lavbz_parse_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lavbz_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

def ziskAccountValidateBalanceZeroPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)\n" ++
  "  addi a0, a3, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, account_validate_balance_zero\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lavbz_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountValidateBalanceZeroFunction ++ "\n" ++
  ".Lavbz_pdone:"

def ziskAccountValidateBalanceZeroDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "avbz_offset:\n" ++
  "  .zero 8\n" ++
  "avbz_length:\n" ++
  "  .zero 8"

def ziskAccountValidateBalanceZeroProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountValidateBalanceZeroPrologue
  dataAsm     := ziskAccountValidateBalanceZeroDataSection
}

end EvmAsm.Codegen
