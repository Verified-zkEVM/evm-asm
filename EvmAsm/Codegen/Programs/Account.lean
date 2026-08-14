/-
  EvmAsm.Codegen.Programs.Account

  Ethereum-account RLP accessors and predicates carved out of
  `EvmAsm.Codegen.Programs.Tx` per the file-size hard cap. Hosts:

    K121  account_extract_nonce    (field 0, u64)
    K120  account_extract_balance  (field 1, u256 BE)
    K123  account_is_empty         (EIP-161 emptiness)

  `account_is_empty` uses the cursor-walk helpers from `Programs/RlpWalk.lean`.
  The remaining standalone field predicates in this file still use indexed RLP
  access through `rlp_list_nth_item` where they perform one-off lookups.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.U256GasPricing

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

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

    Composes a single RLP cursor walk over the four account fields:
      - field 0 content decoded by rlp_content_to_u64 for nonce
      - field 1 content decoded by rlp_content_to_u256_be for balance
      - field 3 content copied/compared directly for code_hash

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : u64 out ptr (1 if empty, 0 if non-empty)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written to *out
        1 : RLP parse failure / field missing / wrong width

    Uses `.data` scratch for `aie_nonce` (u64), `aie_balance` (32 B), and the
    `aie_empty_code_hash` constant. The probe data section also carries legacy
    offset/length cells for sibling indexed helpers. -/
def accountIsEmptyFunction : String :=
  "account_is_empty:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # out u64 ptr\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Step 1: initialize the account field cursor.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Laie_parse_fail\n" ++
  "  mv s3, a0                   # cursor\n" ++
  "  mv s4, a1                   # end\n" ++
  "  # Step 2: nonce (field 0) -> aie_nonce.\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Laie_parse_fail\n" ++
  "  sub t0, a0, a2; mv s3, a0; mv a0, t0; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Laie_parse_fail\n" ++
  "  la t0, aie_nonce; sd a0, 0(t0)\n" ++
  "  mv t1, a0\n" ++
  "  bnez t1, .Laie_not_empty\n" ++
  "  # Step 3: balance (field 1, u256 BE) -> aie_balance.\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Laie_parse_fail\n" ++
  "  sub t0, a0, a2; mv s3, a0; mv a0, t0; mv a1, a2; la a2, aie_balance\n" ++
  "  jal ra, rlp_content_to_u256_be\n" ++
  "  bnez a0, .Laie_parse_fail\n" ++
  "  la t0, aie_balance\n" ++
  "  ld t1,  0(t0); bnez t1, .Laie_not_empty\n" ++
  "  ld t1,  8(t0); bnez t1, .Laie_not_empty\n" ++
  "  ld t1, 16(t0); bnez t1, .Laie_not_empty\n" ++
  "  ld t1, 24(t0); bnez t1, .Laie_not_empty\n" ++
  "  # Step 4: skip storage_root (field 2).\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Laie_parse_fail; mv s3, a0\n" ++
  "  # Step 5: code_hash (field 3) compared against EMPTY_CODE_HASH.\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Laie_parse_fail\n" ++
  "  mv t1, a2\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Laie_parse_fail\n" ++
  "  sub t3, a0, a2\n" ++
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
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
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
  rlpWalkHelpersClosure ++ "\n" ++
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
def accountChargeGasPreExec_prog : Program :=
  [ .ADDI .x2 .x2 (-24 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x13,
    .MV .x10 .x11,
    .MV .x11 .x12,
    .AUIPC .x12 (laHi GuestAddrs.acpg_gas_fee (GuestAddrs.account_charge_gas_pre_exec + 32)),
    .ADDI .x12 .x12 (laLo GuestAddrs.acpg_gas_fee (GuestAddrs.account_charge_gas_pre_exec + 32)),
    .JAL .x1 (jalOff GuestAddrs.u256_mul_u64_be (GuestAddrs.account_charge_gas_pre_exec + 40)),
    .BNE .x10 .x0 (48 : BitVec 13),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.acpg_gas_fee (GuestAddrs.account_charge_gas_pre_exec + 52)),
    .ADDI .x11 .x11 (laLo GuestAddrs.acpg_gas_fee (GuestAddrs.account_charge_gas_pre_exec + 52)),
    .MV .x12 .x8,
    .JAL .x1 (jalOff GuestAddrs.u256_sub_be (GuestAddrs.account_charge_gas_pre_exec + 64)),
    .BNE .x10 .x0 (32 : BitVec 13),
    .LD .x5 .x9 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .SD .x9 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (24 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountChargeGasPreExec_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountChargeGasPreExec_relocs : RelocTable :=
  [ (8, .la .x12 "acpg_gas_fee"),
    (10, .jal .x1 "u256_mul_u64_be"),
    (13, .la .x11 "acpg_gas_fee"),
    (16, .jal .x1 "u256_sub_be") ]

def accountChargeGasPreExecFunction : String :=
  "account_charge_gas_pre_exec:\n" ++ emitProgramR accountChargeGasPreExec_prog accountChargeGasPreExec_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountChargeGasPreExec_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountChargeGasPreExecFunction_eq_prog :
    accountChargeGasPreExecFunction = "account_charge_gas_pre_exec:\n" ++ emitProgramR accountChargeGasPreExec_prog accountChargeGasPreExec_relocs := rfl

#guard accountChargeGasPreExecFunction.startsWith "account_charge_gas_pre_exec:\n"
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
def txUpfrontPrecharge_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .AUIPC .x5 (laHi GuestAddrs.txup_nonce (GuestAddrs.tx_upfront_precharge + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.txup_nonce (GuestAddrs.tx_upfront_precharge + 52)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.txup_gas_limit (GuestAddrs.tx_upfront_precharge + 64)),
    .ADDI .x5 .x5 (laLo GuestAddrs.txup_gas_limit (GuestAddrs.tx_upfront_precharge + 64)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.txup_effective_gas_price (GuestAddrs.tx_upfront_precharge + 76)),
    .ADDI .x5 .x5 (laLo GuestAddrs.txup_effective_gas_price (GuestAddrs.tx_upfront_precharge + 76)),
    .SD .x5 .x0 (0 : BitVec 12),
    .SD .x5 .x0 (8 : BitVec 12),
    .SD .x5 .x0 (16 : BitVec 12),
    .SD .x5 .x0 (24 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.txup_priority_fee (GuestAddrs.tx_upfront_precharge + 100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.txup_priority_fee (GuestAddrs.tx_upfront_precharge + 100)),
    .SD .x5 .x0 (0 : BitVec 12),
    .SD .x5 .x0 (8 : BitVec 12),
    .SD .x5 .x0 (16 : BitVec 12),
    .SD .x5 .x0 (24 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.txup_nonce (GuestAddrs.tx_upfront_precharge + 132)),
    .ADDI .x12 .x12 (laLo GuestAddrs.txup_nonce (GuestAddrs.tx_upfront_precharge + 132)),
    .AUIPC .x13 (laHi GuestAddrs.txup_gas_limit (GuestAddrs.tx_upfront_precharge + 140)),
    .ADDI .x13 .x13 (laLo GuestAddrs.txup_gas_limit (GuestAddrs.tx_upfront_precharge + 140)),
    .JAL .x1 (jalOff GuestAddrs.tx_extract_nonce_and_gas (GuestAddrs.tx_upfront_precharge + 148)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (10 : Word),
    .JAL .x0 (jalOff (GuestAddrs.tx_upfront_precharge + 272) (GuestAddrs.tx_upfront_precharge + 160)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .AUIPC .x13 (laHi GuestAddrs.txup_effective_gas_price (GuestAddrs.tx_upfront_precharge + 176)),
    .ADDI .x13 .x13 (laLo GuestAddrs.txup_effective_gas_price (GuestAddrs.tx_upfront_precharge + 176)),
    .AUIPC .x14 (laHi GuestAddrs.txup_priority_fee (GuestAddrs.tx_upfront_precharge + 184)),
    .ADDI .x14 .x14 (laLo GuestAddrs.txup_priority_fee (GuestAddrs.tx_upfront_precharge + 184)),
    .JAL .x1 (jalOff GuestAddrs.tx_effective_gas_pricing (GuestAddrs.tx_upfront_precharge + 192)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (20 : Word),
    .JAL .x0 (jalOff (GuestAddrs.tx_upfront_precharge + 272) (GuestAddrs.tx_upfront_precharge + 204)),
    .MV .x10 .x19,
    .AUIPC .x11 (laHi GuestAddrs.txup_effective_gas_price (GuestAddrs.tx_upfront_precharge + 212)),
    .ADDI .x11 .x11 (laLo GuestAddrs.txup_effective_gas_price (GuestAddrs.tx_upfront_precharge + 212)),
    .AUIPC .x5 (laHi GuestAddrs.txup_gas_limit (GuestAddrs.tx_upfront_precharge + 220)),
    .ADDI .x5 .x5 (laLo GuestAddrs.txup_gas_limit (GuestAddrs.tx_upfront_precharge + 220)),
    .LD .x12 .x5 (0 : BitVec 12),
    .MV .x13 .x20,
    .JAL .x1 (jalOff GuestAddrs.account_charge_gas_pre_exec (GuestAddrs.tx_upfront_precharge + 236)),
    .BEQ .x10 .x0 (28 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (12 : BitVec 13),
    .LI .x10 (32 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (31 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txUpfrontPrecharge_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txUpfrontPrecharge_relocs : RelocTable :=
  [ (13, .la .x5 "txup_nonce"),
    (16, .la .x5 "txup_gas_limit"),
    (19, .la .x5 "txup_effective_gas_price"),
    (25, .la .x5 "txup_priority_fee"),
    (33, .la .x12 "txup_nonce"),
    (35, .la .x13 "txup_gas_limit"),
    (37, .jal .x1 "tx_extract_nonce_and_gas"),
    (44, .la .x13 "txup_effective_gas_price"),
    (46, .la .x14 "txup_priority_fee"),
    (48, .jal .x1 "tx_effective_gas_pricing"),
    (53, .la .x11 "txup_effective_gas_price"),
    (55, .la .x5 "txup_gas_limit"),
    (59, .jal .x1 "account_charge_gas_pre_exec") ]

def txUpfrontPrechargeFunction : String :=
  "tx_upfront_precharge:\n" ++ emitProgramR txUpfrontPrecharge_prog txUpfrontPrecharge_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txUpfrontPrecharge_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txUpfrontPrechargeFunction_eq_prog :
    txUpfrontPrechargeFunction = "tx_upfront_precharge:\n" ++ emitProgramR txUpfrontPrecharge_prog txUpfrontPrecharge_relocs := rfl

#guard txUpfrontPrechargeFunction.startsWith "tx_upfront_precharge:\n"
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
def txGasResultIncrements_prog : Program :=
  [ .BLTU .x10 .x11 (80 : BitVec 13),
    .SUB .x5 .x10 .x11,
    .LI .x6 (5 : Word),
    .DIVU .x7 .x5 .x6,
    .MV .x28 .x12,
    .BGEU .x7 .x28 (8 : BitVec 13),
    .MV .x28 .x7,
    .SUB .x29 .x5 .x28,
    .MV .x30 .x5,
    .BGEU .x30 .x13 (8 : BitVec 13),
    .MV .x30 .x13,
    .MV .x31 .x29,
    .BGEU .x31 .x13 (8 : BitVec 13),
    .MV .x31 .x13,
    .LI .x10 (0 : Word),
    .MV .x11 .x30,
    .MV .x12 .x31,
    .MV .x13 .x5,
    .MV .x14 .x28,
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LI .x11 (0 : Word),
    .LI .x12 (0 : Word),
    .LI .x13 (0 : Word),
    .LI .x14 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def txGasResultIncrementsFunction : String :=
  "tx_gas_result_increments:\n" ++ emitProgram txGasResultIncrements_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `txGasResultIncrements_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem txGasResultIncrementsFunction_eq_prog :
    txGasResultIncrementsFunction = "tx_gas_result_increments:\n" ++ emitProgram txGasResultIncrements_prog := rfl

#guard txGasResultIncrementsFunction.startsWith "tx_gas_result_increments:\n"
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


end EvmAsm.Codegen
