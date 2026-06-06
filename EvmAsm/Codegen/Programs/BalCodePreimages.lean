/-
  EvmAsm.Codegen.Programs.BalCodePreimages

  BAL-scoped witness.codes preimage gate for the stateless verdict.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.StateCompose
import EvmAsm.Codegen.Programs.Address

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_code_preimages_valid -- reject code-read-shaped accounts whose
    non-empty code_hash is absent from witness.codes.

    This mirrors the executable spec shape where `build_code_db(witness.codes)`
    maps `keccak(code) -> code`, and `WitnessState.get_code` raises if an
    executing or EXTCODE-touched account's non-empty code_hash is not present.
    The helper is deliberately narrow: balance/nonce-only BAL entries do not
    prove that account bytecode was read, so they are skipped. Pure
    account-touch rows are skipped only when `bbcv_skip_touch_only` is set by
    the caller for withdrawal-only blocks. A pure account-touch row whose
    pre-state code hash is exactly keccak(0x00) is also skipped: EIP-7708
    selfdestruct beneficiaries can have one-byte STOP code without requiring
    the bytecode preimage. Scalar rows with nonce changes still require the
    pre-state code preimage: EIP-7702 sender validation reads a delegated
    sender's marker code while incrementing the sender nonce. A pure
    account-touch row is also accepted when a pure account-touch row for the
    block fee recipient is also skipped:
    Amsterdam warms/touches coinbase without reading its bytecode. A
    literal `PUSH20 <address>; EXTCODEHASH` occurs in witness bytecode, since
    EXTCODEHASH reads the account leaf's code_hash and does not call
    WitnessState.get_code. Likewise, literal `PUSHn <address>; BALANCE`
    reads only the account leaf's balance. A pure account-touch row is also accepted when a
    witness bytecode or a legacy transaction data payload contains
    `PUSH20 <address>; SELFDESTRUCT`: the executable spec touches the
    beneficiary account there without reading its bytecode. The same exception
    covers dynamic self-beneficiary bytecode that materializes `ADDRESS` and
    later reaches `SELFDESTRUCT`, as in EIP-6780 create/selfdestruct-same-tx
    fixtures. A pure
    account-touch row is also accepted when it is the
    `CREATE(to, 0)` address for a legacy transaction target and witness bytecode
    contains a CREATE opcode, when it is the top-level CREATE(sender, nonce)
    address for a legacy contract-creation transaction, or when it is a
    CREATE2 address for a BAL creator row with nonce/storage activity, a
    recoverable literal salt, and copied initcode present in witness.codes.
    These match CREATE collision predicate paths (`account_has_code_or_nonce` /
    `account_has_storage`) which do not read bytecode. Rows that carry storage
    or code activity still reject the
    extcodesize helper's status 5 and leave deeper obligations for later gates.
    -/
def balCodePreimagesValidFunction : String :=
  "bal_code_preimages_valid:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                   # BAL ptr\n" ++
  "  mv s1, a1                   # BAL len\n" ++
  "  mv s2, a2                   # parent header RLP ptr\n" ++
  "  mv s3, a3                   # parent header RLP len\n" ++
  "  mv s4, a4                   # witness.state ptr\n" ++
  "  mv s5, a5                   # witness.state len\n" ++
  "  mv s6, a6                   # witness.codes ptr\n" ++
  "  mv s7, a7                   # witness.codes len\n" ++
  "  # Some EEST fixture plumbing passes the parent block RLP here. Normalize\n" ++
  "  # to the header RLP if item 0 is itself a header list rather than the\n" ++
  "  # 32-byte parent_hash field of an already-normalized header.\n" ++
  "  mv a0, s2; mv a1, s3; li a2, 0; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbcv_parent_header_done\n" ++
  "  la t0, bbcv_field_len; ld t1, 0(t0); li t2, 32; beq t1, t2, .Lbbcv_parent_header_done\n" ++
  "  mv a0, s2; mv a1, s3; li a2, 0; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  bnez a0, .Lbbcv_parent_header_done\n" ++
  "  la t0, bbcv_field_off; ld t2, 0(t0); la t0, bbcv_field_len; ld t1, 0(t0); add s2, s2, t2; mv s3, t1\n" ++
  ".Lbbcv_parent_header_done:\n" ++
  "  mv a0, s0; mv a1, s1; la a2, bbcv_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_count; ld s8, 0(t0)\n" ++
  "  li s9, 0\n" ++
  ".Lbbcv_loop:\n" ++
  "  beq s9, s8, .Lbbcv_ok\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s9; la a3, bbcv_off; la a4, bbcv_size\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_off; ld t1, 0(t0); add s10, s0, t1\n" ++
  "  la t0, bbcv_size; ld t1, 0(t0); la t2, bbcv_acct_len; sd t1, 0(t2)\n" ++
  "  mv a0, s10; mv a1, t1; li a2, 0; la a3, bbcv_addr_off; la a4, bbcv_addr_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_addr_len; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lbbcv_parse_fail\n" ++
  "  li t1, 1; la t0, bbcv_touch_only; sd t1, 0(t0)\n" ++
  "  # Balance/nonce-only BAL entries record scalar account effects and do\n" ++
  "  # not imply that account bytecode was read. Pure account-touch rows\n" ++
  "  # are skipped only when the caller marks withdrawal-only mode.\n" ++
  "  mv a0, s10; la t0, bbcv_acct_len; ld a1, 0(t0); li a2, 1; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_off; ld t1, 0(t0); add a0, s10, t1; la t0, bbcv_field_len; ld a1, 0(t0); la a2, bbcv_field_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_count; ld t1, 0(t0); bnez t1, .Lbbcv_check_code_non_touch\n" ++
  "  mv a0, s10; la t0, bbcv_acct_len; ld a1, 0(t0); li a2, 2; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_off; ld t1, 0(t0); add a0, s10, t1; la t0, bbcv_field_len; ld a1, 0(t0); la a2, bbcv_field_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_count; ld t1, 0(t0); bnez t1, .Lbbcv_check_code_non_touch\n" ++
  "  mv a0, s10; la t0, bbcv_acct_len; ld a1, 0(t0); li a2, 3; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_off; ld t1, 0(t0); add a0, s10, t1; la t0, bbcv_field_len; ld a1, 0(t0); la a2, bbcv_field_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_count; ld t1, 0(t0)\n" ++
  "  la t2, bbcv_balance_count; sd t1, 0(t2)\n" ++
  "  mv a0, s10; la t0, bbcv_acct_len; ld a1, 0(t0); li a2, 4; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_off; ld t1, 0(t0); add a0, s10, t1; la t0, bbcv_field_len; ld a1, 0(t0); la a2, bbcv_field_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_count; ld t1, 0(t0)\n" ++
  "  la t2, bbcv_nonce_count; sd t1, 0(t2)\n" ++
  "  mv a0, s10; la t0, bbcv_acct_len; ld a1, 0(t0); li a2, 5; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_off; ld t1, 0(t0); add a0, s10, t1; la t0, bbcv_field_len; ld a1, 0(t0); la a2, bbcv_field_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_count; ld t1, 0(t0); bnez t1, .Lbbcv_check_code_non_touch\n" ++
  "  la t0, bbcv_balance_count; ld t1, 0(t0)\n" ++
  "  la t2, bbcv_nonce_count; ld t3, 0(t2)\n" ++
  "  or t4, t1, t3\n" ++
  "  bnez t4, .Lbbcv_scalar_touch\n" ++
  "  la t0, bbcv_fee_recipient_valid; ld t0, 0(t0); beqz t0, .Lbbcv_touch_skip_flags\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add t1, s10, t1\n" ++
  "  la t2, bbcv_fee_recipient\n" ++
  "  li t3, 20\n" ++
  ".Lbbcv_fee_recipient_cmp:\n" ++
  "  beqz t3, .Lbbcv_next\n" ++
  "  lbu t4, 0(t1); lbu t5, 0(t2); bne t4, t5, .Lbbcv_touch_skip_flags\n" ++
  "  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lbbcv_fee_recipient_cmp\n" ++
  ".Lbbcv_touch_skip_flags:\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a0, s10, t1\n" ++
  "  jal ra, bbcv_addr_is_system_contract\n" ++
  "  bnez a0, .Lbbcv_next\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a2, s10, t1\n" ++
  "  mv a0, s6; mv a1, s7\n" ++
  "  jal ra, bal_codes_contains_push20_code_read\n" ++
  "  bnez a0, .Lbbcv_check_code_non_touch\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a2, s10, t1\n" ++
  "  mv a0, s6; mv a1, s7\n" ++
  "  jal ra, bal_codes_contains_push20_call_target\n" ++
  "  beqz a0, .Lbbcv_touch_skip_flags_done\n" ++
  "  # Failed CALL prechecks still require the target account proof during\n" ++
  "  # executable-spec witness replay. Accept present (0) and absent (1)\n" ++
  "  # account results, but reject parse/proof failures (>= 2).\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a2, s10, t1\n" ++
  "  mv a0, s2; mv a1, s3; li a3, 20; mv a4, s4; mv a5, s5; la a6, bbcv_acct_struct\n" ++
  "  jal ra, account_at_header_state_root\n" ++
  "  li t0, 2; bgeu a0, t0, .Lbbcv_missing_code\n" ++
  ".Lbbcv_touch_skip_flags_done:\n" ++
  "  la t0, bbcv_skip_touch_only; ld t4, 0(t0)\n" ++
  "  bnez t4, .Lbbcv_next\n" ++
  "  j .Lbbcv_check_code\n" ++
  ".Lbbcv_scalar_touch:\n" ++
  "  # Balance-only rows normally do not prove bytecode was read, but nonce\n" ++
  "  # changes do: EIP-7702 sender validation reads delegated sender markers.\n" ++
  "  la t0, bbcv_nonce_count; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lbbcv_scalar_sender_fallback\n" ++
  "  la t0, bbcv_touch_only; sd zero, 0(t0)\n" ++
  "  j .Lbbcv_check_code\n" ++
  ".Lbbcv_scalar_sender_fallback:\n" ++
  "  # Keep the sender recovery fallback for older fixtures where the BAL row\n" ++
  "  # shape does not expose a nonce-change count in the expected slot.\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a0, s10, t1\n" ++
  "  jal ra, bal_addr_is_tx_sender\n" ++
  "  beqz a0, .Lbbcv_next\n" ++
  "  la t0, bbcv_touch_only; sd zero, 0(t0)\n" ++
  "  j .Lbbcv_check_code\n" ++
  ".Lbbcv_check_code_non_touch:\n" ++
  "  la t0, bbcv_touch_only; sd zero, 0(t0)\n" ++
  ".Lbbcv_check_code:\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a2, s10, t1\n" ++
  "  mv a0, s2; mv a1, s3; mv a3, s4; mv a4, s5; mv a5, s6; mv a6, s7\n" ++
  "  jal ra, extcodesize_at_header_state_root\n" ++
  "  li t0, 5; beq a0, t0, .Lbbcv_maybe_stop_touch\n" ++
  ".Lbbcv_next:\n" ++
  "  addi s9, s9, 1; j .Lbbcv_loop\n" ++
  ".Lbbcv_ok:\n" ++
  "  li a0, 0; j .Lbbcv_ret\n" ++
  ".Lbbcv_maybe_stop_touch:\n" ++
  "  la t0, bbcv_touch_only; ld t1, 0(t0); beqz t1, .Lbbcv_missing_code\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a2, s10, t1\n" ++
  "  mv a0, s2; mv a1, s3; mv a3, s4; mv a4, s5; la a5, bbcv_code_hash\n" ++
  "  jal ra, code_hash_at_header_state_root\n" ++
  "  bnez a0, .Lbbcv_missing_code\n" ++
  "  la t0, bbcv_code_hash; la t1, bbcv_stop_code_hash\n" ++
  "  ld t2, 0(t0); ld t3, 0(t1); bne t2, t3, .Lbbcv_check_extcodehash_literal\n" ++
  "  ld t2, 8(t0); ld t3, 8(t1); bne t2, t3, .Lbbcv_check_extcodehash_literal\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lbbcv_check_extcodehash_literal\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lbbcv_check_extcodehash_literal\n" ++
  "  j .Lbbcv_next\n" ++
  ".Lbbcv_check_extcodehash_literal:\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a2, s10, t1\n" ++
  "  mv a0, s6; mv a1, s7\n" ++
  "  jal ra, bal_codes_contains_push20_extcodehash\n" ++
  "  bnez a0, .Lbbcv_next\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a2, s10, t1\n" ++
  "  mv a0, s6; mv a1, s7\n" ++
  "  jal ra, bal_codes_contains_push20_balance\n" ++
  "  bnez a0, .Lbbcv_next\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a2, s10, t1\n" ++
  "  mv a0, s6; mv a1, s7\n" ++
  "  jal ra, bal_codes_contains_push20_selfdestruct\n" ++
  "  bnez a0, .Lbbcv_next\n" ++
  "  mv a0, s6; mv a1, s7\n" ++
  "  jal ra, bal_codes_contains_address_selfdestruct\n" ++
  "  bnez a0, .Lbbcv_next\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a0, s10, t1\n" ++
  "  jal ra, bal_txs_contains_push20_selfdestruct\n" ++
  "  bnez a0, .Lbbcv_next\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a0, s10, t1; mv a1, s6; mv a2, s7\n" ++
  "  jal ra, bal_txs_contains_create_collision_touch\n" ++
  "  bnez a0, .Lbbcv_next\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a0, s10, t1\n" ++
  "  jal ra, bal_txs_contains_top_create2_collision_touch\n" ++
  "  bnez a0, .Lbbcv_next\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a0, s10, t1; mv a1, s6; mv a2, s7; mv a3, s0; mv a4, s1\n" ++
  "  jal ra, bal_contains_internal_create_collision_touch\n" ++
  "  bnez a0, .Lbbcv_next\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a0, s10, t1; mv a1, s6; mv a2, s7; mv a3, s0; mv a4, s1\n" ++
  "  jal ra, bal_contains_internal_create2_collision_touch\n" ++
  "  bnez a0, .Lbbcv_next\n" ++
  "  j .Lbbcv_missing_code\n" ++
  ".Lbbcv_missing_code:\n" ++
  "  li a0, 1; j .Lbbcv_ret\n" ++
  ".Lbbcv_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbbcv_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff a 20-byte address is one of execution-specs' fork-level\n" ++
  "# system contracts. Pure BAL touches of these accounts do not require\n" ++
  "# ordinary witness.codes bytecode preimages.\n" ++
  "bbcv_addr_is_system_contract:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv a0, s0; la a1, bbcv_sys_2935; jal ra, bbcv_addr_eq20\n" ++
  "  bnez a0, .Lbbcv_sys_yes\n" ++
  "  mv a0, s0; la a1, bbcv_sys_4788; jal ra, bbcv_addr_eq20\n" ++
  "  bnez a0, .Lbbcv_sys_yes\n" ++
  "  mv a0, s0; la a1, bbcv_sys_7002; jal ra, bbcv_addr_eq20\n" ++
  "  bnez a0, .Lbbcv_sys_yes\n" ++
  "  mv a0, s0; la a1, bbcv_sys_7251; jal ra, bbcv_addr_eq20\n" ++
  "  bnez a0, .Lbbcv_sys_yes\n" ++
  "  mv a0, s0; la a1, bbcv_sys_6110; jal ra, bbcv_addr_eq20\n" ++
  "  bnez a0, .Lbbcv_sys_yes\n" ++
  "  li a0, 0; j .Lbbcv_sys_ret\n" ++
  ".Lbbcv_sys_yes:\n" ++
  "  li a0, 1\n" ++
  ".Lbbcv_sys_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret\n" ++
  "bbcv_addr_eq20:\n" ++
  "  mv t0, a0; mv t1, a1; li t2, 20\n" ++
  ".Lbbcv_eq20_loop:\n" ++
  "  beqz t2, .Lbbcv_eq20_yes\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbbcv_eq20_no\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1\n" ++
  "  j .Lbbcv_eq20_loop\n" ++
  ".Lbbcv_eq20_yes:\n" ++
  "  li a0, 1; ret\n" ++
  ".Lbbcv_eq20_no:\n" ++
  "  li a0, 0; ret\n" ++
  "\n" ++
  "# Return 1 iff a 20-byte address equals any recovered transaction sender.\n" ++
  "# Sender validation reads an EIP-7702 delegation marker when the sender has\n" ++
  "# delegated code, so sender scalar BAL rows cannot skip code-preimage checks.\n" ++
  "bal_addr_is_tx_sender:\n" ++
  "  addi sp, sp, -88\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # 20-byte target address ptr\n" ++
  "  la t0, bv_exec_p; ld s1, 0(t0)\n" ++
  "  la t0, bv_tx_off; ld s2, 0(t0)\n" ++
  "  la t0, bv_public_keys_ptr; ld s3, 0(t0)\n" ++
  "  la t0, bv_public_keys_len; ld s4, 0(t0)\n" ++
  "  beqz s1, .Lbats_no\n" ++
  "  beqz s3, .Lbats_no\n" ++
  "  add s5, s1, s2             # tx list ptr\n" ++
  "  addi a0, s1, 508; jal ra, bgv_u32le\n" ++
  "  bleu a0, s2, .Lbats_no\n" ++
  "  sub s6, a0, s2             # tx list len\n" ++
  "  li t0, 4; bltu s6, t0, .Lbats_no\n" ++
  "  mv a0, s5; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbats_no\n" ++
  "  srli s7, a0, 2             # tx count\n" ++
  "  beqz s7, .Lbats_no\n" ++
  "  li t0, 16; bgtu s7, t0, .Lbats_no\n" ++
  "  slli t0, s7, 2; bgtu t0, s6, .Lbats_no\n" ++
  "  li s8, 0                   # tx index\n" ++
  ".Lbats_loop:\n" ++
  "  beq s8, s7, .Lbats_no\n" ++
  "  li t0, 65; mul t1, s8, t0; add t2, t1, t0; bgtu t2, s4, .Lbats_next\n" ++
  "  add a0, s3, t1; addi a0, a0, 1       # skip SEC1 0x04 prefix\n" ++
  "  la a1, bbcv_sender_addr; jal ra, address_from_pubkey\n" ++
  "  la t0, bbcv_sender_addr; li t1, 0\n" ++
  ".Lbats_cmp:\n" ++
  "  li t2, 20; beq t1, t2, .Lbats_yes\n" ++
  "  add t3, t0, t1; lbu t3, 0(t3)\n" ++
  "  add t4, s0, t1; lbu t4, 0(t4)\n" ++
  "  bne t3, t4, .Lbats_next\n" ++
  "  addi t1, t1, 1; j .Lbats_cmp\n" ++
  ".Lbats_next:\n" ++
  "  addi s8, s8, 1; j .Lbats_loop\n" ++
  ".Lbats_yes:\n" ++
  "  li a0, 1; j .Lbats_ret\n" ++
  ".Lbats_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbats_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 88\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff any witness code contains PUSH20 <addr>; EXTCODEHASH.\n" ++
  "# This recognizes the EIP-8025 optional-proof case where EXTCODEHASH only\n" ++
  "# needs account.code_hash from the trie leaf, not the bytecode preimage.\n" ++
  "bal_codes_contains_push20_extcodehash:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp)\n" ++
  "  sd s3, 24(sp); sd s4, 32(sp); sd s5, 40(sp)\n" ++
  "  mv s0, a0                  # witness.codes section ptr\n" ++
  "  mv s1, a1                  # witness.codes section len\n" ++
  "  mv s2, a2                  # 20-byte target address ptr\n" ++
  "  beqz s1, .Lbce_no\n" ++
  "  lwu t0, 0(s0)              # first element offset = 4*N\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0\n" ++
  ".Lbce_elem_loop:\n" ++
  "  beq s4, s3, .Lbce_no\n" ++
  "  slli t0, s4, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # element offset\n" ++
  "  add s5, s0, t2             # element start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lbce_elem_end_section\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # element end\n" ++
  "  j .Lbce_have_elem_end\n" ++
  ".Lbce_elem_end_section:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lbce_have_elem_end:\n" ++
  "  sub t4, t4, s5             # element len\n" ++
  "  li t5, 22\n" ++
  "  bltu t4, t5, .Lbce_next_elem\n" ++
  "  sub t6, t4, t5             # max start offset\n" ++
  "  li t0, 0                   # scan offset\n" ++
  ".Lbce_scan_loop:\n" ++
  "  bgtu t0, t6, .Lbce_next_elem\n" ++
  "  add t1, s5, t0\n" ++
  "  lbu t2, 0(t1)\n" ++
  "  li t3, 0x73                # PUSH20\n" ++
  "  bne t2, t3, .Lbce_advance_scan\n" ++
  "  li t3, 0                   # address byte index\n" ++
  ".Lbce_addr_loop:\n" ++
  "  li t2, 20\n" ++
  "  beq t3, t2, .Lbce_check_opcode\n" ++
  "  add t4, t1, t3\n" ++
  "  lbu t4, 1(t4)\n" ++
  "  add t5, s2, t3\n" ++
  "  lbu t5, 0(t5)\n" ++
  "  bne t4, t5, .Lbce_advance_scan\n" ++
  "  addi t3, t3, 1\n" ++
  "  j .Lbce_addr_loop\n" ++
  ".Lbce_check_opcode:\n" ++
  "  lbu t4, 21(t1)\n" ++
  "  li t5, 0x3f                # EXTCODEHASH\n" ++
  "  beq t4, t5, .Lbce_yes\n" ++
  ".Lbce_advance_scan:\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lbce_scan_loop\n" ++
  ".Lbce_next_elem:\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lbce_elem_loop\n" ++
  ".Lbce_yes:\n" ++
  "  li a0, 1; j .Lbce_ret\n" ++
  ".Lbce_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbce_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp)\n" ++
  "  ld s3, 24(sp); ld s4, 32(sp); ld s5, 40(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff any witness code contains PUSH20 <addr>; EXTCODESIZE or\n" ++
  "# PUSH20 <addr>; EXTCODECOPY. These opcodes call WitnessState.get_code,\n" ++
  "# so a non-empty target code_hash must have a witness.codes preimage.\n" ++
  "bal_codes_contains_push20_code_read:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp)\n" ++
  "  sd s3, 24(sp); sd s4, 32(sp); sd s5, 40(sp)\n" ++
  "  mv s0, a0                  # witness.codes section ptr\n" ++
  "  mv s1, a1                  # witness.codes section len\n" ++
  "  mv s2, a2                  # 20-byte target address ptr\n" ++
  "  beqz s1, .Lbccr_no\n" ++
  "  lwu t0, 0(s0)              # first element offset = 4*N\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0\n" ++
  ".Lbccr_elem_loop:\n" ++
  "  beq s4, s3, .Lbccr_no\n" ++
  "  slli t0, s4, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # element offset\n" ++
  "  add s5, s0, t2             # element start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lbccr_elem_end_section\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # element end\n" ++
  "  j .Lbccr_have_elem_end\n" ++
  ".Lbccr_elem_end_section:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lbccr_have_elem_end:\n" ++
  "  sub t4, t4, s5             # element len\n" ++
  "  li t5, 22\n" ++
  "  bltu t4, t5, .Lbccr_next_elem\n" ++
  "  sub t6, t4, t5             # max start offset\n" ++
  "  li t0, 0                   # scan offset\n" ++
  ".Lbccr_scan_loop:\n" ++
  "  bgtu t0, t6, .Lbccr_next_elem\n" ++
  "  add t1, s5, t0\n" ++
  "  lbu t2, 0(t1)\n" ++
  "  li t3, 0x73                # PUSH20\n" ++
  "  bne t2, t3, .Lbccr_advance_scan\n" ++
  "  li t3, 0                   # address byte index\n" ++
  ".Lbccr_addr_loop:\n" ++
  "  li t2, 20\n" ++
  "  beq t3, t2, .Lbccr_check_opcode\n" ++
  "  add t4, t1, t3\n" ++
  "  lbu t4, 1(t4)\n" ++
  "  add t5, s2, t3\n" ++
  "  lbu t5, 0(t5)\n" ++
  "  bne t4, t5, .Lbccr_advance_scan\n" ++
  "  addi t3, t3, 1\n" ++
  "  j .Lbccr_addr_loop\n" ++
  ".Lbccr_check_opcode:\n" ++
  "  lbu t4, 21(t1)\n" ++
  "  li t5, 0x3b                # EXTCODESIZE\n" ++
  "  beq t4, t5, .Lbccr_yes\n" ++
  "  li t5, 0x3c                # EXTCODECOPY\n" ++
  "  beq t4, t5, .Lbccr_yes\n" ++
  ".Lbccr_advance_scan:\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lbccr_scan_loop\n" ++
  ".Lbccr_next_elem:\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lbccr_elem_loop\n" ++
  ".Lbccr_yes:\n" ++
  "  li a0, 1; j .Lbccr_ret\n" ++
  ".Lbccr_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbccr_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp)\n" ++
  "  ld s3, 24(sp); ld s4, 32(sp); ld s5, 40(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff any witness code contains PUSHn <addr>; BALANCE.\n" ++
  "# BALANCE reads account.balance from the state leaf and does not require\n" ++
  "# WitnessState.get_code for the touched account. Accept PUSH1..PUSH20\n" ++
  "# when omitted high address bytes are zero.\n" ++
  "bal_codes_contains_push20_balance:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp)\n" ++
  "  sd s3, 24(sp); sd s4, 32(sp); sd s5, 40(sp)\n" ++
  "  mv s0, a0                  # witness.codes section ptr\n" ++
  "  mv s1, a1                  # witness.codes section len\n" ++
  "  mv s2, a2                  # 20-byte target address ptr\n" ++
  "  beqz s1, .Lbcb_no\n" ++
  "  lwu t0, 0(s0)              # first element offset = 4*N\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0\n" ++
  ".Lbcb_elem_loop:\n" ++
  "  beq s4, s3, .Lbcb_no\n" ++
  "  slli t0, s4, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # element offset\n" ++
  "  add s5, s0, t2             # element start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lbcb_elem_end_section\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # element end\n" ++
  "  j .Lbcb_have_elem_end\n" ++
  ".Lbcb_elem_end_section:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lbcb_have_elem_end:\n" ++
  "  sub t4, t4, s5             # element len\n" ++
  "  li t5, 3\n" ++
  "  bltu t4, t5, .Lbcb_next_elem\n" ++
  "  sub t6, t4, t5             # max start offset for PUSH1 + opcode\n" ++
  "  li t0, 0                   # scan offset\n" ++
  ".Lbcb_scan_loop:\n" ++
  "  bgtu t0, t6, .Lbcb_next_elem\n" ++
  "  add t1, s5, t0\n" ++
  "  lbu t2, 0(t1)\n" ++
  "  li t3, 0x60                # PUSH1\n" ++
  "  bltu t2, t3, .Lbcb_advance_scan\n" ++
  "  li t3, 0x73                # PUSH20\n" ++
  "  bgtu t2, t3, .Lbcb_advance_scan\n" ++
  "  addi t3, t2, -95           # pushed byte count\n" ++
  "  add t5, t0, t3\n" ++
  "  addi t5, t5, 1             # opcode byte offset\n" ++
  "  addi t4, t6, 2             # last valid opcode offset\n" ++
  "  bgtu t5, t4, .Lbcb_advance_scan\n" ++
  "  li t5, 20\n" ++
  "  sub t5, t5, t3             # omitted leading target bytes\n" ++
  "  li t2, 0\n" ++
  ".Lbcb_leading_zero_loop:\n" ++
  "  beq t2, t5, .Lbcb_addr_loop_start\n" ++
  "  add t4, s2, t2\n" ++
  "  lbu t4, 0(t4)\n" ++
  "  bnez t4, .Lbcb_advance_scan\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lbcb_leading_zero_loop\n" ++
  ".Lbcb_addr_loop_start:\n" ++
  "  li t2, 0                   # pushed address byte index\n" ++
  ".Lbcb_addr_loop:\n" ++
  "  beq t2, t3, .Lbcb_check_opcode\n" ++
  "  add t4, t1, t2\n" ++
  "  lbu t4, 1(t4)\n" ++
  "  li t5, 20\n" ++
  "  sub t5, t5, t3\n" ++
  "  add t5, t5, t2\n" ++
  "  add t5, s2, t5\n" ++
  "  lbu t5, 0(t5)\n" ++
  "  bne t4, t5, .Lbcb_advance_scan\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lbcb_addr_loop\n" ++
  ".Lbcb_check_opcode:\n" ++
  "  add t4, t1, t3\n" ++
  "  lbu t4, 1(t4)\n" ++
  "  li t5, 0x31                # BALANCE\n" ++
  "  beq t4, t5, .Lbcb_yes\n" ++
  ".Lbcb_advance_scan:\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lbcb_scan_loop\n" ++
  ".Lbcb_next_elem:\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lbcb_elem_loop\n" ++
  ".Lbcb_yes:\n" ++
  "  li a0, 1; j .Lbcb_ret\n" ++
  ".Lbcb_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbcb_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp)\n" ++
  "  ld s3, 24(sp); ld s4, 32(sp); ld s5, 40(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff any witness code contains PUSH20 <addr>; SELFDESTRUCT.\n" ++
  "# SELFDESTRUCT touches the beneficiary account but does not execute or read\n" ++
  "# that account's bytecode preimage.\n" ++
  "bal_codes_contains_push20_selfdestruct:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp)\n" ++
  "  sd s3, 24(sp); sd s4, 32(sp); sd s5, 40(sp)\n" ++
  "  mv s0, a0                  # witness.codes section ptr\n" ++
  "  mv s1, a1                  # witness.codes section len\n" ++
  "  mv s2, a2                  # 20-byte target address ptr\n" ++
  "  beqz s1, .Lbcsd_no\n" ++
  "  lwu t0, 0(s0)              # first element offset = 4*N\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0\n" ++
  ".Lbcsd_elem_loop:\n" ++
  "  beq s4, s3, .Lbcsd_no\n" ++
  "  slli t0, s4, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # element offset\n" ++
  "  add s5, s0, t2             # element start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lbcsd_elem_end_section\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # element end\n" ++
  "  j .Lbcsd_have_elem_end\n" ++
  ".Lbcsd_elem_end_section:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lbcsd_have_elem_end:\n" ++
  "  sub t4, t4, s5             # element len\n" ++
  "  li t5, 22\n" ++
  "  bltu t4, t5, .Lbcsd_next_elem\n" ++
  "  sub t6, t4, t5             # max start offset\n" ++
  "  li t0, 0                   # scan offset\n" ++
  ".Lbcsd_scan_loop:\n" ++
  "  bgtu t0, t6, .Lbcsd_next_elem\n" ++
  "  add t1, s5, t0\n" ++
  "  lbu t2, 0(t1)\n" ++
  "  li t3, 0x73                # PUSH20\n" ++
  "  bne t2, t3, .Lbcsd_advance_scan\n" ++
  "  li t3, 0                   # address byte index\n" ++
  ".Lbcsd_addr_loop:\n" ++
  "  li t2, 20\n" ++
  "  beq t3, t2, .Lbcsd_check_opcode\n" ++
  "  add t4, t1, t3\n" ++
  "  lbu t4, 1(t4)\n" ++
  "  add t5, s2, t3\n" ++
  "  lbu t5, 0(t5)\n" ++
  "  bne t4, t5, .Lbcsd_advance_scan\n" ++
  "  addi t3, t3, 1\n" ++
  "  j .Lbcsd_addr_loop\n" ++
  ".Lbcsd_check_opcode:\n" ++
  "  lbu t4, 21(t1)\n" ++
  "  li t5, 0xff                # SELFDESTRUCT\n" ++
  "  beq t4, t5, .Lbcsd_yes\n" ++
  ".Lbcsd_advance_scan:\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lbcsd_scan_loop\n" ++
  ".Lbcsd_next_elem:\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lbcsd_elem_loop\n" ++
  ".Lbcsd_yes:\n" ++
  "  li a0, 1; j .Lbcsd_ret\n" ++
  ".Lbcsd_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbcsd_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp)\n" ++
  "  ld s3, 24(sp); ld s4, 32(sp); ld s5, 40(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff any witness code contains ADDRESS followed shortly by SELFDESTRUCT.\n" ++
  "# This recognizes dynamic self-beneficiary SELFDESTRUCT bytecode, where the\n" ++
  "# beneficiary is computed from ADDRESS/MLOAD rather than a PUSH20 literal.\n" ++
  "bal_codes_contains_address_selfdestruct:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp)\n" ++
  "  sd s3, 24(sp); sd s4, 32(sp); sd s5, 40(sp)\n" ++
  "  mv s0, a0                  # witness.codes section ptr\n" ++
  "  mv s1, a1                  # witness.codes section len\n" ++
  "  beqz s1, .Lbcasd_no\n" ++
  "  lwu t0, 0(s0)              # first element offset = 4*N\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0\n" ++
  ".Lbcasd_elem_loop:\n" ++
  "  beq s4, s3, .Lbcasd_no\n" ++
  "  slli t0, s4, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # element offset\n" ++
  "  add s5, s0, t2             # element start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lbcasd_elem_end_section\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # element end\n" ++
  "  j .Lbcasd_have_elem_end\n" ++
  ".Lbcasd_elem_end_section:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lbcasd_have_elem_end:\n" ++
  "  sub t4, t4, s5             # element len\n" ++
  "  li t5, 2\n" ++
  "  bltu t4, t5, .Lbcasd_next_elem\n" ++
  "  addi t6, t4, -1            # max ADDRESS scan offset\n" ++
  "  li t0, 0                   # scan offset\n" ++
  ".Lbcasd_scan_loop:\n" ++
  "  bgtu t0, t6, .Lbcasd_next_elem\n" ++
  "  add t1, s5, t0\n" ++
  "  lbu t2, 0(t1)\n" ++
  "  li t3, 0x30                # ADDRESS\n" ++
  "  bne t2, t3, .Lbcasd_advance_scan\n" ++
  "  addi t2, t0, 1             # lookahead offset\n" ++
  "  addi t3, t0, 96            # bounded dynamic-beneficiary window\n" ++
  "  bltu t3, t4, .Lbcasd_have_limit\n" ++
  "  mv t3, t4\n" ++
  ".Lbcasd_have_limit:\n" ++
  "  beq t2, t3, .Lbcasd_advance_scan\n" ++
  "  add t5, s5, t2\n" ++
  "  lbu t5, 0(t5)\n" ++
  "  li t1, 0xff                # SELFDESTRUCT\n" ++
  "  beq t5, t1, .Lbcasd_yes\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lbcasd_have_limit\n" ++
  ".Lbcasd_advance_scan:\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lbcasd_scan_loop\n" ++
  ".Lbcasd_next_elem:\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lbcasd_elem_loop\n" ++
  ".Lbcasd_yes:\n" ++
  "  li a0, 1; j .Lbcasd_ret\n" ++
  ".Lbcasd_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbcasd_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp)\n" ++
  "  ld s3, 24(sp); ld s4, 32(sp); ld s5, 40(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff any witness code contains PUSH20 <addr> followed shortly by CALL.\n" ++
  "# This recognizes CALL target-account touches, including calls that fail\n" ++
  "# during precheck before child code runs; execution-spec witness replay still\n" ++
  "# requires the target account proof in that case.\n" ++
  "bal_codes_contains_push20_call_target:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp)\n" ++
  "  sd s3, 24(sp); sd s4, 32(sp); sd s5, 40(sp); sd s6, 48(sp)\n" ++
  "  mv s0, a0                  # witness.codes section ptr\n" ++
  "  mv s1, a1                  # witness.codes section len\n" ++
  "  mv s2, a2                  # 20-byte target address ptr\n" ++
  "  beqz s1, .Lbccall_no\n" ++
  "  lwu t0, 0(s0)              # first element offset = 4*N\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0\n" ++
  ".Lbccall_elem_loop:\n" ++
  "  beq s4, s3, .Lbccall_no\n" ++
  "  slli t0, s4, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # element offset\n" ++
  "  add s5, s0, t2             # element start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lbccall_elem_end_section\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # element end\n" ++
  "  j .Lbccall_have_elem_end\n" ++
  ".Lbccall_elem_end_section:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lbccall_have_elem_end:\n" ++
  "  sub t4, t4, s5             # element len\n" ++
  "  li t5, 22\n" ++
  "  bltu t4, t5, .Lbccall_next_elem\n" ++
  "  sub t6, t4, t5             # max start offset for PUSH20 + one opcode\n" ++
  "  li t0, 0                   # scan offset\n" ++
  ".Lbccall_scan_loop:\n" ++
  "  bgtu t0, t6, .Lbccall_next_elem\n" ++
  "  add t1, s5, t0\n" ++
  "  lbu t2, 0(t1)\n" ++
  "  li t3, 0x73                # PUSH20\n" ++
  "  bne t2, t3, .Lbccall_advance_scan\n" ++
  "  li t3, 0                   # address byte index\n" ++
  ".Lbccall_addr_loop:\n" ++
  "  li t2, 20\n" ++
  "  beq t3, t2, .Lbccall_find_call\n" ++
  "  add t4, t1, t3\n" ++
  "  lbu t4, 1(t4)\n" ++
  "  add t5, s2, t3\n" ++
  "  lbu t5, 0(t5)\n" ++
  "  bne t4, t5, .Lbccall_advance_scan\n" ++
  "  addi t3, t3, 1\n" ++
  "  j .Lbccall_addr_loop\n" ++
  ".Lbccall_find_call:\n" ++
  "  addi t2, t0, 21            # first byte after PUSH20 immediate\n" ++
  "  addi s6, t6, 22            # element len = max_start + pattern len\n" ++
  "  addi t3, t2, 64            # bounded lookahead for CALL opcode\n" ++
  "  bleu t3, s6, .Lbccall_limit_window\n" ++
  "  j .Lbccall_have_limit\n" ++
  ".Lbccall_limit_window:\n" ++
  "  mv s6, t3\n" ++
  ".Lbccall_have_limit:\n" ++
  "  beq t2, s6, .Lbccall_advance_scan\n" ++
  "  add t3, s5, t2\n" ++
  "  lbu t3, 0(t3)\n" ++
  "  li t5, 0xf1                # CALL\n" ++
  "  beq t3, t5, .Lbccall_yes\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lbccall_have_limit\n" ++
  ".Lbccall_advance_scan:\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lbccall_scan_loop\n" ++
  ".Lbccall_next_elem:\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lbccall_elem_loop\n" ++
  ".Lbccall_yes:\n" ++
  "  li a0, 1; j .Lbccall_ret\n" ++
  ".Lbccall_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbccall_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp)\n" ++
  "  ld s3, 24(sp); ld s4, 32(sp); ld s5, 40(sp); ld s6, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff any legacy transaction data contains PUSH20 <addr>; SELFDESTRUCT.\n" ++
  "# Reads bv_exec_p/bv_tx_off populated by block_verdict. Malformed or typed\n" ++
  "# transactions are treated conservatively as no match.\n" ++
  "bal_txs_contains_push20_selfdestruct:\n" ++
  "  addi sp, sp, -104\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                  # 20-byte target address ptr\n" ++
  "  la t0, bv_exec_p; ld s1, 0(t0)\n" ++
  "  la t0, bv_tx_off; ld s2, 0(t0)\n" ++
  "  beqz s1, .Lbcs_no\n" ++
  "  add s3, s1, s2             # tx list ptr\n" ++
  "  addi a0, s1, 508; jal ra, bgv_u32le\n" ++
  "  bleu a0, s2, .Lbcs_no\n" ++
  "  sub s4, a0, s2             # tx list len\n" ++
  "  li t0, 4; bltu s4, t0, .Lbcs_no\n" ++
  "  mv a0, s3; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbcs_no\n" ++
  "  srli s5, a0, 2             # tx count\n" ++
  "  beqz s5, .Lbcs_no\n" ++
  "  li t0, 16; bgtu s5, t0, .Lbcs_no\n" ++
  "  slli t0, s5, 2; bgtu t0, s4, .Lbcs_no\n" ++
  "  li s6, 0                   # tx index\n" ++
  ".Lbcs_tx_loop:\n" ++
  "  beq s6, s5, .Lbcs_no\n" ++
  "  slli t0, s6, 2; add a0, s3, t0; jal ra, bgv_u32le\n" ++
  "  mv s7, a0                  # item offset\n" ++
  "  addi t0, s6, 1\n" ++
  "  beq t0, s5, .Lbcs_last_tx\n" ++
  "  slli t1, t0, 2; add a0, s3, t1; jal ra, bgv_u32le\n" ++
  "  j .Lbcs_have_next\n" ++
  ".Lbcs_last_tx:\n" ++
  "  mv a0, s4\n" ++
  ".Lbcs_have_next:\n" ++
  "  bltu a0, s7, .Lbcs_next_tx\n" ++
  "  sub s8, a0, s7             # tx len\n" ++
  "  add s9, s3, s7             # tx ptr\n" ++
  "  mv a0, s9; mv a1, s8; la a2, bsg_tx_type; la a3, bsg_tx_inner\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Lbcs_next_tx\n" ++
  "  la t0, bsg_tx_type; ld t1, 0(t0); bnez t1, .Lbcs_next_tx\n" ++
  "  mv a0, s9; mv a1, s8; li a2, 5; la a3, bsg_data_off; la a4, bsg_data_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbcs_next_tx\n" ++
  "  la t0, bsg_data_off; ld t1, 0(t0); add s10, s9, t1\n" ++
  "  la t0, bsg_data_len; ld t2, 0(t0)\n" ++
  "  li t3, 22; bltu t2, t3, .Lbcs_next_tx\n" ++
  "  sub t4, t2, t3             # max start offset\n" ++
  "  li t5, 0                   # scan offset\n" ++
  ".Lbcs_scan_loop:\n" ++
  "  bgtu t5, t4, .Lbcs_next_tx\n" ++
  "  add t6, s10, t5\n" ++
  "  lbu t0, 0(t6); li t1, 0x73; bne t0, t1, .Lbcs_advance_scan\n" ++
  "  li t0, 0                   # address byte index\n" ++
  ".Lbcs_addr_loop:\n" ++
  "  li t1, 20; beq t0, t1, .Lbcs_check_opcode\n" ++
  "  add t2, t6, t0; lbu t2, 1(t2)\n" ++
  "  add t3, s0, t0; lbu t3, 0(t3)\n" ++
  "  bne t2, t3, .Lbcs_advance_scan\n" ++
  "  addi t0, t0, 1; j .Lbcs_addr_loop\n" ++
  ".Lbcs_check_opcode:\n" ++
  "  lbu t0, 21(t6); li t1, 0xff\n" ++
  "  beq t0, t1, .Lbcs_yes\n" ++
  ".Lbcs_advance_scan:\n" ++
  "  addi t5, t5, 1; j .Lbcs_scan_loop\n" ++
  ".Lbcs_next_tx:\n" ++
  "  addi s6, s6, 1; j .Lbcs_tx_loop\n" ++
  ".Lbcs_yes:\n" ++
  "  li a0, 1; j .Lbcs_ret\n" ++
  ".Lbcs_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbcs_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 104\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff target equals CREATE(tx.to, 0) for a legacy tx and witness\n" ++
  "# bytecode contains a CREATE opcode. This recognizes CREATE-collision BAL\n" ++
  "# touches, which read account metadata but not the bytecode preimage.\n" ++
  "bal_txs_contains_create_collision_touch:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                  # 20-byte target address ptr\n" ++
  "  mv s1, a1                  # witness.codes ptr\n" ++
  "  mv s2, a2                  # witness.codes len\n" ++
  "  la t0, bv_exec_p; ld s3, 0(t0)\n" ++
  "  la t0, bv_tx_off; ld s4, 0(t0)\n" ++
  "  beqz s3, .Lbcc_no\n" ++
  "  add s5, s3, s4             # tx list ptr\n" ++
  "  addi a0, s3, 508; jal ra, bgv_u32le\n" ++
  "  bleu a0, s4, .Lbcc_no\n" ++
  "  sub s6, a0, s4             # tx list len\n" ++
  "  li t0, 4; bltu s6, t0, .Lbcc_no\n" ++
  "  mv a0, s5; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbcc_no\n" ++
  "  srli s7, a0, 2             # tx count\n" ++
  "  beqz s7, .Lbcc_no\n" ++
  "  li t0, 16; bgtu s7, t0, .Lbcc_no\n" ++
  "  slli t0, s7, 2; bgtu t0, s6, .Lbcc_no\n" ++
  "  li s8, 0                   # tx index\n" ++
  ".Lbcc_tx_loop:\n" ++
  "  beq s8, s7, .Lbcc_no\n" ++
  "  slli t0, s8, 2; add a0, s5, t0; jal ra, bgv_u32le\n" ++
  "  mv s9, a0                  # item offset\n" ++
  "  addi t0, s8, 1\n" ++
  "  beq t0, s7, .Lbcc_last_tx\n" ++
  "  slli t1, t0, 2; add a0, s5, t1; jal ra, bgv_u32le\n" ++
  "  j .Lbcc_have_next\n" ++
  ".Lbcc_last_tx:\n" ++
  "  mv a0, s6\n" ++
  ".Lbcc_have_next:\n" ++
  "  bltu a0, s9, .Lbcc_next_tx\n" ++
  "  sub t2, a0, s9             # tx len\n" ++
  "  add t3, s5, s9             # tx ptr\n" ++
  "  la t0, bsg_change_ptr; sd t3, 0(t0); la t0, bsg_change_item_len; sd t2, 0(t0)\n" ++
  "  mv a0, t3; mv a1, t2; la a2, bsg_tx_type; la a3, bsg_tx_inner\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Lbcc_next_tx\n" ++
  "  la t0, bsg_tx_type; ld t1, 0(t0); bnez t1, .Lbcc_next_tx\n" ++
  "  la t0, bsg_change_ptr; ld t3, 0(t0); la t0, bsg_change_item_len; ld t2, 0(t0)\n" ++
  "  mv a0, t3; mv a1, t2; li a2, 3; la a3, bsg_to_off; la a4, bsg_to_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbcc_next_tx\n" ++
  "  la t0, bsg_change_ptr; ld t3, 0(t0)\n" ++
  "  la t0, bsg_to_len; ld t1, 0(t0); li t2, 20; beq t1, t2, .Lbcc_internal_create\n" ++
  "  bnez t1, .Lbcc_next_tx\n" ++
  "  # Top-level legacy contract creation: compare target with CREATE(sender, nonce).\n" ++
  "  la t0, bv_public_keys_ptr; ld t4, 0(t0)\n" ++
  "  la t0, bv_public_keys_len; ld t5, 0(t0)\n" ++
  "  beqz t4, .Lbcc_next_tx\n" ++
  "  li t0, 65; mul t1, s8, t0; add t2, t1, t0; bgtu t2, t5, .Lbcc_next_tx\n" ++
  "  add a0, t4, t1; addi a0, a0, 1       # skip SEC1 0x04 prefix\n" ++
  "  la a1, bbcv_sender_addr; jal ra, address_from_pubkey\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0)\n" ++
  "  li a2, 0; la a3, bsg_tx_nonce; jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lbcc_next_tx\n" ++
  "  la a0, bbcv_sender_addr; la t0, bsg_tx_nonce; ld a1, 0(t0); la a2, bbcv_create_addr\n" ++
  "  jal ra, address_compute_create\n" ++
  "  la t0, bbcv_create_addr; li t1, 0\n" ++
  ".Lbcc_cmp_top_create_addr:\n" ++
  "  li t2, 20; beq t1, t2, .Lbcc_yes\n" ++
  "  add t3, t0, t1; lbu t3, 0(t3)\n" ++
  "  add t4, s0, t1; lbu t4, 0(t4)\n" ++
  "  bne t3, t4, .Lbcc_next_tx\n" ++
  "  addi t1, t1, 1; j .Lbcc_cmp_top_create_addr\n" ++
  ".Lbcc_internal_create:\n" ++
  "  jal ra, bal_codes_contains_create_opcode\n" ++
  "  beqz a0, .Lbcc_next_tx\n" ++
  "  la t0, bsg_change_ptr; ld t3, 0(t0)\n" ++
  "  la t0, bsg_to_off; ld t1, 0(t0); add t3, t3, t1\n" ++
  "  la t0, bsr_kbuf            # RLP([to, 0]) buffer\n" ++
  "  li t1, 0xd6; sb t1, 0(t0)\n" ++
  "  li t1, 0x94; sb t1, 1(t0)\n" ++
  "  li t1, 0\n" ++
  ".Lbcc_copy_to:\n" ++
  "  li t2, 20; beq t1, t2, .Lbcc_hash_create\n" ++
  "  add t4, t3, t1; lbu t4, 0(t4)\n" ++
  "  add t5, t0, t1; sb t4, 2(t5)\n" ++
  "  addi t1, t1, 1; j .Lbcc_copy_to\n" ++
  ".Lbcc_hash_create:\n" ++
  "  li t1, 0x80; sb t1, 22(t0)\n" ++
  "  mv a0, t0; li a1, 23; la a2, bbcv_code_hash; jal ra, zkvm_keccak256\n" ++
  "  la t0, bbcv_code_hash; addi t0, t0, 12\n" ++
  "  li t1, 0\n" ++
  ".Lbcc_cmp_addr:\n" ++
  "  li t2, 20; beq t1, t2, .Lbcc_yes\n" ++
  "  add t3, t0, t1; lbu t3, 0(t3)\n" ++
  "  add t4, s0, t1; lbu t4, 0(t4)\n" ++
  "  bne t3, t4, .Lbcc_next_tx\n" ++
  "  addi t1, t1, 1; j .Lbcc_cmp_addr\n" ++
  ".Lbcc_next_tx:\n" ++
  "  addi s8, s8, 1; j .Lbcc_tx_loop\n" ++
  ".Lbcc_yes:\n" ++
  "  li a0, 1; j .Lbcc_ret\n" ++
  ".Lbcc_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbcc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff target equals CREATE2(CREATE(sender, nonce), salt, initcode)\n" ++
  "# for a top-level legacy contract-creation tx with simple literal initcode.\n" ++
  "bal_txs_contains_top_create2_collision_touch:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                  # 20-byte target address ptr\n" ++
  "  la t0, bv_exec_p; ld s1, 0(t0)\n" ++
  "  la t0, bv_tx_off; ld s2, 0(t0)\n" ++
  "  beqz s1, .Lbctc2_no\n" ++
  "  add s3, s1, s2             # tx list ptr\n" ++
  "  addi a0, s1, 508; jal ra, bgv_u32le\n" ++
  "  bleu a0, s2, .Lbctc2_no\n" ++
  "  sub s4, a0, s2             # tx list len\n" ++
  "  li t0, 4; bltu s4, t0, .Lbctc2_no\n" ++
  "  mv a0, s3; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbctc2_no\n" ++
  "  srli s5, a0, 2             # tx count\n" ++
  "  beqz s5, .Lbctc2_no\n" ++
  "  li t0, 16; bgtu s5, t0, .Lbctc2_no\n" ++
  "  slli t0, s5, 2; bgtu t0, s4, .Lbctc2_no\n" ++
  "  li s6, 0                   # tx index\n" ++
  ".Lbctc2_tx_loop:\n" ++
  "  beq s6, s5, .Lbctc2_no\n" ++
  "  slli t0, s6, 2; add a0, s3, t0; jal ra, bgv_u32le\n" ++
  "  mv s7, a0                  # item offset\n" ++
  "  addi t0, s6, 1\n" ++
  "  beq t0, s5, .Lbctc2_last_tx\n" ++
  "  slli t1, t0, 2; add a0, s3, t1; jal ra, bgv_u32le\n" ++
  "  j .Lbctc2_have_next\n" ++
  ".Lbctc2_last_tx:\n" ++
  "  mv a0, s4\n" ++
  ".Lbctc2_have_next:\n" ++
  "  bltu a0, s7, .Lbctc2_next_tx\n" ++
  "  sub s8, a0, s7             # tx len\n" ++
  "  add s9, s3, s7             # tx ptr\n" ++
  "  la t0, bsg_change_ptr; sd s9, 0(t0); la t0, bsg_change_item_len; sd s8, 0(t0)\n" ++
  "  mv a0, s9; mv a1, s8; la a2, bsg_tx_type; la a3, bsg_tx_inner\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Lbctc2_next_tx\n" ++
  "  la t0, bsg_tx_type; ld t1, 0(t0); bnez t1, .Lbctc2_next_tx\n" ++
  "  mv a0, s9; mv a1, s8; li a2, 3; la a3, bsg_to_off; la a4, bsg_to_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbctc2_next_tx\n" ++
  "  la t0, bsg_to_len; ld t1, 0(t0); bnez t1, .Lbctc2_next_tx\n" ++
  "  la t0, bv_public_keys_ptr; ld t4, 0(t0)\n" ++
  "  la t0, bv_public_keys_len; ld t5, 0(t0)\n" ++
  "  beqz t4, .Lbctc2_next_tx\n" ++
  "  li t0, 65; mul t1, s6, t0; add t2, t1, t0; bgtu t2, t5, .Lbctc2_next_tx\n" ++
  "  add a0, t4, t1; addi a0, a0, 1\n" ++
  "  la a1, bbcv_sender_addr; jal ra, address_from_pubkey\n" ++
  "  mv a0, s9; mv a1, s8; li a2, 0; la a3, bsg_tx_nonce\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lbctc2_next_tx\n" ++
  "  la a0, bbcv_sender_addr; la t0, bsg_tx_nonce; ld a1, 0(t0); la a2, bbcv_create_addr\n" ++
  "  jal ra, address_compute_create\n" ++
  "  mv a0, s9; mv a1, s8; li a2, 5; la a3, bsg_data_off; la a4, bsg_data_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbctc2_next_tx\n" ++
  "  la t0, bsg_data_off; ld t1, 0(t0); add s10, s9, t1\n" ++
  "  la t0, bsg_data_len; ld s11, 0(t0)\n" ++
  "  mv a0, s0; la a1, bbcv_create_addr; mv a2, s10; mv a3, s11\n" ++
  "  jal ra, bal_tx_initcode_contains_create2_target\n" ++
  "  bnez a0, .Lbctc2_yes\n" ++
  ".Lbctc2_next_tx:\n" ++
  "  addi s6, s6, 1; j .Lbctc2_tx_loop\n" ++
  ".Lbctc2_yes:\n" ++
  "  li a0, 1; j .Lbctc2_ret\n" ++
  ".Lbctc2_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbctc2_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret\n" ++
  "\n" ++
  "# Match simple top-level initcode CREATE2 patterns from create2collision_code.\n" ++
  "bal_tx_initcode_contains_create2_target:\n" ++
  "  addi sp, sp, -88\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                  # target address ptr\n" ++
  "  mv s1, a1                  # CREATE deployer ptr\n" ++
  "  mv s2, a2                  # tx initcode ptr\n" ++
  "  mv s3, a3                  # tx initcode len\n" ++
  "  li s4, 0                   # scan offset\n" ++
  ".Lbti_scan:\n" ++
  "  beq s4, s3, .Lbti_no\n" ++
  "  add t0, s2, s4; lbu t1, 0(t0); li t2, 0xf5; bne t1, t2, .Lbti_advance\n" ++
  "  li t2, 8; bltu s4, t2, .Lbti_advance\n" ++
  "  addi s5, t0, -8            # four PUSH1 args before CREATE2\n" ++
  "  lbu t1, 0(s5); li t2, 0x60; bne t1, t2, .Lbti_advance\n" ++
  "  lbu t1, 2(s5); bne t1, t2, .Lbti_advance\n" ++
  "  lbu t1, 4(s5); bne t1, t2, .Lbti_advance\n" ++
  "  lbu t1, 6(s5); bne t1, t2, .Lbti_advance\n" ++
  "  la s6, bbcv_create2_salt\n" ++
  "  sd zero, 0(s6); sd zero, 8(s6); sd zero, 16(s6); sw zero, 24(s6)\n" ++
  "  lbu t1, 1(s5); sb t1, 31(s6)  # salt byte\n" ++
  "  lbu s7, 3(s5)              # initcode size byte\n" ++
  "  beqz s7, .Lbti_empty_init\n" ++
  "  li t1, 33; bgtu s7, t1, .Lbti_advance\n" ++
  "  lbu t1, 0(s2); li t2, 0x60; bltu t1, t2, .Lbti_advance\n" ++
  "  li t2, 0x7f; bgtu t1, t2, .Lbti_advance\n" ++
  "  addi t1, t1, -0x5f         # PUSHn literal length\n" ++
  "  bne t1, s7, .Lbti_advance\n" ++
  "  addi t2, s7, 1; bgtu t2, s3, .Lbti_advance\n" ++
  "  addi s8, s2, 1; mv s9, s7\n" ++
  "  j .Lbti_compute\n" ++
  ".Lbti_empty_init:\n" ++
  "  mv s8, s2; li s9, 0\n" ++
  ".Lbti_compute:\n" ++
  "  mv a0, s1; mv a1, s6; mv a2, s8; mv a3, s9; la a4, bbcv_sender_addr\n" ++
  "  jal ra, address_compute_create2\n" ++
  "  la t0, bbcv_sender_addr; li t1, 0\n" ++
  ".Lbti_cmp:\n" ++
  "  li t2, 20; beq t1, t2, .Lbti_yes\n" ++
  "  add t3, t0, t1; lbu t3, 0(t3)\n" ++
  "  add t4, s0, t1; lbu t4, 0(t4)\n" ++
  "  bne t3, t4, .Lbti_advance\n" ++
  "  addi t1, t1, 1; j .Lbti_cmp\n" ++
  ".Lbti_advance:\n" ++
  "  addi s4, s4, 1; j .Lbti_scan\n" ++
  ".Lbti_yes:\n" ++
  "  li a0, 1; j .Lbti_ret\n" ++
  ".Lbti_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbti_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 88\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff target equals CREATE(creator, pre_nonce) for a BAL creator\n" ++
  "# row whose nonce increases and witness bytecode contains CREATE. This covers\n" ++
  "# internal CREATE collision metadata touches without requiring code preimage.\n" ++
  "bal_contains_internal_create_collision_touch:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                  # 20-byte target address ptr\n" ++
  "  mv s1, a1                  # witness.codes ptr\n" ++
  "  mv s2, a2                  # witness.codes len\n" ++
  "  mv s3, a3                  # BAL ptr\n" ++
  "  mv s4, a4                  # BAL len\n" ++
  "  jal ra, bal_codes_contains_create_opcode\n" ++
  "  beqz a0, .Lbicc_no\n" ++
  "  mv a0, s3; mv a1, s4; la a2, bbcv_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbicc_no\n" ++
  "  la t0, bbcv_count; ld s5, 0(t0)\n" ++
  "  li s6, 0                  # BAL row index\n" ++
  ".Lbicc_row_loop:\n" ++
  "  beq s6, s5, .Lbicc_no\n" ++
  "  mv a0, s3; mv a1, s4; mv a2, s6; la a3, bbcv_off; la a4, bbcv_size\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  bnez a0, .Lbicc_next_row\n" ++
  "  la t0, bbcv_off; ld t1, 0(t0); add s7, s3, t1     # row ptr\n" ++
  "  la t0, bbcv_size; ld s8, 0(t0)                    # row len\n" ++
  "  mv a0, s7; mv a1, s8; li a2, 0; la a3, bbcv_addr_off; la a4, bbcv_addr_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbicc_next_row\n" ++
  "  la t0, bbcv_addr_len; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lbicc_next_row\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add s9, s7, t1 # creator address ptr\n" ++
  "  mv a0, s7; mv a1, s8; li a2, 4; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbicc_next_row\n" ++
  "  la t0, bbcv_field_off; ld t1, 0(t0); add s10, s7, t1 # nonce_changes ptr\n" ++
  "  la t0, bbcv_field_len; ld s11, 0(t0)                  # nonce_changes len\n" ++
  "  mv a0, s10; mv a1, s11; la a2, bbcv_field_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbicc_next_row\n" ++
  "  la t0, bbcv_field_count; ld t1, 0(t0); beqz t1, .Lbicc_next_row\n" ++
  "  # Use the first nonce change: [block_access_index, new_nonce].\n" ++
  "  mv a0, s10; mv a1, s11; mv a2, zero; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbicc_next_row\n" ++
  "  la t0, bbcv_field_off; ld t1, 0(t0); add a0, s10, t1\n" ++
  "  la t0, bbcv_field_len; ld a1, 0(t0); li a2, 1; la a3, bsg_tx_nonce\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lbicc_next_row\n" ++
  "  la t0, bsg_tx_nonce; ld a1, 0(t0); beqz a1, .Lbicc_next_row\n" ++
  "  addi a1, a1, -1           # pre_nonce = new_nonce - 1\n" ++
  "  mv a0, s9; la a2, bbcv_create_addr\n" ++
  "  jal ra, address_compute_create\n" ++
  "  la t0, bbcv_create_addr; li t1, 0\n" ++
  ".Lbicc_cmp_addr:\n" ++
  "  li t2, 20; beq t1, t2, .Lbicc_yes\n" ++
  "  add t3, t0, t1; lbu t3, 0(t3)\n" ++
  "  add t4, s0, t1; lbu t4, 0(t4)\n" ++
  "  bne t3, t4, .Lbicc_next_row\n" ++
  "  addi t1, t1, 1; j .Lbicc_cmp_addr\n" ++
  ".Lbicc_next_row:\n" ++
  "  addi s6, s6, 1; j .Lbicc_row_loop\n" ++
  ".Lbicc_yes:\n" ++
  "  li a0, 1; j .Lbicc_ret\n" ++
  ".Lbicc_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbicc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff witness bytecode exposes a literal CREATE2 salt and a BAL\n" ++
  "# creator row with nonce/storage activity produces target for some witness\n" ++
  "# code element used as copied initcode.\n" ++
  "bal_contains_internal_create2_collision_touch:\n" ++
  "  addi sp, sp, -104\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                  # 20-byte target address ptr\n" ++
  "  mv s1, a1                  # witness.codes ptr\n" ++
  "  mv s2, a2                  # witness.codes len\n" ++
  "  mv s3, a3                  # BAL ptr\n" ++
  "  mv s4, a4                  # BAL len\n" ++
  "  mv a0, s1; mv a1, s2; la a2, bbcv_create2_salt\n" ++
  "  jal ra, bal_codes_find_create2_push4_salt\n" ++
  "  beqz a0, .Lbic2_no\n" ++
  "  mv a0, s3; mv a1, s4; la a2, bbcv_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbic2_no\n" ++
  "  la t0, bbcv_count; ld s5, 0(t0)\n" ++
  "  li s6, 0                  # BAL row index\n" ++
  ".Lbic2_row_loop:\n" ++
  "  beq s6, s5, .Lbic2_no\n" ++
  "  mv a0, s3; mv a1, s4; mv a2, s6; la a3, bbcv_off; la a4, bbcv_size\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  bnez a0, .Lbic2_next_row\n" ++
  "  la t0, bbcv_off; ld t1, 0(t0); add s7, s3, t1     # row ptr\n" ++
  "  la t0, bbcv_size; ld s8, 0(t0)                    # row len\n" ++
  "  mv a0, s7; mv a1, s8; li a2, 0; la a3, bbcv_addr_off; la a4, bbcv_addr_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbic2_next_row\n" ++
  "  la t0, bbcv_addr_len; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lbic2_next_row\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add s9, s7, t1 # creator address ptr\n" ++
  "  mv a0, s7; mv a1, s8; li a2, 4; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbic2_check_storage\n" ++
  "  la t0, bbcv_field_off; ld t1, 0(t0); add a0, s7, t1\n" ++
  "  la t0, bbcv_field_len; ld a1, 0(t0); la a2, bbcv_field_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbic2_check_storage\n" ++
  "  la t0, bbcv_field_count; ld t1, 0(t0); bnez t1, .Lbic2_try_creator\n" ++
  ".Lbic2_check_storage:\n" ++
  "  mv a0, s7; mv a1, s8; li a2, 2; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbic2_next_row\n" ++
  "  la t0, bbcv_field_off; ld t1, 0(t0); add a0, s7, t1\n" ++
  "  la t0, bbcv_field_len; ld a1, 0(t0); la a2, bbcv_field_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbic2_next_row\n" ++
  "  la t0, bbcv_field_count; ld t1, 0(t0); beqz t1, .Lbic2_next_row\n" ++
  ".Lbic2_try_creator:\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s9; la a4, bbcv_create2_salt\n" ++
  "  jal ra, bal_try_create2_initcodes\n" ++
  "  bnez a0, .Lbic2_yes\n" ++
  ".Lbic2_next_row:\n" ++
  "  addi s6, s6, 1; j .Lbic2_row_loop\n" ++
  ".Lbic2_yes:\n" ++
  "  li a0, 1; j .Lbic2_ret\n" ++
  ".Lbic2_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbic2_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 104\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 after writing a 32-byte salt when a code element contains\n" ++
  "# PUSH4 <salt>; ...; CREATE2. The PUSH4 literal is zero-extended to BE32.\n" ++
  "bal_codes_find_create2_push4_salt:\n" ++
  "  addi sp, sp, -88\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                  # witness.codes ptr\n" ++
  "  mv s1, a1                  # witness.codes len\n" ++
  "  mv s2, a2                  # 32-byte salt output\n" ++
  "  beqz s1, .Lbc2s_no\n" ++
  "  mv a0, s0; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbc2s_no\n" ++
  "  srli s3, a0, 2             # code count\n" ++
  "  beqz s3, .Lbc2s_no\n" ++
  "  li s4, 0                   # code index\n" ++
  ".Lbc2s_elem_loop:\n" ++
  "  beq s4, s3, .Lbc2s_no\n" ++
  "  slli t0, s4, 2; add a0, s0, t0; jal ra, bgv_u32le\n" ++
  "  mv s5, a0                  # element offset\n" ++
  "  addi t0, s4, 1\n" ++
  "  beq t0, s3, .Lbc2s_last\n" ++
  "  slli t1, t0, 2; add a0, s0, t1; jal ra, bgv_u32le\n" ++
  "  j .Lbc2s_have_end\n" ++
  ".Lbc2s_last:\n" ++
  "  mv a0, s1\n" ++
  ".Lbc2s_have_end:\n" ++
  "  bltu a0, s5, .Lbc2s_next_elem\n" ++
  "  add s6, s0, s5; sub s7, a0, s5\n" ++
  "  li t0, 6; bltu s7, t0, .Lbc2s_next_elem\n" ++
  "  sub s8, s7, t0             # max PUSH4 offset with one following byte\n" ++
  "  li s9, 0                   # scan offset\n" ++
  ".Lbc2s_scan_loop:\n" ++
  "  bgtu s9, s8, .Lbc2s_next_elem\n" ++
  "  add t1, s6, s9\n" ++
  "  lbu t2, 0(t1); li t3, 0x63; bne t2, t3, .Lbc2s_advance_scan\n" ++
  "  addi t4, s9, 5             # search after PUSH4 immediate\n" ++
  ".Lbc2s_find_create2:\n" ++
  "  beq t4, s7, .Lbc2s_advance_scan\n" ++
  "  add t5, s6, t4; lbu t5, 0(t5); li t6, 0xf5; beq t5, t6, .Lbc2s_write_salt\n" ++
  "  addi t4, t4, 1; j .Lbc2s_find_create2\n" ++
  ".Lbc2s_write_salt:\n" ++
  "  sd zero, 0(s2); sd zero, 8(s2); sd zero, 16(s2); sw zero, 24(s2)\n" ++
  "  lbu t0, 1(t1); sb t0, 28(s2)\n" ++
  "  lbu t0, 2(t1); sb t0, 29(s2)\n" ++
  "  lbu t0, 3(t1); sb t0, 30(s2)\n" ++
  "  lbu t0, 4(t1); sb t0, 31(s2)\n" ++
  "  li a0, 1; j .Lbc2s_ret\n" ++
  ".Lbc2s_advance_scan:\n" ++
  "  addi s9, s9, 1; j .Lbc2s_scan_loop\n" ++
  ".Lbc2s_next_elem:\n" ++
  "  addi s4, s4, 1; j .Lbc2s_elem_loop\n" ++
  ".Lbc2s_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbc2s_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 88\n" ++
  "  ret\n" ++
  "\n" ++
  "# Try every witness code element as copied initcode for CREATE2.\n" ++
  "bal_try_create2_initcodes:\n" ++
  "  addi sp, sp, -88\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                  # target address ptr\n" ++
  "  mv s1, a1                  # witness.codes ptr\n" ++
  "  mv s2, a2                  # witness.codes len\n" ++
  "  mv s3, a3                  # creator address ptr\n" ++
  "  mv s4, a4                  # salt ptr\n" ++
  "  beqz s2, .Lbtci_no\n" ++
  "  mv a0, s1; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbtci_no\n" ++
  "  srli s5, a0, 2             # code count\n" ++
  "  beqz s5, .Lbtci_no\n" ++
  "  li s6, 0                   # code index\n" ++
  ".Lbtci_elem_loop:\n" ++
  "  beq s6, s5, .Lbtci_no\n" ++
  "  slli t0, s6, 2; add a0, s1, t0; jal ra, bgv_u32le\n" ++
  "  mv s7, a0                  # element offset\n" ++
  "  addi t0, s6, 1\n" ++
  "  beq t0, s5, .Lbtci_last\n" ++
  "  slli t1, t0, 2; add a0, s1, t1; jal ra, bgv_u32le\n" ++
  "  j .Lbtci_have_end\n" ++
  ".Lbtci_last:\n" ++
  "  mv a0, s2\n" ++
  ".Lbtci_have_end:\n" ++
  "  bltu a0, s7, .Lbtci_next_elem\n" ++
  "  add s8, s1, s7; sub s9, a0, s7\n" ++
  "  mv a0, s3; mv a1, s4; mv a2, s8; mv a3, s9; la a4, bbcv_create_addr\n" ++
  "  jal ra, address_compute_create2\n" ++
  "  la t0, bbcv_create_addr; li t1, 0\n" ++
  ".Lbtci_cmp_addr:\n" ++
  "  li t2, 20; beq t1, t2, .Lbtci_yes\n" ++
  "  add t3, t0, t1; lbu t3, 0(t3)\n" ++
  "  add t4, s0, t1; lbu t4, 0(t4)\n" ++
  "  bne t3, t4, .Lbtci_next_elem\n" ++
  "  addi t1, t1, 1; j .Lbtci_cmp_addr\n" ++
  ".Lbtci_next_elem:\n" ++
  "  addi s6, s6, 1; j .Lbtci_elem_loop\n" ++
  ".Lbtci_yes:\n" ++
  "  li a0, 1; j .Lbtci_ret\n" ++
  ".Lbtci_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbtci_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 88\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff any witness code byte is CREATE (0xf0).\n" ++
  "bal_codes_contains_create_opcode:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra, 0(sp); sd s3, 8(sp); sd s4, 16(sp); sd s5, 24(sp)\n" ++
  "  sd s6, 32(sp); sd s7, 40(sp)\n" ++
  "  beqz s2, .Lbcco_no\n" ++
  "  mv a0, s1; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbcco_no\n" ++
  "  srli s3, a0, 2             # code count\n" ++
  "  beqz s3, .Lbcco_no\n" ++
  "  li s4, 0                   # code index\n" ++
  ".Lbcco_elem_loop:\n" ++
  "  beq s4, s3, .Lbcco_no\n" ++
  "  slli t3, s4, 2; add a0, s1, t3; jal ra, bgv_u32le\n" ++
  "  mv s5, a0                  # element offset\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lbcco_last\n" ++
  "  slli t5, t3, 2; add a0, s1, t5; jal ra, bgv_u32le\n" ++
  "  j .Lbcco_have_end\n" ++
  ".Lbcco_last:\n" ++
  "  mv a0, s2\n" ++
  ".Lbcco_have_end:\n" ++
  "  bltu a0, s5, .Lbcco_next_elem\n" ++
  "  add s6, s1, s5; sub s7, a0, s5\n" ++
  ".Lbcco_scan:\n" ++
  "  beqz s7, .Lbcco_next_elem\n" ++
  "  lbu a0, 0(s6); li t3, 0xf0; beq a0, t3, .Lbcco_yes\n" ++
  "  addi s6, s6, 1; addi s7, s7, -1; j .Lbcco_scan\n" ++
  ".Lbcco_next_elem:\n" ++
  "  addi s4, s4, 1; j .Lbcco_elem_loop\n" ++
  ".Lbcco_yes:\n" ++
  "  li a0, 1; j .Lbcco_ret\n" ++
  ".Lbcco_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbcco_ret:\n" ++
  "  ld ra, 0(sp); ld s3, 8(sp); ld s4, 16(sp); ld s5, 24(sp)\n" ++
  "  ld s6, 32(sp); ld s7, 40(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

end EvmAsm.Codegen
