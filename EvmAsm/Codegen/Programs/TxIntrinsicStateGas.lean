/-
  EvmAsm.Codegen.Programs.TxIntrinsicStateGas

  `tx_intrinsic_state_gas`: per-tx EIP-8037 intrinsic state-gas helper (g8zeq.1.4.3.1).

  Computes the per-transaction EIP-8037 intrinsic-state-gas contribution from
  encoded transaction bytes.  Its byte-tied Program and focused probe live in
  `TxIntrinsicStateGasProg`; this module retains the BAL-aware EIP-7702 helper
  and its array callers.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Codegen.Programs.IntrinsicGas
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.BlockVerdictBalFindAccount
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinals
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.Eip7702Authority
import EvmAsm.Codegen.Programs.CreateCodeEffectLog
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasProg
import EvmAsm.Codegen.Programs.TxIntrinsicAuthEffects

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## tx_intrinsic_state_gas

    Calling convention:
      a0 (input)  : encoded tx bytes ptr
      a1 (input)  : encoded tx byte length
      a2 (input)  : u64 out ptr (receives tx_state_gas = intrinsic_state_gas)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx_extract_to_address failed (bad `to` field / unknown type)
        2 : tx_type_dispatch or EIP-7702 authorization_list parse failed
        (eip8037_tx_state_gas status is propagated on the success path; it cannot
         underflow here because state_refund = 0)

    Scratch: tis_to_buf (20B `to`, unused output), tis_is_creation, tis_type,
    tis_inner_off, tis_auth_count, plus the tea_*
    slots consumed internally by tx_extract_to_address. -/

/-! ## bal_account_nonce_before_index

    Return the latest BAL nonce value for an account strictly before a block
    access index.  `nonce_changes` is AccountChanges item 4 and contains
    `[block_access_index, post_nonce]` tuples.

    a0 = AccountChanges ptr, a1 = length, a2 = current block_access_index
    a0 output = 0 found, 1 no earlier change, 2 malformed; a1 = nonce when found. -/
def balAccountNonceBeforeIndexFunction : String :=
  "bal_account_nonce_before_index:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  li a2, 4; addi a3, sp, 72; addi a4, sp, 80\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbanbi_malformed\n" ++
  "  ld t0, 72(sp); add s3, s0, t0; ld s4, 80(sp)\n" ++
  "  mv a0, s3; mv a1, s4; addi a2, sp, 88; jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbanbi_malformed\n" ++
  "  ld s4, 88(sp); li s5, 0; li s6, 0; li s7, 0; sd zero, 104(sp)\n" ++
  ".Lbanbi_loop:\n" ++
  "  beq s5, s4, .Lbanbi_done_scan\n" ++
  "  mv a0, s3; ld a1, 80(sp); mv a2, s5; addi a3, sp, 72; addi a4, sp, 88\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  bnez a0, .Lbanbi_malformed\n" ++
  "  ld t0, 72(sp); add t0, s3, t0; sd t0, 96(sp)\n" ++
  "  mv a0, t0; ld a1, 88(sp); li a2, 0; addi a3, sp, 72; jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lbanbi_malformed\n" ++
  "  ld t0, 72(sp); bgeu t0, s2, .Lbanbi_next\n" ++
  "  bltu t0, s6, .Lbanbi_next\n" ++
  "  mv s6, t0; ld a0, 96(sp); ld a1, 88(sp); li a2, 1; addi a3, sp, 72\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lbanbi_malformed\n" ++
  "  ld s7, 72(sp); li t0, 1; sd t0, 104(sp)\n" ++
  ".Lbanbi_next:\n" ++
  "  addi s5, s5, 1; j .Lbanbi_loop\n" ++
  ".Lbanbi_done_scan:\n" ++
  "  ld t0, 104(sp); beqz t0, .Lbanbi_none\n" ++
  "  li a0, 0; mv a1, s7; j .Lbanbi_return\n" ++
  ".Lbanbi_none:\n" ++
  "  li a0, 1; li a1, 0; j .Lbanbi_return\n" ++
  ".Lbanbi_malformed:\n" ++
  "  li a0, 2; li a1, 0\n" ++
  ".Lbanbi_return:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 112; ret\n"

/-! ## eip7702_authority_asof

    Resolve one authority at the start of an MTx transaction.  Execution's
    pending/durable AccountState is authoritative for prior successful block
    transitions; on a miss, use only the authenticated pre-block witness.
    BAL post-state fields are intentionally not consulted.

    a0 = canonical authority address
    returns a0 = 0 absent, 1 live, 2 unavailable/malformed, 3 live with
    unsupported (non-delegation) code;
            a1 = current nonce, a2 = is-delegated. -/
def eip7702AuthorityAsOfFunction : String :=
  "eip7702_authority_asof:\n" ++
  "  addi sp, sp, -64; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd a3, 32(sp); sd a4, 40(sp); sd a5, 48(sp); mv s0, a0\n" ++
  "  addi a1, sp, 56; addi a2, sp, 48; mv a0, s0; jal ra, account_state_auth_current\n" ++
  "  li t0, 1; bne a0, t0, .L77as_header; ld a1, 56(sp); ld t0, 48(sp); andi t0, t0, 8; snez a2, t0; li a0, 1; j .L77as_ret\n" ++
  ".L77as_header:\n" ++
  "  li t0, 2; beq a0, t0, .L77as_absent\n" ++
  "  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0); mv a2, s0; li a3, 20; la t0, bv_witness_state_ptr; ld a4, 0(t0); la t0, bv_witness_state_len; ld a5, 0(t0); la a6, teer_pre_acct; jal ra, account_at_header_state_root\n" ++
  "  beqz a0, .L77as_found; li t0, 1; beq a0, t0, .L77as_absent; li a0, 2; li a1, 0; li a2, 0; j .L77as_ret\n" ++
  ".L77as_found:\n" ++
  "  la t0, teer_pre_acct; ld a1, 0(t0)\n" ++
  "  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0); mv a2, s0; la t0, bv_witness_state_ptr; ld a3, 0(t0); la t0, bv_witness_state_len; ld a4, 0(t0); la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0); jal ra, code_at_header_state_root\n" ++
  "  beqz a0, .L77as_code; li t0, 1; beq a0, t0, .L77as_live_empty; li t0, 5; beq a0, t0, .L77as_live_empty; li a0, 2; li a1, 0; li a2, 0; j .L77as_ret\n" ++
  ".L77as_code:\n" ++
  "  la t0, cahsr_code_length; ld t0, 0(t0); beqz t0, .L77as_live_empty; li t1, 23; bne t0, t1, .L77as_invalid_code; la t0, svf_codes_ptr; ld t0, 0(t0); la t1, cahsr_code_offset; ld t1, 0(t1); add t0, t0, t1; lbu t1, 0(t0); li t2, 239; bne t1, t2, .L77as_invalid_code; lbu t1, 1(t0); li t2, 1; bne t1, t2, .L77as_invalid_code; lbu t1, 2(t0); bnez t1, .L77as_invalid_code; li a2, 1; j .L77as_live\n" ++
  ".L77as_invalid_code:\n" ++
  "  li a0, 3; li a1, 0; li a2, 0; j .L77as_ret\n" ++
  ".L77as_live_empty:\n" ++
  "  li a2, 0\n" ++
  ".L77as_live:\n" ++
  "  la t0, teer_pre_acct; ld a1, 0(t0); li a0, 1; j .L77as_ret\n" ++
  ".L77as_absent:\n" ++
  "  li a0, 0; li a1, 0; li a2, 0\n" ++
  ".L77as_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld a3, 32(sp); ld a4, 40(sp); ld a5, 48(sp); addi sp, sp, 64; ret"

/-! ## eip7702_auth_state_prepare

    The live EIP-7702 intrinsic-state-gas writer.  Unlike the frozen legacy
    replay routine, this executes once at the transaction boundary and writes
    its accepted authorizations directly to AccountState's pending overlay.
    AccountState then provides the as-of state to the next transaction only
    after the ordinary success commit.

    a0/a1: inner RLP transaction bytes; a2: sender address; a3: tx type;
    a4: mode (0 = compute this tx's gas, 1 = success-boundary publish only).
    The compute mode writes the runtime auth gas/count cells; publish mode
    writes only AccountState after the transaction has succeeded.  Bad
    individual authorizations are ignored, matching `validate_authorization`.
    Malformed outer RLP returns one so the caller fails closed. -/
def eip7702AuthStatePrepareFunction : String :=
  "eip7702_auth_state_prepare:\n" ++
  "  addi sp, sp, -176; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; sd a4, 136(sp)\n" ++
  "  ld t0, 136(sp); bnez t0, .L77prep_mode_ready; la t0, runtime_tx_auth_state_refund; sd zero, 0(t0); la t0, runtime_tx_auth_regular_refund; sd zero, 0(t0); la t0, runtime_tx_auth_count; sd zero, 0(t0); la t0, runtime_tx_top_frame_regular_gas; sd zero, 0(t0); la t0, teer_success_count; sd zero, 0(t0); .L77prep_mode_ready:\n" ++
  "  li t0, 4; bne s3, t0, .L77prep_ok\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 9; la a3, b1an_auth_off; la a4, b1an_auth_len; jal ra, rlp_list_nth_item; bnez a0, .L77prep_bad_outer\n" ++
  "  la t0, b1an_auth_off; ld t0, 0(t0); add s4, s0, t0; la t0, b1an_auth_len; ld s5, 0(t0)\n" ++
  "  mv a0, s4; mv a1, s5; la a2, b1an_auth_count; jal ra, rlp_list_count_items; bnez a0, .L77prep_bad_list\n" ++
  "  la t0, b1an_auth_count; ld s6, 0(t0); ld t0, 136(sp); bnez t0, .L77prep_auth_intrinsic_done; la t0, runtime_tx_auth_count; sd s6, 0(t0); .L77prep_auth_intrinsic_done: li s7, 0\n" ++
  -- `set_delegation` seeds `written_accounts` with the transaction origin and,
  -- for a value transfer, its recipient.  Retain the typed transaction's
  -- recipient/value shape while walking auth tuples so ACCOUNT_WRITE is charged
  -- only for an authority that is not already in that set.  The item helper
  -- returns the recipient's raw 20-byte content; a zero-length value is zero.
  "  mv a0, s0; mv a1, s1; li a2, 5; addi a3, sp, 144; addi a4, sp, 152; jal ra, rlp_list_nth_item; bnez a0, .L77prep_bad_outer; ld t0, 144(sp); add t0, s0, t0; sd t0, 144(sp)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 6; addi a3, sp, 160; addi a4, sp, 168; jal ra, rlp_list_nth_item; bnez a0, .L77prep_bad_outer; ld t0, 168(sp); bnez t0, .L77prep_value_nonzero; sd zero, 160(sp); j .L77prep_value_done\n" ++
  ".L77prep_value_nonzero:\n" ++
  "  li t0, 1; sd t0, 160(sp)\n" ++
  ".L77prep_value_done:\n" ++
  ".L77prep_loop:\n" ++
  "  bgeu s7, s6, .L77prep_ok\n" ++
  "  mv a0, s4; mv a1, s5; mv a2, s7; la a3, b1an_item_off; la a4, b1an_item_len; jal ra, rlp_item_span; bnez a0, .L77prep_bad_span\n" ++
  "  la t0, b1an_item_off; ld t0, 0(t0); add s8, s4, t0; la t0, b1an_item_len; ld s9, 0(t0)\n" ++
  -- chain id, target and signed nonce are all read from the immutable tuple.
  "  mv a0, s8; mv a1, s9; li a2, 0; la a3, b1an_field; jal ra, rlp_field_to_u64; bnez a0, .L77prep_bad_chain; la t0, b1an_field; ld t0, 0(t0); beqz t0, .L77prep_chain_ok; la t1, bv_chain_id; ld t1, 0(t1); bne t0, t1, .L77prep_next\n" ++
  ".L77prep_chain_ok:\n" ++
  "  mv a0, s8; mv a1, s9; li a2, 2; la a3, b1an_signed_nonce; jal ra, rlp_field_to_u64; bnez a0, .L77prep_bad_nonce; la t0, b1an_signed_nonce; ld t0, 0(t0); li t1, -1; beq t0, t1, .L77prep_next\n" ++
  -- `rlp_list_nth_item` returns raw byte-string CONTENT, with its RLP prefix
  -- stripped.  Thus `0x80` is a zero-length target and `0x94 || address`
  -- is returned as the 20-byte address payload.
  "  mv a0, s8; mv a1, s9; li a2, 1; la a3, b1an_target_off; la a4, b1an_target_len; jal ra, rlp_list_nth_item; bnez a0, .L77prep_bad_target; la t0, b1an_target_off; ld t0, 0(t0); add s10, s8, t0; la t0, b1an_target_len; ld t0, 0(t0); beqz t0, .L77prep_target_maybe_null; li t1, 20; bne t0, t1, .L77prep_next; li s11, 1; li t0, 0\n" ++
  ".L77prep_target_zero_loop:\n" ++
  "  li t1, 20; beq t0, t1, .L77prep_target_all_zero; add t1, s10, t0; lbu t1, 0(t1); bnez t1, .L77prep_recover; addi t0, t0, 1; j .L77prep_target_zero_loop\n" ++
  ".L77prep_target_all_zero:\n" ++
  "  li s10, 0; li s11, 0; j .L77prep_recover\n" ++
  ".L77prep_target_maybe_null:\n" ++
  "  li s10, 0; li s11, 0\n" ++
  ".L77prep_target_null:\n" ++
  "  li s10, 0; li s11, 0\n" ++
  ".L77prep_recover:\n" ++
  "  mv a0, s8; mv a1, s9; la a2, b1an_authority; la a3, b1an_recover_scratch; jal ra, eip7702_authorization_recover_address; bnez a0, .L77prep_next\n" ++
  "  la a0, b1an_authority; jal ra, eip7702_authority_asof; sd a0, 104(sp); sd a1, 112(sp); sd a2, 120(sp); li t0, 2; bgeu a0, t0, .L77prep_next\n" ++
  -- `process_transaction` increments the sender nonce before processing its
  -- authorization list.  For a self-sponsored authorization, therefore,
  -- validate against the AccountState-as-of nonce plus that transaction's
  -- sender increment; other authorities use their as-of nonce unchanged.
  "  la t0, b1an_signed_nonce; ld t0, 0(t0); ld t1, 112(sp); la t2, b1an_authority; li t3, 0\n" ++
  ".L77prep_sender_nonce_cmp:\n" ++
  "  li t4, 20; beq t3, t4, .L77prep_sender_nonce_inc; add t4, t2, t3; lbu t5, 0(t4); add t4, s2, t3; lbu t6, 0(t4); bne t5, t6, .L77prep_sender_nonce_ready; addi t3, t3, 1; j .L77prep_sender_nonce_cmp\n" ++
  ".L77prep_sender_nonce_inc:\n" ++
  "  addi t1, t1, 1\n" ++
  ".L77prep_sender_nonce_ready:\n" ++
  "  bne t0, t1, .L77prep_next\n" ++
  -- `teer_success_table` is now a transaction-local first-write set only:
  -- AccountState owns all cross-transaction state, while this bounded table
  -- implements the spec's one ACCOUNT_WRITE charge per authority per tx.
  "  li t0, 1; sd t0, 128(sp); sd zero, 168(sp); la t0, teer_success_count; ld t1, 0(t0); li t2, 0\n" ++
  ".L77prep_seen_loop:\n" ++
  "  bgeu t2, t1, .L77prep_seen_append; slli t3, t2, 5; la t4, teer_success_table; add t4, t4, t3; li t5, 0\n" ++
  ".L77prep_seen_cmp:\n" ++
  "  li t6, 20; beq t5, t6, .L77prep_seen_found; la t3, b1an_authority; add t3, t3, t5; lbu t6, 0(t3); add t3, t4, t5; lbu t3, 0(t3); bne t6, t3, .L77prep_seen_next; addi t5, t5, 1; j .L77prep_seen_cmp\n" ++
  ".L77prep_seen_next:\n" ++
  "  addi t2, t2, 1; j .L77prep_seen_loop\n" ++
  ".L77prep_seen_found:\n" ++
  "  lw t0, 20(t4); sd t0, 168(sp); sd zero, 128(sp); j .L77prep_charges\n" ++
  ".L77prep_seen_append:\n" ++
  "  li t3, " ++ toString teerSuccessfulAuthCapacity ++ "; bgeu t1, t3, .L77prep_bad; slli t3, t1, 5; la t4, teer_success_table; add t4, t4, t3; la t5, b1an_authority; li t6, 0\n" ++
  ".L77prep_seen_copy:\n" ++
  "  li t3, 20; beq t6, t3, .L77prep_seen_stored; add t3, t5, t6; lbu t3, 0(t3); add a4, t4, t6; sb t3, 0(a4); addi t6, t6, 1; j .L77prep_seen_copy\n" ++
  ".L77prep_seen_stored:\n" ++
  "  sw zero, 20(t4); la t0, teer_success_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  ".L77prep_charges:\n" ++
  "  ld t0, 136(sp); bnez t0, .L77prep_record\n" ++
  -- state charge = NEW_ACCOUNT iff absent, plus AUTH_BASE for a non-null
  -- delegation target when the current state is not already delegated.
  "  ld t0, 104(sp); bnez t0, .L77prep_no_new; la t0, runtime_tx_auth_state_refund; ld t1, 0(t0); li t2, " ++ toString amsterdamNewAccountStateGas ++ "; add t1, t1, t2; sd t1, 0(t0)\n" ++
  ".L77prep_no_new:\n" ++
  "  beqz s11, .L77prep_regular; ld t0, 120(sp); bnez t0, .L77prep_regular; ld t0, 168(sp); bnez t0, .L77prep_regular; la t0, runtime_tx_auth_state_refund; ld t1, 0(t0); li t2, " ++ toString (amsterdamStateBytesPerAuthBase * amsterdamCostPerStateByte) ++ "; add t1, t1, t2; sd t1, 0(t0); li t0, 1; sw t0, 20(t4)\n" ++
  ".L77prep_regular:\n" ++
  -- ACCOUNT_WRITE is charged exactly once for a non-sender authority in this
  -- transaction; the transaction-local first-write set above intentionally
  -- does not leak across the success commit boundary.
  "  ld t0, 128(sp); beqz t0, .L77prep_record; la t0, b1an_authority; li t1, 0\n" ++
  ".L77prep_sender_cmp:\n" ++
  "  li t2, 20; beq t1, t2, .L77prep_not_sender; add t2, t0, t1; lbu t3, 0(t2); add t2, s2, t1; lbu t4, 0(t2); bne t3, t4, .L77prep_not_sender; addi t1, t1, 1; j .L77prep_sender_cmp\n" ++
  ".L77prep_not_sender:\n" ++
  "  li t2, 20; beq t1, t2, .L77prep_record; ld t0, 160(sp); beqz t0, .L77prep_charge_regular; ld t0, 152(sp); li t1, 20; bne t0, t1, .L77prep_charge_regular; ld t0, 144(sp); la t1, b1an_authority; li t2, 0\n" ++
  ".L77prep_recipient_cmp:\n" ++
  "  li t3, 20; beq t2, t3, .L77prep_record; add t3, t0, t2; lbu t4, 0(t3); add t3, t1, t2; lbu t3, 0(t3); bne t4, t3, .L77prep_charge_regular; addi t2, t2, 1; j .L77prep_recipient_cmp\n" ++
  ".L77prep_charge_regular:\n" ++
  "  la t0, runtime_tx_auth_regular_refund; ld t1, 0(t0); li t2, 8000; add t1, t1, t2; sd t1, 0(t0); la t0, runtime_tx_top_frame_regular_gas; ld t1, 0(t0); li t2, 8000; add t1, t1, t2; sd t1, 0(t0)\n" ++
  ".L77prep_record:\n" ++
  "  ld t0, 136(sp); beqz t0, .L77prep_next; la a0, b1an_authority; ld a1, 112(sp); addi a1, a1, 1; mv a2, s11; jal ra, account_state_record_auth; bnez a0, .L77prep_bad_record\n" ++
  -- `set_delegation` increments the recovered authority once per valid
  -- authorization entry, even when the same authority appears repeatedly.
  -- B1 tracks only transaction senders, so replay that increment only when
  -- this valid authority has a sender-table row.  This runs only in mode 1:
  -- successful preparation persists across a body revert, while preparation
  -- failure never reaches the publish pass.
  "  la a0, bv_b1_sender_table; la t0, bv_b1_sender_count; ld a1, 0(t0); la a2, b1an_authority; jal ra, b1_sender_table_find; bnez a0, .L77prep_next; ld t0, 32(a1); addi t0, t0, 1; sd t0, 32(a1)\n" ++
  ".L77prep_next:\n" ++
  "  addi s7, s7, 1; j .L77prep_loop\n" ++
  ".L77prep_ok:\n" ++
  "  li a0, 0; j .L77prep_ret\n" ++
  ".L77prep_bad_outer:\n" ++
  ".L77prep_bad_list:\n" ++
  ".L77prep_bad_span:\n" ++
  ".L77prep_bad_chain:\n" ++
  ".L77prep_bad_nonce:\n" ++
  ".L77prep_bad_target:\n" ++
  ".L77prep_bad_record:\n" ++
  ".L77prep_bad:\n" ++
  "  li a0, 1\n" ++
  ".L77prep_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp); addi sp, sp, 176; ret"

/-- Live per-transaction intrinsic state-gas boundary.

    This replaces the former block-final replay/overlay: decode the transaction's
    ordinary intrinsic state charge and add the AccountState-as-of-this-tx
    EIP-7702 charge while both inputs are live.  The intrinsic decoder needs
    the full typed envelope, whereas authorization decoding needs the inner
    RLP payload; multi-tx contexts retain both representations. -/
def blockVerdictTxStateGasInlinePrepareFunction : String :=
  "block_verdict_tx_state_gas_inline_prepare:\n" ++
  -- a0/a1 = full typed envelope; a2/a3 = inner RLP; a4 = sender;
  -- a5 = tx type; a6 = transaction index.
  "  addi sp, sp, -64; sd ra, 0(sp); sd a0, 8(sp); sd a1, 16(sp); sd a2, 24(sp); sd a3, 32(sp); sd a4, 40(sp); sd a5, 48(sp); sd a6, 56(sp)\n" ++
  "  slli t0, a6, 3; la t1, bvgr_tx_state_gas; add a2, t1, t0; ld a0, 8(sp); ld a1, 16(sp); jal ra, tx_intrinsic_state_gas\n" ++
  "  bnez a0, .Lbvtgip_ret\n" ++
  "  ld t0, 56(sp); slli t0, t0, 3; la t1, bvgr_tx_state_gas; add t1, t1, t0; ld t2, 0(t1)\n" ++
  "  ld a0, 24(sp); ld a1, 32(sp); ld a2, 40(sp); ld a3, 48(sp); li a4, 0; jal ra, eip7702_auth_state_prepare\n" ++
  "  bnez a0, .Lbvtgip_ret\n" ++
  "  ld t0, 56(sp); slli t0, t0, 3; la t1, bvgr_tx_state_gas; add t1, t1, t0; ld t2, 0(t1); la t3, runtime_tx_auth_state_refund; ld t3, 0(t3); add t2, t2, t3; sd t2, 0(t1)\n" ++
  ".Lbvtgip_ret:\n" ++
  "  ld ra, 0(sp); addi sp, sp, 64; ret"

/-- Complete the live per-transaction state-gas cell after execution settles.

    State refunds are presently represented by the zero-initialized
    `bvgr_tx_state_refund` substrate, so the exact current identity is the
    intrinsic/auth charge plus executed state gas for successful transactions.
    Failed transactions retain only the intrinsic/auth component. -/
def blockVerdictTxStateGasInlineFinalizeFunction : String :=
  "block_verdict_tx_state_gas_inline_finalize:\n" ++
  "  slli t0, a0, 3; la t1, bvgr_tx_state_gas; add t1, t1, t0; ld t2, 0(t1)\n" ++
  -- The depth-zero preparation snapshot is rolled back on ExceptionalHalt.
  -- `runtime_tx_auth_phase_applied` is the same gas-coverage-derived control
  -- fact used by the AccountState commit path: a failed transaction before
  -- that point restores the *entire* pre-preparation state-gas cell.  The
  -- dispatcher may already have consumed the live auth-refund scratch while
  -- attempting its gas spill, so subtracting that scratch here is neither
  -- stable nor the snapshot semantics.
  "  bnez a1, .Lbvtgif_exec\n" ++
  "  la t3, runtime_tx_auth_phase_applied; ld t3, 0(t3); bnez t3, .Lbvtgif_store; sd zero, 0(t1); li t2, 0\n" ++
  -- The same pre-dispatch snapshot owns the staged ACCOUNT_WRITE regular gas.
  -- A phase-zero exceptional halt restores it together with NEW_ACCOUNT and
  -- AUTH_BASE; a body revert (phase one) retains all preparation charges.
  "  .Lbvtgif_clear_regular: la t3, runtime_tx_auth_regular_refund; sd zero, 0(t3); la t3, runtime_tx_top_frame_regular_gas; sd zero, 0(t3); j .Lbvtgif_store\n" ++
  ".Lbvtgif_exec:\n" ++
  "  la t3, bvgr_tx_exec_state_gas; add t3, t3, t0; ld t3, 0(t3); add t2, t2, t3\n" ++
  ".Lbvtgif_store:\n" ++
  "  la t1, bvgr_tx_total_state_gas; add t1, t1, t0; sd t2, 0(t1); li a0, 0; ret"

end EvmAsm.Codegen
