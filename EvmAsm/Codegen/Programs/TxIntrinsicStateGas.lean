/-
  EvmAsm.Codegen.Programs.TxIntrinsicStateGas

  `tx_intrinsic_state_gas`: per-tx EIP-8037 intrinsic state-gas helper (g8zeq.1.4.3.1).

  In the BAL-replay-only guest there is no opcode-level `state_gas_used` /
  `state_refund`, so a transaction's `tx_state_gas` reduces to its
  `intrinsic_state_gas` (eip8037_tx_state_gas with state_gas_used = state_refund =
  error = 0). This helper computes that per-tx value from the encoded tx alone:

    intrinsic_state_gas = (is_creation ? NEW_ACCOUNT_STATE_GAS : 0)
                        + authorization_count * AUTH_STATE_GAS_PER_AUTH

  It composes existing, verified building blocks:
    - tx_extract_to_address  (K101)  -> is_creation, handling per-type `to` index
    - tx_type_dispatch       (K40)   -> tx type + inner-RLP offset (for the type-4 auth list)
    - RlpWalk / rlp_list_count_items -> EIP-7702 authorization_list count
    - eip8037_tx_state_gas   (g8zeq.1.3) -> the canonical settlement (intrinsic + 0 - 0)

  It is intentionally standalone and UNWIRED: g8zeq.1.4.3 will call it per-tx to
  fill the `bvgr_tx_state_gas` array in a separate arena pass, WITHOUT modifying
  the wired `block_verdict_tx_gas_limits` (zero regression risk).
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
import EvmAsm.Codegen.Programs.Eip7702Authority
import EvmAsm.Codegen.Programs.CreateCodeEffectLog

namespace EvmAsm.Codegen

open EvmAsm.Rv64

private def repeatAsm : Nat -> String -> String
  | 0, _ => ""
  | n + 1, s => s ++ repeatAsm n s

/-- Maximum EIP-7702 authorizations admitted by Amsterdam's 16,777,216 regular
    transaction-gas cap at 15,816 regular gas per authorization. -/
private def teerSuccessfulAuthCapacity : Nat := 1060

private def rlpWalkSkipAsm (failLabel : String) (n : Nat) (cursorReg endReg : String) : String :=
  repeatAsm n <|
    "  mv a0, " ++ cursorReg ++ "; mv a1, " ++ endReg ++
    "; jal ra, rlp_walk_next; bnez a1, " ++ failLabel ++
    "; mv " ++ cursorReg ++ ", a0\n"

private def rlpWalkFieldAsm
    (failLabel : String) (n : Nat) (cursorReg endReg ptrReg lenReg : String) : String :=
  rlpWalkSkipAsm failLabel n cursorReg endReg ++
  "  mv a0, " ++ cursorReg ++ "; mv a1, " ++ endReg ++
  "; jal ra, rlp_walk_next; bnez a1, " ++ failLabel ++ "\n" ++
  "  sub " ++ ptrReg ++ ", a0, a2; mv " ++ lenReg ++ ", a2\n"

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
def txIntrinsicStateGasFunction : String :=
  "tx_intrinsic_state_gas:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # tx_ptr\n" ++
  "  mv s1, a1                   # tx_len\n" ++
  "  mv s2, a2                   # out ptr\n" ++
  "  # is_creation via K101 (handles per-type `to` field index)\n" ++
  "  mv a0, s0; mv a1, s1; la a2, tis_to_buf; la a3, tis_is_creation\n" ++
  "  jal ra, tx_extract_to_address\n" ++
  "  bnez a0, .Ltisg_fail1\n" ++
  "  # tx type + inner-RLP offset (for the EIP-7702 authorization_list)\n" ++
  "  mv a0, s0; mv a1, s1; la a2, tis_type; la a3, tis_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Ltisg_fail2\n" ++
  "  li s3, 0                    # authorization_count\n" ++
  "  la t0, tis_type; ld t1, 0(t0); li t2, 4; bne t1, t2, .Ltisg_no_auth\n" ++
  "  # type 4 (EIP-7702): authorization_list is inner field index 9\n" ++
  "  la t0, tis_inner_off; ld t1, 0(t0)\n" ++
  "  add a0, s0, t1              # inner RLP ptr\n" ++
  "  sub a1, s1, t1              # inner RLP len\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Ltisg_fail2\n" ++
  "  mv s5, a0; mv s6, a1\n" ++
  rlpWalkFieldAsm ".Ltisg_fail2" 9 "s5" "s6" "a0" "a1" ++
  "  la a2, tis_auth_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Ltisg_fail2\n" ++
  "  la t0, tis_auth_count; ld s3, 0(t0)\n" ++
  ".Ltisg_no_auth:\n" ++
  "  li s4, 0                    # intrinsic_state_gas accumulator\n" ++
  "  la t0, tis_is_creation; ld t1, 0(t0); beqz t1, .Ltisg_after_create\n" ++
  liAmsterdamNewAccountStateGas "t2" ++
  "  add s4, s4, t2\n" ++
  ".Ltisg_after_create:\n" ++
  "  beqz s3, .Ltisg_after_auth\n" ++
  liAmsterdamAuthStateGasPerAuth "t2" ++
  "  mul t3, s3, t2; add s4, s4, t3\n" ++
  ".Ltisg_after_auth:\n" ++
  "  # tx_state_gas = eip8037_tx_state_gas(intrinsic, 0, 0, error=0, is_creation)\n" ++
  "  mv a0, s4; li a1, 0; li a2, 0; li a3, 0\n" ++
  "  la t0, tis_is_creation; ld a4, 0(t0)\n" ++
  "  mv a5, s2\n" ++
  "  jal ra, eip8037_tx_state_gas\n" ++
  "  j .Ltisg_ret\n" ++
  ".Ltisg_fail1:\n" ++
  "  li a0, 1; sd zero, 0(s2); j .Ltisg_ret\n" ++
  ".Ltisg_fail2:\n" ++
  "  li a0, 2; sd zero, 0(s2)\n" ++
  ".Ltisg_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_tx_intrinsic_state_gas`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes 8..16  : tx_len
      bytes 16..   : encoded tx bytes
    Output:
      bytes 0.. 8  : status
      bytes 8..16  : tx_state_gas (= intrinsic_state_gas) -/
def ziskTxIntrinsicStateGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # tx_len\n" ++
  "  addi a0, a4, 16             # tx ptr\n" ++
  "  li a2, 0xa0010008           # tx_state_gas out (OUTPUT + 8)\n" ++
  "  jal ra, tx_intrinsic_state_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Ltisg_pdone\n" ++
  txIntrinsicStateGasFunction ++ "\n" ++
  txExtractToAddressFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  eip8037TxStateGasFunction ++ "\n" ++
  ".Ltisg_pdone:"

def ziskTxIntrinsicStateGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "tea_type:\n  .zero 8\n" ++
  "tea_inner_off:\n  .zero 8\n" ++
  "tea_field_off:\n  .zero 8\n" ++
  "tea_field_len:\n  .zero 8\n" ++
  "tis_to_buf:\n  .zero 32\n" ++
  "tis_is_creation:\n  .zero 8\n" ++
  "tis_type:\n  .zero 8\n" ++
  "tis_inner_off:\n  .zero 8\n" ++
  "tis_auth_count:\n  .zero 8"

def ziskTxIntrinsicStateGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxIntrinsicStateGasPrologue
  dataAsm     := ziskTxIntrinsicStateGasDataSection
}


/-! ## tx_eip7702_existing_authority_refund

    Bridge for the EIP-7702 existing-authority state-gas refund. For type-4
    authorizations that pass basic chain/nonce/target parsing, this recovers the
    authority address, finds the authority's BAL AccountChanges row, and subtracts
    the NEW_ACCOUNT refund when the authority existed in pre-state and BAL shows
    the authorization nonce increment. It separately subtracts AUTH_BASE only when
    the authority code was already a delegation marker. Callers pass BAL ptr 0 to
    keep the older intrinsic-only behavior.

    Calling convention:
      a0 = encoded tx ptr, a1 = encoded tx len
      a2 = BAL ptr gate (0 disables), a3 = BAL length
      a4 = block chain id
      a5 = current tx block_access_index (tx index + 1)
      a0 output = state refund amount (u64). Parse failures for an individual
                  authorization conservatively contribute zero.
      a1 output = regular refund amount (u64) to add to refund_counter. -/
def txEip7702ExistingAuthorityRefundFunction : String :=
  "tx_eip7702_existing_authority_refund:\n" ++
  "  addi sp, sp, -160\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  sd a5, 104(sp)              # current block_access_index\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx len\n" ++
  "  mv s2, a2                   # BAL ptr\n" ++
  "  mv s3, a3                   # reserved\n" ++
  "  mv s4, a4                   # chain id\n" ++
  "  li s10, 0                   # accumulated state refund\n" ++
  "  la t0, teer_regular_refund; sd zero, 0(t0)\n" ++
  "  la t0, teer_success_count; sd zero, 0(t0)\n" ++
  "  beqz s2, .Lteer_done\n" ++
  "  mv a0, s0; mv a1, s1; la a2, teer_type; la a3, teer_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Lteer_done\n" ++
  "  la t0, teer_type; ld t1, 0(t0); li t2, 4; bne t1, t2, .Lteer_done\n" ++
  "  la t0, teer_inner_off; ld t1, 0(t0); add s5, s0, t1; sub s6, s1, t1\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lteer_done\n" ++
  "  mv s5, a0; mv s6, a1\n" ++
  rlpWalkFieldAsm ".Lteer_done" 9 "s5" "s6" "s5" "s6" ++
  "  mv a0, s5; mv a1, s6; la a2, teer_auth_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lteer_done\n" ++
  "  la t0, teer_auth_count; ld s7, 0(t0)\n" ++
  "  li t0, 1; bgtu s7, t0, .Lteer_same_authority_try\n" ++
  ".Lteer_single_loop_setup:\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lteer_done\n" ++
  "  mv s5, a0; mv s6, a1; li s8, 0\n" ++
  ".Lteer_loop:\n" ++
  "  beq s8, s7, .Lteer_done\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lteer_done\n" ++
  "  mv s5, a0; sub s9, a0, a2; sd a2, 136(sp)\n" ++
  "  mv a0, s9; ld a1, 136(sp); jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lteer_next\n" ++
  "  sd a0, 112(sp); sd a1, 120(sp)\n" ++
  "  ld a0, 112(sp); ld a1, 120(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lteer_next\n" ++
  "  sd a0, 112(sp); sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lteer_next\n" ++
  "  mv t1, a0; beqz t1, .Lteer_chain_ok; bne t1, s4, .Lteer_invalid_auth_full_refund\n" ++
  ".Lteer_chain_ok:\n" ++
  "  ld a0, 112(sp); ld a1, 120(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lteer_next\n" ++
  "  sd a0, 112(sp); li t2, 20; bne a2, t2, .Lteer_next\n" ++
  "  sub s11, a0, a2\n" ++
  "  ld a0, 112(sp); ld a1, 120(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lteer_next\n" ++
  "  sd a0, 112(sp); sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lteer_next\n" ++
  "  mv t1, a0; li t2, -1; beq t1, t2, .Lteer_invalid_auth_full_refund\n" ++
  "  sd t1, 144(sp)              # signed authorization nonce\n" ++
  "  mv a0, s9; ld a1, 136(sp); la a2, teer_authority; la a3, teer_recover_scratch\n" ++
  "  jal ra, eip7702_authorization_recover_address\n" ++
  "  bnez a0, .Lteer_invalid_auth_full_refund\n" ++
  "  # A prior successfully validated tuple with this exact (authority, nonce)\n" ++
  "  # necessarily incremented the live nonce, so this occurrence is invalid.\n" ++
  "  la t0, teer_success_count; ld t1, 0(t0); li t2, 0\n" ++
  ".Lteer_success_find_loop:\n" ++
  "  beq t2, t1, .Lteer_success_not_found\n" ++
  "  slli t3, t2, 5; la t4, teer_success_table; add t3, t3, t4\n" ++
  "  la t4, teer_authority; mv t5, t3; li t6, 20\n" ++
  ".Lteer_success_addr_cmp:\n" ++
  "  beqz t6, .Lteer_success_addr_match\n" ++
  "  lbu a6, 0(t4); lbu a7, 0(t5); bne a6, a7, .Lteer_success_find_next\n" ++
  "  addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lteer_success_addr_cmp\n" ++
  ".Lteer_success_addr_match:\n" ++
  "  ld t4, 24(t3); ld t5, 144(sp); beq t4, t5, .Lteer_invalid_auth_full_refund\n" ++
  ".Lteer_success_find_next:\n" ++
  "  addi t2, t2, 1; j .Lteer_success_find_loop\n" ++
  ".Lteer_success_not_found:\n" ++
  "  mv a0, s2; mv a1, s3; la a2, teer_authority; la a3, teer_acct_ptr; la a4, teer_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .Lteer_next\n" ++
  "  la t0, teer_acct_ptr; ld a0, 0(t0); la t0, teer_acct_len; ld a1, 0(t0); la a2, teer_finals\n" ++
  "  jal ra, bal_account_nonstorage_finals\n" ++
  "  bnez a0, .Lteer_next\n" ++
  "  # execution-specs validate_authorization returns None when recovered authority\n" ++
  "  # has non-empty ordinary code, and set_delegation refunds the full auth state\n" ++
  "  # charge plus ACCOUNT_WRITE for every None case. In single-tx blocks the header\n" ++
  "  # pre-state code is the live authority code at set_delegation time.\n" ++
  "  la t0, svf_tx_count; ld t0, 0(t0); li t1, 1; bne t0, t1, .Lteer_invalid_code_check_done\n" ++
  "  la t0, bv_witness_state_ptr; ld a3, 0(t0); beqz a3, .Lteer_invalid_code_check_done\n" ++
  "  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, teer_authority\n" ++
  "  la t0, bv_witness_state_len; ld a4, 0(t0)\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  bnez a0, .Lteer_invalid_code_check_done\n" ++
  "  la t0, cahsr_code_length; ld t1, 0(t0); beqz t1, .Lteer_invalid_code_check_done\n" ++
  "  li t2, 23; bne t1, t2, .Lteer_invalid_auth_full_refund\n" ++
  "  la t0, svf_codes_ptr; ld t0, 0(t0); la t1, cahsr_code_offset; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  lbu t1, 0(t0); li t2, 0xef; bne t1, t2, .Lteer_invalid_auth_full_refund\n" ++
  "  lbu t1, 1(t0); li t2, 0x01; bne t1, t2, .Lteer_invalid_auth_full_refund\n" ++
  "  lbu t1, 2(t0); bnez t1, .Lteer_invalid_auth_full_refund\n" ++
  "  j .Lteer_invalid_code_check_done\n" ++
  ".Lteer_invalid_auth_full_refund:\n" ++
  liAmsterdamAuthStateGasPerAuth "t3" ++
  "  add s10, s10, t3\n" ++
  "  la t0, teer_regular_refund; ld t4, 0(t0); li t3, 8000; add t4, t4, t3; sd t4, 0(t0)\n" ++
  "  j .Lteer_next\n" ++
  ".Lteer_invalid_code_check_done:\n" ++
  "  # validate_authorization also returns None when the signed nonce does not\n" ++
  "  # equal the authority account nonce. In single-tx blocks the header-state\n" ++
  "  # account is the live authority account at this point.\n" ++
  "  la t0, svf_tx_count; ld t0, 0(t0); li t1, 1; bne t0, t1, .Lteer_nonce_check_done\n" ++
  "  la t0, bv_witness_state_ptr; ld t0, 0(t0); beqz t0, .Lteer_nonce_check_done\n" ++
  "  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, teer_authority; li a3, 20; la t0, bv_witness_state_ptr; ld a4, 0(t0); la t0, bv_witness_state_len; ld a5, 0(t0); la a6, teer_pre_acct\n" ++
  "  jal ra, account_at_header_state_root\n" ++
  "  beqz a0, .Lteer_nonce_have_pre\n" ++
  "  li t0, 1; bne a0, t0, .Lteer_nonce_check_done\n" ++
  "  ld t1, 144(sp); bnez t1, .Lteer_invalid_auth_full_refund\n" ++
  "  j .Lteer_nonce_check_done\n" ++
  ".Lteer_nonce_have_pre:\n" ++
  "  la t0, teer_pre_acct; ld t1, 0(t0)        # header-state nonce\n" ++
  "  # process_transaction increments the sender nonce before set_delegation.\n" ++
  "  # For a self-sponsored authorization the live comparison nonce is therefore\n" ++
  "  # header_nonce + 1; other authorities still compare against header_nonce.\n" ++
  "  la t2, teer_authority; la t3, bv_stx_sender_addr; li t4, 20\n" ++
  ".Lteer_nonce_sender_cmp:\n" ++
  "  beqz t4, .Lteer_nonce_sender_match\n" ++
  "  lbu t5, 0(t2); lbu t6, 0(t3); bne t5, t6, .Lteer_nonce_expected_ready\n" ++
  "  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lteer_nonce_sender_cmp\n" ++
  ".Lteer_nonce_sender_match:\n" ++
  "  addi t1, t1, 1\n" ++
  ".Lteer_nonce_expected_ready:\n" ++
  "  ld t2, 144(sp); bne t1, t2, .Lteer_invalid_auth_full_refund\n" ++
  ".Lteer_nonce_check_done:\n" ++
  "  # Every successful validate_authorization path increments the authority\n" ++
  "  # nonce. A recovered authority with no BAL nonce change therefore took the\n" ++
  "  # execution-specs None branch and receives the full per-auth refund.\n" ++
  "  la t0, teer_finals; ld t1, 40(t0); beqz t1, .Lteer_invalid_auth_full_refund\n" ++
  "  # Record only tuples that have passed the chain/signature/code/nonce gates.\n" ++
  "  # Capacity covers the protocol maximum; the guard remains conservative.\n" ++
  "  la t0, teer_success_count; ld t1, 0(t0); li t2, " ++ toString teerSuccessfulAuthCapacity ++ "; bgeu t1, t2, .Lteer_success_append_done\n" ++
  "  slli t2, t1, 5; la t3, teer_success_table; add t2, t2, t3\n" ++
  "  la t3, teer_authority; mv t4, t2; li t5, 20\n" ++
  ".Lteer_success_copy:\n" ++
  "  beqz t5, .Lteer_success_copy_done\n" ++
  "  lbu t6, 0(t3); sb t6, 0(t4); addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lteer_success_copy\n" ++
  ".Lteer_success_copy_done:\n" ++
  "  ld t3, 144(sp); sd t3, 24(t2); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  ".Lteer_success_append_done:\n" ++
  "  # Later execution can increment the same authority nonce again (e.g. delegated CREATE2).\n" ++
  "  la t0, teer_finals\n" ++
  "  ld t1, 48(t0); ld t2, 144(sp); addi t2, t2, 1; bltu t1, t2, .Lteer_next\n" ++
  "  # execution-specs set_delegation refunds NEW_ACCOUNT when the authority\n" ++
  "  # account already exists, even if delegating to NULL_ADDRESS causes no code change.\n" ++
  "  la t0, teer_records_ptr; ld t0, 0(t0); beqz t0, .Lteer_existing_code_check\n" ++
  "  la t1, bfa_index; ld t1, 0(t1); slli t2, t1, 4; slli t3, t1, 3; add t2, t2, t3; add t2, t0, t2\n" ++
  "  ld t3, 16(t2); bnez t3, .Lteer_existing_code_check\n" ++
  liAmsterdamNewAccountStateGas "t3" ++
  "  add s10, s10, t3\n" ++
  "  la t0, teer_regular_refund; ld t4, 0(t0); li t3, 8000; add t4, t4, t3; sd t4, 0(t0)\n" ++
  ".Lteer_existing_code_check:\n" ++
  "  la t0, teer_finals; ld t1, 56(t0); beqz t1, .Lteer_final_no_code\n" ++
  "  ld t2, 72(t0); beqz t2, .Lteer_marker_match\n" ++
  "  li t3, 23; bne t2, t3, .Lteer_next\n" ++
  "  ld t2, 64(t0); la t4, teer_acct_ptr; ld t4, 0(t4); add t2, t4, t2\n" ++
  "  lbu t3, 0(t2); li t4, 0xef; bne t3, t4, .Lteer_next\n" ++
  "  lbu t3, 1(t2); li t4, 0x01; bne t3, t4, .Lteer_next\n" ++
  "  lbu t3, 2(t2); bnez t3, .Lteer_next\n" ++
  "  addi t2, t2, 3; mv t4, s11; li t5, 20\n" ++
  ".Lteer_marker_cmp:\n" ++
  "  beqz t5, .Lteer_marker_match\n" ++
  "  lbu t3, 0(t2); lbu t6, 0(t4); bne t3, t6, .Lteer_next\n" ++
  "  addi t2, t2, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lteer_marker_cmp\n" ++
  ".Lteer_final_no_code:\n" ++
  "  mv t2, s11; li t3, 20\n" ++
  ".Lteer_null_target_check:\n" ++
  "  beqz t3, .Lteer_refund_match\n" ++
  "  # Nonzero target + no codeChanges means a successful authorization left an\n" ++
  "  # identical delegation marker in place. Confirm that marker in pre-state\n" ++
  "  # before refunding AUTH_BASE; do not silently classify it as new code.\n" ++
  "  lbu t4, 0(t2); bnez t4, .Lteer_marker_match\n" ++
  "  addi t2, t2, 1; addi t3, t3, -1; j .Lteer_null_target_check\n" ++
  ".Lteer_marker_match:\n" ++
  "  # 5tmlt.3: AUTH_BASE is also refunded when the authority was delegated in a PRIOR\n" ++
  "  # BLOCK -- its delegation indicator is in the PRE-state, not this block's BAL. Spec\n" ++
  "  # set_delegation reads authority_code via get_code and refunds when is_valid_delegation.\n" ++
  "  # Resolve the authority's pre-state code; a 23-byte ef0100 marker => refund AUTH_BASE\n" ++
  "  # and skip the BAL (prior-tx-same-block) path below to avoid double-counting.\n" ++
  "  # code_at_header_state_root preserves callee-saved s-regs (s10 refund accumulator).\n" ++
  "  # SOUNDNESS gate: only trust pre-state code when it equals the LIVE authority code at\n" ++
  "  # set_delegation time -- i.e. single-tx blocks (no earlier tx in this block can have\n" ++
  "  # un-delegated the authority, which would make a pre-state marker a stale over-refund\n" ++
  "  # = under-charge = false-accept). Multi-tx falls to the BAL (prior-tx) path below.\n" ++
  "  la t0, svf_tx_count; ld t0, 0(t0); li t1, 1; bne t0, t1, .Lteer_prestate_no\n" ++
  "  la t0, bv_witness_state_ptr; ld a3, 0(t0); beqz a3, .Lteer_prestate_no\n" ++
  "  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, teer_authority\n" ++
  "  la t0, bv_witness_state_len; ld a4, 0(t0)\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  bnez a0, .Lteer_prestate_no\n" ++
  "  la t0, cahsr_code_length; ld t0, 0(t0); li t1, 23; bne t0, t1, .Lteer_prestate_no\n" ++
  "  la t0, svf_codes_ptr; ld t0, 0(t0); la t1, cahsr_code_offset; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  lbu t1, 0(t0); li t2, 0xef; bne t1, t2, .Lteer_prestate_no\n" ++
  "  lbu t1, 1(t0); li t2, 0x01; bne t1, t2, .Lteer_prestate_no\n" ++
  "  lbu t1, 2(t0); bnez t1, .Lteer_prestate_no\n" ++
  "  la t0, teer_predelegated_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  li t3, " ++ toString (amsterdamStateBytesPerAuthBase * amsterdamCostPerStateByte) ++ "\n" ++
  "  add s10, s10, t3; j .Lteer_next\n" ++
  ".Lteer_prestate_no:\n" ++
  "  # In a single-tx block, a final delegation marker was written by this auth,\n" ++
  "  # not by an earlier same-block tx, so it must not refund AUTH_BASE.\n" ++
  "  ld t0, 104(sp); li t1, 1; beq t0, t1, .Lteer_next\n" ++
  "  # The final delegation marker only proves the authority is non-empty after the block.\n" ++
  "  # AUTH_BASE is refunded only when a prior transaction already installed delegation code;\n" ++
  "  # this tx's own set_delegation write is not pre-existing authority_code.\n" ++
  "  la t0, teer_acct_ptr; ld a0, 0(t0); la t0, teer_acct_len; ld a1, 0(t0)\n" ++
  "  li a2, 5; la a3, c2nsf_off; la a4, c2nsf_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lteer_next\n" ++
  "  la t0, c2nsf_off; ld t1, 0(t0); la t2, teer_acct_ptr; ld t2, 0(t2); add t1, t2, t1\n" ++
  "  la t0, c2nsf_len; ld t2, 0(t0)\n" ++
  "  mv a0, t1; mv a1, t2; la a2, c2nsf_cnt\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lteer_next\n" ++
  "  la t0, c2nsf_cnt; ld t3, 0(t0); beqz t3, .Lteer_next\n" ++
  "  addi t3, t3, -1\n" ++
  "  la t0, c2nsf_off; ld t1, 0(t0); la t2, teer_acct_ptr; ld t2, 0(t2); add t1, t2, t1\n" ++
  "  la t0, c2nsf_len; ld t2, 0(t0)\n" ++
  "  mv a0, t1; mv a1, t2; mv a2, t3; la a3, c2nsf_toff; la a4, c2nsf_tlen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lteer_next\n" ++
  "  la t0, c2nsf_off; ld t1, 0(t0); la t2, teer_acct_ptr; ld t2, 0(t2); add t1, t2, t1\n" ++
  "  la t0, c2nsf_toff; ld t3, 0(t0); add a0, t1, t3\n" ++
  "  la t0, c2nsf_tlen; ld a1, 0(t0)\n" ++
  "  li a2, 0; addi a3, sp, 128\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lteer_next\n" ++
  "  ld t0, 128(sp); ld t1, 104(sp); bgeu t0, t1, .Lteer_next\n" ++
  ".Lteer_refund_match:\n" ++
  "  li t3, " ++ toString (amsterdamStateBytesPerAuthBase * amsterdamCostPerStateByte) ++ "\n" ++
  "  add s10, s10, t3; j .Lteer_next\n" ++

  ".Lteer_next:\n" ++
  "  addi s8, s8, 1; j .Lteer_loop\n" ++
  ".Lteer_same_authority_try:\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lteer_single_loop_setup\n" ++
  "  sd a0, 112(sp); sd a1, 120(sp); li s8, 0\n" ++
  "  la t0, teer_auth_chain; sd zero, 0(t0)  # previous same-authority target was nonzero\n" ++
  "  la t0, teer_auth_nonce; sd zero, 0(t0)  # same-tx AUTH_BASE refund count\n" ++
  "  la t0, teer_invalid_auth_count; sd zero, 0(t0)  # same-authority auths that do not advance nonce\n" ++
  ".Lteer_same_loop:\n" ++
  "  beq s8, s7, .Lteer_same_after_scan\n" ++
  "  ld a0, 112(sp); ld a1, 120(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lteer_single_loop_setup\n" ++
  "  sd a0, 112(sp); sub s9, a0, a2; sd a2, 136(sp)\n" ++
  "  mv a0, s9; ld a1, 136(sp); jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lteer_single_loop_setup\n" ++
  "  sd a0, 128(sp); sd a1, 144(sp)\n" ++
  "  ld a0, 128(sp); ld a1, 144(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lteer_single_loop_setup\n" ++
  "  sd a0, 128(sp); sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lteer_single_loop_setup\n" ++
  "  mv t1, a0; beqz t1, .Lteer_same_chain_ok; bne t1, s4, .Lteer_single_loop_setup\n" ++
  ".Lteer_same_chain_ok:\n" ++
  "  ld a0, 128(sp); ld a1, 144(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lteer_single_loop_setup\n" ++
  "  sd a0, 128(sp); li t2, 20; bne a2, t2, .Lteer_single_loop_setup\n" ++
  "  sub s11, a0, a2; sd s11, 152(sp)\n" ++
  "  beqz s8, .Lteer_same_authbase_counted\n" ++
  "  la t0, teer_auth_chain; ld t1, 0(t0); beqz t1, .Lteer_same_authbase_counted\n" ++
  "  la t0, teer_auth_nonce; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  ".Lteer_same_authbase_counted:\n" ++
  "  mv t0, s11; li t1, 20; li t2, 0\n" ++
  ".Lteer_same_target_or:\n" ++
  "  beqz t1, .Lteer_same_target_ready\n" ++
  "  lbu t3, 0(t0); or t2, t2, t3; addi t0, t0, 1; addi t1, t1, -1; j .Lteer_same_target_or\n" ++
  ".Lteer_same_target_ready:\n" ++
  "  snez t2, t2; bnez t2, .Lteer_same_target_store\n" ++
  "  la t0, teer_auth_nonce; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  ".Lteer_same_target_store:\n" ++
  "  la t0, teer_auth_chain; sd t2, 0(t0)\n" ++
  "  ld a0, 128(sp); ld a1, 144(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lteer_single_loop_setup\n" ++
  "  sd a0, 128(sp); sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lteer_single_loop_setup\n" ++
  "  mv t2, a0; beqz s8, .Lteer_same_first_nonce_check\n" ++
  "  la t0, teer_first_nonce; ld t1, 0(t0); add t1, t1, s8; bne t2, t1, .Lteer_same_nonce_mismatch\n" ++
  "  j .Lteer_same_nonce_ok\n" ++
  ".Lteer_same_first_nonce_check:\n" ++
  "  li t1, -1; beq t2, t1, .Lteer_single_loop_setup\n" ++
  "  la t0, teer_first_nonce; sd t2, 0(t0)\n" ++
  ".Lteer_same_nonce_ok:\n" ++
  "  bnez s8, .Lteer_same_recover_current\n" ++
  "  mv a0, s9; ld a1, 136(sp); la a2, teer_first_authority; la a3, teer_recover_scratch\n" ++
  "  jal ra, eip7702_authorization_recover_address\n" ++
  "  bnez a0, .Lteer_single_loop_setup\n" ++
  "  j .Lteer_same_next\n" ++
  ".Lteer_same_nonce_mismatch:\n" ++
  "  # execution-specs validate_authorization returns None when the signed nonce\n" ++
  "  # does not equal the authority live nonce. In the same-authority fast path,\n" ++
  "  # a repeated or stale nonce after an earlier valid authorization is exactly that\n" ++
  "  # case: set_delegation refunds the tuple's full AUTH_BASE state component.\n" ++
  "  # The NEW_ACCOUNT state and ACCOUNT_WRITE regular refunds are already counted\n" ++
  "  # per tuple by .Lteer_same_compute_refund; teer_auth_nonce carries the extra\n" ++
  "  # AUTH_BASE refunds. Recover and compare the authority so a different-authority\n" ++
  "  # mixed list still falls back to the generic per-auth loop.\n" ++
  "  mv a0, s9; ld a1, 136(sp); la a2, teer_authority; la a3, teer_recover_scratch\n" ++
  "  jal ra, eip7702_authorization_recover_address\n" ++
  "  bnez a0, .Lteer_same_next\n" ++
  "  la t0, teer_authority; la t1, teer_first_authority; li t2, 20\n" ++
  ".Lteer_same_nonce_mismatch_authority_cmp:\n" ++
  "  beqz t2, .Lteer_same_nonce_mismatch_same_authority\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lteer_single_loop_setup\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lteer_same_nonce_mismatch_authority_cmp\n" ++
  ".Lteer_same_nonce_mismatch_same_authority:\n" ++
  "  la t0, teer_invalid_auth_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  ".Lteer_same_recover_current:\n" ++
  "  mv a0, s9; ld a1, 136(sp); la a2, teer_authority; la a3, teer_recover_scratch\n" ++
  "  jal ra, eip7702_authorization_recover_address\n" ++
  "  bnez a0, .Lteer_single_loop_setup\n" ++
  "  la t0, teer_authority; la t1, teer_first_authority; li t2, 20\n" ++
  ".Lteer_same_authority_cmp:\n" ++
  "  beqz t2, .Lteer_same_next\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lteer_single_loop_setup\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lteer_same_authority_cmp\n" ++
  ".Lteer_same_next:\n" ++
  "  addi s8, s8, 1; j .Lteer_same_loop\n" ++
  ".Lteer_same_after_scan:\n" ++
  "  mv a0, s2; mv a1, s3; la a2, teer_first_authority; la a3, teer_acct_ptr; la a4, teer_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .Lteer_single_loop_setup\n" ++
  "  la t0, teer_acct_ptr; ld a0, 0(t0); la t0, teer_acct_len; ld a1, 0(t0); la a2, teer_finals\n" ++
  "  jal ra, bal_account_nonstorage_finals\n" ++
  "  bnez a0, .Lteer_single_loop_setup\n" ++
  "  la t0, teer_finals; ld t1, 40(t0); beqz t1, .Lteer_single_loop_setup\n" ++
  "  # Later execution can increment the same authority nonce again after the auth chain.\n" ++
  "  ld t2, 48(t0); la t0, teer_first_nonce; ld t1, 0(t0); add t1, t1, s7\n" ++
  "  la t0, teer_invalid_auth_count; ld t3, 0(t0); sub t1, t1, t3\n" ++
  "  bltu t2, t1, .Lteer_single_loop_setup\n" ++
  "  la t0, teer_finals; ld t1, 56(t0); beqz t1, .Lteer_same_final_no_code\n" ++
  "  ld t2, 72(t0); li t3, 23; bne t2, t3, .Lteer_single_loop_setup\n" ++
  "  ld t2, 64(t0); la t4, teer_acct_ptr; ld t4, 0(t4); add t2, t4, t2\n" ++
  "  lbu t3, 0(t2); li t4, 0xef; bne t3, t4, .Lteer_single_loop_setup\n" ++
  "  lbu t3, 1(t2); li t4, 0x01; bne t3, t4, .Lteer_single_loop_setup\n" ++
  "  lbu t3, 2(t2); bnez t3, .Lteer_single_loop_setup\n" ++
  "  addi t2, t2, 3; ld t4, 152(sp); li t5, 20\n" ++
  ".Lteer_same_final_marker_cmp:\n" ++
  "  beqz t5, .Lteer_same_compute_refund\n" ++
  "  lbu t3, 0(t2); lbu t6, 0(t4); bne t3, t6, .Lteer_single_loop_setup\n" ++
  "  addi t2, t2, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lteer_same_final_marker_cmp\n" ++
  ".Lteer_same_final_no_code:\n" ++
  "  la t0, teer_auth_chain; ld t1, 0(t0); bnez t1, .Lteer_single_loop_setup\n" ++
  ".Lteer_same_compute_refund:\n" ++
  "  la t0, teer_records_ptr; ld t0, 0(t0); beqz t0, .Lteer_single_loop_setup\n" ++
  "  la t1, bfa_index; ld t1, 0(t1); slli t2, t1, 4; slli t3, t1, 3; add t2, t2, t3; add t2, t0, t2\n" ++
  "  ld t3, 16(t2)\n" ++
  liAmsterdamNewAccountStateGas "t4" ++
  "  mul s10, s7, t4\n" ++
  "  li t6, 8000; mul t6, s7, t6\n" ++
  "  beqz t3, .Lteer_same_have_new_refund\n" ++
  "  sub s10, s10, t4\n" ++
  "  li t5, 8000; sub t6, t6, t5\n" ++
  ".Lteer_same_have_new_refund:\n" ++
  "  la t5, teer_regular_refund; sd t6, 0(t5)\n" ++
  "  la t5, teer_auth_nonce; ld t5, 0(t5)\n" ++
  "  li t4, " ++ toString (amsterdamStateBytesPerAuthBase * amsterdamCostPerStateByte) ++ "\n" ++
  "  mul t5, t5, t4\n" ++
  "  add s10, s10, t5\n" ++
  "  j .Lteer_done\n" ++
  ".Lteer_done:\n" ++
  "  mv a0, s10\n" ++
  "  la t0, teer_regular_refund; ld a1, 0(t0)\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 160\n" ++
  "  ret"


/-! ## block_verdict_tx_state_gas_array  (g8zeq.1.4.3)

    Fill a per-tx `tx_state_gas` array from the SSZ transactions section, the
    state-gas counterpart of the `bvgr_block_gas_increments` regular-gas array.
    Iterates the SSZ `List[Transaction]` offset table exactly like
    `block_verdict_tx_gas_limits` and calls `tx_intrinsic_state_gas` per tx, so
    `out[i] = tx_state_gas(tx i)` for `i in [0, count)`.

    Generic in its output pointer and a SEPARATE pass — it does NOT modify the
    wired `block_verdict_tx_gas_limits`. g8zeq.1.4.2 calls it with
    `bvgr_tx_state_gas` once the runtime arena is complete (count == tx_count),
    then feeds both arrays to `eip8037_block_gas_used`.

    Calling convention:
      a0 (input)  : SSZ transactions-section ptr (offset table + tx bodies)
      a1 (input)  : section byte length
      a2 (input)  : expected transaction count (arena consistency)
      a3 (input)  : u64 out array ptr (>= 8*count bytes)
      a4 (input)  : optional BAL ptr (0 disables existing-authority refunds)
      a5 (input)  : BAL length
      a6 (input)  : block chain id
      ra (input)  : return
      a0 (output) :
        0 : success (out[0..count) populated)
        1 : malformed transactions section / offset table
        2 : tx count disagrees with expected count
        3 : a per-tx tx_intrinsic_state_gas call failed -/
def blockVerdictTxStateGasArray_prog : Program :=
  [ .ADDI .x2 .x2 (-112 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .SD .x2 .x25 (80 : BitVec 12),
    .SD .x2 .x26 (88 : BitVec 12),
    .SD .x2 .x27 (96 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x24 .x14,
    .MV .x25 .x15,
    .MV .x26 .x16,
    .LI .x5 (4 : Word),
    .BLTU .x9 .x5 (216 : BitVec 13),
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_tx_state_gas_array + 96)),
    .ANDI .x5 .x10 (3 : BitVec 12),
    .BNE .x5 .x0 (200 : BitVec 13),
    .BLTU .x9 .x10 (196 : BitVec 13),
    .SRLI .x20 .x10 (2 : BitVec 6),
    .BNE .x20 .x18 (196 : BitVec 13),
    .BEQ .x20 .x0 (176 : BitVec 13),
    .MV .x21 .x0,
    .BEQ .x21 .x20 (168 : BitVec 13),
    .SLLI .x5 .x21 (2 : BitVec 6),
    .ADD .x10 .x8 .x5,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_tx_state_gas_array + 140)),
    .MV .x22 .x10,
    .SLLI .x5 .x20 (2 : BitVec 6),
    .BLTU .x22 .x5 (152 : BitVec 13),
    .BLTU .x9 .x22 (148 : BitVec 13),
    .ADDI .x5 .x21 (1 : BitVec 12),
    .BEQ .x5 .x20 (24 : BitVec 13),
    .SLLI .x6 .x5 (2 : BitVec 6),
    .ADD .x10 .x8 .x6,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_tx_state_gas_array + 176)),
    .MV .x23 .x10,
    .JAL .x0 (8 : BitVec 21),
    .MV .x23 .x9,
    .BLTU .x23 .x22 (112 : BitVec 13),
    .BLTU .x9 .x23 (108 : BitVec 13),
    .ADD .x10 .x8 .x22,
    .SUB .x11 .x23 .x22,
    .SLLI .x5 .x21 (3 : BitVec 6),
    .ADD .x12 .x19 .x5,
    .JAL .x1 (jalOff GuestAddrs.tx_intrinsic_state_gas (GuestAddrs.block_verdict_tx_state_gas_array + 216)),
    .BNE .x10 .x0 (100 : BitVec 13),
    .BEQ .x24 .x0 (64 : BitVec 13),
    .ADD .x10 .x8 .x22,
    .SUB .x11 .x23 .x22,
    .MV .x12 .x24,
    .MV .x13 .x25,
    .MV .x14 .x26,
    .ADDI .x15 .x21 (1 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_eip7702_existing_authority_refund (GuestAddrs.block_verdict_tx_state_gas_array + 252)),
    .SLLI .x5 .x21 (3 : BitVec 6),
    .ADD .x6 .x19 .x5,
    .LD .x7 .x6 (0 : BitVec 12),
    .BLTU .x7 .x10 (16 : BitVec 13),
    .SUB .x7 .x7 .x10,
    .SD .x6 .x7 (0 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .SD .x6 .x0 (0 : BitVec 12),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (-164 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (3 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .LD .x25 .x2 (80 : BitVec 12),
    .LD .x26 .x2 (88 : BitVec 12),
    .LD .x27 .x2 (96 : BitVec 12),
    .ADDI .x2 .x2 (112 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blockVerdictTxStateGasArray_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blockVerdictTxStateGasArray_relocs : RelocTable :=
  [ (24, .jal .x1 "bgv_u32le"),
    (35, .jal .x1 "bgv_u32le"),
    (44, .jal .x1 "bgv_u32le"),
    (54, .jal .x1 "tx_intrinsic_state_gas"),
    (63, .jal .x1 "tx_eip7702_existing_authority_refund") ]

def blockVerdictTxStateGasArrayFunction : String :=
  "block_verdict_tx_state_gas_array:\n" ++ emitProgramR blockVerdictTxStateGasArray_prog blockVerdictTxStateGasArray_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blockVerdictTxStateGasArray_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blockVerdictTxStateGasArrayFunction_eq_prog :
    blockVerdictTxStateGasArrayFunction = "block_verdict_tx_state_gas_array:\n" ++ emitProgramR blockVerdictTxStateGasArray_prog blockVerdictTxStateGasArray_relocs := rfl

#guard blockVerdictTxStateGasArrayFunction.startsWith "block_verdict_tx_state_gas_array:\n"
#guard blockVerdictTxStateGasArray_prog.length = 96
/-! ## block_verdict_eip7702_auth_nonstorage_effects

    EIP-7702 set_delegation increments each successfully authorized authority's
    nonce before message execution. That nonce change is not produced by CALL /
    CREATE execution, so append a nonce-only non-storage effect for every auth
    tuple whose recovered authority is present in the BAL and whose pre-state
    nonce matches the signed nonce. Code changes remain covered by the existing
    7702 code-comparator exception; this helper supplies only the balance/nonce
    effect used by the all-accounts non-storage comparators. -/
def eip7702AuthNonstorageEffectsFunction : String :=
  "eip7702_auth_nonstorage_effects:\n" ++
  "  addi sp, sp, -128\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx len\n" ++
  "  mv s2, a2                   # BAL ptr\n" ++
  "  mv s3, a3                   # BAL len\n" ++
  "  mv s4, a4                   # chain id\n" ++
  "  beqz s2, .Lteanse_done\n" ++
  "  mv a0, s0; mv a1, s1; la a2, teer_type; la a3, teer_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Lteanse_done\n" ++
  "  la t0, teer_type; ld t1, 0(t0); li t2, 4; bne t1, t2, .Lteanse_done\n" ++
  "  la t0, teer_inner_off; ld t1, 0(t0); bgtu t1, s1, .Lteanse_done; add s5, s0, t1; sub s6, s1, t1\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lteanse_done\n" ++
  "  mv s5, a0; mv s6, a1\n" ++
  rlpWalkFieldAsm ".Lteanse_done" 9 "s5" "s6" "s5" "s6" ++
  "  mv a0, s5; mv a1, s6; la a2, teer_auth_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lteanse_done\n" ++
  "  la t0, teer_auth_count; ld s7, 0(t0)\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lteanse_done\n" ++
  "  mv s5, a0; mv s6, a1; li s8, 0\n" ++
  ".Lteanse_loop:\n" ++
  "  beq s8, s7, .Lteanse_done\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lteanse_done\n" ++
  "  mv s5, a0; sub s9, a0, a2; mv s10, a2\n" ++
  "  mv a0, s9; mv a1, s10; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lteanse_next\n" ++
  "  sd a0, 104(sp); sd a1, 112(sp)\n" ++
  "  ld a0, 104(sp); ld a1, 112(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lteanse_next\n" ++
  "  sd a0, 104(sp); sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lteanse_next\n" ++
  "  mv t1, a0; beqz t1, .Lteanse_chain_ok; bne t1, s4, .Lteanse_next\n" ++
  ".Lteanse_chain_ok:\n" ++
  "  ld a0, 104(sp); ld a1, 112(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lteanse_next\n" ++
  "  sd a0, 104(sp); li t2, 20; bne a2, t2, .Lteanse_next\n" ++
  "  ld a0, 104(sp); ld a1, 112(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lteanse_next\n" ++
  "  sd a0, 104(sp); sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lteanse_next\n" ++
  "  mv s11, a0; li t2, -1; beq s11, t2, .Lteanse_next\n" ++
  "  mv a0, s9; mv a1, s10; la a2, teer_authority; la a3, teer_recover_scratch\n" ++
  "  jal ra, eip7702_authorization_recover_address\n" ++
  "  bnez a0, .Lteanse_next\n" ++
  "  mv a0, s2; mv a1, s3; la a2, teer_authority; la a3, teer_acct_ptr; la a4, teer_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .Lteanse_next\n" ++
  "  la t0, teer_acct_ptr; ld a0, 0(t0); la t0, teer_acct_len; ld a1, 0(t0); la a2, teer_finals\n" ++
  "  jal ra, bal_account_nonstorage_finals\n" ++
  "  bnez a0, .Lteanse_next\n" ++
  "  la t0, teer_finals; ld t1, 40(t0); beqz t1, .Lteanse_next\n" ++
  "  ld t1, 48(t0); addi t2, s11, 1; bltu t1, t2, .Lteanse_next\n" ++
  "  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, teer_authority; li a3, 20; la t0, bv_witness_state_ptr; ld a4, 0(t0); la t0, bv_witness_state_len; ld a5, 0(t0); la a6, teer_pre_acct\n" ++
  "  jal ra, account_at_header_state_root\n" ++
  "  beqz a0, .Lteanse_have_pre\n" ++
  "  li t0, 1; bne a0, t0, .Lteanse_next\n" ++
  "  bnez s11, .Lteanse_next\n" ++
  "  la t0, teer_pre_acct; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0); sd zero, 32(t0)\n" ++
  "  j .Lteanse_record\n" ++
  ".Lteanse_have_pre:\n" ++
  "  la t0, teer_pre_acct; ld t1, 0(t0); bne t1, s11, .Lteanse_next\n" ++
  ".Lteanse_record:\n" ++
  "  la a0, teer_authority; la a1, teer_pre_acct; addi a1, a1, 8; mv a2, a1; mv a3, s11; addi a4, s11, 1\n" ++
  "  jal ra, record_nonstorage_effect\n" ++
  "  la t0, teer_finals; ld t1, 56(t0); beqz t1, .Lteanse_next\n" ++
  "  ld t1, 72(t0); bnez t1, .Lteanse_next\n" ++
  "  la t0, exec_code_effect_next; ld t1, 0(t0); addi t2, t1, 48; li t3, " ++ toString execCodeEffectLogCap ++ "; bgtu t2, t3, .Lteanse_code_overflow\n" ++
  "  la t3, exec_code_effect_log; add t3, t3, t1\n" ++
  "  sd zero, 0(t3); sd zero, 8(t3); sd zero, 16(t3); sd zero, 24(t3)\n" ++
  "  la t4, teer_authority; mv t5, t3; li t6, 20\n" ++
  ".Lteanse_code_addr:\n" ++
  "  beqz t6, .Lteanse_code_addr_done\n" ++
  "  lbu a0, 0(t4); sb a0, 0(t5); addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lteanse_code_addr\n" ++
  ".Lteanse_code_addr_done:\n" ++
  "  li t4, 1; sd t4, 32(t3); sd zero, 40(t3)\n" ++
  "  la t0, exec_code_effect_count; ld t4, 0(t0); addi t4, t4, 1; sd t4, 0(t0)\n" ++
  "  la t0, exec_code_effect_next; sd t2, 0(t0); j .Lteanse_next\n" ++
  ".Lteanse_code_overflow:\n" ++
  "  la t0, exec_code_effect_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".Lteanse_next:\n" ++
  "  addi s8, s8, 1; j .Lteanse_loop\n" ++
  ".Lteanse_done:\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 128\n" ++
  "  ret"

def blockVerdictEip7702AuthNonstorageEffectsArray_prog : Program :=
  [ .ADDI .x2 .x2 (-88 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x24 .x15,
    .LI .x5 (4 : Word),
    .BLTU .x9 .x5 (140 : BitVec 13),
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_eip7702_auth_nonstorage_effects_array + 80)),
    .ANDI .x5 .x10 (3 : BitVec 12),
    .BNE .x5 .x0 (124 : BitVec 13),
    .BLTU .x9 .x10 (120 : BitVec 13),
    .SRLI .x21 .x10 (2 : BitVec 6),
    .BNE .x21 .x18 (112 : BitVec 13),
    .LI .x22 (0 : Word),
    .BEQ .x22 .x21 (104 : BitVec 13),
    .SLLI .x5 .x22 (2 : BitVec 6),
    .ADD .x10 .x8 .x5,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_eip7702_auth_nonstorage_effects_array + 120)),
    .MV .x23 .x10,
    .SLLI .x5 .x21 (2 : BitVec 6),
    .BLTU .x23 .x5 (72 : BitVec 13),
    .BLTU .x9 .x23 (68 : BitVec 13),
    .ADDI .x5 .x22 (1 : BitVec 12),
    .BEQ .x5 .x21 (20 : BitVec 13),
    .SLLI .x6 .x5 (2 : BitVec 6),
    .ADD .x10 .x8 .x6,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_eip7702_auth_nonstorage_effects_array + 156)),
    .JAL .x0 (8 : BitVec 21),
    .MV .x10 .x9,
    .BLTU .x10 .x23 (36 : BitVec 13),
    .BLTU .x9 .x10 (32 : BitVec 13),
    .ADD .x11 .x8 .x23,
    .SUB .x11 .x10 .x23,
    .ADD .x10 .x8 .x23,
    .MV .x12 .x19,
    .MV .x13 .x20,
    .MV .x14 .x24,
    .JAL .x1 (jalOff GuestAddrs.eip7702_auth_nonstorage_effects (GuestAddrs.block_verdict_eip7702_auth_nonstorage_effects_array + 200)),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .JAL .x0 (-100 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .ADDI .x2 .x2 (88 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blockVerdictEip7702AuthNonstorageEffectsArray_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blockVerdictEip7702AuthNonstorageEffectsArray_relocs : RelocTable :=
  [ (20, .jal .x1 "bgv_u32le"),
    (30, .jal .x1 "bgv_u32le"),
    (39, .jal .x1 "bgv_u32le"),
    (50, .jal .x1 "eip7702_auth_nonstorage_effects") ]

def blockVerdictEip7702AuthNonstorageEffectsArrayFunction : String :=
  "block_verdict_eip7702_auth_nonstorage_effects_array:\n" ++ emitProgramR blockVerdictEip7702AuthNonstorageEffectsArray_prog blockVerdictEip7702AuthNonstorageEffectsArray_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blockVerdictEip7702AuthNonstorageEffectsArray_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blockVerdictEip7702AuthNonstorageEffectsArrayFunction_eq_prog :
    blockVerdictEip7702AuthNonstorageEffectsArrayFunction = "block_verdict_eip7702_auth_nonstorage_effects_array:\n" ++ emitProgramR blockVerdictEip7702AuthNonstorageEffectsArray_prog blockVerdictEip7702AuthNonstorageEffectsArray_relocs := rfl

#guard blockVerdictEip7702AuthNonstorageEffectsArrayFunction.startsWith "block_verdict_eip7702_auth_nonstorage_effects_array:\n"
#guard blockVerdictEip7702AuthNonstorageEffectsArray_prog.length = 66
/-- `zisk_block_verdict_tx_state_gas_array`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : tx-section byte length
      bytes 16..24 : expected tx count
      bytes 24..   : SSZ transactions section (offset table + tx bodies)
    Output:
      bytes  0.. 8 : status
      bytes  8..   : tx_state_gas[i] (u64 LE), i in [0, count) -/
def ziskBlockVerdictTxStateGasArrayPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # tx-section len\n" ++
  "  ld a2, 16(a4)               # expected count\n" ++
  "  addi a0, a4, 24             # tx-section ptr\n" ++
  "  li a3, 0xa0010008           # out array (OUTPUT + 8)\n" ++
  "  li a4, 0; li a5, 0; li a6, 0 # no BAL refund in the standalone probe\n" ++
  "  jal ra, block_verdict_tx_state_gas_array\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbvtsg_pdone\n" ++
  blockVerdictTxStateGasArrayFunction ++ "\n" ++
  txEip7702ExistingAuthorityRefundFunction ++ "\n" ++
  txIntrinsicStateGasFunction ++ "\n" ++
  txExtractToAddressFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  eip8037TxStateGasFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  zkvmKeccak256SegmentsFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  secp256k1CurveCommonFunctions ++ "\n" ++
  secp256k1RecoverRFunction ++ "\n" ++
  txSigningHashFunction ++ "\n" ++
  txPubkeyEcrecoverStageMaterialFunction ++ "\n" ++
  secp256k1RecoverPubkeyStagedFunction ++ "\n" ++
  addressFromPubkeyFunction ++ "\n" ++
  eip7702AuthorizationExtractSignatureFunction ++ "\n" ++
  eip7702AuthorizationSigningHashFunction ++ "\n" ++
  eip7702AuthorizationRecoverAddressFunction ++ "\n" ++
  balFindAccountByAddressFunction ++ "\n" ++
  balAccountNonstorageFinalsFunction ++ "\n" ++
  bgvU32leFunction ++ "\n" ++
  ".Lbvtsg_pdone:"

def ziskBlockVerdictTxStateGasArrayDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "tea_type:\n  .zero 8\n" ++
  "tea_inner_off:\n  .zero 8\n" ++
  "tea_field_off:\n  .zero 8\n" ++
  "tea_field_len:\n  .zero 8\n" ++
  "tis_to_buf:\n  .zero 32\n" ++
  "tis_is_creation:\n  .zero 8\n" ++
  "tis_type:\n  .zero 8\n" ++
  "tis_inner_off:\n  .zero 8\n" ++
  "tis_auth_count:\n  .zero 8\n" ++
  "teer_type:\n  .zero 8\n" ++
  "teer_inner_off:\n  .zero 8\n" ++
  "teer_auth_count:\n  .zero 8\n" ++
  "teer_regular_refund:\n  .zero 8\n" ++
  "teer_predelegated_count:\n  .zero 8\n" ++
  "teer_existing_count:\n  .zero 8\n" ++
  "teer_records_ptr:\n  .zero 8\n" ++
  "teer_tuple_off:\n  .zero 8\n" ++
  "teer_tuple_len:\n  .zero 8\n" ++
  "teer_target_off:\n  .zero 8\n" ++
  "teer_target_len:\n  .zero 8\n" ++
  "teer_auth_chain:\n  .zero 8\n" ++
  "teer_auth_nonce:\n  .zero 8\n" ++
  "teer_invalid_auth_count:\n  .zero 8\n" ++
  "teer_first_nonce:\n  .zero 8\n" ++
  "teer_authority:\n  .zero 24\n" ++
  "teer_first_authority:\n  .zero 24\n" ++
  ".balign 8\n" ++
  "teer_recover_scratch:\n  .zero 360\n" ++
  "teer_acct_ptr:\n  .zero 8\n" ++
  "teer_acct_len:\n  .zero 8\n" ++
  "teer_finals:\n  .zero 88\n" ++
  "teer_pre_acct:\n  .zero 104\n" ++
  ziskEip7702AuthorizationRecoverAddressDataSection ++ "\n" ++
  "c2nsf_off:\n  .zero 8\n" ++
  "c2nsf_len:\n  .zero 8\n" ++
  "c2nsf_cnt:\n  .zero 8\n" ++
  "c2nsf_toff:\n  .zero 8\n" ++
  "c2nsf_tlen:\n  .zero 8\n" ++
  "c2nsf_coff:\n  .zero 8\n" ++
  "c2nsf_clen:\n  .zero 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  "bfa_cnt:\n  .zero 8\n" ++
  "bfa_index:\n  .zero 8\n" ++
  "bfa_aoff:\n  .zero 8\n" ++
  "bfa_alen:\n  .zero 8\n" ++
  "bfa_doff:\n  .zero 8\n" ++
  "bfa_dlen:\n  .zero 8\n" ++
  "teer_data_end:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "teer_success_count:\n  .zero 8\n" ++
  "teer_success_table:\n  .zero " ++ toString (teerSuccessfulAuthCapacity * 32) ++ "\n"

def ziskBlockVerdictTxStateGasArrayProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockVerdictTxStateGasArrayPrologue
  dataAsm     := ziskBlockVerdictTxStateGasArrayDataSection
}

end EvmAsm.Codegen
