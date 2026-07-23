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
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasReplay

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

/-! ## zisk_block_verdict_tx_state_gas_array

    Focused probe for the linked tx state-gas array routines. -/
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
  balAccountNonceBeforeIndexFunction ++ "\n" ++
  txEip7702ExistingAuthorityRefundFunction ++ "\n" ++
  txEip7702ExistingAuthorityRefundWithSenderNonceFunction ++ "\n" ++
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
  "teer_recipient_ptr:\n  .zero 8\n" ++
  "teer_recipient_len:\n  .zero 8\n" ++
  "teer_value_nonzero:\n  .zero 8\n" ++
  "teer_prior_count:\n  .zero 8\n" ++
  "teer_prior_set_flag:\n  .zero 8\n" ++
  "teer_acct_absent:\n  .zero 8\n" ++
  "teer_rolled_back:\n  .zero 8\n" ++
  "teer_wouldbe_state:\n  .zero 8\n" ++
  "teer_wouldbe_regular:\n  .zero 8\n" ++
  "teer_first_nonce:\n  .zero 8\n" ++
  -- `nonstorage_effect_latest_{balance,nonce}` compare the padded 32-byte
  -- effect-log key word-for-word.  The recovered address occupies bytes 0..19;
  -- retain an explicit zero tail rather than reading into the next scratch cell.
  "teer_authority:\n  .zero 32\n" ++
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
