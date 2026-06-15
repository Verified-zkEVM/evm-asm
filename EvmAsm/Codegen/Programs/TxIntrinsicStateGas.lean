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
    - rlp_list_nth_item / rlp_list_count_items -> EIP-7702 authorization_list count
    - eip8037_tx_state_gas   (g8zeq.1.3) -> the canonical settlement (intrinsic + 0 - 0)

  It is intentionally standalone and UNWIRED: g8zeq.1.4.3 will call it per-tx to
  fill the `bvgr_tx_state_gas` array in a separate arena pass, WITHOUT modifying
  the wired `block_verdict_tx_gas_limits` (zero regression risk).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Codegen.Programs.IntrinsicGas
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.BlockVerdictBalFindAccount
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinals
import EvmAsm.Codegen.Programs.Eip7702Authority

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
    tis_inner_off, tis_auth_off, tis_auth_len, tis_auth_count, plus the tea_*
    slots consumed internally by tx_extract_to_address. -/
def txIntrinsicStateGasFunction : String :=
  "tx_intrinsic_state_gas:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
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
  "  li a2, 9; la a3, tis_auth_off; la a4, tis_auth_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Ltisg_fail2\n" ++
  "  la t0, tis_inner_off; ld t1, 0(t0); add t1, s0, t1   # inner RLP ptr\n" ++
  "  la t0, tis_auth_off; ld t2, 0(t0); add a0, t1, t2    # auth_list ptr\n" ++
  "  la t0, tis_auth_len; ld a1, 0(t0); la a2, tis_auth_count\n" ++
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
  "  addi sp, sp, 48\n" ++
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
  rlpListNthItemFunction ++ "\n" ++
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
  "tis_auth_off:\n  .zero 8\n" ++
  "tis_auth_len:\n  .zero 8\n" ++
  "tis_auth_count:\n  .zero 8"

def ziskTxIntrinsicStateGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxIntrinsicStateGasPrologue
  dataAsm     := ziskTxIntrinsicStateGasDataSection
}


/-! ## tx_eip7702_existing_authority_refund

    Bridge for the EIP-7702 existing-authority state-gas refund. For type-4
    authorizations that pass basic chain/nonce/target parsing, this recovers the
    authority address, finds the authority's BAL AccountChanges row, and only
    subtracts the refund when BAL records the matching 0xef0100||target
    delegation marker. Callers pass BAL ptr 0 to keep the older intrinsic-only
    behavior.

    Calling convention:
      a0 = encoded tx ptr, a1 = encoded tx len
      a2 = BAL ptr gate (0 disables), a3 = BAL length
      a4 = block chain id
      a0 output = refund amount (u64). Parse failures for an individual
                  authorization conservatively contribute zero. -/
def txEip7702ExistingAuthorityRefundFunction : String :=
  "tx_eip7702_existing_authority_refund:\n" ++
  "  addi sp, sp, -104\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx len\n" ++
  "  mv s2, a2                   # BAL ptr\n" ++
  "  mv s3, a3                   # reserved\n" ++
  "  mv s4, a4                   # chain id\n" ++
  "  li s10, 0                   # accumulated refund\n" ++
  "  beqz s2, .Lteer_done\n" ++
  "  mv a0, s0; mv a1, s1; la a2, teer_type; la a3, teer_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Lteer_done\n" ++
  "  la t0, teer_type; ld t1, 0(t0); li t2, 4; bne t1, t2, .Lteer_done\n" ++
  "  la t0, teer_inner_off; ld t1, 0(t0); add s5, s0, t1; sub s6, s1, t1\n" ++
  "  mv a0, s5; mv a1, s6; li a2, 9; la a3, teer_auth_off; la a4, teer_auth_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lteer_done\n" ++
  "  la t0, teer_auth_off; ld t1, 0(t0); add s5, s5, t1     # auth list ptr\n" ++
  "  la t0, teer_auth_len; ld s6, 0(t0)                     # auth list len\n" ++
  "  mv a0, s5; mv a1, s6; la a2, teer_auth_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lteer_done\n" ++
  "  la t0, teer_auth_count; ld s7, 0(t0)\n" ++
  "  li s8, 0\n" ++
  ".Lteer_loop:\n" ++
  "  beq s8, s7, .Lteer_done\n" ++
  "  mv a0, s5; mv a1, s6; mv a2, s8; la a3, teer_tuple_off; la a4, teer_tuple_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lteer_next\n" ++
  "  la t0, teer_tuple_off; ld t1, 0(t0); add s9, s5, t1\n" ++
  "  la t0, teer_tuple_len; ld t2, 0(t0)\n" ++
  "  mv a0, s9; mv a1, t2; li a2, 0; la a3, teer_auth_chain\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lteer_next\n" ++
  "  la t0, teer_auth_chain; ld t1, 0(t0); beqz t1, .Lteer_chain_ok; bne t1, s4, .Lteer_next\n" ++
  ".Lteer_chain_ok:\n" ++
  "  la t0, teer_tuple_len; ld t2, 0(t0)\n" ++
  "  mv a0, s9; mv a1, t2; li a2, 2; la a3, teer_auth_nonce\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lteer_next\n" ++
  "  la t0, teer_auth_nonce; ld t1, 0(t0); li t2, -1; beq t1, t2, .Lteer_next\n" ++
  "  la t0, teer_tuple_len; ld a1, 0(t0); mv a0, s9; li a2, 1; la a3, teer_target_off; la a4, teer_target_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lteer_next\n" ++
  "  la t0, teer_target_len; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lteer_next\n" ++
  "  la t0, teer_target_off; ld t0, 0(t0); add s11, s9, t0\n" ++
  "  la t0, teer_tuple_len; ld a1, 0(t0); mv a0, s9; la a2, teer_authority; la a3, teer_recover_scratch\n" ++
  "  jal ra, eip7702_authorization_recover_address\n" ++
  "  bnez a0, .Lteer_next\n" ++
  "  mv a0, s2; mv a1, s3; la a2, teer_authority; la a3, teer_acct_ptr; la a4, teer_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .Lteer_next\n" ++
  "  la t0, teer_acct_ptr; ld a0, 0(t0); la t0, teer_acct_len; ld a1, 0(t0); la a2, teer_finals\n" ++
  "  jal ra, bal_account_nonstorage_finals\n" ++
  "  bnez a0, .Lteer_next\n" ++
  "  la t0, teer_finals; ld t1, 56(t0); beqz t1, .Lteer_next\n" ++
  "  ld t2, 72(t0); li t3, 23; bne t2, t3, .Lteer_next\n" ++
  "  ld t2, 64(t0); la t4, teer_acct_ptr; ld t4, 0(t4); add t2, t4, t2\n" ++
  "  lbu t3, 0(t2); li t4, 0xef; bne t3, t4, .Lteer_next\n" ++
  "  lbu t3, 1(t2); li t4, 0x01; bne t3, t4, .Lteer_next\n" ++
  "  lbu t3, 2(t2); bnez t3, .Lteer_next\n" ++
  "  addi t2, t2, 3; mv t4, s11; li t5, 20\n" ++
  ".Lteer_marker_cmp:\n" ++
  "  beqz t5, .Lteer_refund_match\n" ++
  "  lbu t3, 0(t2); lbu t6, 0(t4); bne t3, t6, .Lteer_next\n" ++
  "  addi t2, t2, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lteer_marker_cmp\n" ++
  ".Lteer_refund_match:\n" ++
  liAmsterdamNewAccountStateGas "t3" ++
  "  add s10, s10, t3; j .Lteer_next\n" ++

  ".Lteer_next:\n" ++
  "  addi s8, s8, 1; j .Lteer_loop\n" ++
  ".Lteer_done:\n" ++
  "  mv a0, s10\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 104\n" ++
  "  ret"


/-! ## block_verdict_receipt_gas_eip8037_adjust

    Add EIP-8037 state-gas components to per-tx receipt gas increments. The
    runtime arena records regular execution gas; Amsterdam receipts use the
    transaction's total gas accounting, so type-4 authorizations also need their
    regular auth-list intrinsic charge and every tx needs intrinsic state gas
    folded into the receipt increment. Executed state gas is part of the block
    gas accounting, not the receipt cumulative gas. Decode failures are non-gating:
    the helper leaves that tx's receipt gas at the runtime value. -/
def blockVerdictReceiptGasEip8037AdjustFunction : String :=
  "block_verdict_receipt_gas_eip8037_adjust:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # tx list ptr\n" ++
  "  mv s1, a1                   # tx list len\n" ++
  "  mv s2, a2                   # tx count\n" ++
  "  mv s3, a3                   # receipt gas increments\n" ++
  "  mv s4, a4                   # intrinsic state gas array\n" ++
  "  mv s5, a5                   # reserved/ignored: executed state gas is not receipt gas\n" ++
  "  beqz s2, .Lbvrga_done\n" ++
  "  li t0, 4; bltu s1, t0, .Lbvrga_done\n" ++
  "  slli s7, s2, 2             # minimum item offset = tx_count * 4\n" ++
  "  bgtu s7, s1, .Lbvrga_done\n" ++
  "  li s6, 0\n" ++
  ".Lbvrga_loop:\n" ++
  "  beq s6, s2, .Lbvrga_done\n" ++
  "  slli t0, s6, 2; add a0, s0, t0; jal ra, bgv_u32le\n" ++
  "  mv s8, a0\n" ++
  "  bltu s8, s7, .Lbvrga_next\n" ++
  "  bgtu s8, s1, .Lbvrga_next\n" ++
  "  addi t0, s6, 1; beq t0, s2, .Lbvrga_last\n" ++
  "  slli t1, t0, 2; add a0, s0, t1; jal ra, bgv_u32le\n" ++
  "  mv s9, a0; j .Lbvrga_have_next\n" ++
  ".Lbvrga_last:\n" ++
  "  mv s9, s1\n" ++
  ".Lbvrga_have_next:\n" ++
  "  bltu s9, s8, .Lbvrga_next\n" ++
  "  bgtu s9, s1, .Lbvrga_next\n" ++
  "  add s10, s0, s8\n" ++
  "  sub s11, s9, s8\n" ++
  "  slli t0, s6, 3\n" ++
  "  add t1, s3, t0; ld t2, 0(t1)\n" ++
  "  beqz s4, .Lbvrga_after_intr_state\n" ++
  "  add t3, s4, t0; ld t3, 0(t3); bgeu t2, t3, .Lbvrga_store_next\n" ++
  "  add t2, t2, t3\n" ++
  ".Lbvrga_after_intr_state:\n" ++
  "  sd t2, 0(t1)\n" ++
  "  mv a0, s10; mv a1, s11; la a2, bvrga_type; la a3, bvrga_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Lbvrga_next\n" ++
  "  la t0, bvrga_type; ld t0, 0(t0); li t1, 4; bne t0, t1, .Lbvrga_next\n" ++
  "  la t0, bvrga_inner_off; ld t0, 0(t0); bgtu t0, s11, .Lbvrga_next\n" ++
  "  add a0, s10, t0; sub a1, s11, t0; li a2, 9; la a3, bvrga_auth_off; la a4, bvrga_auth_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbvrga_next\n" ++
  "  la t0, bvrga_inner_off; ld t1, 0(t0); add t1, s10, t1\n" ++
  "  la t0, bvrga_auth_off; ld t2, 0(t0); add a0, t1, t2\n" ++
  "  la t0, bvrga_auth_len; ld a1, 0(t0); la a2, bvrga_auth_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbvrga_next\n" ++
  "  la t0, bvrga_auth_count; ld t0, 0(t0); li t1, 7500; mul t0, t0, t1\n" ++
  "  slli t1, s6, 3; add t2, s3, t1; ld t3, 0(t2); add t3, t3, t0; sd t3, 0(t2)\n" ++
  "  j .Lbvrga_next\n" ++
  ".Lbvrga_store_next:\n" ++
  "  sd t2, 0(t1)\n" ++
  ".Lbvrga_next:\n" ++
  "  addi s6, s6, 1; j .Lbvrga_loop\n" ++
  ".Lbvrga_done:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
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
def blockVerdictTxStateGasArrayFunction : String :=
  "block_verdict_tx_state_gas_array:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # tx-section ptr\n" ++
  "  mv s1, a1                   # tx-section len\n" ++
  "  mv s2, a2                   # expected count\n" ++
  "  mv s3, a3                   # out array\n" ++
  "  mv s8, a4                   # optional BAL ptr\n" ++
  "  mv s9, a5                   # BAL len\n" ++
  "  mv s10, a6                  # chain id\n" ++
  "  li t0, 4; bltu s1, t0, .Lbvtsg_malformed\n" ++
  "  mv a0, s0; jal ra, bgv_u32le             # first offset = 4 * tx_count\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbvtsg_malformed\n" ++
  "  bgtu a0, s1, .Lbvtsg_malformed\n" ++
  "  srli s4, a0, 2              # tx_count\n" ++
  "  bne s4, s2, .Lbvtsg_mismatch\n" ++
  "  beqz s4, .Lbvtsg_ok\n" ++
  "  mv s5, zero                 # index\n" ++
  ".Lbvtsg_loop:\n" ++
  "  beq s5, s4, .Lbvtsg_ok\n" ++
  "  slli t0, s5, 2; add a0, s0, t0; jal ra, bgv_u32le; mv s6, a0   # cur offset\n" ++
  "  slli t0, s4, 2; bltu s6, t0, .Lbvtsg_malformed                 # >= offset-table end\n" ++
  "  bgtu s6, s1, .Lbvtsg_malformed\n" ++
  "  addi t0, s5, 1; beq t0, s4, .Lbvtsg_last\n" ++
  "  slli t1, t0, 2; add a0, s0, t1; jal ra, bgv_u32le; mv s7, a0   # next offset\n" ++
  "  j .Lbvtsg_have\n" ++
  ".Lbvtsg_last:\n" ++
  "  mv s7, s1                   # final tx ends at section end\n" ++
  ".Lbvtsg_have:\n" ++
  "  bltu s7, s6, .Lbvtsg_malformed\n" ++
  "  bgtu s7, s1, .Lbvtsg_malformed\n" ++
  "  add a0, s0, s6              # tx ptr\n" ++
  "  sub a1, s7, s6             # tx len\n" ++
  "  slli t0, s5, 3; add a2, s3, t0   # &out[i]\n" ++
  "  jal ra, tx_intrinsic_state_gas\n" ++
  "  bnez a0, .Lbvtsg_tx_fail\n" ++
  "  beqz s8, .Lbvtsg_after_refund\n" ++
  "  add a0, s0, s6; sub a1, s7, s6; mv a2, s8; mv a3, s9; mv a4, s10\n" ++
  "  jal ra, tx_eip7702_existing_authority_refund\n" ++
  "  slli t0, s5, 3; add t1, s3, t0; ld t2, 0(t1); bgtu a0, t2, .Lbvtsg_refund_clamp\n" ++
  "  sub t2, t2, a0; sd t2, 0(t1); j .Lbvtsg_after_refund\n" ++
  ".Lbvtsg_refund_clamp:\n" ++
  "  sd zero, 0(t1)\n" ++
  ".Lbvtsg_after_refund:\n" ++
  "  addi s5, s5, 1; j .Lbvtsg_loop\n" ++
  ".Lbvtsg_ok:\n" ++
  "  li a0, 0; j .Lbvtsg_ret\n" ++
  ".Lbvtsg_malformed:\n" ++
  "  li a0, 1; j .Lbvtsg_ret\n" ++
  ".Lbvtsg_mismatch:\n" ++
  "  li a0, 2; j .Lbvtsg_ret\n" ++
  ".Lbvtsg_tx_fail:\n" ++
  "  li a0, 3\n" ++
  ".Lbvtsg_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

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
  "tis_auth_off:\n  .zero 8\n" ++
  "tis_auth_len:\n  .zero 8\n" ++
  "tis_auth_count:\n  .zero 8\n" ++
  "teer_type:\n  .zero 8\n" ++
  "teer_inner_off:\n  .zero 8\n" ++
  "teer_auth_off:\n  .zero 8\n" ++
  "teer_auth_len:\n  .zero 8\n" ++
  "teer_auth_count:\n  .zero 8\n" ++
  "teer_tuple_off:\n  .zero 8\n" ++
  "teer_tuple_len:\n  .zero 8\n" ++
  "teer_target_off:\n  .zero 8\n" ++
  "teer_target_len:\n  .zero 8\n" ++
  "teer_auth_chain:\n  .zero 8\n" ++
  "teer_auth_nonce:\n  .zero 8\n" ++
  "teer_authority:\n  .zero 24\n" ++
  ".balign 8\n" ++
  "teer_recover_scratch:\n  .zero 360\n" ++
  "teer_acct_ptr:\n  .zero 8\n" ++
  "teer_acct_len:\n  .zero 8\n" ++
  "teer_finals:\n  .zero 88\n" ++
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
  "bfa_aoff:\n  .zero 8\n" ++
  "bfa_alen:\n  .zero 8\n" ++
  "bfa_doff:\n  .zero 8\n" ++
  "bfa_dlen:\n  .zero 8\n" ++
  "teer_data_end:\n  .zero 8"

def ziskBlockVerdictTxStateGasArrayProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockVerdictTxStateGasArrayPrologue
  dataAsm     := ziskBlockVerdictTxStateGasArrayDataSection
}

end EvmAsm.Codegen
