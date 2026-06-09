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
      ra (input)  : return
      a0 (output) :
        0 : success (out[0..count) populated)
        1 : malformed transactions section / offset table
        2 : tx count disagrees with expected count
        3 : a per-tx tx_intrinsic_state_gas call failed -/
def blockVerdictTxStateGasArrayFunction : String :=
  "block_verdict_tx_state_gas_array:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # tx-section ptr\n" ++
  "  mv s1, a1                   # tx-section len\n" ++
  "  mv s2, a2                   # expected count\n" ++
  "  mv s3, a3                   # out array\n" ++
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
  "  addi sp, sp, 80\n" ++
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
  "  jal ra, block_verdict_tx_state_gas_array\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbvtsg_pdone\n" ++
  blockVerdictTxStateGasArrayFunction ++ "\n" ++
  txIntrinsicStateGasFunction ++ "\n" ++
  txExtractToAddressFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  eip8037TxStateGasFunction ++ "\n" ++
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
  "tis_auth_count:\n  .zero 8"

def ziskBlockVerdictTxStateGasArrayProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockVerdictTxStateGasArrayPrologue
  dataAsm     := ziskBlockVerdictTxStateGasArrayDataSection
}

end EvmAsm.Codegen
