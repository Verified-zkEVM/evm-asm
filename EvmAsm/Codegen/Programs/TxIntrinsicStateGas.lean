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
def txIntrinsicStateGas_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.tis_to_buf (GuestAddrs.tx_intrinsic_state_gas + 56)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tis_to_buf (GuestAddrs.tx_intrinsic_state_gas + 56)),
    .AUIPC .x13 (laHi GuestAddrs.tis_is_creation (GuestAddrs.tx_intrinsic_state_gas + 64)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tis_is_creation (GuestAddrs.tx_intrinsic_state_gas + 64)),
    .JAL .x1 (jalOff GuestAddrs.tx_extract_to_address (GuestAddrs.tx_intrinsic_state_gas + 72)),
    .BNE .x10 .x0 (80 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.tis_type (GuestAddrs.tx_intrinsic_state_gas + 88)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tis_type (GuestAddrs.tx_intrinsic_state_gas + 88)),
    .AUIPC .x13 (laHi GuestAddrs.tis_inner_off (GuestAddrs.tx_intrinsic_state_gas + 96)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tis_inner_off (GuestAddrs.tx_intrinsic_state_gas + 96)),
    .JAL .x1 (jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.tx_intrinsic_state_gas + 104)),
    .BNE .x10 .x0 (60 : BitVec 13),
    .LI .x20 (0 : Word),
    .MV .x10 .x20,
    .LI .x11 (0 : Word),
    .LI .x12 (0 : Word),
    .LI .x13 (0 : Word),
    .AUIPC .x5 (laHi GuestAddrs.tis_is_creation (GuestAddrs.tx_intrinsic_state_gas + 132)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tis_is_creation (GuestAddrs.tx_intrinsic_state_gas + 132)),
    .LD .x14 .x5 (0 : BitVec 12),
    .MV .x15 .x18,
    .JAL .x1 (jalOff GuestAddrs.eip8037_tx_state_gas (GuestAddrs.tx_intrinsic_state_gas + 148)),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (1 : Word),
    .SD .x18 .x0 (0 : BitVec 12),
    .JAL .x0 (12 : BitVec 21),
    .LI .x10 (2 : Word),
    .SD .x18 .x0 (0 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txIntrinsicStateGas_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txIntrinsicStateGas_relocs : RelocTable :=
  [ (14, .la .x12 "tis_to_buf"),
    (16, .la .x13 "tis_is_creation"),
    (18, .jal .x1 "tx_extract_to_address"),
    (22, .la .x12 "tis_type"),
    (24, .la .x13 "tis_inner_off"),
    (26, .jal .x1 "tx_type_dispatch"),
    (33, .la .x5 "tis_is_creation"),
    (37, .jal .x1 "eip8037_tx_state_gas") ]

def txIntrinsicStateGasFunction : String :=
  "tx_intrinsic_state_gas:\n" ++ emitProgramR txIntrinsicStateGas_prog txIntrinsicStateGas_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txIntrinsicStateGas_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txIntrinsicStateGasFunction_eq_prog :
    txIntrinsicStateGasFunction = "tx_intrinsic_state_gas:\n" ++ emitProgramR txIntrinsicStateGas_prog txIntrinsicStateGas_relocs := rfl

#guard txIntrinsicStateGasFunction.startsWith "tx_intrinsic_state_gas:\n"
#guard txIntrinsicStateGas_prog.length = 54
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

/-! ## tx_eip7702_existing_authority_refund

    Bridge for the EIP-7702 existing-authority state-gas refund. For type-4
    authorizations that pass basic chain/nonce/target parsing, this recovers the
    authority address, finds the authority's BAL AccountChanges row, and subtracts
    the NEW_ACCOUNT refund when the authority existed in pre-state and BAL shows
    the authorization nonce increment. It separately subtracts AUTH_BASE only when
    the authority code was already a delegation marker. Callers pass BAL ptr 0 to
    keep the older intrinsic-only behavior.

    v0.6.0 (tests-zkevm@v0.6.0, EIP-2780/7702 rework): this helper now
    computes the EXACT set_delegation CHARGES (the v0.5.0 worst-case
    refund model is gone with the intrinsic worst-case charges):

      state  charge = per valid auth:
                        NEW_ACCOUNT iff the authority leaf did not
                          pre-exist (block is_insert record) and no
                          earlier auth this tx materialized it
                      + AUTH_BASE iff a net-new delegation indicator is
                          written (non-NULL target, no prior non-NULL
                          set this tx, not delegated in pre-state)
      regular charge = ACCOUNT_WRITE per valid auth whose authority is
                       written for the first time this tx (not the
                       sender, not the value-receiving recipient, no
                       prior auth for it).

    Calling convention:
      a0 = encoded tx ptr, a1 = encoded tx len
      a2 = BAL ptr gate (0 disables), a3 = BAL length
      a4 = block chain id
      a5 = current tx block_access_index (tx index + 1)
      a0 output = state CHARGE amount (u64). Parse failures for an
                  individual authorization contribute zero.
      a1 output = regular CHARGE amount (u64), applied to the top-frame
                  gas before dispatch. -/
def txEip7702ExistingAuthorityRefund_prog : Program :=
  [ .ADDI .x2 .x2 (-160 : BitVec 12),
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
    .SD .x2 .x15 (104 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .LI .x26 (0 : Word),
    .AUIPC .x5 (laHi GuestAddrs.teer_regular_refund (GuestAddrs.tx_eip7702_existing_authority_refund + 84)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_regular_refund (GuestAddrs.tx_eip7702_existing_authority_refund + 84)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_success_count (GuestAddrs.tx_eip7702_existing_authority_refund + 96)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_success_count (GuestAddrs.tx_eip7702_existing_authority_refund + 96)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_predelegated_count (GuestAddrs.tx_eip7702_existing_authority_refund + 108)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_predelegated_count (GuestAddrs.tx_eip7702_existing_authority_refund + 108)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_rolled_back (GuestAddrs.tx_eip7702_existing_authority_refund + 120)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_rolled_back (GuestAddrs.tx_eip7702_existing_authority_refund + 120)),
    .SD .x5 .x0 (0 : BitVec 12),
    .BEQ .x18 .x0 (2724 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.teer_type (GuestAddrs.tx_eip7702_existing_authority_refund + 144)),
    .ADDI .x12 .x12 (laLo GuestAddrs.teer_type (GuestAddrs.tx_eip7702_existing_authority_refund + 144)),
    .AUIPC .x13 (laHi GuestAddrs.teer_inner_off (GuestAddrs.tx_eip7702_existing_authority_refund + 152)),
    .ADDI .x13 .x13 (laLo GuestAddrs.teer_inner_off (GuestAddrs.tx_eip7702_existing_authority_refund + 152)),
    .JAL .x1 (jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.tx_eip7702_existing_authority_refund + 160)),
    .BNE .x10 .x0 (2692 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.teer_type (GuestAddrs.tx_eip7702_existing_authority_refund + 168)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_type (GuestAddrs.tx_eip7702_existing_authority_refund + 168)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (4 : Word),
    .BNE .x6 .x7 (2672 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.teer_inner_off (GuestAddrs.tx_eip7702_existing_authority_refund + 188)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_inner_off (GuestAddrs.tx_eip7702_existing_authority_refund + 188)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x21 .x8 .x6,
    .SUB .x22 .x9 .x6,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_eip7702_existing_authority_refund + 216)),
    .BNE .x12 .x0 (2636 : BitVec 13),
    .MV .x24 .x10,
    .MV .x25 .x11,
    .MV .x10 .x24,
    .MV .x11 .x25,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 240)),
    .BNE .x11 .x0 (2612 : BitVec 13),
    .MV .x24 .x10,
    .MV .x10 .x24,
    .MV .x11 .x25,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 260)),
    .BNE .x11 .x0 (2592 : BitVec 13),
    .MV .x24 .x10,
    .MV .x10 .x24,
    .MV .x11 .x25,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 280)),
    .BNE .x11 .x0 (2572 : BitVec 13),
    .MV .x24 .x10,
    .MV .x10 .x24,
    .MV .x11 .x25,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 300)),
    .BNE .x11 .x0 (2552 : BitVec 13),
    .MV .x24 .x10,
    .MV .x10 .x24,
    .MV .x11 .x25,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 320)),
    .BNE .x11 .x0 (2532 : BitVec 13),
    .MV .x24 .x10,
    .MV .x10 .x24,
    .MV .x11 .x25,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 340)),
    .BNE .x11 .x0 (2512 : BitVec 13),
    .SUB .x30 .x10 .x12,
    .AUIPC .x5 (laHi GuestAddrs.teer_recipient_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 352)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_recipient_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 352)),
    .SD .x5 .x30 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_recipient_len (GuestAddrs.tx_eip7702_existing_authority_refund + 364)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_recipient_len (GuestAddrs.tx_eip7702_existing_authority_refund + 364)),
    .SD .x5 .x12 (0 : BitVec 12),
    .MV .x24 .x10,
    .MV .x10 .x24,
    .MV .x11 .x25,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 388)),
    .BNE .x11 .x0 (2464 : BitVec 13),
    .SLTU .x30 .x0 .x12,
    .AUIPC .x5 (laHi GuestAddrs.teer_value_nonzero (GuestAddrs.tx_eip7702_existing_authority_refund + 400)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_value_nonzero (GuestAddrs.tx_eip7702_existing_authority_refund + 400)),
    .SD .x5 .x30 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_inner_off (GuestAddrs.tx_eip7702_existing_authority_refund + 412)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_inner_off (GuestAddrs.tx_eip7702_existing_authority_refund + 412)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x21 .x8 .x6,
    .SUB .x22 .x9 .x6,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_eip7702_existing_authority_refund + 440)),
    .BNE .x12 .x0 (2412 : BitVec 13),
    .MV .x21 .x10,
    .MV .x22 .x11,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 464)),
    .BNE .x11 .x0 (2388 : BitVec 13),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 484)),
    .BNE .x11 .x0 (2368 : BitVec 13),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 504)),
    .BNE .x11 .x0 (2348 : BitVec 13),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 524)),
    .BNE .x11 .x0 (2328 : BitVec 13),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 544)),
    .BNE .x11 .x0 (2308 : BitVec 13),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 564)),
    .BNE .x11 .x0 (2288 : BitVec 13),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 584)),
    .BNE .x11 .x0 (2268 : BitVec 13),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 604)),
    .BNE .x11 .x0 (2248 : BitVec 13),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 624)),
    .BNE .x11 .x0 (2228 : BitVec 13),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 644)),
    .BNE .x11 .x0 (2208 : BitVec 13),
    .SUB .x21 .x10 .x12,
    .MV .x22 .x12,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .AUIPC .x12 (laHi GuestAddrs.teer_auth_count (GuestAddrs.tx_eip7702_existing_authority_refund + 668)),
    .ADDI .x12 .x12 (laLo GuestAddrs.teer_auth_count (GuestAddrs.tx_eip7702_existing_authority_refund + 668)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.tx_eip7702_existing_authority_refund + 676)),
    .BNE .x10 .x0 (2176 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.teer_auth_count (GuestAddrs.tx_eip7702_existing_authority_refund + 684)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_auth_count (GuestAddrs.tx_eip7702_existing_authority_refund + 684)),
    .LD .x23 .x5 (0 : BitVec 12),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_eip7702_existing_authority_refund + 704)),
    .BNE .x12 .x0 (2148 : BitVec 13),
    .MV .x21 .x10,
    .MV .x22 .x11,
    .LI .x24 (0 : Word),
    .BEQ .x24 .x23 (2132 : BitVec 13),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 736)),
    .BNE .x11 .x0 (2116 : BitVec 13),
    .MV .x21 .x10,
    .SUB .x25 .x10 .x12,
    .SD .x2 .x12 (136 : BitVec 12),
    .MV .x10 .x25,
    .LD .x11 .x2 (136 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_eip7702_existing_authority_refund + 764)),
    .BNE .x12 .x0 (2080 : BitVec 13),
    .SD .x2 .x10 (112 : BitVec 12),
    .SD .x2 .x11 (120 : BitVec 12),
    .LD .x10 .x2 (112 : BitVec 12),
    .LD .x11 .x2 (120 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 788)),
    .BNE .x11 .x0 (2056 : BitVec 13),
    .SD .x2 .x10 (112 : BitVec 12),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.tx_eip7702_existing_authority_refund + 808)),
    .BNE .x11 .x0 (2036 : BitVec 13),
    .MV .x6 .x10,
    .BEQ .x6 .x0 (8 : BitVec 13),
    .BNE .x6 .x20 (1020 : BitVec 13),
    .LD .x10 .x2 (112 : BitVec 12),
    .LD .x11 .x2 (120 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 836)),
    .BNE .x11 .x0 (2008 : BitVec 13),
    .SD .x2 .x10 (112 : BitVec 12),
    .LI .x7 (20 : Word),
    .BNE .x12 .x7 (1996 : BitVec 13),
    .SUB .x27 .x10 .x12,
    .LD .x10 .x2 (112 : BitVec 12),
    .LD .x11 .x2 (120 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 868)),
    .BNE .x11 .x0 (1976 : BitVec 13),
    .SD .x2 .x10 (112 : BitVec 12),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.tx_eip7702_existing_authority_refund + 888)),
    .BNE .x11 .x0 (1956 : BitVec 13),
    .MV .x6 .x10,
    .LI .x7 (-1 : Word),
    .BEQ .x6 .x7 (940 : BitVec 13),
    .SD .x2 .x6 (144 : BitVec 12),
    .MV .x10 .x25,
    .LD .x11 .x2 (136 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 920)),
    .ADDI .x12 .x12 (laLo GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 920)),
    .AUIPC .x13 (laHi GuestAddrs.teer_recover_scratch (GuestAddrs.tx_eip7702_existing_authority_refund + 928)),
    .ADDI .x13 .x13 (laLo GuestAddrs.teer_recover_scratch (GuestAddrs.tx_eip7702_existing_authority_refund + 928)),
    .JAL .x1 (jalOff GuestAddrs.eip7702_authorization_recover_address (GuestAddrs.tx_eip7702_existing_authority_refund + 936)),
    .BNE .x10 .x0 (904 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.teer_prior_count (GuestAddrs.tx_eip7702_existing_authority_refund + 944)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_prior_count (GuestAddrs.tx_eip7702_existing_authority_refund + 944)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_prior_set_flag (GuestAddrs.tx_eip7702_existing_authority_refund + 956)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_prior_set_flag (GuestAddrs.tx_eip7702_existing_authority_refund + 956)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_success_count (GuestAddrs.tx_eip7702_existing_authority_refund + 968)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_success_count (GuestAddrs.tx_eip7702_existing_authority_refund + 968)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (0 : Word),
    .BEQ .x7 .x6 (132 : BitVec 13),
    .SLLI .x28 .x7 (5 : BitVec 6),
    .AUIPC .x29 (laHi GuestAddrs.teer_success_table (GuestAddrs.tx_eip7702_existing_authority_refund + 992)),
    .ADDI .x29 .x29 (laLo GuestAddrs.teer_success_table (GuestAddrs.tx_eip7702_existing_authority_refund + 992)),
    .ADD .x28 .x28 .x29,
    .AUIPC .x29 (laHi GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 1004)),
    .ADDI .x29 .x29 (laLo GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 1004)),
    .MV .x30 .x28,
    .LI .x31 (20 : Word),
    .BEQ .x31 .x0 (32 : BitVec 13),
    .LBU .x16 .x29 (0 : BitVec 12),
    .LBU .x17 .x30 (0 : BitVec 12),
    .BNE .x16 .x17 (76 : BitVec 13),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LD .x29 .x28 (24 : BitVec 12),
    .LD .x30 .x2 (144 : BitVec 12),
    .BEQ .x29 .x30 (784 : BitVec 13),
    .AUIPC .x29 (laHi GuestAddrs.teer_prior_count (GuestAddrs.tx_eip7702_existing_authority_refund + 1064)),
    .ADDI .x29 .x29 (laLo GuestAddrs.teer_prior_count (GuestAddrs.tx_eip7702_existing_authority_refund + 1064)),
    .LD .x30 .x29 (0 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .SD .x29 .x30 (0 : BitVec 12),
    .LW .x29 .x28 (20 : BitVec 12),
    .BNE .x29 .x0 (20 : BitVec 13),
    .AUIPC .x29 (laHi GuestAddrs.teer_prior_set_flag (GuestAddrs.tx_eip7702_existing_authority_refund + 1092)),
    .ADDI .x29 .x29 (laLo GuestAddrs.teer_prior_set_flag (GuestAddrs.tx_eip7702_existing_authority_refund + 1092)),
    .LI .x30 (1 : Word),
    .SD .x29 .x30 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-128 : BitVec 21),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .AUIPC .x12 (laHi GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 1124)),
    .ADDI .x12 .x12 (laLo GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 1124)),
    .AUIPC .x13 (laHi GuestAddrs.teer_acct_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1132)),
    .ADDI .x13 .x13 (laLo GuestAddrs.teer_acct_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1132)),
    .AUIPC .x14 (laHi GuestAddrs.teer_acct_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1140)),
    .ADDI .x14 .x14 (laLo GuestAddrs.teer_acct_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1140)),
    .JAL .x1 (jalOff GuestAddrs.bal_find_account_by_address (GuestAddrs.tx_eip7702_existing_authority_refund + 1148)),
    .BNE .x10 .x0 (324 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.teer_acct_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1156)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_acct_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1156)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_acct_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1168)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_acct_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1168)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.teer_finals (GuestAddrs.tx_eip7702_existing_authority_refund + 1180)),
    .ADDI .x12 .x12 (laLo GuestAddrs.teer_finals (GuestAddrs.tx_eip7702_existing_authority_refund + 1180)),
    .JAL .x1 (jalOff GuestAddrs.bal_account_nonstorage_finals (GuestAddrs.tx_eip7702_existing_authority_refund + 1188)),
    .BNE .x10 .x0 (1656 : BitVec 13),
    .AUIPC .x7 (laHi GuestAddrs.teer_acct_absent (GuestAddrs.tx_eip7702_existing_authority_refund + 1196)),
    .ADDI .x7 .x7 (laLo GuestAddrs.teer_acct_absent (GuestAddrs.tx_eip7702_existing_authority_refund + 1196)),
    .SD .x7 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_records_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1208)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_records_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1208)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BEQ .x5 .x0 (56 : BitVec 13),
    .AUIPC .x6 (laHi GuestAddrs.bfa_index (GuestAddrs.tx_eip7702_existing_authority_refund + 1224)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bfa_index (GuestAddrs.tx_eip7702_existing_authority_refund + 1224)),
    .LD .x6 .x6 (0 : BitVec 12),
    .SLLI .x7 .x6 (4 : BitVec 6),
    .SLLI .x28 .x6 (3 : BitVec 6),
    .ADD .x7 .x7 .x28,
    .ADD .x7 .x5 .x7,
    .LD .x28 .x7 (16 : BitVec 12),
    .BEQ .x28 .x0 (20 : BitVec 13),
    .AUIPC .x7 (laHi GuestAddrs.teer_acct_absent (GuestAddrs.tx_eip7702_existing_authority_refund + 1260)),
    .ADDI .x7 .x7 (laLo GuestAddrs.teer_acct_absent (GuestAddrs.tx_eip7702_existing_authority_refund + 1260)),
    .LI .x28 (1 : Word),
    .SD .x7 .x28 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_tx_count (GuestAddrs.tx_eip7702_existing_authority_refund + 1276)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_tx_count (GuestAddrs.tx_eip7702_existing_authority_refund + 1276)),
    .LD .x5 .x5 (0 : BitVec 12),
    .LI .x6 (1 : Word),
    .BNE .x5 .x6 (556 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1296)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1296)),
    .LD .x13 .x5 (0 : BitVec 12),
    .BEQ .x13 .x0 (540 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1312)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1312)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1324)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1324)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 1336)),
    .ADDI .x12 .x12 (laLo GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 1336)),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1344)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1344)),
    .LD .x14 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1356)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1356)),
    .LD .x15 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1368)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1368)),
    .LD .x16 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.code_at_header_state_root (GuestAddrs.tx_eip7702_existing_authority_refund + 1380)),
    .BNE .x10 .x0 (464 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cahsr_code_length (GuestAddrs.tx_eip7702_existing_authority_refund + 1388)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cahsr_code_length (GuestAddrs.tx_eip7702_existing_authority_refund + 1388)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (448 : BitVec 13),
    .LI .x7 (23 : Word),
    .BNE .x6 .x7 (436 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1412)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1412)),
    .LD .x5 .x5 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.cahsr_code_offset (GuestAddrs.tx_eip7702_existing_authority_refund + 1424)),
    .ADDI .x6 .x6 (laLo GuestAddrs.cahsr_code_offset (GuestAddrs.tx_eip7702_existing_authority_refund + 1424)),
    .LD .x6 .x6 (0 : BitVec 12),
    .ADD .x5 .x5 .x6,
    .LBU .x6 .x5 (0 : BitVec 12),
    .LI .x7 (239 : Word),
    .BNE .x6 .x7 (396 : BitVec 13),
    .LBU .x6 .x5 (1 : BitVec 12),
    .LI .x7 (1 : Word),
    .BNE .x6 .x7 (384 : BitVec 13),
    .LBU .x6 .x5 (2 : BitVec 12),
    .BNE .x6 .x0 (376 : BitVec 13),
    .JAL .x0 (376 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.teer_acct_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1476)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_acct_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1476)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_acct_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1488)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_acct_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1488)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1500)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1500)),
    .LD .x13 .x5 (0 : BitVec 12),
    .BEQ .x13 .x0 (1336 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1516)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1516)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1528)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1528)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 1540)),
    .ADDI .x12 .x12 (laLo GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 1540)),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1548)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1548)),
    .LD .x14 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1560)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1560)),
    .LD .x15 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1572)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1572)),
    .LD .x16 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.code_at_header_state_root (GuestAddrs.tx_eip7702_existing_authority_refund + 1584)),
    .BNE .x10 .x0 (88 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cahsr_code_length (GuestAddrs.tx_eip7702_existing_authority_refund + 1592)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cahsr_code_length (GuestAddrs.tx_eip7702_existing_authority_refund + 1592)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (72 : BitVec 13),
    .LI .x7 (23 : Word),
    .BNE .x6 .x7 (1236 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1616)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1616)),
    .LD .x5 .x5 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.cahsr_code_offset (GuestAddrs.tx_eip7702_existing_authority_refund + 1628)),
    .ADDI .x6 .x6 (laLo GuestAddrs.cahsr_code_offset (GuestAddrs.tx_eip7702_existing_authority_refund + 1628)),
    .LD .x6 .x6 (0 : BitVec 12),
    .ADD .x5 .x5 .x6,
    .LBU .x6 .x5 (0 : BitVec 12),
    .LI .x7 (239 : Word),
    .BNE .x6 .x7 (1196 : BitVec 13),
    .LBU .x6 .x5 (1 : BitVec 12),
    .LI .x7 (1 : Word),
    .BNE .x6 .x7 (1184 : BitVec 13),
    .LBU .x6 .x5 (2 : BitVec 12),
    .BNE .x6 .x0 (1176 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1676)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1676)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1688)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1688)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 1700)),
    .ADDI .x12 .x12 (laLo GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 1700)),
    .LI .x13 (20 : Word),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1712)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1712)),
    .LD .x14 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1724)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1724)),
    .LD .x15 .x5 (0 : BitVec 12),
    .AUIPC .x16 (laHi GuestAddrs.teer_pre_acct (GuestAddrs.tx_eip7702_existing_authority_refund + 1736)),
    .ADDI .x16 .x16 (laLo GuestAddrs.teer_pre_acct (GuestAddrs.tx_eip7702_existing_authority_refund + 1736)),
    .JAL .x1 (jalOff GuestAddrs.account_at_header_state_root (GuestAddrs.tx_eip7702_existing_authority_refund + 1744)),
    .BEQ .x10 .x0 (52 : BitVec 13),
    .LI .x5 (1 : Word),
    .BNE .x10 .x5 (1092 : BitVec 13),
    .AUIPC .x7 (laHi GuestAddrs.teer_acct_absent (GuestAddrs.tx_eip7702_existing_authority_refund + 1760)),
    .ADDI .x7 .x7 (laLo GuestAddrs.teer_acct_absent (GuestAddrs.tx_eip7702_existing_authority_refund + 1760)),
    .LI .x28 (1 : Word),
    .SD .x7 .x28 (0 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.teer_rolled_back (GuestAddrs.tx_eip7702_existing_authority_refund + 1776)),
    .ADDI .x7 .x7 (laLo GuestAddrs.teer_rolled_back (GuestAddrs.tx_eip7702_existing_authority_refund + 1776)),
    .LI .x28 (1 : Word),
    .SD .x7 .x28 (0 : BitVec 12),
    .LI .x6 (0 : Word),
    .JAL .x0 (224 : BitVec 21),
    .AUIPC .x7 (laHi GuestAddrs.teer_acct_absent (GuestAddrs.tx_eip7702_existing_authority_refund + 1800)),
    .ADDI .x7 .x7 (laLo GuestAddrs.teer_acct_absent (GuestAddrs.tx_eip7702_existing_authority_refund + 1800)),
    .SD .x7 .x0 (0 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.teer_rolled_back (GuestAddrs.tx_eip7702_existing_authority_refund + 1812)),
    .ADDI .x7 .x7 (laLo GuestAddrs.teer_rolled_back (GuestAddrs.tx_eip7702_existing_authority_refund + 1812)),
    .LI .x28 (1 : Word),
    .SD .x7 .x28 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_pre_acct (GuestAddrs.tx_eip7702_existing_authority_refund + 1828)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_pre_acct (GuestAddrs.tx_eip7702_existing_authority_refund + 1828)),
    .LD .x6 .x5 (0 : BitVec 12),
    .JAL .x0 (180 : BitVec 21),
    .JAL .x0 (1004 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.teer_acct_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1848)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_acct_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1848)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_acct_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1860)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_acct_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1860)),
    .LD .x11 .x5 (0 : BitVec 12),
    .LD .x12 .x2 (104 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_account_nonce_before_index (GuestAddrs.tx_eip7702_existing_authority_refund + 1876)),
    .BEQ .x10 .x0 (136 : BitVec 13),
    .LI .x5 (1 : Word),
    .BNE .x10 .x5 (212 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1892)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1892)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BEQ .x5 .x0 (196 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1908)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1908)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1920)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1920)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 1932)),
    .ADDI .x12 .x12 (laLo GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 1932)),
    .LI .x13 (20 : Word),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1944)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 1944)),
    .LD .x14 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1956)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_len (GuestAddrs.tx_eip7702_existing_authority_refund + 1956)),
    .LD .x15 .x5 (0 : BitVec 12),
    .AUIPC .x16 (laHi GuestAddrs.teer_pre_acct (GuestAddrs.tx_eip7702_existing_authority_refund + 1968)),
    .ADDI .x16 .x16 (laLo GuestAddrs.teer_pre_acct (GuestAddrs.tx_eip7702_existing_authority_refund + 1968)),
    .JAL .x1 (jalOff GuestAddrs.account_at_header_state_root (GuestAddrs.tx_eip7702_existing_authority_refund + 1976)),
    .BEQ .x10 .x0 (20 : BitVec 13),
    .LI .x5 (1 : Word),
    .BNE .x10 .x5 (112 : BitVec 13),
    .LI .x6 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.teer_pre_acct (GuestAddrs.tx_eip7702_existing_authority_refund + 2000)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_pre_acct (GuestAddrs.tx_eip7702_existing_authority_refund + 2000)),
    .LD .x6 .x5 (0 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .MV .x6 .x11,
    .AUIPC .x7 (laHi GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 2020)),
    .ADDI .x7 .x7 (laLo GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 2020)),
    .AUIPC .x28 (laHi GuestAddrs.bv_stx_sender_addr (GuestAddrs.tx_eip7702_existing_authority_refund + 2028)),
    .ADDI .x28 .x28 (laLo GuestAddrs.bv_stx_sender_addr (GuestAddrs.tx_eip7702_existing_authority_refund + 2028)),
    .LI .x29 (20 : Word),
    .BEQ .x29 .x0 (32 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .LBU .x31 .x28 (0 : BitVec 12),
    .BNE .x30 .x31 (24 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.teer_prior_count (GuestAddrs.tx_eip7702_existing_authority_refund + 2076)),
    .ADDI .x7 .x7 (laLo GuestAddrs.teer_prior_count (GuestAddrs.tx_eip7702_existing_authority_refund + 2076)),
    .LD .x7 .x7 (0 : BitVec 12),
    .ADD .x6 .x6 .x7,
    .LD .x7 .x2 (144 : BitVec 12),
    .BNE .x6 .x7 (-252 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.teer_acct_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 2100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_acct_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 2100)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (56 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.teer_finals (GuestAddrs.tx_eip7702_existing_authority_refund + 2116)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_finals (GuestAddrs.tx_eip7702_existing_authority_refund + 2116)),
    .LD .x6 .x5 (40 : BitVec 12),
    .BEQ .x6 .x0 (24 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.teer_finals (GuestAddrs.tx_eip7702_existing_authority_refund + 2132)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_finals (GuestAddrs.tx_eip7702_existing_authority_refund + 2132)),
    .LD .x6 .x5 (48 : BitVec 12),
    .LD .x7 .x2 (144 : BitVec 12),
    .BLTU .x7 .x6 (20 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.teer_rolled_back (GuestAddrs.tx_eip7702_existing_authority_refund + 2152)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_rolled_back (GuestAddrs.tx_eip7702_existing_authority_refund + 2152)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_prior_count (GuestAddrs.tx_eip7702_existing_authority_refund + 2168)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_prior_count (GuestAddrs.tx_eip7702_existing_authority_refund + 2168)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BNE .x6 .x0 (204 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.teer_acct_absent (GuestAddrs.tx_eip7702_existing_authority_refund + 2184)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_acct_absent (GuestAddrs.tx_eip7702_existing_authority_refund + 2184)),
    .LD .x28 .x5 (0 : BitVec 12),
    .BEQ .x28 .x0 (16 : BitVec 13),
    .LUI .x28 (45 : BitVec 20),
    .ADDIW .x28 .x28 (-720 : BitVec 12),
    .ADD .x26 .x26 .x28,
    .AUIPC .x7 (laHi GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 2212)),
    .ADDI .x7 .x7 (laLo GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 2212)),
    .AUIPC .x28 (laHi GuestAddrs.bv_stx_sender_addr (GuestAddrs.tx_eip7702_existing_authority_refund + 2220)),
    .ADDI .x28 .x28 (laLo GuestAddrs.bv_stx_sender_addr (GuestAddrs.tx_eip7702_existing_authority_refund + 2220)),
    .LI .x29 (20 : Word),
    .BEQ .x29 .x0 (152 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .LBU .x31 .x28 (0 : BitVec 12),
    .BNE .x30 .x31 (20 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.teer_value_nonzero (GuestAddrs.tx_eip7702_existing_authority_refund + 2264)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_value_nonzero (GuestAddrs.tx_eip7702_existing_authority_refund + 2264)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (80 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.teer_recipient_len (GuestAddrs.tx_eip7702_existing_authority_refund + 2280)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_recipient_len (GuestAddrs.tx_eip7702_existing_authority_refund + 2280)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (20 : Word),
    .BNE .x6 .x7 (60 : BitVec 13),
    .AUIPC .x7 (laHi GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 2300)),
    .ADDI .x7 .x7 (laLo GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 2300)),
    .AUIPC .x5 (laHi GuestAddrs.teer_recipient_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 2308)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_recipient_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 2308)),
    .LD .x28 .x5 (0 : BitVec 12),
    .LI .x29 (20 : Word),
    .BEQ .x29 .x0 (60 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .LBU .x31 .x28 (0 : BitVec 12),
    .BNE .x30 .x31 (20 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.teer_regular_refund (GuestAddrs.tx_eip7702_existing_authority_refund + 2356)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_regular_refund (GuestAddrs.tx_eip7702_existing_authority_refund + 2356)),
    .LD .x29 .x5 (0 : BitVec 12),
    .LUI .x28 (2 : BitVec 20),
    .ADDIW .x28 .x28 (-192 : BitVec 12),
    .ADD .x29 .x29 .x28,
    .SD .x5 .x29 (0 : BitVec 12),
    .MV .x7 .x27,
    .LI .x28 (20 : Word),
    .LI .x29 (0 : Word),
    .BEQ .x28 .x0 (24 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .OR .x29 .x29 .x30,
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .BEQ .x29 .x0 (288 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.teer_prior_set_flag (GuestAddrs.tx_eip7702_existing_authority_refund + 2424)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_prior_set_flag (GuestAddrs.tx_eip7702_existing_authority_refund + 2424)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BNE .x6 .x0 (272 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.svf_tx_count (GuestAddrs.tx_eip7702_existing_authority_refund + 2440)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_tx_count (GuestAddrs.tx_eip7702_existing_authority_refund + 2440)),
    .LD .x5 .x5 (0 : BitVec 12),
    .LI .x6 (1 : Word),
    .BNE .x5 .x6 (200 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 2460)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 2460)),
    .LD .x13 .x5 (0 : BitVec 12),
    .BEQ .x13 .x0 (224 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 2476)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 2476)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_len (GuestAddrs.tx_eip7702_existing_authority_refund + 2488)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_len (GuestAddrs.tx_eip7702_existing_authority_refund + 2488)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 2500)),
    .ADDI .x12 .x12 (laLo GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 2500)),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_len (GuestAddrs.tx_eip7702_existing_authority_refund + 2508)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_len (GuestAddrs.tx_eip7702_existing_authority_refund + 2508)),
    .LD .x14 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 2520)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 2520)),
    .LD .x15 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_len (GuestAddrs.tx_eip7702_existing_authority_refund + 2532)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_len (GuestAddrs.tx_eip7702_existing_authority_refund + 2532)),
    .LD .x16 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.code_at_header_state_root (GuestAddrs.tx_eip7702_existing_authority_refund + 2544)),
    .BNE .x10 .x0 (148 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cahsr_code_length (GuestAddrs.tx_eip7702_existing_authority_refund + 2552)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cahsr_code_length (GuestAddrs.tx_eip7702_existing_authority_refund + 2552)),
    .LD .x5 .x5 (0 : BitVec 12),
    .LI .x6 (23 : Word),
    .BNE .x5 .x6 (128 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 2572)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 2572)),
    .LD .x5 .x5 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.cahsr_code_offset (GuestAddrs.tx_eip7702_existing_authority_refund + 2584)),
    .ADDI .x6 .x6 (laLo GuestAddrs.cahsr_code_offset (GuestAddrs.tx_eip7702_existing_authority_refund + 2584)),
    .LD .x6 .x6 (0 : BitVec 12),
    .ADD .x5 .x5 .x6,
    .LBU .x6 .x5 (0 : BitVec 12),
    .LI .x7 (239 : Word),
    .BNE .x6 .x7 (88 : BitVec 13),
    .LBU .x6 .x5 (1 : BitVec 12),
    .LI .x7 (1 : Word),
    .BNE .x6 .x7 (76 : BitVec 13),
    .LBU .x6 .x5 (2 : BitVec 12),
    .BNE .x6 .x0 (68 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.teer_predelegated_count (GuestAddrs.tx_eip7702_existing_authority_refund + 2632)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_predelegated_count (GuestAddrs.tx_eip7702_existing_authority_refund + 2632)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .JAL .x0 (56 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.teer_acct_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 2656)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_acct_ptr (GuestAddrs.tx_eip7702_existing_authority_refund + 2656)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_acct_len (GuestAddrs.tx_eip7702_existing_authority_refund + 2668)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_acct_len (GuestAddrs.tx_eip7702_existing_authority_refund + 2668)),
    .LD .x11 .x5 (0 : BitVec 12),
    .LD .x12 .x2 (104 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_account_nonce_before_index (GuestAddrs.tx_eip7702_existing_authority_refund + 2684)),
    .BNE .x10 .x0 (8 : BitVec 13),
    .JAL .x0 (16 : BitVec 21),
    .LUI .x28 (9 : BitVec 20),
    .ADDIW .x28 .x28 (-1674 : BitVec 12),
    .ADD .x26 .x26 .x28,
    .AUIPC .x5 (laHi GuestAddrs.teer_success_count (GuestAddrs.tx_eip7702_existing_authority_refund + 2708)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_success_count (GuestAddrs.tx_eip7702_existing_authority_refund + 2708)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (1060 : Word),
    .BGEU .x6 .x7 (124 : BitVec 13),
    .SLLI .x7 .x6 (5 : BitVec 6),
    .AUIPC .x28 (laHi GuestAddrs.teer_success_table (GuestAddrs.tx_eip7702_existing_authority_refund + 2732)),
    .ADDI .x28 .x28 (laLo GuestAddrs.teer_success_table (GuestAddrs.tx_eip7702_existing_authority_refund + 2732)),
    .ADD .x7 .x7 .x28,
    .AUIPC .x28 (laHi GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 2744)),
    .ADDI .x28 .x28 (laLo GuestAddrs.teer_authority (GuestAddrs.tx_eip7702_existing_authority_refund + 2744)),
    .MV .x29 .x7,
    .LI .x30 (20 : Word),
    .BEQ .x30 .x0 (28 : BitVec 13),
    .LBU .x31 .x28 (0 : BitVec 12),
    .SB .x29 .x31 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .SW .x7 .x0 (20 : BitVec 12),
    .MV .x28 .x27,
    .LI .x29 (20 : Word),
    .BEQ .x29 .x0 (24 : BitVec 13),
    .LBU .x30 .x28 (0 : BitVec 12),
    .BNE .x30 .x0 (24 : BitVec 13),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .LI .x28 (1 : Word),
    .SW .x7 .x28 (20 : BitVec 12),
    .LD .x28 .x2 (144 : BitVec 12),
    .SD .x7 .x28 (24 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .ADDI .x24 .x24 (1 : BitVec 12),
    .JAL .x0 (-2128 : BitVec 21),
    .MV .x10 .x26,
    .AUIPC .x5 (laHi GuestAddrs.teer_regular_refund (GuestAddrs.tx_eip7702_existing_authority_refund + 2860)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_regular_refund (GuestAddrs.tx_eip7702_existing_authority_refund + 2860)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_wouldbe_state (GuestAddrs.tx_eip7702_existing_authority_refund + 2872)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_wouldbe_state (GuestAddrs.tx_eip7702_existing_authority_refund + 2872)),
    .SD .x5 .x10 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_wouldbe_regular (GuestAddrs.tx_eip7702_existing_authority_refund + 2884)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_wouldbe_regular (GuestAddrs.tx_eip7702_existing_authority_refund + 2884)),
    .SD .x5 .x11 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teer_rolled_back (GuestAddrs.tx_eip7702_existing_authority_refund + 2896)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_rolled_back (GuestAddrs.tx_eip7702_existing_authority_refund + 2896)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .LI .x11 (0 : Word),
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
    .ADDI .x2 .x2 (160 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txEip7702ExistingAuthorityRefund_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txEip7702ExistingAuthorityRefund_relocs : RelocTable :=
  [ (21, .la .x5 "teer_regular_refund"),
    (24, .la .x5 "teer_success_count"),
    (27, .la .x5 "teer_predelegated_count"),
    (30, .la .x5 "teer_rolled_back"),
    (36, .la .x12 "teer_type"),
    (38, .la .x13 "teer_inner_off"),
    (40, .jal .x1 "tx_type_dispatch"),
    (42, .la .x5 "teer_type"),
    (47, .la .x5 "teer_inner_off"),
    (54, .jal .x1 "rlp_walk_init"),
    (60, .jal .x1 "rlp_walk_next"),
    (65, .jal .x1 "rlp_walk_next"),
    (70, .jal .x1 "rlp_walk_next"),
    (75, .jal .x1 "rlp_walk_next"),
    (80, .jal .x1 "rlp_walk_next"),
    (85, .jal .x1 "rlp_walk_next"),
    (88, .la .x5 "teer_recipient_ptr"),
    (91, .la .x5 "teer_recipient_len"),
    (97, .jal .x1 "rlp_walk_next"),
    (100, .la .x5 "teer_value_nonzero"),
    (103, .la .x5 "teer_inner_off"),
    (110, .jal .x1 "rlp_walk_init"),
    (116, .jal .x1 "rlp_walk_next"),
    (121, .jal .x1 "rlp_walk_next"),
    (126, .jal .x1 "rlp_walk_next"),
    (131, .jal .x1 "rlp_walk_next"),
    (136, .jal .x1 "rlp_walk_next"),
    (141, .jal .x1 "rlp_walk_next"),
    (146, .jal .x1 "rlp_walk_next"),
    (151, .jal .x1 "rlp_walk_next"),
    (156, .jal .x1 "rlp_walk_next"),
    (161, .jal .x1 "rlp_walk_next"),
    (167, .la .x12 "teer_auth_count"),
    (169, .jal .x1 "rlp_list_count_items"),
    (171, .la .x5 "teer_auth_count"),
    (176, .jal .x1 "rlp_walk_init"),
    (184, .jal .x1 "rlp_walk_next"),
    (191, .jal .x1 "rlp_walk_init"),
    (197, .jal .x1 "rlp_walk_next"),
    (202, .jal .x1 "rlp_content_to_u64"),
    (209, .jal .x1 "rlp_walk_next"),
    (217, .jal .x1 "rlp_walk_next"),
    (222, .jal .x1 "rlp_content_to_u64"),
    (230, .la .x12 "teer_authority"),
    (232, .la .x13 "teer_recover_scratch"),
    (234, .jal .x1 "eip7702_authorization_recover_address"),
    (236, .la .x5 "teer_prior_count"),
    (239, .la .x5 "teer_prior_set_flag"),
    (242, .la .x5 "teer_success_count"),
    (248, .la .x29 "teer_success_table"),
    (251, .la .x29 "teer_authority"),
    (266, .la .x29 "teer_prior_count"),
    (273, .la .x29 "teer_prior_set_flag"),
    (281, .la .x12 "teer_authority"),
    (283, .la .x13 "teer_acct_ptr"),
    (285, .la .x14 "teer_acct_len"),
    (287, .jal .x1 "bal_find_account_by_address"),
    (289, .la .x5 "teer_acct_ptr"),
    (292, .la .x5 "teer_acct_len"),
    (295, .la .x12 "teer_finals"),
    (297, .jal .x1 "bal_account_nonstorage_finals"),
    (299, .la .x7 "teer_acct_absent"),
    (302, .la .x5 "teer_records_ptr"),
    (306, .la .x6 "bfa_index"),
    (315, .la .x7 "teer_acct_absent"),
    (319, .la .x5 "svf_tx_count"),
    (324, .la .x5 "bv_witness_state_ptr"),
    (328, .la .x5 "sv_pre_rlp_ptr"),
    (331, .la .x5 "sv_pre_rlp_len"),
    (334, .la .x12 "teer_authority"),
    (336, .la .x5 "bv_witness_state_len"),
    (339, .la .x5 "svf_codes_ptr"),
    (342, .la .x5 "svf_codes_len"),
    (345, .jal .x1 "code_at_header_state_root"),
    (347, .la .x5 "cahsr_code_length"),
    (353, .la .x5 "svf_codes_ptr"),
    (356, .la .x6 "cahsr_code_offset"),
    (369, .la .x5 "teer_acct_ptr"),
    (372, .la .x5 "teer_acct_len"),
    (375, .la .x5 "bv_witness_state_ptr"),
    (379, .la .x5 "sv_pre_rlp_ptr"),
    (382, .la .x5 "sv_pre_rlp_len"),
    (385, .la .x12 "teer_authority"),
    (387, .la .x5 "bv_witness_state_len"),
    (390, .la .x5 "svf_codes_ptr"),
    (393, .la .x5 "svf_codes_len"),
    (396, .jal .x1 "code_at_header_state_root"),
    (398, .la .x5 "cahsr_code_length"),
    (404, .la .x5 "svf_codes_ptr"),
    (407, .la .x6 "cahsr_code_offset"),
    (419, .la .x5 "sv_pre_rlp_ptr"),
    (422, .la .x5 "sv_pre_rlp_len"),
    (425, .la .x12 "teer_authority"),
    (428, .la .x5 "bv_witness_state_ptr"),
    (431, .la .x5 "bv_witness_state_len"),
    (434, .la .x16 "teer_pre_acct"),
    (436, .jal .x1 "account_at_header_state_root"),
    (440, .la .x7 "teer_acct_absent"),
    (444, .la .x7 "teer_rolled_back"),
    (450, .la .x7 "teer_acct_absent"),
    (453, .la .x7 "teer_rolled_back"),
    (457, .la .x5 "teer_pre_acct"),
    (462, .la .x5 "teer_acct_ptr"),
    (465, .la .x5 "teer_acct_len"),
    (469, .jal .x1 "bal_account_nonce_before_index"),
    (473, .la .x5 "bv_witness_state_ptr"),
    (477, .la .x5 "sv_pre_rlp_ptr"),
    (480, .la .x5 "sv_pre_rlp_len"),
    (483, .la .x12 "teer_authority"),
    (486, .la .x5 "bv_witness_state_ptr"),
    (489, .la .x5 "bv_witness_state_len"),
    (492, .la .x16 "teer_pre_acct"),
    (494, .jal .x1 "account_at_header_state_root"),
    (500, .la .x5 "teer_pre_acct"),
    (505, .la .x7 "teer_authority"),
    (507, .la .x28 "bv_stx_sender_addr"),
    (519, .la .x7 "teer_prior_count"),
    (525, .la .x5 "teer_acct_ptr"),
    (529, .la .x5 "teer_finals"),
    (533, .la .x5 "teer_finals"),
    (538, .la .x5 "teer_rolled_back"),
    (542, .la .x5 "teer_prior_count"),
    (546, .la .x5 "teer_acct_absent"),
    (553, .la .x7 "teer_authority"),
    (555, .la .x28 "bv_stx_sender_addr"),
    (566, .la .x5 "teer_value_nonzero"),
    (570, .la .x5 "teer_recipient_len"),
    (575, .la .x7 "teer_authority"),
    (577, .la .x5 "teer_recipient_ptr"),
    (589, .la .x5 "teer_regular_refund"),
    (606, .la .x5 "teer_prior_set_flag"),
    (610, .la .x5 "svf_tx_count"),
    (615, .la .x5 "bv_witness_state_ptr"),
    (619, .la .x5 "sv_pre_rlp_ptr"),
    (622, .la .x5 "sv_pre_rlp_len"),
    (625, .la .x12 "teer_authority"),
    (627, .la .x5 "bv_witness_state_len"),
    (630, .la .x5 "svf_codes_ptr"),
    (633, .la .x5 "svf_codes_len"),
    (636, .jal .x1 "code_at_header_state_root"),
    (638, .la .x5 "cahsr_code_length"),
    (643, .la .x5 "svf_codes_ptr"),
    (646, .la .x6 "cahsr_code_offset"),
    (658, .la .x5 "teer_predelegated_count"),
    (664, .la .x5 "teer_acct_ptr"),
    (667, .la .x5 "teer_acct_len"),
    (671, .jal .x1 "bal_account_nonce_before_index"),
    (677, .la .x5 "teer_success_count"),
    (683, .la .x28 "teer_success_table"),
    (686, .la .x28 "teer_authority"),
    (715, .la .x5 "teer_regular_refund"),
    (718, .la .x5 "teer_wouldbe_state"),
    (721, .la .x5 "teer_wouldbe_regular"),
    (724, .la .x5 "teer_rolled_back") ]

def txEip7702ExistingAuthorityRefundFunction : String :=
  "tx_eip7702_existing_authority_refund:\n" ++ emitProgramR txEip7702ExistingAuthorityRefund_prog txEip7702ExistingAuthorityRefund_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txEip7702ExistingAuthorityRefund_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txEip7702ExistingAuthorityRefundFunction_eq_prog :
    txEip7702ExistingAuthorityRefundFunction = "tx_eip7702_existing_authority_refund:\n" ++ emitProgramR txEip7702ExistingAuthorityRefund_prog txEip7702ExistingAuthorityRefund_relocs := rfl

#guard txEip7702ExistingAuthorityRefundFunction.startsWith "tx_eip7702_existing_authority_refund:\n"
#guard txEip7702ExistingAuthorityRefund_prog.length = 745
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
    .ADD .x7 .x7 .x10,
    .SD .x6 .x7 (0 : BitVec 12),
    .JAL .x0 (12 : BitVec 21),
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
  balAccountNonceBeforeIndexFunction ++ "\n" ++
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
