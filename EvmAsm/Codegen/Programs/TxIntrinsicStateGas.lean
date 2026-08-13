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
import EvmAsm.Codegen.GuestAddrs

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
/-! Probe-only local PC placeholder. -/
def balAccountNonceBeforeIndexPc : Nat := 0x80000000

def balAccountNonceBeforeIndex_prog : Program :=
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
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .LI .x12 (4 : Word),
    .ADDI .x13 .x2 (72 : BitVec 12),
    .ADDI .x14 .x2 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (balAccountNonceBeforeIndexPc + 64)),
    .BNE .x10 .x0 (brOff (balAccountNonceBeforeIndexPc + 284) (balAccountNonceBeforeIndexPc + 68)),
    .LD .x5 .x2 (72 : BitVec 12),
    .ADD .x19 .x8 .x5,
    .LD .x20 .x2 (80 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x20,
    .ADDI .x12 .x2 (88 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (balAccountNonceBeforeIndexPc + 96)),
    .BNE .x10 .x0 (brOff (balAccountNonceBeforeIndexPc + 284) (balAccountNonceBeforeIndexPc + 100)),
    .LD .x20 .x2 (88 : BitVec 12),
    .LI .x21 (0 : Word),
    .LI .x22 (0 : Word),
    .LI .x23 (0 : Word),
    .SD .x2 .x0 (104 : BitVec 12),
    .BEQ .x21 .x20 (brOff (balAccountNonceBeforeIndexPc + 252) (balAccountNonceBeforeIndexPc + 124)),
    .MV .x10 .x19,
    .LD .x11 .x2 (80 : BitVec 12),
    .MV .x12 .x21,
    .ADDI .x13 .x2 (72 : BitVec 12),
    .ADDI .x14 .x2 (88 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_item_span (balAccountNonceBeforeIndexPc + 148)),
    .BNE .x10 .x0 (brOff (balAccountNonceBeforeIndexPc + 284) (balAccountNonceBeforeIndexPc + 152)),
    .LD .x5 .x2 (72 : BitVec 12),
    .ADD .x5 .x19 .x5,
    .SD .x2 .x5 (96 : BitVec 12),
    .MV .x10 .x5,
    .LD .x11 .x2 (88 : BitVec 12),
    .LI .x12 (0 : Word),
    .ADDI .x13 .x2 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict (balAccountNonceBeforeIndexPc + 184)),
    .BNE .x10 .x0 (brOff (balAccountNonceBeforeIndexPc + 284) (balAccountNonceBeforeIndexPc + 188)),
    .LD .x5 .x2 (72 : BitVec 12),
    .BGEU .x5 .x18 (48 : BitVec 13),
    .BLTU .x5 .x22 (44 : BitVec 13),
    .MV .x22 .x5,
    .LD .x10 .x2 (96 : BitVec 12),
    .LD .x11 .x2 (88 : BitVec 12),
    .LI .x12 (1 : Word),
    .ADDI .x13 .x2 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict (balAccountNonceBeforeIndexPc + 224)),
    .BNE .x10 .x0 (56 : BitVec 13),
    .LD .x23 .x2 (72 : BitVec 12),
    .LI .x5 (1 : Word),
    .SD .x2 .x5 (104 : BitVec 12),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (jalOff (balAccountNonceBeforeIndexPc + 124) (balAccountNonceBeforeIndexPc + 248)),
    .LD .x5 .x2 (104 : BitVec 12),
    .BEQ .x5 .x0 (16 : BitVec 13),
    .LI .x10 (0 : Word),
    .MV .x11 .x23,
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (1 : Word),
    .LI .x11 (0 : Word),
    .JAL .x0 (12 : BitVec 21),
    .LI .x10 (2 : Word),
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
    .ADDI .x2 .x2 (112 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balAccountNonceBeforeIndex_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balAccountNonceBeforeIndex_relocs : RelocTable :=
  [ (16, .jal .x1 "rlp_list_nth_item"),
    (24, .jal .x1 "rlp_list_count_items"),
    (37, .jal .x1 "rlp_item_span"),
    (46, .jal .x1 "rlp_field_to_u64_strict"),
    (56, .jal .x1 "rlp_field_to_u64_strict") ]

def balAccountNonceBeforeIndexFunction : String :=
  "bal_account_nonce_before_index:\n" ++ emitProgramR balAccountNonceBeforeIndex_prog balAccountNonceBeforeIndex_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balAccountNonceBeforeIndex_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balAccountNonceBeforeIndexFunction_eq_prog :
    balAccountNonceBeforeIndexFunction = "bal_account_nonce_before_index:\n" ++ emitProgramR balAccountNonceBeforeIndex_prog balAccountNonceBeforeIndex_relocs := rfl

#guard balAccountNonceBeforeIndexFunction.startsWith "bal_account_nonce_before_index:\n"
#guard balAccountNonceBeforeIndex_prog.length = 84
/-! ## eip7702_authority_asof

    Resolve one authority for EIP-7702 auth preparation.

    a1 (nonce) is CURRENT (transaction map then block map) — auth validation needs the
    post-prior-auth nonce within the same transaction.

    a2 (delegated) is TRANSACTION-START `delegated_before_tx` per
    eoa_delegation.py:265-281 / get_pre_state_account: block map
    only (prior committed txs), then authenticated pre-block header code —
    NEVER the pending current-tx overlay.  First auth clearing a delegation
    must not make a later same-tx auth see delegated=0 and re-charge AUTH_BASE
    (GH #11310).  Header-only would also be wrong when an earlier tx in the
    block left durable delegated=1.

    The block-map branch reads the actual code pointer/length returned by
    `account_writes_auth_block` and recognizes the EF0100 marker bytes.  The
    EXEC_FLAGS word remains an account-state flag payload; it is not a
    delegation marker.

    BAL post-state fields are intentionally not consulted.

    a0 = canonical authority address
    returns a0 = 0 absent, 1 live, 2 unavailable/malformed, 3 live with
    unsupported (non-delegation) code;
            a1 = current nonce, a2 = delegated_before_tx.

    On auth_current hit + auth_block miss, header fall-through must still run
    for a2 (delegated_before_tx). Empty/no-delegation exits from the code-length
    and EF0100 checks must land on the MV a1←nonce head of that tail (#12273);
    landing one instruction past it leaves stale a1 (header arg setup / caller-
    saved) and drops a successful tx-map nonce. Do not short-circuit: a2 must
    not come from the pending tx overlay. -/
def eip7702AuthorityAsof_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x13 (32 : BitVec 12),
    .SD .x2 .x14 (40 : BitVec 12),
    .SD .x2 .x15 (48 : BitVec 12),
    .MV .x8 .x10,
    .LI .x18 (0 : Word),
    .ADDI .x11 .x2 (56 : BitVec 12),
    .ADDI .x12 .x2 (48 : BitVec 12),
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.account_writes_auth_current (GuestAddrs.eip7702_authority_asof + 52)),
    .LI .x5 (1 : Word),
    .BNE .x10 .x5 (brOff (GuestAddrs.eip7702_authority_asof + 484) (GuestAddrs.eip7702_authority_asof + 60)),
    .LD .x9 .x2 (56 : BitVec 12),
    .MV .x10 .x8,
    .ADDI .x11 .x2 (56 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.account_writes_latest_nonce_tx (GuestAddrs.eip7702_authority_asof + 76)),
    .BEQ .x10 .x0 (8 : BitVec 13),
    .LD .x9 .x2 (56 : BitVec 12),
    .MV .x10 .x8,
    .ADDI .x11 .x2 (56 : BitVec 12),
    .ADDI .x12 .x2 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.account_writes_auth_block (GuestAddrs.eip7702_authority_asof + 100)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.eip7702_authority_asof + 192) (GuestAddrs.eip7702_authority_asof + 104)),
    .LI .x5 (2 : Word),
    .BEQ .x10 .x5 (brOff (GuestAddrs.eip7702_authority_asof + 176) (GuestAddrs.eip7702_authority_asof + 112)),
    .BEQ .x12 .x0 (60 : BitVec 13),
    .LI .x5 (23 : Word),
    .BNE .x12 .x5 (52 : BitVec 13),
    .LBU .x5 .x11 (0 : BitVec 12),
    .LI .x6 (239 : Word),
    .BNE .x5 .x6 (40 : BitVec 13),
    .LBU .x5 .x11 (1 : BitVec 12),
    .LI .x6 (1 : Word),
    .BNE .x5 .x6 (28 : BitVec 13),
    .LBU .x5 .x11 (2 : BitVec 12),
    .BNE .x5 .x0 (20 : BitVec 13),
    .MV .x11 .x9,
    .LI .x12 (1 : Word),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.eip7702_authority_asof + 992) (GuestAddrs.eip7702_authority_asof + 172)),
    .MV .x11 .x9,
    .LI .x12 (0 : Word),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.eip7702_authority_asof + 992) (GuestAddrs.eip7702_authority_asof + 188)),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.eip7702_authority_asof + 192)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.eip7702_authority_asof + 192)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_len (GuestAddrs.eip7702_authority_asof + 204)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_len (GuestAddrs.eip7702_authority_asof + 204)),
    .LD .x11 .x5 (0 : BitVec 12),
    .MV .x12 .x8,
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_ptr (GuestAddrs.eip7702_authority_asof + 220)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_ptr (GuestAddrs.eip7702_authority_asof + 220)),
    .LD .x13 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_len (GuestAddrs.eip7702_authority_asof + 232)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_len (GuestAddrs.eip7702_authority_asof + 232)),
    .LD .x14 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_ptr (GuestAddrs.eip7702_authority_asof + 244)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_ptr (GuestAddrs.eip7702_authority_asof + 244)),
    .LD .x15 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_len (GuestAddrs.eip7702_authority_asof + 256)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_len (GuestAddrs.eip7702_authority_asof + 256)),
    .LD .x16 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.code_at_header_state_root (GuestAddrs.eip7702_authority_asof + 268)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.eip7702_authority_asof + 376) (GuestAddrs.eip7702_authority_asof + 272)),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (brOff (GuestAddrs.eip7702_authority_asof + 176) (GuestAddrs.eip7702_authority_asof + 280)),
    .LI .x5 (5 : Word),
    .BNE .x10 .x5 (brOff (GuestAddrs.eip7702_authority_asof + 360) (GuestAddrs.eip7702_authority_asof + 288)),
    .AUIPC .x5 (laHi GuestAddrs.cahsr_acct_struct (GuestAddrs.eip7702_authority_asof + 292)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cahsr_acct_struct (GuestAddrs.eip7702_authority_asof + 292)),
    .AUIPC .x6 (laHi GuestAddrs.chahsr_empty_code_hash (GuestAddrs.eip7702_authority_asof + 300)),
    .ADDI .x6 .x6 (laLo GuestAddrs.chahsr_empty_code_hash (GuestAddrs.eip7702_authority_asof + 300)),
    .LD .x7 .x5 (72 : BitVec 12),
    .LD .x10 .x6 (0 : BitVec 12),
    .BNE .x7 .x10 (44 : BitVec 13),
    .LD .x7 .x5 (80 : BitVec 12),
    .LD .x10 .x6 (8 : BitVec 12),
    .BNE .x7 .x10 (32 : BitVec 13),
    .LD .x7 .x5 (88 : BitVec 12),
    .LD .x10 .x6 (16 : BitVec 12),
    .BNE .x7 .x10 (20 : BitVec 13),
    .LD .x7 .x5 (96 : BitVec 12),
    .LD .x10 .x6 (24 : BitVec 12),
    .BNE .x7 .x10 (8 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.eip7702_authority_asof + 176) (GuestAddrs.eip7702_authority_asof + 356)),
    .MV .x11 .x9,
    .LI .x12 (0 : Word),
    .LI .x10 (2 : Word),
    .JAL .x0 (jalOff (GuestAddrs.eip7702_authority_asof + 988) (GuestAddrs.eip7702_authority_asof + 372)),
    .AUIPC .x5 (laHi GuestAddrs.cahsr_code_length (GuestAddrs.eip7702_authority_asof + 376)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cahsr_code_length (GuestAddrs.eip7702_authority_asof + 376)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BEQ .x5 .x0 (brOff (GuestAddrs.eip7702_authority_asof + 176) (GuestAddrs.eip7702_authority_asof + 388)),
    .LI .x6 (23 : Word),
    .BNE .x5 .x6 (brOff (GuestAddrs.eip7702_authority_asof + 176) (GuestAddrs.eip7702_authority_asof + 396)),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_ptr (GuestAddrs.eip7702_authority_asof + 400)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_ptr (GuestAddrs.eip7702_authority_asof + 400)),
    .LD .x5 .x5 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.cahsr_code_offset (GuestAddrs.eip7702_authority_asof + 412)),
    .ADDI .x6 .x6 (laLo GuestAddrs.cahsr_code_offset (GuestAddrs.eip7702_authority_asof + 412)),
    .LD .x6 .x6 (0 : BitVec 12),
    .ADD .x5 .x5 .x6,
    .LBU .x6 .x5 (0 : BitVec 12),
    .LI .x7 (239 : Word),
    .BNE .x6 .x7 (brOff (GuestAddrs.eip7702_authority_asof + 176) (GuestAddrs.eip7702_authority_asof + 436)),
    .LBU .x6 .x5 (1 : BitVec 12),
    .LI .x7 (1 : Word),
    .BNE .x6 .x7 (brOff (GuestAddrs.eip7702_authority_asof + 176) (GuestAddrs.eip7702_authority_asof + 448)),
    .LBU .x6 .x5 (2 : BitVec 12),
    .BNE .x6 .x0 (brOff (GuestAddrs.eip7702_authority_asof + 176) (GuestAddrs.eip7702_authority_asof + 456)),
    .MV .x11 .x9,
    .LI .x12 (1 : Word),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.eip7702_authority_asof + 988) (GuestAddrs.eip7702_authority_asof + 472)),
    .LI .x5 (2 : Word),
    .BEQ .x10 .x5 (brOff (GuestAddrs.eip7702_authority_asof + 980) (GuestAddrs.eip7702_authority_asof + 480)),
    .MV .x10 .x8,
    .ADDI .x11 .x2 (56 : BitVec 12),
    .LI .x12 (20 : Word),
    .JAL .x1 (jalOff GuestAddrs.account_writes_latest_nonce_tx (GuestAddrs.eip7702_authority_asof + 496)),
    .BEQ .x10 .x0 (16 : BitVec 13),
    .LD .x9 .x2 (56 : BitVec 12),
    .LI .x18 (1 : Word),
    .JAL .x0 (32 : BitVec 21),
    .MV .x10 .x8,
    .ADDI .x11 .x2 (56 : BitVec 12),
    .LI .x12 (21 : Word),
    .JAL .x1 (jalOff GuestAddrs.account_writes_latest_nonce_block (GuestAddrs.eip7702_authority_asof + 528)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LD .x9 .x2 (56 : BitVec 12),
    .LI .x18 (1 : Word),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.eip7702_authority_asof + 544)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.eip7702_authority_asof + 544)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_len (GuestAddrs.eip7702_authority_asof + 556)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_len (GuestAddrs.eip7702_authority_asof + 556)),
    .LD .x11 .x5 (0 : BitVec 12),
    .MV .x12 .x8,
    .LI .x13 (20 : Word),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_ptr (GuestAddrs.eip7702_authority_asof + 576)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_ptr (GuestAddrs.eip7702_authority_asof + 576)),
    .LD .x14 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_len (GuestAddrs.eip7702_authority_asof + 588)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_len (GuestAddrs.eip7702_authority_asof + 588)),
    .LD .x15 .x5 (0 : BitVec 12),
    .AUIPC .x16 (laHi GuestAddrs.teer_pre_acct (GuestAddrs.eip7702_authority_asof + 600)),
    .ADDI .x16 .x16 (laLo GuestAddrs.teer_pre_acct (GuestAddrs.eip7702_authority_asof + 600)),
    .JAL .x1 (jalOff GuestAddrs.account_at_header_state_root (GuestAddrs.eip7702_authority_asof + 608)),
    .BEQ .x10 .x0 (28 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (brOff (GuestAddrs.eip7702_authority_asof + 980) (GuestAddrs.eip7702_authority_asof + 620)),
    .LI .x10 (2 : Word),
    .LI .x11 (0 : Word),
    .LI .x12 (0 : Word),
    .JAL .x0 (jalOff (GuestAddrs.eip7702_authority_asof + 988) (GuestAddrs.eip7702_authority_asof + 636)),
    .BNE .x18 .x0 (16 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.teer_pre_acct (GuestAddrs.eip7702_authority_asof + 644)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_pre_acct (GuestAddrs.eip7702_authority_asof + 644)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.eip7702_authority_asof + 656)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_ptr (GuestAddrs.eip7702_authority_asof + 656)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sv_pre_rlp_len (GuestAddrs.eip7702_authority_asof + 668)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sv_pre_rlp_len (GuestAddrs.eip7702_authority_asof + 668)),
    .LD .x11 .x5 (0 : BitVec 12),
    .MV .x12 .x8,
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_ptr (GuestAddrs.eip7702_authority_asof + 684)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_ptr (GuestAddrs.eip7702_authority_asof + 684)),
    .LD .x13 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_witness_state_len (GuestAddrs.eip7702_authority_asof + 696)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_witness_state_len (GuestAddrs.eip7702_authority_asof + 696)),
    .LD .x14 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_ptr (GuestAddrs.eip7702_authority_asof + 708)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_ptr (GuestAddrs.eip7702_authority_asof + 708)),
    .LD .x15 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_len (GuestAddrs.eip7702_authority_asof + 720)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_len (GuestAddrs.eip7702_authority_asof + 720)),
    .LD .x16 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.code_at_header_state_root (GuestAddrs.eip7702_authority_asof + 732)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.eip7702_authority_asof + 840) (GuestAddrs.eip7702_authority_asof + 736)),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (brOff (GuestAddrs.eip7702_authority_asof + 944) (GuestAddrs.eip7702_authority_asof + 744)),
    .LI .x5 (5 : Word),
    .BNE .x10 .x5 (brOff (GuestAddrs.eip7702_authority_asof + 824) (GuestAddrs.eip7702_authority_asof + 752)),
    .AUIPC .x5 (laHi GuestAddrs.cahsr_acct_struct (GuestAddrs.eip7702_authority_asof + 756)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cahsr_acct_struct (GuestAddrs.eip7702_authority_asof + 756)),
    .AUIPC .x6 (laHi GuestAddrs.chahsr_empty_code_hash (GuestAddrs.eip7702_authority_asof + 764)),
    .ADDI .x6 .x6 (laLo GuestAddrs.chahsr_empty_code_hash (GuestAddrs.eip7702_authority_asof + 764)),
    .LD .x7 .x5 (72 : BitVec 12),
    .LD .x10 .x6 (0 : BitVec 12),
    .BNE .x7 .x10 (44 : BitVec 13),
    .LD .x7 .x5 (80 : BitVec 12),
    .LD .x10 .x6 (8 : BitVec 12),
    .BNE .x7 .x10 (32 : BitVec 13),
    .LD .x7 .x5 (88 : BitVec 12),
    .LD .x10 .x6 (16 : BitVec 12),
    .BNE .x7 .x10 (20 : BitVec 13),
    .LD .x7 .x5 (96 : BitVec 12),
    .LD .x10 .x6 (24 : BitVec 12),
    .BNE .x7 .x10 (8 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.eip7702_authority_asof + 948) (GuestAddrs.eip7702_authority_asof + 820)),
    .LI .x10 (2 : Word),
    .LI .x11 (0 : Word),
    .LI .x12 (0 : Word),
    .JAL .x0 (jalOff (GuestAddrs.eip7702_authority_asof + 992) (GuestAddrs.eip7702_authority_asof + 836)),
    .AUIPC .x5 (laHi GuestAddrs.cahsr_code_length (GuestAddrs.eip7702_authority_asof + 840)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cahsr_code_length (GuestAddrs.eip7702_authority_asof + 840)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BEQ .x5 .x0 (brOff (GuestAddrs.eip7702_authority_asof + 948) (GuestAddrs.eip7702_authority_asof + 852)),
    .LI .x6 (23 : Word),
    .BNE .x5 .x6 (brOff (GuestAddrs.eip7702_authority_asof + 932) (GuestAddrs.eip7702_authority_asof + 860)),
    .AUIPC .x5 (laHi GuestAddrs.svf_codes_ptr (GuestAddrs.eip7702_authority_asof + 864)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_codes_ptr (GuestAddrs.eip7702_authority_asof + 864)),
    .LD .x5 .x5 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.cahsr_code_offset (GuestAddrs.eip7702_authority_asof + 876)),
    .ADDI .x6 .x6 (laLo GuestAddrs.cahsr_code_offset (GuestAddrs.eip7702_authority_asof + 876)),
    .LD .x6 .x6 (0 : BitVec 12),
    .ADD .x5 .x5 .x6,
    .LBU .x6 .x5 (0 : BitVec 12),
    .LI .x7 (239 : Word),
    .BNE .x6 .x7 (32 : BitVec 13),
    .LBU .x6 .x5 (1 : BitVec 12),
    .LI .x7 (1 : Word),
    .BNE .x6 .x7 (20 : BitVec 13),
    .LBU .x6 .x5 (2 : BitVec 12),
    .BNE .x6 .x0 (12 : BitVec 13),
    .LI .x12 (1 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (3 : Word),
    .LI .x11 (0 : Word),
    .LI .x12 (0 : Word),
    .JAL .x0 (48 : BitVec 21),
    .LI .x12 (0 : Word),
    .BNE .x18 .x0 (16 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.teer_pre_acct (GuestAddrs.eip7702_authority_asof + 956)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_pre_acct (GuestAddrs.eip7702_authority_asof + 956)),
    .LD .x9 .x5 (0 : BitVec 12),
    .MV .x11 .x9,
    .LI .x10 (1 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (0 : Word),
    .LI .x11 (0 : Word),
    .LI .x12 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x13 .x2 (32 : BitVec 12),
    .LD .x14 .x2 (40 : BitVec 12),
    .LD .x15 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `eip7702AuthorityAsof_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def eip7702AuthorityAsof_relocs : RelocTable :=
  [ (13, .jal .x1 "account_writes_auth_current"),
    (19, .jal .x1 "account_writes_latest_nonce_tx"),
    (25, .jal .x1 "account_writes_auth_block"),
    (48, .la .x5 "sv_pre_rlp_ptr"),
    (51, .la .x5 "sv_pre_rlp_len"),
    (55, .la .x5 "bv_witness_state_ptr"),
    (58, .la .x5 "bv_witness_state_len"),
    (61, .la .x5 "svf_codes_ptr"),
    (64, .la .x5 "svf_codes_len"),
    (67, .jal .x1 "code_at_header_state_root"),
    (73, .la .x5 "cahsr_acct_struct"),
    (75, .la .x6 "chahsr_empty_code_hash"),
    (94, .la .x5 "cahsr_code_length"),
    (100, .la .x5 "svf_codes_ptr"),
    (103, .la .x6 "cahsr_code_offset"),
    (124, .jal .x1 "account_writes_latest_nonce_tx"),
    (132, .jal .x1 "account_writes_latest_nonce_block"),
    (136, .la .x5 "sv_pre_rlp_ptr"),
    (139, .la .x5 "sv_pre_rlp_len"),
    (144, .la .x5 "bv_witness_state_ptr"),
    (147, .la .x5 "bv_witness_state_len"),
    (150, .la .x16 "teer_pre_acct"),
    (152, .jal .x1 "account_at_header_state_root"),
    (161, .la .x5 "teer_pre_acct"),
    (164, .la .x5 "sv_pre_rlp_ptr"),
    (167, .la .x5 "sv_pre_rlp_len"),
    (171, .la .x5 "bv_witness_state_ptr"),
    (174, .la .x5 "bv_witness_state_len"),
    (177, .la .x5 "svf_codes_ptr"),
    (180, .la .x5 "svf_codes_len"),
    (183, .jal .x1 "code_at_header_state_root"),
    (189, .la .x5 "cahsr_acct_struct"),
    (191, .la .x6 "chahsr_empty_code_hash"),
    (210, .la .x5 "cahsr_code_length"),
    (216, .la .x5 "svf_codes_ptr"),
    (219, .la .x6 "cahsr_code_offset"),
    (239, .la .x5 "teer_pre_acct") ]

def eip7702AuthorityAsOfFunction : String :=
  "eip7702_authority_asof:\n" ++ emitProgramR eip7702AuthorityAsof_prog eip7702AuthorityAsof_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `eip7702AuthorityAsof_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem eip7702AuthorityAsOfFunction_eq_prog :
    eip7702AuthorityAsOfFunction = "eip7702_authority_asof:\n" ++ emitProgramR eip7702AuthorityAsof_prog eip7702AuthorityAsof_relocs := rfl

#guard eip7702AuthorityAsOfFunction.startsWith "eip7702_authority_asof:\n"
#guard eip7702AuthorityAsof_prog.length = 257
/-! ## eip7702_auth_state_prepare

    The live EIP-7702 intrinsic-state-gas writer.  Unlike the frozen legacy
    replay routine, this executes once at the transaction boundary and writes
    its accepted authorizations directly to the account-writes overlay.
    AccountState then provides the as-of state to the next transaction only
    after the ordinary success commit.

    a0/a1: inner RLP transaction bytes; a2: sender address; a3: tx type.
    This is the single execution-time traversal for EIP-7702 preparation:
    it charges the state-dependent costs, records the regular ACCOUNT_WRITE
    component, and writes accepted authorities to the account-writes
    overlay plus the BAL effects at the same authorization point. The dispatcher invokes it after the state-gas
    reservoir exists and before prepare_dispatch consumes the staged charge.
    Bad individual authorizations are ignored, matching `validate_authorization`.
    Malformed outer RLP returns one so the caller fails closed. -/
def eip7702AuthStatePrepareFunction : String :=
  "eip7702_auth_state_prepare:\n" ++
  "  addi sp, sp, -176; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp); sd a4, 136(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  la t0, runtime_tx_auth_state_refund; sd zero, 0(t0); la t0, runtime_tx_auth_state_charge; sd zero, 0(t0); la t0, runtime_tx_auth_regular_refund; sd zero, 0(t0); la t0, runtime_tx_top_frame_regular_gas; sd zero, 0(t0); la t0, teer_success_count; sd zero, 0(t0)\n" ++
  "  ld t0, 136(sp); li t1, -1; beq t0, t1, .L77prep_aggregate_mode; la t0, runtime_tx_auth_state_charged; li t1, 1; sd t1, 0(t0)\n" ++
  ".L77prep_aggregate_mode:\n" ++
  "  li t0, 4; bne s3, t0, .L77prep_ok\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 9; la a3, b1an_auth_off; la a4, b1an_auth_len; jal ra, rlp_list_nth_item; bnez a0, .L77prep_bad_outer\n" ++
  "  la t0, b1an_auth_off; ld t0, 0(t0); add s4, s0, t0; la t0, b1an_auth_len; ld s5, 0(t0)\n" ++
  "  mv a0, s4; mv a1, s5; la a2, b1an_auth_count; jal ra, rlp_list_count_items; bnez a0, .L77prep_bad_list\n" ++
  "  la t0, b1an_auth_count; ld s6, 0(t0); li s7, 0\n" ++
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
  "  la t0, runtime_tx_auth_state_charge; sd zero, 0(t0)\n" ++
  "  bgeu s7, s6, .L77prep_ok\n" ++
  "  mv a0, s4; mv a1, s5; mv a2, s7; la a3, b1an_item_off; la a4, b1an_item_len; jal ra, rlp_item_span; bnez a0, .L77prep_bad_span\n" ++
  "  la t0, b1an_item_off; ld t0, 0(t0); add s8, s4, t0; la t0, b1an_item_len; ld s9, 0(t0)\n" ++
  -- Chain id is a U256 in execution-specs.  For a canonical scalar wider
  -- than u64, validate it with the U256 decoder and skip this authorization:
  -- it cannot equal the u64 block chain id.  The U256 decoder preserves the
  -- fail-closed behavior for non-canonical or over-32-byte scalar content.
  "  mv a0, s8; mv a1, s9; li a2, 0; la a3, b1an_target_off; la a4, b1an_target_len; jal ra, rlp_list_nth_item; bnez a0, .L77prep_bad_chain; la t0, b1an_target_len; ld t0, 0(t0); li t1, 8; bltu t1, t0, .L77prep_chain_wide\n" ++
  "  mv a0, s8; mv a1, s9; li a2, 0; la a3, b1an_field; jal ra, rlp_field_to_u64_strict; bnez a0, .L77prep_bad_chain; la t0, b1an_field; ld t0, 0(t0); beqz t0, .L77prep_chain_ok; la t1, bv_chain_id; ld t1, 0(t1); bne t0, t1, .L77prep_next; j .L77prep_chain_ok\n" ++
  ".L77prep_chain_wide:\n" ++
  "  la t0, b1an_target_off; ld t0, 0(t0); add a0, s8, t0; la t0, b1an_target_len; ld a1, 0(t0); la a2, b1an_recover_scratch; jal ra, rlp_content_to_u256_be_strict; bnez a0, .L77prep_bad_chain; j .L77prep_next\n" ++
  ".L77prep_chain_ok:\n" ++
  "  mv a0, s8; mv a1, s9; li a2, 2; la a3, b1an_signed_nonce; jal ra, rlp_field_to_u64_strict; bnez a0, .L77prep_bad_nonce; la t0, b1an_signed_nonce; ld t0, 0(t0); li t1, -1; beq t0, t1, .L77prep_next\n" ++
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
  -- The MTx runtime has already published the sender's inclusion-time nonce
  -- to durable AccountState.  A self-sponsored authority therefore reads the
  -- same current transaction state as every other authority; no B1-derived
  -- `+1` compensation is needed here.
  "  la t0, b1an_signed_nonce; ld t0, 0(t0); ld t1, 112(sp)\n" ++
  "  bne t0, t1, .L77prep_next\n" ++
  -- COMPENSATION (two-pass guest versus one-pass spec): `teer_success_table`
  -- is a transaction-local first-write set only.  AccountState owns all
  -- cross-transaction state, while this bounded table implements the spec's
  -- one ACCOUNT_WRITE charge per authority per tx.  It is not a durable nonce
  -- overlay; the missing shared transaction overlay is the upstream fix that
  -- will make this compensation dead code.
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
  -- state charge = NEW_ACCOUNT iff absent, plus AUTH_BASE for a non-null
  -- delegation target when the current state is not already delegated.
  -- In the dispatcher callback, charge each authorization immediately after
  -- its account read/validation.  This matches eoa_delegation.py's
  -- recover/get_account ordering: an auth-phase OOG stops later auths while
  -- the account read itself remains visible.  The direct single-tx caller
  -- passes -1 and retains the aggregate compatibility path.
  "  ld t0, 104(sp); bnez t0, .L77prep_no_new; la t0, runtime_tx_auth_state_refund; ld t1, 0(t0); li t2, " ++ toString amsterdamNewAccountStateGas ++ "; add t1, t1, t2; sd t1, 0(t0); la t0, runtime_tx_auth_state_charge; ld t1, 0(t0); add t1, t1, t2; sd t1, 0(t0)\n" ++
  ".L77prep_no_new:\n" ++
  -- AUTH_BASE is charged (fall-through) iff s11 != 0 (non-null delegation
  -- target) AND 120(sp) == 0 (not delegated_before_tx) AND 168(sp) == 0
  -- (not already charged this tx via teer_success_table +20). Each failed
  -- conjunct branches to .L77prep_no_auth_base — the SKIP path, not the
  -- charge path (GH #11724). Spec: e5a8caf1b eoa_delegation.py:278.
  "  beqz s11, .L77prep_no_auth_base; ld t0, 120(sp); bnez t0, .L77prep_no_auth_base; ld t0, 168(sp); bnez t0, .L77prep_no_auth_base; la t0, runtime_tx_auth_state_refund; ld t1, 0(t0); li t2, " ++ toString (amsterdamStateBytesPerAuthBase * amsterdamCostPerStateByte) ++ "; add t1, t1, t2; sd t1, 0(t0); la t0, runtime_tx_auth_state_charge; ld t1, 0(t0); add t1, t1, t2; sd t1, 0(t0); li t0, 1; sw t0, 20(t4)\n" ++
  ".L77prep_no_auth_base:\n" ++
  "  ld t0, 136(sp); li t1, -1; beq t0, t1, .L77prep_auth_charge_done; la t0, runtime_tx_auth_state_charge; ld t1, 0(t0); beqz t1, .L77prep_auth_charge_done; la t2, evm_state_gas_left; ld t3, 0(t2); bgeu t3, t1, .L77prep_auth_charge_reservoir; sub t4, t1, t3; ld t0, 136(sp); bltu t0, t4, .L77prep_auth_charge_oog; sd zero, 0(t2); sub t0, t0, t4; sd t0, 136(sp); j .L77prep_auth_charge_used\n" ++
  ".L77prep_auth_charge_reservoir:\n" ++
  "  sub t3, t3, t1; sd t3, 0(t2)\n" ++
  ".L77prep_auth_charge_used:\n" ++
  "  la t2, runtime_tx_auth_state_charge; sd zero, 0(t2); j .L77prep_auth_charge_done\n" ++
  ".L77prep_auth_charge_oog:\n" ++
  -- Distinct from parse/RLP fail (a0=1): charge OOG is ExceptionalHalt of the
  -- tx (failed receipt), not a block-level prepare hard-fail. Callers map 2 →
  -- halted + a0=0 so MTx publishes status=0 without code 72.
  "  li a0, 2; j .L77prep_ret\n" ++
  ".L77prep_auth_charge_done:\n" ++
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
  -- Spec charges ACCOUNT_WRITE via charge_gas inside the set_delegation loop
  -- (eoa_delegation.py), so OOG aborts before later auths run validate /
  -- get_account. Deferring the debit to top_frame_regular_gas is fine for the
  -- actual subtract, but the live a4 budget must still gate here — otherwise
  -- an exact-intrinsic type-4 tx processes the rest of the list, asof-touches
  -- authorities the spec never reaches, and BAL grows empty shells (GH #11542
  -- 24498 multiple_signers_2: +27 b2ef). Aggregate a4=-1 keeps the old path.
  "  ld t0, 136(sp); li t1, -1; beq t0, t1, .L77prep_charge_regular_acc\n" ++
  "  la t2, runtime_tx_top_frame_regular_gas; ld t3, 0(t2); li t4, 8000; add t3, t3, t4; bltu t0, t3, .L77prep_auth_charge_oog\n" ++
  ".L77prep_charge_regular_acc:\n" ++
  "  la t0, runtime_tx_auth_regular_refund; ld t1, 0(t0); li t2, 8000; add t1, t1, t2; sd t1, 0(t0); la t0, runtime_tx_top_frame_regular_gas; ld t1, 0(t0); li t2, 8000; add t1, t1, t2; sd t1, 0(t0)\n" ++
  ".L77prep_record:\n" ++
  -- Build the stable delegation designator before publishing the account-write
  -- row.
  -- The same pointer is reused by the optional AccountWrite producer below;
  -- allocating twice would consume two block-lifetime slots for one auth.
  -- The account-write producer below is unconditional on the MTx-only path.
  "  beqz s11, .L77prep_state_code_null; la t0, eip7702_auth_code_next; ld t1, 0(t0); li t2, " ++ toString bvEip7702AuthEntryCapacity ++ "; bgeu t1, t2, .L77prep_bad_record; slli t3, t1, 3; slli t4, t1, 4; add t3, t3, t4; la t4, eip7702_auth_code_slots; add s8, t4, t3; addi t1, t1, 1; sd t1, 0(t0); li t0, 0xef; sb t0, 0(s8); li t0, 1; sb t0, 1(s8); sb zero, 2(s8); li t0, 0\n" ++
  ".L77prep_state_code_copy:\n" ++
  "  li t1, 20; beq t0, t1, .L77prep_state_code_ready; add t1, s10, t0; lbu t2, 0(t1); add t1, s8, t0; addi t1, t1, 3; sb t2, 0(t1); addi t0, t0, 1; j .L77prep_state_code_copy\n" ++
  ".L77prep_state_code_null:\n" ++
  "  li s8, 0\n" ++
  ".L77prep_state_code_ready:\n" ++
  -- execution-specs `eoa_delegation.py:set_delegation` installs the authority
  -- code and increments its nonce here, before message execution.  Publish the
  -- append-only code effect, nonce effect, and account-write row at this same
  -- point: the row receives the current transaction BAI rather than a
  -- post-runtime replay BAI.  Body REVERT restores only the post-preparation
  -- snapshot, so this auth record persists through a reverted message as in
  -- the spec.
  -- The code-effect log is deliberately written before runtime.  It is the
  -- execution-time source used by code-read suppression and code-effect
  -- comparators; the AccountWrite map below carries the actual marker bytes to
  -- the BAL builder in MTx mode.  Keep the record shape identical to the old
  -- comparator input: address, has_code_change = 1, code_len = 0.
  "  la t0, exec_code_effect_next; ld t1, 0(t0); addi t2, t1, 48; li t3, " ++ toString execCodeEffectLogCap ++ "; bgtu t2, t3, .L77prep_code_overflow\n" ++
  "  la t3, exec_code_effect_log; add t3, t3, t1; sd zero, 0(t3); sd zero, 8(t3); sd zero, 16(t3); sd zero, 24(t3)\n" ++
  "  la t4, b1an_authority; mv t5, t3; li t6, 20\n" ++
  ".L77prep_code_addr:\n" ++
  "  beqz t6, .L77prep_code_addr_done; lbu a0, 0(t4); sb a0, 0(t5); addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .L77prep_code_addr\n" ++
  ".L77prep_code_addr_done:\n" ++
  "  li t4, 1; sd t4, 32(t3); sd zero, 40(t3); la t0, exec_code_effect_count; ld t4, 0(t0); addi t4, t4, 1; sd t4, 0(t0); la t0, exec_code_effect_next; sd t2, 0(t0); j .L77prep_code_done\n" ++
  ".L77prep_code_overflow:\n" ++
  "  la t0, exec_code_effect_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".L77prep_code_done:\n" ++
  "  la a0, b1an_authority; la a1, nse_zero_bal; la a2, nse_zero_bal; ld a3, 112(sp); addi a4, a3, 1; jal ra, record_nonstorage_effect_nonce_only_after_account_state; bnez a0, .L77prep_bad_record\n" ++
  -- The direct single-tx lane has no account-write builder pass.  MTx records
  -- the same accepted authorization into the transaction map, reusing the
  -- AccountState producer's block-lifetime slot so the two consumers cannot
  -- observe different marker bytes.
  -- `set_delegation` in execution-specs (eoa_delegation.py:223-229) calls
  -- `set_code` and `increment_nonce`; both go through `modify_state`, so even
  -- an absent authority is written back as `Some Account`.  Keep `a5 = 1`
  -- and advertise that Optional-account state with the state-valid bit as well
  -- as nonce and code.  Retain TOUCHED: it is the sticky row-presence marker
  -- added by #11382, so an auth-only account cannot disappear from the map.
  "  la a0, b1an_authority; li a1, 0; ld a2, 112(sp); addi a2, a2, 1; mv a3, s8; li a4, 23; bnez s11, .L77prep_auth_code_record_emit; li a4, 0\n" ++
  ".L77prep_auth_code_record_emit:\n" ++
  -- The +96 EXEC_FLAGS table in AccountWriteMap.lean defines bit 2 as LIVE;
  -- this authorization row must carry that bit so later auth readers retain it.
  "  li a5, 1; li a6, " ++ toString (accountWriteHasNonce + accountWriteHasCode + accountWriteHasState + accountWriteHasExecFlags + accountWriteHasTouched) ++ "; li a7, 2\n" ++
  "  jal ra, account_write_record; j .L77prep_next\n" ++
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
  "  ld a4, 136(sp); ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp); addi sp, sp, 176; ret"

-- The widened scalar read is reached through typed-transaction field 9, then
-- authorization-tuple field 0.  Pin both emitted selectors: outer field 0 is
-- a U64 transaction chain id and must never take the U256 authorization path.
#guard eip7702AuthStatePrepareFunction.contains
  "li a2, 9; la a3, b1an_auth_off; la a4, b1an_auth_len; jal ra, rlp_list_nth_item"
#guard eip7702AuthStatePrepareFunction.contains
  "li a2, 0; la a3, b1an_target_off; la a4, b1an_target_len; jal ra, rlp_list_nth_item"
-- The authorization AccountWrite row is `Some Account` with nonce, code and
-- presence all valid.  Keep the state bit pinned so a future mask edit cannot
-- silently make Optional[Account] absence indistinguishable from zero fields.
#guard eip7702AuthStatePrepareFunction.contains
  "li a5, 1; li a6, 62; li a7, 2"
#guard eip7702AuthorityAsof_prog.contains
  (.LBU .x6 .x5 (0 : BitVec 12))
#guard eip7702AuthorityAsof_prog.contains
  (.LI .x7 (239 : Word))
#guard eip7702AuthorityAsof_prog.contains
  (.BNE .x6 .x7 (32 : BitVec 13))

/-- Live per-transaction intrinsic state-gas boundary.

    This replaces the former block-final replay/overlay: decode the transaction's
    ordinary intrinsic state charge and add the AccountState-as-of-this-tx
    EIP-7702 charge while both inputs are live.  The intrinsic decoder needs
    the full typed envelope, whereas authorization decoding needs the inner
    RLP payload; multi-tx contexts retain both representations. -/
def blockVerdictTxStateGasInlinePrepare_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x10 (8 : BitVec 12),
    .SD .x2 .x11 (16 : BitVec 12),
    .SD .x2 .x12 (24 : BitVec 12),
    .SD .x2 .x13 (32 : BitVec 12),
    .SD .x2 .x14 (40 : BitVec 12),
    .SD .x2 .x15 (48 : BitVec 12),
    .SD .x2 .x16 (56 : BitVec 12),
    .SLLI .x5 .x16 (3 : BitVec 6),
    .AUIPC .x6 (laHi GuestAddrs.bvgr_tx_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 40)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvgr_tx_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 40)),
    .ADD .x12 .x6 .x5,
    .AUIPC .x6 (laHi GuestAddrs.runtime_tx_state_gas_ptr (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 52)),
    .ADDI .x6 .x6 (laLo GuestAddrs.runtime_tx_state_gas_ptr (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 52)),
    .SD .x6 .x12 (0 : BitVec 12),
    .LD .x10 .x2 (8 : BitVec 12),
    .LD .x11 .x2 (16 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_intrinsic_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 72)),
    .BNE .x10 .x0 (brOff (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 796) (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 76)),
    .LD .x5 .x2 (56 : BitVec 12),
    .SLLI .x5 .x5 (3 : BitVec 6),
    .AUIPC .x6 (laHi GuestAddrs.bvgr_tx_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 88)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvgr_tx_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 88)),
    .ADD .x6 .x6 .x5,
    .LD .x7 .x6 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_nonstorage_effect_count (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 104)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_nonstorage_effect_count (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 104)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_effect_count_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 116)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_effect_count_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 116)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_nonstorage_effect_overflow (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 128)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_nonstorage_effect_overflow (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 128)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_effect_overflow_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 140)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_effect_overflow_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 140)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_code_effect_count (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 152)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_code_effect_count (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 152)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_code_effect_count_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 164)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_code_effect_count_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 164)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_code_effect_next (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 176)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_code_effect_next (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 176)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_code_effect_next_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 188)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_code_effect_next_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 188)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_code_effect_overflow (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 200)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_code_effect_overflow (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 200)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_code_effect_overflow_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 212)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_code_effect_overflow_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 212)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bv_mtx_ctx (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 224)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bv_mtx_ctx (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 224)),
    .JAL .x1 (jalOff GuestAddrs.simple_transfer_intrinsic_gas (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 232)),
    .BNE .x10 .x0 (brOff (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 796) (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 236)),
    .MV .x7 .x11,
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_calldata_floor (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 244)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_calldata_floor (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 244)),
    .SD .x5 .x12 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_runtime_calldata_floor (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 256)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_runtime_calldata_floor (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 256)),
    .SD .x5 .x12 (0 : BitVec 12),
    .LD .x5 .x2 (56 : BitVec 12),
    .SLLI .x5 .x5 (3 : BitVec 6),
    .AUIPC .x6 (laHi GuestAddrs.bvgr_tx_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 276)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvgr_tx_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 276)),
    .ADD .x6 .x6 .x5,
    .LD .x28 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_mtx_ctx (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 292)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_mtx_ctx (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 292)),
    .LD .x29 .x5 (40 : BitVec 12),
    .ADD .x30 .x7 .x28,
    .BLTU .x29 .x30 (brOff (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 796) (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 308)),
    .SUB .x30 .x29 .x30,
    .LUI .x31 (4096 : BitVec 20),
    .BGEU .x7 .x31 (brOff (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 796) (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 320)),
    .SUB .x31 .x31 .x7,
    .AUIPC .x6 (laHi GuestAddrs.evm_state_gas_left (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 328)),
    .ADDI .x6 .x6 (laLo GuestAddrs.evm_state_gas_left (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 328)),
    .SD .x6 .x0 (0 : BitVec 12),
    .BGEU .x31 .x30 (20 : BitVec 13),
    .SUB .x5 .x30 .x31,
    .SD .x6 .x5 (0 : BitVec 12),
    .MV .x14 .x31,
    .JAL .x0 (8 : BitVec 21),
    .MV .x14 .x30,
    .AUIPC .x6 (laHi GuestAddrs.evm_state_gas_spilled (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 364)),
    .ADDI .x6 .x6 (laLo GuestAddrs.evm_state_gas_spilled (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 364)),
    .LD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.runtime_tx_state_gas_message_spilled (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 376)),
    .ADDI .x6 .x6 (laLo GuestAddrs.runtime_tx_state_gas_message_spilled (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 376)),
    .SD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.evm_state_gas_left (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 388)),
    .ADDI .x6 .x6 (laLo GuestAddrs.evm_state_gas_left (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 388)),
    .LD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.runtime_tx_state_gas_message_left (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 400)),
    .ADDI .x6 .x6 (laLo GuestAddrs.runtime_tx_state_gas_message_left (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 400)),
    .SD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.runtime_tx_state_reservoir_initial (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 412)),
    .ADDI .x6 .x6 (laLo GuestAddrs.runtime_tx_state_reservoir_initial (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 412)),
    .SD .x6 .x5 (0 : BitVec 12),
    .LI .x5 (1 : Word),
    .AUIPC .x6 (laHi GuestAddrs.runtime_tx_state_gas_entry_valid (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 428)),
    .ADDI .x6 .x6 (laLo GuestAddrs.runtime_tx_state_gas_entry_valid (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 428)),
    .SD .x6 .x5 (0 : BitVec 12),
    .LD .x10 .x2 (24 : BitVec 12),
    .LD .x11 .x2 (32 : BitVec 12),
    .LD .x12 .x2 (40 : BitVec 12),
    .LD .x13 .x2 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.eip7702_auth_state_prepare (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 456)),
    .AUIPC .x5 (laHi GuestAddrs.evm_state_gas_left (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 460)),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_state_gas_left (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 460)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_state_gas_message_left (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 472)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_state_gas_message_left (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 472)),
    .LD .x7 .x5 (0 : BitVec 12),
    .SUB .x7 .x7 .x6,
    .AUIPC .x5 (laHi GuestAddrs.evm_state_gas_spilled (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 488)),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_state_gas_spilled (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 488)),
    .LD .x28 .x5 (0 : BitVec 12),
    .ADD .x7 .x7 .x28,
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_state_gas_message_spilled (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 504)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_state_gas_message_spilled (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 504)),
    .LD .x28 .x5 (0 : BitVec 12),
    .SUB .x7 .x7 .x28,
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_auth_state_used (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 520)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_auth_state_used (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 520)),
    .SD .x5 .x7 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_state_gas_message_left (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 532)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_state_gas_message_left (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 532)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.evm_state_gas_spilled (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 544)),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_state_gas_spilled (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 544)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_state_gas_message_spilled (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 556)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_state_gas_message_spilled (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 556)),
    .SD .x5 .x0 (0 : BitVec 12),
    .BEQ .x10 .x0 (brOff (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 764) (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 568)),
    .LI .x6 (2 : Word),
    .BEQ .x10 .x6 (8 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 796) (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 580)),
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_auth_phase_halted (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 584)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_auth_phase_halted (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 584)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_effect_count_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 600)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_effect_count_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 600)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_nonstorage_effect_count (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 612)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_nonstorage_effect_count (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 612)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_effect_overflow_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 624)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_effect_overflow_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 624)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_nonstorage_effect_overflow (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 636)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_nonstorage_effect_overflow (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 636)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_code_effect_count_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 648)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_code_effect_count_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 648)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_code_effect_count (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 660)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_code_effect_count (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 660)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_code_effect_next_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 672)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_code_effect_next_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 672)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_code_effect_next (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 684)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_code_effect_next (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 684)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_code_effect_overflow_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 696)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_code_effect_overflow_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 696)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_code_effect_overflow (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 708)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_code_effect_overflow (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 708)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_regular_refund (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 720)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_regular_refund (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 720)),
    .SD .x28 .x0 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_top_frame_regular_gas (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 732)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_top_frame_regular_gas (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 732)),
    .SD .x28 .x0 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.teer_success_count (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 744)),
    .ADDI .x28 .x28 (laLo GuestAddrs.teer_success_count (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 744)),
    .SD .x28 .x0 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (52 : BitVec 21),
    .LD .x5 .x2 (48 : BitVec 12),
    .LI .x6 (4 : Word),
    .BNE .x5 .x6 (40 : BitVec 13),
    .LI .x6 (1 : Word),
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_auth_prepared (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 780)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_auth_prepared (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 780)),
    .SD .x5 .x6 (0 : BitVec 12),
    .JAL .x0 (20 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_auth_phase_halted (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 796)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_auth_phase_halted (GuestAddrs.block_verdict_tx_state_gas_inline_prepare + 796)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blockVerdictTxStateGasInlinePrepare_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blockVerdictTxStateGasInlinePrepare_relocs : RelocTable :=
  [ (10, .la .x6 "bvgr_tx_state_gas"),
    (13, .la .x6 "runtime_tx_state_gas_ptr"),
    (18, .jal .x1 "tx_intrinsic_state_gas"),
    (22, .la .x6 "bvgr_tx_state_gas"),
    (26, .la .x28 "exec_nonstorage_effect_count"),
    (29, .la .x28 "runtime_tx_auth_effect_count_checkpoint"),
    (32, .la .x28 "exec_nonstorage_effect_overflow"),
    (35, .la .x28 "runtime_tx_auth_effect_overflow_checkpoint"),
    (38, .la .x28 "exec_code_effect_count"),
    (41, .la .x28 "runtime_tx_auth_code_effect_count_checkpoint"),
    (44, .la .x28 "exec_code_effect_next"),
    (47, .la .x28 "runtime_tx_auth_code_effect_next_checkpoint"),
    (50, .la .x28 "exec_code_effect_overflow"),
    (53, .la .x28 "runtime_tx_auth_code_effect_overflow_checkpoint"),
    (56, .la .x10 "bv_mtx_ctx"),
    (58, .jal .x1 "simple_transfer_intrinsic_gas"),
    (61, .la .x5 "runtime_tx_calldata_floor"),
    (64, .la .x5 "bv_runtime_calldata_floor"),
    (69, .la .x6 "bvgr_tx_state_gas"),
    (73, .la .x5 "bv_mtx_ctx"),
    (82, .la .x6 "evm_state_gas_left"),
    (91, .la .x6 "evm_state_gas_spilled"),
    (94, .la .x6 "runtime_tx_state_gas_message_spilled"),
    (97, .la .x6 "evm_state_gas_left"),
    (100, .la .x6 "runtime_tx_state_gas_message_left"),
    (103, .la .x6 "runtime_tx_state_reservoir_initial"),
    (107, .la .x6 "runtime_tx_state_gas_entry_valid"),
    (114, .jal .x1 "eip7702_auth_state_prepare"),
    (115, .la .x5 "evm_state_gas_left"),
    (118, .la .x5 "runtime_tx_state_gas_message_left"),
    (122, .la .x5 "evm_state_gas_spilled"),
    (126, .la .x5 "runtime_tx_state_gas_message_spilled"),
    (130, .la .x5 "runtime_tx_auth_state_used"),
    (133, .la .x5 "runtime_tx_state_gas_message_left"),
    (136, .la .x5 "evm_state_gas_spilled"),
    (139, .la .x5 "runtime_tx_state_gas_message_spilled"),
    (146, .la .x5 "runtime_tx_auth_phase_halted"),
    (150, .la .x28 "runtime_tx_auth_effect_count_checkpoint"),
    (153, .la .x28 "exec_nonstorage_effect_count"),
    (156, .la .x28 "runtime_tx_auth_effect_overflow_checkpoint"),
    (159, .la .x28 "exec_nonstorage_effect_overflow"),
    (162, .la .x28 "runtime_tx_auth_code_effect_count_checkpoint"),
    (165, .la .x28 "exec_code_effect_count"),
    (168, .la .x28 "runtime_tx_auth_code_effect_next_checkpoint"),
    (171, .la .x28 "exec_code_effect_next"),
    (174, .la .x28 "runtime_tx_auth_code_effect_overflow_checkpoint"),
    (177, .la .x28 "exec_code_effect_overflow"),
    (180, .la .x28 "runtime_tx_auth_regular_refund"),
    (183, .la .x28 "runtime_tx_top_frame_regular_gas"),
    (186, .la .x28 "teer_success_count"),
    (195, .la .x5 "runtime_tx_auth_prepared"),
    (199, .la .x5 "runtime_tx_auth_phase_halted") ]

def blockVerdictTxStateGasInlinePrepareFunction : String :=
  "block_verdict_tx_state_gas_inline_prepare:\n" ++ emitProgramR blockVerdictTxStateGasInlinePrepare_prog blockVerdictTxStateGasInlinePrepare_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blockVerdictTxStateGasInlinePrepare_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blockVerdictTxStateGasInlinePrepareFunction_eq_prog :
    blockVerdictTxStateGasInlinePrepareFunction = "block_verdict_tx_state_gas_inline_prepare:\n" ++ emitProgramR blockVerdictTxStateGasInlinePrepare_prog blockVerdictTxStateGasInlinePrepare_relocs := rfl

#guard blockVerdictTxStateGasInlinePrepareFunction.startsWith "block_verdict_tx_state_gas_inline_prepare:\n"
#guard blockVerdictTxStateGasInlinePrepare_prog.length = 206
/-- Complete the live per-transaction state-gas cell after execution settles.

    State refunds are presently represented by the zero-initialized
    `bvgr_tx_state_refund` substrate, so the exact current identity is the
    intrinsic/auth charge plus executed state gas for successful transactions.
    Failed transactions retain only the intrinsic/auth component. -/
def blockVerdictTxStateGasInlineFinalize_prog : Program :=
  [ .SLLI .x5 .x10 (3 : BitVec 6),
    .AUIPC .x6 (laHi GuestAddrs.bvgr_tx_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 4)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvgr_tx_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 4)),
    .ADD .x6 .x6 .x5,
    .LD .x7 .x6 (0 : BitVec 12),
    .BNE .x11 .x0 (brOff (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 196) (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 20)),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_phase_halted (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 24)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_phase_halted (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 24)),
    .LD .x28 .x28 (0 : BitVec 12),
    .BEQ .x28 .x0 (brOff (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 216) (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 36)),
    .SD .x6 .x0 (0 : BitVec 12),
    .LI .x7 (0 : Word),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_effect_count_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 48)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_effect_count_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 48)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_nonstorage_effect_count (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 60)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_nonstorage_effect_count (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 60)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_effect_overflow_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 72)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_effect_overflow_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 72)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_nonstorage_effect_overflow (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 84)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_nonstorage_effect_overflow (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 84)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_code_effect_count_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 96)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_code_effect_count_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 96)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_code_effect_count (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 108)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_code_effect_count (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 108)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_code_effect_next_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 120)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_code_effect_next_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 120)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_code_effect_next (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 132)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_code_effect_next (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 132)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_code_effect_overflow_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 144)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_code_effect_overflow_checkpoint (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 144)),
    .LD .x29 .x28 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.exec_code_effect_overflow (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 156)),
    .ADDI .x28 .x28 (laLo GuestAddrs.exec_code_effect_overflow (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 156)),
    .SD .x28 .x29 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_auth_regular_refund (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 168)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_auth_regular_refund (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 168)),
    .SD .x28 .x0 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.runtime_tx_top_frame_regular_gas (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 180)),
    .ADDI .x28 .x28 (laLo GuestAddrs.runtime_tx_top_frame_regular_gas (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 180)),
    .SD .x28 .x0 (0 : BitVec 12),
    .JAL .x0 (24 : BitVec 21),
    .AUIPC .x28 (laHi GuestAddrs.bvgr_tx_exec_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 196)),
    .ADDI .x28 .x28 (laLo GuestAddrs.bvgr_tx_exec_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 196)),
    .ADD .x28 .x28 .x5,
    .LD .x28 .x28 (0 : BitVec 12),
    .ADD .x7 .x7 .x28,
    .AUIPC .x6 (laHi GuestAddrs.bvgr_tx_total_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 216)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvgr_tx_total_state_gas (GuestAddrs.block_verdict_tx_state_gas_inline_finalize + 216)),
    .ADD .x6 .x6 .x5,
    .SD .x6 .x7 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blockVerdictTxStateGasInlineFinalize_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blockVerdictTxStateGasInlineFinalize_relocs : RelocTable :=
  [ (1, .la .x6 "bvgr_tx_state_gas"),
    (6, .la .x28 "runtime_tx_auth_phase_halted"),
    (12, .la .x28 "runtime_tx_auth_effect_count_checkpoint"),
    (15, .la .x28 "exec_nonstorage_effect_count"),
    (18, .la .x28 "runtime_tx_auth_effect_overflow_checkpoint"),
    (21, .la .x28 "exec_nonstorage_effect_overflow"),
    (24, .la .x28 "runtime_tx_auth_code_effect_count_checkpoint"),
    (27, .la .x28 "exec_code_effect_count"),
    (30, .la .x28 "runtime_tx_auth_code_effect_next_checkpoint"),
    (33, .la .x28 "exec_code_effect_next"),
    (36, .la .x28 "runtime_tx_auth_code_effect_overflow_checkpoint"),
    (39, .la .x28 "exec_code_effect_overflow"),
    (42, .la .x28 "runtime_tx_auth_regular_refund"),
    (45, .la .x28 "runtime_tx_top_frame_regular_gas"),
    (49, .la .x28 "bvgr_tx_exec_state_gas"),
    (54, .la .x6 "bvgr_tx_total_state_gas") ]

def blockVerdictTxStateGasInlineFinalizeFunction : String :=
  "block_verdict_tx_state_gas_inline_finalize:\n" ++ emitProgramR blockVerdictTxStateGasInlineFinalize_prog blockVerdictTxStateGasInlineFinalize_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blockVerdictTxStateGasInlineFinalize_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blockVerdictTxStateGasInlineFinalizeFunction_eq_prog :
    blockVerdictTxStateGasInlineFinalizeFunction = "block_verdict_tx_state_gas_inline_finalize:\n" ++ emitProgramR blockVerdictTxStateGasInlineFinalize_prog blockVerdictTxStateGasInlineFinalize_relocs := rfl

#guard blockVerdictTxStateGasInlineFinalizeFunction.startsWith "block_verdict_tx_state_gas_inline_finalize:\n"
#guard blockVerdictTxStateGasInlineFinalize_prog.length = 60
end EvmAsm.Codegen
