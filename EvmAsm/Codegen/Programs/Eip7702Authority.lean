/-
  EvmAsm.Codegen.Programs.Eip7702Authority

  EIP-7702 authorization authority recovery. This is the reusable bridge
  between an authorization tuple and the 20-byte authority address needed by
  static set-delegation accounting.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Address
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Secp256k1Curve
import EvmAsm.Codegen.Programs.Secp256k1Recover
import EvmAsm.Codegen.Programs.TxSignature
import EvmAsm.Codegen.Programs.TxSigningHash
import EvmAsm.Codegen.Programs.TxPubkey
import EvmAsm.Codegen.Programs.U256

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## eip7702_authorization_recover_address

    Recover the authority/delegator address for one EIP-7702 authorization tuple:

      authorization = rlp([chain_id, address, nonce, y_parity, r, s])
      signing_hash  = keccak256(0x05 || rlp([chain_id, address, nonce]))
      authority     = address_from_pubkey(secp256k1_recover(signing_hash, r, s, y_parity))

    Calling convention:
      a0 (input)  : authorization tuple RLP ptr
      a1 (input)  : authorization tuple byte length
      a2 (input)  : 20-byte authority address output ptr
      a3 (input)  : scratch ptr, >= 360 bytes, 8-byte aligned
      ra (input)  : return
      a0 (output) : status

    Scratch layout:
      +0    tx_pubkey-style material block (128 bytes)
      +128  staged ecrecover ABI block (168 bytes)
      +296  recovered public key x||y (64 bytes)

    Status:
      0  success
      10 signature extraction failed
      20 signing hash failed
      31 bad y_parity
      40 r is zero
      41 s is zero
      42 r >= secp256k1n
      43 s > secp256k1n / 2
      50 ecrecover ABI staging failed
      60 secp256k1 recovery failed -/
def eip7702AuthorizationRecoverAddress_prog : Program :=
  [ .ADDI .x2 .x2 (-56 : BitVec 12),
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
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x18 .x0 (8 : BitVec 12),
    .SW .x18 .x0 (16 : BitVec 12),
    .MV .x5 .x19,
    .LI .x6 (16 : Word),
    .SD .x5 .x0 (0 : BitVec 12),
    .ADDI .x5 .x5 (8 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .BNE .x6 .x0 (-12 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .ADDI .x12 .x19 (8 : BitVec 12),
    .ADDI .x13 .x19 (16 : BitVec 12),
    .ADDI .x14 .x19 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.eip7702_authorization_extract_signature (GuestAddrs.eip7702_authorization_recover_address + 104)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (10 : Word),
    .JAL .x0 (252 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .ADDI .x12 .x19 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.eip7702_authorization_signing_hash (GuestAddrs.eip7702_authorization_recover_address + 132)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (20 : Word),
    .JAL .x0 (224 : BitVec 21),
    .LD .x5 .x19 (8 : BitVec 12),
    .LI .x6 (1 : Word),
    .BLTU .x6 .x5 (176 : BitVec 13),
    .ADDI .x10 .x19 (16 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.u256_is_zero (GuestAddrs.eip7702_authorization_recover_address + 164)),
    .BNE .x10 .x0 (172 : BitVec 13),
    .ADDI .x10 .x19 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.u256_is_zero (GuestAddrs.eip7702_authorization_recover_address + 176)),
    .BNE .x10 .x0 (168 : BitVec 13),
    .ADDI .x10 .x19 (16 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.a77ra_secp256k1_n (GuestAddrs.eip7702_authorization_recover_address + 188)),
    .ADDI .x11 .x11 (laLo GuestAddrs.a77ra_secp256k1_n (GuestAddrs.eip7702_authorization_recover_address + 188)),
    .AUIPC .x12 (laHi GuestAddrs.a77ra_cmp (GuestAddrs.eip7702_authorization_recover_address + 196)),
    .ADDI .x12 .x12 (laLo GuestAddrs.a77ra_cmp (GuestAddrs.eip7702_authorization_recover_address + 196)),
    .JAL .x1 (jalOff GuestAddrs.u256_lt_be (GuestAddrs.eip7702_authorization_recover_address + 204)),
    .AUIPC .x5 (laHi GuestAddrs.a77ra_cmp (GuestAddrs.eip7702_authorization_recover_address + 208)),
    .ADDI .x5 .x5 (laLo GuestAddrs.a77ra_cmp (GuestAddrs.eip7702_authorization_recover_address + 208)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (136 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.a77ra_secp256k1_half_n (GuestAddrs.eip7702_authorization_recover_address + 224)),
    .ADDI .x10 .x10 (laLo GuestAddrs.a77ra_secp256k1_half_n (GuestAddrs.eip7702_authorization_recover_address + 224)),
    .ADDI .x11 .x19 (48 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.a77ra_cmp (GuestAddrs.eip7702_authorization_recover_address + 236)),
    .ADDI .x12 .x12 (laLo GuestAddrs.a77ra_cmp (GuestAddrs.eip7702_authorization_recover_address + 236)),
    .JAL .x1 (jalOff GuestAddrs.u256_lt_be (GuestAddrs.eip7702_authorization_recover_address + 244)),
    .AUIPC .x5 (laHi GuestAddrs.a77ra_cmp (GuestAddrs.eip7702_authorization_recover_address + 248)),
    .ADDI .x5 .x5 (laLo GuestAddrs.a77ra_cmp (GuestAddrs.eip7702_authorization_recover_address + 248)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BNE .x6 .x0 (104 : BitVec 13),
    .MV .x10 .x19,
    .ADDI .x11 .x19 (128 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_pubkey_ecrecover_stage_material (GuestAddrs.eip7702_authorization_recover_address + 272)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (50 : Word),
    .JAL .x0 (84 : BitVec 21),
    .ADDI .x10 .x19 (128 : BitVec 12),
    .ADDI .x11 .x19 (296 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.secp256k1_recover_pubkey_staged (GuestAddrs.eip7702_authorization_recover_address + 296)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (60 : Word),
    .JAL .x0 (60 : BitVec 21),
    .ADDI .x10 .x19 (296 : BitVec 12),
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.address_from_pubkey (GuestAddrs.eip7702_authorization_recover_address + 320)),
    .LI .x10 (0 : Word),
    .JAL .x0 (40 : BitVec 21),
    .LI .x10 (31 : Word),
    .JAL .x0 (32 : BitVec 21),
    .LI .x10 (40 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (41 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (42 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (43 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `eip7702AuthorizationRecoverAddress_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def eip7702AuthorizationRecoverAddress_relocs : RelocTable :=
  [ (26, .jal .x1 "eip7702_authorization_extract_signature"),
    (33, .jal .x1 "eip7702_authorization_signing_hash"),
    (41, .jal .x1 "u256_is_zero"),
    (44, .jal .x1 "u256_is_zero"),
    (47, .la .x11 "a77ra_secp256k1_n"),
    (49, .la .x12 "a77ra_cmp"),
    (51, .jal .x1 "u256_lt_be"),
    (52, .la .x5 "a77ra_cmp"),
    (56, .la .x10 "a77ra_secp256k1_half_n"),
    (59, .la .x12 "a77ra_cmp"),
    (61, .jal .x1 "u256_lt_be"),
    (62, .la .x5 "a77ra_cmp"),
    (68, .jal .x1 "tx_pubkey_ecrecover_stage_material"),
    (74, .jal .x1 "secp256k1_recover_pubkey_staged"),
    (80, .jal .x1 "address_from_pubkey") ]

def eip7702AuthorizationRecoverAddressFunction : String :=
  "eip7702_authorization_recover_address:\n" ++ emitProgramR eip7702AuthorizationRecoverAddress_prog eip7702AuthorizationRecoverAddress_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `eip7702AuthorizationRecoverAddress_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem eip7702AuthorizationRecoverAddressFunction_eq_prog :
    eip7702AuthorizationRecoverAddressFunction = "eip7702_authorization_recover_address:\n" ++ emitProgramR eip7702AuthorizationRecoverAddress_prog eip7702AuthorizationRecoverAddress_relocs := rfl

#guard eip7702AuthorizationRecoverAddressFunction.startsWith "eip7702_authorization_recover_address:\n"
#guard eip7702AuthorizationRecoverAddress_prog.length = 101
/-! ## eip7702_warm_recovered_authorities

    coc3g.5 (multi-hop authority warming). Mirror execution-specs amsterdam
    `eoa_delegation.validate_authorization`: for every authorization in the type-4
    tx's authorization_list, warm the RECOVERED authority into the EIP-2929 runtime
    account warm set (`message.accessed_addresses.add(authority)`), gated EXACTLY on
    the spec's pre-recovery conditions — and NOTHING more (warming less than the spec
    over-charges = safe; warming more = under-charge = false-accept, so the gate is
    tight):

      * `auth.chain_id in (block_env.chain_id, 0)`   (bv_chain_id)
      * `auth.nonce < U64.MAX_VALUE`                 (skip nonce == 2^64-1)
      * `recover_authority(auth)` succeeds            (valid secp256k1 signature)

    The spec adds the authority to accessed_addresses BEFORE the
    `authority_code is valid delegation` and `authority_nonce == auth.nonce` checks,
    so warming is INDEPENDENT of those — every recovered authority on a chain/nonce-
    valid auth is warmed even if it ultimately fails to install a delegation.

    Calling convention:
      a0 = authorization_list RLP ptr   a1 = authorization_list RLP length
    Clobbers a0..a7, t0..t6; saves the s-registers it uses. Returns nothing
    (a failed parse leaves the warm set unchanged = conservative over-charge). -/
def eip7702WarmRecoveredAuthorities_prog : Program :=
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
    .BEQ .x8 .x0 (brOff (GuestAddrs.eip7702_warm_recovered_authorities + 364) (GuestAddrs.eip7702_warm_recovered_authorities + 40)),
    .BEQ .x9 .x0 (brOff (GuestAddrs.eip7702_warm_recovered_authorities + 364) (GuestAddrs.eip7702_warm_recovered_authorities + 44)),
    .AUIPC .x5 (laHi GuestAddrs.bv_chain_id (GuestAddrs.eip7702_warm_recovered_authorities + 48)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_chain_id (GuestAddrs.eip7702_warm_recovered_authorities + 48)),
    .LD .x20 .x5 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.e77w_count (GuestAddrs.eip7702_warm_recovered_authorities + 68)),
    .ADDI .x12 .x12 (laLo GuestAddrs.e77w_count (GuestAddrs.eip7702_warm_recovered_authorities + 68)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.eip7702_warm_recovered_authorities + 76)),
    .BNE .x10 .x0 (brOff (GuestAddrs.eip7702_warm_recovered_authorities + 364) (GuestAddrs.eip7702_warm_recovered_authorities + 80)),
    .AUIPC .x5 (laHi GuestAddrs.e77w_count (GuestAddrs.eip7702_warm_recovered_authorities + 84)),
    .ADDI .x5 .x5 (laLo GuestAddrs.e77w_count (GuestAddrs.eip7702_warm_recovered_authorities + 84)),
    .LD .x18 .x5 (0 : BitVec 12),
    .LI .x19 (0 : Word),
    .BEQ .x19 .x18 (brOff (GuestAddrs.eip7702_warm_recovered_authorities + 364) (GuestAddrs.eip7702_warm_recovered_authorities + 100)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x19,
    .AUIPC .x13 (laHi GuestAddrs.e77w_toff (GuestAddrs.eip7702_warm_recovered_authorities + 116)),
    .ADDI .x13 .x13 (laLo GuestAddrs.e77w_toff (GuestAddrs.eip7702_warm_recovered_authorities + 116)),
    .AUIPC .x14 (laHi GuestAddrs.e77w_tlen (GuestAddrs.eip7702_warm_recovered_authorities + 124)),
    .ADDI .x14 .x14 (laLo GuestAddrs.e77w_tlen (GuestAddrs.eip7702_warm_recovered_authorities + 124)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.eip7702_warm_recovered_authorities + 132)),
    .BNE .x10 .x0 (brOff (GuestAddrs.eip7702_warm_recovered_authorities + 356) (GuestAddrs.eip7702_warm_recovered_authorities + 136)),
    .AUIPC .x5 (laHi GuestAddrs.e77w_toff (GuestAddrs.eip7702_warm_recovered_authorities + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.e77w_toff (GuestAddrs.eip7702_warm_recovered_authorities + 140)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x21 .x8 .x6,
    .AUIPC .x5 (laHi GuestAddrs.e77w_tlen (GuestAddrs.eip7702_warm_recovered_authorities + 156)),
    .ADDI .x5 .x5 (laLo GuestAddrs.e77w_tlen (GuestAddrs.eip7702_warm_recovered_authorities + 156)),
    .LD .x7 .x5 (0 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.e77w_tlen (GuestAddrs.eip7702_warm_recovered_authorities + 168)),
    .ADDI .x28 .x28 (laLo GuestAddrs.e77w_tlen (GuestAddrs.eip7702_warm_recovered_authorities + 168)),
    .LD .x11 .x28 (0 : BitVec 12),
    .MV .x10 .x21,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.e77w_chain (GuestAddrs.eip7702_warm_recovered_authorities + 188)),
    .ADDI .x13 .x13 (laLo GuestAddrs.e77w_chain (GuestAddrs.eip7702_warm_recovered_authorities + 188)),
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict (GuestAddrs.eip7702_warm_recovered_authorities + 196)),
    .BNE .x10 .x0 (brOff (GuestAddrs.eip7702_warm_recovered_authorities + 356) (GuestAddrs.eip7702_warm_recovered_authorities + 200)),
    .AUIPC .x5 (laHi GuestAddrs.e77w_chain (GuestAddrs.eip7702_warm_recovered_authorities + 204)),
    .ADDI .x5 .x5 (laLo GuestAddrs.e77w_chain (GuestAddrs.eip7702_warm_recovered_authorities + 204)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (8 : BitVec 13),
    .BNE .x6 .x20 (brOff (GuestAddrs.eip7702_warm_recovered_authorities + 356) (GuestAddrs.eip7702_warm_recovered_authorities + 220)),
    .AUIPC .x28 (laHi GuestAddrs.e77w_tlen (GuestAddrs.eip7702_warm_recovered_authorities + 224)),
    .ADDI .x28 .x28 (laLo GuestAddrs.e77w_tlen (GuestAddrs.eip7702_warm_recovered_authorities + 224)),
    .LD .x11 .x28 (0 : BitVec 12),
    .MV .x10 .x21,
    .LI .x12 (2 : Word),
    .AUIPC .x13 (laHi GuestAddrs.e77w_nonce (GuestAddrs.eip7702_warm_recovered_authorities + 244)),
    .ADDI .x13 .x13 (laLo GuestAddrs.e77w_nonce (GuestAddrs.eip7702_warm_recovered_authorities + 244)),
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict (GuestAddrs.eip7702_warm_recovered_authorities + 252)),
    .BNE .x10 .x0 (brOff (GuestAddrs.eip7702_warm_recovered_authorities + 356) (GuestAddrs.eip7702_warm_recovered_authorities + 256)),
    .AUIPC .x5 (laHi GuestAddrs.e77w_nonce (GuestAddrs.eip7702_warm_recovered_authorities + 260)),
    .ADDI .x5 .x5 (laLo GuestAddrs.e77w_nonce (GuestAddrs.eip7702_warm_recovered_authorities + 260)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (-1 : Word),
    .BEQ .x6 .x7 (brOff (GuestAddrs.eip7702_warm_recovered_authorities + 356) (GuestAddrs.eip7702_warm_recovered_authorities + 276)),
    .AUIPC .x28 (laHi GuestAddrs.e77w_tlen (GuestAddrs.eip7702_warm_recovered_authorities + 280)),
    .ADDI .x28 .x28 (laLo GuestAddrs.e77w_tlen (GuestAddrs.eip7702_warm_recovered_authorities + 280)),
    .LD .x11 .x28 (0 : BitVec 12),
    .MV .x10 .x21,
    .AUIPC .x12 (laHi GuestAddrs.e77w_authority (GuestAddrs.eip7702_warm_recovered_authorities + 296)),
    .ADDI .x12 .x12 (laLo GuestAddrs.e77w_authority (GuestAddrs.eip7702_warm_recovered_authorities + 296)),
    .AUIPC .x13 (laHi GuestAddrs.e77w_scratch (GuestAddrs.eip7702_warm_recovered_authorities + 304)),
    .ADDI .x13 .x13 (laLo GuestAddrs.e77w_scratch (GuestAddrs.eip7702_warm_recovered_authorities + 304)),
    .JAL .x1 (jalOff GuestAddrs.eip7702_authorization_recover_address (GuestAddrs.eip7702_warm_recovered_authorities + 312)),
    .BNE .x10 .x0 (40 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.e77w_authority (GuestAddrs.eip7702_warm_recovered_authorities + 320)),
    .ADDI .x10 .x10 (laLo GuestAddrs.e77w_authority (GuestAddrs.eip7702_warm_recovered_authorities + 320)),
    .AUIPC .x11 (laHi GuestAddrs.evm_access_account_table (GuestAddrs.eip7702_warm_recovered_authorities + 328)),
    .ADDI .x11 .x11 (laLo GuestAddrs.evm_access_account_table (GuestAddrs.eip7702_warm_recovered_authorities + 328)),
    .AUIPC .x12 (laHi GuestAddrs.evm_access_account_count (GuestAddrs.eip7702_warm_recovered_authorities + 336)),
    .ADDI .x12 .x12 (laLo GuestAddrs.evm_access_account_count (GuestAddrs.eip7702_warm_recovered_authorities + 336)),
    .LUI .x13 (24 : BitVec 20),
    .ADDIW .x13 .x13 (1696 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.runtime_access_account_seed (GuestAddrs.eip7702_warm_recovered_authorities + 352)),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.eip7702_warm_recovered_authorities + 100) (GuestAddrs.eip7702_warm_recovered_authorities + 360)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `eip7702WarmRecoveredAuthorities_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def eip7702WarmRecoveredAuthorities_relocs : RelocTable :=
  [ (12, .la .x5 "bv_chain_id"),
    (17, .la .x12 "e77w_count"),
    (19, .jal .x1 "rlp_list_count_items"),
    (21, .la .x5 "e77w_count"),
    (29, .la .x13 "e77w_toff"),
    (31, .la .x14 "e77w_tlen"),
    (33, .jal .x1 "rlp_list_nth_item"),
    (35, .la .x5 "e77w_toff"),
    (39, .la .x5 "e77w_tlen"),
    (42, .la .x28 "e77w_tlen"),
    (47, .la .x13 "e77w_chain"),
    (49, .jal .x1 "rlp_field_to_u64_strict"),
    (51, .la .x5 "e77w_chain"),
    (56, .la .x28 "e77w_tlen"),
    (61, .la .x13 "e77w_nonce"),
    (63, .jal .x1 "rlp_field_to_u64_strict"),
    (65, .la .x5 "e77w_nonce"),
    (70, .la .x28 "e77w_tlen"),
    (74, .la .x12 "e77w_authority"),
    (76, .la .x13 "e77w_scratch"),
    (78, .jal .x1 "eip7702_authorization_recover_address"),
    (80, .la .x10 "e77w_authority"),
    (82, .la .x11 "evm_access_account_table"),
    (84, .la .x12 "evm_access_account_count"),
    (88, .jal .x1 "runtime_access_account_seed") ]

def eip7702WarmRecoveredAuthoritiesFunction : String :=
  "eip7702_warm_recovered_authorities:\n" ++ emitProgramR eip7702WarmRecoveredAuthorities_prog eip7702WarmRecoveredAuthorities_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `eip7702WarmRecoveredAuthorities_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem eip7702WarmRecoveredAuthoritiesFunction_eq_prog :
    eip7702WarmRecoveredAuthoritiesFunction = "eip7702_warm_recovered_authorities:\n" ++ emitProgramR eip7702WarmRecoveredAuthorities_prog eip7702WarmRecoveredAuthorities_relocs := rfl

#guard eip7702WarmRecoveredAuthoritiesFunction.startsWith "eip7702_warm_recovered_authorities:\n"
#guard eip7702WarmRecoveredAuthorities_prog.length = 100
/-- Scratch for `eip7702_warm_recovered_authorities`. Used inline by the
    block-verdict data section (`BlockVerdictDataSection`); kept here for any
    standalone probe that links the function on its own. -/
def eip7702WarmRecoveredAuthoritiesDataSection : String :=
  ".balign 8\n" ++
  "e77w_count:\n  .zero 8\n" ++
  "e77w_toff:\n  .zero 8\n" ++
  "e77w_tlen:\n  .zero 8\n" ++
  "e77w_chain:\n  .zero 8\n" ++
  "e77w_nonce:\n  .zero 8\n" ++
  "e77w_authority:\n  .zero 24\n" ++
  ".balign 8\n" ++
  "e77w_scratch:\n  .zero 360\n"

def eip7702AuthorizationRecoverAddressDataSection : String :=
  ".balign 8\n" ++
  "a77ra_cmp:\n  .zero 8\n" ++
  "a77ra_secp256k1_n:\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfe\n" ++
  "  .byte 0xba,0xae,0xdc,0xe6,0xaf,0x48,0xa0,0x3b\n" ++
  "  .byte 0xbf,0xd2,0x5e,0x8c,0xd0,0x36,0x41,0x41\n" ++
  "a77ra_secp256k1_half_n:\n" ++
  "  .byte 0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0x5d,0x57,0x6e,0x73,0x57,0xa4,0x50,0x1d\n" ++
  "  .byte 0xdf,0xe9,0x2f,0x46,0x68,0x1b,0x20,0xa0\n" ++
  "a77ra_scratch:\n  .zero 360\n"

/-- `zisk_eip7702_authorization_recover_address`: focused probe.

    Input layout after the ziskemu 8-byte length header:
      user bytes 0..8 : authorization tuple byte length
      user bytes 8..  : authorization tuple RLP

    Output layout:
      +0  status
      +8  recovered 20-byte authority address, zero on failure
      +32 recovered public key x||y, zero on failure -/
def ziskEip7702AuthorizationRecoverAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  ld a1, 8(t6)                # tuple len (user +0)\n" ++
  "  addi a0, t6, 16             # tuple ptr (user +8)\n" ++
  "  li a2, 0xa0010008           # address output\n" ++
  "  la a3, a77ra_scratch\n" ++
  "  jal ra, eip7702_authorization_recover_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  # Copy recovered pubkey scratch for validation when recovery succeeds.\n" ++
  "  addi t0, t0, 32\n" ++
  "  la t1, a77ra_scratch; addi t1, t1, 296\n" ++
  "  li t2, 8\n" ++
  ".La77rap_copy_pub:\n" ++
  "  ld t3, 0(t1); sd t3, 0(t0); addi t1, t1, 8; addi t0, t0, 8; addi t2, t2, -1; bnez t2, .La77rap_copy_pub\n" ++
  "  j .La77rap_done\n" ++
  rlpListNthItemFunction ++ "\n" ++
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
  ".La77rap_done:"

def ziskEip7702AuthorizationRecoverAddressDataSection : String :=
  ziskEip7702AuthorizationSigningHashDataSection ++ "\n" ++
  ziskEip7702AuthorizationExtractSignatureDataSection ++ "\n" ++
  secp256k1CurveDataSection ++ "\n" ++
  secp256k1RecoverDataSection ++ "\n" ++
  txPubkeyRecoverRawDataSection ++ "\n" ++
  "afp_digest:\n  .zero 32\n" ++
  eip7702AuthorizationRecoverAddressDataSection

def ziskEip7702AuthorizationRecoverAddressProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskEip7702AuthorizationRecoverAddressPrologue
  dataAsm     := ziskEip7702AuthorizationRecoverAddressDataSection
}

end EvmAsm.Codegen
