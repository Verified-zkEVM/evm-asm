/-
  EvmAsm.Codegen.Programs.Eip7702Authority

  EIP-7702 authorization authority recovery. This is the reusable bridge
  between an authorization tuple and the 20-byte authority address needed by
  static set-delegation accounting.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
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
def eip7702AuthorizationRecoverAddressFunction : String :=
  "eip7702_authorization_recover_address:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # tuple ptr\n" ++
  "  mv s1, a1                   # tuple len\n" ++
  "  mv s2, a2                   # 20-byte address out\n" ++
  "  mv s3, a3                   # scratch base\n" ++
  "  # Clear the address output up front so failure cannot expose stale bytes.\n" ++
  "  sd zero, 0(s2); sd zero, 8(s2); sw zero, 16(s2)\n" ++
  "  # Clear the material block. Only +8/+16/+48/+80 are semantically used by\n" ++
  "  # tx_pubkey_ecrecover_stage_material, but zeroing keeps probes readable.\n" ++
  "  mv t0, s3; li t1, 16\n" ++
  ".La77ra_zero_material:\n" ++
  "  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; bnez t1, .La77ra_zero_material\n" ++
  "  # Extract y_parity/r/s into material +8/+16/+48.\n" ++
  "  mv a0, s0; mv a1, s1; addi a2, s3, 8; addi a3, s3, 16; addi a4, s3, 48\n" ++
  "  jal ra, eip7702_authorization_extract_signature\n" ++
  "  beqz a0, .La77ra_sig_ok\n" ++
  "  li a0, 10\n" ++
  "  j .La77ra_ret\n" ++
  ".La77ra_sig_ok:\n" ++
  "  # Compute signing hash into material +80.\n" ++
  "  mv a0, s0; mv a1, s1; addi a2, s3, 80\n" ++
  "  jal ra, eip7702_authorization_signing_hash\n" ++
  "  beqz a0, .La77ra_hash_ok\n" ++
  "  li a0, 20\n" ++
  "  j .La77ra_ret\n" ++
  ".La77ra_hash_ok:\n" ++
  "  # Validate recid/y_parity and scalar ranges before calling the recovery kernel.\n" ++
  "  ld t0, 8(s3); li t1, 1; bgtu t0, t1, .La77ra_bad_y\n" ++
  "  addi a0, s3, 16; jal ra, u256_is_zero\n" ++
  "  bnez a0, .La77ra_r_zero\n" ++
  "  addi a0, s3, 48; jal ra, u256_is_zero\n" ++
  "  bnez a0, .La77ra_s_zero\n" ++
  "  addi a0, s3, 16; la a1, a77ra_secp256k1_n; la a2, a77ra_cmp\n" ++
  "  jal ra, u256_lt_be\n" ++
  "  la t0, a77ra_cmp; ld t1, 0(t0); beqz t1, .La77ra_r_order\n" ++
  "  la a0, a77ra_secp256k1_half_n; addi a1, s3, 48; la a2, a77ra_cmp\n" ++
  "  jal ra, u256_lt_be\n" ++
  "  la t0, a77ra_cmp; ld t1, 0(t0); bnez t1, .La77ra_s_high\n" ++
  "  # Stage the material and recover the public key.\n" ++
  "  mv a0, s3; addi a1, s3, 128\n" ++
  "  jal ra, tx_pubkey_ecrecover_stage_material\n" ++
  "  beqz a0, .La77ra_stage_ok\n" ++
  "  li a0, 50\n" ++
  "  j .La77ra_ret\n" ++
  ".La77ra_stage_ok:\n" ++
  "  addi a0, s3, 128; addi a1, s3, 296\n" ++
  "  jal ra, secp256k1_recover_pubkey_staged\n" ++
  "  beqz a0, .La77ra_recover_ok\n" ++
  "  li a0, 60\n" ++
  "  j .La77ra_ret\n" ++
  ".La77ra_recover_ok:\n" ++
  "  addi a0, s3, 296; mv a1, s2\n" ++
  "  jal ra, address_from_pubkey\n" ++
  "  li a0, 0\n" ++
  "  j .La77ra_ret\n" ++
  ".La77ra_bad_y:\n" ++
  "  li a0, 31\n" ++
  "  j .La77ra_ret\n" ++
  ".La77ra_r_zero:\n" ++
  "  li a0, 40\n" ++
  "  j .La77ra_ret\n" ++
  ".La77ra_s_zero:\n" ++
  "  li a0, 41\n" ++
  "  j .La77ra_ret\n" ++
  ".La77ra_r_order:\n" ++
  "  li a0, 42\n" ++
  "  j .La77ra_ret\n" ++
  ".La77ra_s_high:\n" ++
  "  li a0, 43\n" ++
  ".La77ra_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

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
