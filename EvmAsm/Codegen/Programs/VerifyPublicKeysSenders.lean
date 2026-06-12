/-
  EvmAsm.Codegen.Programs.VerifyPublicKeysSenders

  Block-level sender-attribution gate (evm-asm-bmvmx.3 / mcogi.3).

  `public_keys_valid` (BlockVerdictChainConfig.lean) checks only the COUNT and
  the canonical 65-byte SEC1 SHAPE of each `stateless_input.public_keys[i]`; it
  does NOT bind a supplied key to the transaction that it is claimed to have
  signed. That is a soundness gap: `stateless_input.public_keys` is prover
  witness, not consensus-bound, so a lying witness can attribute a transaction
  to an attacker-chosen account and the guest validates the whole BAL state
  transition against the WRONG sender.

  `verify_public_keys_match_senders` closes that gap by mirroring
  execution-specs Amsterdam `recover_sender_from_public_key` over every
  transaction: for each i it recovers the canonical public key from the i-th
  transaction's signature and compares it to `public_keys[i]`, rejecting on the
  first mismatch (or any recovery failure). It walks the SSZ `transactions`
  offset table the same way as `multi_tx_nth_context` / `block_verdict`
  (BlockVerdictMultiTx.lean) to locate each `tx[i] = [offset[i], offset[i+1])`,
  then delegates the per-transaction recover-and-compare to the already-verified
  `tx_pubkey_public_key_matches` (TxPubkey.lean), which is accelerator-backed at
  ~2e6 ziskemu steps per transaction.

  This slice provides the helper + a standalone probe ONLY; linking the
  TX-side recovery stack into the guest closure and calling this from the live
  verdict (after `public_keys_valid`) is the follow-up child bmvmx.3.2.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.TxPubkey

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## verify_public_keys_match_senders

    Verify every `stateless_input.public_keys[i]` against the i-th transaction's
    recovered signer key. Mirrors execution-specs
    `recover_sender_from_public_key` applied to each transaction of the block.

    Reads the block globals prepared earlier in the verdict:
      bv_tx_list_ptr / bv_tx_list_len : SSZ `transactions` list (u32 LE offset
                                        table of `tx_count` entries followed by
                                        the concatenated transaction bytes).
      bv_public_keys_ptr              : base of the 65-byte SEC1 public keys
                                        (`public_keys[i] = base + 65*i`).
      bv_chain_id                     : execution chain id (u64), used by legacy
                                        EIP-155 recovery.

    Calling convention:
      (no register inputs; consumes the globals above)
      ra (input)  : return
      a0 (output) : status

    Status:
      0   all transactions: supplied key == recovered key (or 0-tx block)
      1   a mismatch (recovery ok, coordinates differ) -> REJECT
      2   a supplied key had a non-0x04 prefix -> REJECT
      10  signature material failed for some tx -> REJECT
      20  ecrecover ABI staging failed for some tx -> REJECT
      60  secp256k1 recovery failed for some tx -> REJECT
      90  malformed SSZ transaction list (table not 4-aligned / offset out of
          range / empty item) -> REJECT

    Any nonzero status is a reject: a valid block recovers every sender and
    matches every supplied key, so this never false-rejects a valid block. The
    helper status is propagated verbatim so the live caller can distinguish a
    genuine mismatch (1) from a recovery/parse failure. -/
def verifyPublicKeysMatchSendersFunction : String :=
  "verify_public_keys_match_senders:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  la t0, bv_tx_list_ptr; ld s0, 0(t0)   # SSZ tx list ptr\n" ++
  "  la t0, bv_tx_list_len; ld s1, 0(t0)   # tx list byte length\n" ++
  "  li t0, 4; bltu s1, t0, .Lvpks_ok      # <4 bytes -> no offset table -> 0 txs\n" ++
  "  mv a0, s0; jal ra, bgv_u32le           # offset[0]\n" ++
  "  andi t0, a0, 3; bnez t0, .Lvpks_malformed\n" ++
  "  srli s2, a0, 2                         # tx_count = offset[0] / 4\n" ++
  "  beqz s2, .Lvpks_ok                     # 0-tx block -> nothing to verify\n" ++
  "  la t0, bv_public_keys_ptr; ld s3, 0(t0)   # public_keys base (65 bytes/key)\n" ++
  "  la t0, bv_chain_id; ld s4, 0(t0)          # execution chain id\n" ++
  "  li s5, 0                               # i = 0\n" ++
  ".Lvpks_loop:\n" ++
  "  beq s5, s2, .Lvpks_ok\n" ++
  "  slli t0, s5, 2; add a0, s0, t0; jal ra, bgv_u32le   # offset[i]\n" ++
  "  mv s6, a0\n" ++
  "  addi t0, s5, 1; beq t0, s2, .Lvpks_last\n" ++
  "  slli t1, t0, 2; add a0, s0, t1; jal ra, bgv_u32le   # offset[i+1]\n" ++
  "  mv s7, a0\n" ++
  "  j .Lvpks_bounds\n" ++
  ".Lvpks_last:\n" ++
  "  mv s7, s1                              # final tx ends at list end\n" ++
  ".Lvpks_bounds:\n" ++
  "  slli t0, s2, 2; bltu s6, t0, .Lvpks_malformed   # offset[i] must be past the table\n" ++
  "  bltu s7, s6, .Lvpks_malformed                   # offset[i+1] >= offset[i]\n" ++
  "  bgtu s7, s1, .Lvpks_malformed                   # offset[i+1] <= list len\n" ++
  "  add a0, s0, s6                         # tx[i] ptr\n" ++
  "  sub a1, s7, s6                         # tx[i] len\n" ++
  "  beqz a1, .Lvpks_malformed              # empty transaction item\n" ++
  "  mv a2, s4                              # chain_id\n" ++
  "  li t0, 65; mul t0, s5, t0; add a3, s3, t0   # &public_keys[i]\n" ++
  "  la a4, vpks_pubkey_out                 # recovered pubkey scratch (64 bytes)\n" ++
  "  la a5, vpks_scratch                    # recover scratch (>= 304 bytes)\n" ++
  "  jal ra, tx_pubkey_public_key_matches\n" ++
  "  bnez a0, .Lvpks_ret                    # mismatch / recovery failure -> reject (propagate)\n" ++
  "  addi s5, s5, 1; j .Lvpks_loop\n" ++
  ".Lvpks_ok:\n" ++
  "  li a0, 0; j .Lvpks_ret\n" ++
  ".Lvpks_malformed:\n" ++
  "  li a0, 90\n" ++
  ".Lvpks_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_verify_public_keys_match_senders`: standalone probe BuildUnit.

    Drives `verify_public_keys_match_senders` over a single-transaction SSZ
    transaction list and one supplied SEC1 public key, so the offset-table walk
    + per-tx `tx_pubkey_public_key_matches` delegation can be checked end-to-end
    against the deterministic legacy EIP-155 priv=1 vector (recovered key == the
    secp256k1 generator G). The full recovery is ~2e6 ziskemu steps, gated by
    the check script's RECOVER_RAW_FULL switch + the 1e9 step budget.

    Input layout (ziskemu writes an 8-byte length header at +0, so user byte k
    is at INPUT+8+k). The tx-list offset is a field so an N-key block lays the
    keys (N*65 bytes) out from user+24 without colliding with the tx list:
      user +0   : SSZ transactions list byte length (u64)
      user +8   : execution chain id (u64)
      user +16  : tx-list offset (u64; byte offset of the SSZ list from user+0)
      user +24  : supplied public keys (N * 65 bytes, each 0x04 || BE x || BE y)
      user +<tx-list offset> : SSZ transactions list bytes (u32 LE offset table
                  + tx bytes), 8-byte aligned

    Output layout at 0xa0010000:
      +0  status (0 all match, 1 mismatch, 2 bad prefix, 10/20/60 recovery,
          90 malformed list) -/
def ziskVerifyPublicKeysMatchSendersPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000           # input base (8-byte length header at +0)\n" ++
  "  ld t0, 8(t6)                # tx list byte length (user +0)\n" ++
  "  la t1, bv_tx_list_len; sd t0, 0(t1)\n" ++
  "  ld t0, 24(t6)               # tx-list offset (user +16)\n" ++
  "  add t0, t6, t0; addi t0, t0, 8   # SSZ tx list ptr = input + 8 + tx_list_offset\n" ++
  "  la t1, bv_tx_list_ptr; sd t0, 0(t1)\n" ++
  "  ld t0, 16(t6)               # chain id (user +8)\n" ++
  "  la t1, bv_chain_id; sd t0, 0(t1)\n" ++
  "  addi t0, t6, 32             # public_keys base (user +24)\n" ++
  "  la t1, bv_public_keys_ptr; sd t0, 0(t1)\n" ++
  "  jal ra, verify_public_keys_match_senders\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lvpksp_done\n" ++
  bgvU32leFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  -- secp256k1 recovery stack (curve common provides u256_lt_be/_add_be/_sub_be,
  -- so no standalone u256_lt_be is linked here to avoid a duplicate label).
  secp256k1CurveCommonFunctions ++ "\n" ++
  secp256k1RecoverRFunction ++ "\n" ++
  txLegacyExtractSignatureFunction ++ "\n" ++
  txEip2930ExtractSignatureFunction ++ "\n" ++
  txEip1559ExtractSignatureFunction ++ "\n" ++
  txEip4844ExtractSignatureFunction ++ "\n" ++
  txEip7702ExtractSignatureFunction ++ "\n" ++
  txSigningHashFunction ++ "\n" ++
  txSigningHashLegacyEip155Function ++ "\n" ++
  txPubkeySignatureMaterialFunction ++ "\n" ++
  txPubkeyEcrecoverStageMaterialFunction ++ "\n" ++
  txPubkeyRecoverRawFunction ++ "\n" ++
  secp256k1RecoverPubkeyStagedFunction ++ "\n" ++
  txPubkeyPublicKeyMatchesFunction ++ "\n" ++
  verifyPublicKeysMatchSendersFunction ++ "\n" ++
  ".Lvpksp_done:"

def ziskVerifyPublicKeysMatchSendersDataSection : String :=
  ziskTxPubkeyPublicKeyMatchesStatusDataSection ++ "\n" ++
  ".balign 8\n" ++
  "bv_tx_list_ptr:\n  .zero 8\n" ++
  "bv_tx_list_len:\n  .zero 8\n" ++
  "bv_public_keys_ptr:\n  .zero 8\n" ++
  "bv_chain_id:\n  .zero 8\n" ++
  "vpks_pubkey_out:\n  .zero 64\n" ++
  "vpks_scratch:\n  .zero 312"

def ziskVerifyPublicKeysMatchSendersProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskVerifyPublicKeysMatchSendersPrologue
  dataAsm     := ziskVerifyPublicKeysMatchSendersDataSection
}

/-- TX-side recovery scratch to APPEND to the guest data section
    (`ziskStatelessVerdictV2DataSection`) when the guest closure links the
    transaction sender-recovery stack (bmvmx.3.2). The secp256k1 constants /
    R-decompression scratch / `tpr_*` recovery scratch and the keccak `zk3_state`
    are ALREADY in the guest data section (the ECRECOVER backend + keccak), so
    this section deliberately omits them — it carries only the signature
    material (`tps_*`), the per-type signature-extractor offset scratch, the
    signing-hash buffers, and the `verify_public_keys_match_senders` scratch +
    `bv_chain_id`. Mirrors `ziskTxPubkeySignatureMaterialDataSection` minus the
    already-present labels. -/
def verifyPublicKeysSendersGuestDataSection : String :=
  ".balign 8\n" ++
  "tps_type:\n  .zero 8\n" ++
  "tps_inner_off:\n  .zero 8\n" ++
  "tps_v:\n  .zero 8\n" ++
  "tps_cmp:\n  .zero 8\n" ++
  "tps_secp256k1_n:\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfe\n" ++
  "  .byte 0xba,0xae,0xdc,0xe6,0xaf,0x48,0xa0,0x3b\n" ++
  "  .byte 0xbf,0xd2,0x5e,0x8c,0xd0,0x36,0x41,0x41\n" ++
  "tps_secp256k1_half_n:\n" ++
  "  .byte 0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0x5d,0x57,0x6e,0x73,0x57,0xa4,0x50,0x1d\n" ++
  "  .byte 0xdf,0xe9,0x2f,0x46,0x68,0x1b,0x20,0xa0\n" ++
  "tlxs_offset:\n  .zero 8\n" ++
  "tlxs_length:\n  .zero 8\n" ++
  "txes_offset:\n  .zero 8\n" ++
  "txes_length:\n  .zero 8\n" ++
  "t29es_offset:\n  .zero 8\n" ++
  "t29es_length:\n  .zero 8\n" ++
  "t44es_offset:\n  .zero 8\n" ++
  "t44es_length:\n  .zero 8\n" ++
  "t77es_offset:\n  .zero 8\n" ++
  "t77es_length:\n  .zero 8\n" ++
  "tsh_buf:\n  .zero 131072\n" ++
  "tsh_trunc_len:\n  .zero 8\n" ++
  "rltn_offset_lo:\n  .zero 8\n" ++
  "rltn_length_lo:\n  .zero 8\n" ++
  "rltn_offset_hi:\n  .zero 8\n" ++
  "rltn_length_hi:\n  .zero 8\n" ++
  "rltn_prefix_len:\n  .zero 8\n" ++
  "t155_buf:\n  .zero 131072\n" ++
  "t155_offset_lo:\n  .zero 8\n" ++
  "t155_length_lo:\n  .zero 8\n" ++
  "t155_offset_hi:\n  .zero 8\n" ++
  "t155_length_hi:\n  .zero 8\n" ++
  "t155_chain_be:\n  .zero 8\n" ++
  "t155_chain_enc:\n  .zero 9\n" ++
  ".balign 8\n" ++
  "t155_prefix_len:\n  .zero 8\n" ++
  -- bmvmx.3.2: verify_public_keys_match_senders scratch + the execution chain id
  -- captured by chain_config_valid. bv_tx_list_ptr/len and bv_public_keys_ptr
  -- are already in the guest data section.
  ".balign 8\n" ++
  "bv_chain_id:\n  .zero 8\n" ++
  "vpks_pubkey_out:\n  .zero 64\n" ++
  "vpks_scratch:\n  .zero 312\n"

/-- The transaction sender-recovery function bodies to link into the guest
    closure(s) for the live `verify_public_keys_match_senders` call (bmvmx.3.2).
    `tx_type_dispatch`, the `tx_extract_*` helpers, `rlp_list_count_items`,
    `rlp_list_nth_item`, `zkvm_keccak256`, `u256_is_zero`, `u256_lt_be`,
    `bgv_u32le`, the secp256k1 curve-common / R-decompression /
    `secp256k1_recover_pubkey_staged` kernel, and `address_from_pubkey` are
    ALREADY in the guest closure (and the debug-verdict prologue); this string
    adds only the missing TX-side bodies (`rlp_list_truncate_to_n_fields`, the
    five per-type signature extractors, both signing-hash builders, the
    signature-material / ecrecover-staging / recover-raw / public-key-matches
    stack, and the loop driver itself). -/
def verifyPublicKeysSendersGuestFunctions : String :=
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  txLegacyExtractSignatureFunction ++ "\n" ++
  txEip2930ExtractSignatureFunction ++ "\n" ++
  txEip1559ExtractSignatureFunction ++ "\n" ++
  txEip4844ExtractSignatureFunction ++ "\n" ++
  txEip7702ExtractSignatureFunction ++ "\n" ++
  txSigningHashFunction ++ "\n" ++
  txSigningHashLegacyEip155Function ++ "\n" ++
  txPubkeySignatureMaterialFunction ++ "\n" ++
  txPubkeyEcrecoverStageMaterialFunction ++ "\n" ++
  txPubkeyRecoverRawFunction ++ "\n" ++
  txPubkeyPublicKeyMatchesFunction ++ "\n" ++
  verifyPublicKeysMatchSendersFunction

end EvmAsm.Codegen
