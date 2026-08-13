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
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
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
def verifyPublicKeysMatchSenders_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_tx_list_ptr (GuestAddrs.verify_public_keys_match_senders + 40)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_tx_list_ptr (GuestAddrs.verify_public_keys_match_senders + 40)),
    .LD .x8 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_tx_list_len (GuestAddrs.verify_public_keys_match_senders + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_tx_list_len (GuestAddrs.verify_public_keys_match_senders + 52)),
    .LD .x9 .x5 (0 : BitVec 12),
    .LI .x5 (4 : Word),
    .BLTU .x9 .x5 (184 : BitVec 13),
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.verify_public_keys_match_senders + 76)),
    .ANDI .x5 .x10 (3 : BitVec 12),
    .BNE .x5 .x0 (176 : BitVec 13),
    .SRLI .x18 .x10 (2 : BitVec 6),
    .BEQ .x18 .x0 (160 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.bv_public_keys_ptr (GuestAddrs.verify_public_keys_match_senders + 96)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_public_keys_ptr (GuestAddrs.verify_public_keys_match_senders + 96)),
    .LD .x19 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_chain_id (GuestAddrs.verify_public_keys_match_senders + 108)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_chain_id (GuestAddrs.verify_public_keys_match_senders + 108)),
    .LD .x20 .x5 (0 : BitVec 12),
    .LI .x21 (0 : Word),
    .BEQ .x21 .x18 (128 : BitVec 13),
    .SLLI .x5 .x21 (2 : BitVec 6),
    .ADD .x10 .x8 .x5,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.verify_public_keys_match_senders + 136)),
    .MV .x22 .x10,
    .ADDI .x5 .x21 (1 : BitVec 12),
    .BEQ .x5 .x18 (24 : BitVec 13),
    .SLLI .x6 .x5 (2 : BitVec 6),
    .ADD .x10 .x8 .x6,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.verify_public_keys_match_senders + 160)),
    .MV .x23 .x10,
    .JAL .x0 (8 : BitVec 21),
    .MV .x23 .x9,
    .SLLI .x5 .x18 (2 : BitVec 6),
    .BLTU .x22 .x5 (80 : BitVec 13),
    .BLTU .x23 .x22 (76 : BitVec 13),
    .BLTU .x9 .x23 (72 : BitVec 13),
    .ADD .x10 .x8 .x22,
    .SUB .x11 .x23 .x22,
    .BEQ .x11 .x0 (60 : BitVec 13),
    .MV .x12 .x20,
    .LI .x5 (65 : Word),
    .MUL .x5 .x21 .x5,
    .ADD .x13 .x19 .x5,
    .AUIPC .x14 (laHi GuestAddrs.vpks_pubkey_out (GuestAddrs.verify_public_keys_match_senders + 220)),
    .ADDI .x14 .x14 (laLo GuestAddrs.vpks_pubkey_out (GuestAddrs.verify_public_keys_match_senders + 220)),
    .AUIPC .x15 (laHi GuestAddrs.vpks_scratch (GuestAddrs.verify_public_keys_match_senders + 228)),
    .ADDI .x15 .x15 (laLo GuestAddrs.vpks_scratch (GuestAddrs.verify_public_keys_match_senders + 228)),
    .JAL .x1 (jalOff GuestAddrs.tx_pubkey_public_key_matches (GuestAddrs.verify_public_keys_match_senders + 236)),
    .BNE .x10 .x0 (24 : BitVec 13),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (-124 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (90 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `verifyPublicKeysMatchSenders_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def verifyPublicKeysMatchSenders_relocs : RelocTable :=
  [ (10, .la .x5 "bv_tx_list_ptr"),
    (13, .la .x5 "bv_tx_list_len"),
    (19, .jal .x1 "bgv_u32le"),
    (24, .la .x5 "bv_public_keys_ptr"),
    (27, .la .x5 "bv_chain_id"),
    (34, .jal .x1 "bgv_u32le"),
    (40, .jal .x1 "bgv_u32le"),
    (55, .la .x14 "vpks_pubkey_out"),
    (57, .la .x15 "vpks_scratch"),
    (59, .jal .x1 "tx_pubkey_public_key_matches") ]

def verifyPublicKeysMatchSendersFunction : String :=
  "verify_public_keys_match_senders:\n" ++ emitProgramR verifyPublicKeysMatchSenders_prog verifyPublicKeysMatchSenders_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `verifyPublicKeysMatchSenders_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem verifyPublicKeysMatchSendersFunction_eq_prog :
    verifyPublicKeysMatchSendersFunction = "verify_public_keys_match_senders:\n" ++ emitProgramR verifyPublicKeysMatchSenders_prog verifyPublicKeysMatchSenders_relocs := rfl

#guard verifyPublicKeysMatchSendersFunction.startsWith "verify_public_keys_match_senders:\n"
#guard verifyPublicKeysMatchSenders_prog.length = 77
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
  zkvmKeccak256SegmentsFunction ++ "\n" ++
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


/-! ## block_verdict_chain_id_gate (evm-asm-7zzfv, v0.6.0 item 8)

    Live per-transaction chain-id-vs-block gate, mirroring execution-specs
    `process_transaction` (fork.py:1051-1055) + `chain_id(tx)`
    (transactions.py:772-787) at 40f956fab:

      * legacy: `v in {27, 28}` -> no chain id (skip); otherwise the tx passes
        iff `v == 35 + 2*chain_id` or `v == 36 + 2*chain_id` (any other `v` is
        either `v < 35` -> InvalidSignatureError("bad v") or a chain-id
        mismatch / U64-overflowing chain id -> WrongChainIdError; every case
        rejects the block). `v` is compared in 128 bits so `35 + 2*chain_id`
        for chain ids near 2^64 stays exact; a `v` longer than 16 bytes always
        exceeds every representable `35/36 + 2*U64`, so it rejects.
      * typed (2930/1559/4844/7702): inner RLP field 0 is the tx chain id; a
        scalar longer than 8 bytes overflows the spec's U64 decode (raises ->
        invalid tx), otherwise it must equal the block chain id.

    Typed transactions embed their own chain id in the signing hash, so sender
    recovery succeeds regardless of the block chain id -- without this gate a
    wrong-chain typed tx was a verdict FALSE-ACCEPT (the one soundness gap in
    the v0.6.0 port; legacy txs were already caught because EIP-155 recovery
    consumes bv_chain_id in the signing hash).

    Malformed structure (offset table, tx type, RLP parse) is DEFERRED (return
    0): verify_public_keys_match_senders runs the same walk immediately after
    and rejects those shapes (status 90/10), so deferral cannot false-accept.

    Reads the same block globals as verify_public_keys_match_senders
    (bv_tx_list_ptr / bv_tx_list_len / bv_chain_id).

    a0 (output): 0 = every tx chain id absent-or-matching; 1 = some tx has a
    present, mismatching (or spec-invalid) chain id -> REJECT the block. -/
def blockVerdictChainIdGate_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_tx_list_ptr (GuestAddrs.block_verdict_chain_id_gate + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_tx_list_ptr (GuestAddrs.block_verdict_chain_id_gate + 32)),
    .LD .x8 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_tx_list_len (GuestAddrs.block_verdict_chain_id_gate + 44)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_tx_list_len (GuestAddrs.block_verdict_chain_id_gate + 44)),
    .LD .x9 .x5 (0 : BitVec 12),
    .LI .x5 (4 : Word),
    .BLTU .x9 .x5 (532 : BitVec 13),
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_chain_id_gate + 68)),
    .ANDI .x5 .x10 (3 : BitVec 12),
    .BNE .x5 .x0 (516 : BitVec 13),
    .SRLI .x18 .x10 (2 : BitVec 6),
    .BEQ .x18 .x0 (508 : BitVec 13),
    .LI .x19 (0 : Word),
    .BEQ .x19 .x18 (500 : BitVec 13),
    .SLLI .x5 .x19 (2 : BitVec 6),
    .ADD .x10 .x8 .x5,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_chain_id_gate + 104)),
    .MV .x20 .x10,
    .ADDI .x5 .x19 (1 : BitVec 12),
    .BEQ .x5 .x18 (24 : BitVec 13),
    .SLLI .x6 .x5 (2 : BitVec 6),
    .ADD .x10 .x8 .x6,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_chain_id_gate + 128)),
    .MV .x21 .x10,
    .JAL .x0 (8 : BitVec 21),
    .MV .x21 .x9,
    .SLLI .x5 .x18 (2 : BitVec 6),
    .BLTU .x20 .x5 (444 : BitVec 13),
    .BLTU .x21 .x20 (440 : BitVec 13),
    .BLTU .x9 .x21 (436 : BitVec 13),
    .ADD .x10 .x8 .x20,
    .SUB .x11 .x21 .x20,
    .BEQ .x11 .x0 (424 : BitVec 13),
    .AUIPC .x12 (laHi GuestAddrs.cig_type (GuestAddrs.block_verdict_chain_id_gate + 172)),
    .ADDI .x12 .x12 (laLo GuestAddrs.cig_type (GuestAddrs.block_verdict_chain_id_gate + 172)),
    .AUIPC .x13 (laHi GuestAddrs.cig_inner_off (GuestAddrs.block_verdict_chain_id_gate + 180)),
    .ADDI .x13 .x13 (laLo GuestAddrs.cig_inner_off (GuestAddrs.block_verdict_chain_id_gate + 180)),
    .JAL .x1 (jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.block_verdict_chain_id_gate + 188)),
    .BNE .x10 .x0 (400 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cig_type (GuestAddrs.block_verdict_chain_id_gate + 196)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cig_type (GuestAddrs.block_verdict_chain_id_gate + 196)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BNE .x5 .x0 (216 : BitVec 13),
    .ADD .x10 .x8 .x20,
    .SUB .x11 .x21 .x20,
    .LI .x12 (6 : Word),
    .AUIPC .x13 (laHi GuestAddrs.cig_off (GuestAddrs.block_verdict_chain_id_gate + 224)),
    .ADDI .x13 .x13 (laLo GuestAddrs.cig_off (GuestAddrs.block_verdict_chain_id_gate + 224)),
    .AUIPC .x14 (laHi GuestAddrs.cig_len (GuestAddrs.block_verdict_chain_id_gate + 232)),
    .ADDI .x14 .x14 (laLo GuestAddrs.cig_len (GuestAddrs.block_verdict_chain_id_gate + 232)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.block_verdict_chain_id_gate + 240)),
    .BNE .x10 .x0 (348 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cig_len (GuestAddrs.block_verdict_chain_id_gate + 248)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cig_len (GuestAddrs.block_verdict_chain_id_gate + 248)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (16 : Word),
    .BLTU .x7 .x6 (336 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cig_off (GuestAddrs.block_verdict_chain_id_gate + 268)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cig_off (GuestAddrs.block_verdict_chain_id_gate + 268)),
    .LD .x5 .x5 (0 : BitVec 12),
    .ADD .x5 .x5 .x8,
    .ADD .x5 .x5 .x20,
    .LI .x28 (0 : Word),
    .LI .x29 (0 : Word),
    .BEQ .x6 .x0 (40 : BitVec 13),
    .SLLI .x28 .x28 (8 : BitVec 6),
    .SRLI .x30 .x29 (56 : BitVec 6),
    .OR .x28 .x28 .x30,
    .SLLI .x29 .x29 (8 : BitVec 6),
    .LBU .x30 .x5 (0 : BitVec 12),
    .OR .x29 .x29 .x30,
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-36 : BitVec 21),
    .BNE .x28 .x0 (20 : BitVec 13),
    .LI .x30 (27 : Word),
    .BEQ .x29 .x30 (240 : BitVec 13),
    .LI .x30 (28 : Word),
    .BEQ .x29 .x30 (232 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.bv_chain_id (GuestAddrs.block_verdict_chain_id_gate + 356)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_chain_id (GuestAddrs.block_verdict_chain_id_gate + 356)),
    .LD .x30 .x5 (0 : BitVec 12),
    .SLLI .x31 .x30 (1 : BitVec 6),
    .SRLI .x30 .x30 (63 : BitVec 6),
    .ADDI .x5 .x31 (35 : BitVec 12),
    .BGEU .x5 .x31 (8 : BitVec 13),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .BNE .x28 .x30 (8 : BitVec 13),
    .BEQ .x29 .x5 (192 : BitVec 13),
    .ADDI .x6 .x5 (1 : BitVec 12),
    .MV .x7 .x30,
    .BNE .x6 .x0 (8 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .BNE .x28 .x7 (188 : BitVec 13),
    .BNE .x29 .x6 (184 : BitVec 13),
    .JAL .x0 (164 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.cig_inner_off (GuestAddrs.block_verdict_chain_id_gate + 424)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cig_inner_off (GuestAddrs.block_verdict_chain_id_gate + 424)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x10 .x8 .x20,
    .ADD .x10 .x10 .x7,
    .SUB .x11 .x21 .x20,
    .SUB .x11 .x11 .x7,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.cig_off (GuestAddrs.block_verdict_chain_id_gate + 456)),
    .ADDI .x13 .x13 (laLo GuestAddrs.cig_off (GuestAddrs.block_verdict_chain_id_gate + 456)),
    .AUIPC .x14 (laHi GuestAddrs.cig_len (GuestAddrs.block_verdict_chain_id_gate + 464)),
    .ADDI .x14 .x14 (laLo GuestAddrs.cig_len (GuestAddrs.block_verdict_chain_id_gate + 464)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.block_verdict_chain_id_gate + 472)),
    .BNE .x10 .x0 (116 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cig_len (GuestAddrs.block_verdict_chain_id_gate + 480)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cig_len (GuestAddrs.block_verdict_chain_id_gate + 480)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (8 : Word),
    .BLTU .x7 .x6 (104 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cig_off (GuestAddrs.block_verdict_chain_id_gate + 500)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cig_off (GuestAddrs.block_verdict_chain_id_gate + 500)),
    .LD .x5 .x5 (0 : BitVec 12),
    .ADD .x5 .x5 .x8,
    .ADD .x5 .x5 .x20,
    .AUIPC .x28 (laHi GuestAddrs.cig_inner_off (GuestAddrs.block_verdict_chain_id_gate + 520)),
    .ADDI .x28 .x28 (laLo GuestAddrs.cig_inner_off (GuestAddrs.block_verdict_chain_id_gate + 520)),
    .LD .x28 .x28 (0 : BitVec 12),
    .ADD .x5 .x5 .x28,
    .LI .x29 (0 : Word),
    .BEQ .x6 .x0 (28 : BitVec 13),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .LBU .x30 .x5 (0 : BitVec 12),
    .OR .x29 .x29 .x30,
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.bv_chain_id (GuestAddrs.block_verdict_chain_id_gate + 568)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_chain_id (GuestAddrs.block_verdict_chain_id_gate + 568)),
    .LD .x30 .x5 (0 : BitVec 12),
    .BNE .x29 .x30 (20 : BitVec 13),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (-496 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blockVerdictChainIdGate_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blockVerdictChainIdGate_relocs : RelocTable :=
  [ (8, .la .x5 "bv_tx_list_ptr"),
    (11, .la .x5 "bv_tx_list_len"),
    (17, .jal .x1 "bgv_u32le"),
    (26, .jal .x1 "bgv_u32le"),
    (32, .jal .x1 "bgv_u32le"),
    (43, .la .x12 "cig_type"),
    (45, .la .x13 "cig_inner_off"),
    (47, .jal .x1 "tx_type_dispatch"),
    (49, .la .x5 "cig_type"),
    (56, .la .x13 "cig_off"),
    (58, .la .x14 "cig_len"),
    (60, .jal .x1 "rlp_list_nth_item"),
    (62, .la .x5 "cig_len"),
    (67, .la .x5 "cig_off"),
    (89, .la .x5 "bv_chain_id"),
    (106, .la .x5 "cig_inner_off"),
    (114, .la .x13 "cig_off"),
    (116, .la .x14 "cig_len"),
    (118, .jal .x1 "rlp_list_nth_item"),
    (120, .la .x5 "cig_len"),
    (125, .la .x5 "cig_off"),
    (130, .la .x28 "cig_inner_off"),
    (142, .la .x5 "bv_chain_id") ]

def blockVerdictChainIdGateFunction : String :=
  "block_verdict_chain_id_gate:\n" ++ emitProgramR blockVerdictChainIdGate_prog blockVerdictChainIdGate_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blockVerdictChainIdGate_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blockVerdictChainIdGateFunction_eq_prog :
    blockVerdictChainIdGateFunction = "block_verdict_chain_id_gate:\n" ++ emitProgramR blockVerdictChainIdGate_prog blockVerdictChainIdGate_relocs := rfl

#guard blockVerdictChainIdGateFunction.startsWith "block_verdict_chain_id_gate:\n"
#guard blockVerdictChainIdGate_prog.length = 160
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
  "vpks_scratch:\n  .zero 312\n" ++
  -- evm-asm-7zzfv: block_verdict_chain_id_gate scratch (tx type / inner-list
  -- offset from tx_type_dispatch; item offset/length from rlp_list_nth_item).
  "cig_type:\n  .zero 8\n" ++
  "cig_inner_off:\n  .zero 8\n" ++
  "cig_off:\n  .zero 8\n" ++
  "cig_len:\n  .zero 8\n"

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
  verifyPublicKeysMatchSendersFunction ++ "\n" ++
  blockVerdictChainIdGateFunction

end EvmAsm.Codegen
