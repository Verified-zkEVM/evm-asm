/-
  EvmAsm.Codegen.Programs.Block

  Block-body and withdrawal cluster lifted out of
  `EvmAsm.Codegen.Programs` per the file-size hard cap. Groups
  every block-body-level helper plus the withdrawal pipeline.

  Withdrawal pipeline:
    K49  withdrawal_decode
    K65  withdrawals_sum_amounts
    K77  process_withdrawal
    K78  process_withdrawals_block

  Block-body helpers:
    K83  block_body_decode
    K84  block_validate_ommers_empty
    K85  block_withdrawals_total
    K86  block_summary
    K89  block_body_blob_gas_total
    K91  block_validate_blob_gas_consistency
    K97  block_compute_tx_hashes
    K124 block_count_withdrawals
    K125 block_count_transactions

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxBlobGas
import EvmAsm.Codegen.Programs.TxDecode
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Programs.Header

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## block_body_decode -- PR-K83

    Decode a post-Shanghai block body RLP into three sub-list
    (offset, length) pairs. The body is `rlp([transactions,
    ommers, withdrawals])`:

      Field 0: transactions   (list of typed tx envelopes)
      Field 1: ommers         (empty list post-merge: 0xc0)
      Field 2: withdrawals    (Shanghai+: list of [index, vi,
                              address, amount])

    Output struct layout (48 bytes):

         0..  8  transactions_offset (u64; within body_rlp)
         8.. 16  transactions_length (u64; full encoded sub-list)
        16.. 24  ommers_offset       (u64)
        24.. 32  ommers_length       (u64)
        32.. 40  withdrawals_offset  (u64)
        40.. 48  withdrawals_length  (u64)

    Composes PR-K20 `rlp_list_nth_item` three times. The
    (offset, length) of each sub-list is the FULL encoded item
    (including its own RLP list prefix), per K20's list-item
    contract — so callers can recurse into each with another
    `rlp_list_nth_item` call.

    For pre-Shanghai bodies (only 2 fields), this helper fails
    on the third call. Such bodies aren't relevant for the
    amsterdam stateless guest.

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : 48-byte output struct ptr
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail (not a 3-item list).

    Pure composition of PR-K20. No new `.data` scratch beyond
    what K20 needs (none). -/
def blockBodyDecodeFunction : String :=
  "block_body_decode:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s1, a1                   # body_len\n" ++
  "  mv s2, a2                   # output struct ptr\n" ++
  "  # Field 0: transactions\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  mv a3, s2\n" ++
  "  addi a4, s2, 8\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbd_fail\n" ++
  "  # Field 1: ommers\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  addi a3, s2, 16\n" ++
  "  addi a4, s2, 24\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbd_fail\n" ++
  "  # Field 2: withdrawals\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  addi a3, s2, 32\n" ++
  "  addi a4, s2, 40\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbd_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lbbd_ret\n" ++
  ".Lbbd_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbbd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_body_decode`: probe BuildUnit. Reads (body_len,
    body_bytes) from host input, writes (status, 48-byte struct)
    to OUTPUT (56 bytes total). -/
def ziskBlockBodyDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # body_len\n" ++
  "  addi a0, a3, 16             # body ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  mv t0, a2; li t1, 6\n" ++
  ".Lbbd_zinit:\n" ++
  "  beqz t1, .Lbbd_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lbbd_zinit\n" ++
  ".Lbbd_zdone:\n" ++
  "  jal ra, block_body_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbbd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  ".Lbbd_pdone:"

def ziskBlockBodyDecodeDataSection : String :=
  ".section .data\n" ++
  "bbd_pad:\n" ++
  "  .zero 8"

def ziskBlockBodyDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockBodyDecodePrologue
  dataAsm     := ziskBlockBodyDecodeDataSection
}

/-! ## block_validate_ommers_empty -- PR-K84

    Verify the post-merge invariant that a block body's ommers
    field is the empty RLP list (`0xc0`). The Merge fork removed
    uncle blocks; every post-merge block must have an empty
    ommers list, matching `EMPTY_OMMERS_HASH` in the header.

    Composes PR-K83 `block_body_decode` + a single-byte check
    on the ommers sub-list.

    An empty RLP list is encoded as the single byte `0xc0`. So
    the check is:
      - ommers_length == 1
      - body_rlp[ommers_offset] == 0xc0

    Calling convention:
      a0 (input)  : block_body_rlp ptr
      a1 (input)  : block_body_rlp byte length
      ra (input)  : return
      a0 (output) :
        0 : ommers is empty (post-merge ok)
        1 : ommers is non-empty (reject — pre-merge or invalid)
        2 : RLP parse failure

    Uses 48 bytes of `.data` scratch (`bvoe_struct`). -/
def blockValidateOmmersEmptyFunction : String :=
  "block_validate_ommers_empty:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  la a2, bvoe_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbvoe_parse_fail\n" ++
  "  la t0, bvoe_struct\n" ++
  "  ld t1, 24(t0)               # ommers_length\n" ++
  "  li t2, 1\n" ++
  "  bne t1, t2, .Lbvoe_not_empty\n" ++
  "  ld t3, 16(t0)               # ommers_offset\n" ++
  "  add t3, s0, t3\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  li t5, 0xc0\n" ++
  "  bne t4, t5, .Lbvoe_not_empty\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvoe_ret\n" ++
  ".Lbvoe_not_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvoe_ret\n" ++
  ".Lbvoe_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbvoe_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_block_validate_ommers_empty`: probe BuildUnit. Reads
    (body_len, body_bytes) from host input, writes 8-byte status
    to OUTPUT. -/
def ziskBlockValidateOmmersEmptyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # body_len\n" ++
  "  addi a0, a3, 16             # body ptr\n" ++
  "  jal ra, block_validate_ommers_empty\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbvoe_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockValidateOmmersEmptyFunction ++ "\n" ++
  ".Lbvoe_pdone:"

def ziskBlockValidateOmmersEmptyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bvoe_struct:\n" ++
  "  .zero 48"

def ziskBlockValidateOmmersEmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateOmmersEmptyPrologue
  dataAsm     := ziskBlockValidateOmmersEmptyDataSection
}


def blockCountTransactionsFunction : String :=
  "block_count_transactions:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s1, a1                   # body_rlp_len\n" ++
  "  mv s2, a2                   # count out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Step 1: block_body_decode \u2192 bct_struct.\n" ++
  "  la a2, bct_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbct_body_fail\n" ++
  "  # Step 2: rlp_list_count_items on txs sub-list.\n" ++
  "  la t0, bct_struct\n" ++
  "  ld t1, 0(t0)                # txs_offset\n" ++
  "  ld t2, 8(t0)                # txs_length\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  beqz a0, .Lbct_ret\n" ++
  "  li a0, 101\n" ++
  "  j .Lbct_ret\n" ++
  ".Lbct_body_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbct_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_count_transactions`: probe BuildUnit. Reads
    (body_len, body_bytes), writes (status, tx_count) to OUTPUT. -/
def ziskBlockCountTransactionsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # body_len\n" ++
  "  addi a0, a3, 16             # body ptr\n" ++
  "  li a2, 0xa0010008           # count out\n" ++
  "  jal ra, block_count_transactions\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbct_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockCountTransactionsFunction ++ "\n" ++
  ".Lbct_pdone:"

def ziskBlockCountTransactionsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bct_struct:\n" ++
  "  .zero 48"

def ziskBlockCountTransactionsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockCountTransactionsPrologue
  dataAsm     := ziskBlockCountTransactionsDataSection
}


/-! ## block_body_blob_gas_total -- PR-K89

    Sum blob_gas_used over all EIP-4844 (type 3) txs in a block body:

      block.blob_gas_used = sum(
        len(tx.blob_versioned_hashes) × GAS_PER_BLOB
        for tx in block.transactions
        if tx.type == 3
      )

    Useful for the consensus rule
    `header.blob_gas_used == this sum` (post-Cancun).

    Composes:
      - PR-K83 `block_body_decode`            — split body
      - PR-K47 `rlp_list_count_items`         — number of txs
      - PR-K20 `rlp_list_nth_item`            — i-th tx bytes
      - PR-K40 `tx_type_dispatch`             — typed-tx detector
      - PR-K88 `tx_eip4844_compute_blob_gas`  — per-tx blob gas

    Iteration policy: skip every non-type-3 tx without examining
    its body. Pre-Cancun blocks (no type-3 txs) return 0 cleanly.

    Status encoding (callers can floor(status/100) to identify
    the failing step):

      0          : success
      1          : block_body_decode failed
      101        : rlp_list_count_items failed
      201        : rlp_list_nth_item failed
      301        : tx_type_dispatch failed
      401..402   : tx_eip4844_compute_blob_gas failed
                   (1=K45 decode fail, 2=K64 sum fail)

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : gas_per_blob (u64; 131072 on mainnet Cancun)
      a3 (input)  : u64 out ptr (receives total blob_gas_used)
      ra (input)  : return
      a0 (output) : composite status code

    Uses 48 bytes `.data` scratch (`bbbgt_struct`) plus the small
    scratch buffers inherited from K88 / K83. -/
def blockBodyBlobGasTotalFunction : String :=
  "block_body_blob_gas_total:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s3, a2                   # gas_per_blob\n" ++
  "  mv s4, a3                   # out ptr\n" ++
  "  li s5, 0                    # total = 0\n" ++
  "  # Step 1: block_body_decode → bbbgt_struct\n" ++
  "  la a2, bbbgt_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbbbgt_body_fail\n" ++
  "  # Load txs sub-list bounds.\n" ++
  "  la t0, bbbgt_struct\n" ++
  "  ld t1, 0(t0)                # txs_offset\n" ++
  "  ld s2, 8(t0)                # s2 = txs_length\n" ++
  "  add s1, s0, t1              # s1 = absolute txs ptr\n" ++
  "  # Step 2: tx_count = rlp_list_count_items(txs)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  la a2, bbbgt_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  beqz a0, .Lbbbgt_loop_init\n" ++
  "  li a0, 101\n" ++
  "  j .Lbbbgt_ret\n" ++
  ".Lbbbgt_loop_init:\n" ++
  "  la t0, bbbgt_count\n" ++
  "  ld s7, 0(t0)                # s7 = tx_count\n" ++
  "  li s6, 0                    # s6 = i\n" ++
  ".Lbbbgt_loop:\n" ++
  "  beq s6, s7, .Lbbbgt_done\n" ++
  "  # rlp_list_nth_item(s1, s2, s6, &item_off, &item_len)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s6\n" ++
  "  la a3, bbbgt_item_off\n" ++
  "  la a4, bbbgt_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  beqz a0, .Lbbbgt_after_nth\n" ++
  "  li a0, 201\n" ++
  "  j .Lbbbgt_ret\n" ++
  ".Lbbbgt_after_nth:\n" ++
  "  la t0, bbbgt_item_off\n" ++
  "  ld t1, 0(t0)                # item_off\n" ++
  "  la t0, bbbgt_item_len\n" ++
  "  ld t2, 0(t0)                # item_len\n" ++
  "  add t3, s1, t1              # tx_ptr = txs + item_off\n" ++
  "  # tx_type_dispatch(tx_ptr, item_len, &type, &inner_off)\n" ++
  "  mv a0, t3\n" ++
  "  mv a1, t2\n" ++
  "  la a2, bbbgt_type\n" ++
  "  la a3, bbbgt_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Lbbbgt_after_dispatch\n" ++
  "  li a0, 301\n" ++
  "  j .Lbbbgt_ret\n" ++
  ".Lbbbgt_after_dispatch:\n" ++
  "  la t0, bbbgt_type\n" ++
  "  ld t1, 0(t0)                # type\n" ++
  "  li t4, 3\n" ++
  "  bne t1, t4, .Lbbbgt_step\n" ++
  "  # type 3: compute blob_gas\n" ++
  "  la t0, bbbgt_item_off\n" ++
  "  ld t1, 0(t0)                # item_off\n" ++
  "  la t0, bbbgt_item_len\n" ++
  "  ld t2, 0(t0)                # item_len\n" ++
  "  la t0, bbbgt_inner_off\n" ++
  "  ld t5, 0(t0)                # inner_off\n" ++
  "  add t3, s1, t1\n" ++
  "  add a0, t3, t5              # inner_ptr = tx_ptr + inner_off\n" ++
  "  sub a1, t2, t5              # inner_len = item_len - inner_off\n" ++
  "  mv a2, s3                   # gas_per_blob\n" ++
  "  la a3, bbbgt_blob_gas\n" ++
  "  jal ra, tx_eip4844_compute_blob_gas\n" ++
  "  beqz a0, .Lbbbgt_after_blob\n" ++
  "  li t0, 400\n" ++
  "  add a0, a0, t0              # 1 → 401, 2 → 402\n" ++
  "  j .Lbbbgt_ret\n" ++
  ".Lbbbgt_after_blob:\n" ++
  "  la t0, bbbgt_blob_gas\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s5, s5, t1              # total += blob_gas\n" ++
  ".Lbbbgt_step:\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lbbbgt_loop\n" ++
  ".Lbbbgt_done:\n" ++
  "  sd s5, 0(s4)                # *out = total\n" ++
  "  li a0, 0\n" ++
  "  j .Lbbbgt_ret\n" ++
  ".Lbbbgt_body_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbbbgt_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_block_body_blob_gas_total`: probe BuildUnit. Reads
    (body_len, gas_per_blob, body_bytes) from host input,
    writes (status, total_blob_gas) to OUTPUT (16 bytes). -/
def ziskBlockBodyBlobGasTotalPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # body_len\n" ++
  "  ld a2, 16(a4)               # gas_per_blob\n" ++
  "  addi a0, a4, 24             # body ptr\n" ++
  "  li a3, 0xa0010008           # out u64 ptr\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, block_body_blob_gas_total\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbbbgt_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  blobGasUsedFromVersionedHashesFunction ++ "\n" ++
  txEip4844ComputeBlobGasFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyBlobGasTotalFunction ++ "\n" ++
  ".Lbbbgt_pdone:"

def ziskBlockBodyBlobGasTotalDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t48_offset:\n" ++
  "  .zero 8\n" ++
  "t48_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bgvh_count_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "tcbg_struct:\n" ++
  "  .zero 248\n" ++
  ".balign 8\n" ++
  "bbbgt_struct:\n" ++
  "  .zero 48\n" ++
  ".balign 8\n" ++
  "bbbgt_count:\n" ++
  "  .zero 8\n" ++
  "bbbgt_item_off:\n" ++
  "  .zero 8\n" ++
  "bbbgt_item_len:\n" ++
  "  .zero 8\n" ++
  "bbbgt_type:\n" ++
  "  .zero 8\n" ++
  "bbbgt_inner_off:\n" ++
  "  .zero 8\n" ++
  "bbbgt_blob_gas:\n" ++
  "  .zero 8"

def ziskBlockBodyBlobGasTotalProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockBodyBlobGasTotalPrologue
  dataAsm     := ziskBlockBodyBlobGasTotalDataSection
}

/-! ## block_validate_blob_gas_consistency -- PR-K91

    Cancun-era consensus rule: the value of `header.blob_gas_used`
    must equal the sum of per-tx blob gas across the block's body.

      header.blob_gas_used == sum(
        len(tx.blob_versioned_hashes) × GAS_PER_BLOB
        for tx in block.transactions
        if tx.type == 3
      )

    Composes:
      - PR-K53 `rlp_field_to_u64`        — extract header field 17
      - PR-K89 `block_body_blob_gas_total` — sum over body

    The Python reference (`forks/amsterdam/fork.py`) enforces this
    inside `apply_body`. This helper packages the check into a
    single ECALL-shaped routine so callers don't need to thread
    intermediate values through registers.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : body_rlp ptr
      a3 (input)  : body_rlp byte length
      a4 (input)  : gas_per_blob (u64; 131072 on mainnet Cancun)
      ra (input)  : return
      a0 (output) : composite status code

    Status decade encoding (floor(status/100) identifies the
    failing step):

      0          : success — header.blob_gas_used == body total
      1          : header parse / field 17 missing / not u64
      2          : mismatch (header.blob_gas_used ≠ body total)
      101        : body decode failed
      201        : body rlp_list_count_items failed
      301        : body rlp_list_nth_item failed
      401        : body tx_type_dispatch failed
      501..502   : body tx_eip4844_compute_blob_gas forwarded
                   (501 = K45 decode, 502 = K64 sum)

    Uses 32 bytes of `.data` scratch (`bvbgc_header_bgu` +
    `bvbgc_body_total`) plus the scratch buffers inherited from
    PR-K89 / K88 / K83. -/
def blockValidateBlobGasConsistencyFunction : String :=
  "block_validate_blob_gas_consistency:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a2                   # body_rlp ptr\n" ++
  "  mv s1, a3                   # body_len\n" ++
  "  mv s2, a4                   # gas_per_blob\n" ++
  "  # Step 1: extract header.blob_gas_used (field 17, u64).\n" ++
  "  # a0,a1 still hold (header_ptr, header_len).\n" ++
  "  li a2, 17\n" ++
  "  la a3, bvbgc_header_bgu\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  beqz a0, .Lbvbgc_step2\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvbgc_ret\n" ++
  ".Lbvbgc_step2:\n" ++
  "  # Step 2: body total via K89.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s2                   # gas_per_blob\n" ++
  "  la a3, bvbgc_body_total\n" ++
  "  jal ra, block_body_blob_gas_total\n" ++
  "  beqz a0, .Lbvbgc_compare\n" ++
  "  # K89 returns: 1=body decode, 101=count, 201=nth, 301=dispatch,\n" ++
  "  # 401..402=K88 forwarded. Re-map onto our 101+ decade space.\n" ++
  "  li t0, 100\n" ++
  "  add a0, a0, t0              # 1→101, 101→201, 201→301, 301→401,\n" ++
  "                              # 401→501, 402→502\n" ++
  "  j .Lbvbgc_ret\n" ++
  ".Lbvbgc_compare:\n" ++
  "  la t0, bvbgc_header_bgu\n" ++
  "  ld t1, 0(t0)\n" ++
  "  la t0, bvbgc_body_total\n" ++
  "  ld t2, 0(t0)\n" ++
  "  beq t1, t2, .Lbvbgc_ok\n" ++
  "  li a0, 2\n" ++
  "  j .Lbvbgc_ret\n" ++
  ".Lbvbgc_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lbvbgc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_validate_blob_gas_consistency`: probe BuildUnit.
    Input layout (LE u64s + variable bytes):
      bytes  0.. 8 : header_len
      bytes  8..16 : body_len
      bytes 16..24 : gas_per_blob
      bytes 24..   : header_rlp ‖ body_rlp (concatenated, no padding
                     between)
    OUTPUT layout (8 bytes):
      bytes  0.. 8 : status code -/
def ziskBlockValidateBlobGasConsistencyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # header_len\n" ++
  "  ld a3, 16(a5)               # body_len\n" ++
  "  ld a4, 24(a5)               # gas_per_blob\n" ++
  "  addi a0, a5, 32             # header_ptr\n" ++
  "  add a2, a0, a1              # body_ptr = header_ptr + header_len\n" ++
  "  jal ra, block_validate_blob_gas_consistency\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbvbgc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  blobGasUsedFromVersionedHashesFunction ++ "\n" ++
  txEip4844ComputeBlobGasFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyBlobGasTotalFunction ++ "\n" ++
  blockValidateBlobGasConsistencyFunction ++ "\n" ++
  ".Lbvbgc_pdone:"

def ziskBlockValidateBlobGasConsistencyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t48_offset:\n" ++
  "  .zero 8\n" ++
  "t48_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bgvh_count_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "tcbg_struct:\n" ++
  "  .zero 248\n" ++
  ".balign 8\n" ++
  "bbbgt_struct:\n" ++
  "  .zero 48\n" ++
  ".balign 8\n" ++
  "bbbgt_count:\n" ++
  "  .zero 8\n" ++
  "bbbgt_item_off:\n" ++
  "  .zero 8\n" ++
  "bbbgt_item_len:\n" ++
  "  .zero 8\n" ++
  "bbbgt_type:\n" ++
  "  .zero 8\n" ++
  "bbbgt_inner_off:\n" ++
  "  .zero 8\n" ++
  "bbbgt_blob_gas:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bvbgc_header_bgu:\n" ++
  "  .zero 8\n" ++
  "bvbgc_body_total:\n" ++
  "  .zero 8"

def ziskBlockValidateBlobGasConsistencyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateBlobGasConsistencyPrologue
  dataAsm     := ziskBlockValidateBlobGasConsistencyDataSection
}

/-! ## block_compute_tx_hashes -- PR-K97

    Walk the block body's `transactions` RLP list and compute the
    keccak256 of each encoded tx, packed into a contiguous output
    buffer. For each item returned by PR-K20 `rlp_list_nth_item`:

      tx_hash = keccak256(tx_bytes_as_returned_by_nth_item)

    `rlp_list_nth_item` returns the byte-string content for typed
    txs (so for a type-3 EIP-4844 tx the bytes are
    `[0x03 || rlp(inner)]`) and the full RLP list bytes for legacy
    txs. In both cases the tx hash on Ethereum is
    `keccak256(encoded_bytes)`, which is precisely what this helper
    computes — matching what `Block.transactions` callers feed
    downstream (receipts, MPT keys, etc.).

    Composes:
      - PR-K47 `rlp_list_count_items` — N
      - PR-K20 `rlp_list_nth_item`    — per-item bounds
      - PR-K3  `zkvm_keccak256`       — per-item hash

    Calling convention:
      a0 (input)  : txs_list_rlp ptr (the txs sub-list bytes)
      a1 (input)  : txs_list byte length
      a2 (input)  : output buffer ptr (must hold N × 32 bytes)
      a3 (input)  : u64 out count ptr (writes N on success)
      ra (input)  : return
      a0 (output) : composite status

    Status decade encoding:
      0          : success — N hashes written, *count = N
      101        : `rlp_list_count_items` failed
      201        : `rlp_list_nth_item` failed (mid-loop)

    Uses 32 bytes of `.data` scratch (`bcth_item_off` +
    `bcth_item_len` + `bcth_count`). -/
def blockComputeTxHashesFunction : String :=
  "block_compute_tx_hashes:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # txs_list ptr\n" ++
  "  mv s1, a1                   # txs_len\n" ++
  "  mv s2, a2                   # out hashes buffer\n" ++
  "  mv s3, a3                   # out count ptr\n" ++
  "  # Step 1: rlp_list_count_items.\n" ++
  "  la a2, bcth_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  beqz a0, .Lbcth_loop_init\n" ++
  "  li a0, 101\n" ++
  "  j .Lbcth_ret\n" ++
  ".Lbcth_loop_init:\n" ++
  "  la t0, bcth_count\n" ++
  "  ld s5, 0(t0)                # N = tx_count\n" ++
  "  li s4, 0                    # i = 0\n" ++
  ".Lbcth_loop:\n" ++
  "  beq s4, s5, .Lbcth_done\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s4\n" ++
  "  la a3, bcth_item_off\n" ++
  "  la a4, bcth_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  beqz a0, .Lbcth_after_nth\n" ++
  "  li a0, 201\n" ++
  "  j .Lbcth_ret\n" ++
  ".Lbcth_after_nth:\n" ++
  "  la t0, bcth_item_off\n" ++
  "  ld t1, 0(t0)\n" ++
  "  la t0, bcth_item_len\n" ++
  "  ld t2, 0(t0)\n" ++
  "  add a0, s0, t1              # tx_ptr\n" ++
  "  mv a1, t2                   # tx_len\n" ++
  "  slli s6, s4, 5              # i × 32\n" ++
  "  add a2, s2, s6              # &out[i*32]\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lbcth_loop\n" ++
  ".Lbcth_done:\n" ++
  "  sd s5, 0(s3)                # *count = N\n" ++
  "  li a0, 0\n" ++
  ".Lbcth_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_block_compute_tx_hashes`: probe BuildUnit. Reads
    (txs_list_len, txs_list_bytes) from host input, writes
    (status, count, N × 32-byte hashes) to OUTPUT. The host caller
    must size OUTPUT for at least 16 + N × 32 bytes.
    Input layout:
      bytes  0.. 8 : txs_list_len
      bytes  8..   : txs_list RLP bytes
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : count (u64 LE)
      bytes 16..   : N concatenated 32-byte hashes -/
def ziskBlockComputeTxHashesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # txs_list_len\n" ++
  "  addi a0, a4, 16             # txs_list ptr\n" ++
  "  li a2, 0xa0010010           # hashes buffer (OUTPUT + 16)\n" ++
  "  li a3, 0xa0010008           # count ptr (OUTPUT + 8)\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, block_compute_tx_hashes\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbcth_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  blockComputeTxHashesFunction ++ "\n" ++
  ".Lbcth_pdone:"

def ziskBlockComputeTxHashesDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "bcth_count:\n" ++
  "  .zero 8\n" ++
  "bcth_item_off:\n" ++
  "  .zero 8\n" ++
  "bcth_item_len:\n" ++
  "  .zero 8"

def ziskBlockComputeTxHashesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockComputeTxHashesPrologue
  dataAsm     := ziskBlockComputeTxHashesDataSection
}

end EvmAsm.Codegen
