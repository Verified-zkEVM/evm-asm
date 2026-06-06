/-
  EvmAsm.Codegen.Programs.TxBlobGas

  Blob-gas helpers for EIP-4844 transactions.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.TxDecode
import EvmAsm.Codegen.Programs.TxExtract

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## tx_eip4844_compute_blob_gas -- PR-K88

    Given an EIP-4844 (type 3) tx inner RLP body, decode it and
    compute the per-tx `blob_gas_used` field:

      blob_gas_used = len(tx.blob_versioned_hashes) × GAS_PER_BLOB

    Where `GAS_PER_BLOB = 131072` (mainnet Cancun); parameterized
    so the helper works across forks that adjust it.

    Composes:
      - PR-K45 `tx_eip4844_decode` — decode inner body → 248 B struct
      - PR-K64 `blob_gas_used_from_versioned_hashes` — count × gas_per_blob

    Useful for verifying that
    `header.blob_gas_used == sum(tx.blob_gas_used for tx in block)`.

    The K45 struct at offsets 168..172 (u32 LE) holds
    `blob_versioned_hashes_offset` (relative to `inner_ptr`), and
    offsets 172..176 hold `blob_versioned_hashes_length`. This
    helper reads those, computes the absolute pointer, and
    invokes K64.

    Calling convention:
      a0 (input)  : inner_rlp ptr (post-0x03 type byte)
      a1 (input)  : inner_rlp byte length
      a2 (input)  : gas_per_blob (u64; 131072 on mainnet)
      a3 (input)  : u64 out ptr (receives blob_gas_used)
      ra (input)  : return
      a0 (output) :
        0  : success
        1  : tx_eip4844_decode failed (parse error)
        2  : blob_gas_used_from_versioned_hashes failed (parse error)

    Uses 248 + 8 bytes of `.data` scratch (`tcbg_struct` for the
    decoded EIP-4844 struct, plus an inherited count scratch). -/
def txEip4844ComputeBlobGasFunction : String :=
  "tx_eip4844_compute_blob_gas:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # inner_rlp ptr\n" ++
  "  mv s1, a2                   # gas_per_blob\n" ++
  "  mv s2, a3                   # out ptr\n" ++
  "  # Step 1: K45 tx_eip4844_decode(inner, len, tcbg_struct)\n" ++
  "  la a2, tcbg_struct\n" ++
  "  # Pre-zero 248 bytes (31 dwords)\n" ++
  "  mv t0, a2; li t1, 31\n" ++
  ".Ltcbg_zinit:\n" ++
  "  beqz t1, .Ltcbg_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltcbg_zinit\n" ++
  ".Ltcbg_zdone:\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Ltcbg_decode_fail\n" ++
  "  # Step 2: K64 blob_gas_used_from_versioned_hashes(...)\n" ++
  "  la t0, tcbg_struct\n" ++
  "  lwu t1, 168(t0)             # blob_versioned_hashes_offset (u32)\n" ++
  "  lwu t2, 172(t0)             # blob_versioned_hashes_length (u32)\n" ++
  "  add a0, s0, t1              # absolute blob_list ptr\n" ++
  "  mv a1, t2                   # blob_list length\n" ++
  "  mv a2, s1                   # gas_per_blob\n" ++
  "  mv a3, s2                   # out ptr\n" ++
  "  jal ra, blob_gas_used_from_versioned_hashes\n" ++
  "  beqz a0, .Ltcbg_ret\n" ++
  "  li a0, 2\n" ++
  "  j .Ltcbg_ret\n" ++
  ".Ltcbg_decode_fail:\n" ++
  "  li a0, 1\n" ++
  ".Ltcbg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_tx_eip4844_compute_blob_gas`: probe BuildUnit. Reads
    (inner_len, gas_per_blob, inner_bytes) from host input,
    writes (status, blob_gas_used) to OUTPUT (16 bytes). -/
def ziskTxEip4844ComputeBlobGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # inner_len\n" ++
  "  ld a2, 16(a4)               # gas_per_blob\n" ++
  "  addi a0, a4, 24             # inner_ptr\n" ++
  "  li a3, 0xa0010008           # out u64 ptr\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, tx_eip4844_compute_blob_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Ltcbg_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  blobGasUsedFromVersionedHashesFunction ++ "\n" ++
  txEip4844ComputeBlobGasFunction ++ "\n" ++
  ".Ltcbg_pdone:"

def ziskTxEip4844ComputeBlobGasDataSection : String :=
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
  "  .zero 248"

def ziskTxEip4844ComputeBlobGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip4844ComputeBlobGasPrologue
  dataAsm     := ziskTxEip4844ComputeBlobGasDataSection
}

/-! ## tx_eip4844_validate_blob_hashes -- PR-K139

    Structural EIP-4844 blob-versioned-hash validation from
    execution-specs `check_transaction`:

      * the blob hash list is non-empty;
      * the list contains at most `max_blob_count` items (6 on mainnet);
      * every blob versioned hash is exactly 32 bytes;
      * every blob versioned hash starts with the KZG version byte `0x01`.

    Calling convention:
      a0 (input)  : inner_rlp ptr (post-0x03 type byte)
      a1 (input)  : inner_rlp byte length
      a2 (input)  : max_blob_count
      a3 (input)  : u64 out ptr (receives blob hash count)
      ra (input)  : return
      a0 (output) :
        0  : success
        1  : tx_eip4844_decode failed
        2  : blob hash list count failed
        3  : zero blob hashes
        4  : too many blob hashes
        5  : malformed blob hash item / not 32 bytes
        6  : invalid KZG version byte

    Uses the shared K45 struct scratch and K64 count/item scratch slots. -/
def txEip4844ValidateBlobHashesFunction : String :=
  "tx_eip4844_validate_blob_hashes:\n" ++
  "  addi sp, sp, -72\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # inner_rlp ptr\n" ++
  "  mv s1, a2                   # max_blob_count\n" ++
  "  mv s2, a3                   # count out ptr\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Step 1: decode inner EIP-4844 body into tcbg_struct.\n" ++
  "  la a2, tcbg_struct\n" ++
  "  mv t0, a2; li t1, 31\n" ++
  ".Lt48v_zinit:\n" ++
  "  beqz t1, .Lt48v_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt48v_zinit\n" ++
  ".Lt48v_zdone:\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Lt48v_decode_fail\n" ++
  "  la t0, tcbg_struct\n" ++
  "  lwu t1, 168(t0)             # blob_versioned_hashes_offset\n" ++
  "  lwu t2, 172(t0)             # blob_versioned_hashes_length\n" ++
  "  add s3, s0, t1              # blob list ptr\n" ++
  "  mv s4, t2                   # blob list length\n" ++
  "  # Step 2: count top-level blob hashes.\n" ++
  "  mv a0, s3; mv a1, s4\n" ++
  "  la a2, bgvh_count_scratch\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lt48v_count_fail\n" ++
  "  la t0, bgvh_count_scratch\n" ++
  "  ld s6, 0(t0)                # blob hash count\n" ++
  "  sd s6, 0(s2)\n" ++
  "  beqz s6, .Lt48v_zero_blobs\n" ++
  "  bltu s1, s6, .Lt48v_too_many\n" ++
  "  # Step 3: validate each item length and KZG version byte.\n" ++
  "  li s5, 0\n" ++
  ".Lt48v_loop:\n" ++
  "  beq s5, s6, .Lt48v_ok\n" ++
  "  mv a0, s3; mv a1, s4; mv a2, s5\n" ++
  "  la a3, t48_offset\n" ++
  "  la a4, t48_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt48v_bad_item\n" ++
  "  la t0, t48_length\n" ++
  "  ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lt48v_bad_item\n" ++
  "  la t0, t48_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add t2, s3, t1\n" ++
  "  lbu t3, 0(t2)\n" ++
  "  li t4, 1\n" ++
  "  bne t3, t4, .Lt48v_bad_version\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lt48v_loop\n" ++
  ".Lt48v_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lt48v_ret\n" ++
  ".Lt48v_decode_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lt48v_ret\n" ++
  ".Lt48v_count_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Lt48v_ret\n" ++
  ".Lt48v_zero_blobs:\n" ++
  "  li a0, 3\n" ++
  "  j .Lt48v_ret\n" ++
  ".Lt48v_too_many:\n" ++
  "  li a0, 4\n" ++
  "  j .Lt48v_ret\n" ++
  ".Lt48v_bad_item:\n" ++
  "  li a0, 5\n" ++
  "  j .Lt48v_ret\n" ++
  ".Lt48v_bad_version:\n" ++
  "  li a0, 6\n" ++
  ".Lt48v_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 72\n" ++
  "  ret"

/-- `zisk_tx_eip4844_validate_blob_hashes`: probe BuildUnit. Reads
    (inner_len, max_blob_count, inner_bytes) from host input,
    writes (status, blob_hash_count) to OUTPUT (16 bytes). -/
def ziskTxEip4844ValidateBlobHashesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # inner_len\n" ++
  "  ld a2, 16(a4)               # max_blob_count\n" ++
  "  addi a0, a4, 24             # inner_ptr\n" ++
  "  li a3, 0xa0010008           # out u64 ptr\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, tx_eip4844_validate_blob_hashes\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lt48v_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  txEip4844ValidateBlobHashesFunction ++ "\n" ++
  ".Lt48v_pdone:"

def ziskTxEip4844ValidateBlobHashesDataSection : String :=
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
  "  .zero 248"

def ziskTxEip4844ValidateBlobHashesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip4844ValidateBlobHashesPrologue
  dataAsm     := ziskTxEip4844ValidateBlobHashesDataSection
}

/-! ## ssz_tx_list_versioned_hashes_match -- PR-K140

    Mirrors execution-specs `is_valid_versioned_hashes`: concatenate every
    EIP-4844 transaction's `blob_versioned_hashes`, in transaction order, and
    compare the resulting byte stream with
    `new_payload_request.versioned_hashes`.

    Calling convention:
      a0 (input)  : execution_payload SSZ ptr
      a1 (input)  : SSZ versioned_hashes ptr (packed Bytes32 elements)
      a2 (input)  : SSZ versioned_hashes byte length
      ra (input)  : return
      a0 (output) :
        0 : match
        1 : malformed SSZ tx list or versioned_hashes list
        2 : tx dispatch/decode failed
        3 : malformed blob hash item
        4 : mismatch / missing / extra hash

    The helper intentionally has no fixed tx-count cap: future EEST fixtures can
    add transactions without changing the walker. -/
def sszTxListVersionedHashesMatchFunction : String :=
  "ssz_tx_list_versioned_hashes_match:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # execution_payload ptr\n" ++
  "  mv s1, a1                   # versioned_hashes ptr\n" ++
  "  mv s2, a2                   # versioned_hashes byte length\n" ++
  "  andi t0, s2, 31\n" ++
  "  bnez t0, .Ltvhm_bad_ssz\n" ++
  "  srli s3, s2, 5              # expected hash count\n" ++
  "  li s4, 0                    # consumed hash count\n" ++
  "  addi a0, s0, 504; jal ra, bgv_u32le       # transactions_offset\n" ++
  "  mv s5, a0\n" ++
  "  addi a0, s0, 508; jal ra, bgv_u32le       # withdrawals_offset\n" ++
  "  add t0, s0, a0\n" ++
  "  add s6, s0, s5              # tx list ptr\n" ++
  "  bltu t0, s6, .Ltvhm_bad_ssz\n" ++
  "  sub s7, t0, s6              # tx list len\n" ++
  "  beqz s7, .Ltvhm_after_txs\n" ++
  "  li t0, 4\n" ++
  "  bltu s7, t0, .Ltvhm_bad_ssz\n" ++
  "  mv a0, s6; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3\n" ++
  "  bnez t0, .Ltvhm_bad_ssz\n" ++
  "  beqz a0, .Ltvhm_bad_ssz\n" ++
  "  bgtu a0, s7, .Ltvhm_bad_ssz\n" ++
  "  srli s8, a0, 2              # tx_count = first offset / 4\n" ++
  "  li s9, 0                    # tx index\n" ++
  ".Ltvhm_tx_loop:\n" ++
  "  beq s9, s8, .Ltvhm_after_txs\n" ++
  "  slli t0, s9, 2; add t1, s6, t0; mv a0, t1; jal ra, bgv_u32le\n" ++
  "  mv s10, a0                  # item_off\n" ++
  "  slli t0, s8, 2\n" ++
  "  bltu s10, t0, .Ltvhm_bad_ssz\n" ++
  "  addi t0, s9, 1\n" ++
  "  beq t0, s8, .Ltvhm_last_tx\n" ++
  "  slli t1, t0, 2; add t1, s6, t1; mv a0, t1; jal ra, bgv_u32le\n" ++
  "  j .Ltvhm_have_tx_end\n" ++
  ".Ltvhm_last_tx:\n" ++
  "  mv a0, s7\n" ++
  ".Ltvhm_have_tx_end:\n" ++
  "  bltu a0, s10, .Ltvhm_bad_ssz\n" ++
  "  bgtu a0, s7, .Ltvhm_bad_ssz\n" ++
  "  sub s11, a0, s10            # tx len\n" ++
  "  add t0, s6, s10             # tx ptr\n" ++
  "  mv a0, t0; mv a1, s11; la a2, tvhm_tx_type; la a3, tvhm_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Ltvhm_tx_fail\n" ++
  "  la t0, tvhm_tx_type; ld t1, 0(t0)\n" ++
  "  li t2, 3\n" ++
  "  bne t1, t2, .Ltvhm_next_tx\n" ++
  "  la t0, tvhm_inner_off; ld t1, 0(t0)\n" ++
  "  bgtu t1, s11, .Ltvhm_tx_fail\n" ++
  "  add t0, s6, s10; add s10, t0, t1      # inner ptr\n" ++
  "  sub s11, s11, t1                      # inner len\n" ++
  "  la a2, tvhm_struct\n" ++
  "  mv t0, a2; li t1, 31\n" ++
  ".Ltvhm_zinit:\n" ++
  "  beqz t1, .Ltvhm_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltvhm_zinit\n" ++
  ".Ltvhm_zdone:\n" ++
  "  mv a0, s10; mv a1, s11; la a2, tvhm_struct\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Ltvhm_tx_fail\n" ++
  "  la t0, tvhm_struct\n" ++
  "  lwu t1, 168(t0); lwu t2, 172(t0)\n" ++
  "  add s10, s10, t1             # blob hash list ptr\n" ++
  "  mv s11, t2                   # blob hash list len\n" ++
  "  mv a0, s10; mv a1, s11; la a2, tvhm_blob_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Ltvhm_bad_blob_item\n" ++
  "  la t0, tvhm_blob_count; ld t0, 0(t0)\n" ++
  "  li t1, 0\n" ++
  ".Ltvhm_blob_loop:\n" ++
  "  beq t1, t0, .Ltvhm_next_tx\n" ++
  "  bgeu s4, s3, .Ltvhm_mismatch\n" ++
  "  mv a0, s10; mv a1, s11; mv a2, t1; la a3, tvhm_hash_off; la a4, tvhm_hash_len\n" ++
  "  la t2, tvhm_blob_index; sd t1, 0(t2)\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  la t2, tvhm_blob_count; ld t0, 0(t2); la t2, tvhm_blob_index; ld t1, 0(t2)\n" ++
  "  bnez a0, .Ltvhm_bad_blob_item\n" ++
  "  la t2, tvhm_hash_len; ld t3, 0(t2)\n" ++
  "  li t4, 32\n" ++
  "  bne t3, t4, .Ltvhm_bad_blob_item\n" ++
  "  la t2, tvhm_hash_off; ld t3, 0(t2)\n" ++
  "  add t3, s10, t3              # actual hash ptr\n" ++
  "  slli t4, s4, 5\n" ++
  "  add t4, s1, t4               # expected hash ptr\n" ++
  "  li t5, 0\n" ++
  ".Ltvhm_hash_cmp:\n" ++
  "  li t6, 32\n" ++
  "  beq t5, t6, .Ltvhm_hash_equal\n" ++
  "  add t6, t3, t5; lbu t6, 0(t6)\n" ++
  "  add a5, t4, t5; lbu a5, 0(a5)\n" ++
  "  bne t6, a5, .Ltvhm_mismatch\n" ++
  "  addi t5, t5, 1\n" ++
  "  j .Ltvhm_hash_cmp\n" ++
  ".Ltvhm_hash_equal:\n" ++
  "  addi s4, s4, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  j .Ltvhm_blob_loop\n" ++
  ".Ltvhm_next_tx:\n" ++
  "  addi s9, s9, 1\n" ++
  "  j .Ltvhm_tx_loop\n" ++
  ".Ltvhm_after_txs:\n" ++
  "  bne s4, s3, .Ltvhm_mismatch\n" ++
  "  li a0, 0\n" ++
  "  j .Ltvhm_ret\n" ++
  ".Ltvhm_bad_ssz:\n" ++
  "  li a0, 1\n" ++
  "  j .Ltvhm_ret\n" ++
  ".Ltvhm_tx_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Ltvhm_ret\n" ++
  ".Ltvhm_bad_blob_item:\n" ++
  "  li a0, 3\n" ++
  "  j .Ltvhm_ret\n" ++
  ".Ltvhm_mismatch:\n" ++
  "  li a0, 4\n" ++
  ".Ltvhm_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_ssz_tx_list_versioned_hashes_match`: probe BuildUnit. Reads
    (tx_list_len, versioned_hashes_len, tx_list_bytes, versioned_hashes_bytes)
    from host input, wraps the tx list in a fake execution-payload SSZ section,
    and writes the helper status to OUTPUT[0..8). -/
def ziskSszTxListVersionedHashesMatchPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld s0, 8(a4)                # tx_list_len\n" ++
  "  ld s1, 16(a4)               # versioned_hashes_len\n" ++
  "  addi s2, a4, 24             # tx_list src\n" ++
  "  add s3, s2, s0              # versioned_hashes src\n" ++
  "  la s4, tvhm_probe_payload\n" ++
  "  li t0, 1024\n" ++
  "  sw t0, 504(s4)              # transactions_offset\n" ++
  "  add t1, t0, s0\n" ++
  "  sw t1, 508(s4)              # withdrawals_offset\n" ++
  "  add s5, s4, t0              # tx_list dst\n" ++
  "  li t2, 0\n" ++
  ".Ltvhmp_copy:\n" ++
  "  beq t2, s0, .Ltvhmp_copied\n" ++
  "  add t3, s2, t2; lbu t4, 0(t3)\n" ++
  "  add t3, s5, t2; sb t4, 0(t3)\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Ltvhmp_copy\n" ++
  ".Ltvhmp_copied:\n" ++
  "  mv a0, s4; mv a1, s3; mv a2, s1\n" ++
  "  jal ra, ssz_tx_list_versioned_hashes_match\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ltvhmp_done\n" ++
  bgvU32leFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  sszTxListVersionedHashesMatchFunction ++ "\n" ++
  ".Ltvhmp_done:"

def ziskSszTxListVersionedHashesMatchDataSection : String :=
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
  "tvhm_tx_type:\n  .zero 8\n" ++
  "tvhm_inner_off:\n  .zero 8\n" ++
  "tvhm_blob_count:\n  .zero 8\n" ++
  "tvhm_blob_index:\n  .zero 8\n" ++
  "tvhm_hash_off:\n  .zero 8\n" ++
  "tvhm_hash_len:\n  .zero 8\n" ++
  "tvhm_struct:\n  .zero 248\n" ++
  ".balign 8\n" ++
  "tvhm_probe_payload:\n  .zero 8192"

def ziskSszTxListVersionedHashesMatchProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszTxListVersionedHashesMatchPrologue
  dataAsm     := ziskSszTxListVersionedHashesMatchDataSection
}

/-! ## tx_calculate_total_blob_gas -- PR-K92

    Python reference (`forks/amsterdam/vm/gas.py`):

      def calculate_total_blob_gas(tx) -> U64:
          if isinstance(tx, BlobTransaction):
              return GAS_PER_BLOB * U64(len(tx.blob_versioned_hashes))
          else:
              return U64(0)

    Accepts a transaction in its encoded form (legacy RLP list,
    or typed `[type_byte || rlp(inner)]`) and returns the per-tx
    blob_gas_used: 0 for any non-EIP-4844 type, otherwise the
    blob-count × gas-per-blob product computed by PR-K88.

    Composes:
      - PR-K40 `tx_type_dispatch`           — typed-tx detector
      - PR-K88 `tx_eip4844_compute_blob_gas` — count × gas_per_blob

    Useful per-tx primitive for `apply_body` and for receipt-side
    bookkeeping that needs the same number on every tx without
    branching on type in the caller.

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : gas_per_blob (u64; 131072 on mainnet Cancun)
      a3 (input)  : u64 out ptr (receives total blob gas)
      ra (input)  : return
      a0 (output) : composite status code

    Status decade encoding (floor(status/100) identifies the
    failing step):

      0          : success
      1          : tx_type_dispatch failed (unknown tx type / empty)
      101..102   : tx_eip4844_compute_blob_gas forwarded
                   (101 = K45 decode, 102 = K64 sum)

    Uses two 8-byte `.data` scratch slots (`tctbg_type`,
    `tctbg_inner_off`) plus the buffers inherited from K88. -/
def txCalculateTotalBlobGasFunction : String :=
  "tx_calculate_total_blob_gas:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx_len\n" ++
  "  mv s3, a2                   # gas_per_blob (stash)\n" ++
  "  mv s2, a3                   # out ptr\n" ++
  "  # Default zero in case of early non-type-3 exit.\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Step 1: tx_type_dispatch(tx, len, &type, &inner_off)\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, tctbg_type\n" ++
  "  la a3, tctbg_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Lctbg_after_dispatch\n" ++
  "  li a0, 1\n" ++
  "  j .Lctbg_ret\n" ++
  ".Lctbg_after_dispatch:\n" ++
  "  la t0, tctbg_type\n" ++
  "  ld t1, 0(t0)\n" ++
  "  li t2, 3\n" ++
  "  bne t1, t2, .Lctbg_zero_ok\n" ++
  "  # type 3: compute blob gas via K88.\n" ++
  "  la t0, tctbg_inner_off\n" ++
  "  ld t3, 0(t0)\n" ++
  "  add a0, s0, t3              # inner_ptr\n" ++
  "  sub a1, s1, t3              # inner_len\n" ++
  "  mv a2, s3                   # gas_per_blob\n" ++
  "  mv a3, s2                   # out ptr\n" ++
  "  jal ra, tx_eip4844_compute_blob_gas\n" ++
  "  beqz a0, .Lctbg_ok\n" ++
  "  li t0, 100\n" ++
  "  add a0, a0, t0              # 1 → 101, 2 → 102\n" ++
  "  j .Lctbg_ret\n" ++
  ".Lctbg_zero_ok:\n" ++
  "  # *out already 0.\n" ++
  ".Lctbg_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lctbg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_calculate_total_blob_gas`: probe BuildUnit. Reads
    (tx_len, gas_per_blob, tx_bytes) from host input, writes
    (status, total_blob_gas) to OUTPUT (16 bytes). -/
def ziskTxCalculateTotalBlobGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # tx_len\n" ++
  "  ld a2, 16(a4)               # gas_per_blob\n" ++
  "  addi a0, a4, 24             # tx_ptr\n" ++
  "  li a3, 0xa0010008           # out u64 ptr\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, tx_calculate_total_blob_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lctbg_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  blobGasUsedFromVersionedHashesFunction ++ "\n" ++
  txEip4844ComputeBlobGasFunction ++ "\n" ++
  txCalculateTotalBlobGasFunction ++ "\n" ++
  ".Lctbg_pdone:"

def ziskTxCalculateTotalBlobGasDataSection : String :=
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
  "tctbg_type:\n" ++
  "  .zero 8\n" ++
  "tctbg_inner_off:\n" ++
  "  .zero 8"

def ziskTxCalculateTotalBlobGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxCalculateTotalBlobGasPrologue
  dataAsm     := ziskTxCalculateTotalBlobGasDataSection
}

end EvmAsm.Codegen
