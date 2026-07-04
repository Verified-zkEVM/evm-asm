/-
  EvmAsm.Codegen.Programs.TxBlobGas

  Blob-gas helpers for EIP-4844 transactions.

-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxDecode
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
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
  -- cursor-walk helpers (closure-drift fix for rewritten decoders)
  rlpWalkHelpersClosure ++ "\n" ++
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
def txEip4844ValidateBlobHashes_prog : Program :=
  [ .ADDI .x2 .x2 (-72 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x12,
    .MV .x18 .x13,
    .SD .x18 .x0 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.tcbg_struct (GuestAddrs.tx_eip4844_validate_blob_hashes + 52)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tcbg_struct (GuestAddrs.tx_eip4844_validate_blob_hashes + 52)),
    .MV .x5 .x12,
    .LI .x6 (31 : Word),
    .BEQ .x6 .x0 (20 : BitVec 13),
    .SD .x5 .x0 (0 : BitVec 12),
    .ADDI .x5 .x5 (8 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .JAL .x1 (jalOff GuestAddrs.tx_eip4844_decode (GuestAddrs.tx_eip4844_validate_blob_hashes + 88)),
    .BNE .x10 .x0 (184 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.tcbg_struct (GuestAddrs.tx_eip4844_validate_blob_hashes + 96)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tcbg_struct (GuestAddrs.tx_eip4844_validate_blob_hashes + 96)),
    .LWU .x6 .x5 (168 : BitVec 12),
    .LWU .x7 .x5 (172 : BitVec 12),
    .ADD .x19 .x8 .x6,
    .MV .x20 .x7,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .AUIPC .x12 (laHi GuestAddrs.bgvh_count_scratch (GuestAddrs.tx_eip4844_validate_blob_hashes + 128)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bgvh_count_scratch (GuestAddrs.tx_eip4844_validate_blob_hashes + 128)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.tx_eip4844_validate_blob_hashes + 136)),
    .BNE .x10 .x0 (144 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.bgvh_count_scratch (GuestAddrs.tx_eip4844_validate_blob_hashes + 144)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bgvh_count_scratch (GuestAddrs.tx_eip4844_validate_blob_hashes + 144)),
    .LD .x22 .x5 (0 : BitVec 12),
    .SD .x18 .x22 (0 : BitVec 12),
    .BEQ .x22 .x0 (132 : BitVec 13),
    .BLTU .x9 .x22 (136 : BitVec 13),
    .LI .x21 (0 : Word),
    .BEQ .x21 .x22 (96 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x20,
    .MV .x12 .x21,
    .AUIPC .x13 (laHi GuestAddrs.t48_offset (GuestAddrs.tx_eip4844_validate_blob_hashes + 188)),
    .ADDI .x13 .x13 (laLo GuestAddrs.t48_offset (GuestAddrs.tx_eip4844_validate_blob_hashes + 188)),
    .AUIPC .x14 (laHi GuestAddrs.t48_length (GuestAddrs.tx_eip4844_validate_blob_hashes + 196)),
    .ADDI .x14 .x14 (laLo GuestAddrs.t48_length (GuestAddrs.tx_eip4844_validate_blob_hashes + 196)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.tx_eip4844_validate_blob_hashes + 204)),
    .BNE .x10 .x0 (100 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.t48_length (GuestAddrs.tx_eip4844_validate_blob_hashes + 212)),
    .ADDI .x5 .x5 (laLo GuestAddrs.t48_length (GuestAddrs.tx_eip4844_validate_blob_hashes + 212)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (32 : Word),
    .BNE .x6 .x7 (80 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.t48_offset (GuestAddrs.tx_eip4844_validate_blob_hashes + 232)),
    .ADDI .x5 .x5 (laLo GuestAddrs.t48_offset (GuestAddrs.tx_eip4844_validate_blob_hashes + 232)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x7 .x19 .x7,
    .LBU .x28 .x7 (0 : BitVec 12),
    .LI .x29 (1 : Word),
    .BNE .x28 .x29 (60 : BitVec 13),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (-92 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (48 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (40 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (32 : BitVec 21),
    .LI .x10 (3 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (4 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (5 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (6 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (72 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txEip4844ValidateBlobHashes_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txEip4844ValidateBlobHashes_relocs : RelocTable :=
  [ (13, .la .x12 "tcbg_struct"),
    (22, .jal .x1 "tx_eip4844_decode"),
    (24, .la .x5 "tcbg_struct"),
    (32, .la .x12 "bgvh_count_scratch"),
    (34, .jal .x1 "rlp_list_count_items"),
    (36, .la .x5 "bgvh_count_scratch"),
    (47, .la .x13 "t48_offset"),
    (49, .la .x14 "t48_length"),
    (51, .jal .x1 "rlp_list_nth_item"),
    (53, .la .x5 "t48_length"),
    (58, .la .x5 "t48_offset") ]

def txEip4844ValidateBlobHashesFunction : String :=
  "tx_eip4844_validate_blob_hashes:\n" ++ emitProgramR txEip4844ValidateBlobHashes_prog txEip4844ValidateBlobHashes_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txEip4844ValidateBlobHashes_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txEip4844ValidateBlobHashesFunction_eq_prog :
    txEip4844ValidateBlobHashesFunction = "tx_eip4844_validate_blob_hashes:\n" ++ emitProgramR txEip4844ValidateBlobHashes_prog txEip4844ValidateBlobHashes_relocs := rfl

#guard txEip4844ValidateBlobHashesFunction.startsWith "tx_eip4844_validate_blob_hashes:\n"
#guard txEip4844ValidateBlobHashes_prog.length = 90
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
  -- cursor-walk helpers (closure-drift fix for rewritten decoders)
  rlpWalkHelpersClosure ++ "\n" ++
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
  "t48_offset:\n" ++
  "  .zero 8\n" ++
  "t48_length:\n" ++
  "  .zero 8\n" ++
  "bgvh_count_scratch:\n" ++
  "  .zero 8\n" ++
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
      a0 (input)  : execution_payload SSZ ptr
      a1 (input)  : SSZ versioned_hashes ptr (packed Bytes32 elements)
      a2 (input)  : SSZ versioned_hashes byte length
        0 : match
        1 : malformed SSZ tx list or versioned_hashes list
        2 : tx dispatch/decode failed
        3 : malformed blob hash item
        4 : mismatch / missing / extra hash
    The helper intentionally has no fixed tx-count cap: future EEST fixtures can
    add transactions without changing the walker. -/
def sszTxListVersionedHashesMatch_prog : Program :=
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
    .ANDI .x5 .x18 (31 : BitVec 12),
    .BNE .x5 .x0 (528 : BitVec 13),
    .SRLI .x19 .x18 (5 : BitVec 6),
    .LI .x20 (0 : Word),
    .ADDI .x10 .x8 (504 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.ssz_tx_list_versioned_hashes_match + 88)),
    .MV .x21 .x10,
    .ADDI .x10 .x8 (508 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.ssz_tx_list_versioned_hashes_match + 100)),
    .ADD .x5 .x8 .x10,
    .ADD .x22 .x8 .x21,
    .BLTU .x5 .x22 (488 : BitVec 13),
    .SUB .x23 .x5 .x22,
    .BEQ .x23 .x0 (468 : BitVec 13),
    .LI .x5 (4 : Word),
    .BLTU .x23 .x5 (472 : BitVec 13),
    .MV .x10 .x22,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.ssz_tx_list_versioned_hashes_match + 136)),
    .ANDI .x5 .x10 (3 : BitVec 12),
    .BEQ .x10 .x0 (456 : BitVec 13),
    .BLTU .x23 .x10 (452 : BitVec 13),
    .SRLI .x24 .x10 (2 : BitVec 6),
    .LI .x25 (0 : Word),
    .BEQ .x25 .x24 (428 : BitVec 13),
    .SLLI .x5 .x25 (2 : BitVec 6),
    .ADD .x6 .x22 .x5,
    .MV .x10 .x6,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.ssz_tx_list_versioned_hashes_match + 176)),
    .MV .x26 .x10,
    .SLLI .x5 .x24 (2 : BitVec 6),
    .BLTU .x26 .x5 (412 : BitVec 13),
    .ADDI .x5 .x25 (1 : BitVec 12),
    .BEQ .x5 .x24 (24 : BitVec 13),
    .SLLI .x6 .x5 (2 : BitVec 6),
    .ADD .x6 .x22 .x6,
    .MV .x10 .x6,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.ssz_tx_list_versioned_hashes_match + 212)),
    .JAL .x0 (8 : BitVec 21),
    .MV .x10 .x23,
    .BLTU .x10 .x26 (376 : BitVec 13),
    .SUB .x27 .x10 .x26,
    .ADD .x5 .x22 .x26,
    .MV .x10 .x5,
    .MV .x11 .x27,
    .AUIPC .x12 (laHi GuestAddrs.tvhm_tx_type (GuestAddrs.ssz_tx_list_versioned_hashes_match + 244)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tvhm_tx_type (GuestAddrs.ssz_tx_list_versioned_hashes_match + 244)),
    .AUIPC .x13 (laHi GuestAddrs.tvhm_inner_off (GuestAddrs.ssz_tx_list_versioned_hashes_match + 252)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tvhm_inner_off (GuestAddrs.ssz_tx_list_versioned_hashes_match + 252)),
    .JAL .x1 (jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.ssz_tx_list_versioned_hashes_match + 260)),
    .BNE .x10 .x0 (344 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.tvhm_tx_type (GuestAddrs.ssz_tx_list_versioned_hashes_match + 268)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tvhm_tx_type (GuestAddrs.ssz_tx_list_versioned_hashes_match + 268)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (3 : Word),
    .BNE .x6 .x7 (296 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.tvhm_inner_off (GuestAddrs.ssz_tx_list_versioned_hashes_match + 288)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tvhm_inner_off (GuestAddrs.ssz_tx_list_versioned_hashes_match + 288)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BLTU .x27 .x6 (308 : BitVec 13),
    .ADD .x5 .x22 .x26,
    .ADD .x26 .x5 .x6,
    .SUB .x27 .x27 .x6,
    .MV .x10 .x26,
    .MV .x11 .x27,
    .AUIPC .x12 (laHi GuestAddrs.tvhm_struct (GuestAddrs.ssz_tx_list_versioned_hashes_match + 324)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tvhm_struct (GuestAddrs.ssz_tx_list_versioned_hashes_match + 324)),
    .JAL .x1 (jalOff GuestAddrs.tx_eip4844_decode (GuestAddrs.ssz_tx_list_versioned_hashes_match + 332)),
    .BNE .x10 .x0 (272 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.tvhm_struct (GuestAddrs.ssz_tx_list_versioned_hashes_match + 340)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tvhm_struct (GuestAddrs.ssz_tx_list_versioned_hashes_match + 340)),
    .LWU .x6 .x5 (168 : BitVec 12),
    .LWU .x7 .x5 (172 : BitVec 12),
    .ADD .x26 .x26 .x6,
    .MV .x27 .x7,
    .MV .x10 .x26,
    .MV .x11 .x27,
    .AUIPC .x12 (laHi GuestAddrs.tvhm_blob_count (GuestAddrs.ssz_tx_list_versioned_hashes_match + 372)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tvhm_blob_count (GuestAddrs.ssz_tx_list_versioned_hashes_match + 372)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.ssz_tx_list_versioned_hashes_match + 380)),
    .BNE .x10 .x0 (232 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.tvhm_blob_count (GuestAddrs.ssz_tx_list_versioned_hashes_match + 388)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tvhm_blob_count (GuestAddrs.ssz_tx_list_versioned_hashes_match + 388)),
    .LD .x5 .x5 (0 : BitVec 12),
    .LI .x6 (0 : Word),
    .BEQ .x6 .x5 (176 : BitVec 13),
    .BGEU .x20 .x19 (216 : BitVec 13),
    .MV .x10 .x26,
    .MV .x11 .x27,
    .MV .x12 .x6,
    .AUIPC .x13 (laHi GuestAddrs.tvhm_hash_off (GuestAddrs.ssz_tx_list_versioned_hashes_match + 424)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tvhm_hash_off (GuestAddrs.ssz_tx_list_versioned_hashes_match + 424)),
    .AUIPC .x14 (laHi GuestAddrs.tvhm_hash_len (GuestAddrs.ssz_tx_list_versioned_hashes_match + 432)),
    .ADDI .x14 .x14 (laLo GuestAddrs.tvhm_hash_len (GuestAddrs.ssz_tx_list_versioned_hashes_match + 432)),
    .AUIPC .x7 (laHi GuestAddrs.tvhm_blob_index (GuestAddrs.ssz_tx_list_versioned_hashes_match + 440)),
    .ADDI .x7 .x7 (laLo GuestAddrs.tvhm_blob_index (GuestAddrs.ssz_tx_list_versioned_hashes_match + 440)),
    .SD .x7 .x6 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.ssz_tx_list_versioned_hashes_match + 452)),
    .BNE .x10 .x0 (160 : BitVec 13),
    .AUIPC .x7 (laHi GuestAddrs.tvhm_blob_count (GuestAddrs.ssz_tx_list_versioned_hashes_match + 460)),
    .ADDI .x7 .x7 (laLo GuestAddrs.tvhm_blob_count (GuestAddrs.ssz_tx_list_versioned_hashes_match + 460)),
    .LD .x5 .x7 (0 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.tvhm_blob_index (GuestAddrs.ssz_tx_list_versioned_hashes_match + 472)),
    .ADDI .x7 .x7 (laLo GuestAddrs.tvhm_blob_index (GuestAddrs.ssz_tx_list_versioned_hashes_match + 472)),
    .LD .x6 .x7 (0 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.tvhm_hash_len (GuestAddrs.ssz_tx_list_versioned_hashes_match + 484)),
    .ADDI .x7 .x7 (laLo GuestAddrs.tvhm_hash_len (GuestAddrs.ssz_tx_list_versioned_hashes_match + 484)),
    .LD .x28 .x7 (0 : BitVec 12),
    .LI .x29 (32 : Word),
    .BNE .x28 .x29 (116 : BitVec 13),
    .AUIPC .x7 (laHi GuestAddrs.tvhm_hash_off (GuestAddrs.ssz_tx_list_versioned_hashes_match + 504)),
    .ADDI .x7 .x7 (laLo GuestAddrs.tvhm_hash_off (GuestAddrs.ssz_tx_list_versioned_hashes_match + 504)),
    .LD .x28 .x7 (0 : BitVec 12),
    .ADD .x28 .x26 .x28,
    .SLLI .x29 .x20 (5 : BitVec 6),
    .ADD .x29 .x9 .x29,
    .LI .x30 (0 : Word),
    .LI .x31 (32 : Word),
    .BEQ .x30 .x31 (32 : BitVec 13),
    .ADD .x31 .x28 .x30,
    .LBU .x31 .x31 (0 : BitVec 12),
    .ADD .x15 .x29 .x30,
    .LBU .x15 .x15 (0 : BitVec 12),
    .BNE .x31 .x15 (68 : BitVec 13),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .JAL .x0 (-172 : BitVec 21),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .JAL .x0 (-424 : BitVec 21),
    .BNE .x20 .x19 (36 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (36 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (28 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (20 : BitVec 21),
    .LI .x10 (3 : Word),
    .JAL .x0 (12 : BitVec 21),
    .LI .x10 (4 : Word),
    .JAL .x0 (4 : BitVec 21),
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

/-- Reloc side-table for `sszTxListVersionedHashesMatch_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def sszTxListVersionedHashesMatch_relocs : RelocTable :=
  [ (22, .jal .x1 "bgv_u32le"),
    (25, .jal .x1 "bgv_u32le"),
    (34, .jal .x1 "bgv_u32le"),
    (44, .jal .x1 "bgv_u32le"),
    (53, .jal .x1 "bgv_u32le"),
    (61, .la .x12 "tvhm_tx_type"),
    (63, .la .x13 "tvhm_inner_off"),
    (65, .jal .x1 "tx_type_dispatch"),
    (67, .la .x5 "tvhm_tx_type"),
    (72, .la .x5 "tvhm_inner_off"),
    (81, .la .x12 "tvhm_struct"),
    (83, .jal .x1 "tx_eip4844_decode"),
    (85, .la .x5 "tvhm_struct"),
    (93, .la .x12 "tvhm_blob_count"),
    (95, .jal .x1 "rlp_list_count_items"),
    (97, .la .x5 "tvhm_blob_count"),
    (106, .la .x13 "tvhm_hash_off"),
    (108, .la .x14 "tvhm_hash_len"),
    (110, .la .x7 "tvhm_blob_index"),
    (113, .jal .x1 "rlp_list_nth_item"),
    (115, .la .x7 "tvhm_blob_count"),
    (118, .la .x7 "tvhm_blob_index"),
    (121, .la .x7 "tvhm_hash_len"),
    (126, .la .x7 "tvhm_hash_off") ]

def sszTxListVersionedHashesMatchFunction : String :=
  "ssz_tx_list_versioned_hashes_match:\n" ++ emitProgramR sszTxListVersionedHashesMatch_prog sszTxListVersionedHashesMatch_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `sszTxListVersionedHashesMatch_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem sszTxListVersionedHashesMatchFunction_eq_prog :
    sszTxListVersionedHashesMatchFunction = "ssz_tx_list_versioned_hashes_match:\n" ++ emitProgramR sszTxListVersionedHashesMatch_prog sszTxListVersionedHashesMatch_relocs := rfl

#guard sszTxListVersionedHashesMatchFunction.startsWith "ssz_tx_list_versioned_hashes_match:\n"
#guard sszTxListVersionedHashesMatch_prog.length = 173
/-- `zisk_ssz_tx_list_versioned_hashes_match`: probe BuildUnit. Reads
    (tx_list_len, versioned_hashes_len, tx_list_bytes, versioned_hashes_bytes)
    from host input, wraps the tx list in a fake execution-payload SSZ section,
    and writes the helper status to OUTPUT[0..8). -/
def ziskSszTxListVersionedHashesMatchPrologue : String :=
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
  txTypeDispatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  -- cursor-walk helpers (closure-drift fix for rewritten decoders)
  rlpWalkHelpersClosure ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  sszTxListVersionedHashesMatchFunction ++ "\n" ++
  ".Ltvhmp_done:"
def ziskSszTxListVersionedHashesMatchDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  "t48_offset:\n  .zero 8\n" ++
  "t48_length:\n  .zero 8\n" ++
  "tvhm_tx_type:\n  .zero 8\n" ++
  "tvhm_inner_off:\n  .zero 8\n" ++
  "tvhm_blob_count:\n  .zero 8\n" ++
  "tvhm_blob_index:\n  .zero 8\n" ++
  "tvhm_hash_off:\n  .zero 8\n" ++
  "tvhm_hash_len:\n  .zero 8\n" ++
  "tvhm_struct:\n  .zero 248\n" ++
  "tvhm_probe_payload:\n  .zero 8192"
def ziskSszTxListVersionedHashesMatchProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszTxListVersionedHashesMatchPrologue
  dataAsm     := ziskSszTxListVersionedHashesMatchDataSection
}

end EvmAsm.Codegen
