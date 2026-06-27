/-
  EvmAsm.Codegen.Programs.TxTotalBlobGas

  EIP-4844 total blob-gas helper split out of `TxDecode.lean`.

  Hosts:
    K92  tx_calculate_total_blob_gas

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.TxDecode
import EvmAsm.Codegen.Programs.TxBlobGas

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

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
  -- cursor-walk helpers (closure-drift fix for rewritten decoders)
  rlpWalkHelpersClosure ++ "\n" ++
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
