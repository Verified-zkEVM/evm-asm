/-
  EvmAsm.Codegen.Programs.HeaderDecode

  Header decoders carved out of `EvmAsm.Codegen.Programs.Header`
  per the file-size hard cap. Hosts:

    K38  header_minimal_decode  (parent_hash + state_root + number + timestamp)
    K39  header_extended_decode (full Amsterdam header decode)
    K55  coinbase_extract_from_header (beneficiary getter)

  Compose K20 / K34 / K35 (RlpRead + Tx).

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## header_minimal_decode -- PR-K38

    Decode the 4 STF-essential fields of an RLP-encoded
    Ethereum block header into a flat 96-byte output struct:

       0..32   parent_hash    (RLP field 0)
      32..64   state_root     (RLP field 3)
      64..72   number (u64)   (RLP field 8)
      72..80   timestamp(u64) (RLP field 11; rejected if > 8 B)

    Header RLP field count varies by fork (15..22 fields).
    This decoder reads only the first 12 fields' indices, so
    it works on any post-Berlin header.

     Calling convention:
       a0 (input)  : header_rlp ptr
       a1 (input)  : header_rlp byte length
       a2 (input)  : 96-byte output struct ptr
       ra (input)  : return
       a0 (output) : 0 success / 1 parse fail (not an RLP list,
                     parent_hash or state_root not 32 bytes,
                     or timestamp > 8 bytes BE).

     Composes the cursor walker (`rlp_walk_init` +
     `rlp_walk_next` + `rlp_content_to_u64`). The four wanted
     fields live at indices {0,3,8,11}; the walker visits the
     first 12 items once (single O(N) pass), capturing the four
     wanted fields and skipping the eight in between. The hash
     fields are copied via 4 x 8-byte `ld`/`sd`. -/
def headerMinimalDecodeFunction : String :=
  "header_minimal_decode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr (base)\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  jal ra, rlp_walk_init      # a0=ptr,a1=len -> cursor,end,status\n" ++
  "  bnez a2, .Lhmd_fail\n" ++
  "  mv s1, a1                  # end\n" ++
  "  mv s3, a0                  # cursor\n" ++
  "  # field 0: parent_hash (32 bytes @ struct+0)\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhmd_fail\n" ++
  "  li t0, 32; bne a2, t0, .Lhmd_fail\n" ++
  "  sub t3, a0, a2             # content_ptr = advanced - len\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  # fields 1..2: skip (ommers_hash, beneficiary)\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhmd_fail\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhmd_fail\n" ++
  "  # field 3: state_root (32 bytes @ struct+32)\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhmd_fail\n" ++
  "  li t0, 32; bne a2, t0, .Lhmd_fail\n" ++
  "  sub t3, a0, a2\n" ++
  "  ld t4,  0(t3); sd t4, 32(s2)\n" ++
  "  ld t4,  8(t3); sd t4, 40(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 48(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 56(s2)\n" ++
  "  # fields 4..7: skip (state_root already read; roots/gas/etc)\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhmd_fail\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhmd_fail\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhmd_fail\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhmd_fail\n" ++
  "  # field 8: number (u64 @ struct+64)\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhmd_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lhmd_fail\n" ++
  "  sd a0, 64(s2)\n" ++
  "  # fields 9..10: skip (gas_limit, gas_used)\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhmd_fail\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhmd_fail\n" ++
  "  # field 11: timestamp (u64 @ struct+72)\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhmd_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lhmd_fail\n" ++
  "  sd a0, 72(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhmd_ret\n" ++
  ".Lhmd_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lhmd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_header_minimal_decode`: probe BuildUnit. Reads
    (header_len, header_bytes) from host input, writes
    (status, 96-byte struct) to OUTPUT. -/
def ziskHeaderMinimalDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 96 bytes.\n" ++
  "  mv t0, a2; li t1, 12\n" ++
  ".Lhmd_zinit:\n" ++
  "  beqz t1, .Lhmd_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lhmd_zinit\n" ++
  ".Lhmd_zdone:\n" ++
  "  jal ra, header_minimal_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhmd_pdone\n" ++
  rlpWalkInitFunction ++ "\n" ++
  rlpWalkNextFunction ++ "\n" ++
  rlpContentToU64Function ++ "\n" ++
  headerMinimalDecodeFunction ++ "\n" ++
  ".Lhmd_pdone:"

def ziskHeaderMinimalDecodeDataSection : String := ""

def ziskHeaderMinimalDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderMinimalDecodePrologue
  dataAsm     := ziskHeaderMinimalDecodeDataSection
}

/-! ## header_extended_decode -- PR-K39

    Extends PR-K38 `header_minimal_decode` with three more
    STF-essential fields:

       0..32   parent_hash    (field 0)
      32..64   state_root     (field 3)
      64..72   number         (field 8, u64)
      72..80   timestamp      (field 11, u64)
      80..88   gas_limit      (field 9, u64)
      88..96   gas_used       (field 10, u64)
      96..128  base_fee_per_gas (field 15, u256 BE)
     128..136  blob_gas_used    (field 17, u64)
     136..144  excess_blob_gas  (field 18, u64)

    The base_fee_per_gas field exists from EIP-1559 (London)
    onward. Headers older than London don't have it; this
    function rejects (status=1) if field 15 doesn't exist.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header byte length
      a2 (input)  : 144-byte output struct ptr
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail. -/
def headerExtendedDecodeFunction : String :=
  "header_extended_decode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr (base)\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  jal ra, rlp_walk_init      # a0=ptr,a1=len -> cursor,end,status\n" ++
  "  bnez a2, .Lhed_fail\n" ++
  "  mv s1, a1                  # end\n" ++
  "  mv s3, a0                  # cursor\n" ++
  "  # field 0: parent_hash (32 bytes @ struct+0)\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  li t0, 32; bne a2, t0, .Lhed_fail\n" ++
  "  sub t3, a0, a2\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  # fields 1..2: skip\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  # field 3: state_root (32 bytes @ struct+32)\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  li t0, 32; bne a2, t0, .Lhed_fail\n" ++
  "  sub t3, a0, a2\n" ++
  "  ld t4,  0(t3); sd t4, 32(s2)\n" ++
  "  ld t4,  8(t3); sd t4, 40(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 48(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 56(s2)\n" ++
  "  # fields 4..7: skip\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  # field 8: number (u64 @ struct+64)\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lhed_fail\n" ++
  "  sd a0, 64(s2)\n" ++
  "  # field 9: gas_limit (u64 @ struct+80)\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lhed_fail\n" ++
  "  sd a0, 80(s2)\n" ++
  "  # field 10: gas_used (u64 @ struct+88)\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lhed_fail\n" ++
  "  sd a0, 88(s2)\n" ++
  "  # field 11: timestamp (u64 @ struct+72)\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lhed_fail\n" ++
  "  sd a0, 72(s2)\n" ++
  "  # fields 12..14: skip\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  # field 15: base_fee_per_gas (u256 @ struct+96)\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2; addi a2, s2, 96\n" ++
  "  jal ra, rlp_content_to_u256_be\n" ++
  "  bnez a0, .Lhed_fail\n" ++
  "  # field 16: skip\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  # field 17: blob_gas_used (u64 @ struct+128)\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lhed_fail\n" ++
  "  sd a0, 128(s2)\n" ++
  "  # field 18: excess_blob_gas (u64 @ struct+136)\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  mv s3, a0; bnez a1, .Lhed_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lhed_fail\n" ++
  "  sd a0, 136(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhed_ret\n" ++
  ".Lhed_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lhed_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_header_extended_decode`: probe BuildUnit. -/
def ziskHeaderExtendedDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 144 bytes.\n" ++
  "  mv t0, a2; li t1, 18\n" ++
  ".Lhed_zinit:\n" ++
  "  beqz t1, .Lhed_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lhed_zinit\n" ++
  ".Lhed_zdone:\n" ++
  "  jal ra, header_extended_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhed_pdone\n" ++
  rlpWalkInitFunction ++ "\n" ++
  rlpWalkNextFunction ++ "\n" ++
  rlpContentToU64Function ++ "\n" ++
  rlpContentToU256BeFunction ++ "\n" ++
  headerExtendedDecodeFunction ++ "\n" ++
  ".Lhed_pdone:"

def ziskHeaderExtendedDecodeDataSection : String := ""

def ziskHeaderExtendedDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtendedDecodePrologue
  dataAsm     := ziskHeaderExtendedDecodeDataSection
}

/-! ## coinbase_extract_from_header -- PR-K55 beneficiary getter

    Extract the 20-byte beneficiary (coinbase) address — field 2
    of an RLP-encoded block header. Direct input to
    `process_transaction`'s priority-fee credit:

      coinbase.balance += effective_priority_fee × gas_used

    The header decoders PR-K38 / PR-K39 read parent_hash,
    state_root, gas_limit, gas_used, etc., but skip the
    beneficiary since it isn't part of the STF skeleton's
    minimal/extended struct. This helper is the dedicated getter
    for callers that only need the coinbase.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 20-byte output ptr (caller-supplied)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail (not a list or field
                    2 not 20 bytes). On failure, output is zeroed.

    Composes PR-K20 `rlp_list_nth_item`. Uses two 8-byte `.data`
    scratch slots (`ceh_offset`, `ceh_length`). -/
def coinbaseExtractFromHeaderFunction : String :=
  "coinbase_extract_from_header:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_len\n" ++
  "  mv s2, a2                  # output 20B ptr\n" ++
  "  # Get field 2 (coinbase) bounds.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, ceh_offset; la a4, ceh_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lceh_fail\n" ++
  "  la t0, ceh_length; ld t1, 0(t0)\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lceh_fail\n" ++
  "  la t0, ceh_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  # Copy 20 bytes: 8 + 8 + 4 = 20.\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  lwu t4, 16(t3); sw t4, 16(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lceh_ret\n" ++
  ".Lceh_fail:\n" ++
  "  sd zero,  0(s2); sd zero, 8(s2); sw zero, 16(s2)\n" ++
  "  li a0, 1\n" ++
  ".Lceh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_coinbase_extract_from_header`: probe BuildUnit. Reads
    (header_len, header_bytes) from host input, writes
    (status, 20B address + 4B pad) to OUTPUT (32 bytes total). -/
def ziskCoinbaseExtractFromHeaderPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # 20B output at OUTPUT + 8\n" ++
  "  # Pre-zero the 20B output + 4B trailing pad.\n" ++
  "  mv t0, a2\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sw zero, 16(t0)\n" ++
  "  jal ra, coinbase_extract_from_header\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lceh_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  coinbaseExtractFromHeaderFunction ++ "\n" ++
  ".Lceh_pdone:"

def ziskCoinbaseExtractFromHeaderDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ceh_offset:\n" ++
  "  .zero 8\n" ++
  "ceh_length:\n" ++
  "  .zero 8"

def ziskCoinbaseExtractFromHeaderProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCoinbaseExtractFromHeaderPrologue
  dataAsm     := ziskCoinbaseExtractFromHeaderDataSection
}


end EvmAsm.Codegen
