/-
  EvmAsm.Codegen.Programs.BlockHeaderSszToRlp

  block_header_ssz_to_rlp (bead evm-asm-fhsxz.2.4.1): re-encode an Amsterdam
  block header from its SSZ ExecutionPayload (plus four roots not carried in
  the payload) into the canonical RLP the consensus block hash is taken over.
  This is the prerequisite for the Step-2 verdict: validate_header_rlp_pair
  needs the current block's header as RLP, and the block-hash linkage is
  keccak256(rlp(header)).

  The 23 Amsterdam header fields (execution-specs amsterdam/blocks.py), in RLP
  order, with their source:
    parent_hash, ommers_hash(=EMPTY_OMMER_HASH const), coinbase, state_root,
    transactions_root(INPUT), receipt_root, bloom, difficulty(=0),
    number, gas_limit, gas_used, timestamp, extra_data, prev_randao,
    nonce(=0 Bytes8), base_fee_per_gas, withdrawals_root(INPUT),
    blob_gas_used, excess_blob_gas, parent_beacon_block_root(INPUT),
    requests_hash(INPUT), block_access_list_hash(INPUT), slot_number.
  transactions_root / withdrawals_root / parent_beacon_block_root /
  requests_hash / block_access_list_hash are NOT in the fixed SSZ payload (the
  payload carries the lists/bytes; commitments are computed separately) ->
  passed in by the caller.

  No-misaligned invariant: the payload's u64 fields sit at byte offsets ≡4 mod
  8, so a plain `ld` would trap on verified RV64. We read every integer field
  byte-wise (LE) and reverse to big-endian via `bhr_rev_le_be`, then
  rlp_encode_uint_be (which strips leading zeros to the minimal RLP form);
  byte-string fields go through rlp_encode_bytes (byte-wise). All scratch
  stores are u64/aligned.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead

-- (HashBridge provides zkvm_keccak256, used by the probe to hash the
-- re-encoded header into the block hash, since the 627-byte RLP exceeds
-- ziskemu's 256-byte OUTPUT capture.)

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bhr_rev_le_be -- reverse `len` little-endian bytes into big-endian.
    a0 = src ptr, a1 = len, a2 = dst ptr. Leaf (LBU/SB only). -/
def bhrRevLeBe_prog : Program :=
  [ .ADD .x5 .x10 .x11,
    .MV .x6 .x12,
    .MV .x7 .x11,
    .BEQ .x7 .x0 (28 : BitVec 13),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bhrRevLeBeFunction : String :=
  "bhr_rev_le_be:\n" ++ emitProgram bhrRevLeBe_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bhrRevLeBe_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bhrRevLeBeFunction_eq_prog :
    bhrRevLeBeFunction = "bhr_rev_le_be:\n" ++ emitProgram bhrRevLeBe_prog := rfl

#guard bhrRevLeBeFunction.startsWith "bhr_rev_le_be:\n"
#guard bhrRevLeBe_prog.length = 11
/-- `block_header_ssz_to_rlp`.
    a0 = SSZ ExecutionPayload ptr     a1 = transactions_root ptr (32B)
    a2 = withdrawals_root ptr (32B)   a3 = parent_beacon_block_root ptr (32B)
    a4 = requests_hash ptr (32B)      a5 = out RLP buffer ptr
    a6 = u64 out length ptr           a7 = block_access_list_hash ptr (32B)
    a0 (output) = 0. -/
def blockHeaderSszToRlpFunction : String :=
  "block_header_ssz_to_rlp:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                   # payload\n" ++
  "  mv s1, a1                   # transactions_root\n" ++
  "  mv s2, a2                   # withdrawals_root\n" ++
  "  mv s3, a3                   # parent_beacon_block_root\n" ++
  "  mv s4, a4                   # requests_hash\n" ++
  "  mv s5, a5                   # out\n" ++
  "  mv s6, a6                   # out_len\n" ++
  "  mv s8, a7                   # block_access_list_hash\n" ++
  "  li s7, 0                    # payload cursor\n" ++
  -- byte-string field helper: encodes (a0=src, a1=len) at bhr_payload+s7.
  -- field 1: parent_hash (payload@0, 32)
  "  addi a0, s0, 0; li a1, 32\n" ++
  "  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1\n" ++
  -- field 2: ommers_hash (EMPTY_OMMER_HASH const, 32)
  "  la a0, bhr_empty_ommers; li a1, 32\n" ++
  "  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1\n" ++
  -- field 3: coinbase (payload@32, 20)
  "  addi a0, s0, 32; li a1, 20\n" ++
  "  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1\n" ++
  -- field 4: state_root (payload@52, 32)
  "  addi a0, s0, 52; li a1, 32\n" ++
  "  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1\n" ++
  -- field 5: transactions_root (INPUT s1, 32)
  "  mv a0, s1; li a1, 32\n" ++
  "  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1\n" ++
  -- field 6: receipt_root (payload@84, 32)
  "  addi a0, s0, 84; li a1, 32\n" ++
  "  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1\n" ++
  -- field 7: bloom (payload@116, 256)
  "  addi a0, s0, 116; li a1, 256\n" ++
  "  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1\n" ++
  -- field 8: difficulty = 0  (uint of zero bytes -> 0x80)
  "  la a0, bhr_zero8; li a1, 8; la a2, bhr_payload; add a2, a2, s7\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  add s7, s7, a0\n" ++
  -- uint field helper: reverse 8 LE bytes at payload@OFF then rlp_encode_uint_be.
  -- field 9: number (payload@404, u64)
  "  addi a0, s0, 404; li a1, 8; la a2, bhr_uint_be\n" ++
  "  jal ra, bhr_rev_le_be\n" ++
  "  la a0, bhr_uint_be; li a1, 8; la a2, bhr_payload; add a2, a2, s7\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  add s7, s7, a0\n" ++
  -- field 10: gas_limit (payload@412)
  "  addi a0, s0, 412; li a1, 8; la a2, bhr_uint_be\n" ++
  "  jal ra, bhr_rev_le_be\n" ++
  "  la a0, bhr_uint_be; li a1, 8; la a2, bhr_payload; add a2, a2, s7\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  add s7, s7, a0\n" ++
  -- field 11: gas_used (payload@420)
  "  addi a0, s0, 420; li a1, 8; la a2, bhr_uint_be\n" ++
  "  jal ra, bhr_rev_le_be\n" ++
  "  la a0, bhr_uint_be; li a1, 8; la a2, bhr_payload; add a2, a2, s7\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  add s7, s7, a0\n" ++
  -- field 12: timestamp (payload@428)
  "  addi a0, s0, 428; li a1, 8; la a2, bhr_uint_be\n" ++
  "  jal ra, bhr_rev_le_be\n" ++
  "  la a0, bhr_uint_be; li a1, 8; la a2, bhr_payload; add a2, a2, s7\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  add s7, s7, a0\n" ++
  -- field 13: extra_data (payload@[extra_off .. tx_off])
  "  lbu t0, 436(s0); lbu t1, 437(s0); slli t1, t1, 8; or t0, t0, t1\n" ++
  "  lbu t1, 438(s0); slli t1, t1, 16; or t0, t0, t1\n" ++
  "  lbu t1, 439(s0); slli t1, t1, 24; or t0, t0, t1   # extra_off\n" ++
  "  lbu t2, 504(s0); lbu t1, 505(s0); slli t1, t1, 8; or t2, t2, t1\n" ++
  "  lbu t1, 506(s0); slli t1, t1, 16; or t2, t2, t1\n" ++
  "  lbu t1, 507(s0); slli t1, t1, 24; or t2, t2, t1   # tx_off\n" ++
  "  sub a1, t2, t0              # extra_len\n" ++
  "  add a0, s0, t0              # extra_ptr\n" ++
  "  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1\n" ++
  -- field 14: prev_randao (payload@372, 32)
  "  addi a0, s0, 372; li a1, 32\n" ++
  "  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1\n" ++
  -- field 15: nonce = Bytes8 zero (rlp_encode_bytes -> 0x88 00..00)
  "  la a0, bhr_zero8; li a1, 8\n" ++
  "  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1\n" ++
  -- field 16: base_fee_per_gas (payload@440, u256 LE -> minimal BE)
  "  addi a0, s0, 440; li a1, 32; la a2, bhr_uint_be\n" ++
  "  jal ra, bhr_rev_le_be\n" ++
  "  la a0, bhr_uint_be; li a1, 32; la a2, bhr_payload; add a2, a2, s7\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  add s7, s7, a0\n" ++
  -- field 17: withdrawals_root (INPUT s2, 32)
  "  mv a0, s2; li a1, 32\n" ++
  "  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1\n" ++
  -- field 18: blob_gas_used (payload@512)
  "  addi a0, s0, 512; li a1, 8; la a2, bhr_uint_be\n" ++
  "  jal ra, bhr_rev_le_be\n" ++
  "  la a0, bhr_uint_be; li a1, 8; la a2, bhr_payload; add a2, a2, s7\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  add s7, s7, a0\n" ++
  -- field 19: excess_blob_gas (payload@520)
  "  addi a0, s0, 520; li a1, 8; la a2, bhr_uint_be\n" ++
  "  jal ra, bhr_rev_le_be\n" ++
  "  la a0, bhr_uint_be; li a1, 8; la a2, bhr_payload; add a2, a2, s7\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  add s7, s7, a0\n" ++
  -- field 20: parent_beacon_block_root (INPUT s3, 32)
  "  mv a0, s3; li a1, 32\n" ++
  "  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1\n" ++
  -- field 21: requests_hash (INPUT s4, 32)
  "  mv a0, s4; li a1, 32\n" ++
  "  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1\n" ++
  -- field 22: block_access_list_hash (INPUT s8, 32)
  "  mv a0, s8; li a1, 32\n" ++
  "  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1\n" ++
  -- field 23: slot_number (payload@532)
  "  addi a0, s0, 532; li a1, 8; la a2, bhr_uint_be\n" ++
  "  jal ra, bhr_rev_le_be\n" ++
  "  la a0, bhr_uint_be; li a1, 8; la a2, bhr_payload; add a2, a2, s7\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  add s7, s7, a0\n" ++
  -- list prefix into out, then copy payload after it.
  "  mv a0, s7; mv a1, s5; la a2, bhr_prefix_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, bhr_prefix_len; ld t1, 0(t0)\n" ++
  "  add t2, s5, t1              # dst = out + prefix_len\n" ++
  "  la t3, bhr_payload          # src\n" ++
  "  mv t4, s7                   # remaining\n" ++
  ".Lbhr_cp:\n" ++
  "  beqz t4, .Lbhr_cpd\n" ++
  "  lbu t5, 0(t3); sb t5, 0(t2)\n" ++
  "  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1\n" ++
  "  j .Lbhr_cp\n" ++
  ".Lbhr_cpd:\n" ++
  "  add t1, t1, s7              # out_len = prefix_len + payload_len\n" ++
  "  sd t1, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_block_header_ssz_to_rlp`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8   payload_len (u64, informational)
      +16  transactions_root (32B)
      +48  withdrawals_root (32B)
      +80  parent_beacon_block_root (32B)
      +112 requests_hash (32B)
      +144 block_access_list_hash (32B)
      +176 SSZ ExecutionPayload bytes
    Output: OUTPUT+0 = header RLP length (u64); OUTPUT+8 = block hash
    (keccak256 of the re-encoded header RLP, 32 B). The RLP itself is built in
    `bhr_result` scratch (the 627-byte RLP exceeds the 256-byte OUTPUT). -/
def ziskBlockHeaderSszToRlpPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a1, t0, 16             # transactions_root\n" ++
  "  addi a2, t0, 48             # withdrawals_root\n" ++
  "  addi a3, t0, 80             # parent_beacon_block_root\n" ++
  "  addi a4, t0, 112            # requests_hash\n" ++
  "  addi a7, t0, 144            # block_access_list_hash\n" ++
  "  addi a0, t0, 176            # SSZ ExecutionPayload\n" ++
  "  la a5, bhr_result           # header RLP buffer\n" ++
  "  la a6, bhr_result_len\n" ++
  "  jal ra, block_header_ssz_to_rlp\n" ++
  "  # block hash = keccak256(header RLP) -> OUTPUT+8; rlp_len -> OUTPUT+0.\n" ++
  "  la t0, bhr_result_len; ld a1, 0(t0)\n" ++
  "  la a0, bhr_result\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la t0, bhr_result_len; ld t1, 0(t0); li t2, 0xa0010000; sd t1, 0(t2)\n" ++
  "  j .Lbhr_pdone\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  bhrRevLeBeFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHeaderSszToRlpFunction ++ "\n" ++
  ".Lbhr_pdone:"

def ziskBlockHeaderSszToRlpDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "bhr_empty_ommers:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47\n" ++
  ".balign 8\n" ++
  "bhr_zero8:\n  .zero 8\n" ++
  "bhr_flen:\n  .zero 8\n" ++
  "bhr_prefix_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bhr_uint_be:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  "bhr_result_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "bhr_payload:\n  .zero 1024\n" ++
  ".balign 8\n" ++
  "bhr_result:\n  .zero 1024"

def ziskBlockHeaderSszToRlpProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockHeaderSszToRlpPrologue
  dataAsm     := ziskBlockHeaderSszToRlpDataSection
}

end EvmAsm.Codegen
