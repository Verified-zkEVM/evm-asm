/-
  EvmAsm.Codegen.Programs.BlobGasPairAtBlockHash

  Hash-keyed `(blob_gas_used, excess_blob_gas)` extractor
  (RLP fields 17 & 18, both u64; Cancun+). Composite that
  saves one keccak vs calling
  `blob_gas_used_at_block_hash` and
  `excess_blob_gas_at_block_hash` separately.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## blob_gas_pair_at_block_hash

    Hash-keyed extractor for the
    `(blob_gas_used, excess_blob_gas)` pair (RLP fields 17
    and 18, Cancun+).

    Pipeline (composes K19 + existing K90; no new helpers):
      witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
      h -> header_extract_blob_gas_pair -> (u64, u64)     [K90]

    Why a composite: the per-field hash-keyed mirrors
    (`blob_gas_used_at_block_hash`,
    `excess_blob_gas_at_block_hash`) each pay a full keccak
    over the matched header. EIP-4844 fee math
    `get_blob_gasprice(excess_blob_gas)` always wants the
    pair together; this combined wrapper halves the keccak
    cost.

    Calling convention (4 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : 16-byte pair out ptr
                    out[0..8]  = blob_gas_used   (u64 LE)
                    out[8..16] = excess_blob_gas (u64 LE)
      ra (input)  : return

      a0 (output) :
        0 = success
        1 = block_hash not in witness.headers
        2 = matched header blob_gas_used (field 17) extraction failed
        3 = matched header excess_blob_gas (field 18) extraction failed
-/
def blobGasPairAtBlockHashFunction : String :=
  "blob_gas_pair_at_block_hash:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # 16 B pair out\n" ++
  "  sd zero, 0(s3); sd zero, 8(s3)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, bgpbh_match_offset\n" ++
  "  la a4, bgpbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lbgpbh_no_match\n" ++
  "  la t0, bgpbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s4, s1, t1\n" ++
  "  la t0, bgpbh_match_length\n" ++
  "  ld s5, 0(t0)\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_blob_gas_pair\n" ++
  "  beqz a0, .Lbgpbh_ret\n" ++
  "  # K90 returns 1 = blob_gas_used fail, 2 = excess_blob_gas fail.\n" ++
  "  # We bump by +1 so callers can distinguish hash-miss (1) from\n" ++
  "  # the two field-specific RLP failures (2 / 3).\n" ++
  "  sd zero, 0(s3); sd zero, 8(s3)\n" ++
  "  addi a0, a0, 1\n" ++
  "  j .Lbgpbh_ret\n" ++
  ".Lbgpbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lbgpbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_blob_gas_pair_at_block_hash`: probe BuildUnit.
    Output layout (24 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..16 : blob_gas_used   u64 LE (0 on failure)
      bytes 16..24 : excess_blob_gas u64 LE (0 on failure) -/
def ziskBlobGasPairAtBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  addi a0, t4, 16             # block_hash ptr\n" ++
  "  addi a1, t4, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # 16 B pair out\n" ++
  "  jal ra, blob_gas_pair_at_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbgpbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  headerExtractBlobGasPairFunction ++ "\n" ++
  blobGasPairAtBlockHashFunction ++ "\n" ++
  ".Lbgpbh_pdone:"

def ziskBlobGasPairAtBlockHashDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bgpbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "bgpbh_match_length:\n" ++
  "  .zero 8"

def ziskBlobGasPairAtBlockHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlobGasPairAtBlockHashPrologue
  dataAsm     := ziskBlobGasPairAtBlockHashDataSection
}

end EvmAsm.Codegen
