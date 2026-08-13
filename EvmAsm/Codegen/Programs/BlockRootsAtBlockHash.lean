/-
  EvmAsm.Codegen.Programs.BlockRootsAtBlockHash

  Hash-keyed body-MPT roots extractor:
  `(transactions_root, receipts_root, withdrawals_root)`
  (RLP fields 4, 5, 16; 32 bytes each).  Composite that
  saves two keccaks vs calling the three singletons
  separately.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.Header

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_roots_at_block_hash

    Hash-keyed extractor for the body-MPT roots triple
    `(transactions_root, receipts_root, withdrawals_root)`
    (RLP fields 4, 5, 16; 32 bytes each; withdrawals_root
    is Shanghai+).

    Pipeline (composes K19 + existing K95
    `header_extract_block_roots`; no new asm helpers):
      witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
      h -> header_extract_block_roots
         -> 96-byte triple

    Why a composite over three singletons: `validate_block_body`
    cross-checks ALL three roots in one pass against the body
    payload. Calling
    `transactions_root_at_block_hash` +
    `receipts_root_at_block_hash` +
    `withdrawals_root_at_block_hash` separately pays three
    keccak256s over the matched header. This composite shares
    that walk -- one keccak per `validate_block_body` call.

    Calling convention (4 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : 96-byte roots-triple out ptr
                    out[ 0..32]  = transactions_root
                    out[32..64]  = receipts_root
                    out[64..96]  = withdrawals_root (Shanghai+)
      ra (input)  : return

      a0 (output) :
        0 = success
        1 = block_hash not in witness.headers
        2 = transactions_root (field 4) missing / not 32 B
        3 = receipts_root (field 5) missing / not 32 B
        4 = withdrawals_root (field 16) missing / not 32 B
            (pre-Shanghai header)
-/
def blockRootsAtBlockHashFunction : String :=
  "block_roots_at_block_hash:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # 96 B triple out\n" ++
  "  # Zero the output (12 × u64).\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  sd zero, 32(s3); sd zero, 40(s3); sd zero, 48(s3); sd zero, 56(s3)\n" ++
  "  sd zero, 64(s3); sd zero, 72(s3); sd zero, 80(s3); sd zero, 88(s3)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, brbh_match_offset\n" ++
  "  la a4, brbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lbrbh_no_match\n" ++
  "  la t0, brbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s4, s1, t1\n" ++
  "  la t0, brbh_match_length\n" ++
  "  ld s5, 0(t0)\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_block_roots\n" ++
  "  beqz a0, .Lbrbh_ret\n" ++
  "  # K95 status:\n" ++
  "  #   1 transactions_root fail -> remap to 2\n" ++
  "  #   2 receipts_root fail     -> remap to 3\n" ++
  "  #   3 withdrawals_root fail  -> remap to 4\n" ++
  "  addi a0, a0, 1\n" ++
  "  j .Lbrbh_ret\n" ++
  ".Lbrbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lbrbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_block_roots_at_block_hash`: probe BuildUnit.
    Output layout (104 bytes):
      bytes   0.. 8 : status (0..4)
      bytes   8..40 : transactions_root (32 B)
      bytes  40..72 : receipts_root     (32 B)
      bytes  72..104: withdrawals_root  (32 B) -/
def ziskBlockRootsAtBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  addi a0, t4, 16             # block_hash ptr\n" ++
  "  addi a1, t4, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # 96 B triple out\n" ++
  "  jal ra, block_roots_at_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbrbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractBlockRootsFunction ++ "\n" ++
  blockRootsAtBlockHashFunction ++ "\n" ++
  ".Lbrbh_pdone:"

def ziskBlockRootsAtBlockHashDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "hebr_offset:\n" ++
  "  .zero 8\n" ++
  "hebr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "brbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "brbh_match_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
