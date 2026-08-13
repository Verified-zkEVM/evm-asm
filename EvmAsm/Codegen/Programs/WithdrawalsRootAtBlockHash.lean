/-
  EvmAsm.Codegen.Programs.WithdrawalsRootAtBlockHash

  Hash-keyed `header.withdrawals_root` extractor
  (RLP field 16, 32 bytes; Shanghai+). Mirror of the
  number-keyed `withdrawals_root_at_block_number` probe but
  takes a block_hash key.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## withdrawals_root_at_block_hash

    Hash-keyed extractor for `header.block.withdrawals_root`
    (RLP field 16, 32 B; Shanghai+).

    Pipeline (composes K19 + existing
    header_extract_withdrawals_root; no new helpers):
      witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
      h -> header_extract_withdrawals_root -> 32 B

    Use cases:
      * Bridge-driven withdrawals-trie attestation -- caller
        has a known block_hash + an off-chain withdrawals_root
        claim; verify without first finding the number.
      * Cross-witness consistency.
      * Reorg detection at the withdrawals_root level.

    Calling convention (4 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : 32-byte withdrawals_root out ptr
      ra (input)  : return

      a0 (output) :
        0 = success
        1 = block_hash not in witness.headers
        2 = matched header withdrawals_root extraction failed
            (RLP malformed / field 16 absent / size != 32)
-/
def withdrawalsRootAtBlockHashFunction : String :=
  "withdrawals_root_at_block_hash:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # withdrawals_root out (32 B)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, wrbh_match_offset\n" ++
  "  la a4, wrbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lwrbh_no_match\n" ++
  "  la t0, wrbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s4, s1, t1\n" ++
  "  la t0, wrbh_match_length\n" ++
  "  ld s5, 0(t0)\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_withdrawals_root\n" ++
  "  beqz a0, .Lwrbh_ret\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li a0, 2\n" ++
  "  j .Lwrbh_ret\n" ++
  ".Lwrbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lwrbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_withdrawals_root_at_block_hash`: probe BuildUnit. -/
def ziskWithdrawalsRootAtBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  addi a0, t4, 16             # block_hash ptr\n" ++
  "  addi a1, t4, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # 32 B withdrawals_root out\n" ++
  "  jal ra, withdrawals_root_at_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwrbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractWithdrawalsRootFunction ++ "\n" ++
  withdrawalsRootAtBlockHashFunction ++ "\n" ++
  ".Lwrbh_pdone:"

def ziskWithdrawalsRootAtBlockHashDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "hewr_offset:\n" ++
  "  .zero 8\n" ++
  "hewr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wrbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "wrbh_match_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
