/-
  EvmAsm.Codegen.Programs.GasPairAtBlockHash

  Hash-keyed `(gas_used, gas_limit)` pair extractor (RLP
  fields 10 & 9, both u64). Composite that halves the
  keccak cost vs. calling the two singletons.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.BlockHashPredicates
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## gas_pair_at_block_hash

    Hash-keyed extractor for the `(gas_used, gas_limit)`
    pair (RLP fields 10 & 9; both u64).

    Pipeline (composes K19 + existing
    header_extract_gas_used + header_extract_gas_limit;
    no new asm helpers):
      witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
      h -> header_extract_gas_used  -> u64 (field 10)
      h -> header_extract_gas_limit -> u64 (field 9)

    Why a composite over two singletons:
      Gas-utilisation / EIP-1559 base-fee tuning oracles
      always want `(gas_used, gas_limit)` together (the
      ratio drives next-block base fee). The two
      hash-keyed singletons would pay two keccak256s over
      the matched header; this pair shares the walk.

      Spec invariant `gas_used <= gas_limit` (EIP-1559) is
      not checked here -- callers do that with the
      returned pair; this primitive just surfaces the raw
      values.

    Calling convention (4 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : 16-byte pair out ptr
                    out[0..8]  = gas_used  (u64 LE)
                    out[8..16] = gas_limit (u64 LE)
      ra (input)  : return

      a0 (output) :
        0 = success
        1 = block_hash not in witness.headers
        2 = gas_used (field 10) extraction failed
        3 = gas_limit (field 9) extraction failed
-/
def gasPairAtBlockHashFunction : String :=
  "gas_pair_at_block_hash:\n" ++
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
  "  la a3, gpbh_match_offset\n" ++
  "  la a4, gpbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lgpbh_no_match\n" ++
  "  la t0, gpbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s4, s1, t1\n" ++
  "  la t0, gpbh_match_length\n" ++
  "  ld s5, 0(t0)\n" ++
  "  # Extract field 10 (gas_used) -> out[0..8]\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_gas_used\n" ++
  "  beqz a0, .Lgpbh_gl\n" ++
  "  sd zero, 0(s3); sd zero, 8(s3)\n" ++
  "  li a0, 2\n" ++
  "  j .Lgpbh_ret\n" ++
  ".Lgpbh_gl:\n" ++
  "  # Extract field 9 (gas_limit) -> out[8..16]\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  addi a2, s3, 8\n" ++
  "  jal ra, header_extract_gas_limit\n" ++
  "  beqz a0, .Lgpbh_done\n" ++
  "  sd zero, 0(s3); sd zero, 8(s3)\n" ++
  "  li a0, 3\n" ++
  "  j .Lgpbh_ret\n" ++
  ".Lgpbh_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lgpbh_ret\n" ++
  ".Lgpbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lgpbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_gas_pair_at_block_hash`: probe BuildUnit.
    Output layout (24 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..16 : gas_used  u64 LE (0 on failure)
      bytes 16..24 : gas_limit u64 LE (0 on failure) -/
def ziskGasPairAtBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  addi a0, t4, 16             # block_hash ptr\n" ++
  "  addi a1, t4, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # 16 B pair out\n" ++
  "  jal ra, gas_pair_at_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lgpbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractGasUsedFunction ++ "\n" ++
  headerExtractGasLimitFunction ++ "\n" ++
  gasPairAtBlockHashFunction ++ "\n" ++
  ".Lgpbh_pdone:"

def ziskGasPairAtBlockHashDataSection : String :=
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
  "gpbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "gpbh_match_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
