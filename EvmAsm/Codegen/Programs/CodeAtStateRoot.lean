/-
  EvmAsm.Codegen.Programs.CodeAtStateRoot

  Trusted-state_root historical bytecode extractor. Given
  a state_root + address, walks K28 to find the account's
  code_hash, then code-specific K19 over witness.codes to retrieve the
  bytecode location.

  Direct-state_root version of #7333 (block-hash-keyed).

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.State
import EvmAsm.Codegen.Programs.WitnessCodeLookup

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## code_at_state_root_address

    Pipeline:
      state_root + address -> account.code_hash         [K28]
      code_hash + witness.codes -> (offset, length)     [code-specific K19]

    Returns the location of the bytecode within
    witness.codes so the caller can slice it.

    Distinct from #7333 (block_hash-keyed):
      * #7333: K19 over witness.headers first, then K201,
        then K28 + code-specific K19 over witness.codes.
      * THIS: skips the chain walk -- assumes caller
        already has a trusted state_root.

    Use cases:
      * Bridge / oracle scenario: caller has trusted
        state_root from snapshot, wants bytecode at an
        address.
      * Chained extraction: after #7364
        (state_root_chain_walk_back_n_steps), use the
        returned state_root to look up bytecode without
        re-walking the chain.

    Status codes:
      0 = success (offset, length valid)
      1 = account absent in state trie
      2 = EMPTY_CODE_HASH (EOA / no code); (offset, length)
          = (0, 0); witness.codes doesn't contain the empty
          string, so the K19 miss is expected and gets a
          distinct code
      3 = state-trie mpt parse error
      4 = account RLP decode failure
      5 = code_hash NOT in witness.codes (witness invalid)

    Argument squeeze: 7 register args + 1 scratch label
    set by the prologue (casr_code_offset_out_ptr).

    Calling convention:
      a0 (input)  : state_root ptr (32 bytes)
      a1 (input)  : address ptr (20 bytes)
      a2 (input)  : witness.state ptr
      a3 (input)  : witness.state len
      a4 (input)  : witness.codes ptr
      a5 (input)  : witness.codes len
      a6 (input)  : u64 length out ptr
      casr_code_offset_out_ptr : u64* scratch
-/
def codeAtStateRootAddressFunction : String :=
  "code_at_state_root_address:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # state_root ptr\n" ++
  "  mv s1, a1                  # address ptr\n" ++
  "  mv s2, a2                  # witness.state ptr\n" ++
  "  mv s3, a3                  # witness.state len\n" ++
  "  mv s4, a4                  # witness.codes ptr\n" ++
  "  mv s5, a5                  # witness.codes len\n" ++
  "  mv s6, a6                  # length out ptr\n" ++
  "  la t6, casr_code_offset_out_ptr\n" ++
  "  ld s7, 0(t6)\n" ++
  "  sd zero, 0(s6)\n" ++
  "  sd zero, 0(s7)\n" ++
  "  # Step 1: account_at_address.\n" ++
  "  mv a0, s1                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  mv a2, s0                  # state_root\n" ++
  "  mv a3, s2                  # witness.state ptr\n" ++
  "  mv a4, s3                  # witness.state len\n" ++
  "  la a5, casr_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lcasr_check_empty\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lcasr_absent\n" ++
  "  # K28: 2 -> 3, 3 -> 4.\n" ++
  "  addi a0, a0, 1\n" ++
  "  j .Lcasr_ret\n" ++
  ".Lcasr_absent:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcasr_ret\n" ++
  ".Lcasr_check_empty:\n" ++
  "  # Check code_hash == EMPTY_CODE_HASH.\n" ++
  "  la t0, casr_walked_struct\n" ++
  "  addi t0, t0, 72\n" ++
  "  la t1, casr_empty_code_hash\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lcasr_lookup\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lcasr_lookup\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lcasr_lookup\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lcasr_lookup\n" ++
  "  li a0, 2                   # EMPTY_CODE_HASH\n" ++
  "  j .Lcasr_ret\n" ++
  ".Lcasr_lookup:\n" ++
  "  # Code-specific K19 over witness.codes with code_hash.\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  la t0, casr_walked_struct\n" ++
  "  addi a2, t0, 72            # target_hash\n" ++
  "  mv a3, s7                  # offset out\n" ++
  "  mv a4, s6                  # length out\n" ++
  "  jal ra, witness_codes_lookup_by_hash\n" ++
  "  beqz a0, .Lcasr_done\n" ++
  "  li a0, 5\n" ++
  "  j .Lcasr_ret\n" ++
  ".Lcasr_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcasr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_code_at_state_root_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_state_len (u64 LE)
      bytes 16..24 : witness_codes_len (u64 LE)
      bytes 24..56 : state_root (32 bytes)
      bytes 56..76 : address (20 bytes)
      bytes 76..   : witness.state ++ witness.codes
    Output layout (24 bytes):
      bytes  0.. 8 : status (0..5)
      bytes  8..16 : code_offset (u64)
      bytes 16..24 : code_length (u64) -/
def ziskCodeAtStateRootAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  ld s1, 8(s0)                # witness_state_len\n" ++
  "  ld s2, 16(s0)               # witness_codes_len\n" ++
  "  addi s3, s0, 76             # witness.state ptr\n" ++
  "  add s4, s3, s1              # witness.codes ptr\n" ++
  "  mv a0, s4; mv a1, s2; jal ra, witness_codes_index_build\n" ++
  "  addi a0, s0, 24             # state_root ptr\n" ++
  "  addi a1, s0, 56             # address ptr\n" ++
  "  mv a2, s3                   # witness.state ptr\n" ++
  "  mv a3, s1                   # witness.state len\n" ++
  "  mv a4, s4                   # witness.codes ptr\n" ++
  "  mv a5, s2                   # witness.codes len\n" ++
  "  li a6, 0xa0010010           # length out (OUTPUT + 16)\n" ++
  "  la t0, casr_code_offset_out_ptr\n" ++
  "  li t1, 0xa0010008\n" ++
  "  sd t1, 0(t0)\n" ++
  "  jal ra, code_at_state_root_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcasr_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  witnessCodesLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  codeAtStateRootAddressFunction ++ "\n" ++
  ".Lcasr_pdone:"

def ziskCodeAtStateRootAddressDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  "wclh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aa_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 32\n" ++
  "casr_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "casr_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70\n" ++
  ".balign 8\n" ++
  "casr_code_offset_out_ptr:\n" ++
  "  .zero 8"

def ziskCodeAtStateRootAddressProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCodeAtStateRootAddressPrologue
  dataAsm     := ziskCodeAtStateRootAddressDataSection
}

end EvmAsm.Codegen
