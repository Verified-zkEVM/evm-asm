/-
  EvmAsm.Codegen.Programs.WithdrawalsRootIndexed

  Standalone block-level withdrawals_root validator backed by the generic
  indexed trie builder. This extends the old fixed one- and two-withdrawal
  probes to arbitrary indexed withdrawal lists supported by
  mpt_indexed_trie_root_small.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.MptIndexedTrieRoot

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_validate_withdrawals_root_indexed

    Validate `header.withdrawals_root` against the MPT root of an indexed list
    of already-RLP-encoded withdrawals. Keys are `rlp(0)..rlp(N-1)` and root
    computation is delegated to `mpt_indexed_trie_root_small`, currently
    supporting `N <= 128`.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : withdrawal value descriptor array ptr, entries `{ptr:u64, len:u64}`
      a3 (input)  : number of withdrawals
      ra (input)  : return
      a0 (output) : status
        0 : success -- predicate returned in a1
        1 : header RLP parse failure / field 16 missing
        2 : header.withdrawals_root length != 32
        3 : indexed trie builder failure
      a1 (output) : 1 iff the extracted root equals the computed root -/
def blockValidateWithdrawalsRootIndexed_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.bvwri_expected_root (GuestAddrs.block_validate_withdrawals_root_indexed + 48)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bvwri_expected_root (GuestAddrs.block_validate_withdrawals_root_indexed + 48)),
    .JAL .x1 (jalOff GuestAddrs.header_extract_withdrawals_root (GuestAddrs.block_validate_withdrawals_root_indexed + 56)),
    .BNE .x10 .x0 (116 : BitVec 13),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .AUIPC .x12 (laHi GuestAddrs.bvwri_computed_root (GuestAddrs.block_validate_withdrawals_root_indexed + 72)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bvwri_computed_root (GuestAddrs.block_validate_withdrawals_root_indexed + 72)),
    .JAL .x1 (jalOff GuestAddrs.mpt_indexed_trie_root_bounded_from_values (GuestAddrs.block_validate_withdrawals_root_indexed + 80)),
    .BNE .x10 .x0 (100 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.bvwri_expected_root (GuestAddrs.block_validate_withdrawals_root_indexed + 88)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvwri_expected_root (GuestAddrs.block_validate_withdrawals_root_indexed + 88)),
    .AUIPC .x6 (laHi GuestAddrs.bvwri_computed_root (GuestAddrs.block_validate_withdrawals_root_indexed + 96)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvwri_computed_root (GuestAddrs.block_validate_withdrawals_root_indexed + 96)),
    .LD .x7 .x5 (0 : BitVec 12),
    .LD .x28 .x6 (0 : BitVec 12),
    .BNE .x7 .x28 (52 : BitVec 13),
    .LD .x7 .x5 (8 : BitVec 12),
    .LD .x28 .x6 (8 : BitVec 12),
    .BNE .x7 .x28 (40 : BitVec 13),
    .LD .x7 .x5 (16 : BitVec 12),
    .LD .x28 .x6 (16 : BitVec 12),
    .BNE .x7 .x28 (28 : BitVec 13),
    .LD .x7 .x5 (24 : BitVec 12),
    .LD .x28 .x6 (24 : BitVec 12),
    .BNE .x7 .x28 (16 : BitVec 13),
    .LI .x10 (0 : Word),
    .LI .x11 (1 : Word),
    .JAL .x0 (32 : BitVec 21),
    .LI .x10 (0 : Word),
    .LI .x11 (0 : Word),
    .JAL .x0 (20 : BitVec 21),
    .LI .x11 (0 : Word),
    .JAL .x0 (12 : BitVec 21),
    .LI .x10 (3 : Word),
    .LI .x11 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blockValidateWithdrawalsRootIndexed_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blockValidateWithdrawalsRootIndexed_relocs : RelocTable :=
  [ (12, .la .x12 "bvwri_expected_root"),
    (14, .jal .x1 "header_extract_withdrawals_root"),
    (18, .la .x12 "bvwri_computed_root"),
    (20, .jal .x1 "mpt_indexed_trie_root_bounded_from_values"),
    (22, .la .x5 "bvwri_expected_root"),
    (24, .la .x6 "bvwri_computed_root") ]

def blockValidateWithdrawalsRootIndexedFunction : String :=
  "block_validate_withdrawals_root_indexed:\n" ++ emitProgramR blockValidateWithdrawalsRootIndexed_prog blockValidateWithdrawalsRootIndexed_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blockValidateWithdrawalsRootIndexed_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blockValidateWithdrawalsRootIndexedFunction_eq_prog :
    blockValidateWithdrawalsRootIndexedFunction = "block_validate_withdrawals_root_indexed:\n" ++ emitProgramR blockValidateWithdrawalsRootIndexed_prog blockValidateWithdrawalsRootIndexed_relocs := rfl

#guard blockValidateWithdrawalsRootIndexedFunction.startsWith "block_validate_withdrawals_root_indexed:\n"
/-- `zisk_block_validate_withdrawals_root_indexed`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..16 : number of withdrawals
      bytes 16..   : withdrawal_rlp_len table (u64 each)
                      header_rlp
                      withdrawal_rlp blobs, each 8-byte aligned
    Output layout:
      bytes  0.. 8 : status (0..3)
      bytes  8..16 : is_valid -/
def ziskBlockValidateWithdrawalsRootIndexedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  ld s1, 8(s0)                # header_rlp_len\n" ++
  "  ld s2, 16(s0)               # n withdrawals\n" ++
  "  addi s3, s0, 24             # length table\n" ++
  "  slli t0, s2, 3; add s4, s3, t0   # header_rlp ptr\n" ++
  "  add s5, s4, s1              # withdrawal blob cursor\n" ++
  "  addi s5, s5, 7; andi s5, s5, -8\n" ++
  "  la s6, bvwri_value_descs\n" ++
  "  li s7, " ++ toString (itrIndexedEntryCapacity + 1) ++ "\n" ++
  "  bgeu s2, s7, .Lbvwri_pdesc_done\n" ++
  "  li s8, 0                    # i\n" ++
  ".Lbvwri_pdesc_loop:\n" ++
  "  beq s8, s2, .Lbvwri_pdesc_done\n" ++
  "  slli t1, s8, 3; add t2, s3, t1; ld t3, 0(t2)\n" ++
  "  slli t4, s8, 4; add t5, s6, t4\n" ++
  "  sd s5, 0(t5); sd t3, 8(t5)\n" ++
  "  add s5, s5, t3\n" ++
  "  addi s5, s5, 7; andi s5, s5, -8\n" ++
  "  addi s8, s8, 1\n" ++
  "  j .Lbvwri_pdesc_loop\n" ++
  ".Lbvwri_pdesc_done:\n" ++
  "  mv a0, s4; mv a1, s1; la a2, bvwri_value_descs; mv a3, s2\n" ++
  "  jal ra, block_validate_withdrawals_root_indexed\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0); sd a1, 8(t0)\n" ++
  "  j .Lbvwri_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptDeleteWalkDbFunction ++ "\n" ++
  mptInsertWalkDbFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  mptLeafExtractFunction ++ "\n" ++
  mptExtensionExtractFunction ++ "\n" ++
  mptExtensionNodeEncodeFunction ++ "\n" ++
  mptSetAccFunction ++ "\n" ++
  mptDeleteAccFunction ++ "\n" ++
  mptInsertAccFunction ++ "\n" ++
  mptStateRootInsFunction ++ "\n" ++
  mptIndexedTrieRootOneLeafFunction ++ "\n" ++
  mptIndexedLargeLeafHashFunction ++ "\n" ++
  mptIndexedTrieRootLargeFunction ++ "\n" ++
  mptIndexedTrieRootSmallFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  mptBoundedNodeRefFunction ++ "\n" ++
  mptBoundedEncodeBranchFunction ++ "\n" ++
  mptBoundedEncodeExtensionFunction ++ "\n" ++
  mptIndexedStreamLeafHashFunction ++ "\n" ++
  mptIndexedSortChangesFunction ++ "\n" ++
  mptIndexedLeafRefFunction ++ "\n" ++
  mptIndexedBuildSubtreeFunction ++ "\n" ++
  mptIndexedTrieRootBoundedFunction ++ "\n" ++
  mptIndexedTrieRootBoundedFromValuesFunction ++ "\n" ++
  headerExtractWithdrawalsRootFunction ++ "\n" ++
  blockValidateWithdrawalsRootIndexedFunction ++ "\n" ++
  ".Lbvwri_pdone:"

def ziskBlockValidateWithdrawalsRootIndexedDataSection : String :=
  ziskMptIndexedTrieRootSmallDataSection ++ "\n" ++
  ".balign 8\n" ++
  "hewr_offset:\n  .zero 8\n" ++
  "hewr_length:\n  .zero 8\n" ++
  "bvwri_expected_root:\n  .zero 32\n" ++
  "bvwri_computed_root:\n  .zero 32\n" ++
  "bvwri_value_descs:\n  .zero " ++ toString (itrIndexedEntryCapacity * 16)


end EvmAsm.Codegen
