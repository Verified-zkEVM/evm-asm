/-
  EvmAsm.Codegen.Programs.StatelessVerdict

  stateless_verdict_from_ssz (bead evm-asm-fhsxz.2.4.2): the END-TO-END Step-2
  verdict over a REAL `SszStatelessInput` blob — the glue that feeds
  `step2_verdict` from the live SSZ guest input via the three extractors
  (#7751/#7752/#7753) instead of a hand-built synthetic params struct.

  This closes the "verdict proven only on synthetic input" gap: the
  `zisk_stateless_verdict` probe is fed the SAME `-i` input file the EEST
  harness generates for a fixture (SSZ_BASE = INPUT + 16 + 2 = 0x40000012,
  identical to the guest's `decode_validation_bit`), navigates it with the
  real extractors, and emits the verdict bit — which must equal the fixture's
  `successful_validation`. Once this is green on real fixtures, the same
  `stateless_verdict_from_ssz` body is dropped into the guest epilogue to
  overwrite OUTPUT[32].

  Flow (no args; reads INPUT directly; returns a0 = verdict bit):
    SSZ_BASE = 0x40000012
    extract_payload_and_withdrawals  -> payload ptr, withdrawals ptr, count
    extract_witness_state_section    -> pre-state witness ptr, len
    extract_parent_header_and_state_root(SSZ_BASE, payload+0 = this.parent_hash)
                                     -> parent header RLP ptr/len, parent state_root
    for each SSZ Withdrawal (44 B): ssz_withdrawal_to_rlp -> descriptor (ptr,len)
    fill the 13-field step2_verdict params struct and call step2_verdict.

  Body roots fed to block_header_ssz_to_rlp: parent_beacon_block_root is the
  real NPR field (SSZ_BASE+24); transactions_root / withdrawals_root /
  requests_hash are placeholders (zeros) -- validate_header_rlp_pair does NOT
  cross-check them (it checks parent-linkage fields + this.parent_hash), so
  the verdict's soundness rests on the state-root recompute
  (withdrawals_state_root vs payload.state_root), which is conservative:
  non-existent-account / repeat / tx-bearing blocks recompute-mismatch ->
  verdict 0 (a MISS, never a false-positive on the state transition). The
  residual body-root gap is measured empirically by the EEST harness.

  Reuses the full step2_verdict asm closure + data section verbatim and adds
  the three extractors, header_extract_state_root, and ssz_withdrawal_to_rlp.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.Step2Verdict
import EvmAsm.Codegen.Programs.SszWithdrawal
import EvmAsm.Codegen.Programs.SszWitnessState
import EvmAsm.Codegen.Programs.SszPayloadWithdrawals
import EvmAsm.Codegen.Programs.SszParentHeader

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## stateless_verdict_from_ssz -- compose the verdict over a real SSZ input.
    No args (reads INPUT). a0 (output) = successful_validation bit (0/1). -/
def statelessVerdictFromSsz_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .LUI .x8 (262144 : BitVec 20),
    .ADDI .x8 .x8 (18 : BitVec 12),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.svf_payload (GuestAddrs.stateless_verdict_from_ssz + 44)),
    .ADDI .x11 .x11 (laLo GuestAddrs.svf_payload (GuestAddrs.stateless_verdict_from_ssz + 44)),
    .AUIPC .x12 (laHi GuestAddrs.svf_wds_ptr (GuestAddrs.stateless_verdict_from_ssz + 52)),
    .ADDI .x12 .x12 (laLo GuestAddrs.svf_wds_ptr (GuestAddrs.stateless_verdict_from_ssz + 52)),
    .AUIPC .x13 (laHi GuestAddrs.svf_wds_count (GuestAddrs.stateless_verdict_from_ssz + 60)),
    .ADDI .x13 .x13 (laLo GuestAddrs.svf_wds_count (GuestAddrs.stateless_verdict_from_ssz + 60)),
    .JAL .x1 (jalOff GuestAddrs.extract_payload_and_withdrawals (GuestAddrs.stateless_verdict_from_ssz + 68)),
    .BNE .x10 .x0 (384 : BitVec 13),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.svf_witness (GuestAddrs.stateless_verdict_from_ssz + 80)),
    .ADDI .x11 .x11 (laLo GuestAddrs.svf_witness (GuestAddrs.stateless_verdict_from_ssz + 80)),
    .AUIPC .x12 (laHi GuestAddrs.svf_witness_len (GuestAddrs.stateless_verdict_from_ssz + 88)),
    .ADDI .x12 .x12 (laLo GuestAddrs.svf_witness_len (GuestAddrs.stateless_verdict_from_ssz + 88)),
    .JAL .x1 (jalOff GuestAddrs.extract_witness_state_section (GuestAddrs.stateless_verdict_from_ssz + 96)),
    .MV .x10 .x8,
    .AUIPC .x5 (laHi GuestAddrs.svf_payload (GuestAddrs.stateless_verdict_from_ssz + 104)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_payload (GuestAddrs.stateless_verdict_from_ssz + 104)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.svf_parent_rlp (GuestAddrs.stateless_verdict_from_ssz + 116)),
    .ADDI .x12 .x12 (laLo GuestAddrs.svf_parent_rlp (GuestAddrs.stateless_verdict_from_ssz + 116)),
    .AUIPC .x13 (laHi GuestAddrs.svf_parent_rlp_len (GuestAddrs.stateless_verdict_from_ssz + 124)),
    .ADDI .x13 .x13 (laLo GuestAddrs.svf_parent_rlp_len (GuestAddrs.stateless_verdict_from_ssz + 124)),
    .AUIPC .x14 (laHi GuestAddrs.svf_parent_sr (GuestAddrs.stateless_verdict_from_ssz + 132)),
    .ADDI .x14 .x14 (laLo GuestAddrs.svf_parent_sr (GuestAddrs.stateless_verdict_from_ssz + 132)),
    .JAL .x1 (jalOff GuestAddrs.extract_parent_header_and_state_root (GuestAddrs.stateless_verdict_from_ssz + 140)),
    .BNE .x10 .x0 (312 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.svf_wds_count (GuestAddrs.stateless_verdict_from_ssz + 148)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_wds_count (GuestAddrs.stateless_verdict_from_ssz + 148)),
    .LD .x9 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_wds_ptr (GuestAddrs.stateless_verdict_from_ssz + 160)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_wds_ptr (GuestAddrs.stateless_verdict_from_ssz + 160)),
    .LD .x18 .x5 (0 : BitVec 12),
    .AUIPC .x19 (laHi GuestAddrs.svf_descriptors (GuestAddrs.stateless_verdict_from_ssz + 172)),
    .ADDI .x19 .x19 (laLo GuestAddrs.svf_descriptors (GuestAddrs.stateless_verdict_from_ssz + 172)),
    .AUIPC .x20 (laHi GuestAddrs.svf_rlp_arena (GuestAddrs.stateless_verdict_from_ssz + 180)),
    .ADDI .x20 .x20 (laLo GuestAddrs.svf_rlp_arena (GuestAddrs.stateless_verdict_from_ssz + 180)),
    .LI .x21 (0 : Word),
    .BGE .x21 .x9 (64 : BitVec 13),
    .MV .x10 .x18,
    .MV .x11 .x20,
    .AUIPC .x12 (laHi GuestAddrs.svf_wd_len (GuestAddrs.stateless_verdict_from_ssz + 204)),
    .ADDI .x12 .x12 (laLo GuestAddrs.svf_wd_len (GuestAddrs.stateless_verdict_from_ssz + 204)),
    .JAL .x1 (jalOff GuestAddrs.ssz_withdrawal_to_rlp (GuestAddrs.stateless_verdict_from_ssz + 212)),
    .SD .x19 .x20 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_wd_len (GuestAddrs.stateless_verdict_from_ssz + 220)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_wd_len (GuestAddrs.stateless_verdict_from_ssz + 220)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x19 .x6 (8 : BitVec 12),
    .ADDI .x18 .x18 (44 : BitVec 12),
    .ADDI .x20 .x20 (72 : BitVec 12),
    .ADDI .x19 .x19 (16 : BitVec 12),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .AUIPC .x6 (laHi GuestAddrs.sv_params (GuestAddrs.stateless_verdict_from_ssz + 256)),
    .ADDI .x6 .x6 (laLo GuestAddrs.sv_params (GuestAddrs.stateless_verdict_from_ssz + 256)),
    .AUIPC .x5 (laHi GuestAddrs.svf_payload (GuestAddrs.stateless_verdict_from_ssz + 264)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_payload (GuestAddrs.stateless_verdict_from_ssz + 264)),
    .LD .x5 .x5 (0 : BitVec 12),
    .SD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_parent_rlp (GuestAddrs.stateless_verdict_from_ssz + 280)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_parent_rlp (GuestAddrs.stateless_verdict_from_ssz + 280)),
    .LD .x5 .x5 (0 : BitVec 12),
    .SD .x6 .x5 (8 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_parent_rlp_len (GuestAddrs.stateless_verdict_from_ssz + 296)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_parent_rlp_len (GuestAddrs.stateless_verdict_from_ssz + 296)),
    .LD .x5 .x5 (0 : BitVec 12),
    .SD .x6 .x5 (16 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_parent_sr (GuestAddrs.stateless_verdict_from_ssz + 312)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_parent_sr (GuestAddrs.stateless_verdict_from_ssz + 312)),
    .SD .x6 .x5 (24 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_zero32 (GuestAddrs.stateless_verdict_from_ssz + 324)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_zero32 (GuestAddrs.stateless_verdict_from_ssz + 324)),
    .SD .x6 .x5 (32 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_zero32 (GuestAddrs.stateless_verdict_from_ssz + 336)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_zero32 (GuestAddrs.stateless_verdict_from_ssz + 336)),
    .SD .x6 .x5 (40 : BitVec 12),
    .ADDI .x5 .x8 (24 : BitVec 12),
    .SD .x6 .x5 (48 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_zero32 (GuestAddrs.stateless_verdict_from_ssz + 356)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_zero32 (GuestAddrs.stateless_verdict_from_ssz + 356)),
    .SD .x6 .x5 (56 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_zero32 (GuestAddrs.stateless_verdict_from_ssz + 368)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_zero32 (GuestAddrs.stateless_verdict_from_ssz + 368)),
    .SD .x6 .x5 (96 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_descriptors (GuestAddrs.stateless_verdict_from_ssz + 380)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_descriptors (GuestAddrs.stateless_verdict_from_ssz + 380)),
    .SD .x6 .x5 (64 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_wds_count (GuestAddrs.stateless_verdict_from_ssz + 392)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_wds_count (GuestAddrs.stateless_verdict_from_ssz + 392)),
    .LD .x5 .x5 (0 : BitVec 12),
    .SD .x6 .x5 (72 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_witness (GuestAddrs.stateless_verdict_from_ssz + 408)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_witness (GuestAddrs.stateless_verdict_from_ssz + 408)),
    .LD .x5 .x5 (0 : BitVec 12),
    .SD .x6 .x5 (80 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.svf_witness_len (GuestAddrs.stateless_verdict_from_ssz + 424)),
    .ADDI .x5 .x5 (laLo GuestAddrs.svf_witness_len (GuestAddrs.stateless_verdict_from_ssz + 424)),
    .LD .x5 .x5 (0 : BitVec 12),
    .SD .x6 .x5 (88 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.sv_params (GuestAddrs.stateless_verdict_from_ssz + 440)),
    .ADDI .x10 .x10 (laLo GuestAddrs.sv_params (GuestAddrs.stateless_verdict_from_ssz + 440)),
    .JAL .x1 (jalOff GuestAddrs.step2_verdict (GuestAddrs.stateless_verdict_from_ssz + 448)),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `statelessVerdictFromSsz_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def statelessVerdictFromSsz_relocs : RelocTable :=
  [ (11, .la .x11 "svf_payload"),
    (13, .la .x12 "svf_wds_ptr"),
    (15, .la .x13 "svf_wds_count"),
    (17, .jal .x1 "extract_payload_and_withdrawals"),
    (20, .la .x11 "svf_witness"),
    (22, .la .x12 "svf_witness_len"),
    (24, .jal .x1 "extract_witness_state_section"),
    (26, .la .x5 "svf_payload"),
    (29, .la .x12 "svf_parent_rlp"),
    (31, .la .x13 "svf_parent_rlp_len"),
    (33, .la .x14 "svf_parent_sr"),
    (35, .jal .x1 "extract_parent_header_and_state_root"),
    (37, .la .x5 "svf_wds_count"),
    (40, .la .x5 "svf_wds_ptr"),
    (43, .la .x19 "svf_descriptors"),
    (45, .la .x20 "svf_rlp_arena"),
    (51, .la .x12 "svf_wd_len"),
    (53, .jal .x1 "ssz_withdrawal_to_rlp"),
    (55, .la .x5 "svf_wd_len"),
    (64, .la .x6 "sv_params"),
    (66, .la .x5 "svf_payload"),
    (70, .la .x5 "svf_parent_rlp"),
    (74, .la .x5 "svf_parent_rlp_len"),
    (78, .la .x5 "svf_parent_sr"),
    (81, .la .x5 "svf_zero32"),
    (84, .la .x5 "svf_zero32"),
    (89, .la .x5 "svf_zero32"),
    (92, .la .x5 "svf_zero32"),
    (95, .la .x5 "svf_descriptors"),
    (98, .la .x5 "svf_wds_count"),
    (102, .la .x5 "svf_witness"),
    (106, .la .x5 "svf_witness_len"),
    (110, .la .x10 "sv_params"),
    (112, .jal .x1 "step2_verdict") ]

def statelessVerdictFromSszFunction : String :=
  "stateless_verdict_from_ssz:\n" ++ emitProgramR statelessVerdictFromSsz_prog statelessVerdictFromSsz_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `statelessVerdictFromSsz_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem statelessVerdictFromSszFunction_eq_prog :
    statelessVerdictFromSszFunction = "stateless_verdict_from_ssz:\n" ++ emitProgramR statelessVerdictFromSsz_prog statelessVerdictFromSsz_relocs := rfl

#guard statelessVerdictFromSszFunction.startsWith "stateless_verdict_from_ssz:\n"
#guard statelessVerdictFromSsz_prog.length = 124
/-- `zisk_stateless_verdict`: probe. Fed the SAME `-i` input file the EEST
    harness generates for a fixture (SSZ_BASE = 0x40000012). Output:
    OUTPUT+0 = verdict bit (the successful_validation byte the guest sets). -/
def ziskStatelessVerdictPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  jal ra, stateless_verdict_from_ssz\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)       # verdict at OUTPUT+0\n" ++
  "  j .Lsvf_pdone\n" ++
  -- full step2_verdict asm closure (verbatim from ziskStep2VerdictPrologue):
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256DivU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256EqFunction ++ "\n" ++
  u256LtBeFunction ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  withdrawalToPathDeltaFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountAddBalanceFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptSetAccFunction ++ "\n" ++
  mptStateRootFunction ++ "\n" ++
  withdrawalsStateRootFunction ++ "\n" ++
  validateHeaderBasicFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  headerValidatePostMergeFunction ++ "\n" ++
  headerValidateExtraDataLengthFunction ++ "\n" ++
  amsterdamBlobGasPriceU256Function ++ "\n" ++
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  headerValidateBaseFeeFunction ++ "\n" ++
  headerValidateExcessBlobGasFunction ++ "\n" ++
  validateHeaderFullFunction ++ "\n" ++
  -- cursor-walk helpers (closure-drift fix for rewritten decoders)
  rlpWalkHelpersClosure ++ "\n" ++
  headerExtendedDecodeFunction ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headerValidateParentHashFunction ++ "\n" ++
  validateHeaderRlpPairFunction ++ "\n" ++
  bhrRevLeBeFunction ++ "\n" ++
  blockHeaderSszToRlpFunction ++ "\n" ++
  step2VerdictFunction ++ "\n" ++
  -- extractors + their leaf helpers + the SSZ withdrawal converter:
  headerExtractStateRootFunction ++ "\n" ++
  ephU32leFunction ++ "\n" ++
  extractParentHeaderAndStateRootFunction ++ "\n" ++
  spwU32leFunction ++ "\n" ++
  extractPayloadAndWithdrawalsFunction ++ "\n" ++
  swsU32leFunction ++ "\n" ++
  extractWitnessStateSectionFunction ++ "\n" ++
  swrRevLeBeFunction ++ "\n" ++
  sszWithdrawalToRlpFunction ++ "\n" ++
  statelessVerdictFromSszFunction ++ "\n" ++
  ".Lsvf_pdone:"

/-- Data: the full step2_verdict data section + header_extract_state_root
    scratch (hesr_*) + ssz_withdrawal scratch (swr_*) + the extractor
    scratch (eph_*) + this glue's own buffers (svf_*). -/
def ziskStatelessVerdictDataSection : String :=
  ziskStep2VerdictDataSection ++ "\n" ++
  -- header_extract_state_root scratch (step2 never calls it):
  ".balign 8\n" ++
  "hesr_offset:\n  .zero 8\n" ++
  "hesr_length:\n  .zero 8\n" ++
  -- extract_parent_header_and_state_root witness_lookup scratch:
  ".balign 8\n" ++
  "eph_off:\n  .zero 8\n" ++
  "eph_len:\n  .zero 8\n" ++
  -- ssz_withdrawal_to_rlp scratch:
  ".balign 8\n" ++
  "swr_flen:\n  .zero 8\n" ++
  "swr_prefix_len:\n  .zero 8\n" ++
  "swr_be:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "swr_payload:\n  .zero 128\n" ++
  -- this glue's buffers:
  ".balign 8\n" ++
  "svf_payload:\n  .zero 8\n" ++
  "svf_wds_ptr:\n  .zero 8\n" ++
  "svf_wds_count:\n  .zero 8\n" ++
  "svf_witness:\n  .zero 8\n" ++
  "svf_witness_len:\n  .zero 8\n" ++
  "svf_parent_rlp:\n  .zero 8\n" ++
  "svf_parent_rlp_len:\n  .zero 8\n" ++
  "svf_wd_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "svf_parent_sr:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "svf_zero32:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "svf_descriptors:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "svf_rlp_arena:\n  .zero 1152"

def ziskStatelessVerdictProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStatelessVerdictPrologue
  dataAsm     := ziskStatelessVerdictDataSection
}

end EvmAsm.Codegen
