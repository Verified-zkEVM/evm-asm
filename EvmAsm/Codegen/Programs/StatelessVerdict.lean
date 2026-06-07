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
    fill the 12-field step2_verdict params struct and call step2_verdict.

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
def statelessVerdictFromSszFunction : String :=
  "stateless_verdict_from_ssz:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  li s0, 0x40000000\n" ++
  "  addi s0, s0, 18             # s0 = SSZ_BASE (INPUT + 16 + 2)\n" ++
  "  # 1. payload + withdrawals.\n" ++
  "  mv a0, s0\n" ++
  "  la a1, svf_payload; la a2, svf_wds_ptr; la a3, svf_wds_count\n" ++
  "  jal ra, extract_payload_and_withdrawals\n" ++
  "  # 2. pre-state witness section.\n" ++
  "  mv a0, s0\n" ++
  "  la a1, svf_witness; la a2, svf_witness_len\n" ++
  "  jal ra, extract_witness_state_section\n" ++
  "  # 3. parent header + state_root (this.parent_hash = payload + 0).\n" ++
  "  mv a0, s0\n" ++
  "  la t0, svf_payload; ld a1, 0(t0)\n" ++
  "  la a2, svf_parent_rlp; la a3, svf_parent_rlp_len; la a4, svf_parent_sr\n" ++
  "  jal ra, extract_parent_header_and_state_root\n" ++
  "  bnez a0, .Lsvf_zero         # parent not found / parse fail\n" ++
  "  # 4. SSZ withdrawals (44 B each) -> RLP descriptors (ptr,len) 16 B each.\n" ++
  "  la t0, svf_wds_count; ld s1, 0(t0)    # s1 = count\n" ++
  "  la t0, svf_wds_ptr;   ld s2, 0(t0)    # s2 = ssz withdrawals base\n" ++
  "  la s3, svf_descriptors                # s3 = descriptor cursor\n" ++
  "  la s4, svf_rlp_arena                  # s4 = rlp arena cursor\n" ++
  "  li s5, 0\n" ++
  ".Lsvf_wloop:\n" ++
  "  bge s5, s1, .Lsvf_wdone\n" ++
  "  mv a0, s2; mv a1, s4; la a2, svf_wd_len\n" ++
  "  jal ra, ssz_withdrawal_to_rlp\n" ++
  "  sd s4, 0(s3)\n" ++
  "  la t0, svf_wd_len; ld t1, 0(t0); sd t1, 8(s3)\n" ++
  "  addi s2, s2, 44\n" ++
  "  addi s4, s4, 72\n" ++
  "  addi s3, s3, 16\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lsvf_wloop\n" ++
  ".Lsvf_wdone:\n" ++
  "  # 5. fill the 12-field step2_verdict params struct (sv_params).\n" ++
  "  la t1, sv_params\n" ++
  "  la t0, svf_payload;        ld t0, 0(t0); sd t0, 0(t1)   # payload\n" ++
  "  la t0, svf_parent_rlp;     ld t0, 0(t0); sd t0, 8(t1)   # parent_rlp ptr\n" ++
  "  la t0, svf_parent_rlp_len; ld t0, 0(t0); sd t0, 16(t1)  # parent_rlp_len\n" ++
  "  la t0, svf_parent_sr;      sd t0, 24(t1)                # parent_state_root ptr\n" ++
  "  la t0, svf_zero32;         sd t0, 32(t1)                # tx_root (placeholder)\n" ++
  "  la t0, svf_zero32;         sd t0, 40(t1)                # wd_root (placeholder)\n" ++
  "  addi t0, s0, 24;           sd t0, 48(t1)                # parent_beacon_block_root (NPR+8)\n" ++
  "  la t0, svf_zero32;         sd t0, 56(t1)                # requests_hash (placeholder)\n" ++
  "  la t0, svf_descriptors;    sd t0, 64(t1)                # wds_descriptors\n" ++
  "  la t0, svf_wds_count;      ld t0, 0(t0); sd t0, 72(t1)  # n_wds\n" ++
  "  la t0, svf_witness;        ld t0, 0(t0); sd t0, 80(t1)  # witness\n" ++
  "  la t0, svf_witness_len;    ld t0, 0(t0); sd t0, 88(t1)  # witness_len\n" ++
  "  # 6. verdict = step2_verdict(params).\n" ++
  "  la a0, sv_params\n" ++
  "  jal ra, step2_verdict\n" ++
  "  j .Lsvf_ret\n" ++
  ".Lsvf_zero:\n" ++
  "  li a0, 0\n" ++
  ".Lsvf_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

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
  rlpFieldToU64Function ++ "\n" ++
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
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  headerValidateBaseFeeFunction ++ "\n" ++
  validateHeaderFullFunction ++ "\n" ++
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
