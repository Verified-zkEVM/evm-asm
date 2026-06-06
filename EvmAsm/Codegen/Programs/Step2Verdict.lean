/-
  EvmAsm.Codegen.Programs.Step2Verdict

  step2_verdict (bead evm-asm-fhsxz.2.4.2, composition core): given a
  withdrawal-only block and its parent + pre-state witness, decide the
  successful_validation bit by composing the verified Step-2 pieces:

    1. block_header_ssz_to_rlp(payload, roots)        -> this header RLP
    2. validate_header_rlp_pair(this_rlp, parent_rlp) -> header validity
    3. withdrawals_state_root(parent.state_root,
         witness, withdrawals)                        -> recomputed post root
    4. memcmp(recomputed, this.state_root)            -> state-transition ok
    verdict = 1  iff  (header valid AND recompute ok AND root matches);
              else 0.

  This proves the WHOLE Step-2 verdict produces the right bit on a consistent
  synthetic block (verdict=1) and rejects a tampered one (verdict=0). It is
  the composition core of the guest-entry wiring (.2.4.2): the remaining work
  is feeding these inputs from the real SSZ guest input (the guest already
  decodes most of them for the NPR root). Soundness: verdict=1 REQUIRES the
  recomputed root to equal the claimed state_root, so an invalid block cannot
  false-positive.

  Bundles the union of the block_header / validate_header / withdrawals_state_root
  closures (deduped against the withdrawals base). All memcmp/byte reads are
  byte-wise (no-misaligned invariant).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Programs.MptSet
import EvmAsm.Codegen.Programs.MptSetAcc
import EvmAsm.Codegen.Programs.AccountBalance
import EvmAsm.Codegen.Programs.Withdrawal
import EvmAsm.Codegen.Programs.WithdrawalPath
import EvmAsm.Codegen.Programs.WithdrawalsStateRoot
import EvmAsm.Codegen.Programs.HeaderDecode
import EvmAsm.Codegen.Programs.HeaderBaseFee
import EvmAsm.Codegen.Programs.HeadersKeccak
import EvmAsm.Codegen.Programs.ValidateHeaderPair
import EvmAsm.Codegen.Programs.BlockHeaderSszToRlp

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## step2_verdict -- compose the full Step-2 successful_validation bit.

    a0 = params ptr (12 u64 fields):
      +0 payload   +8 parent_rlp  +16 parent_rlp_len  +24 parent_state_root
      +32 tx_root  +40 wd_root     +48 beacon_root     +56 requests_hash
      +64 wds_descriptors  +72 n_wds  +80 witness  +88 witness_len
    a0 (output) = verdict bit (0 / 1). -/
def step2VerdictFunction : String :=
  "step2_verdict:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # params\n" ++
  "  # 1. this header RLP = block_header_ssz_to_rlp(payload, 4 roots).\n" ++
  "  ld a0, 0(s0); ld a1, 32(s0); ld a2, 40(s0); ld a3, 48(s0); ld a4, 56(s0)\n" ++
  "  la a5, sv_this_rlp; la a6, sv_this_rlp_len\n" ++
  "  jal ra, block_header_ssz_to_rlp\n" ++
  "  # 2. validate_header_rlp_pair(this_rlp, parent_rlp).\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0)\n" ++
  "  ld a2, 8(s0); ld a3, 16(s0)\n" ++
  "  jal ra, validate_header_rlp_pair\n" ++
  "  mv s1, a0                   # header validity status\n" ++
  "  # 3. recompute post-state root from withdrawals over the pre-state.\n" ++
  "  ld a0, 24(s0); ld a1, 80(s0); ld a2, 88(s0)\n" ++
  "  ld a3, 64(s0); ld a4, 72(s0); la a5, sv_recomputed\n" ++
  "  jal ra, withdrawals_state_root\n" ++
  "  mv s2, a0                   # recompute status\n" ++
  "  # 4. memcmp(recomputed, this.state_root = payload+52) over 32 bytes.\n" ++
  "  la t0, sv_recomputed\n" ++
  "  ld t1, 0(s0); addi t1, t1, 52   # claimed state_root ptr\n" ++
  "  li t2, 32\n" ++
  ".Lsv_cmp:\n" ++
  "  beqz t2, .Lsv_cmp_ok\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1)\n" ++
  "  bne t3, t4, .Lsv_zero\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1\n" ++
  "  j .Lsv_cmp\n" ++
  ".Lsv_cmp_ok:\n" ++
  "  # 5. verdict = (header valid) AND (recompute ok) AND (root match).\n" ++
  "  bnez s1, .Lsv_zero\n" ++
  "  bnez s2, .Lsv_zero\n" ++
  "  li a0, 1\n" ++
  "  j .Lsv_ret\n" ++
  ".Lsv_zero:\n" ++
  "  li a0, 0\n" ++
  ".Lsv_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_step2_verdict`: probe. Input layout (file -> INPUT+8):
      +8  witness_len   +16 n_wds   +24 parent_rlp_len   +32 payload_len
      +40 parent_state_root(32)  +72 tx_root(32)  +104 wd_root(32)
      +136 beacon_root(32)  +168 requests_hash(32)
      +200 parent_rlp (parent_rlp_len, 8-aligned)
      then payload (payload_len, 8-aligned), then wd length table (N x u64)
      + wd blobs (8-aligned each), then witness (8-aligned).
    The prologue builds the params struct + the wd descriptor array, then
    calls step2_verdict. Output: OUTPUT+0 = verdict bit. -/
def ziskStep2VerdictPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # witness_len\n" ++
  "  ld a4, 16(t0)               # n_wds\n" ++
  "  ld a3, 24(t0)               # parent_rlp_len\n" ++
  "  ld a5, 32(t0)               # payload_len\n" ++
  "  la t1, sv_params\n" ++
  "  addi t2, t0, 40;  sd t2, 24(t1)  # parent_state_root\n" ++
  "  addi t2, t0, 72;  sd t2, 32(t1)  # tx_root\n" ++
  "  addi t2, t0, 104; sd t2, 40(t1)  # wd_root\n" ++
  "  addi t2, t0, 136; sd t2, 48(t1)  # beacon_root\n" ++
  "  addi t2, t0, 168; sd t2, 56(t1)  # requests_hash\n" ++
  "  sd a3, 16(t1)                    # parent_rlp_len\n" ++
  "  sd a4, 72(t1)                    # n_wds\n" ++
  "  sd a2, 88(t1)                    # witness_len\n" ++
  "  addi t3, t0, 200; sd t3, 8(t1)   # parent_rlp ptr (= INPUT+200)\n" ++
  "  # payload ptr = parent_rlp + roundup8(parent_rlp_len)\n" ++
  "  addi t4, a3, 7; andi t4, t4, -8; add t3, t3, t4; sd t3, 0(t1)\n" ++
  "  # wd table base = payload + roundup8(payload_len)\n" ++
  "  addi t4, a5, 7; andi t4, t4, -8; add t6, t3, t4\n" ++
  "  # build wd descriptor array at sv_wds; blobs after the N-entry length table.\n" ++
  "  slli t4, a4, 3; add t2, t6, t4   # blob cursor = wd_table + 8*N\n" ++
  "  la t5, sv_wds\n" ++
  "  li a0, 0\n" ++
  ".Lsvp_build:\n" ++
  "  beq a0, a4, .Lsvp_done\n" ++
  "  slli t3, a0, 3; add t3, t6, t3; ld t4, 0(t3)   # wd_rlp_len[i]\n" ++
  "  sd t2, 0(t5); sd t4, 8(t5)\n" ++
  "  addi t4, t4, 7; andi t4, t4, -8; add t2, t2, t4\n" ++
  "  addi t5, t5, 16; addi a0, a0, 1\n" ++
  "  j .Lsvp_build\n" ++
  ".Lsvp_done:\n" ++
  "  la t1, sv_params\n" ++
  "  sd t2, 80(t1)               # witness ptr (after last wd blob)\n" ++
  "  la t3, sv_wds; sd t3, 64(t1) # wds descriptors\n" ++
  "  mv a0, t1\n" ++
  "  jal ra, step2_verdict\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)   # verdict at OUTPUT+0\n" ++
  "  j .Lsv_pdone\n" ++
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
  ".Lsv_pdone:"

/-- Data section: the withdrawals_state_root scratch (covers the recompute +
    keccak + u256 + rfu + zk3 scratch) plus the validate_header and
    block_header extras (deduped) plus the verdict's own buffers. -/
def ziskStep2VerdictDataSection : String :=
  ziskWithdrawalsStateRootDataSection ++ "\n" ++
  -- validate_header_rlp_pair extras (u256m_acc/rfu_*/zk3_state already present)
  ".balign 32\n" ++
  "empty_ommers_hash:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47\n" ++
  ".balign 32\n" ++
  "hvbf_expected:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "hvpm_off:\n  .zero 8\n" ++
  "hvpm_len:\n  .zero 8\n" ++
  "hved_off:\n  .zero 8\n" ++
  "hved_len:\n  .zero 8\n" ++
  "hmd_offset:\n  .zero 8\n" ++
  "hmd_length:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "hvph_claimed:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "hvph_computed:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "vhrp_this_struct:\n  .zero 128\n" ++
  ".balign 8\n" ++
  "vhrp_parent_struct:\n  .zero 128\n" ++
  -- block_header_ssz_to_rlp extras (zk3_state already present)
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
  "bhr_result_len:\n  .zero 8\n" ++
  "bhr_payload:\n  .zero 1024\n" ++
  ".balign 8\n" ++
  "bhr_result:\n  .zero 1024\n" ++
  -- verdict scratch
  ".balign 8\n" ++
  "sv_this_rlp_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "sv_recomputed:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "sv_params:\n  .zero 96\n" ++
  "sv_wds:\n  .zero 1024\n" ++
  "sv_this_rlp:\n  .zero 1024"

def ziskStep2VerdictProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStep2VerdictPrologue
  dataAsm     := ziskStep2VerdictDataSection
}

end EvmAsm.Codegen
