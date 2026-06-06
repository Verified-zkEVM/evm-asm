/-
  EvmAsm.Codegen.Programs.StatelessGuestEpilogue

  Validator-pipeline + .Lsg_hash merkle epilogue for the
  `stateless_guest` ELF. Carved out of `Programs.lean` for the
  file-size hard cap; consumed by the registry hub via
  `statelessGuestEpilogue` (and its inner
  `statelessGuestValidatorPipeline`).
-/
import EvmAsm.Codegen.Programs.ChainValidate
import EvmAsm.Codegen.Programs.ChainValidateBlob
import EvmAsm.Codegen.Programs.ChainValidatePostMerge
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Ssz
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.BlockVerdict
import EvmAsm.Codegen.Programs.BlockVerdictV2

namespace EvmAsm.Codegen

/-! ## stateless_guest header-validator pipeline (integration PR)

    Inserted between the body's `serialize_stateless_output` and the
    existing SSZ `hash_tree_root` epilogue. Reads N=x16 (header count),
    section_ptr=x17 (witness.headers section), section_len=x14, then
    iterates a curated set of K-PR header validators on the chain.

    On any K-PR violation: writes 0xFEFEFE..FE marker + 8-byte reason
    code at OUTPUT_ADDR and HALTs (matches Stateless.unimplemented_exit
    layout).  On all-pass: overrides OUTPUT[32] := 1 (the
    `successful_validation` byte) and falls through to the hash code.

    s2 = N (callee-saved)
    s3 = section_ptr (callee-saved)
    s4 = section_len (callee-saved)
    s5 = headers_data_ptr = section_ptr + 4*N (callee-saved)

    Reason codes (see `EvmAsm/Stateless/Unimplemented.lean`):
      0x10 POST_MERGE_VIOLATION (K290)
      0x11 EXTRA_DATA_TOO_LONG  (K291)
      0x12 GAS_USED_OVER_LIMIT  (K240)
      0x13 BLOB_GAS_MISALIGNED  (K278)
      0x14 BLOB_GAS_OVER_MAX    (K277)
      0x15 TIMESTAMP_NOT_INCREASING (K229)
      0x16 NUMBERS_NOT_CONSECUTIVE  (K230)
      0x17 RLP_PARSE_FAIL_IN_HEADER (any K-PR returns nonzero status) -/
def statelessGuestValidatorPipeline : String :=
  "  # PR-integration: header-validator pipeline\n" ++
  "  li sp, 0xa0050000\n" ++
  "  mv s2, x16                  # s2 = N\n" ++
  "  mv s3, x21                  # s3 = section_ptr (now from decoder's x21,\n" ++
  "                              # which holds headers_addr; x17 is kept as\n" ++
  "                              # SSZ_BASE for the encoder's bounded byte-copy)\n" ++
  "  mv s4, x14                  # s4 = section_len\n" ++
  "  beqz s2, .Lsg_all_pass      # N=0: skip validators\n" ++
  "  # Build sg_header_lengths[N]: convert N u32 inner-offset deltas\n" ++
  "  # to N u64 absolute lengths.\n" ++
  "  mv t0, s3                   # t0 = offsets cursor (section_ptr)\n" ++
  "  la t1, sg_header_lengths    # t1 = lengths-out cursor\n" ++
  "  mv t2, s2                   # t2 = i (counts down from N)\n" ++
  ".Lsg_bl:\n" ++
  "  beqz t2, .Lsg_bl_done\n" ++
  "  lwu t3, 0(t0)               # t3 = inner_offset[i]\n" ++
  "  addi t4, t2, -1\n" ++
  "  beqz t4, .Lsg_bl_last       # if last header, end = section_len\n" ++
  "  lwu t5, 4(t0)               # t5 = inner_offset[i+1]\n" ++
  "  j .Lsg_bl_diff\n" ++
  ".Lsg_bl_last:\n" ++
  "  mv t5, s4                   # t5 = section_len\n" ++
  ".Lsg_bl_diff:\n" ++
  "  sub t5, t5, t3              # length_i = end - start\n" ++
  "  sd t5, 0(t1)\n" ++
  "  addi t0, t0, 4\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lsg_bl\n" ++
  ".Lsg_bl_done:\n" ++
  "  # s5 = headers_data_ptr = section_ptr + 4*N\n" ++
  "  slli t0, s2, 2\n" ++
  "  add s5, s3, t0\n" ++
  "  # Validator 1: K290 chain_validate_post_merge_full\n" ++
  "  mv a0, s2; la a1, sg_header_lengths; mv a2, s5\n" ++
  "  la a3, sg_kpr_valid; la a4, sg_kpr_bad_index\n" ++
  "  jal ra, chain_validate_post_merge_full\n" ++
  "  bnez a0, .Lsg_fail_rlp\n" ++
  "  la t0, sg_kpr_valid; ld t1, 0(t0); beqz t1, .Lsg_fail_pm\n" ++
  "  # Validator 2: K291 chain_validate_extra_data_length\n" ++
  "  mv a0, s2; la a1, sg_header_lengths; mv a2, s5\n" ++
  "  la a3, sg_kpr_valid; la a4, sg_kpr_bad_index\n" ++
  "  jal ra, chain_validate_extra_data_length\n" ++
  "  bnez a0, .Lsg_fail_rlp\n" ++
  "  la t0, sg_kpr_valid; ld t1, 0(t0); beqz t1, .Lsg_fail_ed\n" ++
  "  # Validator 3: K240 chain_validate_gas_used_under_limit\n" ++
  "  mv a0, s2; la a1, sg_header_lengths; mv a2, s5\n" ++
  "  la a3, sg_kpr_valid; la a4, sg_kpr_bad_index\n" ++
  "  jal ra, chain_validate_gas_used_under_limit\n" ++
  "  bnez a0, .Lsg_fail_rlp\n" ++
  "  la t0, sg_kpr_valid; ld t1, 0(t0); beqz t1, .Lsg_fail_gas\n" ++
  "  # Validator 4: K278 chain_validate_blob_gas_used_multiple\n" ++
  "  mv a0, s2; la a1, sg_header_lengths; mv a2, s5\n" ++
  "  la a3, sg_kpr_valid; la a4, sg_kpr_bad_index\n" ++
  "  jal ra, chain_validate_blob_gas_used_multiple\n" ++
  "  bnez a0, .Lsg_fail_rlp\n" ++
  "  la t0, sg_kpr_valid; ld t1, 0(t0); beqz t1, .Lsg_fail_bgm\n" ++
  "  # Validator 5: K277 chain_validate_blob_gas_used_under_max\n" ++
  "  mv a0, s2; la a1, sg_header_lengths; mv a2, s5\n" ++
  "  la a3, sg_kpr_valid; la a4, sg_kpr_bad_index\n" ++
  "  jal ra, chain_validate_blob_gas_used_under_max\n" ++
  "  bnez a0, .Lsg_fail_rlp\n" ++
  "  la t0, sg_kpr_valid; ld t1, 0(t0); beqz t1, .Lsg_fail_bgum\n" ++
  "  # Validator 6: K229 chain_validate_increasing_timestamps\n" ++
  "  mv a0, s2; la a1, sg_header_lengths; mv a2, s5\n" ++
  "  la a3, sg_kpr_valid; la a4, sg_kpr_bad_index\n" ++
  "  jal ra, chain_validate_increasing_timestamps\n" ++
  "  bnez a0, .Lsg_fail_rlp\n" ++
  "  la t0, sg_kpr_valid; ld t1, 0(t0); beqz t1, .Lsg_fail_ts\n" ++
  "  # Validator 7: K230 chain_validate_consecutive_numbers\n" ++
  "  mv a0, s2; la a1, sg_header_lengths; mv a2, s5\n" ++
  "  la a3, sg_kpr_valid; la a4, sg_kpr_bad_index\n" ++
  "  jal ra, chain_validate_consecutive_numbers\n" ++
  "  bnez a0, .Lsg_fail_rlp\n" ++
  "  la t0, sg_kpr_valid; ld t1, 0(t0); beqz t1, .Lsg_fail_nm\n" ++
  ".Lsg_all_pass:\n" ++
  "  # All validators that ran passed (or N=0 fast-path). NB: with\n" ++
  "  # the new-schema decoder stubs in `EvmAsm/Stateless/SSZ/Decode/\n" ++
  "  # Program.lean`, N is always 0 right now, so no real validation\n" ++
  "  # has occurred. We deliberately do NOT override OUTPUT[32]:\n" ++
  "  # the encoder already wrote `x11` (= 0 from the decoder stub),\n" ++
  "  # matching the spec's `verify_stateless_new_payload(empty) ==\n" ++
  "  # False` outcome. Once the real witness walk + validators run,\n" ++
  "  # the body's encoder will see x11 = 1 from a real success.\n" ++
  "  j .Lsg_hash\n" ++
  ".Lsg_fail_pm:   li a0, 0x10; j .Lsg_unimpl\n" ++
  ".Lsg_fail_ed:   li a0, 0x11; j .Lsg_unimpl\n" ++
  ".Lsg_fail_gas:  li a0, 0x12; j .Lsg_unimpl\n" ++
  ".Lsg_fail_bgm:  li a0, 0x13; j .Lsg_unimpl\n" ++
  ".Lsg_fail_bgum: li a0, 0x14; j .Lsg_unimpl\n" ++
  ".Lsg_fail_ts:   li a0, 0x15; j .Lsg_unimpl\n" ++
  ".Lsg_fail_nm:   li a0, 0x16; j .Lsg_unimpl\n" ++
  ".Lsg_fail_rlp:  li a0, 0x17\n" ++
  ".Lsg_unimpl:\n" ++
  "  # Previously this block wrote the 0xFEFEFEFEFEFEFEFE unimplemented-\n" ++
  "  # exit marker at OUTPUT[0..8) plus the REASON code at OUTPUT[8..16),\n" ++
  "  # then halted with ECALL. That diverged from the spec's behaviour\n" ++
  "  # for the same input shape (spec catches the validator exception\n" ++
  "  # and returns valid=False with chain_config echo + empty NPR root).\n" ++
  "  # Falling through to .Lsg_hash matches the spec: the encoder's\n" ++
  "  # x11=0 writes valid=False to OUTPUT[32], .Lsg_hash computes\n" ++
  "  # the NPR root at OUTPUT[0..32), and the codegen halt stub takes\n" ++
  "  # over.\n" ++
  "  j .Lsg_hash"

def statelessGuestEpilogue : String :=
  statelessGuestValidatorPipeline ++ "\n" ++
  ".Lsg_hash:\n" ++
  "  # Compute `compute_new_payload_request_root(stateless_input)`\n" ++
  "  # at OUTPUT[0..32) -- the SSZ merkle root over the four NPR\n" ++
  "  # field roots:\n" ++
  "  #   field_root[0] = hash_tree_root(execution_payload)\n" ++
  "  #   field_root[1] = hash_tree_root(versioned_hashes)\n" ++
  "  #   field_root[2] = parent_beacon_block_root      (Bytes32 inline)\n" ++
  "  #   field_root[3] = hash_tree_root(execution_requests)\n" ++
  "  # field_root[0], field_root[1], and field_root[3] are derived\n" ++
  "  # dynamically into `npr_exec_payload_root`,\n" ++
  "  # `npr_versioned_hashes_dyn`, and `npr_exec_requests_dyn`.\n" ++
  "  # field_root[2] is read from input at NPR_addr + 8 (NPR_addr\n" ++
  "  # = SSZ_BASE + outer.offsets[0]; for this schema outer.offsets[0]\n" ++
  "  # is always 16).\n" ++
  "  # \n" ++
  "  # Computation:\n" ++
  "  #   left_subtree  = sha256(npr_exec_payload_root ||\n" ++
  "  #                          npr_versioned_hashes_dyn)\n" ++
  "  #   right_subtree = sha256(parent_beacon_block_root ||\n" ++
  "  #                          npr_exec_requests_dyn)\n" ++
  "  #   npr_root      = sha256(left_subtree || right_subtree)\n" ++
  "  # \n" ++
  "  # For pbr=zero (every previously-shipped fixture) the\n" ++
  "  # computation reproduces the precomputed `empty_npr_root`\n" ++
  "  # constant. For non-empty pbr it produces the spec-matching\n" ++
  "  # root.\n" ++
  "  # \n" ++
  "  # Re-derive SSZ_BASE in s6 (callee-saved -- survives zkvm_sha256\n" ++
  "  # calls). K-PR pipeline only saves s0-s5 in its validators, so\n" ++
  "  # s6 is free.\n" ++
  "  li s6, 0x40000000\n" ++
  "  addi s6, s6, 18             # s6 = SSZ_BASE\n" ++
  "  # Preserve zisk's current trap vector: the embedded verdict uses a\n" ++
  "  # large scratch arena and can overwrite CSR-like system memory.\n" ++
  "  li t0, 0xa0009828           # zisk MTVEC memory slot\n" ++
  "  ld t1, 0(t0)\n" ++
  "  la t2, npr_saved_mtvec\n" ++
  "  sd t1, 0(t2)\n" ++
  "  # \n" ++
  "  # ===== dynamic NPR list field-roots (replace empty-list consts) =====\n" ++
  "  # exec_payload_addr = NPR_addr + 44 (NPR fixed header) = s6 + 16 + 44\n" ++
  "  # = s6 + 60. The variable fields' u32 offsets sit in the exec_payload\n" ++
  "  # fixed header: transactions @ +504, withdrawals @ +508,\n" ++
  "  # block_access_list @ +528. The list/bytes helpers cap N<=32 elements\n" ++
  "  # and <=1024 bytes/element; blocks beyond that stay root-diffs.\n" ++
  "  # All offset reads use sg_load_u32le (LBU-packed): the SSZ base s6 is\n" ++
  "  # 0x40000012 (mod 4 = 2), so a direct LWU would be a misaligned access\n" ++
  "  # (the verified RV64 subset traps on those). s7/s8 are scratch (free:\n" ++
  "  # the validator pipeline only uses s2-s5 and s6=SSZ_BASE; the ssz_*\n" ++
  "  # helpers save s0-s6 and never touch s7/s8).\n" ++
  "  # --- transactions_root = hash_tree_root(List[ByteList[2^30], 2^20]) ---\n" ++
  "  addi a0, s6, 564           # &transactions_offset (exec_payload+504)\n" ++
  "  jal ra, sg_load_u32le\n" ++
  "  mv s7, a0                  # s7 = transactions_offset\n" ++
  "  addi a0, s6, 568           # &withdrawals_offset (exec_payload+508)\n" ++
  "  jal ra, sg_load_u32le\n" ++
  "  mv s8, a0                  # s8 = withdrawals_offset\n" ++
  "  addi t0, s6, 60            # exec_payload_addr\n" ++
  "  add a0, t0, s7             # transactions_start (unaligned ptr OK: helper offset\n" ++
  "                             # table now LBU-packed; element bytes via LBU packer)\n" ++
  "  sub a1, s8, s7             # transactions_len\n" ++
  "  li a2, 25                  # per-element chunk-cap log2 (2^30 / 32)\n" ++
  "  li a3, 20                  # list capacity log2 (MAX_TRANSACTIONS_PER_PAYLOAD)\n" ++
  "  la a4, npr_dynamic_tx_root\n" ++
  "  jal ra, ssz_hash_tree_root_list_bytelist\n" ++
  "  # --- block_access_list_root = hash_tree_root(ByteList[2^24]) ---\n" ++
  "  # bal section ends at exec_payload end = NPR + versioned_hashes_offset.\n" ++
  "  addi a0, s6, 588           # &block_access_list_offset (exec_payload+528)\n" ++
  "  jal ra, sg_load_u32le\n" ++
  "  mv s7, a0                  # s7 = block_access_list_offset\n" ++
  "  addi a0, s6, 20            # &versioned_hashes_offset (NPR+4)\n" ++
  "  jal ra, sg_load_u32le\n" ++
  "  mv s8, a0                  # s8 = versioned_hashes_offset (= exec_payload end rel NPR)\n" ++
  "  addi t0, s6, 60            # exec_payload_addr\n" ++
  "  add a0, t0, s7             # bal_start (unaligned OK: htr_bytes packs via LBU)\n" ++
  "  addi t1, s6, 16            # NPR_addr\n" ++
  "  add t1, t1, s8             # exec_payload_end = NPR + versioned_hashes_offset\n" ++
  "  sub a1, t1, a0             # bal_len\n" ++
  "  li a2, 19                  # chunk-cap log2 (2^24 / 32)\n" ++
  "  la a3, npr_dynamic_bal_root\n" ++
  "  jal ra, ssz_hash_tree_root_bytes\n" ++
  "  # --- versioned_hashes_root = hash_tree_root(List[Bytes32, 4096]) ---\n" ++
  "  # NPR field 1: fixed-size Bytes32 elements (no inner offset table), so\n" ++
  "  # the section is N*32 bytes (N = len/32) and the root is\n" ++
  "  # merkleize(section_chunks, capacity 2^12) then mix_in_length(N).\n" ++
  "  # Offsets: versioned_hashes @ NPR+4 (s6+20), execution_requests @\n" ++
  "  # NPR+40 (s6+56); read via sg_load_u32le (LBU -- s6 is unaligned).\n" ++
  "  addi a0, s6, 20            # &versioned_hashes_offset (NPR+4)\n" ++
  "  jal ra, sg_load_u32le\n" ++
  "  mv s7, a0                  # s7 = versioned_hashes_offset (rel NPR)\n" ++
  "  addi a0, s6, 56            # &execution_requests_offset (NPR+40)\n" ++
  "  jal ra, sg_load_u32le\n" ++
  "  sub s9, a0, s7             # s9 = versioned_hashes section_len\n" ++
  "  addi t0, s6, 16            # NPR_addr\n" ++
  "  add a1, t0, s7             # src = NPR + versioned_hashes_offset (unaligned)\n" ++
  "  la a0, npr_vh_aligned      # dst (8-byte aligned)\n" ++
  "  mv a2, s9                  # len\n" ++
  "  jal ra, sg_memcpy          # byte-copy section -> aligned buffer\n" ++
  "  srli s10, s9, 5            # s10 = N = section_len / 32\n" ++
  "  la a0, npr_vh_aligned\n" ++
  "  mv a1, s10                 # N chunks (Bytes32 = 1 chunk each)\n" ++
  "  li a2, 12                  # capacity log2 (MAX_BLOB_COMMITMENTS_PER_BLOCK)\n" ++
  "  la a3, npr_vh_partial\n" ++
  "  jal ra, ssz_merkleize      # pre-mix merkle root -> npr_vh_partial\n" ++
  "  # mix_in_length: sha256(partial || u256_le(N)) -> npr_versioned_hashes_dyn\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_vh_partial\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  sd s10, 32(t1)             # length = N (u64 LE)\n" ++
  "  sd zero, 40(t1); sd zero, 48(t1); sd zero, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_versioned_hashes_dyn\n" ++
  "  jal ra, zkvm_sha256\n" ++
  "  # --- withdrawals_root = hash_tree_root(List[SszWithdrawal, 16]) ---\n" ++
  "  # ExecutionPayload field 14: fixed 44-byte containers (index u64,\n" ++
  "  # validator_index u64, address ByteVector[20], amount u64), no inner\n" ++
  "  # offset table; section = N*44 at exec_payload+withdrawals_offset\n" ++
  "  # (@+508), ending at block_access_list_offset (@+528).\n" ++
  "  addi a0, s6, 568           # &withdrawals_offset (exec_payload+508)\n" ++
  "  jal ra, sg_load_u32le\n" ++
  "  mv s7, a0                  # s7 = withdrawals_offset (rel exec_payload)\n" ++
  "  addi a0, s6, 588           # &block_access_list_offset (exec_payload+528)\n" ++
  "  jal ra, sg_load_u32le\n" ++
  "  sub s9, a0, s7             # s9 = withdrawals section_len\n" ++
  "  addi t0, s6, 60            # exec_payload_addr\n" ++
  "  add a0, t0, s7             # withdrawals_start (unaligned ptr OK)\n" ++
  "  mv a1, s9                  # section_len\n" ++
  "  la a2, npr_dynamic_wd_root\n" ++
  "  jal ra, ssz_htr_withdrawals\n" ++
  "  # --- execution_requests_root = hash_tree_root(SszExecutionRequests) ---\n" ++
  "  # NewPayloadRequest field 3 (last variable field): a container of three\n" ++
  "  # List[Container] fields. Section = [NPR+er_off, NPR_end=witness_off).\n" ++
  "  # er_off @ NPR+40 (s6+56); witness_off = outer.offsets[1] @ blob+4 (s6+4).\n" ++
  "  addi a0, s6, 56            # &execution_requests_offset (NPR+40)\n" ++
  "  jal ra, sg_load_u32le\n" ++
  "  mv s7, a0                  # s7 = execution_requests_offset (rel NPR)\n" ++
  "  addi a0, s6, 4             # &witness_offset (outer.offsets[1])\n" ++
  "  jal ra, sg_load_u32le\n" ++
  "  mv s8, a0                  # s8 = witness_offset (= NPR end, rel blob)\n" ++
  "  addi a0, s6, 16            # NPR_addr\n" ++
  "  add a0, a0, s7             # er_section_start = NPR + er_off\n" ++
  "  sub a1, s8, s7             # witness_off - er_off\n" ++
  "  addi a1, a1, -16           # er_section_len = witness_off - 16 - er_off\n" ++
  "  la a2, npr_exec_requests_dyn\n" ++
  "  jal ra, ssz_htr_execution_requests\n" ++
  "  # ===== exec_payload merkle path (leaves 0-15) =====\n" ++
  "  # Path leaf_6 -> node_6_7 -> node_4_7 -> node_0_7 -> node_0_15\n" ++
  "  # \n" ++
  "  # Dynamic leaf_4 = hash_tree_root(logs_bloom) supporting CHUNKS\n" ++
  "  # 0 AND 1 variation. logs_bloom is ByteVector[256], merkleized\n" ++
  "  # over 8 32-byte chunks (3 levels). For NOW we read chunks 0 and\n" ++
  "  # 1 from input; chunks 2..7 stay at their default zero.\n" ++
  "  # Path leaf_4_chunk_0 -> node_0_1 -> node_0_3 -> node_0_7 (= leaf_4):\n" ++
  "  #   node_0_1   = sha256(chunk_0 || chunk_1)\n" ++
  "  #   node_0_3   = sha256(node_0_1 || ssz_zero_hash[1])\n" ++
  "  #   leaf_4     = sha256(node_0_3 || ssz_zero_hash[2])\n" ++
  "  # chunk_0 lives at SSZ_BASE + 16 + 44 + 116 = +176\n" ++
  "  # chunk_1 lives at SSZ_BASE + 16 + 44 + 148 = +208\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 176(s6); sd t2,  0(t1)\n" ++
  "  ld t2, 184(s6); sd t2,  8(t1)\n" ++
  "  ld t2, 192(s6); sd t2, 16(t1)\n" ++
  "  ld t2, 200(s6); sd t2, 24(t1)\n" ++
  "  ld t2, 208(s6); sd t2, 32(t1)\n" ++
  "  ld t2, 216(s6); sd t2, 40(t1)\n" ++
  "  ld t2, 224(s6); sd t2, 48(t1)\n" ++
  "  ld t2, 232(s6); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_leaf_4_logs_bloom_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_0_1 -> npr_leaf_4_logs_bloom_scratch\n" ++
  "  # Dynamic node_2_3 = sha256(chunk_2 || chunk_3)\n" ++
  "  # chunk_2 @ SSZ_BASE + 16 + 44 + 180 = +240\n" ++
  "  # chunk_3 @ SSZ_BASE + 16 + 44 + 212 = +272\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 240(s6); sd t2,  0(t1)\n" ++
  "  ld t2, 248(s6); sd t2,  8(t1)\n" ++
  "  ld t2, 256(s6); sd t2, 16(t1)\n" ++
  "  ld t2, 264(s6); sd t2, 24(t1)\n" ++
  "  ld t2, 272(s6); sd t2, 32(t1)\n" ++
  "  ld t2, 280(s6); sd t2, 40(t1)\n" ++
  "  ld t2, 288(s6); sd t2, 48(t1)\n" ++
  "  ld t2, 296(s6); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_logs_bloom_node_2_3_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_2_3 -> npr_logs_bloom_node_2_3_scratch\n" ++
  "  # node_0_3 = sha256(node_0_1 || node_2_3)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_leaf_4_logs_bloom_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_logs_bloom_node_2_3_scratch\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_leaf_4_logs_bloom_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_0_3 -> npr_leaf_4_logs_bloom_scratch\n" ++
  "  # leaf_4 (logs_bloom root) = sha256(node_0_3 || node_4_7), where\n" ++
  "  # node_4_7 covers logs_bloom chunks 4-7 (previously assumed zero via\n" ++
  "  # ssz_zero_hash[2] -- wrong for any block that emits logs). chunk_k\n" ++
  "  # lives at SSZ_BASE + 176 + 32*k: chunk4 @ +304 .. chunk7 @ +400.\n" ++
  "  # chunk_k @ s6+176+32*k is unaligned (s6 = 0x40000012), so copy the\n" ++
  "  # 64-byte (chunk4||chunk5) / (chunk6||chunk7) ranges byte-wise via\n" ++
  "  # sg_memcpy into the aligned npr_sha_input buffer (no misaligned LD).\n" ++
  "  #   node_4_5 = sha256(chunk4 || chunk5)\n" ++
  "  la a0, npr_sha_input        # dst (aligned)\n" ++
  "  addi a1, s6, 304            # src = chunk4 (unaligned)\n" ++
  "  li a2, 64\n" ++
  "  jal ra, sg_memcpy\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_lb_node_45_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_4_5 -> npr_lb_node_45_scratch\n" ++
  "  #   node_6_7 = sha256(chunk6 || chunk7)\n" ++
  "  la a0, npr_sha_input        # dst (aligned)\n" ++
  "  addi a1, s6, 368            # src = chunk6 (unaligned)\n" ++
  "  li a2, 64\n" ++
  "  jal ra, sg_memcpy\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_lb_node_67_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_6_7 -> npr_lb_node_67_scratch\n" ++
  "  #   node_4_7 = sha256(node_4_5 || node_6_7) -> npr_lb_node_45_scratch\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_lb_node_45_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_lb_node_67_scratch\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_lb_node_45_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_4_7 -> npr_lb_node_45_scratch\n" ++
  "  #   leaf_4 = sha256(node_0_3 || node_4_7)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_leaf_4_logs_bloom_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_lb_node_45_scratch\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_leaf_4_logs_bloom_scratch\n" ++
  "  jal ra, zkvm_sha256         # leaf_4 (logs_bloom root) -> npr_leaf_4_logs_bloom_scratch\n" ++
  "  # \n" ++
  "  # Dynamic node_4_5 = sha256(leaf_4 || leaf_5)\n" ++
  "  # where leaf_4 is the dynamic logs_bloom root (above) and\n" ++
  "  # leaf_5 = prev_randao (Bytes32 @ SSZ_BASE + 16 + 44 + 372 = +432).\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_leaf_4_logs_bloom_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  ld t2, 432(s6); sd t2, 32(t1)\n" ++
  "  ld t2, 440(s6); sd t2, 40(t1)\n" ++
  "  ld t2, 448(s6); sd t2, 48(t1)\n" ++
  "  ld t2, 456(s6); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_4_5_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_4_5 -> npr_node_4_5_scratch\n" ++
  "  # \n" ++
  "  # Dynamic node_10_11 = sha256(leaf_10=extra_data_root ||\n" ++
  "  #                            leaf_11=base_fee_per_gas):\n" ++
  "  #   leaf_10 = hash_tree_root(extra_data: ByteList[32]) where\n" ++
  "  #             extra_data is exec_payload@[extra_off .. tx_off].\n" ++
  "  #   leaf_11 = base_fee_per_gas (uint256, 32 bytes LE @\n" ++
  "  #             SSZ_BASE + 16 + 44 + 440 = +500)\n" ++
  "  addi a0, s6, 496           # &extra_data_offset (exec_payload+436)\n" ++
  "  jal ra, sg_load_u32le\n" ++
  "  mv s7, a0                  # s7 = extra_data_offset\n" ++
  "  addi a0, s6, 564           # &transactions_offset (exec_payload+504)\n" ++
  "  jal ra, sg_load_u32le\n" ++
  "  mv s8, a0                  # s8 = transactions_offset\n" ++
  "  addi t0, s6, 60            # exec_payload_addr\n" ++
  "  add a0, t0, s7             # extra_data_start\n" ++
  "  sub a1, s8, s7             # extra_data_len\n" ++
  "  li a2, 0                   # ByteList[32] => 2^0 chunks\n" ++
  "  la a3, npr_leaf_10_extra_data_scratch\n" ++
  "  jal ra, ssz_hash_tree_root_bytes\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_leaf_10_extra_data_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  ld t2, 500(s6); sd t2, 32(t1)\n" ++
  "  ld t2, 508(s6); sd t2, 40(t1)\n" ++
  "  ld t2, 516(s6); sd t2, 48(t1)\n" ++
  "  ld t2, 524(s6); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_10_11_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_10_11 -> npr_node_10_11_scratch\n" ++
  "  # \n" ++
  "  # Dynamic node_14_15 (supports leaf_15 = blob_gas_used):\n" ++
  "  #   node_14_15 = sha256(npr_leaf_14_withdrawals_root ||\n" ++
  "  #                       leaf_15=blob_gas_used)\n" ++
  "  # blob_gas_used (u64 LE @ SSZ_BASE + 16 + 44 + 512 = +572)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_dynamic_wd_root\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  ld t2, 572(s6); sd t2, 32(t1)\n" ++
  "  sd zero, 40(t1); sd zero, 48(t1); sd zero, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_14_15_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_14_15 -> npr_node_14_15_scratch\n" ++
  "  # Dynamic node_12_15 (supports leaf_12 = block_hash):\n" ++
  "  # node_12_13 = sha256(leaf_12=block_hash || leaf_13=transactions_root)\n" ++
  "  # leaf_13 (transactions default empty list root) is a static\n" ++
  "  # `npr_leaf_13_transactions_root` constant.\n" ++
  "  # block_hash (Bytes32 @ SSZ_BASE + 16 + 44 + 472 = +532)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 532(s6); sd t2,  0(t1)\n" ++
  "  ld t2, 540(s6); sd t2,  8(t1)\n" ++
  "  ld t2, 548(s6); sd t2, 16(t1)\n" ++
  "  ld t2, 556(s6); sd t2, 24(t1)\n" ++
  "  la t3, npr_dynamic_tx_root\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_12_13_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_12_13 -> npr_node_12_13_scratch\n" ++
  "  # node_12_15 = sha256(node_12_13 || npr_node_14_15_scratch)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_node_12_13_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_node_14_15_scratch\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_12_15_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_12_15 -> npr_node_12_15_scratch\n" ++
  "  # \n" ++
  "  # Dynamic node_8_15 path (supports leaf_8 = gas_used and\n" ++
  "  # leaf_9 = timestamp):\n" ++
  "  #   leaf_8 = gas_used  (u64 LE @ SSZ_BASE + 16 + 44 + 420 = +480)\n" ++
  "  #            || 24 bytes of zero padding\n" ++
  "  #   leaf_9 = timestamp (u64 LE @ SSZ_BASE + 16 + 44 + 428 = +488)\n" ++
  "  #            || 24 bytes of zero padding\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 480(s6)              # gas_used\n" ++
  "  sd t2,  0(t1)\n" ++
  "  sd zero,  8(t1); sd zero, 16(t1); sd zero, 24(t1)\n" ++
  "  ld t2, 488(s6)              # timestamp\n" ++
  "  sd t2, 32(t1)\n" ++
  "  sd zero, 40(t1); sd zero, 48(t1); sd zero, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_8_9 -> npr_sha_subtree\n" ++
  "  # node_8_11 = sha256(node_8_9 || npr_node_10_11_scratch)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_node_10_11_scratch\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_8_11 -> npr_sha_subtree\n" ++
  "  # node_8_15 = sha256(node_8_11 || npr_node_12_15_scratch) -> npr_node_8_15_scratch\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_node_12_15_scratch\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_8_15_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_8_15 -> npr_node_8_15_scratch\n" ++
  "  # leaf_6 = block_number (u64 LE @ SSZ_BASE + 16 + 44 + 404 = +464)\n" ++
  "  #          || 24 bytes of zero padding\n" ++
  "  # leaf_7 = gas_limit    (u64 LE @ SSZ_BASE + 16 + 44 + 412 = +472)\n" ++
  "  #          || 24 bytes of zero padding\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 464(s6)              # block_number\n" ++
  "  sd t2,  0(t1)\n" ++
  "  sd zero,  8(t1); sd zero, 16(t1); sd zero, 24(t1)\n" ++
  "  ld t2, 472(s6)              # gas_limit\n" ++
  "  sd t2, 32(t1)\n" ++
  "  sd zero, 40(t1); sd zero, 48(t1); sd zero, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_6_7 -> npr_sha_subtree\n" ++
  "  # node_4_7 = sha256(npr_node_4_5_scratch || node_6_7)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_node_4_5_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_4_7 -> npr_sha_subtree\n" ++
  "  # Dynamic node_0_3 path (supports leaf_0 = parent_hash and\n" ++
  "  # leaf_1 = fee_recipient):\n" ++
  "  #   leaf_0 = parent_hash    (Bytes32 @ SSZ_BASE + 16 + 44 + 0 = +60)\n" ++
  "  #   leaf_1 = fee_recipient  (ByteVector[20] @ SSZ_BASE + 16 + 44 + 32\n" ++
  "  #            = +92), packed into 32 bytes via 20 bytes from input\n" ++
  "  #            + 12 zero padding (SSZ ByteVector[20].hash_tree_root).\n" ++
  "  # node_0_1 = sha256(leaf_0 || leaf_1) -> npr_node_0_3_scratch (temp)\n" ++
  "  # We use npr_node_0_3_scratch as both temp (for node_0_1) and final\n" ++
  "  # (for node_0_3) since sha256 reads input then writes output.\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2,  60(s6); sd t2,  0(t1)\n" ++
  "  ld t2,  68(s6); sd t2,  8(t1)\n" ++
  "  ld t2,  76(s6); sd t2, 16(t1)\n" ++
  "  ld t2,  84(s6); sd t2, 24(t1)\n" ++
  "  ld t2,  92(s6); sd t2, 32(t1)\n" ++
  "  ld t2, 100(s6); sd t2, 40(t1)\n" ++
  "  lwu t2, 108(s6); sd t2, 48(t1)\n" ++
  "  sd zero, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_0_3_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_0_1 -> npr_node_0_3_scratch\n" ++
  "  # node_2_3 = sha256(leaf_2=state_root || leaf_3=receipts_root):\n" ++
  "  #   state_root    (Bytes32 @ SSZ_BASE + 16 + 44 + 52  = +112)\n" ++
  "  #   receipts_root (Bytes32 @ SSZ_BASE + 16 + 44 + 84  = +144)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 112(s6); sd t2,  0(t1)\n" ++
  "  ld t2, 120(s6); sd t2,  8(t1)\n" ++
  "  ld t2, 128(s6); sd t2, 16(t1)\n" ++
  "  ld t2, 136(s6); sd t2, 24(t1)\n" ++
  "  ld t2, 144(s6); sd t2, 32(t1)\n" ++
  "  ld t2, 152(s6); sd t2, 40(t1)\n" ++
  "  ld t2, 160(s6); sd t2, 48(t1)\n" ++
  "  ld t2, 168(s6); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_2_3_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_2_3 -> npr_node_2_3_scratch\n" ++
  "  # node_0_3 = sha256(node_0_1 || node_2_3)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_node_0_3_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_node_2_3_scratch\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_0_3_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_0_3 -> npr_node_0_3_scratch\n" ++
  "  # node_0_7 = sha256(npr_node_0_3_scratch || node_4_7)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_node_0_3_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_0_7 -> npr_sha_subtree\n" ++
  "  # node_0_15 = sha256(node_0_7 || npr_node_8_15) -> npr_node_0_15_scratch\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_node_8_15_scratch\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_0_15_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_0_15 -> npr_node_0_15_scratch\n" ++
  "  # \n" ++
  "  # ===== exec_payload merkle path (leaves 16-31) =====\n" ++
  "  # node_16_17 = sha256(leaf_16 || leaf_17) where\n" ++
  "  #   leaf_16 = excess_blob_gas (u64 LE @ SSZ_BASE + 16 + 44 + 520\n" ++
  "  #             = +580) || 24 bytes zero padding\n" ++
  "  #   leaf_17 = npr_leaf_17_bal_root (block_access_list_root for\n" ++
  "  #             the empty/default ByteList -- constant)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 580(s6)              # excess_blob_gas\n" ++
  "  sd t2,  0(t1)\n" ++
  "  sd zero,  8(t1); sd zero, 16(t1); sd zero, 24(t1)\n" ++
  "  la t3, npr_dynamic_bal_root\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_16_17_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_16_17 -> npr_node_16_17_scratch\n" ++
  "  # leaf_18 = slot_number (u64 LE at SSZ_BASE + 16 + 44 + 532 = +592)\n" ++
  "  #          || 24 bytes of zero padding\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 592(s6)              # slot_number\n" ++
  "  sd t2,  0(t1)\n" ++
  "  sd zero,  8(t1); sd zero, 16(t1); sd zero, 24(t1)\n" ++
  "  # bytes [32..64) = ssz_zero_hash[0] = leaf_19\n" ++
  "  sd zero, 32(t1); sd zero, 40(t1); sd zero, 48(t1); sd zero, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_18_19 -> npr_sha_subtree\n" ++
  "  # node_16_19 = sha256(node_16_17_scratch || node_18_19)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_node_16_17_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_16_19 -> npr_sha_subtree\n" ++
  "  # node_16_23 = sha256(node_16_19 || ssz_zero_hash[2])\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, ssz_zero_hashes\n" ++
  "  addi t3, t3, 64             # ssz_zero_hash[2]\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_16_23 -> npr_sha_subtree\n" ++
  "  # node_16_31 = sha256(node_16_23 || ssz_zero_hash[3])\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, ssz_zero_hashes\n" ++
  "  addi t3, t3, 96             # ssz_zero_hash[3]\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # node_16_31 -> npr_sha_subtree\n" ++
  "  # exec_payload_root = sha256(node_0_15 || node_16_31)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_node_0_15_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_exec_payload_root\n" ++
  "  jal ra, zkvm_sha256         # exec_payload_root -> npr_exec_payload_root\n" ++
  "  # \n" ++
  "  # ===== NPR top-level merkle =====\n" ++
  "  # left_subtree = sha256(exec_payload_root || versioned_hashes_root)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_exec_payload_root\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_versioned_hashes_dyn\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_left_subtree_scratch\n" ++
  "  jal ra, zkvm_sha256         # left_subtree -> npr_left_subtree_scratch\n" ++
  "  # right_subtree = sha256(parent_beacon_block_root || npr_exec_requests_root)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  ld t2, 24(s6); sd t2,  0(t1)\n" ++
  "  ld t2, 32(s6); sd t2,  8(t1)\n" ++
  "  ld t2, 40(s6); sd t2, 16(t1)\n" ++
  "  ld t2, 48(s6); sd t2, 24(t1)\n" ++
  "  la t3, npr_exec_requests_dyn\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_sha_subtree\n" ++
  "  jal ra, zkvm_sha256         # right_subtree -> npr_sha_subtree\n" ++
  "  # root = sha256(left_subtree || right_subtree) -> OUTPUT_ADDR\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, npr_left_subtree_scratch\n" ++
  "  ld t2,  0(t3); sd t2,  0(t1)\n" ++
  "  ld t2,  8(t3); sd t2,  8(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 24(t1)\n" ++
  "  la t3, npr_sha_subtree\n" ++
  "  ld t2,  0(t3); sd t2, 32(t1)\n" ++
  "  ld t2,  8(t3); sd t2, 40(t1)\n" ++
  "  ld t2, 16(t3); sd t2, 48(t1)\n" ++
  "  ld t2, 24(t3); sd t2, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; li a2, 0xa0010000\n" ++
  "  jal ra, zkvm_sha256         # root -> OUTPUT_ADDR\n" ++
  "  # ===== Step-2 successful_validation: sound full state-transition verdict =====\n" ++
  "  # (header-validate + withdrawals/EIP-2935/EIP-4788 state recompute ==\n" ++
  "  #  payload.state_root + EIP-7928 BAL gas-limit rule). NPR root is already at\n" ++
  "  #  OUTPUT[0..32); stamp the verdict bit at OUTPUT[32]. Conservative: any\n" ++
  "  #  unhandled case -> 0 (never a false positive).\n" ++
  "  jal ra, stateless_verdict_v2\n" ++
  "  li t0, 0xa0010000; sb a0, 32(t0)\n" ++
  "  # Restore zisk's trap vector before the final Linux-93 halt ecall.\n" ++
  "  li t0, 0xa0009828          # zisk MTVEC memory slot\n" ++
  "  la t1, npr_saved_mtvec\n" ++
  "  ld t1, 0(t1)\n" ++
  "  sd t1, 0(t0)\n" ++
  "  j .Lsg_done\n" ++
  zkvmSha256Function ++ "\n" ++
  -- SSZ merkleization helpers for the dynamic transactions_root /
  -- block_access_list_root (zkvm_sha256 already emitted just above, so it
  -- is NOT re-included here -- doing so would duplicate the label).
  sszPackBytesFunction ++ "\n" ++
  sszMerkleizePow2Function ++ "\n" ++
  sszMerkleizeFunction ++ "\n" ++
  sszHashTreeRootBytesFunction ++ "\n" ++
  sszHashTreeRootListByteListFunction ++ "\n" ++
  -- Alignment-safe little-endian u32 load: a0 = addr -> a0 = u32 LE.
  -- Reads byte-wise (LBU) so the source may be unaligned (SSZ base is
  -- 0x40000012). Leaf; clobbers t0,t1,a0; preserves all s-registers and ra.
  "sg_load_u32le:\n" ++
  "  lbu t0, 0(a0)\n" ++
  "  lbu t1, 1(a0); slli t1, t1, 8;  or t0, t0, t1\n" ++
  "  lbu t1, 2(a0); slli t1, t1, 16; or t0, t0, t1\n" ++
  "  lbu t1, 3(a0); slli t1, t1, 24; or t0, t0, t1\n" ++
  "  mv a0, t0\n" ++
  "  ret\n" ++
  -- Alignment-safe byte copy: a0 = dst, a1 = src, a2 = len. Byte-wise
  -- (LBU/SB) so src/dst may be unaligned. Leaf; clobbers t0,a0,a1,a2;
  -- preserves all s-registers and ra.
  "sg_memcpy:\n" ++
  ".Lsgmc_loop:\n" ++
  "  beqz a2, .Lsgmc_done\n" ++
  "  lbu t0, 0(a1)\n" ++
  "  sb  t0, 0(a0)\n" ++
  "  addi a0, a0, 1\n" ++
  "  addi a1, a1, 1\n" ++
  "  addi a2, a2, -1\n" ++
  "  j .Lsgmc_loop\n" ++
  ".Lsgmc_done:\n" ++
  "  ret\n" ++
  -- hash_tree_root(List[SszWithdrawal, 16]):  a0=section ptr (may be
  -- unaligned), a1=section_len, a2=32-byte out. Each withdrawal is a
  -- fixed 44-byte container; its root = merkleize([index|pad,
  -- validator_index|pad, address|pad, amount|pad], limit_log2=2). The
  -- list root = merkleize(child_roots, limit_log2=4) then
  -- mix_in_length(N). N=0 yields the empty-list constant (no regression).
  -- All reads byte-wise (sg_memcpy) -- alignment-safe. Preserves s0-s6+ra.
  "ssz_htr_withdrawals:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                  # s0 = section\n" ++
  "  mv s3, a2                  # s3 = out\n" ++
  "  li t0, 44\n" ++
  "  divu s1, a1, t0            # s1 = N = section_len / 44\n" ++
  "  li s2, 0                   # s2 = i\n" ++
  "  la s4, wd_child_roots      # s4 = &child_roots[i]\n" ++
  ".Lwd_loop:\n" ++
  "  beq s2, s1, .Lwd_done\n" ++
  "  li t0, 44; mul t0, s2, t0; add s5, s0, t0   # s5 = w = section + i*44\n" ++
  "  # node_01 = sha256(index|pad24 || validator_index|pad24)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  sd zero,0(t1); sd zero,8(t1); sd zero,16(t1); sd zero,24(t1)\n" ++
  "  sd zero,32(t1); sd zero,40(t1); sd zero,48(t1); sd zero,56(t1)\n" ++
  "  la a0, npr_sha_input; mv a1, s5; li a2, 8; jal ra, sg_memcpy\n" ++
  "  la a0, npr_sha_input; addi a0, a0, 32; addi a1, s5, 8; li a2, 8; jal ra, sg_memcpy\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, wd_node_a; jal ra, zkvm_sha256\n" ++
  "  # node_23 = sha256(address|pad12 || amount|pad24)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  sd zero,0(t1); sd zero,8(t1); sd zero,16(t1); sd zero,24(t1)\n" ++
  "  sd zero,32(t1); sd zero,40(t1); sd zero,48(t1); sd zero,56(t1)\n" ++
  "  la a0, npr_sha_input; addi a1, s5, 16; li a2, 20; jal ra, sg_memcpy\n" ++
  "  la a0, npr_sha_input; addi a0, a0, 32; addi a1, s5, 36; li a2, 8; jal ra, sg_memcpy\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, wd_node_b; jal ra, zkvm_sha256\n" ++
  "  # wroot = sha256(node_01 || node_23) -> child_roots[i]\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, wd_node_a\n" ++
  "  ld t2,0(t3); sd t2,0(t1); ld t2,8(t3); sd t2,8(t1); ld t2,16(t3); sd t2,16(t1); ld t2,24(t3); sd t2,24(t1)\n" ++
  "  la t3, wd_node_b\n" ++
  "  ld t2,0(t3); sd t2,32(t1); ld t2,8(t3); sd t2,40(t1); ld t2,16(t3); sd t2,48(t1); ld t2,24(t3); sd t2,56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; mv a2, s4; jal ra, zkvm_sha256\n" ++
  "  addi s4, s4, 32\n" ++
  "  addi s2, s2, 1\n" ++
  "  j .Lwd_loop\n" ++
  ".Lwd_done:\n" ++
  "  la a0, wd_child_roots; mv a1, s1; li a2, 4; la a3, wd_partial; jal ra, ssz_merkleize\n" ++
  "  # mix_in_length: sha256(wd_partial || u256_le(N)) -> out\n" ++
  "  la t1, npr_sha_input\n" ++
  "  la t3, wd_partial\n" ++
  "  ld t2,0(t3); sd t2,0(t1); ld t2,8(t3); sd t2,8(t1); ld t2,16(t3); sd t2,16(t1); ld t2,24(t3); sd t2,24(t1)\n" ++
  "  sd s1, 32(t1); sd zero,40(t1); sd zero,48(t1); sd zero,56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; mv a2, s3; jal ra, zkvm_sha256\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n" ++
  -- ===== execution_requests hash_tree_root (SszExecutionRequests) =====
  -- Container of 3 List[Container] fields {deposits, withdrawals,
  -- consolidations}; root = merkleize([htr(each list)], limit_log2=2).
  -- Built from reusable pieces (all alignment-safe via sg_memcpy; all
  -- save/restore the s-registers they use, and the nested ssz_merkleize
  -- saves s0-s6, so deep nesting is register-safe). Verified byte-for-byte
  -- against remerkleable for deposits / withdrawal-requests /
  -- consolidations / mixed fixtures.
  --
  -- htr(ByteVector[48]) = sha256(b[0:32] || b[32:48]|pad16).
  "sg_htr_bv48:\n" ++                       -- a0=src, a1=out
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  "  la t0, bv_buf; sd zero, 48(t0); sd zero, 56(t0)\n" ++
  "  la a0, bv_buf; mv a1, s0; li a2, 48; jal ra, sg_memcpy\n" ++
  "  la a0, bv_buf; li a1, 64; mv a2, s1; jal ra, zkvm_sha256\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); addi sp, sp, 32; ret\n" ++
  -- htr(ByteVector[96]) = merkleize([b0,b1,b2], limit_log2=2).
  "sg_htr_bv96:\n" ++                       -- a0=src, a1=out
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  "  la a0, bv_buf; mv a1, s0; li a2, 96; jal ra, sg_memcpy\n" ++
  "  la a0, bv_buf; li a1, 3; li a2, 2; mv a3, s1; jal ra, ssz_merkleize\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); addi sp, sp, 32; ret\n" ++
  -- htr(SszDepositRequest): 192B {pubkey BV48, wc Bytes32, amount u64,\n" ++
  -- sig BV96, index u64}; 5 leaves merkleized at limit_log2=3.
  "sg_htr_deposit:\n" ++                     -- a0=w(192), a1=out
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  "  mv a0, s0; la a1, er_leaf_buf; jal ra, sg_htr_bv48\n" ++             -- leaf0 pubkey
  "  la a0, er_leaf_buf; addi a0, a0, 32; addi a1, s0, 48; li a2, 32; jal ra, sg_memcpy\n" ++  -- leaf1 wc
  "  la t0, er_leaf_buf; sd zero, 64(t0); sd zero, 72(t0); sd zero, 80(t0); sd zero, 88(t0)\n" ++
  "  la a0, er_leaf_buf; addi a0, a0, 64; addi a1, s0, 80; li a2, 8; jal ra, sg_memcpy\n" ++   -- leaf2 amount
  "  addi a0, s0, 88; la a1, er_leaf_buf; addi a1, a1, 96; jal ra, sg_htr_bv96\n" ++           -- leaf3 sig
  "  la t0, er_leaf_buf; sd zero, 128(t0); sd zero, 136(t0); sd zero, 144(t0); sd zero, 152(t0)\n" ++
  "  la a0, er_leaf_buf; addi a0, a0, 128; addi a1, s0, 184; li a2, 8; jal ra, sg_memcpy\n" ++ -- leaf4 index
  "  la a0, er_leaf_buf; li a1, 5; li a2, 3; mv a3, s1; jal ra, ssz_merkleize\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); addi sp, sp, 32; ret\n" ++
  -- htr(SszWithdrawalRequest): 76B {src_addr BV20, validator_pubkey BV48,\n" ++
  -- amount u64}; 3 leaves at limit_log2=2.
  "sg_htr_wr:\n" ++                          -- a0=w(76), a1=out
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  "  la t0, er_leaf_buf; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la a0, er_leaf_buf; mv a1, s0; li a2, 20; jal ra, sg_memcpy\n" ++                          -- leaf0 src_addr
  "  addi a0, s0, 20; la a1, er_leaf_buf; addi a1, a1, 32; jal ra, sg_htr_bv48\n" ++            -- leaf1 validator_pubkey
  "  la t0, er_leaf_buf; sd zero, 64(t0); sd zero, 72(t0); sd zero, 80(t0); sd zero, 88(t0)\n" ++
  "  la a0, er_leaf_buf; addi a0, a0, 64; addi a1, s0, 68; li a2, 8; jal ra, sg_memcpy\n" ++    -- leaf2 amount
  "  la a0, er_leaf_buf; li a1, 3; li a2, 2; mv a3, s1; jal ra, ssz_merkleize\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); addi sp, sp, 32; ret\n" ++
  -- htr(SszConsolidationRequest): 116B {src_addr BV20, src_pubkey BV48,\n" ++
  -- target_pubkey BV48}; 3 leaves at limit_log2=2.
  "sg_htr_cr:\n" ++                          -- a0=w(116), a1=out
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  "  la t0, er_leaf_buf; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la a0, er_leaf_buf; mv a1, s0; li a2, 20; jal ra, sg_memcpy\n" ++                          -- leaf0 src_addr
  "  addi a0, s0, 20; la a1, er_leaf_buf; addi a1, a1, 32; jal ra, sg_htr_bv48\n" ++            -- leaf1 src_pubkey
  "  addi a0, s0, 68; la a1, er_leaf_buf; addi a1, a1, 64; jal ra, sg_htr_bv48\n" ++            -- leaf2 target_pubkey
  "  la a0, er_leaf_buf; li a1, 3; li a2, 2; mv a3, s1; jal ra, ssz_merkleize\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); addi sp, sp, 32; ret\n" ++
  -- hash_tree_root(List[FixedContainer, cap]) via a per-element htr fn ptr.
  --   a0=body, a1=section_len, a2=elem_size, a3=elem_htr_fn, a4=limit_log2,
  --   a5=32-byte out. root = merkleize(child_roots, limit) + mix_in_length(N).
  "sg_htr_clist:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s3, a2; mv s4, a3; mv s6, a4; mv s5, a5\n" ++
  "  divu s1, a1, s3            # N = section_len / elem_size\n" ++
  "  li s2, 0\n" ++
  ".Lcl_loop:\n" ++
  "  beq s2, s1, .Lcl_done\n" ++
  "  mul t0, s2, s3; add a0, s0, t0          # elem = body + i*esz\n" ++
  "  la a1, er_child_roots; slli t0, s2, 5; add a1, a1, t0   # &child_roots[i]\n" ++
  "  jalr ra, s4, 0                          # elem_htr(elem, slot)\n" ++
  "  addi s2, s2, 1; j .Lcl_loop\n" ++
  ".Lcl_done:\n" ++
  "  la a0, er_child_roots; mv a1, s1; mv a2, s6; la a3, er_clist_partial; jal ra, ssz_merkleize\n" ++
  "  la t1, npr_sha_input; la t3, er_clist_partial\n" ++
  "  ld t2,0(t3); sd t2,0(t1); ld t2,8(t3); sd t2,8(t1); ld t2,16(t3); sd t2,16(t1); ld t2,24(t3); sd t2,24(t1)\n" ++
  "  sd s1, 32(t1); sd zero,40(t1); sd zero,48(t1); sd zero,56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; mv a2, s5; jal ra, zkvm_sha256\n" ++
  "  ld ra,0(sp); ld s0,8(sp); ld s1,16(sp); ld s2,24(sp)\n" ++
  "  ld s3,32(sp); ld s4,40(sp); ld s5,48(sp); ld s6,56(sp); addi sp,sp,64; ret\n" ++
  -- hash_tree_root(SszExecutionRequests): a0=section, a1=section_len, a2=out.
  -- 3 u32 offsets (deposits/withdrawals/consolidations) at section+0/+4/+8;
  -- each list body is fixed-size containers (no inner offset table).
  "ssz_htr_execution_requests:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s2, a1; mv s1, a2\n" ++
  "  mv a0, s0; jal ra, sg_load_u32le; mv s3, a0          # deposits offset\n" ++
  "  addi a0, s0, 4; jal ra, sg_load_u32le; mv s4, a0     # withdrawals offset\n" ++
  "  addi a0, s0, 8; jal ra, sg_load_u32le; mv s5, a0     # consolidations offset\n" ++
  "  add a0, s0, s3; sub a1, s4, s3; li a2, 192; la a3, sg_htr_deposit; li a4, 13; la a5, er_outer_buf; jal ra, sg_htr_clist\n" ++
  "  add a0, s0, s4; sub a1, s5, s4; li a2, 76;  la a3, sg_htr_wr;      li a4, 4;  la a5, er_outer_buf; addi a5, a5, 32; jal ra, sg_htr_clist\n" ++
  "  add a0, s0, s5; sub a1, s2, s5; li a2, 116; la a3, sg_htr_cr;      li a4, 1;  la a5, er_outer_buf; addi a5, a5, 64; jal ra, sg_htr_clist\n" ++
  "  la a0, er_outer_buf; li a1, 3; li a2, 2; mv a3, s1; jal ra, ssz_merkleize\n" ++
  "  ld ra,0(sp); ld s0,8(sp); ld s1,16(sp); ld s2,24(sp)\n" ++
  "  ld s3,32(sp); ld s4,40(sp); ld s5,48(sp); addi sp,sp,64; ret\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainValidatePostMergeFullFunction ++ "\n" ++
  chainValidateExtraDataLengthFunction ++ "\n" ++
  chainValidateGasUsedUnderLimitFunction ++ "\n" ++
  chainValidateBlobGasUsedMultipleFunction ++ "\n" ++
  chainValidateBlobGasUsedUnderMaxFunction ++ "\n" ++
  chainValidateIncreasingTimestampsFunction ++ "\n" ++
  chainValidateConsecutiveNumbersFunction ++ "\n" ++
  -- Step-2 verdict closure (omits rlp_list_nth_item / rlp_field_to_u64 — already
  -- defined above in this epilogue — to avoid duplicate labels):
  statelessVerdictV2GuestClosure ++ "\n" ++
  ".Lsg_done:"

end EvmAsm.Codegen
