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
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm
import EvmAsm.Codegen.Programs.SgMemcpySAsm
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Ssz
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.BlockVerdict
import EvmAsm.Codegen.Programs.BlockVerdictV2
import EvmAsm.Codegen.Programs.HeaderChain
import EvmAsm.Stateless.SSZ.Encode.Program

namespace EvmAsm.Codegen

/-! ## stateless_guest input decoder

    The body of `stateless_guest` is intentionally only the core structural
    slot. The image-level entry therefore decodes the host-framed,
    schema-prefixed SSZ payload before any validator reads its derived
    registers. This is the executable counterpart of
    `SpecRef.deserialize_stateless_input`: schema id, canonical outer offsets,
    section bounds, the fixed chain-config header, the public-key list shape,
    and the witness-header list framing are checked before the existing
    verifier pipeline is entered. A failure jumps directly to the exact
    `_default_failed_stateless_output` byte copy below.

    On success the decoder leaves the established pipeline interface:
    `x10 = chain_id`, `x11 = 0` (the verifier writes the success byte),
    `x14 = headers section length`, `x16 = header count`, `x17 = SSZ base`,
    and `x21 = headers data pointer`. The serializer is emitted immediately
    after this decoder, so the chain-config echo is written before the
    verifier can clobber temporary argument registers.
-/
def statelessGuestInputDecode : String :=
  "  # execution-specs deserialize_stateless_input: host length includes the 2-byte schema id\n" ++
  "  li sp, 0xa0050000                 # SSZ framing validators use a private frame\n" ++
  "  li t0, 0x40000008; ld t6, 0(t0)\n" ++
  "  li t5, 2; bltu t6, t5, .Lsg_default_failed_output\n" ++
  "  li t1, 0x40000000; addi t1, t1, 16\n" ++
  "  lbu t2, 0(t1); lbu t3, 1(t1)\n" ++
  "  li t4, 0x15; bne t2, t4, .Lsg_default_failed_output\n" ++
  "  li t4, 1; bne t3, t4, .Lsg_default_failed_output\n" ++
  "  addi t6, t6, -2; li t1, 0x40000012\n" ++
  "  # SszStatelessInput fixed section: four offsets, 16 bytes.\n" ++
  "  lbu t2, 0(t1); lbu t3, 1(t1); slli t3, t3, 8; or t2, t2, t3\n" ++
  "  lbu t3, 2(t1); slli t3, t3, 16; or t2, t2, t3; lbu t3, 3(t1); slli t3, t3, 24; or t2, t2, t3\n" ++
  "  li t4, 16; bne t2, t4, .Lsg_default_failed_output; bgtu t2, t6, .Lsg_default_failed_output\n" ++
  "  lbu t3, 4(t1); lbu t4, 5(t1); slli t4, t4, 8; or t3, t3, t4\n" ++
  "  lbu t4, 6(t1); slli t4, t4, 16; or t3, t3, t4; lbu t4, 7(t1); slli t4, t4, 24; or t3, t3, t4\n" ++
  "  bltu t3, t2, .Lsg_default_failed_output; bgtu t3, t6, .Lsg_default_failed_output\n" ++
  "  add x22, t1, t3; mv t2, t3\n" ++
  "  lbu t3, 8(t1); lbu t4, 9(t1); slli t4, t4, 8; or t3, t3, t4\n" ++
  "  lbu t4, 10(t1); slli t4, t4, 16; or t3, t3, t4; lbu t4, 11(t1); slli t4, t4, 24; or t3, t3, t4\n" ++
  "  bltu t3, t2, .Lsg_default_failed_output; bgtu t3, t6, .Lsg_default_failed_output\n" ++
  "  add x23, t1, t3; mv x20, x23; mv t2, t3\n" ++
  "  lbu t3, 12(t1); lbu t4, 13(t1); slli t4, t4, 8; or t3, t3, t4\n" ++
  "  lbu t4, 14(t1); slli t4, t4, 16; or t3, t3, t4; lbu t4, 15(t1); slli t4, t4, 24; or t3, t3, t4\n" ++
  "  bltu t3, t2, .Lsg_default_failed_output; bgtu t3, t6, .Lsg_default_failed_output\n" ++
  "  li t4, 12; sub t5, t3, t2; bltu t5, t4, .Lsg_default_failed_output\n" ++
  "  sub t5, x23, x22; bltu t5, t4, .Lsg_default_failed_output\n" ++
  "  sub t5, x22, t1; li t4, 16; bltu t5, t4, .Lsg_default_failed_output\n" ++
  "  # Keep the outer framing values across the nested SSZ checks.\n" ++
  "  mv x17, t1                         # SSZ_BASE\n" ++
  "  mv x16, t3                         # public_keys offset\n" ++
  "  sub x18, t6, t3                    # public_keys byte length\n" ++
  "  sub x15, t3, t2                    # chain_config byte length\n" ++
  "  # The generic SSZ decoder rejects malformed nested containers and lists\n" ++
  "  # before the verifier sees any derived field.\n" ++
  "  mv a0, x17; jal ra, sg_load_u32le; add a0, x17, a0\n" ++
  "  sub a1, x22, a0; li a2, 0; jal ra, sg_validate_npr\n" ++
  "  bnez a0, .Lsg_default_failed_output\n" ++
  "  sub x14, x23, x22\n" ++
  "  mv a0, x22; mv a1, x14; jal ra, sg_validate_witness\n" ++
  "  bnez a0, .Lsg_default_failed_output\n" ++
  "  mv a0, x20; mv a1, x15; jal ra, sg_validate_chain_config\n" ++
  "  bnez a0, .Lsg_default_failed_output\n" ++
  "  add a0, x17, x16; mv a1, x18; li a2, 65; li a3, 32768\n" ++
  "  jal ra, sg_validate_fixed_list\n" ++
  "  bnez a0, .Lsg_default_failed_output\n" ++
  "  # Decode chain_config.chain_id (u64 LE) without an unaligned LD.\n" ++
  "  lbu x10, 0(x20); lbu t5, 1(x20); slli t5, t5, 8; or x10, x10, t5\n" ++
  "  lbu t5, 2(x20); slli t5, t5, 16; or x10, x10, t5; lbu t5, 3(x20); slli t5, t5, 24; or x10, x10, t5\n" ++
  "  lbu t5, 4(x20); slli t5, t5, 32; or x10, x10, t5; lbu t5, 5(x20); slli t5, t5, 40; or x10, x10, t5\n" ++
  "  lbu t5, 6(x20); slli t5, t5, 48; or x10, x10, t5; lbu t5, 7(x20); slli t5, t5, 56; or x10, x10, t5\n" ++
  "  # Witness section: three variable lists, then the headers list.\n" ++
  "  sub x14, x23, x22\n" ++
  "  lbu x21, 8(x22); lbu t5, 9(x22); slli t5, t5, 8; or x21, x21, t5\n" ++
  "  lbu t5, 10(x22); slli t5, t5, 16; or x21, x21, t5; lbu t5, 11(x22); slli t5, t5, 24; or x21, x21, t5\n" ++
  "  li t4, 12; bltu x21, t4, .Lsg_default_failed_output; bgtu x21, x14, .Lsg_default_failed_output\n" ++
  "  sub x14, x14, x21; add x21, x22, x21; li x11, 0\n" ++
  "  beqz x14, .Lsg_decode_no_headers\n" ++
  "  lbu x16, 0(x21); lbu t5, 1(x21); slli t5, t5, 8; or x16, x16, t5\n" ++
  "  lbu t5, 2(x21); slli t5, t5, 16; or x16, x16, t5; lbu t5, 3(x21); slli t5, t5, 24; or x16, x16, t5\n" ++
  "  li t4, 4; remu t5, x16, t4; bnez t5, .Lsg_default_failed_output; beqz x16, .Lsg_default_failed_output\n" ++
  "  bgtu x16, x14, .Lsg_default_failed_output; srli x16, x16, 2\n" ++
  "  li t4, 256; bgtu x16, t4, .Lsg_default_failed_output\n" ++
  "  j .Lsg_decode_done\n" ++
  ".Lsg_decode_no_headers:\n" ++
  "  li x16, 0\n" ++
  ".Lsg_decode_done:\n"

/-! ## stateless_guest header-validator pipeline (integration PR)

    Inserted after the entry decoder and output serializer, before the
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
  "  # 9lw0m: spec validate_headers asserts len(encoded_headers) <= 256. Enforce it\n" ++
  "  # here, BEFORE building sg_header_lengths (a fixed 256*8 = 2048-byte buffer):\n" ++
  "  # this both matches the spec (a >256-header witness is invalid -> reject, closing\n" ++
  "  # a false-accept) and prevents the .Lsg_bl loop from overflowing sg_header_lengths.\n" ++
  "  li t0, 256\n" ++
  "  bgtu s2, t0, .Lsg_fail_toomany\n" ++
  "  # Build sg_header_lengths[N]: convert N u32 inner-offset deltas\n" ++
  "  # to N u64 absolute lengths.\n" ++
  "  mv t0, s3                   # t0 = offsets cursor (section_ptr)\n" ++
  "  la t1, sg_header_lengths    # t1 = lengths-out cursor\n" ++
  "  mv t2, s2                   # t2 = i (counts down from N)\n" ++
  ".Lsg_bl:\n" ++
  "  beqz t2, .Lsg_bl_done\n" ++
  "  # #12057 u32 LE t0+0\n  lbu t3, 0(t0)\n  lbu t4, 1(t0); slli t4, t4, 8; or t3, t3, t4\n  lbu t4, 2(t0); slli t4, t4, 16; or t3, t3, t4\n  lbu t4, 3(t0); slli t4, t4, 24; or t3, t3, t4\n" ++
  "  addi t4, t2, -1\n" ++
  "  beqz t4, .Lsg_bl_last       # if last header, end = section_len\n" ++
  "  # #12057 u32 LE t0+4\n  lbu t5, 4(t0)\n  lbu t4, 5(t0); slli t4, t4, 8; or t5, t5, t4\n  lbu t4, 6(t0); slli t4, t4, 16; or t5, t5, t4\n  lbu t4, 7(t0); slli t4, t4, 24; or t5, t5, t4\n" ++
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
  "  # 9lw0m: spec validate_headers parent_hash contiguity (stateless.py:266-277).\n" ++
  "  # For i in 1..N-1, child.parent_hash == keccak256(encoded_header[i-1]); reject a\n" ++
  "  # non-contiguous witness chain. This is the spec's ONLY header-chain check and\n" ++
  "  # was previously omitted (a false-accept: a witness with a broken keccak link but\n" ++
  "  # plausible fields would pass). N<2 is vacuously contiguous. s6-s9 hold the loop\n" ++
  "  # state and survive validate_parent_hash_link (it saves s0-s4 only).\n" ++
  "  li t0, 2\n" ++
  "  bltu s2, t0, .Lsg_contig_done\n" ++
  "  la t0, sg_header_lengths\n" ++
  "  ld s6, 0(t0)                # prev_len = lengths[0]\n" ++
  "  mv s7, s5                   # prev_ptr = header[0]\n" ++
  "  add s8, s5, s6              # cur_ptr = header[1]\n" ++
  "  li s9, 1                    # i = 1\n" ++
  ".Lsg_contig_loop:\n" ++
  "  beq s9, s2, .Lsg_contig_done\n" ++
  "  slli t0, s9, 3; la t1, sg_header_lengths; add t1, t1, t0; ld a3, 0(t1)  # cur_len\n" ++
  "  mv a0, s7; mv a1, s6; mv a2, s8; la a4, sg_contig_valid\n" ++
  "  jal ra, validate_parent_hash_link\n" ++
  "  bnez a0, .Lsg_fail_contig   # parse/size failure => reject\n" ++
  "  la t0, sg_contig_valid; ld t0, 0(t0); beqz t0, .Lsg_fail_contig\n" ++
  "  slli t0, s9, 3; la t1, sg_header_lengths; add t1, t1, t0; ld t2, 0(t1)  # cur_len (a3 clobbered)\n" ++
  "  mv s7, s8; mv s6, t2; add s8, s8, t2; addi s9, s9, 1\n" ++
  "  j .Lsg_contig_loop\n" ++
  ".Lsg_contig_done:\n" ++
  "  # 9lw0m deviation B: the spec's validate_headers (amsterdam stateless.py:266-277)\n" ++
  "  # field-validates the witness ancestor headers ONLY for parent_hash contiguity\n" ++
  "  # (checked above) + count<=256 (checked at entry). It does NOT re-validate the\n" ++
  "  # ancestors' post-merge fields / extra_data / gas_used / blob_gas / timestamps /\n" ++
  "  # numbers -- those are historical blocks the stateless client trusts, and the\n" ++
  "  # block-under-test's own header is validated separately in the verdict path. The\n" ++
  "  # 7 per-witness-header validators here were a spec-absent over-check (a latent\n" ++
  "  # false-reject vector), so they are removed to match the spec. (RLP-decodability\n" ++
  "  # of each ancestor is still enforced: the contiguity check parses every header to\n" ++
  "  # extract parent_hash.)\n" ++
  ".Lsg_all_pass:\n" ++
  "  # All validators that ran passed (or N=0 fast-path). The entry decoder\n" ++
  "  # has already established the schema and SSZ framing, and the serializer\n" ++
  "  # has recorded the decoded chain id and the validator's success byte.\n" ++
  "  # The existing verifier machinery owns the remaining payload semantics;\n" ++
  "  # this stage only preserves its result and continues to the SSZ root.\n" ++
  "  j .Lsg_hash\n" ++
  ".Lsg_fail_contig: li a0, 0x18; j .Lsg_unimpl\n" ++
  ".Lsg_fail_toomany: li a0, 0x19; j .Lsg_unimpl\n" ++
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
  statelessGuestInputDecode ++
  -- The serializer is now after decode. This is what makes the failure branch
  -- exact: malformed input never runs the old diagnostic body or verifier.
  emitProgram EvmAsm.Stateless.SSZ.Encode.serialize_stateless_output ++ "\n" ++
  statelessGuestValidatorPipeline ++ "\n" ++
  ".Lsg_hash:\n" ++
  "  # The entry decoder above is the single deserialize boundary. It has\n" ++
  "  # already checked the schema, outer offsets, section bounds, chain id,\n" ++
  "  # public-key framing, and witness-header list framing. Keeping the root\n" ++
  "  # epilogue free of a second decoder prevents the two paths from drifting.\n" ++
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
  "  # --- block_access_list_root = hash_tree_root(ByteList[2^30]) ---\n" ++
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
  "  li a2, 25                  # chunk-cap log2 (2^30 / 32)\n" ++
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
  "  # #12057: memcpy 64B from s6+176 -> t1 (unaligned-safe)\n  mv a0, t1\n  addi a1, s6, 176\n  li a2, 64\n  jal ra, sg_memcpy\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_leaf_4_logs_bloom_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_0_1 -> npr_leaf_4_logs_bloom_scratch\n" ++
  "  # Dynamic node_2_3 = sha256(chunk_2 || chunk_3)\n" ++
  "  # chunk_2 @ SSZ_BASE + 16 + 44 + 180 = +240\n" ++
  "  # chunk_3 @ SSZ_BASE + 16 + 44 + 212 = +272\n" ++
  "  la t1, npr_sha_input\n" ++
  "  # #12057: memcpy 64B from s6+240 -> t1 (unaligned-safe)\n  mv a0, t1\n  addi a1, s6, 240\n  li a2, 64\n  jal ra, sg_memcpy\n" ++
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
  "  # #12057: memcpy 32B from s6+432 -> t1+32\n  addi a0, t1, 32\n  addi a1, s6, 432\n  li a2, 32\n  jal ra, sg_memcpy\n" ++
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
  "  # #12057: memcpy 32B from s6+500 -> t1+32\n  addi a0, t1, 32\n  addi a1, s6, 500\n  li a2, 32\n  jal ra, sg_memcpy\n" ++
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
  "  # #12057: memcpy 8B from s6+572 -> t1+32\n  addi a0, t1, 32\n  addi a1, s6, 572\n  li a2, 8\n  jal ra, sg_memcpy\n" ++
  "  sd zero, 40(t1); sd zero, 48(t1); sd zero, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_14_15_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_14_15 -> npr_node_14_15_scratch\n" ++
  "  # Dynamic node_12_15 (supports leaf_12 = block_hash):\n" ++
  "  # node_12_13 = sha256(leaf_12=block_hash || leaf_13=transactions_root)\n" ++
  "  # leaf_13 (transactions default empty list root) is a static\n" ++
  "  # `npr_leaf_13_transactions_root` constant.\n" ++
  "  # block_hash (Bytes32 @ SSZ_BASE + 16 + 44 + 472 = +532)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  # #12057: memcpy 32B from s6+532 -> t1 (unaligned-safe)\n  mv a0, t1\n  addi a1, s6, 532\n  li a2, 32\n  jal ra, sg_memcpy\n" ++
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
  "  # #12057 u64              # gas_used\n  lbu t2, 480(s6)\n  lbu t3, 481(s6); slli t3, t3, 8; or t2, t2, t3\n  lbu t3, 482(s6); slli t3, t3, 16; or t2, t2, t3\n  lbu t3, 483(s6); slli t3, t3, 24; or t2, t2, t3\n  lbu t3, 484(s6); slli t3, t3, 32; or t2, t2, t3\n  lbu t3, 485(s6); slli t3, t3, 40; or t2, t2, t3\n  lbu t3, 486(s6); slli t3, t3, 48; or t2, t2, t3\n  lbu t3, 487(s6); slli t3, t3, 56; or t2, t2, t3\n" ++
  "  sd t2,  0(t1)\n" ++
  "  sd zero,  8(t1); sd zero, 16(t1); sd zero, 24(t1)\n" ++
  "  # #12057 u64              # timestamp\n  lbu t2, 488(s6)\n  lbu t3, 489(s6); slli t3, t3, 8; or t2, t2, t3\n  lbu t3, 490(s6); slli t3, t3, 16; or t2, t2, t3\n  lbu t3, 491(s6); slli t3, t3, 24; or t2, t2, t3\n  lbu t3, 492(s6); slli t3, t3, 32; or t2, t2, t3\n  lbu t3, 493(s6); slli t3, t3, 40; or t2, t2, t3\n  lbu t3, 494(s6); slli t3, t3, 48; or t2, t2, t3\n  lbu t3, 495(s6); slli t3, t3, 56; or t2, t2, t3\n" ++
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
  "  # #12057 u64              # block_number\n  lbu t2, 464(s6)\n  lbu t3, 465(s6); slli t3, t3, 8; or t2, t2, t3\n  lbu t3, 466(s6); slli t3, t3, 16; or t2, t2, t3\n  lbu t3, 467(s6); slli t3, t3, 24; or t2, t2, t3\n  lbu t3, 468(s6); slli t3, t3, 32; or t2, t2, t3\n  lbu t3, 469(s6); slli t3, t3, 40; or t2, t2, t3\n  lbu t3, 470(s6); slli t3, t3, 48; or t2, t2, t3\n  lbu t3, 471(s6); slli t3, t3, 56; or t2, t2, t3\n" ++
  "  sd t2,  0(t1)\n" ++
  "  sd zero,  8(t1); sd zero, 16(t1); sd zero, 24(t1)\n" ++
  "  # #12057 u64              # gas_limit\n  lbu t2, 472(s6)\n  lbu t3, 473(s6); slli t3, t3, 8; or t2, t2, t3\n  lbu t3, 474(s6); slli t3, t3, 16; or t2, t2, t3\n  lbu t3, 475(s6); slli t3, t3, 24; or t2, t2, t3\n  lbu t3, 476(s6); slli t3, t3, 32; or t2, t2, t3\n  lbu t3, 477(s6); slli t3, t3, 40; or t2, t2, t3\n  lbu t3, 478(s6); slli t3, t3, 48; or t2, t2, t3\n  lbu t3, 479(s6); slli t3, t3, 56; or t2, t2, t3\n" ++
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
  "  # #12057 parent_hash 32B from s6+60\n" ++
  "  mv a0, t1; addi a1, s6, 60; li a2, 32; jal ra, sg_memcpy\n" ++
  "  # fee_recipient first 8B at s6+92 (may be unaligned)\n" ++
  "  lbu t2, 92(s6)\n" ++
  "  lbu t3, 93(s6); slli t3, t3, 8; or t2, t2, t3\n" ++
  "  lbu t3, 94(s6); slli t3, t3, 16; or t2, t2, t3\n" ++
  "  lbu t3, 95(s6); slli t3, t3, 24; or t2, t2, t3\n" ++
  "  lbu t3, 96(s6); slli t3, t3, 32; or t2, t2, t3\n" ++
  "  lbu t3, 97(s6); slli t3, t3, 40; or t2, t2, t3\n" ++
  "  lbu t3, 98(s6); slli t3, t3, 48; or t2, t2, t3\n" ++
  "  lbu t3, 99(s6); slli t3, t3, 56; or t2, t2, t3\n" ++
  "  sd t2, 32(t1)\n" ++
  "  # #12057: memcpy 8B from s6+100 -> t1+40\n  addi a0, t1, 40\n  addi a1, s6, 100\n  li a2, 8\n  jal ra, sg_memcpy\n" ++
  "  lbu t2, 108(s6)\n  lbu t3, 109(s6); slli t3, t3, 8; or t2, t2, t3\n  lbu t3, 110(s6); slli t3, t3, 16; or t2, t2, t3\n  lbu t3, 111(s6); slli t3, t3, 24; or t2, t2, t3\n  sd t2, 48(t1)\n" ++
  "  sd zero, 56(t1)\n" ++
  "  la a0, npr_sha_input; li a1, 64; la a2, npr_node_0_3_scratch\n" ++
  "  jal ra, zkvm_sha256         # node_0_1 -> npr_node_0_3_scratch\n" ++
  "  # node_2_3 = sha256(leaf_2=state_root || leaf_3=receipts_root):\n" ++
  "  #   state_root    (Bytes32 @ SSZ_BASE + 16 + 44 + 52  = +112)\n" ++
  "  #   receipts_root (Bytes32 @ SSZ_BASE + 16 + 44 + 84  = +144)\n" ++
  "  la t1, npr_sha_input\n" ++
  "  # #12057: memcpy 64B from s6+112 -> t1 (unaligned-safe)\n  mv a0, t1\n  addi a1, s6, 112\n  li a2, 64\n  jal ra, sg_memcpy\n" ++
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
  "  # #12057 u64              # excess_blob_gas\n  lbu t2, 580(s6)\n  lbu t3, 581(s6); slli t3, t3, 8; or t2, t2, t3\n  lbu t3, 582(s6); slli t3, t3, 16; or t2, t2, t3\n  lbu t3, 583(s6); slli t3, t3, 24; or t2, t2, t3\n  lbu t3, 584(s6); slli t3, t3, 32; or t2, t2, t3\n  lbu t3, 585(s6); slli t3, t3, 40; or t2, t2, t3\n  lbu t3, 586(s6); slli t3, t3, 48; or t2, t2, t3\n  lbu t3, 587(s6); slli t3, t3, 56; or t2, t2, t3\n" ++
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
  "  # #12057 u64              # slot_number\n  lbu t2, 592(s6)\n  lbu t3, 593(s6); slli t3, t3, 8; or t2, t2, t3\n  lbu t3, 594(s6); slli t3, t3, 16; or t2, t2, t3\n  lbu t3, 595(s6); slli t3, t3, 24; or t2, t2, t3\n  lbu t3, 596(s6); slli t3, t3, 32; or t2, t2, t3\n  lbu t3, 597(s6); slli t3, t3, 40; or t2, t2, t3\n  lbu t3, 598(s6); slli t3, t3, 48; or t2, t2, t3\n  lbu t3, 599(s6); slli t3, t3, 56; or t2, t2, t3\n" ++
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
  "  # #12057: memcpy 32B from s6+24 -> t1 (unaligned-safe)\n  mv a0, t1\n  addi a1, s6, 24\n  li a2, 32\n  jal ra, sg_memcpy\n" ++
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
  -- fhsxz.2.4.2.57.11.6.5: the verdict's contract dispatch lets real RETURN/REVERT handlers
  -- write OUTPUT_ADDR (0xa0010000), clobbering the result we just computed (npr_root + tail) on
  -- revert/return blocks. Save OUTPUT[0:112] before the verdict and restore it after, so the
  -- 105-byte SszStatelessValidationResult survives. (The verdict reads its outcome from env/rdg,
  -- not its own OUTPUT, so discarding those dispatch-time OUTPUT writes is sound. a0 = the verdict
  -- bit; the restore loop touches only t-regs, so a0 survives for the succ stamp below.)
  "  li t0, 0xa0010000; la t1, npr_saved_output; li t2, 0\n" ++
  ".Lsg_npr_save:\n" ++
  "  add t3, t0, t2; ld t4, 0(t3); add t3, t1, t2; sd t4, 0(t3)\n" ++
  "  addi t2, t2, 8; li t3, 112; bltu t2, t3, .Lsg_npr_save\n" ++
  "  jal ra, stateless_verdict_v2\n" ++
  -- Verdict-debug ABI: byte 32 is only the success bit and byte 33 belongs
  -- to result payload, so neither is the internal rejection classification.
  -- Surface the actual verdict accumulator at OUTPUT+112 (outside the saved
  -- result prefix) for multi-tx census/debug probes.  This is diagnostic-only
  -- and does not participate in the SSZ validation result.
  "  la t5, bv_fail_code; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 112(t0)\n" ++
  -- Shadow rebuilt-BAL comparison: 0 = rebuilt hash matches supplied BAL,
  -- 1 = mismatch, 2 = serializer/sort failure, 3 = rejected-input skip.
  -- OUTPUT+120 is outside the saved SSZ result prefix and never feeds a
  -- verdict branch.
  "  la t5, bv_bal_shadow_status; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 120(t0)\n" ++
  -- The two lengths partition a shadow hash mismatch: unequal means a row
  -- population gap; equal means the next diagnostic must inspect values/order.
  "  la t5, bv_bal_shadow_rebuilt_len; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 128(t0)\n" ++
  "  la t5, bv_bal_shadow_supplied_len; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 136(t0)\n" ++
  "  la t5, bv_bal_shadow_emit_storage_changes; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 144(t0)\n" ++
  "  la t5, bv_bal_shadow_emit_storage_reads; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 152(t0)\n" ++
  "  la t5, bv_bal_shadow_emit_balance_changes; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 160(t0)\n" ++
  "  la t5, bv_bal_shadow_emit_nonce_changes; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 168(t0)\n" ++
  "  la t5, bv_bal_shadow_emit_code_changes; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 176(t0)\n" ++
  "  la t5, storage_reads_count; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 184(t0)\n" ++
  -- Producer-side BAL diagnostic cells (see BlockVerdictDataSection for the
  -- staging argument).  OUTPUT+192..248 is outside the 112-byte saved SSZ result
  -- prefix and outside the 0..184 range the existing probes claim.  Exclusivity
  -- was established from the EMITTED asm, not from source greps: every `li rd,
  -- 0xa0010000` in `stateless_guest.s` was walked forward to the stores that use
  -- rd, which gives the complete per-function offset inventory.  It found that
  -- `h_RETURN` and `h_REVERT` write OUTPUT+0/8/16/24/32/64/248, so **248 is
  -- contended** and the eighth cell sits at 256 instead.  These stores run after
  -- `stateless_verdict_v2` returns, so a cell at 248 would have won the race and
  -- read correctly anyway -- but only by store order, and `h_RETURN`'s 248 is a
  -- return-data length capped at 176, i.e. a value that would have read as a
  -- plausible count had the order been the other way.  192..240 and 256 have no
  -- other writer at all, which is the claim worth having.  NOTE: the harness dumps
  -- 256 OUTPUT bytes by default, i.e. offsets 0..248, so the cell at 256 is only
  -- visible with `SPIKE_OUTPUT_LEN=264` (spike) or an equivalently widened read.
  -- The other seven are inside the default dump;
  -- the stores at 192..248 off `a2`/`a6` elsewhere in the file are the EVM value
  -- stack in `h_SWAP6` and a frame record near `evm_memory`, not OUTPUT.
  -- Read order per component: bit_set, differs, builder_count, cmp_attempts.
  "  la t5, bald_bal_bit_set; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 192(t0)\n" ++
  "  la t5, bald_bal_differs; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 200(t0)\n" ++
  "  la t5, bald_bal_builder_count; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 208(t0)\n" ++
  "  la t5, bald_bal_cmp_attempts; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 216(t0)\n" ++
  "  la t5, bald_non_bit_set; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 224(t0)\n" ++
  "  la t5, bald_non_differs; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 232(t0)\n" ++
  "  la t5, bald_non_builder_count; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 240(t0)\n" ++
  "  la t5, bald_non_cmp_attempts; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 256(t0)\n" ++
  -- Witness cells at 264..328.  Nothing else in the unit writes an OUTPUT base
  -- above 256 except `block_verdict_creation_runtime` at 472/480, established by
  -- the same forward walk from every `li rd, 0xa0010000`.  Needs
  -- `SPIKE_OUTPUT_LEN=344` to read (the default dump is 256 bytes).
  --
  -- USEFUL ASYMMETRY for a future reader: the `_bai_mask` cells shift by `bai`, and
  -- RV64 takes the low 6 bits of the shift amount, so on a block with 64 or more
  -- transactions THE MASKS BECOME UNTRUSTWORTHY WHILE THE COUNTS STAY VALID.
  -- The cells remain usable there, just not all of them.
  --
  -- The `_eq_val_*` cells are LAST-WRITE-WINS across equal rows, so on a fixture
  -- with more than one equal row they name a value but not which row produced it.
  "  la t5, bald_bal_eq_bai_mask; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 264(t0)\n" ++
  "  la t5, bald_bal_ne_bai_mask; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 272(t0)\n" ++
  "  la t5, bald_bal_eq_val_lo; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 280(t0)\n" ++
  "  la t5, bald_bal_eq_val_hi; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 288(t0)\n" ++
  "  la t5, bald_non_eq_bai_mask; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 296(t0)\n" ++
  "  la t5, bald_non_ne_bai_mask; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 304(t0)\n" ++
  "  la t5, bald_non_eq_val_pre; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 312(t0)\n" ++
  "  la t5, bald_non_eq_val_post; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 320(t0)\n" ++
  "  la t5, bald_bal_eq_addr_a; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 328(t0)\n" ++
  "  la t5, bald_bal_eq_addr_b; ld t5, 0(t5); li t0, 0xa0010000; sd t5, 336(t0)\n" ++
  "  li t0, 0xa0010000; la t1, npr_saved_output; li t2, 0\n" ++
  ".Lsg_npr_restore:\n" ++
  "  add t3, t1, t2; ld t4, 0(t3); add t3, t0, t2; sd t4, 0(t3)\n" ++
  "  addi t2, t2, 8; li t3, 112; bltu t2, t3, .Lsg_npr_restore\n" ++
  -- The entry decoder is the single schema/SSZ rejection boundary. At this
  -- point a0 is the verifier's result; only that result is copied into the
  -- serialized validation result before the common halt path.
  "  li t0, 0xa0010000; sb a0, 32(t0)\n" ++
  "  # Restore zisk's trap vector before the final Linux-93 halt ecall.\n" ++
  "  li t0, 0xa0009828          # zisk MTVEC memory slot\n" ++
  "  la t1, npr_saved_mtvec\n" ++
  "  ld t1, 0(t1)\n" ++
  "  sd t1, 0(t0)\n" ++
  "  j .Lsg_done\n" ++
  ".Lsg_default_failed_output:\n" ++
  "  li t0, 0xa0010000; la t1, default_failed_stateless_output; li t2, 0\n" ++
  ".Lsg_dfo_copy:\n" ++
  "  add t3, t1, t2; lbu t4, 0(t3); add t3, t0, t2; sb t4, 0(t3)\n" ++
  "  addi t2, t2, 1; li t3, 61; bltu t2, t3, .Lsg_dfo_copy\n" ++
  "  li t4, 0\n" ++
  ".Lsg_dfo_zero_tail:\n" ++
  "  add t3, t0, t2; sb t4, 0(t3)\n" ++
  "  addi t2, t2, 1; li t3, 112; bltu t2, t3, .Lsg_dfo_zero_tail\n" ++
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
  emitProgram SgLoadU32leSAsm.sgLoadU32le_prog ++ "\n" ++
  -- Alignment-safe byte copy: a0 = dst, a1 = src, a2 = len. Byte-wise
  -- (LBU/SB) so src/dst may be unaligned. Leaf; clobbers t0,a0,a1,a2;
  -- preserves all s-registers and ra.
  "sg_memcpy:\n" ++
  emitProgram SgMemcpySAsm.sgMemcpy_prog ++ "\n" ++
  -- The following are structural SSZ validators for the four nested
  -- containers. They intentionally validate wire framing only: fixed-field
  -- widths, canonical offsets, list element sizes, and list limits. The
  -- existing verifier consumes the decoded fields after this boundary.
  "sg_validate_fixed_list:\n" ++
  "  beqz a2, .Lsg_vfixed_bad\n" ++
  "  remu t0, a1, a2; bnez t0, .Lsg_vfixed_bad\n" ++
  "  divu t0, a1, a2; bgtu t0, a3, .Lsg_vfixed_bad\n" ++
  "  li a0, 0; ret\n" ++
  ".Lsg_vfixed_bad:\n" ++
  "  li a0, 1; ret\n" ++
  "sg_validate_var_list:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  beqz s1, .Lsg_vvar_ok\n" ++
  "  mv a0, s0; jal ra, sg_load_u32le; mv s3, a0\n" ++
  "  beqz s3, .Lsg_vvar_bad\n" ++
  "  li t0, 4; remu t1, s3, t0; bnez t1, .Lsg_vvar_bad\n" ++
  "  bgtu s3, s1, .Lsg_vvar_bad\n" ++
  "  srli s4, s3, 2; bgtu s4, s2, .Lsg_vvar_bad\n" ++
  "  li t2, 0; li t3, 0\n" ++
  ".Lsg_vvar_loop:\n" ++
  "  beq t2, s4, .Lsg_vvar_ok\n" ++
  "  slli t0, t2, 2; add t0, s0, t0; mv a0, t0; jal ra, sg_load_u32le\n" ++
  "  bltu a0, s3, .Lsg_vvar_bad; bgtu a0, s1, .Lsg_vvar_bad\n" ++
  "  beqz t2, .Lsg_vvar_first\n" ++
  "  bltu a0, t3, .Lsg_vvar_bad\n" ++
  ".Lsg_vvar_first:\n" ++
  "  mv t3, a0; addi t2, t2, 1; j .Lsg_vvar_loop\n" ++
  ".Lsg_vvar_ok:\n" ++
  "  li a0, 0; j .Lsg_vvar_return\n" ++
  ".Lsg_vvar_bad:\n" ++
  "  li a0, 1\n" ++
  ".Lsg_vvar_return:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); addi sp, sp, 48; ret\n" ++
  "sg_validate_execution_payload:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  "  li t0, 540; bltu s1, t0, .Lsg_vpay_bad\n" ++
  "  addi a0, s0, 436; jal ra, sg_load_u32le; mv s2, a0\n" ++
  "  addi a0, s0, 504; jal ra, sg_load_u32le; mv s3, a0\n" ++
  "  addi a0, s0, 508; jal ra, sg_load_u32le; mv s4, a0\n" ++
  "  addi a0, s0, 528; jal ra, sg_load_u32le; mv s5, a0\n" ++
  "  li t0, 540; bne s2, t0, .Lsg_vpay_bad\n" ++
  "  bltu s3, s2, .Lsg_vpay_bad; bltu s4, s3, .Lsg_vpay_bad; bltu s5, s4, .Lsg_vpay_bad; bgtu s5, s1, .Lsg_vpay_bad\n" ++
  "  sub t0, s3, s2; li t1, 32; bgtu t0, t1, .Lsg_vpay_bad\n" ++
  "  add a0, s0, s3; sub a1, s4, s3; li a2, 1048576; jal ra, sg_validate_var_list; bnez a0, .Lsg_vpay_bad\n" ++
  "  add a0, s0, s4; sub a1, s5, s4; li a2, 44; li a3, 16; jal ra, sg_validate_fixed_list; bnez a0, .Lsg_vpay_bad\n" ++
  "  sub t0, s1, s5; li t1, 0x40000000; bgtu t0, t1, .Lsg_vpay_bad\n" ++
  "  li a0, 0; j .Lsg_vpay_return\n" ++
  ".Lsg_vpay_bad:\n" ++
  "  li a0, 1\n" ++
  ".Lsg_vpay_return:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); addi sp, sp, 64; ret\n" ++
  "sg_validate_execution_requests:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1; li t0, 20; bltu s1, t0, .Lsg_ver_bad\n" ++
  "  mv a0, s0; jal ra, sg_load_u32le; mv s2, a0\n" ++
  "  addi a0, s0, 4; jal ra, sg_load_u32le; mv s3, a0\n" ++
  "  addi a0, s0, 8; jal ra, sg_load_u32le; mv s4, a0\n" ++
  "  addi a0, s0, 12; jal ra, sg_load_u32le; mv s5, a0\n" ++
  "  addi a0, s0, 16; jal ra, sg_load_u32le; mv s6, a0\n" ++
  "  li t0, 20; bne s2, t0, .Lsg_ver_bad\n" ++
  "  bltu s3, s2, .Lsg_ver_bad; bltu s4, s3, .Lsg_ver_bad; bltu s5, s4, .Lsg_ver_bad; bltu s6, s5, .Lsg_ver_bad; bgtu s6, s1, .Lsg_ver_bad\n" ++
  "  add a0, s0, s2; sub a1, s3, s2; li a2, 192; li a3, 8192; jal ra, sg_validate_fixed_list; bnez a0, .Lsg_ver_bad\n" ++
  "  add a0, s0, s3; sub a1, s4, s3; li a2, 76; li a3, 16; jal ra, sg_validate_fixed_list; bnez a0, .Lsg_ver_bad\n" ++
  "  add a0, s0, s4; sub a1, s5, s4; li a2, 116; li a3, 2; jal ra, sg_validate_fixed_list; bnez a0, .Lsg_ver_bad\n" ++
  "  add a0, s0, s5; sub a1, s6, s5; li a2, 184; li a3, 64; jal ra, sg_validate_fixed_list; bnez a0, .Lsg_ver_bad\n" ++
  "  add a0, s0, s6; sub a1, s1, s6; li a2, 68; li a3, 16; jal ra, sg_validate_fixed_list; bnez a0, .Lsg_ver_bad\n" ++
  "  li a0, 0; j .Lsg_ver_return\n" ++
  ".Lsg_ver_bad:\n" ++
  "  li a0, 1\n" ++
  ".Lsg_ver_return:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); addi sp, sp, 80; ret\n" ++
  "sg_validate_npr:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; li t0, 44; bltu s1, t0, .Lsg_vnpr_bad\n" ++
  "  mv a0, s0; jal ra, sg_load_u32le; mv s2, a0\n" ++
  "  addi a0, s0, 4; jal ra, sg_load_u32le; mv s3, a0\n" ++
  "  addi a0, s0, 40; jal ra, sg_load_u32le; mv s4, a0\n" ++
  "  li t0, 44; bne s2, t0, .Lsg_vnpr_bad\n" ++
  "  bltu s3, s2, .Lsg_vnpr_bad; bltu s4, s3, .Lsg_vnpr_bad; bgtu s4, s1, .Lsg_vnpr_bad\n" ++
  "  addi a0, s0, 44; sub a1, s3, s2; jal ra, sg_validate_execution_payload; bnez a0, .Lsg_vnpr_bad\n" ++
  "  add a0, s0, s3; sub a1, s4, s3; li a2, 32; li a3, 4096; jal ra, sg_validate_fixed_list; bnez a0, .Lsg_vnpr_bad\n" ++
  "  add a0, s0, s4; sub a1, s1, s4; jal ra, sg_validate_execution_requests; bnez a0, .Lsg_vnpr_bad\n" ++
  "  li a0, 0; j .Lsg_vnpr_return\n" ++
  ".Lsg_vnpr_bad:\n" ++
  "  li a0, 1\n" ++
  ".Lsg_vnpr_return:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); addi sp, sp, 64; ret\n" ++
  "sg_validate_witness:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; li t0, 12; bltu s1, t0, .Lsg_vwit_bad\n" ++
  "  mv a0, s0; jal ra, sg_load_u32le; mv s2, a0\n" ++
  "  addi a0, s0, 4; jal ra, sg_load_u32le; mv s3, a0\n" ++
  "  addi a0, s0, 8; jal ra, sg_load_u32le; mv s4, a0\n" ++
  "  li t0, 12; bne s2, t0, .Lsg_vwit_bad\n" ++
  "  bltu s3, s2, .Lsg_vwit_bad; bltu s4, s3, .Lsg_vwit_bad; bgtu s4, s1, .Lsg_vwit_bad\n" ++
  "  add a0, s0, s2; sub a1, s3, s2; li a2, 4194304; jal ra, sg_validate_var_list; bnez a0, .Lsg_vwit_bad\n" ++
  "  add a0, s0, s3; sub a1, s4, s3; li a2, 262144; jal ra, sg_validate_var_list; bnez a0, .Lsg_vwit_bad\n" ++
  "  add a0, s0, s4; sub a1, s1, s4; li a2, 256; jal ra, sg_validate_var_list; bnez a0, .Lsg_vwit_bad\n" ++
  "  li a0, 0; j .Lsg_vwit_return\n" ++
  ".Lsg_vwit_bad:\n" ++
  "  li a0, 1\n" ++
  ".Lsg_vwit_return:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); addi sp, sp, 64; ret\n" ++
  "sg_validate_chain_config:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1; li t0, 12; bltu s1, t0, .Lsg_vcc_bad\n" ++
  "  addi a0, s0, 8; jal ra, sg_load_u32le; mv s2, a0\n" ++
  "  li t0, 12; bltu s2, t0, .Lsg_vcc_bad; bgtu s2, s1, .Lsg_vcc_bad\n" ++
  "  sub s3, s1, s2; add a0, s0, s2; jal ra, sg_load_u32le; mv s4, a0\n" ++
  "  li t0, 4; bne s4, t0, .Lsg_vcc_bad; bgtu s4, s3, .Lsg_vcc_bad\n" ++
  "  sub s5, s3, s4; add a0, s0, s2; add a0, a0, s4; jal ra, sg_load_u32le; mv s6, a0\n" ++
  "  add a0, s0, s2; add a0, a0, s4; addi a0, a0, 4; jal ra, sg_load_u32le; mv t2, a0\n" ++
  "  li t0, 8; bne s6, t0, .Lsg_vcc_bad; bltu t2, s6, .Lsg_vcc_bad; bgtu t2, s5, .Lsg_vcc_bad\n" ++
  "  add a0, s0, s2; add a0, a0, s4; add a0, a0, s6; sub a1, t2, s6; li a2, 8; li a3, 1; jal ra, sg_validate_fixed_list; bnez a0, .Lsg_vcc_bad\n" ++
  "  add a0, s0, s2; add a0, a0, s4; add a0, a0, t2; sub a1, s5, t2; li a2, 8; li a3, 1; jal ra, sg_validate_fixed_list; bnez a0, .Lsg_vcc_bad\n" ++
  "  li a0, 0; j .Lsg_vcc_return\n" ++
  ".Lsg_vcc_bad:\n" ++
  "  li a0, 1\n" ++
  ".Lsg_vcc_return:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); addi sp, sp, 80; ret\n" ++
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
  -- Container of 5 List[Container] fields {deposits, withdrawals,
  -- consolidations, builder_deposits, builder_exits}; root = merkleize
  -- ([htr(each list)], limit_log2=3).
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
  -- htr(BuilderDepositRequest): 184B {pubkey BV48, wc Bytes32,
  -- amount u64, signature BV96}; four leaves at limit_log2=2.
  "sg_htr_bd:\n" ++                          -- a0=w(184), a1=out
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  "  mv a0, s0; la a1, er_leaf_buf; jal ra, sg_htr_bv48\n" ++
  "  la a0, er_leaf_buf; addi a0, a0, 32; addi a1, s0, 48; li a2, 32; jal ra, sg_memcpy\n" ++
  "  la t0, er_leaf_buf; sd zero, 64(t0); sd zero, 72(t0); sd zero, 80(t0); sd zero, 88(t0)\n" ++
  "  la a0, er_leaf_buf; addi a0, a0, 64; addi a1, s0, 80; li a2, 8; jal ra, sg_memcpy\n" ++
  "  addi a0, s0, 88; la a1, er_leaf_buf; addi a1, a1, 96; jal ra, sg_htr_bv96\n" ++
  "  la a0, er_leaf_buf; li a1, 4; li a2, 2; mv a3, s1; jal ra, ssz_merkleize\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); addi sp, sp, 32; ret\n" ++
  -- htr(BuilderExitRequest): 68B {source_address BV20, pubkey BV48};
  -- two leaves at limit_log2=1.
  "sg_htr_be:\n" ++                          -- a0=w(68), a1=out
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  "  la t0, er_leaf_buf; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la a0, er_leaf_buf; mv a1, s0; li a2, 20; jal ra, sg_memcpy\n" ++
  "  addi a0, s0, 20; la a1, er_leaf_buf; addi a1, a1, 32; jal ra, sg_htr_bv48\n" ++
  "  la a0, er_leaf_buf; li a1, 2; li a2, 1; mv a3, s1; jal ra, ssz_merkleize\n" ++
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
  -- 5 u32 offsets (deposits/withdrawals/consolidations/builder_deposits/
  -- builder_exits) at section+0/+4/+8/+12/+16; each list body is fixed-size
  -- containers (no inner offset table).
  "ssz_htr_execution_requests:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0; mv s2, a1; mv s1, a2\n" ++
  "  mv a0, s0; jal ra, sg_load_u32le; mv s3, a0          # deposits offset\n" ++
  "  addi a0, s0, 4; jal ra, sg_load_u32le; mv s4, a0     # withdrawals offset\n" ++
  "  addi a0, s0, 8; jal ra, sg_load_u32le; mv s5, a0     # consolidations offset\n" ++
  "  addi a0, s0, 12; jal ra, sg_load_u32le; mv s6, a0    # builder deposits offset\n" ++
  "  addi a0, s0, 16; jal ra, sg_load_u32le; mv s7, a0    # builder exits offset\n" ++
  "  add a0, s0, s3; sub a1, s4, s3; li a2, 192; la a3, sg_htr_deposit; li a4, 13; la a5, er_outer_buf; jal ra, sg_htr_clist\n" ++
  "  add a0, s0, s4; sub a1, s5, s4; li a2, 76;  la a3, sg_htr_wr;      li a4, 4;  la a5, er_outer_buf; addi a5, a5, 32; jal ra, sg_htr_clist\n" ++
  "  add a0, s0, s5; sub a1, s6, s5; li a2, 116; la a3, sg_htr_cr;      li a4, 1;  la a5, er_outer_buf; addi a5, a5, 64; jal ra, sg_htr_clist\n" ++
  "  add a0, s0, s6; sub a1, s7, s6; li a2, 184; la a3, sg_htr_bd;      li a4, 6;  la a5, er_outer_buf; addi a5, a5, 96; jal ra, sg_htr_clist\n" ++
  "  add a0, s0, s7; sub a1, s2, s7; li a2, 68;  la a3, sg_htr_be;      li a4, 4;  la a5, er_outer_buf; addi a5, a5, 128; jal ra, sg_htr_clist\n" ++
  "  la a0, er_outer_buf; li a1, 5; li a2, 3; mv a3, s1; jal ra, ssz_merkleize\n" ++
  "  ld ra,0(sp); ld s0,8(sp); ld s1,16(sp); ld s2,24(sp)\n" ++
  "  ld s3,32(sp); ld s4,40(sp); ld s5,48(sp); ld s6,56(sp); ld s7,64(sp); addi sp,sp,80; ret\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  -- #12351: retired uncalled `chain_validate_{post_merge_full,increasing_timestamps,
  -- consecutive_numbers}` from the guest image (0 entry j/jal; no indirect refs).
  -- Program texts + offline proofs remain under ChainValidateOfflineAddrs.
  -- #12386: the four remaining standalone chain validators are also uncalled;
  -- their predicates are enforced by reachable header/body validators.
  -- #12386: retired uncalled `rlp_field_to_u256_be`; its Program and proofs stay
  -- offline under RlpFieldToU256BeOfflineAddrs, not in the production closure.
  -- Step-2 verdict closure (omits rlp_list_nth_item / rlp_field_to_u64 — already
  -- defined above in this epilogue — to avoid duplicate labels):
  statelessVerdictV2GuestClosure ++ "\n" ++
  ".Lsg_done:"

end EvmAsm.Codegen
