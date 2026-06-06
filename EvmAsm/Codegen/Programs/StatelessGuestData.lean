/-
  EvmAsm.Codegen.Programs.StatelessGuestData

  `.data` section for the `stateless_guest` ELF.  Carved out of
  `Programs.lean` for the file-size hard cap; consumed by the
  registry hub via `statelessGuestDataSection`.

  Contains:
    * sha256 + keccak permutation scratch buffers (zkvm_sha256
      and zkvm_keccak256 require these by label).
    * SSZ merkleization scratch buffers (`ssz_merkleize_*`,
      `ssz_hb_*`, `ssz_ltb_*`, `ssz_ew_field_roots`).
    * `ssz_zero_hashes` lookup table (32 × 32 bytes).
    * Header-validator pipeline scratch (`sg_header_lengths`,
      `sg_kpr_valid`, `sg_kpr_bad_index`).
    * Shared K-PR scratch (`zk3_state`, `rfu_offset`,
      `rfu_length`) plus per-K-PR locals.
    * Live SSZ sub-tree constants plus historical reference bytes for the
      `compute_new_payload_request_root` computation at `.Lsg_hash`.
      Current live roots are mostly derived into `npr_*_scratch` or
      `npr_*_dyn` buffers from the SSZ input; legacy labels such as
      `empty_npr_root`, `npr_left_subtree`, `npr_node_0_15`, and
      `npr_node_16_17` are retained only as reference bytes unless a
      later comment says a label is read by the epilogue.
    * Two scratch buffers `npr_sha_input` (64 bytes) and
      `npr_sha_subtree` (32 bytes) plus `npr_exec_payload_root`
      / `npr_left_subtree_scratch` (32 bytes each) for the
      multi-step merkle computation.
-/
import EvmAsm.Codegen.Programs.Ssz

namespace EvmAsm.Codegen

def statelessGuestDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n" ++
  -- ssz_merkleize_scratch / _padded relocated to the .sszscratch NOBITS
  -- region (statelessGuestSszScratchSection, base SSZ_SCRATCH_BASE) and
  -- enlarged; only the small _partial stays in .data.
  ".balign 32\n" ++
  "ssz_merkleize_partial:\n" ++
  "  .zero 64\n" ++
  -- ssz_hb_chunks relocated to .sszscratch (enlarged for big elements).
  ".balign 32\n" ++
  "ssz_hb_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ssz_hb_mix:\n" ++
  "  .zero 64\n" ++
  -- ssz_ltb_child_roots relocated to .sszscratch (enlarged for >32 list
  -- elements, e.g. blocks with many transactions).
  ".balign 32\n" ++
  "ssz_ltb_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ssz_ltb_mix:\n" ++
  "  .zero 64\n" ++
  ".balign 32\n" ++
  "ssz_ew_field_roots:\n" ++
  "  .zero 96\n" ++
  -- Dynamic NPR field-root scratch (PR: dynamic transactions_root +
  -- block_access_list_root). Filled by the .Lsg_hash epilogue from the
  -- live SSZ input, replacing the empty-list constants for these fields.
  ".balign 32\n" ++
  "npr_dynamic_tx_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "npr_dynamic_bal_root:\n" ++
  "  .zero 32\n" ++
  -- logs_bloom chunks 4-7 merkle scratch (full 8-chunk logs_bloom root).
  ".balign 32\n" ++
  "npr_lb_node_45_scratch:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "npr_lb_node_67_scratch:\n" ++
  "  .zero 32\n" ++
  -- versioned_hashes (List[Bytes32, 4096]) dynamic root scratch:
  -- npr_vh_aligned holds the 8-byte-aligned copy of the section (<=32
  -- chunks = 1024 bytes); npr_vh_partial is the pre-mix merkleize root;
  -- npr_versioned_hashes_dyn is the final mixed-in-length root.
  -- npr_vh_aligned relocated to .sszscratch (enlarged: List[Bytes32,4096]
  -- versioned_hashes section is up to 4096*32 = 128 KiB).
  ".balign 32\n" ++
  "npr_vh_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "npr_versioned_hashes_dyn:\n" ++
  "  .zero 32\n" ++
  -- withdrawals (List[SszWithdrawal,16]) dynamic root scratch:
  -- wd_child_roots holds up to 16 per-withdrawal roots; wd_node_a/b are
  -- the 2 inner-merkle nodes per withdrawal; wd_partial is the pre-mix
  -- list root; npr_dynamic_wd_root is the final mixed-in-length root.
  ".balign 32\n" ++
  "wd_child_roots:\n" ++
  "  .zero 512\n" ++          -- 16 * 32
  ".balign 32\n" ++
  "wd_node_a:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "wd_node_b:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "wd_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "npr_dynamic_wd_root:\n" ++
  "  .zero 32\n" ++
  -- execution_requests (SszExecutionRequests) dynamic root scratch:
  -- bv_buf packs a ByteVector[<=96]; er_leaf_buf holds a container's
  -- field leaves (<=5*32); er_clist_partial / er_outer_buf are pre-mix
  -- merkle roots; npr_exec_requests_dyn is the final field root.
  ".balign 32\n" ++
  "bv_buf:\n" ++
  "  .zero 96\n" ++
  ".balign 32\n" ++
  "er_leaf_buf:\n" ++
  "  .zero 256\n" ++
  ".balign 32\n" ++
  "er_clist_partial:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "er_outer_buf:\n" ++
  "  .zero 96\n" ++
  ".balign 32\n" ++
  "npr_exec_requests_dyn:\n" ++
  "  .zero 32\n" ++
  sszZeroHashesDataSection ++ "\n" ++
  -- Header-validator pipeline scratch:
  ".balign 8\n" ++
  "sg_header_lengths:\n" ++
  "  .zero 2048\n" ++          -- MAX_WITNESS_HEADERS (256) × 8 bytes
  "sg_kpr_valid:\n" ++
  "  .zero 8\n" ++
  "sg_kpr_bad_index:\n" ++
  "  .zero 8\n" ++
  -- Shared K-PR scratch (zk3_state / rfu_offset / rfu_length: used by
  -- rlp_list_nth_item + rlp_field_to_u64). Now provided by the appended Step-2
  -- verdict data section (statelessGuestUnit.dataAsm), so NOT declared here to
  -- avoid duplicate-symbol errors.
  -- K290 chain_validate_post_merge_full scratch:
  "cvpmf_field:\n" ++
  "  .zero 8\n" ++
  "cvpmf_offset:\n" ++
  "  .zero 8\n" ++
  "cvpmf_length:\n" ++
  "  .zero 8\n" ++
  "cvpmf_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvpmf_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvpmf_empty_hash:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47\n" ++
  -- K291 chain_validate_extra_data_length scratch:
  "cvedl_offset:\n" ++
  "  .zero 8\n" ++
  "cvedl_length:\n" ++
  "  .zero 8\n" ++
  "cvedl_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvedl_iter_i:\n" ++
  "  .zero 8\n" ++
  -- K240 chain_validate_gas_used_under_limit scratch:
  "cvgul_gas_used:\n" ++
  "  .zero 8\n" ++
  "cvgul_gas_limit:\n" ++
  "  .zero 8\n" ++
  "cvgul_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvgul_iter_i:\n" ++
  "  .zero 8\n" ++
  -- K278 chain_validate_blob_gas_used_multiple scratch:
  "cvbgm_field:\n" ++
  "  .zero 8\n" ++
  "cvbgm_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvbgm_iter_i:\n" ++
  "  .zero 8\n" ++
  -- K277 chain_validate_blob_gas_used_under_max scratch:
  "cvbgum_field:\n" ++
  "  .zero 8\n" ++
  "cvbgum_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvbgum_iter_i:\n" ++
  "  .zero 8\n" ++
  -- K229 chain_validate_increasing_timestamps scratch:
  "cvit_ts:\n" ++
  "  .zero 8\n" ++
  "cvit_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvit_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvit_iter_prev:\n" ++
  "  .zero 8\n" ++
  -- K230 chain_validate_consecutive_numbers scratch:
  "cvcn_num:\n" ++
  "  .zero 8\n" ++
  "cvcn_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvcn_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvcn_iter_prev:\n" ++
  "  .zero 8\n" ++
  -- compute_new_payload_request_root(empty_input) -- historical reference
  -- bytes for the spec hash of an empty `SszNewPayloadRequest`,
  -- independent of chain_id. The epilogue no longer stamps this
  -- constant at OUTPUT[0..32); it recomputes the NPR root dynamically
  -- from the live SSZ input in `.Lsg_hash`.
  -- (Verified against
  --  `execution-specs/.../stateless.compute_new_payload_request_root`
  --  on d7fe16ab8.)
  ".balign 8\n" ++
  "empty_npr_root:\n" ++
  "  .byte 0xf7, 0x83, 0x79, 0x28, 0xaf, 0x2f, 0xf9, 0x7a\n" ++
  "  .byte 0xdd, 0x39, 0x49, 0x6e, 0x3c, 0x72, 0xbc, 0xdf\n" ++
  "  .byte 0xba, 0xdf, 0xfc, 0x45, 0x3d, 0xee, 0x6a, 0x58\n" ++
  "  .byte 0x2c, 0xa2, 0xa5, 0xc7, 0xcc, 0x51, 0x2f, 0x71\n" ++
  -- SSZ field roots / merkle sub-trees for the NPR computation
  -- at `.Lsg_hash`. Several old whole-subtree constants remain below
  -- as historical reference bytes, but the live epilogue now recomputes
  -- the top-level NPR from `npr_exec_payload_root`,
  -- `npr_versioned_hashes_dyn`, parent_beacon_block_root, and
  -- `npr_exec_requests_dyn`.
  --
  --   `npr_left_subtree` is legacy: it was the precomputed
  --     sha256(field_root[execution_payload] || field_root[versioned_hashes])
  --     for the empty case before the dynamic exec_payload and
  --     versioned_hashes paths landed. The live epilogue writes
  --     `npr_left_subtree_scratch` instead.
  --   `npr_exec_requests_root` is legacy for the empty execution_requests
  --     case; the live epilogue uses `npr_exec_requests_dyn`.
  --   `npr_node_0_15` and `npr_node_16_17` are legacy default
  --     exec_payload subtree roots; the live epilogue uses
  --     `npr_node_0_15_scratch` and `npr_node_16_17_scratch`.
  --   `npr_versioned_hashes_root` is retained as the empty-list
  --     reference value; the live epilogue consumes
  --     `npr_versioned_hashes_dyn`.
  ".balign 8\n" ++
  "npr_left_subtree:\n" ++
  "  .byte 0x50, 0x57, 0xc2, 0x29, 0xce, 0xf7, 0x0b, 0x3d\n" ++
  "  .byte 0x2f, 0xe3, 0x46, 0xe2, 0xd6, 0x19, 0x8f, 0x3d\n" ++
  "  .byte 0xd5, 0x36, 0x5b, 0xd9, 0x65, 0x13, 0x22, 0xe8\n" ++
  "  .byte 0x81, 0xa0, 0x99, 0x4c, 0xbd, 0x34, 0x30, 0x57\n" ++
  ".balign 8\n" ++
  "npr_exec_requests_root:\n" ++
  "  .byte 0x85, 0xe2, 0x53, 0xb4, 0x05, 0x99, 0xd0, 0xdf\n" ++
  "  .byte 0x75, 0x6b, 0xe0, 0x43, 0xea, 0x69, 0x49, 0xe4\n" ++
  "  .byte 0x9a, 0x07, 0xe7, 0x56, 0xde, 0xef, 0x72, 0xb3\n" ++
  "  .byte 0x58, 0x8a, 0x4b, 0x05, 0x36, 0x22, 0x06, 0xb5\n" ++
  ".balign 8\n" ++
  "npr_sha_input:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "npr_sha_subtree:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "npr_node_0_15:\n" ++
  "  .byte 0x71, 0xfc, 0x71, 0x15, 0x80, 0xd1, 0x9a, 0x35\n" ++
  "  .byte 0x16, 0x98, 0xda, 0xb1, 0x39, 0x16, 0x66, 0xd8\n" ++
  "  .byte 0x49, 0xe0, 0x60, 0x9a, 0xea, 0x02, 0x09, 0x65\n" ++
  "  .byte 0x15, 0x6b, 0x5e, 0x8d, 0x8c, 0x83, 0xa2, 0xe7\n" ++
  ".balign 8\n" ++
  "npr_node_16_17:\n" ++
  "  .byte 0x95, 0xcc, 0x8c, 0xa6, 0xc4, 0xc1, 0x05, 0x66\n" ++
  "  .byte 0x41, 0xe5, 0xad, 0x8d, 0xc6, 0xe5, 0x66, 0xae\n" ++
  "  .byte 0x5e, 0x6f, 0xeb, 0x2c, 0x03, 0xde, 0x7a, 0xf8\n" ++
  "  .byte 0xfc, 0x95, 0x84, 0x0f, 0x55, 0xdf, 0x8b, 0x8c\n" ++
  ".balign 8\n" ++
  "npr_versioned_hashes_root:\n" ++
  "  .byte 0xdb, 0xa9, 0x67, 0x1b, 0xac, 0x95, 0x13, 0xc9\n" ++
  "  .byte 0x48, 0x2f, 0x14, 0x16, 0xa5, 0x3a, 0xab, 0xd2\n" ++
  "  .byte 0xc6, 0xce, 0x90, 0xd5, 0xa5, 0xf8, 0x65, 0xce\n" ++
  "  .byte 0x5a, 0x55, 0xc7, 0x75, 0x32, 0x5c, 0x91, 0x36\n" ++
  ".balign 8\n" ++
  "npr_exec_payload_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "npr_left_subtree_scratch:\n" ++
  "  .zero 32\n" ++
  -- `npr_leaf_17_bal_root` is the SSZ hash_tree_root of an
  -- empty `block_access_list` (ByteList[MAX_BLOCK_ACCESS_LIST_BYTES]),
  -- = leaf 17 of the default exec_payload merkle tree. Now that
  -- the `.Lsg_hash` epilogue computes `node_16_17` dynamically
  -- (to support non-default `excess_blob_gas` = leaf 16), only
  -- leaf 17 needs to be precomputed as a constant; the prior
  -- `npr_node_16_17` is no longer referenced but kept for
  -- diff-context.
  -- `npr_node_16_17_scratch` is the 32-byte buffer that holds
  -- the dynamic sha256(leaf_16 || npr_leaf_17_bal_root).
  ".balign 8\n" ++
  "npr_leaf_17_bal_root:\n" ++
  "  .byte 0x0e, 0x61, 0x79, 0x77, 0x4d, 0x9c, 0x1f, 0x78\n" ++
  "  .byte 0x0c, 0x91, 0xa6, 0x89, 0x68, 0xa1, 0x43, 0xb5\n" ++
  "  .byte 0xff, 0xd2, 0xf1, 0x8c, 0x2c, 0x01, 0xa2, 0xe8\n" ++
  "  .byte 0x50, 0x16, 0xe1, 0x2a, 0x8c, 0x78, 0x1a, 0x0b\n" ++
  ".balign 8\n" ++
  "npr_node_16_17_scratch:\n" ++
  "  .zero 32\n" ++
  -- Two new sibling constants for the leaf_6 (block_number)
  -- merkle path through node_0_15:
  --   npr_node_4_5 = sha256(leaf_4=logs_bloom_default ||
  --                         leaf_5=prev_randao_default)
  --   npr_node_8_15 = the subtree root of default leaves 8..15
  --     (sha256 over leaves 8..15 for the default exec_payload).
  -- The remaining two siblings on the path are
  -- `ssz_zero_hash[0]` (leaf_7 default = u64 zero) and
  -- `ssz_zero_hash[2]` (node_0_3 = sha256(zero || zero) at
  -- depth 2). The prior `npr_node_0_15` constant is now
  -- unreferenced (dynamic recompute via these siblings).
  -- `npr_node_0_15_scratch` is the 32-byte buffer that holds
  -- the dynamic computation result.
  ".balign 8\n" ++
  "npr_node_4_5:\n" ++
  "  .byte 0xe8, 0xe5, 0x27, 0xe8, 0x4f, 0x66, 0x61, 0x63\n" ++
  "  .byte 0xa9, 0x0e, 0xf9, 0x00, 0xe0, 0x13, 0xf5, 0x6b\n" ++
  "  .byte 0x0a, 0x4d, 0x02, 0x01, 0x48, 0xb2, 0x22, 0x40\n" ++
  "  .byte 0x57, 0xb7, 0x19, 0xf3, 0x51, 0xb0, 0x03, 0xa6\n" ++
  ".balign 8\n" ++
  "npr_node_8_15:\n" ++
  "  .byte 0x9c, 0xd6, 0x13, 0x23, 0x26, 0x94, 0x9e, 0x18\n" ++
  "  .byte 0x79, 0x4d, 0xb8, 0x5d, 0x0b, 0xed, 0x67, 0xe6\n" ++
  "  .byte 0xff, 0x8d, 0x84, 0x02, 0x0c, 0x0b, 0x18, 0x89\n" ++
  "  .byte 0xb6, 0x76, 0xd2, 0x91, 0x3b, 0xac, 0x8d, 0x4e\n" ++
  ".balign 8\n" ++
  "npr_node_0_15_scratch:\n" ++
  "  .zero 32\n" ++
  -- `npr_leaf_4_logs_bloom_root` is the SSZ hash_tree_root of
  -- an empty `logs_bloom` (ByteVector[256], all zeros), = leaf 4
  -- of the default exec_payload merkle. Now that the
  -- `.Lsg_hash` epilogue computes `node_4_5` dynamically to
  -- support non-default `prev_randao` (= leaf 5), only the
  -- logs_bloom-side leaf needs to be precomputed as a constant.
  -- `npr_node_4_5_scratch` holds the dynamic
  -- sha256(npr_leaf_4_logs_bloom_root || prev_randao).
  ".balign 8\n" ++
  "npr_leaf_4_logs_bloom_root:\n" ++
  "  .byte 0xc7, 0x80, 0x09, 0xfd, 0xf0, 0x7f, 0xc5, 0x6a\n" ++
  "  .byte 0x11, 0xf1, 0x22, 0x37, 0x06, 0x58, 0xa3, 0x53\n" ++
  "  .byte 0xaa, 0xa5, 0x42, 0xed, 0x63, 0xe4, 0x4c, 0x4b\n" ++
  "  .byte 0xc1, 0x5f, 0xf4, 0xcd, 0x10, 0x5a, 0xb3, 0x3c\n" ++
  ".balign 8\n" ++
  "npr_node_4_5_scratch:\n" ++
  "  .zero 32\n" ++
  -- Sibling constants for the dynamic node_8_15 path supporting
  -- leaf_8 = gas_used. Both are subtree roots over default
  -- exec_payload fields and remain static until those leaves
  -- are opened up in follow-up PRs:
  --   npr_node_10_11 = sha256(leaf_10=extra_data_root_default ||
  --                           leaf_11=base_fee_per_gas_default)
  --   npr_node_12_15 = subtree over default leaves 12..15
  --                    (block_hash, transactions, withdrawals,
  --                    blob_gas_used).
  -- `npr_node_8_15_scratch` is the 32-byte buffer that holds
  -- the dynamic node_8_15.
  ".balign 8\n" ++
  "npr_node_10_11:\n" ++
  "  .byte 0x7a, 0x05, 0x01, 0xf5, 0x95, 0x7b, 0xdf, 0x9c\n" ++
  "  .byte 0xb3, 0xa8, 0xff, 0x49, 0x66, 0xf0, 0x22, 0x65\n" ++
  "  .byte 0xf9, 0x68, 0x65, 0x8b, 0x7a, 0x9c, 0x62, 0x64\n" ++
  "  .byte 0x2c, 0xba, 0x11, 0x65, 0xe8, 0x66, 0x42, 0xf5\n" ++
  ".balign 8\n" ++
  "npr_node_12_15:\n" ++
  "  .byte 0x88, 0x4f, 0x54, 0x7a, 0xad, 0x3a, 0x48, 0x73\n" ++
  "  .byte 0xe7, 0x79, 0xe0, 0x4f, 0x8d, 0xdd, 0xb8, 0x8f\n" ++
  "  .byte 0xd4, 0xe8, 0x22, 0x22, 0xa4, 0x4a, 0xb8, 0xa0\n" ++
  "  .byte 0x37, 0xf2, 0x21, 0xdb, 0x97, 0xe9, 0x7b, 0xaa\n" ++
  ".balign 8\n" ++
  "npr_node_8_15_scratch:\n" ++
  "  .zero 32\n" ++
  -- `npr_node_0_3_scratch` holds the dynamic node_0_3 = sha256(
  --   sha256(leaf_0=parent_hash || leaf_1=ssz_zero_hash[0]) ||
  --   ssz_zero_hash[1])
  -- computed in two stages within the same buffer. Used to replace
  -- the previously-static `ssz_zero_hash[2]` constant as the LEFT
  -- input to node_0_7 = sha256(node_0_3 || node_4_7) -- this opens
  -- up leaf_0 (parent_hash). Future PRs can extend the node_0_1
  -- step to read fee_recipient as leaf_1 (sibling extension,
  -- mirroring the leaf_7/gas_limit pattern).
  ".balign 8\n" ++
  "npr_node_0_3_scratch:\n" ++
  "  .zero 32\n" ++
  -- `npr_node_2_3_scratch` holds dynamic
  -- sha256(leaf_2=state_root || leaf_3=receipts_root). Replaces
  -- the previously-static `ssz_zero_hash[1]` (= default
  -- node_2_3) as the right input to
  -- node_0_3 = sha256(node_0_1 || node_2_3). Opens up leaf_2
  -- (state_root) and leaf_3 (receipts_root) for non-default
  -- values.
  ".balign 8\n" ++
  "npr_node_2_3_scratch:\n" ++
  "  .zero 32\n" ++
  -- `npr_leaf_10_extra_data_scratch` holds dynamic
  -- hash_tree_root(extra_data), and `npr_node_10_11_scratch` holds
  -- dynamic sha256(leaf_10=extra_data_root || leaf_11=base_fee_per_gas).
  -- Replaces the previously-static `npr_node_10_11` constant when
  -- combined with node_8_9 to form node_8_11. Opens up leaf_10
  -- (extra_data) and leaf_11 (base_fee_per_gas) for non-default values.
  ".balign 8\n" ++
  "npr_leaf_10_extra_data_scratch:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "npr_node_10_11_scratch:\n" ++
  "  .zero 32\n" ++
  -- Constants for the dynamic node_12_15 path supporting
  -- leaf_12 = block_hash:
  --   `npr_leaf_13_transactions_root` is the historical SSZ hash_tree_root
  --     of the default empty `transactions` list; the live path reads
  --     `npr_dynamic_tx_root`.
  --   `npr_node_14_15` = sha256(leaf_14=withdrawals_default_root
  --     || leaf_15=blob_gas_used_default=zero). Stays static
  --     until leaf 14 or 15 is opened up in a follow-up PR.
  -- Scratch buffers `npr_node_12_13_scratch` and
  -- `npr_node_12_15_scratch` hold the intermediate and final
  -- merkle nodes for the dynamic computation.
  ".balign 8\n" ++
  "npr_leaf_13_transactions_root:\n" ++
  "  .byte 0x7f, 0xfe, 0x24, 0x1e, 0xa6, 0x01, 0x87, 0xfd\n" ++
  "  .byte 0xb0, 0x18, 0x7b, 0xfa, 0x22, 0xde, 0x35, 0xd1\n" ++
  "  .byte 0xf9, 0xbe, 0xd7, 0xab, 0x06, 0x1d, 0x94, 0x01\n" ++
  "  .byte 0xfd, 0x47, 0xe3, 0x4a, 0x54, 0xfb, 0xed, 0xe1\n" ++
  ".balign 8\n" ++
  "npr_node_14_15:\n" ++
  "  .byte 0x33, 0x64, 0x88, 0x03, 0x3f, 0xe5, 0xf3, 0xef\n" ++
  "  .byte 0x4c, 0xcc, 0x12, 0xaf, 0x07, 0xb9, 0x37, 0x0b\n" ++
  "  .byte 0x92, 0xe5, 0x53, 0xe3, 0x5e, 0xcb, 0x4a, 0x33\n" ++
  "  .byte 0x7a, 0x1b, 0x1c, 0x0e, 0x4a, 0xfe, 0x1e, 0x0e\n" ++
  ".balign 8\n" ++
  "npr_saved_mtvec:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "npr_node_12_13_scratch:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "npr_node_12_15_scratch:\n" ++
  "  .zero 32\n" ++
  -- New constant + scratch for the dynamic node_14_15 path
  -- supporting leaf_15 = blob_gas_used:
  --   `npr_leaf_14_withdrawals_root` is the historical SSZ hash_tree_root
  --     of the default empty `withdrawals` list; the live path reads
  --     `npr_dynamic_wd_root`.
  --   `npr_node_14_15_scratch` holds dynamic
  --     sha256(npr_leaf_14_withdrawals_root || blob_gas_used).
  -- The prior static `npr_node_14_15` constant becomes
  -- unreferenced (kept for diff-context).
  ".balign 8\n" ++
  "npr_leaf_14_withdrawals_root:\n" ++
  "  .byte 0x79, 0x29, 0x30, 0xbb, 0xd5, 0xba, 0xac, 0x43\n" ++
  "  .byte 0xbc, 0xc7, 0x98, 0xee, 0x49, 0xaa, 0x81, 0x85\n" ++
  "  .byte 0xef, 0x76, 0xbb, 0x3b, 0x44, 0xba, 0x62, 0xb9\n" ++
  "  .byte 0x1d, 0x86, 0xae, 0x56, 0x9e, 0x4b, 0xb5, 0x35\n" ++
  ".balign 8\n" ++
  "npr_node_14_15_scratch:\n" ++
  "  .zero 32\n" ++
  -- `npr_leaf_4_logs_bloom_scratch` holds the dynamic
  -- hash_tree_root of logs_bloom (= leaf 4 in the exec_payload
  -- merkle). logs_bloom is ByteVector[256] merkleized over 8
  -- chunks (3 levels of sha256). Currently we only read chunk 0
  -- from input; chunks 1..7 stay at their default zero and the
  -- siblings on the path collapse to existing ssz_zero_hashes
  -- entries. The prior static `npr_leaf_4_logs_bloom_root`
  -- constant becomes unreferenced (kept for diff-context).
  ".balign 8\n" ++
  "npr_leaf_4_logs_bloom_scratch:\n" ++
  "  .zero 32\n" ++
  -- Scratch for the dynamic node_2_3 of the logs_bloom subtree
  -- (chunks 2 and 3 paired). Replaces the prior static
  -- `ssz_zero_hash[1]` constant used at level 1 of the
  -- logs_bloom merkle (under node_0_3).
  ".balign 8\n" ++
  "npr_logs_bloom_node_2_3_scratch:\n" ++
  "  .zero 32\n" ++
  -- ===== .sszscratch: large NOBITS SSZ-merkleization work region =====
  -- Relocated here (out of .data) and enlarged so hash_tree_root of a large element fits:
  -- the largest EEST transaction element is ~1 MiB and block_access_list
  -- ~90 KiB. Placed at SSZ_SCRATCH_BASE = 0xbf500000 by the linker's
  -- --section-start=.sszscratch=0xbf500000 (see Driver.lean). @nobits =>
  -- the multi-MiB reservation never lands in the ELF file. Inside the
  -- verified RAM zone (0xa0000000..0xc0000000), so isValidMemAddr already
  -- accepts it. Same labels as before => every `la <buf>` resolves here.
  ".section .sszscratch, \"aw\", @nobits\n" ++
  ".balign 32\n" ++
  "ssz_merkleize_scratch:\n" ++
  "  .zero 0x200000\n" ++              -- 2 MiB (in-place reduction; >= chunks)
  ".balign 32\n" ++
  "ssz_merkleize_padded:\n" ++
  "  .zero 0x200000\n" ++              -- 2 MiB (next-pow2 padding buffer)
  ".balign 32\n" ++
  "ssz_hb_chunks:\n" ++
  "  .zero 0x200000\n" ++              -- 2 MiB (packed bytes of one element)
  ".balign 32\n" ++
  "ssz_ltb_child_roots:\n" ++
  "  .zero 0x20000\n" ++               -- 128 KiB (up to 4096 list-element roots)
  ".balign 32\n" ++
  "npr_vh_aligned:\n" ++
  "  .zero 0x20000\n" ++               -- 128 KiB (versioned_hashes List[Bytes32,4096])
  ".balign 32\n" ++
  "er_child_roots:\n" ++
  "  .zero 0x40000"                    -- 256 KiB (up to MAX_DEPOSIT_REQUESTS = 2^13 roots)

end EvmAsm.Codegen
