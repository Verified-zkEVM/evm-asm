/-
  EvmAsm.Codegen.Programs.BlockVerdictDataSection

  Data-section (BSS/static arenas) for the stateless verdict v2 program.
  Carved out of BlockVerdict.lean to stay within the 1500-line file-size cap.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.NonstorageEffectLog
import EvmAsm.Codegen.CallFrameLayout
import EvmAsm.Codegen.Programs.StatelessVerdict
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.Programs.BalAccountHasStateChange
import EvmAsm.Codegen.Programs.BalStorageChangeValues
import EvmAsm.Codegen.Programs.BalModeledSystem
import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransfer
import EvmAsm.Codegen.Programs.LogRecordsRlp
import EvmAsm.Codegen.Programs.TxPubkey
import EvmAsm.Codegen.Programs.VerifyPublicKeysSenders
-- #11118: BalAllAccountsCodeCovers / BalStorageReadsExecLog data unlinked with dead 43/38.
import EvmAsm.Codegen.Programs.BlockVerdictDataSectionTail
import EvmAsm.Codegen.Programs.AccountWriteMap
import EvmAsm.Codegen.Programs.BlockAccessListBuilder

namespace EvmAsm.Codegen

/-! The post-merge owner set has one entry per account-map row or storage-map
    row, plus the two modeled-system owners seeded outside both maps.  Its
    capacity is therefore the conservative three-term bound: 20,480 account
    rows + 16,384 storage rows + 2 system owners = 36,866.  Keep this tied to
    the authenticated map caps rather than to the 64-entry runtime
    access-account scratch table. -/
def bsrMapOwnerCapacity : Nat :=
  blockAccountWritesCapacity + storageWritesCapacity + bsrModeledSystemChanges

#guard bsrMapOwnerCapacity = 36866

def ziskStatelessVerdictV2DataSection : String :=
  -- .62.2.5: secp256k1 recovery scratch/constants for the ECRECOVER backend
  -- (generator + field constants + R-decompression scratch + tpr_* recovery
  -- scratch). Emitted first so the additions cannot disturb existing label
  -- ordering assumptions below.
  secp256k1CurveDataSection ++ "\n" ++
  secp256k1RecoverDataSection ++ "\n" ++
  txPubkeyRecoverRawDataSection ++ "\n" ++
  -- bmvmx.3.2: TX-side sender-recovery scratch (signature material + per-type
  -- extractor offsets + signing-hash buffers) + verify_public_keys_match_senders
  -- scratch + bv_chain_id. The secp/tpr_* recovery data above is already present
  -- for the ECRECOVER backend; this adds only the transaction-signature delta.
  verifyPublicKeysSendersGuestDataSection ++ "\n" ++
  ziskStatelessVerdictDataSection ++ "\n" ++
  runtimeAccessAccountOutcomeData ++ "\n" ++
  storageAccessGasData ++ "\n" ++
  executionRequestsHashDataSection ++ "\n" ++
  ".balign 32\n" ++
  "svf_tx_root:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "svf_bal_hash:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "svf_withdrawals_root:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "bv_block_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  -- ON TODAY: `.dword 1` with NO WRITER anywhere in the guest, so only a source edit
  -- turns it off. What it gates is larger than its name suggests.
  --
  -- It guards the block-hash comparison at `BlockVerdictFunction.lean:70`. That
  -- comparison is ALSO the only thing binding the supplied block-access-list bytes to
  -- the header: the guest never reads a header BAL-hash field, it CONSTRUCTS one --
  -- `svf_bal_hash` (keccak over the supplied BAL bytes) is passed as a7 to
  -- `block_header_ssz_to_rlp` (`BlockHeaderSszToRlp.lean:77`, a7 = block_access_list_hash
  -- ptr) and embedded while the header RLP is rebuilt. `block_hash_from_header` then
  -- hashes that RLP and compares it byte-by-byte against the payload's block hash.
  --
  -- So with this flag at zero, NOTHING binds the supplied BAL to the header, and a
  -- rebuild-and-compare check over that BAL becomes self-referential -- verifying its
  -- own input against itself. That consequence is invisible from here and from the
  -- comparison site; the dependency runs from this declaration, through an argument
  -- register, into a routine two levels away, and neither end mentioned the other.
  -- See GH #10770.
  "bv_block_hash_check_enabled:\n  .dword 1\n" ++
  ".balign 8\n" ++
  "svf_tx_count:\n  .zero 8\n" ++
  "svf_tx_descriptors:\n  .zero " ++ toString (bvMtxFullTxCap * 16) ++ "\n" ++
  "bah_bal_start:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "sltr_field_len:\n  .zero 8\n" ++
  "sltr_nibble_count:\n  .zero 8\n" ++
  "sltr_hp_len:\n  .zero 8\n" ++
  "sltr_cursor:\n  .zero 8\n" ++
  "sltr_total_payload:\n  .zero 8\n" ++
  "sltr_nibbles:\n  .zero 2048\n" ++
  "sltr_hp_buf:\n  .zero 1024\n" ++
  "sltr_payload_buf:\n  .zero 16384\n" ++
  "sltr_node_buf:\n  .zero 16384\n" ++
  "mtoli_nibbles:\n  .zero 8\n" ++
  "mtoli_leaf_len:\n  .zero 8\n" ++
  "mtoli_leaf_buf:\n  .zero 16384\n" ++
  ".balign 32\n" ++
  "srss_key:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "srss_rlpval:\n  .zero 40\n" ++
  "srss_rlpval_len:\n  .zero 8\n" ++
  "asr_ref:\n  .zero 40\n" ++
  "aps_off:\n  .zero 8\n" ++
  "aps_len:\n  .zero 8\n" ++
  "aps_witness_ptr:\n  .zero 8\n" ++
  "aps_witness_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aps_newsroot:\n  .zero 32\n" ++
  "aps_path:\n  .zero 64\n" ++
  "aps_empty_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21\n" ++
  ".balign 32\n" ++
  "swd_2935_slot:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_2935_val:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_slot:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_val:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_root_slot:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_root_val:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "swd_2935_vlen:\n  .zero 8\n" ++
  "swd_4788_vlen:\n  .zero 8\n" ++
  "swd_4788_root_vlen:\n  .zero 8\n" ++
  "bv_eip4788_current_fast_seen:\n  .zero 8\n" ++
  "swd_ts_be8:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "bsr_root_p:\n  .zero 8\n" ++
  "bsr_wit_p:\n  .zero 8\n" ++
  "bsr_wl_v:\n  .zero 8\n" ++
  "bsr_ssz_p:\n  .zero 8\n" ++
  "bsr_bal_start:\n  .zero 8\n" ++
  "bsr_bal_len:\n  .zero 8\n" ++
  "bsr_bal_count:\n  .zero 8\n" ++
  "bsr_exec_p:\n  .zero 8\n" ++
  "bsr_tx_off:\n  .zero 8\n" ++
  "bsr_pathp:\n  .zero 8\n" ++
  -- Step 1 #10651 scratch: a synthetic AccountChanges item with the map
  -- address and empty BAL field lists.  It lets map-only addresses reuse the
  -- existing account-path/post-account machinery while Step 2 switches the
  -- account fields themselves to account_writes values.
  ".balign 8\n" ++
  "bsr_map_path:\n  .zero 64\n" ++
  "bsr_map_item:\n" ++
  "  .zero 27\n" ++
  "bsr_acct_len:\n  .zero 8\n" ++
  "bsr_tmplen:\n  .zero 8\n" ++
  "bsr_prev_desc:\n  .zero 8\n" ++
  "bsr_prev_acct:\n  .zero 8\n" ++ ziskBalAccountHasStateChangeDataSection ++
  "bsr_bal_item_ptr:\n  .zero 8\n" ++
  "bsr_bal_item_len:\n  .zero 8\n" ++
  ziskBalAccountIsModeledSystemDataSection ++
  ".balign 32\n" ++
  "bsr_kbuf:\n  .zero 32\n" ++
  "bsr_delta:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bsr_acct:\n  .zero 256\n" ++
  "bsr_paths:\n  .zero " ++ toString (bsrMaxAuxChanges * bsrPathBytes) ++
  "\nbsr_newaccts:\n  .zero " ++ toString (bsrMaxAuxChanges * bsrSystemAccountBytes) ++
  "\nbsr_changes:\n  .zero " ++ toString (bsrMaxStateChanges * bsrStateChangeBytes) ++ "\n" ++
  -- sd13v: the bounded builder sorts the already-normalized final descriptors
  -- in place.  Its only sort workspace and construction state are derived
  -- from the 64-nibble key depth, never from an attacker-provided count.
  "bsr_sort_ranges:\n  .zero " ++ toString (bsrMptSortRangeStackCapacity * bsrMptSortRangeFrameBytes) ++ "\n" ++
  "bsr_builder_frames:\n  .zero " ++ toString (bsrMptBuilderFrameCapacity * bsrMptBuilderFrameBytes) ++ "\n" ++
  -- A single depth-first node buffer. Completed children are immediately
  -- reduced to raw references in their parent frame, so construction never
  -- needs one node-sized allocation per descriptor or per depth.
  "bsr_builder_node:\n  .zero " ++ toString bsrMptBuilderNodeScratchBytes ++ "\n" ++
  -- A fixed depth-indexed cache for a constructed hashed child that may be
  -- immediately needed by its parent's one-child collapse.  Tags prevent a
  -- stale sibling's node from ever being reopened.
  "bsr_builder_constructed_nodes:\n  .zero " ++ toString bsrMptConstructedCacheBytes ++ "\n" ++
  "bsr_builder_constructed_refs:\n  .zero " ++ toString bsrMptConstructedCacheRefBytes ++ "\n" ++
  "bsr_builder_constructed_ref_lens:\n  .zero " ++ toString bsrMptConstructedCacheWordBytes ++ "\n" ++
  "bsr_builder_constructed_node_lens:\n  .zero " ++ toString bsrMptConstructedCacheWordBytes ++ "\n" ++
  -- One transient raw result is sufficient for depth-first unwinding. Parents
  -- immediately copy it into their fixed frame slot before visiting a sibling.
  "bsr_builder_result_ref:\n  .zero " ++ toString bsrMptFrameChildRefBytes ++ "\n" ++
  "bsr_builder_result_len:\n  .zero 8\n" ++
  -- The bounded builder is shared by account and storage tries. Thin root
  -- wrappers select the constructed-value and independently the witness-leaf
  -- limits. Storage writes are uint256 (33-byte encoded maximum), but a
  -- hash-authenticated unchanged witness leaf is copied verbatim and is not
  -- rejected merely for exceeding that constructed-value bound.
  "bsr_builder_value_max:\n  .dword " ++ toString bsrEncodedAccountBytes ++ "\n" ++
  "bsr_builder_witness_value_max:\n  .dword " ++ toString bsrEncodedAccountBytes ++ "\n" ++
  "bsr_changed_account_count:\n  .zero 8\n" ++
  "bsr_emitted_owner_count:\n  .zero 8\n" ++
  "bsr_account_from_map:\n  .zero 8\n" ++
  "bsr_account_row:\n  .zero 8\n" ++
  "bsr_access_count:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bsr_changed_accounts:\n  .zero " ++ toString (bsrMaxAccessAccounts * 32) ++ "\n" ++
  "bsr_emitted_owners:\n  .zero " ++ toString (bsrMapOwnerCapacity * 32) ++ "\n" ++
  "baaod_hash:\n  .zero 32\n" ++
  "bsaod_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bsaod_empty_value:\n  .zero 1\n" ++
  "baaod_empty_account:\n" ++
  "  .byte 0xf8,0x44,0x80,0x80,0xa0\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  "  .byte 0xa0\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  ".balign 32\n" ++
  "bsr_addr_2935:\n" ++
  "  .byte 0x00, 0x00, 0xF9, 0x08, 0x27, 0xF1, 0xC5, 0x3a\n" ++
  "  .byte 0x10, 0xcb, 0x7A, 0x02, 0x33, 0x5B, 0x17, 0x53\n" ++
  "  .byte 0x20, 0x00, 0x29, 0x35\n" ++
  ".balign 32\n" ++
  "bsr_addr_4788:\n" ++
  "  .byte 0x00, 0x0F, 0x3d, 0xf6, 0xD7, 0x32, 0x80, 0x7E\n" ++
  "  .byte 0xf1, 0x31, 0x9f, 0xB7, 0xB8, 0xbB, 0x85, 0x22\n" ++
  "  .byte 0xd0, 0xBe, 0xac, 0x02\n" ++
  ".balign 8\n" ++
  -- v0.6.0: begin-of-block system-call code gates (process_unchecked_system_
  -- transaction runs the CONTRACT's code; an absent/codeless history or
  -- beacon-roots contract writes nothing).
  "bsr_sys_has_2935:\n  .zero 8\n" ++
  "bsr_sys_has_4788:\n  .zero 8\n" ++
  "bsr_sys_acct:\n  .zero 104\n" ++
  "bsr_sys_slot_2935:\n  .zero 8\n" ++
  "bsr_sys_slot_4788:\n  .zero 8\n" ++
  "bgv_count:\n  .zero 8\n" ++
  "bgv_off:\n  .zero 8\n" ++
  "bgv_size:\n  .zero 8\n" ++
  "bgv_acctlen:\n  .zero 8\n" ++
  "bv_exec_p:\n  .zero 8\n" ++
  "bv_npr_p:\n  .zero 8\n" ++
  "bv_bal_start:\n  .zero 8\n" ++
  "bv_bal_len:\n  .zero 8\n" ++
  -- Shadow-only rebuilt-BAL digest result: 0 = hash match, 1 = mismatch,
  -- 2 = serializer/sort failure, 3 = skipped on an already-rejected input.
  -- The 40-byte scratch satisfies the verifier's at-least-33-byte ABI without
  -- reusing a serializer-internal work buffer.
  "bv_bal_shadow_status:\n  .zero 8\n" ++
  -- Shadow-only rebuilt/supplied BAL byte lengths.  A hash mismatch with
  -- unequal lengths is a missing/extra-row problem; equal lengths instead
  -- localise the next diagnostic pass to wrong values or ordering.
  "bv_bal_shadow_rebuilt_len:\n  .zero 8\n" ++
  "bv_bal_shadow_supplied_len:\n  .zero 8\n" ++
  -- Set only after BAL slice decoding/gas validation, the structural precondition
  -- shared by the downstream granular BAL comparators.
  "bv_bal_shadow_ready:\n  .zero 8\n" ++
  -- Header gas_limit captured at BAL-slice decode for late gas-on-built (#11120).
  "bv_block_gas_limit:\n  .zero 8\n" ++
  -- Shadow serializer list counters: actual rows emitted, not producer writes.
  "bv_bal_shadow_emit_storage_changes:\n  .zero 8\n" ++
  "bv_bal_shadow_emit_storage_reads:\n  .zero 8\n" ++
  "bv_bal_shadow_emit_balance_changes:\n  .zero 8\n" ++
  "bv_bal_shadow_emit_nonce_changes:\n  .zero 8\n" ++
  "bv_bal_shadow_emit_code_changes:\n  .zero 8\n" ++
  -- Producer-side diagnostic cells for the balance/nonce row-population gap.
  -- The ten `bv_bal_shadow_emit_*` counters above are all EMIT-side, downstream
  -- of every candidate cause, so they measure the composition and localise
  -- nothing.  These four per component stage the pipeline instead:
  --
  --   `_bit_set`        producer bit observed at the consumer (`s8` mask bit
  --                     0 = balance, 1 = nonce), per account-loop iteration.
  --   `_differs`        the change-compare against the resolver baseline found
  --                     inequality, so `bal_builder_append_*` was CALLED.
  --   `_builder_count`  `bal_builder_*_count` snapshotted at the point the
  --                     emitter starts -- rows that actually landed in the
  --                     builder array, so an append that overflowed or a
  --                     builder reset between produce and emit is visible.
  --   `_cmp_attempts`   emitter address-filter comparisons attempted, i.e.
  --                     (rows in builder) x (accounts the emit loop visited).
  --
  -- Adjacent differences localise one stage each: bit_set->differs is the
  -- compare, differs->builder_count is the append, builder_count->emit is the
  -- address filter, and cmp_attempts separates "the filter rejected the row"
  -- from "the account loop never offered it".  All-zero groups are promoted to
  -- `.bss` by `Layout.moveZeroDataLines`, so this adds no `.data` bytes and
  -- shifts no address-pinned `.data` symbol.
  "bald_bal_bit_set:\n  .zero 8\n" ++
  "bald_bal_differs:\n  .zero 8\n" ++
  "bald_bal_builder_count:\n  .zero 8\n" ++
  "bald_bal_cmp_attempts:\n  .zero 8\n" ++
  "bald_non_bit_set:\n  .zero 8\n" ++
  "bald_non_differs:\n  .zero 8\n" ++
  "bald_non_builder_count:\n  .zero 8\n" ++
  "bald_non_cmp_attempts:\n  .zero 8\n" ++
  -- Witness cells.  The four staging cells above give COUNTS, and a count cannot
  -- distinguish "the two second rows of the multi-row accounts were lost" from
  -- "the two single-row accounts were lost" -- both predict differs = 4 of 6 on
  -- `bal_2935_simple`, whose six declared balance rows are four accounts, two of
  -- them carrying rows at both block_access_index 1 and 2.
  --
  --   `_eq_bai_mask`  bit `bai` set for every (address, bai) iteration whose
  --                   change-compare found EQUALITY, i.e. the lost rows.
  --   `_ne_bai_mask`  the same for iterations that appended, i.e. the working
  --                   rows.  Together the two masks partition every mask-set
  --                   iteration by bai, so the working rows are a differential
  --                   control rather than an inference.
  --   `_eq_val_lo/hi` the two compared limbs on an equal row (they are equal by
  --                   construction, so one value; publishing it distinguishes
  --                   "both sides zero, nothing populated" from "the pre side
  --                   already carries the post value").
  --
  -- The masks use `sll` by bai, whose RV64 shift amount is the low 6 bits, so a
  -- bai of 64 or more ALIASES onto a low bit.  Sound for these fixtures (bai is
  -- 1..2 here) and a diagnostic-only limitation, not a silent one.
  "bald_bal_eq_bai_mask:\n  .zero 8\n" ++
  "bald_bal_ne_bai_mask:\n  .zero 8\n" ++
  "bald_bal_eq_val_lo:\n  .zero 8\n" ++
  "bald_bal_eq_val_hi:\n  .zero 8\n" ++
  "bald_non_eq_bai_mask:\n  .zero 8\n" ++
  "bald_non_ne_bai_mask:\n  .zero 8\n" ++
  "bald_non_eq_val_pre:\n  .zero 8\n" ++
  "bald_non_eq_val_post:\n  .zero 8\n" ++
  -- Address witness, BALANCE ONLY.  The bai masks establish that the lost rows are
  -- per-account and not per-index, so naming the account is the last step before a
  -- fix site: if the stale-post account is a credit RECIPIENT (tx recipient,
  -- coinbase fee, withdrawal) then this deficit and the #10786 EOA-credit producer
  -- gap are one defect; if it is an ordinary sender they are separate.
  -- Bytes 0..15 of the 20-byte canonical address at `0(s4)`, which is more than
  -- enough to discriminate the four accounts in these fixtures.
  --
  -- NOT mirrored for nonce on purpose: the nonce reading is UNIFORM (both operands
  -- zero on every iteration of every fixture), so an address cannot discriminate
  -- anything there and the cell would only look like coverage.
  "bald_bal_eq_addr_a:\n  .zero 8\n" ++
  "bald_bal_eq_addr_b:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "bv_bal_shadow_scratch:\n  .zero 40\n" ++
  "bv_tx_off:\n  .zero 8\n" ++
  "bv_tx_list_ptr:\n  .zero 8\nbv_tx_list_len:\n  .zero 8\nbv_tx_count:\n  .zero 8\nbv_tx_index:\n  .zero 8\nbv_tx_item_start:\n  .zero 8\n" ++
  "bv_public_keys_ptr:\n  .zero 8\n" ++
  "bv_public_keys_len:\n  .zero 8\n" ++
  "bv_fail_code:\n  .zero 8\n" ++
  "bv_header_status:\n  .zero 8\n" ++
  "bv_state_status:\n  .zero 8\n" ++
  "bv_tx_root_status:\n  .zero 8\n" ++
  "bv_block_rlp_len:\n  .zero 8\n" ++
  "bv_blockhash_required_headers:\n  .zero 8\n" ++
  "bv_versioned_hashes_len:\n  .zero 8\n" ++
  "bv_blob_gas_expected:\n  .zero 8\n" ++
  "bv_blob_gas_observed:\n  .zero 8\n" ++
  "bv_withdrawals_root_status:\n  .zero 8\n" ++
  "bv_withdrawals_root_valid:\n  .zero 8\n" ++
  "brr_status:\n  .zero 8\n" ++
  "brr_append_status:\n  .zero 8\n" ++
  "brr_tx_type:\n  .zero 8\n" ++
  "brr_tx_inner:\n  .zero 8\n" ++
  "brr_tx_gas:\n  .zero 8\n" ++
  "brr_receipt_gas_ptr:\n  .zero 8\n" ++
  "brr_receipt_gas_count:\n  .zero 8\n" ++
  -- .63.1.6.2.1: per-tx execution-status plumbing. bv_tx_status_arr holds the
  -- dispatcher_tx_gas_settle success bit per tx (single-tx path writes index 0,
  -- the mtx loop index i); brr_tx_status_ptr is the materializer's saved arg.
  "brr_tx_status_ptr:\n  .zero 8\n" ++
  "bv_tx_status_arr:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  -- xbi56.2: per-tx creation-error refund eligibility flag parallel to
  -- bv_tx_status_arr, used by the EIP-8037 tx-error state-gas rule when
  -- materializing exact block state gas.
  "bv_tx_is_creation_arr:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  -- .63.1.6.2.1: block-level log arena + per-tx windows. Each dispatch call
  -- resets/overwrites the capture buffers, so block_log_window_snapshot copies
  -- every tx's descriptors (256 B each, 128 cap) + data bytes (64 KiB cap,
  -- offsets rebased into bv_block_log_meta) out between dispatches.
  -- bv_record_* and bv_logs_rlp_arena carry the per-record logs RLP + blooms
  -- (block_receipt_logs_materialize), in the {bloom,rlp,len} shape
  -- receipt_records_encode_no_logs consumes via record@56.
  "brr_tx_window_ptr:\n  .zero 8\n" ++
  "bv_block_log_count:\n  .zero 8\n" ++
  "bv_block_log_data_used:\n  .zero 8\n" ++
  "bv_block_log_desc_used:\n  .zero 8\n" ++
  "bv_block_log_overflow:\n  .zero 8\n" ++
  "bv_last_log_start:\n  .zero 8\n" ++
  "bv_last_log_count:\n  .zero 8\n" ++
  "bv_receipt_logs_status:\n  .zero 8\n" ++
  "bv_logs_rlp_len:\n  .zero 8\n" ++
  "bv_logs_rlp_arena_used:\n  .zero 8\n" ++
  "bv_tx_log_window:\n  .zero " ++ toString bvMtxLogWindowBytes ++ "\n" ++
  ".balign 8\n" ++
  "bv_block_log_descs:\n  .zero " ++ toString bvBlockLogDescBytes ++ "\n" ++
  "bv_block_log_meta:\n  .zero " ++ toString bvBlockLogMetaBytes ++ "\n" ++
  "bv_block_log_data:\n  .zero " ++ toString bvBlockLogDataBytes ++ "\n" ++
  "bv_logs_rlp_arena:\n  .zero " ++ toString bvLogsRlpArenaBytes ++ "\n" ++
  "bv_record_blooms:\n  .zero " ++ toString bvRecordBloomsBytes ++ "\n" ++
  "bv_record_logs_desc:\n  .zero " ++ toString bvRecordLogsDescBytes ++ "\n" ++
  -- .63.1.6.2.3: encoded full-receipt RLP list plus encoder scratch.
  -- Output/scratch overflow is capacity debt and remains conservative unless a
  -- later slice proves a supported in-capacity semantic mismatch.
  "bv_receipts_rlp:\n  .zero " ++ toString bvReceiptsRlpBytes ++ "\n" ++
  "bv_receipts_rlp_len:\n  .zero 8\n" ++
  -- Status returned by receipt_records_encode_no_logs in the receipts tail:
  -- 0 success, 1 malformed/count over capacity, 2 missing logs descriptor,
  -- 3 output/scratch overflow, 4 unsupported tx type.
  "bv_receipts_encoder_status:\n  .zero 8\n" ++
  -- Status returned by block_validate_receipts_consensus_list in the receipts tail:
  -- 0 success, 1 receipts-root helper failure, 2 receipts-root mismatch,
  -- 3 logs-bloom helper failure, 4 logs-bloom mismatch.
  "bv_receipts_validator_status:\n  .zero 8\n" ++
  -- .63.1.6.2.3: receipt_encode + receipt_records_encode_no_logs scratch.
  -- Live materialize uses brr_control/brr_records below. Old rle_control/rle_records
  -- twin was never referenced from production (migration leftover; probe
  -- ReceiptList.lean keeps local rle_*). KEEP encoder scratch below.
  ".balign 8\n" ++
  "rle_field_len:\n  .zero 8\n" ++
  "rle_prefix_len:\n  .zero 8\n" ++
  "re_field_len:\n  .zero 8\n" ++
  "re_cursor:\n  .zero 8\n" ++
  "re_total_payload:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "rle_empty_logs:\n  .byte 0xc0\n" ++
  ".balign 8\n" ++
  "rle_zero_bloom:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "re_payload_buf:\n  .zero " ++ toString bvReceiptEncodePayloadBytes ++ "\n" ++
  ".balign 8\n" ++
  "rle_payload_buf:\n  .zero " ++ toString bvReceiptListPayloadBytes ++ "\n" ++
  -- .63.1.6.2.3: block_validate_logs_bloom + block_logs_bloom_from_receipts_list scratch
  -- (helb_offset/helb_length are already linked via header_extract_logs_bloom).
  ".balign 8\n" ++
  "relb_offset:\n  .zero 8\n" ++
  "relb_length:\n  .zero 8\n" ++
  "blbr_count:\n  .zero 8\n" ++
  "blbr_offset:\n  .zero 8\n" ++
  "blbr_length:\n  .zero 8\n" ++
  "blbr_next_offset:\n  .zero 8\n" ++
  "blbr_next_length:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "blbr_scratch_bloom:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "bvlb_header_bloom:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "bvlb_computed_bloom:\n  .zero 256\n" ++
  -- .63.1.6.2.3: block_validate_receipts_consensus_list scratch (the indexed-trie/root and
  -- logs-bloom sub-scratch are already linked above / via the no-tx receipts path).
  ".balign 8\n" ++
  "brcl_count:\n  .zero 8\n" ++
  "brcl_offset:\n  .zero 8\n" ++
  "brcl_length:\n  .zero 8\n" ++
  "brcl_next_offset:\n  .zero 8\n" ++
  "brcl_next_length:\n  .zero 8\n" ++
  "brcl_root_valid:\n  .zero 8\n" ++
  "brcl_bloom_valid:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "brcl_value_descs:\n  .zero " ++ toString bvReceiptConsensusDescBytes ++ "\n" ++
  -- scratch for log_records_encode_rlp (lrr_*) and the bloom accumulators
  -- (bav_/lba_/llba_ — zk3_state is already defined by the guest).
  logRecordsRlpDataSection ++
  "bav_hash:\n  .zero 32\n" ++
  "lba_offset:\n  .zero 8\n" ++
  "lba_length:\n  .zero 8\n" ++
  "lba_topics_offset:\n  .zero 8\n" ++
  "lba_topics_length:\n  .zero 8\n" ++
  "lba_topic_count:\n  .zero 8\n" ++
  "llba_offset:\n  .zero 8\n" ++
  "llba_length:\n  .zero 8\n" ++
  "llba_count:\n  .zero 8\n" ++
  -- KEEP-list brr_*: live receipt materialize (block_receipt_records_materialize).
  "brr_control:\n  .zero 24\n" ++
  ".balign 8\n" ++
  "brr_records:\n  .zero " ++ toString bvReceiptRecordsBytes ++ "\n" ++
  "hewr_offset:\n  .zero 8\n" ++
  "hewr_length:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bvwri_expected_root:\n  .zero 32\n" ++
  "bvwri_computed_root:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "itr_empty_witness:\n  .zero 8\n" ++
  -- itr_value_descs was probe-only; production uses external descs + itr_paths/changes.
  -- Probe MptIndexedTrieRoot.lean keeps a local itr_value_descs.
  "itr_paths:\n  .zero " ++ toString (itrIndexedEntryCapacity * 8) ++ "\n" ++
  "itr_changes:\n  .zero " ++ toString (itrIndexedEntryCapacity * 40) ++ "\n" ++
  "itr_sort_ranges:\n  .zero " ++ toString (itrIndexedSortRangeStackCapacity * 32) ++ "\n" ++
  "itr_sort_scratch:\n  .zero 40\n" ++
  "itr_builder_node_len:\n  .zero 8\n" ++
  "itr_builder_node:\n  .zero 1024\n" ++
  "itr_builder_frames:\n  .zero " ++ toString (itrIndexedBuilderFrameCapacity * 1024) ++ "\n" ++
  "itr_root_ref_len:\n  .zero 8\n" ++
  "itr_root_ref:\n  .zero 32\n" ++
  -- .63.1.6.2.3: receipts-consensus scratch (mirrors the hewr_/bvwri_ withdrawals
  -- pair above). herr_/helb_ are header field-extraction cursors; bvrri_* the
  -- expected/computed receipts roots + per-receipt {ptr,len} descriptors (16 B ×
  -- 128, same cap as mpt_indexed_trie_root_small); bv_header_bloom /
  -- bv_zero_bloom / bv_bloom_eq_out drive the header.logs_bloom compare.
  "herr_offset:\n  .zero 8\n" ++
  "herr_length:\n  .zero 8\n" ++
  "helb_offset:\n  .zero 8\n" ++
  "helb_length:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bvrri_expected_root:\n  .zero 32\n" ++
  "bvrri_computed_root:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bvrri_value_descs:\n  .zero " ++ toString bvReceiptConsensusDescBytes ++ "\n" ++
  ".balign 8\n" ++
  "bv_header_bloom:\n  .zero 256\n" ++
  "bv_zero_bloom:\n  .zero 256\n" ++
  "bv_bloom_eq_out:\n  .zero 8\n" ++
  "bvgr_runtime_gas_left_ptr:\n  .zero 8\n" ++
  "bvgr_runtime_refund_counter_ptr:\n  .zero 8\n" ++
  "bvgr_runtime_calldata_floor_ptr:\n  .zero 8\n" ++
  "bvgr_runtime_count:\n  .zero 8\n" ++
  ".balign 8\n" ++
  -- bmvmx.1.7.2: sized to fit a max EIP-170 contract (round8(24576)) + the
  -- 584-byte env/gas trailer + headroom for calldata and the
  -- future M29 blockhash table (.3b). dispatch_tx_runtime_code's .Ldtrc_stage guard bails
  -- conservatively for any payload that would still exceed this, so the staging write can
  -- never overflow into the adjacent gas-result / bvcd_* cells.
  "bv_runtime_payload:\n  .zero " ++ toString (bsrAccountSlotCap * 64 + 65536) ++ "\n" ++   -- 4jczt class-B BAL>128 lift: hold storage*64 at the gas-derived bsrAccountSlotCap (6.4MB) + the original 65536 code/calldata/witness/584 headroom (calldata/witness worst case stays bmvmx.1.7.2's payload-cap concern). .data headroom verified ~62MB (dataBase 0xa3000000 -> sszScratchBase 0xbf600000).
  "bv_stop_code:\n  .byte 0x00\n" ++
  ".balign 8\n" ++
  "bv_runtime_gas_left:\n  .zero 8\n" ++
  "bv_runtime_refund_counter:\n  .zero 8\n" ++
  "bv_runtime_calldata_floor:\n  .zero 8\n" ++
  "bv_runtime_intrinsic_state_gas:\n  .zero 8\n" ++
  -- Last dispatch_tx_runtime_code status: 0 success; 1 code lookup; 2 non-self-contained;
  -- 3 BAL/account/key cap; 4 storage proof/slot lookup; 5 payload cap; 6 staging;
  -- 7 access-list unsupported/parse/count. Nonzero still means conservative bail.
  "bv_dispatch_runtime_status:\n  .zero 8\n" ++
  -- Runtime-gas completeness classifier: 0 complete/unknown, 1 gas-result arena tx/count/cap,
  -- 2 runtime_count/pointer mismatch, 3 single-tx dispatch unsupported,
  -- 4 multi-tx dispatch unsupported, 5 multi-tx generic bail. Nonzero is debug-only.
  "bv_runtime_completeness_status:\n  .zero 8\n" ++
  -- Contract-recipient dispatch scratch (evm-asm-fhsxz.2.4.2.57.11.6.4.3.2).
  -- GH #11176: bvcd_keys (3,200,000 B) and bvcd_preload (6,400,000 B) plus the
  -- bvcd_key_count / bvcd_sc_count / bvcd_i cursors are GONE with the eager recipient
  -- storage preload -- 9,600,024 B = 9.155 MiB of .bss. bvcd_acct_ptr / bvcd_acct_len
  -- REMAIN: bal_find_account_by_address still writes them for the parse-validity bail.
  ".balign 8\n" ++
  "bvcd_code_ptr:\n  .zero 8\n" ++
  "bvcd_code_len:\n  .zero 8\n" ++
  "bvcd_acct_ptr:\n  .zero 8\n" ++
  "bvcd_acct_len:\n  .zero 8\n" ++
  -- bmvmx.1.6.2 bal_storage_change_values scratch (tuple path). matches/covers/allaccounts data unlinked #10681.
  balStorageChangeValuesData ++
  -- #11118: bacov_*/bsr_krev guest data removed with dead code_covers (43) and reads (38).
  -- bmvmx.1.6.3 recipient nonce/code-change emptiness probe (rlp_list_nth_item out cells).
  "bv_rcf_off:\n  .zero 8\n" ++
  "bv_rcf_len:\n  .zero 8\n" ++
  -- The recipient SELFBALANCE resolver still writes the account decode scratch;
  -- F3 retirement removes only the eager BAL-account tables around it.
  ".balign 8\n" ++
  "csce_bal_struct:\n  .zero 104\n" ++

  "bv_eip7778_status:\n  .zero 8\n" ++
  "bv_eip7778_index:\n  .zero 8\n" ++
  "bv_eip7778_used:\n  .zero 8\n" ++
  "bvgr_status:\n  .zero 8\n" ++
  "bvgr_count:\n  .zero 8\n" ++
  "bvgr_fail_index:\n  .zero 8\n" ++
  "bvgr_tx_type:\n  .zero 8\n" ++
  "bvgr_tx_inner:\n  .zero 8\n" ++
  "bvgr_nonce:\n  .zero 8\n" ++
  "bvgr_gas:\n  .zero 8\n" ++
  "bvgr_arena_status:\n  .zero 8\n" ++
  "bvgr_arena_tx_count:\n  .zero 8\n" ++
  "bvgr_arena_runtime_count:\n  .zero 8\n" ++
  "bvgr_arena_fail_index:\n  .zero 8\n" ++
  "bvgr_arena_substatus:\n  .zero 8\n" ++
  "bvgr_tx_gas_limits:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bvgr_gas_left:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bvgr_refund_counter:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bvgr_calldata_floor:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bvgr_block_gas_increments:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  -- g8zeq.1.4.3: per-tx EIP-8037 intrinsic/auth state-gas array, the state
  -- counterpart of bvgr_block_gas_increments.  The live transaction boundary
  -- writes it before runtime dispatch; the common gas gate consumes it later.
  "bvgr_tx_state_gas:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  -- fhsxz.2.4.2.57.11.6.5.2.1 P1: per-tx EXECUTED state gas (net of refunds), filled by
  -- dispatcher_capture_exec_state_gas at each contract dispatch (mirrors
  -- bvgr_tx_state_gas). Behavior-neutral substrate for the 2D state-dim (P3 reads it).
  "bvgr_tx_exec_state_gas:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  -- xbi56.1: exact net EIP-8037 tx_state_gas = intrinsic + executed - refund,
  -- with transaction error rules applied. Populated after runtime gas results.
  "bvgr_tx_total_state_gas:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  -- xbi56.2: EIP-8037 state-refund input was never wired from production text
  -- (full bvMtxU64ArenaBytes twin of bvgr_tx_state_gas was orphaned). KEEP other
  -- bvgr_*: block_gas_increments, tx_state_gas, tx_exec_state_gas, tx_total_state_gas,
  -- tx_predelegated_auth_count, receipt_gas_increments, before/applied_refund.
  -- CreateCollision.lean still names a scalar cell under this label when that
  -- branch is linked; keep an 8-byte placeholder so the name resolves.
  "bvgr_tx_state_refund:\n  .zero 8\n" ++
  -- Per-tx count of EIP-7702 authorities whose pre-state code was already a
  -- delegation marker. The inline transaction-boundary helper uses this
  -- accounting context when materializing auth state gas.
  "bvgr_tx_predelegated_auth_count:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  -- Preserve the settled-prefix block gas across `bgv_u64le` while checking
  -- whether a following CREATE transaction fits the remaining 2D budget.
  "bv_mtx_creation_prefix_used:\n  .zero 8\n" ++
  "bv_exact_header_gas_used:\n  .zero 8\n" ++
  "bv_exact_expected_gas_used:\n  .zero 8\n" ++
  "bv_exact_net_status:\n  .zero 8\n" ++
  "bv_exact_net_index:\n  .zero 8\n" ++
  "bv_exact_block_status:\n  .zero 8\n" ++
  "bvgr_receipt_gas_increments:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bvgr_before_refund:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bvgr_applied_refund:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  -- EIP-7702 authenticated-header lookup scratch retained by the live inline
  -- authority/account-state helpers.
  "teer_type:\n  .zero 8\n" ++
  "teer_inner_off:\n  .zero 8\n" ++
  "teer_auth_off:\n  .zero 8\n" ++
  "teer_auth_len:\n  .zero 8\n" ++
  "teer_auth_count:\n  .zero 8\n" ++
  "teer_regular_refund:\n  .zero 8\n" ++
  "teer_predelegated_count:\n  .zero 8\n" ++
  "teer_existing_count:\n  .zero 8\n" ++
  "teer_records_ptr:\n  .zero 8\n" ++
  "teer_tuple_off:\n  .zero 8\n" ++
  "teer_tuple_len:\n  .zero 8\n" ++
  "teer_target_off:\n  .zero 8\n" ++
  "teer_target_len:\n  .zero 8\n" ++
  "teer_auth_chain:\n  .zero 8\n" ++
  "teer_auth_nonce:\n  .zero 8\n" ++
  "teer_invalid_auth_count:\n  .zero 8\n" ++
  "teer_recipient_ptr:\n  .zero 8\n" ++
  "teer_recipient_len:\n  .zero 8\n" ++
  "teer_value_nonzero:\n  .zero 8\n" ++
  "teer_prior_count:\n  .zero 8\n" ++
  "teer_prior_set_flag:\n  .zero 8\n" ++
  "teer_acct_absent:\n  .zero 8\n" ++
  "teer_rolled_back:\n  .zero 8\n" ++
  "teer_wouldbe_state:\n  .zero 8\n" ++
  "teer_wouldbe_regular:\n  .zero 8\n" ++
  "teer_first_nonce:\n  .zero 8\n" ++
  -- Keep the EIP-7702 authority as a full padded non-storage-effect key.
  "teer_authority:\n  .zero 32\n" ++
  "teer_first_authority:\n  .zero 24\n" ++
  ".balign 8\n" ++
  "teer_recover_scratch:\n  .zero 360\n" ++
  "teer_acct_ptr:\n  .zero 8\n" ++
  "teer_acct_len:\n  .zero 8\n" ++
  "teer_finals:\n  .zero 88\n" ++
  "teer_pre_acct:\n  .zero 104\n" ++
  -- coc3g.5 multi-hop: eip7702_warm_recovered_authorities private scratch.
  ".balign 8\n" ++
  "e77w_count:\n  .zero 8\n" ++
  "e77w_toff:\n  .zero 8\n" ++
  "e77w_tlen:\n  .zero 8\n" ++
  "e77w_chain:\n  .zero 8\n" ++
  "e77w_nonce:\n  .zero 8\n" ++
  "e77w_authority:\n  .zero 24\n" ++
  ".balign 8\n" ++
  "e77w_scratch:\n  .zero 360\n" ++
  "a77ra_cmp:\n  .zero 8\n" ++
  "a77ra_secp256k1_n:\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfe\n" ++
  "  .byte 0xba,0xae,0xdc,0xe6,0xaf,0x48,0xa0,0x3b\n" ++
  "  .byte 0xbf,0xd2,0x5e,0x8c,0xd0,0x36,0x41,0x41\n" ++
  "a77ra_secp256k1_half_n:\n" ++
  "  .byte 0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0x5d,0x57,0x6e,0x73,0x57,0xa4,0x50,0x1d\n" ++
  "  .byte 0xdf,0xe9,0x2f,0x46,0x68,0x1b,0x20,0xa0\n" ++
  "ta77es_offset:\n  .zero 8\n" ++
  "ta77es_length:\n  .zero 8\n" ++
  blockVerdictTxGasPrechargeDataSection ++
  ".balign 8\n" ++
  -- uyu11.1: EIP-4895 withdrawal-aware credit scratch for the coinbase/recipient
  -- post-balance checks + the bv_sum_withdrawals_to_address accumulator.
  "strv_wd_credit:\n  .zero 32\n" ++
  "stfv_wd_credit:\n  .zero 32\n" ++
  "bsw_amount:\n  .zero 32\n" ++
  "bsw_wei:\n  .zero 32\n" ++
  -- 7rbp3: authenticated EIP-4895 withdrawal -> nonstorage-effect producer scratch.
  ".balign 32\n" ++
  "bv_wdne_addr:\n  .zero 32\n" ++
  "bv_wdne_acct:\n  .zero 104\n" ++
  "bv_wdne_post:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "strv_count:\n  .zero 8\n" ++
  "strv_row_off:\n  .zero 8\n" ++
  "strv_row_len:\n  .zero 8\n" ++
  "strv_addr_off:\n  .zero 8\n" ++
  "strv_addr_len:\n  .zero 8\n" ++
  "strv_post_len:\n  .zero 8\n" ++
  "strv_nonce_len:\n  .zero 8\n" ++
  "stfv_count:\n  .zero 8\n" ++
  "stfv_row_off:\n  .zero 8\n" ++
  "stfv_row_len:\n  .zero 8\n" ++
  "stfv_addr_off:\n  .zero 8\n" ++
  "stfv_addr_len:\n  .zero 8\n" ++
  "stfv_post_len:\n  .zero 8\n" ++
  "stfv_nonce_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "strv_post_raw:\n  .zero 32\n" ++
  "strv_nonce_raw:\n  .zero 32\n" ++
  "stfv_effective_gas_price:\n  .zero 32\n" ++
  "stfv_post_raw:\n  .zero 32\n" ++
  "stfv_nonce_raw:\n  .zero 32\n" ++
  ".balign 8\n" ++
  ".balign 8\n" ++
  "tvhm_tx_type:\n  .zero 8\n" ++
  "tvhm_inner_off:\n  .zero 8\n" ++
  "tvhm_blob_count:\n  .zero 8\n" ++
  "tvhm_blob_index:\n  .zero 8\n" ++
  "tvhm_hash_off:\n  .zero 8\n" ++
  "tvhm_hash_len:\n  .zero 8\n" ++
  "tvhm_struct:\n  .zero 248\n" ++
  ".balign 32\n" ++
  "afp_digest:\n  .zero 32\n" ++
  "brl_item_start:\n  .zero 8\n" ++
  "brl_item_end:\n  .zero 8\n" ++
  "brl_wd_len:\n  .zero 8\n" ++
  "brl_wd_buf:\n  .zero 72\n" ++
  "svf_witness_section:\n  .zero 8\n" ++
  "svf_witness_end:\n  .zero 8\n" ++
  "svf_codes_ptr:\n  .zero 8\n" ++
  "svf_codes_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "wclh_scratch_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "svf_headers_ptr:\n  .zero 8\n" ++
  "svf_headers_len:\n  .zero 8\n" ++
  -- 8uld3.2.3.3.1 (C.1): scratch for execution-derived withdrawal+consolidation requests_hash.
  ".balign 8\n" ++
  "c1_saved_logcount:\n  .zero 8\n" ++
  "c1_system_log_cursor:\n  .zero 8\n" ++
  -- bmvmx.5.5.1.2.1.3.1.1: side arena for system-call SSTORE rows.
  -- The system-call derives append to the regular storage log, then the verdict
  -- restores evm_env+448 so user storage/nonstorage comparators preserve their
  -- current behavior. Capture those erased rows here with txindex=0 for the
  -- follow-up tuple-merge comparator.
  "bv_system_storage_log_count:\n  .zero 8\n" ++
  -- Set only around the pre-user descriptor pass: reuse the row conversion
  -- without emitting a duplicate side-log/BAL event before terminal replay.
  "bv_system_storage_map_seed_only:\n  .zero 8\n" ++
  "bv_system_storage_txindex:\n  .zero " ++ toString bvSystemStorageTxindexBytes ++ "\n" ++
  -- 4ch8f.73: bv_system_storage_log is a STANDALONE .data region (NOT unioned into
  -- call_frame_arena). The former ~77 MiB union placement was UNSOUND: the audit's
  -- claimed "dead during Phase-D dispatch" was false — the syslog is WRITTEN
  -- pre-dispatch (capture_system_storage_exec_rows) but READ POST-dispatch by the
  -- BAL validators (bal_storage_matches_exec_log @BlockVerdictFunction:972,
  -- bal_storage_covers_exec_log :984, account_tuple_sequences_consistent :1135),
  -- while per-tx dispatch frames at depth ≥ 221 physically zero the union front
  -- (call_frame_arena + (d-1)*0x39000 covers the syslog extent). Reservation was
  -- also tightened from the unreachable gas bound (600000 rows) to
  -- bvSystemStorageLogCapacity (= 2 * runtime exec-log cap 16384; see
  -- BlockVerdictParams) so the standalone region is only 4 MiB and fits the .data
  -- headroom. Disjointness from every frame slot: syslog_disjoint_from_frameArena
  -- (RegionMap.lean).
  ".balign 32\n" ++
  "bv_system_storage_log:\n  .zero " ++ toString bvSystemStorageLogBytes ++ "\n" ++
  ".balign 8\n" ++
  "bv_system_storage_capture_status:\n  .zero 8\n" ++
  "bv_system_storage_capture_start:\n  .zero 8\n" ++
  "bv_system_storage_capture_end:\n  .zero 8\n" ++
  "bv_system_storage_capture_rows:\n  .zero 8\n" ++
  "bv_system_storage_capture_old_count:\n  .zero 8\n" ++
  "bv_system_storage_capture_new_count:\n  .zero 8\n" ++
  "cssc_stamp_txindex:\n  .zero 8\n" ++       -- lv44p.2.2: block_access_index stamped into captured system rows
  -- bmvmx.5.5.10 PR-2: per-tx USER-write side arena. The live exec log only holds
  -- the LAST dispatch's rows (each dispatch resets persistentLogLength), so the
  -- mtx loop captures each tx's surviving SSTORE rows here (same 128-byte layout,
  -- txindex = block_access_index i+1) for the forward BAL storage comparator.
  -- Standalone region, same disjointness argument as bv_system_storage_log.
  "bv_user_storage_log_count:\n  .zero 8\n" ++
  "bv_user_storage_txindex:\n  .zero " ++ toString bvUserStorageTxindexBytes ++ "\n" ++
  ".balign 32\n" ++
  "bv_user_storage_log:\n  .zero " ++ toString bvUserStorageLogBytes ++ "\n" ++
  ".balign 8\n" ++
  "c1_wcode_ptr:\n  .zero 8\n" ++
  "c1_wcode_len:\n  .zero 8\n" ++
  "c1_er_input:\n  .zero 8\n" ++
  ".balign 8\n" ++
  -- Fix7: system-call payload = env_base+504; env_base grows with M29 block hashes.
  -- The request predeploy's storage is resolved by the authenticated state path.
  -- fhsxz.2.4.2.66.1: 32768 overflowed for the system_contract_errors EEST predeploys
  -- (modified 7002/7251 contracts of 72946 B; predeploy code is NOT EIP-170-bounded):
  -- stage_runtime_payload_code's zero+code copy ran ~40 KiB past the buffer, smashing
  -- every .data global above (c1_saved_*, dbsr_*, rlp args) -> ERROR(exit)/false-reject.
  -- .66.1.2: sized by the shared c1StagingBytes constant (BlockVerdictParams.lean) =
  -- bsrMaxWitnessBytes + bsrAccountSlotCap*64 + 16384 — fits round8(code <= witness cap)
  -- + the conservative shared headroom + M29 + 584. The size guard in stage_system_call_payload
  -- (SystemCallStaging.lean) uses the same constant and bails on anything larger
  -- instead of corrupting .data.
  "c1_staging:\n  .zero " ++ toString c1StagingBytes ++ "\n" ++
  ".balign 8\n" ++
  "c1_er_assembled:\n  .zero " ++ toString bvMaxExecutionRequestSectionBytes ++ "\n" ++
  "c1_er_assembled_len:\n  .zero 8\n" ++
  "c1_erh_status:\n  .zero 8\n" ++
  "c1_notx_deposit_body_len:\n  .zero 8\n" ++
  "c1_dstatus:\n  .zero 8\n" ++
  "c1_dlen:\n  .zero 8\n" ++
  "c1_dbody:\n  .zero " ++ toString bvMaxDepositRequestBodyBytes ++ "\n" ++
  "c1_log_records:\n  .zero " ++ toString bvMaxDepositLogRecordBytes ++ "\n" ++
  "c1_ccode_ptr:\n  .zero 8\n" ++
  "c1_ccode_len:\n  .zero 8\n" ++
  "c1_bd_code_ptr:\n  .zero 8\n" ++
  "c1_bd_code_len:\n  .zero 8\n" ++
  "c1_be_code_ptr:\n  .zero 8\n" ++
  "c1_be_code_len:\n  .zero 8\n" ++
  "c1_bal_acct_ptr:\n  .zero 8\n" ++
  "c1_bal_acct_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "c1_bal_start:\n  .zero 8\n" ++
  "c1_bal_len:\n  .zero 8\n" ++
  "c1_bal_count:\n  .zero 8\n" ++
  "c1_saved_s0:\n  .zero 8\n" ++
  "c1_saved_s3:\n  .zero 8\n" ++
  "svf_headers_count:\n  .zero 8\n" ++
  "bbcv_count:\n  .zero 8\n" ++
  "bbcv_off:\n  .zero 8\n" ++
  "bbcv_size:\n  .zero 8\n" ++
  "bbcv_acct_len:\n  .zero 8\n" ++
  "bbcv_addr_off:\n  .zero 8\n" ++
  "bbcv_addr_len:\n  .zero 8\n" ++
  "bbcv_acct_struct:\n  .zero 104\n" ++
  "aahsr_state_root:\n  .zero 32\n" ++
  "bbcv_field_off:\n  .zero 8\n" ++
  "bbcv_field_len:\n  .zero 8\n" ++
  "bbcv_field_count:\n  .zero 8\n" ++
  "bbcv_balance_count:\n  .zero 8\n" ++
  "bbcv_nonce_count:\n  .zero 8\n" ++
  "bbcv_skip_touch_only:\n  .zero 8\n" ++
  "bbcv_touch_only:\n  .zero 8\n" ++
  "bbcv_fee_recipient_valid:\n  .zero 8\n.balign 8\nbbcv_fee_recipient:\n  .zero 20\n" ++
  ".balign 32\n" ++
  "bbcv_sys_2935:\n" ++
  "  .byte 0x00, 0x00, 0xf9, 0x08, 0x27, 0xf1, 0xc5, 0x3a\n" ++
  "  .byte 0x10, 0xcb, 0x7a, 0x02, 0x33, 0x5b, 0x17, 0x53\n" ++
  "  .byte 0x20, 0x00, 0x29, 0x35\n" ++
  "bbcv_sys_4788:\n" ++
  "  .byte 0x00, 0x0f, 0x3d, 0xf6, 0xd7, 0x32, 0x80, 0x7e\n" ++
  "  .byte 0xf1, 0x31, 0x9f, 0xb7, 0xb8, 0xbb, 0x85, 0x22\n" ++
  "  .byte 0xd0, 0xbe, 0xac, 0x02\n" ++
  "bbcv_sys_7002:\n" ++
  "  .byte 0x00, 0x00, 0x09, 0x61, 0xef, 0x48, 0x0e, 0xb5\n" ++
  "  .byte 0x5e, 0x80, 0xd1, 0x9a, 0xd8, 0x35, 0x79, 0xa6\n" ++
  "  .byte 0x4c, 0x00, 0x70, 0x02\n" ++
  "bbcv_sys_7251:\n" ++
  "  .byte 0x00, 0x00, 0xbb, 0xdd, 0xc7, 0xce, 0x48, 0x86\n" ++
  "  .byte 0x42, 0xfb, 0x57, 0x9f, 0x8b, 0x00, 0xf3, 0xa5\n" ++
  "  .byte 0x90, 0x00, 0x72, 0x51\n" ++
  "bbcv_sys_6110:\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x21, 0x9a, 0xb5, 0x40\n" ++
  "  .byte 0x35, 0x6c, 0xbb, 0x83, 0x9c, 0xbe, 0x05, 0x30\n" ++
  "  .byte 0x3d, 0x77, 0x05, 0xfa\n" ++
  "bbcv_sys_system:\n" ++
  "  .byte 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff\n" ++
  "  .byte 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff\n" ++
  "  .byte 0xff, 0xff, 0xff, 0xfe\n" ++
  ".balign 32\n" ++
  "bbcv_code_hash:\n  .zero 32\n" ++
  "bbcv_delegated_code_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bbcv_code_off:\n  .zero 8\n" ++
  "bbcv_code_len:\n  .zero 8\n" ++
  "bbcv_scan_count:\n  .zero 8\n" ++
  "bbcv_scan_off:\n  .zero 8\n" ++
  "bbcv_scan_size:\n  .zero 8\n" ++
  "bbcv_scan_addr_off:\n  .zero 8\n" ++
  "bbcv_scan_addr_len:\n  .zero 8\n" ++
  "bv_cf_code_off:\n  .zero 8\n" ++
  "bv_cf_code_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bv_tx_recipient_code_hash:\n  .zero 32\n" ++
  "bv_create_addr:\n  .zero 32\n" ++
  -- GH #10944: the top-level CREATE endowment in canonical 32-byte BE, copied from the
  -- context record so the shared `record_message_value_transfer` can take a pointer to it.
  "bvcr_endow_val_be:\n  .zero 32\n" ++
  -- GH #11164: the AUTHENTICATED pre-state balance of the top-level created account, in
  -- canonical 32-byte BE.  Captured from `create_prebalance_acct+8` BEFORE
  -- `runtime_dispatcher_call`, because that buffer is rewritten by
  -- `call_frame_descend`/`create_frame_descend` and so cannot survive the constructor.
  "bvcr_created_pre_bal:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bv_creation_ctx_ptr:\n  .zero 8\n" ++
  -- Output routing for the generalized top-level creation runner.  Mode 0 is
  -- the legacy single-tx scalar publication; mode 1 scatters its settled
  -- result into the current multi-tx slot.
  "bv_creation_output_mode:\n  .zero 8\n" ++
  "bv_creation_output_index:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bbcv_sender_addr:\n  .zero 32\n" ++
  "bbcv_create_addr:\n  .zero 32\n" ++
  "bbcv_create2_salt:\n  .zero 32\n" ++
  "ac2_inner_digest:\n  .zero 32\n" ++
  "ac2_outer_digest:\n  .zero 32\n" ++
  "ac2_preimage:\n  .zero 88\n" ++
  "ac_buffer:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "ac_nonce_be:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "ac_digest:\n  .zero 32\n" ++
  "bbcv_stop_code_hash:\n" ++
  "  .quad 0x14281e7a9e7836bc, 0x7d818f8229424636, 0x9165d677b4f71266, 0x8ac9bc64e0a996ff\n" ++
  "chahsr_state_root:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "chahsr_acct_struct:\n  .zero 104\n" ++
  ".balign 32\n" ++
  "chahsr_empty_code_hash:\n" ++
  "  .quad 0x3c23f7860146d2c5, 0xc003c7dcb27d7e92, 0x3b2782ca53b600e5, 0x70a4855d04d8fa7b\n" ++
  "ad_offset:\n  .zero 8\n" ++
  "ad_length:\n  .zero 8\n" ++
  "aa_value_len:\n  .zero 8\n" ++
  "ecsahsr_dummy_offset:\n  .zero 8\n" ++
  "ecsahsr_code_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n  .zero 256\n" ++
  "ecsahsr_state_root:\n  .zero 32\n" ++
  "mlk_keccak_buf:\n  .zero 32\n" ++
  "mlk_nibble_buf:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "ecsahsr_acct_struct:\n  .zero 104\n" ++
  ".balign 32\n" ++
  "ecsahsr_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70\n" ++
  ".balign 32\n" ++
  "vh_keccak_table:\n" ++
  "  .zero 8192\n" ++
  ".balign 32\n" ++
  "vh_extracted_parent_hash:\n" ++
  "  .zero 32\n" ++
  "bsg_count:\n  .zero 8\n" ++
  "bsg_off:\n  .zero 8\n" ++
  "bsg_len:\n  .zero 8\n" ++
  "bsg_tx_nonce:\n  .zero 8\n" ++
  "bsg_slot_count:\n  .zero 8\n" ++
  "bsg_slot_off:\n  .zero 8\n" ++
  "bsg_slot_len:\n  .zero 8\n" ++
  "bsg_slot_ptr:\n  .zero 8\n" ++
  "bsg_slot_item_len:\n  .zero 8\n" ++
  "bsg_changes_off:\n  .zero 8\n" ++
  "bsg_changes_len:\n  .zero 8\n" ++
  "bsg_changes_ptr:\n  .zero 8\n" ++
  "bsg_change_count:\n  .zero 8\n" ++
  "bsg_change_off:\n  .zero 8\n" ++
  "bsg_change_len:\n  .zero 8\n" ++
  "bsg_change_ptr:\n  .zero 8\n" ++
  "bsg_change_item_len:\n  .zero 8\n" ++
  "bsg_idx_off:\n  .zero 8\n" ++
  "bsg_idx_len:\n  .zero 8\n" ++
  "bsg_index:\n  .zero 8\n" ++
  "bsg_value_off:\n  .zero 8\n" ++
  "bsg_value_len:\n  .zero 8\n" ++
  "bsg_tx_type:\n  .zero 8\n" ++
  "bsg_tx_inner:\n  .zero 8\n" ++
  "bsg_tx_gas:\n  .zero 8\n" ++
  "bsg_gas_field:\n  .zero 8\n" ++
  "bsg_to_field:\n  .zero 8\n" ++
  "bsg_value_field:\n  .zero 8\n" ++
  "bsg_data_field:\n  .zero 8\n" ++
  "bsg_access_field:\n  .zero 8\n" ++
  "bsg_auth_field:\n  .zero 8\n" ++
  "bsg_intrinsic_gas:\n  .zero 8\n" ++
  "bsg_floor_gas:\n  .zero 8\n" ++
  "bsg_data_ptr:\n  .zero 8\n" ++
  "bsg_data_off:\n  .zero 8\n" ++
  "bsg_data_len:\n  .zero 8\n" ++
  "bsg_to_off:\n  .zero 8\n" ++
  "bsg_to_len:\n  .zero 8\n" ++
  "bsg_access_off:\n  .zero 8\n" ++
  "bsg_access_len:\n  .zero 8\n" ++
  "bsg_access_addrs:\n  .zero 8\n" ++
  "bsg_access_slots:\n  .zero 8\n" ++
  "bsg_auth_off:\n  .zero 8\n" ++
  "bsg_auth_len:\n  .zero 8\n" ++
  "bsg_auth_count:\n  .zero 8\n" ++
  "bsg_min_block_gas:\n  .zero 8\n" ++
  "alc_scratch:\n  .zero 8\n" ++
  "alc_entry_offset:\n  .zero 8\n" ++
  "alc_entry_length:\n  .zero 8\n" ++
  "alc_keys_offset:\n  .zero 8\n" ++
  "alc_keys_length:\n  .zero 8\n" ++
  "bsg_worst_state:\n  .zero 8\n" ++
  "bsg_prior_state:\n  .zero 8\n" ++
  "bsg_state_gas:\n  .zero 8\n" ++
  "bsg_exact_state_ok:\n  .zero 8\n" ++
  "bsg_blob_count:\n  .zero 8\n" ++
  "bsg_blob_gas_accum:\n  .zero 8\n" ++
  "bgvh_count_scratch:\n  .zero 8\n" ++
  "tcbg_struct:\n  .zero 248\n" ++
  -- Full u256 (BE) max_fee_per_blob_gas, persisted by tx_eip4844_decode for
  -- callers that need the >u64 value (EIP-8037 gate blob-price check). tcbg_struct+160
  -- keeps only the low-64 view; in the high blob-fee regime (excess_blob_gas > ~328M)
  -- the price and a valid tx's max_fee both exceed u64, so the gate compares u256.
  "tcbg_blob_fee_be:\n  .zero 32\n" ++
  "bsg_blob_price_be:\n  .zero 32\n" ++
  "bsg_blob_lt_out:\n  .zero 8\n" ++
  "bsg_sender_addr:\n  .zero 32\n" ++
  "bsr_fail_code:\n  .zero 8\n" ++
  "bsr_storage_from_map:\n  .zero 8\n" ++
  "bsr_header_state_root_p:\n  .zero 8\n" ++
  "bsr_wds_p:\n  .zero 8\n" ++
  "bsr_wds_n:\n  .zero 8\n" ++
  "bsr_change_count:\n  .zero 8\n" ++
  "sri_cur_mode:\n  .zero 8\n" ++
  "sri_fail_index:\n  .zero 8\n" ++
  "sri_fail_mode:\n  .zero 8\n" ++
  "sri_fail_status:\n  .zero 8\n" ++
  "bpf_list_off:\n  .zero 8\n" ++
  "bpf_list_len:\n  .zero 8\n" ++
  "bpf_list_ptr:\n  .zero 8\n" ++
  "bpf_count:\n  .zero 8\n" ++
  "bpf_item_off:\n  .zero 8\n" ++
  "bpf_item_len:\n  .zero 8\n" ++
  "bpf_item_ptr:\n  .zero 8\n" ++
  "bpf_val_off:\n  .zero 8\n" ++
  "bpf_val_len:\n  .zero 8\n" ++
  "baap_bal_len:\n  .zero 8\n" ++
  "baap_nonce_len:\n  .zero 8\n" ++
  "baap_tmp_len:\n  .zero 8\n" ++
  "baap_tmp2_len:\n  .zero 8\n" ++
  "baap_fail_code:\n  .zero 8\n" ++
  "baap_sc_off:\n  .zero 8\n" ++
  "baap_sc_len:\n  .zero 8\n" ++
  "baap_sc_ptr:\n  .zero 8\n" ++
  "baap_sc_count:\n  .zero 8\n" ++
  "baap_sc_index:\n  .zero 8\n" ++
  "baap_sc_out_count:\n  .zero 8\n" ++
  "baap_storage_empty_flag:\n  .zero 8\n" ++
  "baap_force_storage_clear:\n  .zero 8\n" ++
  "baap_storage_root_ptr:\n  .zero 8\n" ++
  "baap_walk_val_len:\n  .zero 8\n" ++
  "mdacc_witness_len:\n  .zero 8\n" ++
  "mdacc_survivor_nibble:\n  .zero 8\n" ++
  "mdacc_child_ptr:\n  .zero 8\n" ++
  "mdacc_child_len:\n  .zero 8\n" ++
  "mdacc_leaf_path_len:\n  .zero 8\n" ++
  "mdacc_ext_path_len:\n  .zero 8\n" ++
  "mdacc_leaf_value_ptr:\n  .zero 8\n" ++
  "mdacc_leaf_value_len:\n  .zero 8\n" ++
  "mee_path_off:\n  .zero 8\n" ++
  "mee_path_len:\n  .zero 8\n" ++
  "baap_item_off:\n  .zero 8\n" ++
  "baap_item_len:\n  .zero 8\n" ++
  "baap_slot_changes_off:\n  .zero 8\n" ++
  "baap_slot_changes_len:\n  .zero 8\n" ++
  "baap_slot_changes_ptr:\n  .zero 8\n" ++
  "baap_slot_changes_count:\n  .zero 8\n" ++
  "baap_val_off:\n  .zero 8\n" ++
  "baap_val_len:\n  .zero 8\n" ++
  "baap_val_ptr:\n  .zero 8\n" ++
  "baap_code_list_off:\n  .zero 8\n" ++
  "baap_code_list_len:\n  .zero 8\n" ++
  "baap_code_list_ptr:\n  .zero 8\n" ++
  "baap_code_count:\n  .zero 8\n" ++
  "baap_code_item_ptr:\n  .zero 8\n" ++
  "baap_code_off:\n  .zero 8\n" ++
  "baap_code_len:\n  .zero 8\n" ++
  "baap_tmp3_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "baap_bal:\n  .zero 32\n" ++
  "baap_nonce:\n  .zero 32\n" ++
  "baap_slot:\n  .zero 32\n" ++
  "baap_code_hash:\n  .zero 32\n" ++
  "baap_map_addr:\n  .zero 32\n" ++
  "baap_map_value:\n  .zero 32\n" ++
  "baap_map_value_be:\n  .zero 32\n" ++
  "baap_map_recip_scratch:\n  .zero 32\n" ++
  "baap_map_slot_scratch:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "baap_tmp:\n  .zero 512\n" ++
  "baap_tmp2:\n  .zero 512\n" ++
  "baap_tmp3:\n  .zero 512\n" ++
  "baap_storage_value_cursor:\n  .zero 8\n" ++
  "baap_walk_val:\n  .zero 128\n" ++
  ziskStatelessVerdictV2DataSectionTail ++ "\n" ++
  accountWriteMapBssSection ++ "\n" ++
  -- Persistent execution-derived BAL builder.  It is deliberately last: this
  -- allocation must not move established data labels, and it remains live from
  -- transaction execution through the later serializer/hash pass.
  blockAccessListBuilderDataSection ++
  -- #11163: keep the shared precompile descriptor after all established BSS
  -- arenas so adding it cannot relocate any pre-existing runtime cell.
  ".balign 8\n" ++
  "precompile_shared_ctx:\n  .zero 24\n" ++
  "precompile_shared_selector:\n  .zero 8\n" ++
  "precompile_shared_cost:\n  .zero 8\n" ++
  "precompile_shared_status:\n  .zero 8\n"

end EvmAsm.Codegen
