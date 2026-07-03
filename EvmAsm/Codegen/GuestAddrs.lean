/-
  EvmAsm.Codegen.GuestAddrs

  GENERATED — do not edit by hand.
  `python3 scripts/asm_to_program.py guest-addrs` regenerates this from
  `scripts/asm-fixtures/symbol-addresses.tsv` (the linker-facts table of
  bead evm-asm-4ch8f.6). One `Nat` constant per guest symbol that a
  converted `_prog` references — function entries (the `pc` base for a
  `la`/`jal` immediate) and `la`/cross-`jal` targets (data arenas, tables,
  callee entries).

  This is the SINGLE file that churns on guest layout drift: the per-
  function `_prog` defs reference these constants by name via
  `AsmReloc.{laHi,laLo,jalOff}`, so a `.text`/`.data` size change only
  requires regenerating the TSV + this file, never the 100s of `_prog`s.
  Guarded by `scripts/check-asm-to-program.sh` (regenerate + diff).

  Addresses are LINK_DEPENDENT (move on any layout change); the trusted
  arbiter that they are correct is the whole-guest byte-identity gate.
-/

namespace EvmAsm.Codegen.GuestAddrs

def account_extract_balance : Nat := 0x8001d8f8
def account_extract_nonce : Nat := 0x8001d94c
def bgv_u32le : Nat := 0x8001aa24
def block_hash_from_header : Nat := 0x8000afb4
def block_rlp_rebuilt_size : Nat := 0x8000ace4
def blsg_lt_p : Nat := 0x80034250
def blsg_p_be : Nat := 0xb7941248
def bnc_is_inf64 : Nat := 0x80034de8
def bnc_on_curve : Nat := 0x80034ff0
def bnc_validate_g1 : Nat := 0x8003507c
def bnf_lt_p : Nat := 0x80034c94
def bnf_p_be : Nat := 0xb7940cb0
def brl_item_end : Nat := 0xaa277dc8
def brl_item_start : Nat := 0xaa277dc0
def brl_wd_buf : Nat := 0xaa277dd8
def brl_wd_len : Nat := 0xaa277dd0
def bvgr_tx_exec_state_gas : Nat := 0xaa206328
def bytes_to_nibbles : Nat := 0x80004e40
def consolidation_request_predeploy_addr : Nat := 0xb75cd0d8
def derive_consolidation_requests : Nat := 0x800576cc
def derive_withdrawal_requests : Nat := 0x800576b0
def dispatcher_capture_exec_state_gas : Nat := 0x8002b464
def evm_call_depth : Nat := 0xb85da820
def evm_state_gas_used : Nat := 0xb794da50
def exec_nonstorage_effect_count : Nat := 0xb7b59e08
def exec_nonstorage_effect_log : Nat := 0xb7b59e20
def extract_witness_state_section : Nat := 0x8000b5a4
def frame_depth_pop : Nat := 0x8003cdec
def frame_depth_push : Nat := 0x8003cdd4
def frame_load_regs : Nat := 0x8003ce20
def frame_save_area : Nat := 0xb85da830
def frame_save_regs : Nat := 0x8003ce04
def header_extract_number : Nat := 0x800245ec
def hp_encode_nibbles : Nat := 0x8000444c
def mbc_length : Nat := 0xa3c423e8
def mbc_offset : Nat := 0xa3c423e0
def mee_path_len : Nat := 0xabbe7e98
def mee_path_off : Nat := 0xabbe7e90
def mle_path_len : Nat := 0xb68b6990
def mle_path_off : Nat := 0xb68b6988
def mlk_keccak_buf : Nat := 0xabbe5920
def mlk_nibble_buf : Nat := 0xabbe5940
def mnk_dummy_length : Nat := 0xa3c423c8
def mnk_dummy_offset : Nat := 0xa3c423c0
def mnk_path_length : Nat := 0xa3c423d8
def mnk_path_offset : Nat := 0xa3c423d0
def mpt_branch_child : Nat := 0x80004240
def mpt_delete_acc : Nat := 0x80006bbc
def mpt_extension_extract : Nat := 0x80006a38
def mpt_indexed_large_leaf_hash : Nat := 0x80009208
def mpt_indexed_trie_root_large : Nat := 0x800093dc
def mpt_insert_acc : Nat := 0x80008130
def mpt_leaf_extract : Nat := 0x800078b0
def mpt_lookup_by_key : Nat := 0x80005c2c
def mpt_node_kind : Nat := 0x8000417c
def mpt_node_slot_encode : Nat := 0x80004db0
def mpt_resolve_cache_reset : Nat := 0x80006264
def mpt_set_acc : Nat := 0x80006850
def mpt_splice_slot : Nat := 0x80005354
def mpt_state_root : Nat := 0x80007794
def mpt_state_root_ins : Nat := 0x80008bf4
def mpt_walk : Nat := 0x80005744
def mset_cursor : Nat := 0xa3c62980
def mset_db_count : Nat := 0xa3c639f8
def mset_db_data : Nat := 0xa3c9ba80
def mset_db_hash : Nat := 0xa3c63a40
def mset_db_top : Nat := 0xa3c63a00
def mset_dr_root : Nat := 0xa449ba80
def mset_head_len : Nat := 0xa3c62958
def mset_memcpy : Nat := 0x80005334
def mset_new_payload_len : Nat := 0xa3c62970
def mset_payload_start : Nat := 0xa3c62950
def mset_prefix_len : Nat := 0xa3c62978
def mset_span_size : Nat := 0xa3c62948
def mset_span_start : Nat := 0xa3c62940
def mset_tail_len : Nat := 0xa3c62968
def mset_tail_start : Nat := 0xa3c62960
def node_db_append : Nat := 0x80006120
def node_db_lookup : Nat := 0x800061e0
def nonstorage_effect_latest_balance : Nat := 0x8003d6b0
def priority_fee_per_gas_eip1559 : Nat := 0x80026664
def rfu_length : Nat := 0xa449c2a8
def rfu_offset : Nat := 0xa449c2a0
def rlp_bytes_encoded_size : Nat := 0x8000ac60
def rlp_content_to_u256_be : Nat := 0x80004b54
def rlp_content_to_u64 : Nat := 0x80004afc
def rlp_encode_bytes : Nat := 0x800044b8
def rlp_encode_list_prefix : Nat := 0x80004674
def rlp_field_to_u256_be : Nat := 0x800040cc
def rlp_field_to_u64 : Nat := 0x800024a0
def rlp_item_span : Nat := 0x800047b8
def rlp_list_encoded_size : Nat := 0x8000acb0
def rlp_list_nth_item : Nat := 0x80002220
def rlp_prefix_to_buffer : Nat := 0x8000919c
def rlp_walk_init : Nat := 0x8000488c
def rlp_walk_next : Nat := 0x80004960
def single_leaf_trie_root : Nat := 0x8000b994
def sltr_cursor : Nat := 0xa463ec70
def sltr_field_len : Nat := 0xa463ec58
def sltr_hp_buf : Nat := 0xa463f480
def sltr_hp_len : Nat := 0xa463ec68
def sltr_nibble_count : Nat := 0xa463ec60
def sltr_nibbles : Nat := 0xa463ec80
def sltr_node_buf : Nat := 0xa4643880
def sltr_payload_buf : Nat := 0xa463f880
def sltr_total_payload : Nat := 0xa463ec78
def sri_cur_mode : Nat := 0xabbe7d58
def sri_fail_index : Nat := 0xabbe7d60
def sri_fail_mode : Nat := 0xabbe7d68
def sri_fail_status : Nat := 0xabbe7d70
def ssz_withdrawal_to_rlp : Nat := 0x8000b63c
def stage_system_call : Nat := 0x800576e8
def sws_u32le : Nat := 0x8000b574
def tcbg_blob_fee_be : Nat := 0xabbe7d00
def tx_eip1559_decode : Nat := 0x80020418
def tx_eip2930_decode : Nat := 0x800201d8
def tx_eip4844_decode : Nat := 0x80019b88
def tx_eip7702_decode : Nat := 0x80020680
def u256_min : Nat := 0x80026604
def u256_sub_be : Nat := 0x800050d8
def withdrawal_request_predeploy_addr : Nat := 0xb75cd0c0
def zkvm_keccak256 : Nat := 0x80003038

end EvmAsm.Codegen.GuestAddrs
