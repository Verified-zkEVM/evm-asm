/-
  EvmAsm.Codegen.Programs.BlockVerdictFunction

  Main block_verdict assembly string, split from BlockVerdict.lean for FileSizeGuard.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BlockVerdictTransactions
import EvmAsm.Codegen.Programs.BlockVerdictReceiptsTail
import EvmAsm.Codegen.Programs.BlockVerdictMtxTail
import EvmAsm.Codegen.Programs.BlockVerdictMtxEoa
import EvmAsm.Codegen.Programs.BlockVerdictReceiptGate

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## block_verdict -- step2_verdict with the FULL (system + withdrawal) recompute.
    a0 = params ptr (the step2_verdict struct)   a1 = SSZ_BASE
    a0 (output) = verdict bit. -/
def blockVerdictFunction : String :=
  "block_verdict:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # params\n" ++
  "  mv s3, a1                   # SSZ_BASE\n" ++
  -- fhsxz.2.4.2.57.11.6.5: stash the parent (PRE-state) header RLP ptr/len so
  -- dispatch_tx_runtime_code's witness lookups use the PRE-state root (witness root),
  -- not sv_this_rlp (this block's POST-state header). 8(s0)/16(s0) is the parent header.
  "  ld t0, 8(s0); la t1, sv_pre_rlp_ptr; sd t0, 0(t1)\n" ++
  "  ld t0, 16(s0); la t1, sv_pre_rlp_len; sd t0, 0(t1)\n" ++
  "  la t0, bv_fail_code; sd zero, 0(t0)\n" ++
  "  la t0, bv_header_status; sd zero, 0(t0)\n" ++
  "  la t0, bv_state_status; sd zero, 0(t0)\n" ++
  "  la t0, bv_tx_root_status; sd zero, 0(t0)\n" ++
  "  la t0, bv_withdrawals_root_status; sd zero, 0(t0)\n" ++
  "  la t0, bv_withdrawals_root_valid; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_runtime_gas_left_ptr; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_runtime_refund_counter_ptr; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_runtime_calldata_floor_ptr; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_runtime_count; sd zero, 0(t0)\n  la t0, bv_runtime_completeness_status; sd zero, 0(t0)\n" ++
  "  ld a0, 0(s0); ld a1, 32(s0); ld a2, 40(s0); ld a3, 48(s0); ld a4, 56(s0); ld a7, 96(s0)\n" ++
  "  la a5, sv_this_rlp; la a6, sv_this_rlp_len\n" ++
  "  jal ra, block_header_ssz_to_rlp\n" ++
  "  la t0, bv_block_hash_check_enabled; ld t0, 0(t0); beqz t0, .Lbv_block_hash_ok\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0); la a2, bv_block_hash\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  la t0, bv_block_hash; ld t1, 0(s0); addi t1, t1, 472; li t2, 32\n" ++
  ".Lbv_block_hash_cmp:\n" ++
  "  beqz t2, .Lbv_block_hash_ok\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_block_hash_mismatch\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_block_hash_cmp\n" ++
  ".Lbv_block_hash_ok:\n" ++
  "  ld a0, 0(s0); la t0, sv_this_rlp_len; ld a1, 0(t0); mv a2, s3\n" ++
  "  jal ra, block_rlp_rebuilt_size\n" ++
  "  bnez a0, .Lbv_block_rlp_parse_fail\n" ++
  "  la t0, bv_block_rlp_len; sd a1, 0(t0)\n" ++
  "  li t1, 0x800000; bgtu a1, t1, .Lbv_block_rlp_limit_fail\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0); ld a2, 8(s0); ld a3, 16(s0)\n" ++
  "  jal ra, validate_header_rlp_pair\n" ++
  "  mv s1, a0\n" ++
  "  la t0, bv_header_status; sd s1, 0(t0)\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0); ld a2, 64(s0); ld a3, 72(s0)\n" ++
  "  jal ra, block_validate_withdrawals_root_indexed\n" ++
  "  la t0, bv_withdrawals_root_status; sd a0, 0(t0)\n" ++
  "  la t0, bv_withdrawals_root_valid; sd a1, 0(t0)\n" ++
  "  bnez a0, .Lbv_withdrawals_root_fail\n" ++
  "  beqz a1, .Lbv_withdrawals_root_fail\n" ++
  -- bmvmx.1.4.4: precompute the supported single-tx EOA settlement scalars BEFORE
  -- block_state_root so .4.1/.4.2 can build execution-derived sender/coinbase leaves.
  -- ADDITIVE (no consumer reads bmvmx_* yet) -> verdict byte-identical. exec_p = 0(s0)
  -- (= bv_exec_p). All bv_* writes here are idempotent with the post-348 tx preamble,
  -- and block_state_root (BlockVerdict.lean:67-302) reads none of these globals.
  "  la t0, bmvmx_avail; sd zero, 0(t0)\n" ++
  "  la t0, eip7708_tl_typed_avail; sd zero, 0(t0)\n" ++
  bvReceiptsShapeClear ++  "  la t0, bmvmx_sender_checked; sd zero, 0(t0)\n" ++             -- bmvmx.1.4.3.1: envelope predicate flags default 0
  "  la t0, bmvmx_coinbase_checked; sd zero, 0(t0)\n" ++
  "  addi t4, s3, 60; la t0, bv_exec_p; sd t4, 0(t0)\n" ++         -- exec_p = ssz_base(s3)+60 (block_state_root's bsr_exec_p derivation; 0(s0) is NOT populated pre-348)
  "  la t4, bv_exec_p; ld t4, 0(t4); addi a0, t4, 504; jal ra, bgv_u32le\n" ++       -- transactions_offset
  "  la t0, bmvmx_txoff; sd a0, 0(t0)\n" ++
  "  la t4, bv_exec_p; ld t4, 0(t4); addi a0, t4, 508; jal ra, bgv_u32le\n" ++       -- withdrawals_offset
  "  la t0, bmvmx_txoff; ld t1, 0(t0)\n" ++
  "  bleu a0, t1, .Lbmvmx_done\n" ++                                -- no transactions
  "  sub t5, a0, t1\n" ++                                           -- tx list byte length
  "  li t6, 4; bltu t5, t6, .Lbmvmx_done\n" ++
  "  la t4, bv_exec_p; ld t4, 0(t4); add t6, t4, t1; la t0, bv_tx_list_ptr; sd t6, 0(t0)\n" ++
  "  la t0, bv_tx_list_len; sd t5, 0(t0)\n" ++
  "  la t0, bv_tx_list_ptr; ld a0, 0(t0); jal ra, bgv_u32le\n" ++  -- offset[0] = 4*tx_count
  "  andi t0, a0, 3; bnez t0, .Lbmvmx_done\n" ++
  "  srli t1, a0, 2; la t0, bv_tx_count; sd t1, 0(t0)\n" ++
  "  li t0, 1; bne t1, t0, .Lbmvmx_done\n" ++                       -- single-tx class only
  "  la a0, bmvmx_ctx; li a1, 0; jal ra, multi_tx_nth_context\n" ++
  "  la t0, bmvmx_ctx; ld t1, 0(t0); bnez t1, .Lbmvmx_done; ld t1, 48(t0); bnez t1, .Lbmvmx_done\n" ++   -- unsupported/creation tx shape
  -- bmvmx.1.4.3.1 envelope (cheap half): restrict the exec-derived balance compare to a
  -- LEGACY (type-0, no access list) single tx. Outside legacy, stay conservative: jump to
  -- .Lbmvmx_done (skip the whole inert compute; bmvmx_avail stays 0, so .4.3.2's gate never
  -- fires). The remaining envelope conditions gate the per-compare bmvmx_*_checked flags:
  -- sender/recipient/coinbase distinctness is enforced below; the EOA-recipient check (so
  -- gas_used==21000 is exact) is DEFERRED to .4.3.2's reject path, since that MPT+keccak
  -- lookup would otherwise burden every single-tx block's verdict (proving-cost sensitive).
  "  la t0, bmvmx_ctx; ld t0, 160(t0); bnez t0, .Lbmvmx_done\n" ++  -- non-legacy (2930/1559/4844/7702) -> conservative
  "  la t4, bv_exec_p; ld t4, 0(t4); addi t1, t4, 440; la t2, bmvmx_basefee_be; li t3, 0\n" ++   -- base_fee LE->BE (32B)
  ".Lbmvmx_rev:\n" ++
  "  li t0, 32; beq t3, t0, .Lbmvmx_rev_done\n" ++
  "  add t0, t1, t3; lbu t5, 0(t0); li t6, 31; sub t6, t6, t3; add t6, t2, t6; sb t5, 0(t6); addi t3, t3, 1; j .Lbmvmx_rev\n" ++
  ".Lbmvmx_rev_done:\n" ++
  "  la t0, bmvmx_ctx; ld a0, 8(t0); ld a1, 16(t0)\n" ++           -- tx bytes ptr/len
  "  la a2, bmvmx_basefee_be; la a3, bmvmx_eff_gas_price; la a4, bmvmx_priority_fee\n" ++
  "  jal ra, tx_effective_gas_pricing\n" ++
  "  bnez a0, .Lbmvmx_done\n" ++                                    -- pricing failed -> stay unavailable
  "  la t1, bmvmx_ctx; addi t1, t1, 96; la t2, bmvmx_value; li t3, 0\n" ++   -- copy value (32B)
  ".Lbmvmx_vcopy:\n" ++
  "  li t0, 32; beq t3, t0, .Lbmvmx_vdone\n" ++
  "  add t0, t1, t3; lbu t5, 0(t0); add t6, t2, t3; sb t5, 0(t6); addi t3, t3, 1; j .Lbmvmx_vcopy\n" ++
  ".Lbmvmx_vdone:\n" ++
  "  la t0, bmvmx_gas_used; li t1, 21000; sd t1, 0(t0)\n" ++       -- EOA intrinsic gas_used
  -- bmvmx.1.4.1: execution-derived sender balance debit = gas_used*eff_gas_price + value
  -- (the amount the sender's balance decreases; consumed by .4.3 as sender_post = pre - debit).
  "  la a0, bmvmx_eff_gas_price; la t0, bmvmx_gas_used; ld a1, 0(t0); la a2, bmvmx_gascost; jal ra, u256_mul_u64_be\n" ++
  "  la a0, bmvmx_gascost; la a1, bmvmx_value; la a2, bmvmx_sender_debit; jal ra, u256_add_be\n" ++
  -- bmvmx.1.4.1 compare (additive; sets bmvmx_sender_match only -> verdict byte-identical):
  -- assert the BAL sender post balance == sender_pre - bmvmx_sender_debit. Sender address is
  -- derived from the selected public key (pubkeys = SSZ_BASE(s3) + offsets[3]@s3+12; 65-byte
  -- SEC1 key 0x04||x||y -> address_from_pubkey(key+1)). Reuses bmvmx_acct/bmvmx_cb_* scratch.
  "  la t0, bmvmx_sender_match; sd zero, 0(t0)\n" ++
  "  addi a0, s3, 12; jal ra, bgv_u32le\n" ++                          -- offsets[3] (public_keys offset)
  "  add t0, s3, a0; addi a0, t0, 1\n" ++                              -- pubkey[0] x||y (skip 0x04 prefix)
  "  la a1, bmvmx_sender_addr; jal ra, address_from_pubkey\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); la a2, bmvmx_sender_addr; li a3, 20; ld a4, 80(s0); ld a5, 88(s0); la a6, bmvmx_acct\n" ++
  "  jal ra, account_at_header_state_root\n" ++
  "  beqz a0, .Lbmvmx_sd_preok\n" ++
  "  li t0, 1; bne a0, t0, .Lbmvmx_sd_skip\n" ++
  "  la t0, bmvmx_acct; sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0); sd zero, 32(t0)\n" ++   -- not found -> pre = 0
  ".Lbmvmx_sd_preok:\n" ++
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0); la a2, bmvmx_sender_addr; la a3, bmvmx_cb_acct_ptr; la a4, bmvmx_cb_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .Lbmvmx_sd_skip\n" ++
  "  la t0, bmvmx_cb_acct_ptr; ld a0, 0(t0); la t0, bmvmx_cb_acct_len; ld a1, 0(t0); la a2, bmvmx_cb_balbytes; la a3, bmvmx_cb_bal_len; la a4, bmvmx_cb_nonce; la a5, bmvmx_cb_nonce_len\n" ++
  "  jal ra, bal_account_post_fields\n" ++
  "  bnez a0, .Lbmvmx_sd_skip\n" ++
  "  la t0, bmvmx_cb_post; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t1, bmvmx_cb_bal_len; ld t1, 0(t1); li t2, 32; bgtu t1, t2, .Lbmvmx_sd_skip\n" ++
  "  la t3, bmvmx_cb_balbytes; la t4, bmvmx_cb_post; sub t5, t2, t1; li t6, 0\n" ++
  ".Lbmvmx_sd_ra:\n" ++
  "  beq t6, t1, .Lbmvmx_sd_rad\n" ++
  "  add t0, t3, t6; lbu a0, 0(t0); add t0, t4, t5; add t0, t0, t6; sb a0, 0(t0); addi t6, t6, 1; j .Lbmvmx_sd_ra\n" ++
  ".Lbmvmx_sd_rad:\n" ++
  "  la a0, bmvmx_acct; addi a0, a0, 8; la a1, bmvmx_sender_debit; la a2, bmvmx_cb_expected; jal ra, u256_sub_be\n" ++   -- expected = pre - debit
  "  la a0, bmvmx_cb_expected; la a1, bmvmx_cb_post; jal ra, u256_eq\n" ++
  "  la t0, bmvmx_sender_match; sd a0, 0(t0)\n" ++                     -- match = (pre - debit == BAL post)
  "  la t0, bmvmx_sender_checked; li t1, 1; sd t1, 0(t0)\n" ++          -- bmvmx.1.4.3.1: sender compare PERFORMED in-envelope (distinctness cleared below)
  ".Lbmvmx_sd_skip:\n" ++
  -- bmvmx.1.4.2: execution-derived coinbase fee credit = priority_fee_per_gas * gas_used
  -- (the tip credited to the block coinbase; EIP-1559 base fee is burned). Consumed by
  -- .4.3 as coinbase_post = coinbase_pre + credit (for the supported single-tx EOA class).
  "  la a0, bmvmx_priority_fee; la t0, bmvmx_gas_used; ld a1, 0(t0); la a2, bmvmx_coinbase_credit; jal ra, u256_mul_u64_be\n" ++
  -- bmvmx.1.4.2 compare (additive; sets bmvmx_coinbase_match only -> verdict byte-identical):
  -- assert the BAL coinbase post balance == coinbase_pre + bmvmx_coinbase_credit. Any miss /
  -- not-found / overlap (coinbase==sender/recipient) / absent leaves match=0 (conservative).
  "  la t0, bmvmx_coinbase_match; sd zero, 0(t0)\n" ++
  "  la t4, bv_exec_p; ld t4, 0(t4); addi t1, t4, 32; la t2, bmvmx_coinbase_addr; li t3, 0\n" ++   -- coinbase = fee_recipient (exec_p+32)
  ".Lbmvmx_cbaddr:\n" ++
  "  li t0, 20; beq t3, t0, .Lbmvmx_cbaddr_d\n" ++
  "  add t0, t1, t3; lbu t5, 0(t0); add t6, t2, t3; sb t5, 0(t6); addi t3, t3, 1; j .Lbmvmx_cbaddr\n" ++
  ".Lbmvmx_cbaddr_d:\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); la a2, bmvmx_coinbase_addr; li a3, 20; ld a4, 80(s0); ld a5, 88(s0); la a6, bmvmx_acct\n" ++
  "  jal ra, account_at_header_state_root\n" ++
  "  beqz a0, .Lbmvmx_cb_preok\n" ++                                  -- 0 = found (pre = bmvmx_acct+8)
  "  li t0, 1; bne a0, t0, .Lbmvmx_cb_skip\n" ++                       -- not 'not-found' -> parse err, skip
  "  la t0, bmvmx_acct; sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0); sd zero, 32(t0)\n" ++   -- not found -> pre = 0
  ".Lbmvmx_cb_preok:\n" ++
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0); la a2, bmvmx_coinbase_addr; la a3, bmvmx_cb_acct_ptr; la a4, bmvmx_cb_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .Lbmvmx_cb_skip\n" ++                                    -- coinbase absent in BAL / err -> conservative
  "  la t0, bmvmx_cb_acct_ptr; ld a0, 0(t0); la t0, bmvmx_cb_acct_len; ld a1, 0(t0); la a2, bmvmx_cb_balbytes; la a3, bmvmx_cb_bal_len; la a4, bmvmx_cb_nonce; la a5, bmvmx_cb_nonce_len\n" ++
  "  jal ra, bal_account_post_fields\n" ++
  "  bnez a0, .Lbmvmx_cb_skip\n" ++
  "  la t0, bmvmx_cb_post; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++   -- zero, then right-align
  "  la t1, bmvmx_cb_bal_len; ld t1, 0(t1); li t2, 32; bgtu t1, t2, .Lbmvmx_cb_skip\n" ++   -- absent (UINT64_MAX) / >32 -> skip
  "  la t3, bmvmx_cb_balbytes; la t4, bmvmx_cb_post; sub t5, t2, t1; li t6, 0\n" ++   -- dst offset = 32 - len
  ".Lbmvmx_cb_ra:\n" ++
  "  beq t6, t1, .Lbmvmx_cb_rad\n" ++
  "  add t0, t3, t6; lbu a0, 0(t0); add t0, t4, t5; add t0, t0, t6; sb a0, 0(t0); addi t6, t6, 1; j .Lbmvmx_cb_ra\n" ++
  ".Lbmvmx_cb_rad:\n" ++
  "  la a0, bmvmx_acct; addi a0, a0, 8; la a1, bmvmx_coinbase_credit; la a2, bmvmx_cb_expected; jal ra, u256_add_be\n" ++
  "  la a0, bmvmx_cb_expected; la a1, bmvmx_cb_post; jal ra, u256_eq\n" ++
  "  la t0, bmvmx_coinbase_match; sd a0, 0(t0)\n" ++                   -- match = (pre+credit == BAL post)
  "  la t0, bmvmx_coinbase_checked; li t1, 1; sd t1, 0(t0)\n" ++       -- bmvmx.1.4.3.1: coinbase compare PERFORMED in-envelope (distinctness cleared below)
  ".Lbmvmx_cb_skip:\n" ++
  "  la t0, bmvmx_avail; li t1, 1; sd t1, 0(t0)\n" ++
  bvReceiptsShapeSet 1 true ++  -- Distinctness clears the performed sender/coinbase checks when value/fee effects overlap.
  "  la a0, bmvmx_sender_addr; la a1, bmvmx_ctx; addi a1, a1, 72; jal ra, .Lbmvmx_addr20_ne\n" ++
  "  bnez a0, .Lbmvmx_s_vs_cb\n" ++                                    -- sender == recipient -> clear sender_checked
  "  la t0, bmvmx_sender_checked; sd zero, 0(t0)\n" ++
  ".Lbmvmx_s_vs_cb:\n" ++
  "  la a0, bmvmx_sender_addr; la a1, bmvmx_coinbase_addr; jal ra, .Lbmvmx_addr20_ne\n" ++
  "  bnez a0, .Lbmvmx_cb_vs_s\n" ++                                    -- sender == coinbase -> clear sender_checked
  "  la t0, bmvmx_sender_checked; sd zero, 0(t0)\n" ++
  ".Lbmvmx_cb_vs_s:\n" ++
  "  la a0, bmvmx_coinbase_addr; la a1, bmvmx_sender_addr; jal ra, .Lbmvmx_addr20_ne\n" ++
  "  bnez a0, .Lbmvmx_cb_vs_r\n" ++                                    -- coinbase == sender -> clear coinbase_checked
  "  la t0, bmvmx_coinbase_checked; sd zero, 0(t0)\n" ++
  ".Lbmvmx_cb_vs_r:\n" ++
  "  la a0, bmvmx_coinbase_addr; la a1, bmvmx_ctx; addi a1, a1, 72; jal ra, .Lbmvmx_addr20_ne\n" ++
  "  bnez a0, .Lbmvmx_dist_done\n" ++                                  -- coinbase == recipient -> clear coinbase_checked
  "  la t0, bmvmx_coinbase_checked; sd zero, 0(t0)\n" ++
  ".Lbmvmx_dist_done:\n" ++
  "  j .Lbmvmx_done\n" ++
  -- local helper: a0,a1 = 20-byte address ptrs; returns a0 = 1 if they differ, 0 if equal.
  -- Reached only via jal (clobbers t0..t2); callers do not rely on ra after.
  ".Lbmvmx_addr20_ne:\n" ++
  "  li t2, 0\n" ++
  ".Lbmvmx_a20_loop:\n" ++
  "  li t0, 20; beq t2, t0, .Lbmvmx_a20_eq\n" ++
  "  add t0, a0, t2; lbu t0, 0(t0); add t1, a1, t2; lbu t1, 0(t1)\n" ++
  "  bne t0, t1, .Lbmvmx_a20_ne\n" ++
  "  addi t2, t2, 1; j .Lbmvmx_a20_loop\n" ++
  ".Lbmvmx_a20_ne:\n" ++
  "  li a0, 1; ret\n" ++
  ".Lbmvmx_a20_eq:\n" ++
  "  li a0, 0; ret\n" ++
  ".Lbmvmx_done:\n" ++
  "  ld a0, 24(s0); ld a1, 80(s0); ld a2, 88(s0); ld a3, 64(s0); ld a4, 72(s0)\n" ++
  "  la a5, sv_recomputed; mv a6, s3\n" ++
  "  jal ra, block_state_root\n" ++
  "  mv s2, a0\n" ++
  "  la t0, bv_state_status; sd s2, 0(t0)\n" ++
  "  la t0, sv_recomputed; ld t1, 0(s0); addi t1, t1, 52; li t2, 32\n" ++
  ".Lbv_cmp:\n" ++
  "  beqz t2, .Lbv_cmpok\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_cmp_mismatch\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_cmp\n" ++
  ".Lbv_cmpok:\n" ++
  "  bnez s1, .Lbv_header_fail\n" ++
  "  bnez s2, .Lbv_state_fail\n" ++
  "  # NO-TRANSACTION gate: this verdict does NOT validate transactions, so it can\n" ++
  "  # only soundly judge no-tx blocks. A tx-bearing INVALID block whose invalid tx\n" ++
  "  # is rejected (no state change) would otherwise match the recompute -> false\n" ++
  "  # positive. tx list is empty iff transactions_offset == withdrawals_offset.\n" ++
  "  ld t4, 0(s0)                # exec_payload from extracted params\n" ++
  "  la t5, bv_exec_p; sd t4, 0(t5)\n" ++
  "  addi a0, t4, 504; jal ra, bgv_u32le        # transactions_offset\n" ++
  "  la t5, bv_tx_off; sd a0, 0(t5)\n" ++
  "  la t5, bv_exec_p; ld t4, 0(t5); addi a0, t4, 508; jal ra, bgv_u32le   # withdrawals_offset\n" ++
  "  la t5, bv_tx_off; ld t3, 0(t5)\n" ++
  "  bgtu a0, t3, .Lbv_tx_present # wd_off > tx_off => transactions present\n" ++
  -- wsvlq: NO-TRANSACTION (withdrawal/system-only) block. execution-specs apply_body
  -- increments block_gas_used / block_state_gas_used ONLY per transaction; system txs
  -- and withdrawals do not touch them (fork.py:1199-1202, 734-798, 1230-1249). So a
  -- no-tx block has block_gas_used = 0 and header.gas_used == max(.,.) must be 0; a
  -- nonzero header.gas_used raises InvalidBlock. Verify it here instead of trusting it.
  "  la t5, bv_exec_p; ld t4, 0(t5); addi a0, t4, 420; jal ra, bgv_u64le   # header.gas_used\n" ++
  "  bnez a0, .Lbv_notx_gas_used_fail\n" ++
  -- .63.1.6.2.3 (slice A): NO-TX receipts consensus. execution-specs apply_body
  -- recomputes receipt_root = root(receipts_trie) and block_logs_bloom =
  -- logs_bloom(block_logs) and hard-rejects on a header mismatch (fork.py
  -- 368-371). A no-tx block has an EMPTY receipts trie and ZERO block logs
  -- (system txs and withdrawals contribute neither receipts nor block_logs),
  -- so header.receipts_root must be the empty-trie root and header.bloom must
  -- be 256 zero bytes. The guest never checked either — the audited
  -- false-accept (hermes-c3, bead .63.1.6): a crafted no-tx block with a
  -- tampered bloom/receipt_root and a self-consistent payload.block_hash
  -- passed every gate. Compute the empty indexed-trie root through the real
  -- validator (count = 0) and compare the extracted header bloom to zeros.
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, bvrri_value_descs; li a3, 0\n" ++
  "  jal ra, block_validate_receipts_root_indexed\n" ++
  "  bnez a0, .Lbv_notx_receipts_root_fail\n" ++
  "  beqz a1, .Lbv_notx_receipts_root_fail\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, bv_header_bloom\n" ++
  "  jal ra, header_extract_logs_bloom\n" ++
  "  bnez a0, .Lbv_notx_bloom_fail\n" ++
  "  la a0, bv_header_bloom; la a1, bv_zero_bloom; la a2, bv_bloom_eq_out\n" ++
  "  jal ra, bloom_eq\n" ++
  "  la t0, bv_bloom_eq_out; ld t0, 0(t0); beqz t0, .Lbv_notx_bloom_fail\n" ++
  "  j .Lbv_after_tx_gate\n" ++
  blockVerdictEmptyTransactionCheckAsm ++
  "  la t5, bsr_bal_count; ld t5, 0(t5); beqz t5, .Lbv_no_bal_for_tx  # tx blocks need BAL replay\n" ++
  "  # Any included transaction must consume nonzero gas. This catches rejected\n" ++
  "  # tx payloads whose state/BAL roots otherwise match the conservative replay.\n" ++
  "  la t5, bv_exec_p; ld t4, 0(t5); addi a0, t4, 420; jal ra, bgv_u64le   # gas_used\n" ++
  "  beqz a0, .Lbv_zero_gas_used\n" ++
  "  # Witness headers must cover concrete in-window BLOCKHASH ancestor accesses\n" ++
  "  # visible in transaction code. execution-specs indexes block_hashes and\n" ++
  "  # fails validation if an accessed ancestor is absent.\n" ++
  "  la t5, svf_codes_ptr; ld a0, 0(t5)\n" ++
  "  la t5, svf_codes_len; ld a1, 0(t5)\n" ++
  "  la a2, bv_blockhash_required_headers\n" ++
  "  jal ra, codes_blockhash_required_headers\n" ++
  "  bnez a0, .Lbv_blockhash_headers_fail\n" ++
  "  la t5, bv_blockhash_required_headers; ld t4, 0(t5)\n" ++
  "  la t5, svf_headers_count; ld t3, 0(t5)\n" ++
  "  bgtu t4, t3, .Lbv_blockhash_headers_fail\n" ++
  ".Lbv_after_tx_gate:\n" ++
  "  # execution-specs is_valid_versioned_hashes: SSZ NPR.versioned_hashes must\n" ++
  "  # equal the concatenation of all EIP-4844 tx blob_versioned_hashes.\n" ++
  "  mv a0, s3; jal ra, bgv_u32le\n" ++
  "  add t0, s3, a0              # NPR = SSZ_BASE + outer.offsets[0]\n" ++
  "  la t2, bv_npr_p; sd t0, 0(t2)\n" ++
  "  addi a0, t0, 4; jal ra, bgv_u32le         # versioned_hashes offset\n" ++
  "  mv t3, a0\n" ++
  "  la t2, bv_npr_p; ld t0, 0(t2); addi a0, t0, 40; jal ra, bgv_u32le # execution_requests offset\n" ++
  "  bltu a0, t3, .Lbv_versioned_hashes_fail\n" ++
  "  sub a2, a0, t3              # SSZ versioned_hashes byte length\n" ++
  "  la t2, bv_versioned_hashes_len; sd a2, 0(t2)\n" ++
  "  la t2, bv_npr_p; ld t0, 0(t2); add a1, t0, t3\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  jal ra, ssz_tx_list_versioned_hashes_match\n" ++
  "  bnez a0, .Lbv_versioned_hashes_fail\n" ++
  "  # execution-specs apply_body checks header.blob_gas_used against the blob\n" ++
  "  # gas consumed by type-3 txs. The previous gate proves NPR.versioned_hashes\n" ++
  "  # equals the tx blob-hash concatenation, so total blob gas is derived from\n" ++
  "  # that SSZ list length.\n" ++
  "  la t2, bv_versioned_hashes_len; ld t0, 0(t2)\n" ++
  "  andi t1, t0, 31; bnez t1, .Lbv_blob_gas_used_fail\n" ++
  "  srli t0, t0, 5              # blob count\n" ++
  "  slli t0, t0, 17             # * GAS_PER_BLOB (131072)\n" ++
  "  la t2, bv_blob_gas_expected; sd t0, 0(t2)\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2); addi a0, t1, 512; jal ra, bgv_u64le\n" ++
  "  la t2, bv_blob_gas_observed; sd a0, 0(t2)\n" ++
  "  la t2, bv_blob_gas_expected; ld t0, 0(t2); bne a0, t0, .Lbv_blob_gas_used_fail\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2); addi a0, t1, 520; jal ra, bgv_u64le\n" ++
  "  la a1, bsg_blob_price_be; jal ra, amsterdam_blob_gas_price_u256\n" ++
  "  bnez a0, .Lbv_blob_gas_used_fail\n" ++
  "  mv a0, s3\n" ++
  "  la t2, bv_exec_p; ld a1, 0(t2)\n" ++
  "  jal ra, public_keys_valid\n" ++
  "  bnez a0, .Lbv_public_keys_fail\n" ++
  -- bmvmx.3.2: bind each witness public_keys[i] to the i-th transaction's
  -- recovered signer key (execution-specs recover_sender_from_public_key over
  -- every tx). public_keys_valid only checked count + 65-byte SEC1 shape; this
  -- recovers the sender from each signature and rejects on any mismatch /
  -- recovery failure, closing the sender-attribution false-accept (a lying
  -- witness can otherwise attribute a tx to an attacker-chosen account). Needs
  -- bv_tx_list_ptr/len (set above), bv_public_keys_ptr (set by public_keys_valid),
  -- and bv_chain_id (captured by chain_config_valid).
  "  jal ra, verify_public_keys_match_senders\n" ++
  "  bnez a0, .Lbv_public_keys_sender_fail\n" ++
  "  # EIP-7928 BAL gas-limit rule: reject if the block_access_list exceeds the\n" ++
  "  # gas limit (a semantic invalidity not caught by header/state checks).\n" ++
  "  mv a0, s3; jal ra, bgv_u32le\n" ++
  "  add t0, s3, a0              # NPR = SSZ_BASE + outer.offsets[0]\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2)\n" ++
  "  la t2, bv_npr_p;  sd t0, 0(t2)\n" ++
  "  addi a0, t1, 528; jal ra, bgv_u32le        # bal_off\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2); add a0, t1, a0   # bal_start\n" ++
  "  la t2, bv_bal_start; sd a0, 0(t2)\n" ++
  "  la t2, bv_npr_p; ld t0, 0(t2); addi a0, t0, 4; jal ra, bgv_u32le   # vh_off\n" ++
  "  la t2, bv_npr_p; ld t0, 0(t2); add a1, t0, a0   # bal_end\n" ++
  "  la t2, bv_bal_start; ld t3, 0(t2); sub a1, a1, t3   # bal_len (a1 survives bgv_u64le)\n" ++
  "  la t2, bv_bal_len; sd a1, 0(t2)\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2); addi a0, t1, 412; jal ra, bgv_u64le   # a0 = gas_limit\n" ++
  "  mv a2, a0                                  # gas_limit\n" ++
  "  la t2, bv_bal_start; ld a0, 0(t2)          # bal_start\n" ++
  "  la t2, bv_bal_len; ld a1, 0(t2)            # bal_len\n" ++
  "  jal ra, bal_gas_valid\n" ++
  "  bnez a0, .Lbv_bal_gas_fail          # BAL gas exceeded (or parse fail) -> invalid\n" ++
  "  # Witness integrity: for every BAL account with non-empty pre-state code,\n" ++
  "  # witness.codes must contain that code hash, matching execution-specs'\n" ++
  "  # WitnessState.get_code behavior for missing non-empty code preimages.\n" ++
  "  # Pure BAL account-touch rows are safe to ignore only for withdrawal-only\n" ++
  "  # blocks: zero-amount withdrawals may touch an account without reading code.\n" ++
  "  la t2, bbcv_skip_touch_only; sd zero, 0(t2)\n" ++
  "  ld t4, 0(s0)\n" ++
  "  addi a0, t4, 504; jal ra, bgv_u32le        # transactions_offset\n" ++
  "  mv t3, a0\n" ++
  "  ld t4, 0(s0)\n" ++
  "  addi a0, t4, 508; jal ra, bgv_u32le        # withdrawals_offset\n" ++
  "  bleu a0, t3, .Lbv_code_preimage_no_txs\n" ++
  "  sub t5, a0, t3                             # tx list byte length\n" ++
  "  li t6, 4; bltu t5, t6, .Lbv_code_preimage_no_txs\n" ++
  "  ld t4, 0(s0); add t4, t4, t3               # tx list ptr\n" ++
  "  mv a0, t4; jal ra, bgv_u32le               # first offset = 4 * tx_count\n" ++
  "  andi t6, a0, 3; bnez t6, .Lbv_code_preimage_no_txs\n" ++
  "  srli t6, a0, 2\n" ++
  "  beqz t6, .Lbv_code_preimage_no_txs\n" ++
  "  bgtu a0, t5, .Lbv_code_preimage_no_txs\n" ++
  "  j .Lbv_code_preimage_flag_done             # transactions present\n" ++
  ".Lbv_code_preimage_no_txs:\n" ++
  "  ld t5, 72(s0)\n" ++
  "  beqz t5, .Lbv_code_preimage_flag_done\n" ++
  "  li t6, 1; la t2, bbcv_skip_touch_only; sd t6, 0(t2)\n" ++
  ".Lbv_code_preimage_flag_done:\n" ++
  "  li t6, 1; la t2, bbcv_fee_recipient_valid; sd t6, 0(t2)\n  la a0, bbcv_fee_recipient; ld a1, 0(s0); addi a1, a1, 32; li a2, 20\n  jal ra, mset_memcpy\n" ++
  "  la t2, bv_bal_start; ld a0, 0(t2)\n" ++
  "  la t2, bv_bal_len; ld a1, 0(t2)\n" ++
  "  ld a2, 8(s0)                  # parent header RLP\n" ++
  "  ld a3, 16(s0)                 # parent header RLP length\n" ++
  "  ld a4, 80(s0)                 # witness.state ptr\n" ++
  "  ld a5, 88(s0)                 # witness.state len\n" ++
  "  la t2, svf_codes_ptr; ld a6, 0(t2)\n" ++
  "  la t2, svf_codes_len; ld a7, 0(t2)\n" ++
  "  jal ra, bal_code_preimages_valid\n" ++
  "  bnez a0, .Lbv_code_preimage_fail\n" ++
  "  # Upfront sender gas pre-charge gate for the currently parse-supported\n" ++
  "  # one-transaction path. Use the selected public key tail (x||y) and the\n" ++
  "  # pre-account record table materialized by block_state_root.\n" ++
  -- evm-asm-fhsxz.2.4.2.57.11.6.2.2.2: gated multi-transaction runtime gas loop.
  -- tx_count==1 (and the degenerate 0-tx block) fall through to the existing
  -- single-tx path BYTE-IDENTICALLY. For 2..16 transactions, only when the block
  -- is INDEPENDENT (bal_txs_independent==0: no account's storage/code/nonce touched
  -- by more than one tx_index) AND every recipient is a self-contained contract,
  -- dispatch each tx against the block-PRE state to measure its runtime gas,
  -- populate the strided runtime-result arrays, and set bvgr_runtime_count=tx_count
  -- so block_verdict_gas_result_arena_prepare + the EIP-7778/8037 block-gas gate
  -- run. Independence makes per-tx pre-state dispatch exact; the per-tx refund is
  -- read from evm_refund_acc (the dispatcher's EIP-3529 SSTORE refund accumulator,
  -- reset per dispatch) so the receipt-gas increment (receipt_inc) is exact; the
  -- EIP-7778 block-gas gate stays refund-independent (block_inc). Any non-independence / unsupported
  -- tx shape / EOA recipient / dispatch miss bails to the conservative path
  -- (bvgr_runtime_count left 0 -> arena count mismatch -> block-gas gate skipped),
  -- i.e. today's behavior, so valid multi-tx blocks are never newly false-rejected.
  "  la t0, bv_tx_count; ld t0, 0(t0); li t1, 1; beq t0, t1, .Lbv_singletx\n" ++
  "  li t1, 2; bltu t0, t1, .Lbv_singletx          # 0-tx block -> existing path\n" ++
  "  li t1, " ++ toString bvMtxArenaTxCap ++ "; bgtu t0, t1, .Lbv_mtx_bail         # arena capacity\n" ++
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  jal ra, bal_txs_independent\n" ++
  "  bnez a0, .Lbv_mtx_bail                         # interacting / parse error -> conservative\n" ++
  "  la t0, bv_mtx_i; sd zero, 0(t0)\n" ++
  "  la t0, bv_mtx_committed_count; sd zero, 0(t0)  # fhsxz.2.4.2.57.11.6.3.2: empty cross-tx committed table\n" ++
  -- bmvmx.5 (fee-validity hoist, multi-tx): multi_tx_nth_context does NOT populate the
  -- record's base_fee_per_gas (record+32 is a per-call INPUT, BlockVerdictMultiTx.lean:44),
  -- so compute the BLOCK base_fee once here (it is block-level, identical for every tx) by
  -- reversing the payload's SSZ little-endian base_fee at bv_exec_p+440 into BE
  -- (bv_mtx_base_fee_be), mirroring the single-tx envelope reversal at line ~101. The per-tx
  -- fee gate below points tx_effective_gas_pricing's a2 at this buffer. bv_exec_p was set
  -- unconditionally at line ~77 (before the tx-count split), so it is valid here.
  "  la t4, bv_exec_p; ld t4, 0(t4); addi t1, t4, 440; la t2, bv_mtx_base_fee_be; li t3, 0\n" ++
  ".Lbv_mtx_bf_rev:\n" ++
  "  li t0, 32; beq t3, t0, .Lbv_mtx_bf_rev_done\n" ++
  "  add t0, t1, t3; lbu t5, 0(t0); li t6, 31; sub t6, t6, t3; add t6, t2, t6; sb t5, 0(t6); addi t3, t3, 1; j .Lbv_mtx_bf_rev\n" ++
  ".Lbv_mtx_bf_rev_done:\n" ++
  "  la t0, bv_mtx_nonce_seen_count; sd zero, 0(t0)\n" ++
  ".Lbv_mtx_loop:\n" ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); la t2, bv_tx_count; ld t2, 0(t2); beq t1, t2, .Lbv_mtx_done\n" ++
  "  la a0, bv_mtx_ctx; mv a1, t1; jal ra, multi_tx_nth_context\n" ++
  "  la t0, bv_mtx_ctx; ld t2, 0(t0); bnez t2, .Lbv_mtx_bail; ld t2, 48(t0); bnez t2, .Lbv_mtx_creation_unsupported        # creation tx shape\n" ++
  -- bmvmx.5 (fee-validity hoist, multi-tx): same PATH-INDEPENDENT check_transaction
  -- fee-validity test as the single-tx gate (max_fee>=base_fee / priority<=max_fee),
  -- run per tx in the mtx loop. bv_mtx_ctx holds tx ptr@8 / len@16 (simple_transfer layout,
  -- BlockVerdictMultiTx.lean:38); base_fee comes from bv_mtx_base_fee_be (computed above —
  -- record+32 is NOT filled by multi_tx_nth_context). Placed before the contract/EOA-recipient
  -- routing so it covers EVERY status-0 tx the loop reaches. tx_effective_gas_pricing returns
  -- 2 (priority>max_fee) / 3 (max_fee<base_fee) for the two spec errors; status 1 (extraction
  -- failed) / 4 (egp overflow) -> fall through. An invalid-fee tx is spec-rejected regardless
  -- of recipient type, and a valid block never carries one, so this only ADDS spec-faithful
  -- rejects -- no false-reject. (t1 is reset at the code-hash compare / reloaded from bv_mtx_i
  -- later; s0-s3 preserved by the call.)
  "  la t2, bv_mtx_ctx\n" ++
  "  ld a0, 8(t2); ld a1, 16(t2); la a2, bv_mtx_base_fee_be\n" ++   -- tx ptr, tx len, block base_fee (BE)
  "  la a3, bv_fee_egp_scratch; la a4, bv_fee_prio_scratch\n" ++
  "  jal ra, tx_effective_gas_pricing\n" ++
  "  li t1, 2; beq a0, t1, .Lbv_fee_invalid_fail\n" ++          -- priority_fee > max_fee -> reject
  "  li t1, 3; beq a0, t1, .Lbv_fee_invalid_fail\n" ++          -- max_fee < base_fee -> reject
  -- bmvmx.5 (multi-tx nonce lower-bound, path-independent like the fee check above): the
  -- single-tx @1082 nonce check (tx.nonce == sender_pre_nonce) does NOT cover the mtx loop, so a
  -- multi-tx block carrying a tx whose nonce is BELOW the sender's pre-state nonce is currently
  -- accepted (the spec rejects it, NonceMismatchError). SOUND-PARTIAL check: reject if
  -- tx.nonce < sender_pre_nonce. Valid txs always have nonce >= the account's block-start nonce
  -- (==pre for the sender's first tx, >pre for a sequenced later tx), so this NEVER false-rejects;
  -- it catches the below-pre adversarial case; the running-count check below also rejects nonce reuse and too-high nonces.
  -- sttc_nonce holds THIS tx's nonce (multi_tx_nth_context wrote it via tx_extract_nonce_and_gas).
  -- sender = address_from_pubkey(public_keys[i]+1): public_keys[i] = bv_public_keys_ptr + i*65
  -- (65-byte SEC1 0x04||x||y, verified bound to tx[i]'s signer by verify_public_keys_match_senders).
  -- i*65 = (i<<6)+i. account_at_header_state_root(pre-state) -> sender acct, nonce@0. s0+8/16/80/88
  -- are the same lookup args the legacy sender lookup uses (@128). Lookup fail/absent -> skip
  -- (conservative; an absent sender has pre_nonce 0 and tx.nonce>=0, so the check is a no-op anyway).
  "  la t0, bv_mtx_i; ld t1, 0(t0)\n" ++
  "  slli t2, t1, 6; add t1, t2, t1\n" ++                       -- t1 = i*65
  "  la t0, bv_public_keys_ptr; ld t0, 0(t0); add t0, t0, t1; addi a0, t0, 1\n" ++  -- a0 = public_keys[i]+1 (skip 0x04)
  "  la a1, bv_mtx_sender_addr; jal ra, address_from_pubkey\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); la a2, bv_mtx_sender_addr; li a3, 20; ld a4, 80(s0); ld a5, 88(s0); la a6, bv_mtx_sender_acct\n" ++
  "  jal ra, account_at_header_state_root\n" ++
  "  bnez a0, .Lbv_mtx_nonce_done\n" ++                         -- sender lookup failed/absent -> skip
  "  la t0, bv_mtx_sender_acct; ld t0, 0(t0)\n" ++              -- t0 = sender block-start (pre-state) nonce
  -- EXACT multi-tx nonce: tx.nonce must == pre_nonce + the running count already seen for
  -- this sender address in the current block. A sender's k-th tx (0-based) executes at nonce
  -- pre+k. The running table is updated in tx order, so this avoids rescanning prior public
  -- keys for every tx while preserving the same reject condition for nonce reuse and too-high
  -- nonces. Sound: valid blocks sequence each sender's txs as pre,pre+1,...
  "  la t1, bv_mtx_nonce_pre; sd t0, 0(t1)\n" ++                -- stash pre_nonce across table update
  "  la t2, bv_mtx_nonce_seen_count; ld t3, 0(t2); li t4, 0\n" ++ -- t3 = distinct count, t4 = k
  ".Lbv_mtx_seq_scan:\n" ++
  "  bgeu t4, t3, .Lbv_mtx_seq_new\n" ++
  "  slli t5, t4, 5; la t6, bv_mtx_nonce_seen_addrs; add t6, t6, t5; li a0, 0\n" ++ -- t6 = addr[k]
  ".Lbv_mtx_seq_cmp:\n" ++
  "  li a1, 20; beq a0, a1, .Lbv_mtx_seq_found\n" ++
  "  add a2, t6, a0; lbu a3, 0(a2); la a4, bv_mtx_sender_addr; add a4, a4, a0; lbu a5, 0(a4); bne a3, a5, .Lbv_mtx_seq_next\n" ++
  "  addi a0, a0, 1; j .Lbv_mtx_seq_cmp\n" ++
  ".Lbv_mtx_seq_next:\n" ++
  "  addi t4, t4, 1; j .Lbv_mtx_seq_scan\n" ++
  ".Lbv_mtx_seq_found:\n" ++
  "  slli t5, t4, 3; la t6, bv_mtx_nonce_seen_counts; add t6, t6, t5; ld t5, 0(t6); addi a0, t5, 1; sd a0, 0(t6); j .Lbv_mtx_seq_done\n" ++
  ".Lbv_mtx_seq_new:\n" ++
  "  li a0, 16; bgeu t3, a0, .Lbv_sender_nonce_fail\n" ++
  "  slli t5, t3, 5; la t6, bv_mtx_nonce_seen_addrs; add t6, t6, t5; li a0, 0\n" ++
  ".Lbv_mtx_seq_copy:\n" ++
  "  li a1, 20; beq a0, a1, .Lbv_mtx_seq_new_count\n" ++
  "  la a2, bv_mtx_sender_addr; add a2, a2, a0; lbu a3, 0(a2); add a4, t6, a0; sb a3, 0(a4); addi a0, a0, 1; j .Lbv_mtx_seq_copy\n" ++
  ".Lbv_mtx_seq_new_count:\n" ++
  "  slli a0, t3, 3; la a1, bv_mtx_nonce_seen_counts; add a1, a1, a0; li a2, 1; sd a2, 0(a1); addi t3, t3, 1; la a0, bv_mtx_nonce_seen_count; sd t3, 0(a0); li t5, 0\n" ++
  ".Lbv_mtx_seq_done:\n" ++
  "  la t0, bv_mtx_nonce_pre; ld t0, 0(t0)\n" ++
  "  add t0, t0, t5\n" ++                                       -- t0 = expected = pre_nonce + count
  "  la t1, sttc_nonce; ld t1, 0(t1)\n" ++                      -- t1 = tx.nonce
  "  bne t1, t0, .Lbv_sender_nonce_fail\n" ++                   -- tx.nonce != pre+count -> reject (Nonce*Error)
  -- bmvmx.5 (multi-tx upfront-balance lower bound): reject if sender_pre_balance <
  -- gas_limit*max_fee_per_gas + blob_gas*max_fee_per_blob_gas + tx.value (spec check_transaction InsufficientBalanceError,
  -- amsterdam fork.py). Mirrors the single-tx upfront check @1123-1138, swapping the operands to
  -- the mtx sources: max_fee = tefgp_max_fee (tx_effective_gas_pricing wrote it at @453 above),
  -- gas_limit = bv_mtx_ctx+40, value = bv_mtx_ctx+96 (multi_tx_nth_context simple_transfer layout),
  -- pre_balance = bv_mtx_sender_acct+8 (32B BE, from the account_at lookup just done). SOUND, no
  -- false-reject: a valid tx's sender covers its upfront (>= for the first tx, strictly > for a
  -- sequenced later tx), so pre_balance < upfront only for the definitely-insufficient case.
  -- (Exact per-sender prior-debit accounting is the sequencing follow-up; this lower bound holds
  -- without it.) Reuses the bv_upfront_cost/islt scratch; u256_mul_u64_be/add_be return 1 on
  -- overflow (a*b or sum >= 2^256 -> upfront unaffordable -> reject); u256_lt_be writes 1 iff a<b.
  "  la a0, tefgp_max_fee\n" ++
  "  la t0, bv_mtx_ctx; ld a1, 40(t0)\n" ++                     -- gas_limit (u64)
  "  la a2, bv_upfront_cost\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++                    -- gas_limit*max_fee >= 2^256 -> reject
  "  la a0, bv_upfront_cost\n" ++
  "  la t0, bv_mtx_ctx; addi a1, t0, 96\n" ++                   -- tx.value (32B BE)
  "  la a2, bv_upfront_cost\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++                    -- upfront + value >= 2^256 -> reject
  "  la t0, bv_mtx_ctx; ld t1, 160(t0); li t2, 3; bne t1, t2, .Lbv_mtx_upfront_blob_done\n" ++
  "  ld a0, 176(t0); ld a1, 184(t0); la a2, tcbg_struct\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  "  la t0, tcbg_struct; lwu t1, 168(t0); lwu t2, 172(t0)\n" ++
  "  la t3, bv_mtx_ctx; ld t3, 176(t3); add a0, t3, t1; mv a1, t2; la a2, bv_upfront_blob_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  "  la t0, bv_upfront_blob_count; ld a1, 0(t0); beqz a1, .Lbv_sender_upfront_fail\n" ++
  "  li t2, 6; bgtu a1, t2, .Lbv_sender_upfront_fail\n" ++
  "  slli a1, a1, 17\n" ++
  "  la a0, tcbg_blob_fee_be; la a2, bv_upfront_blob_cost\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  "  la a0, bv_upfront_cost; la a1, bv_upfront_blob_cost; la a2, bv_upfront_cost\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  ".Lbv_mtx_upfront_blob_done:\n" ++
  "  la a0, bv_mtx_sender_acct; addi a0, a0, 8\n" ++            -- sender pre_balance (32B BE)
  "  la a1, bv_upfront_cost\n" ++
  "  la a2, bv_upfront_islt\n" ++
  "  jal ra, u256_lt_be\n" ++
  "  la t0, bv_upfront_islt; ld t0, 0(t0)\n" ++
  "  bnez t0, .Lbv_sender_upfront_fail\n" ++                    -- pre_balance < upfront -> reject
  ".Lbv_mtx_nonce_done:\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); la a2, bv_mtx_ctx; addi a2, a2, 72; ld a3, 80(s0); ld a4, 88(s0); la a5, bv_tx_recipient_code_hash\n" ++
  "  jal ra, code_hash_at_header_state_root\n" ++
  -- fhsxz.2.4.2.57.11.6.5.4 (e): code 2 = MPT could not resolve this tx's recipient at the
  -- pre-state root. The recipient is ACCESSED (the tx sends to it), so a complete stateless
  -- witness MUST carry it -> code 2 means the witness genuinely lacks a node on its path
  -- (verified: the multi_transaction_gas_accounting GAS_USED_OVERFLOW witness omits tx1's
  -- recipient node, 22 vs the valid variant's 24 nodes). An unverifiable accessed account =>
  -- the block cannot be statelessly validated as valid => REJECT (not conservative-accept,
  -- which was the false-accept). A valid block's witness always resolves the recipient
  -- (code 0), so this never false-rejects. Codes 3/4 (decode/header) stay conservative.
  "  li t1, 2; beq a0, t1, .Lbv_mtx_recipient_unresolvable_fail\n" ++
  "  bnez a0, .Lbv_mtx_bail                         # other lookup failure (3/4) -> conservative\n" ++
  "  la t0, bv_tx_recipient_code_hash; la t1, chahsr_empty_code_hash\n" ++
  "  ld t3,  0(t0); ld t4,  0(t1); bne t3, t4, .Lbv_mtx_is_contract\n" ++
  "  ld t3,  8(t0); ld t4,  8(t1); bne t3, t4, .Lbv_mtx_is_contract\n" ++
  "  ld t3, 16(t0); ld t4, 16(t1); bne t3, t4, .Lbv_mtx_is_contract\n" ++
  "  ld t3, 24(t0); ld t4, 24(t1); bne t3, t4, .Lbv_mtx_is_contract\n" ++
  blockVerdictMtxEoaSettlement ++
  ".Lbv_mtx_is_contract:\n" ++
  -- bmvmx.1.6.6 multi-tx enabler: stamp this user tx's block_access_index = i+1 (EIP-7928:
  -- 0 for system, i+1 for the i-th user tx; fork.py:1030) so the SSTORE handler tags every
  -- exec-log entry it appends during this dispatch with the right per-tx index. Without this
  -- the loop leaves current_block_access_index at its single-tx default 1, and the per-tx
  -- tuple-sequence comparators (bmvmx.1.6.6) would see tx i>0 writes mis-indexed as 1.
  -- Additive/inert today: exec_log_txindex is consumed only by those (still-unwired) checks.
  "  la t0, bv_mtx_i; ld t1, 0(t0); addi t1, t1, 1; la t0, current_block_access_index; sd t1, 0(t0)\n" ++
  -- fhsxz.2.4.2.57.11.6.5: gate the PRE-state header to THIS (mtx) dispatch call only.
  -- Single-tx dispatch (.Lbv_cd_* path, line ~717) leaves the flag 0 -> sv_this_rlp,
  -- byte-identical to #8686 (no >10% regression recurrence). Reset immediately after.
  "  li t0, 1; la t1, dtrc_use_pre_header; sd t0, 0(t1)\n" ++
  -- bmvmx.7.2: multi-tx contract-recipient top-level EIP-7708 value-transfer log.
  -- Emit before runtime dispatch so the block log window preserves spec order: top-level
  -- value move first, then logs produced by the recipient code. If append overflows, leave
  -- the completeness flag unset and let the receipts gate stay conservative.
  "  la t0, bv_mtx_ctx; addi t0, t0, 96; ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2; ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2\n" ++
  "  beqz t1, .Lbv_mtx_tl7708_skip\n" ++
  "  la t0, bv_mtx_sender_addr; la t1, bv_mtx_ctx; addi t1, t1, 72; li t2, 20\n" ++
  ".Lbv_mtx_tl_selfcmp:\n" ++
  "  beqz t2, .Lbv_mtx_tl7708_skip\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_mtx_tl_notself\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_mtx_tl_selfcmp\n" ++
  ".Lbv_mtx_tl_notself:\n" ++
  "  addi sp, sp, -16\n  sd x20, 0(sp)\n" ++
  "  la t0, eip7708_tl_from32\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, bv_mtx_sender_addr; addi t1, t1, 19; mv t2, t0; li t3, 20\n" ++
  ".Lbv_mtx_tl_from:\n  beqz t3, .Lbv_mtx_tl_from_d\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbv_mtx_tl_from\n" ++
  ".Lbv_mtx_tl_from_d:\n" ++
  "  la t0, eip7708_tl_to32\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, bv_mtx_ctx; addi t1, t1, 91; mv t2, t0; li t3, 20\n" ++
  ".Lbv_mtx_tl_to:\n  beqz t3, .Lbv_mtx_tl_to_d\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbv_mtx_tl_to\n" ++
  ".Lbv_mtx_tl_to_d:\n" ++
  "  la t0, eip7708_tl_val32\n  la t1, bv_mtx_ctx; addi t1, t1, 127; mv t2, t0; li t3, 32\n" ++
  ".Lbv_mtx_tl_val:\n  beqz t3, .Lbv_mtx_tl_val_d\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbv_mtx_tl_val\n" ++
  ".Lbv_mtx_tl_val_d:\n" ++
  "  la x20, evm_env\n  la a0, eip7708_tl_from32\n  la a1, eip7708_tl_to32\n  la a2, eip7708_tl_val32\n" ++
  "  jal ra, eip7708_append_transfer_log\n" ++
  "  ld x20, 0(sp)\n  addi sp, sp, 16\n" ++
  "  bnez a0, .Lbv_mtx_tl7708_skip\n" ++
  "  li t1, 1; la t0, eip7708_tl_typed_avail; sd t1, 0(t0)\n" ++
  ".Lbv_mtx_tl7708_skip:\n" ++
  "  la a0, bv_mtx_ctx; ld a1, 80(s0); ld a2, 88(s0); jal ra, dispatch_tx_runtime_code\n" ++
  "  la t0, bv_dispatch_runtime_status; sd a0, 0(t0)\n  la t1, dtrc_use_pre_header; sd zero, 0(t1)\n" ++
  "  bnez a0, .Lbv_mtx_dispatch_unsupported                         # structured dispatch bail reason\n" ++
  bvReceiptsShapeSet 5 true ++  -- fhsxz.2.4.2.57.11.6.5.2.1 P1: persist this tx's executed state gas into bvgr_tx_exec_state_gas[i]
  -- (i = bv_mtx_i; evm_state_gas_used is fresh per-tx). Clobbers only a0/t0-t2, preserves the dispatch
  -- results a1-a4 used below. Behavior-neutral substrate (array not yet read by the gate).
  "  la a0, bv_mtx_i; ld a0, 0(a0); jal ra, dispatcher_capture_exec_state_gas\n" ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); slli t0, t1, 3\n" ++
  "  la t3, bv_mtx_gas_left; add t3, t3, t0; sd a1, 0(t3)\n" ++
  "  la t3, bv_mtx_calldata; add t3, t3, t0; sd a2, 0(t3)\n" ++
  -- nxio8: a3 = the settle-folded refund counter (0 when the tx erred), not a
  -- raw evm_refund_acc read.
  "  la t3, bv_mtx_refund;   add t3, t3, t0; sd a3, 0(t3)\n" ++
  "  la t3, bv_tx_status_arr; add t3, t3, t0; sd a4, 0(t3)\n" ++   -- .63.1.6.2.1: receipt status, tx i
  "  slli t4, t1, 4\n" ++   -- .63.1.6.2.1: per-tx log window (16-byte stride)
  "  la t3, bv_tx_log_window; add t3, t3, t4\n" ++
  "  la t4, bv_last_log_start; ld t5, 0(t4); sd t5, 0(t3)\n" ++
  "  la t4, bv_last_log_count; ld t5, 0(t4); sd t5, 8(t3)\n" ++
  -- fhsxz.2.4.2.57.11.6.3.2: snapshot this tx's committed storage into the cross-tx table,
  -- re-keyed (addrHash) to its recipient (bv_mtx_ctx+72, 20B zero-padded to 32) so the next
  -- tx's preload can thread a prior tx's committed value. The live exec log (env+448 entries
  -- at 0xa0630000) holds the recipient's own slots only (dispatch_tx_runtime_code requires
  -- self-contained), so a single recipient re-tag is correct. Append (last-write-wins via
  -- exec_log_latest_value's last-match); bail conservatively if the table overflows.
  "  la t0, evm_env; ld t0, 448(t0)                 # t0 = live log entry count\n" ++
  "  la t1, bv_mtx_committed_count; ld t1, 0(t1)    # t1 = table count\n" ++
  "  li t2, 0xa0630000                              # t2 = live log base\n" ++
  "  li t3, 0                                       # j = 0\n" ++
  ".Lbv_mtx_snap:\n" ++
  "  beq t3, t0, .Lbv_mtx_snap_done\n" ++
  "  li t4, 128; bgeu t1, t4, .Lbv_mtx_bail         # committed table full -> conservative\n" ++
  "  slli t4, t3, 7; add t4, t2, t4                 # src = live[j]\n" ++
  "  slli t5, t1, 7; la t6, bv_mtx_committed; add t5, t6, t5   # dst = table[count]\n" ++
  "  sd zero, 0(t5); sd zero, 8(t5); sd zero, 16(t5); sd zero, 24(t5)   # addrHash = 0, then recipient 20B\n" ++
  "  la t6, bv_mtx_ctx; addi t6, t6, 72; li a0, 0\n" ++
  ".Lbv_mtx_snap_k:\n" ++
  "  li a1, 20; beq a0, a1, .Lbv_mtx_snap_kd\n" ++
  "  add a2, t6, a0; lbu a3, 0(a2); add a2, t5, a0; sb a3, 0(a2); addi a0, a0, 1; j .Lbv_mtx_snap_k\n" ++
  ".Lbv_mtx_snap_kd:\n" ++
  "  ld a0, 32(t4);  sd a0, 32(t5);  ld a0, 40(t4);  sd a0, 40(t5)\n" ++   -- slotKey
  "  ld a0, 48(t4);  sd a0, 48(t5);  ld a0, 56(t4);  sd a0, 56(t5)\n" ++
  "  ld a0, 64(t4);  sd a0, 64(t5);  ld a0, 72(t4);  sd a0, 72(t5)\n" ++   -- original
  "  ld a0, 80(t4);  sd a0, 80(t5);  ld a0, 88(t4);  sd a0, 88(t5)\n" ++
  "  ld a0, 96(t4);  sd a0, 96(t5);  ld a0, 104(t4); sd a0, 104(t5)\n" ++  -- current
  "  ld a0, 112(t4); sd a0, 112(t5); ld a0, 120(t4); sd a0, 120(t5)\n" ++
  "  addi t1, t1, 1; addi t3, t3, 1; j .Lbv_mtx_snap\n" ++
  ".Lbv_mtx_snap_done:\n" ++
  "  la t4, bv_mtx_committed_count; sd t1, 0(t4)\n" ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lbv_mtx_loop\n" ++
  ".Lbv_mtx_done:\n" ++
  "  la t4, bvgr_runtime_gas_left_ptr; la t5, bv_mtx_gas_left; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_refund_counter_ptr; la t5, bv_mtx_refund; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_calldata_floor_ptr; la t5, bv_mtx_calldata; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_count; la t5, bv_tx_count; ld t5, 0(t5); sd t5, 0(t4)\n" ++
  blockVerdictMtxValidationTail ++
  ".Lbv_mtx_creation_unsupported:\n" ++
  bvReceiptsShapeSet 60 false ++
  "  j .Lbv_mtx_bail_after_shape\n" ++
  ".Lbv_mtx_dispatch_unsupported:\n" ++
  bvRuntimeCompletenessSet 4 ++ bvReceiptsShapeSet 61 false ++
  "  j .Lbv_mtx_bail_after_shape\n" ++
  ".Lbv_mtx_bail:\n" ++
  bvRuntimeCompletenessSet 5 ++ bvReceiptsShapeSet 62 false ++  ".Lbv_mtx_bail_after_shape:\n" ++
  "  j .Lbv_after_tx_gas_precharge\n" ++
  ".Lbv_singletx:\n" ++
  "  la a0, bv_simple_transfer_tx\n" ++
  "  jal ra, simple_transfer_tx_context\n" ++
  "  la t2, bv_simple_transfer_tx; ld t0, 0(t2); bnez t0, .Lbv_after_tx_gas_precharge; ld t0, 48(t2); bnez t0, .Lbv_creation_unsupported\n" ++
  -- bmvmx.5 (fee-validity hoist, single-tx): the spec check_transaction fee-validity
  -- pre-conditions -- max_fee_per_gas >= base_fee_per_gas (InsufficientMaxFeePerGasError)
  -- and max_priority_fee_per_gas <= max_fee_per_gas (PriorityFeeGreaterThanMaxFeeError,
  -- amsterdam/fork.py check_transaction) -- are PATH-INDEPENDENT: they read only the tx
  -- fee fields and the block base_fee, no execution or sender lookup. They were enforced
  -- ONLY inside the value-movement-free contract path (.Lbv_sbc_safe status 50, ~line 1006),
  -- so a value-MOVING contract recipient (CALL/DELEGATECALL/SELFDESTRUCT bytecode), a
  -- coinbase sender, or a block with withdrawals collateral-SKIPPED the fee check -- a
  -- latent false-accept (an adversarial max_fee<base_fee / priority>max_fee tx on those
  -- paths is spec-rejected but guest-accepted). Hoist it here, UNCONDITIONALLY for the
  -- single tx, before the value-move / EOA-vs-contract split. tx_effective_gas_pricing
  -- returns 2 (priority>max_fee) / 3 (max_fee<base_fee) for exactly those two spec errors;
  -- status 1 (extraction failed) / 4 (egp overflow) are "cannot determine" -> fall through
  -- (never newly false-reject). A valid block never carries such a tx, so this only ADDS
  -- rejects the spec also makes -- strictly sound, no false-reject. (Multi-tx loop fee gate
  -- + the nonce-eligibility/upfront-balance hoists are bmvmx.5 follow-ups.)
  "  la t2, bv_simple_transfer_tx\n" ++
  "  ld a0, 8(t2); ld a1, 16(t2); ld a2, 32(t2)\n" ++           -- tx ptr, tx len, base_fee_per_gas ptr
  "  la a3, bv_fee_egp_scratch; la a4, bv_fee_prio_scratch\n" ++
  "  jal ra, tx_effective_gas_pricing\n" ++
  "  li t1, 2; beq a0, t1, .Lbv_fee_invalid_fail\n" ++          -- priority_fee > max_fee -> reject
  "  li t1, 3; beq a0, t1, .Lbv_fee_invalid_fail\n" ++          -- max_fee < base_fee -> reject
  "  la t2, bv_simple_transfer_tx\n" ++                         -- restore t2 (jal clobbered it) for the code-hash route below
  -- evm-asm-fhsxz.2.4.2.57.11.6.4.3.2: route a contract recipient (non-empty code)
  -- to the execution-derived contract dispatch; EOA (empty-code) recipients fall
  -- through to the existing simple-transfer path BYTE-IDENTICALLY (no regression).
  "  ld a0, 8(s0); ld a1, 16(s0); addi a2, t2, 72; ld a3, 80(s0); ld a4, 88(s0); la a5, bv_tx_recipient_code_hash\n" ++
  "  jal ra, code_hash_at_header_state_root\n" ++
  "  bnez a0, .Lbv_cd_eoa_restore        # code-hash lookup failed -> conservative EOA path\n" ++
  "  la t0, bv_tx_recipient_code_hash; la t1, chahsr_empty_code_hash\n" ++
  "  ld t3,  0(t0); ld t4,  0(t1); bne t3, t4, .Lbv_contract_dispatch\n" ++
  "  ld t3,  8(t0); ld t4,  8(t1); bne t3, t4, .Lbv_contract_dispatch\n" ++
  "  ld t3, 16(t0); ld t4, 16(t1); bne t3, t4, .Lbv_contract_dispatch\n" ++
  "  ld t3, 24(t0); ld t4, 24(t1); bne t3, t4, .Lbv_contract_dispatch\n" ++
  ".Lbv_cd_eoa_restore:\n" ++
  "  la t2, bv_simple_transfer_tx        # restore t2 for the EOA path (jal clobbered it)\n" ++
  "  ld t0, 64(t2); bnez t0, .Lbv_after_tx_gas_precharge  # EOA calldata not staged here\n" ++
  "  ld t0,  96(t2); bnez t0, .Lbv_tx_gas_precharge_nonzero_value\n" ++
  "  ld t0, 104(t2); bnez t0, .Lbv_tx_gas_precharge_nonzero_value\n" ++
  "  ld t0, 112(t2); bnez t0, .Lbv_tx_gas_precharge_nonzero_value\n" ++
  "  ld t0, 120(t2); beqz t0, .Lbv_after_tx_gas_precharge\n" ++
  ".Lbv_tx_gas_precharge_nonzero_value:\n" ++
  "  # The post-balance verifier below models an EOA simple transfer: sender\n" ++
  "  # final balance = precharge + unused intrinsic refund - value. For value\n" ++
  "  # transfers into contracts, bytecode execution spends additional gas, so\n" ++
  "  # leave the verdict to the state-root/BAL checks instead.\n" ++
  "  # Direct transfers to active precompiles also execute code despite having\n" ++
  "  # no state-trie code hash; skip this 21k-only verifier for them too.\n" ++
  "  mv t0, t2; addi t0, t0, 72; li t1, 0\n" ++
  ".Lbv_tx_gas_precharge_pc_prefix:\n" ++
  "  li t3, 18; beq t1, t3, .Lbv_tx_gas_precharge_pc_low16\n" ++
  "  add t3, t0, t1; lbu t4, 0(t3); bnez t4, .Lbv_tx_gas_precharge_not_precompile\n" ++
  "  addi t1, t1, 1; j .Lbv_tx_gas_precharge_pc_prefix\n" ++
  ".Lbv_tx_gas_precharge_pc_low16:\n" ++
  "  lbu t3, 18(t0); lbu t4, 19(t0); slli t3, t3, 8; or t3, t3, t4\n" ++
  "  li t4, 1; bltu t3, t4, .Lbv_tx_gas_precharge_not_precompile\n" ++
  "  li t4, 17; bgeu t4, t3, .Lbv_after_tx_gas_precharge\n" ++
  "  li t4, 256; beq t3, t4, .Lbv_after_tx_gas_precharge\n" ++
  ".Lbv_tx_gas_precharge_not_precompile:\n" ++  "  ld a0, 8(s0); ld a1, 16(s0); addi a2, t2, 72; ld a3, 80(s0); ld a4, 88(s0); la a5, bv_tx_recipient_code_hash\n" ++
  "  jal ra, code_hash_at_header_state_root\n" ++
  "  bnez a0, .Lbv_tx_gas_precharge_fail\n" ++
  "  la t0, bv_tx_recipient_code_hash; la t1, chahsr_empty_code_hash\n" ++
  "  ld t3,  0(t0); ld t4,  0(t1); bne t3, t4, .Lbv_after_tx_gas_precharge\n" ++
  "  ld t3,  8(t0); ld t4,  8(t1); bne t3, t4, .Lbv_after_tx_gas_precharge\n" ++
  "  ld t3, 16(t0); ld t4, 16(t1); bne t3, t4, .Lbv_after_tx_gas_precharge\n" ++
  "  ld t3, 24(t0); ld t4, 24(t1); bne t3, t4, .Lbv_after_tx_gas_precharge\n" ++
  "  la t2, bv_simple_transfer_tx\n" ++
  "  ld t0, 160(t2); li t1, 3; beq t0, t1, .Lbv_after_tx_gas_precharge  # blob txs need blob-aware settlement\n" ++
  "  li t1, 4; beq t0, t1, .Lbv_after_tx_gas_precharge  # EIP-7702 auth-list intrinsic gas is not 21k-only\n" ++
  "  ld a0, 8(t2); ld a1, 16(t2); ld a3, 24(t2); ld a2, 32(t2)\n" ++
  "  la t2, bv_bal_start; ld a4, 0(t2)\n" ++
  "  la t2, bv_bal_len; ld a5, 0(t2)\n" ++
  "  la a6, basr_records; la a7, bv_tx_gas_precharge\n" ++
  "  jal ra, tx_gas_bal_post_verify\n" ++
  "  la t2, bv_tx_gas_precharge; ld t0, 0(t2); bnez t0, .Lbv_tx_gas_precharge_fail\n" ++
  "  # Non-overlapping EOA simple transfers must also expose recipient and\n" ++
  "  # fee-recipient BAL post balances matching value and priority-fee effects.\n" ++
  "  la t2, bv_simple_transfer_tx\n" ++
  "  la t0, bv_tx_gas_precharge\n" ++
  "  addi t3, t2, 72; addi t4, t0, 104; li t5, 20\n" ++
  ".Lbv_st_recipient_sender_cmp:\n" ++
  "  beqz t5, .Lbv_st_skip_recipient_overlap\n" ++
  "  lbu t6, 0(t3); lbu a0, 0(t4); bne t6, a0, .Lbv_st_recipient_distinct\n" ++
  "  addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lbv_st_recipient_sender_cmp\n" ++
  ".Lbv_st_recipient_distinct:\n" ++
  "  # Skip the strict recipient BAL balance check when the simple-transfer\n" ++
  "  # recipient is the block coinbase: that account's BAL post balance also\n" ++
  "  # folds in the priority fee (transaction_fee), so pre+value != post and\n" ++
  "  # the EIP-7708 coinbase-recipient case would false-reject even though the\n" ++
  "  # recomputed post-state root still anchors the coinbase balance. Mirrors\n" ++
  "  # the fee-recipient coinbase-overlap skip below.\n" ++
  "  ld t0, 0(s0); addi t0, t0, 32\n" ++
  "  la t1, bv_simple_transfer_tx; addi t1, t1, 72\n" ++
  "  li t5, 20\n" ++
  ".Lbv_st_recipient_coinbase_cmp:\n" ++
  "  beqz t5, .Lbv_st_skip_recipient_overlap\n" ++
  "  lbu t6, 0(t0); lbu a0, 0(t1); bne t6, a0, .Lbv_st_recipient_do_verify\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t5, t5, -1; j .Lbv_st_recipient_coinbase_cmp\n" ++
  ".Lbv_st_recipient_do_verify:\n" ++
  "  # EIP-7928/4895 (evm-asm-ouis9): like the fee-recipient skip below, the strict\n" ++
  "  # recipient post-balance check models recipient_post = recipient_pre + value.\n" ++
  "  # When the block has withdrawals the recipient may ALSO receive a withdrawal\n" ++
  "  # (e.g. bal_withdrawal_and_value_transfer_same_address), so\n" ++
  "  # post = pre + value + withdrawal and the strict check false-rejects. Skip it\n" ++
  "  # for blocks with withdrawals: the recomputed post-state root (which folds in\n" ++
  "  # both the value transfer and the withdrawal) already validates the balance.\n" ++
  "  # uyu11.1: instead of skipping the strict recipient check on withdrawal\n" ++
  "  # blocks (the old #8484 false-reject fix, which left a false-accept hole),\n" ++
  "  # compute the EIP-4895 withdrawal credit to the recipient and fold it into\n" ++
  "  # the check via strv_wd_credit, so expected = pre + value + withdrawal.\n" ++
  "  la t0, strv_wd_credit; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t2, svf_wds_count; ld a2, 0(t2); beqz a2, .Lbv_st_recipient_wd_done\n" ++
  "  la t2, bv_simple_transfer_tx; addi a0, t2, 72\n" ++
  "  la t2, svf_wds_ptr; ld a1, 0(t2)\n" ++
  "  la a3, strv_wd_credit\n" ++
  "  jal ra, bv_sum_withdrawals_to_address\n" ++
  ".Lbv_st_recipient_wd_done:\n" ++
  "  la t2, bv_simple_transfer_tx\n" ++
  "  addi a0, t2, 72; addi a1, t2, 96\n" ++
  "  la t2, bv_bal_start; ld a2, 0(t2)\n" ++
  "  la t2, bv_bal_len; ld a3, 0(t2)\n" ++
  "  la a4, basr_records; la a5, bv_simple_transfer_recipient\n" ++
  "  jal ra, simple_transfer_recipient_bal_verify\n" ++
  "  la t2, bv_simple_transfer_recipient; ld t0, 0(t2); bnez t0, .Lbv_simple_transfer_recipient_fail\n" ++
  ".Lbv_st_skip_recipient_overlap:\n" ++
  "  ld t0, 0(s0); addi t0, t0, 32\n" ++
  "  la t1, bv_tx_gas_precharge; addi t1, t1, 104\n" ++
  "  mv t3, t0; mv t4, t1; li t5, 20\n" ++
  ".Lbv_st_fee_sender_cmp:\n" ++
  "  beqz t5, .Lbv_st_skip_fee_overlap\n" ++
  "  lbu t6, 0(t3); lbu a0, 0(t4); bne t6, a0, .Lbv_st_fee_check_recipient\n" ++
  "  addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lbv_st_fee_sender_cmp\n" ++
  ".Lbv_st_fee_check_recipient:\n" ++
  "  ld t0, 0(s0); addi t0, t0, 32\n" ++
  "  la t1, bv_simple_transfer_tx; addi t1, t1, 72\n" ++
  "  mv t3, t0; mv t4, t1; li t5, 20\n" ++
  ".Lbv_st_fee_recipient_cmp:\n" ++
  "  beqz t5, .Lbv_st_skip_fee_overlap\n" ++
  "  lbu t6, 0(t3); lbu a0, 0(t4); bne t6, a0, .Lbv_st_fee_distinct\n" ++
  "  addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lbv_st_fee_recipient_cmp\n" ++
  ".Lbv_st_fee_distinct:\n" ++
  "  # EIP-7928/4895 (evm-asm-ouis9): the strict fee-recipient post-balance check\n" ++
  "  # below models coinbase_post = coinbase_pre + transaction_fee. When the block\n" ++
  "  # has withdrawals, the coinbase may ALSO be a withdrawal recipient (e.g.\n" ++
  "  # bal_withdrawal_to_coinbase), so post = pre + fee + withdrawal and the strict\n" ++
  "  # check false-rejects. Skip it for blocks with withdrawals: the recomputed\n" ++
  "  # post-state root (which folds in both the fee and the withdrawal) already\n" ++
  "  # validates the coinbase balance, so this redundant sanity check is dropped\n" ++
  "  # rather than risk a false reject.\n" ++
  "  # uyu11.1: instead of skipping the strict fee-recipient (coinbase) check on\n" ++
  "  # withdrawal blocks, compute the EIP-4895 withdrawal credit to the coinbase\n" ++
  "  # and fold it via stfv_wd_credit, so expected = pre + fee + withdrawal.\n" ++
  "  la t0, stfv_wd_credit; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t2, svf_wds_count; ld a2, 0(t2); beqz a2, .Lbv_st_fee_wd_done\n" ++
  "  ld a0, 0(s0); addi a0, a0, 32\n" ++
  "  la t2, svf_wds_ptr; ld a1, 0(t2)\n" ++
  "  la a3, stfv_wd_credit\n" ++
  "  jal ra, bv_sum_withdrawals_to_address\n" ++
  ".Lbv_st_fee_wd_done:\n" ++
  "  ld a0, 0(s0); addi a0, a0, 32\n" ++
  "  la t2, bv_simple_transfer_tx\n" ++
  "  ld a1, 8(t2); ld a2, 16(t2); ld a3, 32(t2)\n" ++
  "  la t2, bv_bal_start; ld a4, 0(t2)\n" ++
  "  la t2, bv_bal_len; ld a5, 0(t2)\n" ++
  "  la a6, basr_records; la a7, bv_simple_transfer_fee_recipient\n" ++
  "  jal ra, simple_transfer_fee_recipient_bal_verify\n" ++
  "  la t2, bv_simple_transfer_fee_recipient; ld t0, 0(t2); bnez t0, .Lbv_simple_transfer_fee_recipient_fail\n" ++
  ".Lbv_st_skip_fee_overlap:\n" ++
  -- bmvmx.1.2.4.6/.1 + bmvmx.1.3: run the staged STOP body through the callable
  -- runtime dispatcher and expose its gas result to
  -- block_verdict_gas_result_arena_prepare. The dispatcher-correctness fixes
  -- L1 (input-ptr +8, codeSize@x10-8), L2 (callable epilogue skips OUTPUT/state
  -- finalization) and L3 (caller-sp save/restore) make this re-enable fault-free.
  -- Unsupported shapes branch to .Lbv_after_tx_gas_precharge with
  -- bvgr_runtime_count left at 0.
  "  la a0, bv_simple_transfer_tx\n" ++
  "  la a1, bv_runtime_payload\n" ++
  "  la t2, bv_exec_p; ld a2, 0(t2)\n" ++
  "  jal ra, stage_runtime_payload\n" ++
  "  bnez a0, .Lbv_after_tx_gas_precharge\n" ++
  "  la t4, runtime_dispatcher_input_ptr; la t5, bv_runtime_payload; addi t5, t5, 8; sd t5, 0(t4)\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp); sd s3, 24(sp)\n" ++
  "  jal ra, runtime_dispatcher_call\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  la t4, runtime_dispatcher_input_ptr; sd zero, 0(t4)\n" ++
  -- fhsxz.2.4.2.63.1.6.2.6 Part 2: EIP-7708 top-level value-transfer log for this tx. The
  -- simple-transfer path has an EOA recipient (no recipient logs), so emitting post-dispatch
  -- here is ordering-safe and the snapshot below captures it as log 0. Sources are big-endian
  -- on the verdict side -- from = recovered sender (bmvmx_sender_addr), to = recipient
  -- (bmvmx_ctx+72), value = bmvmx_value -- reversed into the LE stack-word form the log
  -- materializer consumes (it byte-reverses each 32B topic slot back to canonical BE; the
  -- appender reverses the value back to BE at descriptor+160). Guarded on bmvmx_avail (the
  -- sender/recipient/value are only valid once the bmvmx compute set it) and value != 0. x20 is
  -- saved/restored: the appender uses x20+472 for the event-log count, so set x20 = evm_env;
  -- block_log_window_snapshot reads evm_env via `la`, so it is unaffected.
  "  la t0, bmvmx_avail; ld t0, 0(t0); bnez t0, .Lbv_tl7708_ready\n" ++
  -- bmvmx.7.1/bmvmx.7.3/57t4x: widen Part-2 top-level transfer-log coverage to the already-supported
  -- single typed simple-transfer runtime path, now including type-3 blob transfers and type-4 set-code transfers. Keep this independent from bmvmx_avail:
  -- the balance-movement verifier is still legacy-only, but receipts completeness only
  -- needs sender/recipient/value. simple_transfer_tx_context has already accepted the tx,
  -- so +24/+72/+96/+160 are populated here. Type 4 relies on the shared gas gate's
  -- authorization-list validation/gas accounting before this point. Reuse bmvmx_sender_addr/bmvmx_value so the
  -- legacy packing block below remains the single source for the EIP-7708 descriptor shape.
  "  la t0, bv_simple_transfer_tx; ld t1, 0(t0); bnez t1, .Lbv_tl7708_skip\n" ++
  "  ld t1, 160(t0); li t2, 1; beq t1, t2, .Lbv_tl_typed_ok\n" ++
  "  li t2, 2; beq t1, t2, .Lbv_tl_typed_ok\n" ++
  "  li t2, 3; beq t1, t2, .Lbv_tl_typed_ok\n" ++
  "  li t2, 4; bne t1, t2, .Lbv_tl7708_skip\n" ++
  ".Lbv_tl_typed_ok:\n" ++
  "  addi t1, t0, 96; la t2, bmvmx_value; li t3, 0\n" ++
  ".Lbv_tl_typed_vcopy:\n" ++
  "  li t4, 32; beq t3, t4, .Lbv_tl_typed_vdone\n" ++
  "  add t5, t1, t3; lbu t6, 0(t5); add t5, t2, t3; sb t6, 0(t5); addi t3, t3, 1; j .Lbv_tl_typed_vcopy\n" ++
  ".Lbv_tl_typed_vdone:\n" ++
  "  la t0, bv_simple_transfer_tx; ld a0, 24(t0); la a1, bmvmx_sender_addr; jal ra, address_from_pubkey\n" ++
  "  li t1, 1; la t0, eip7708_tl_typed_avail; sd t1, 0(t0)\n" ++
  bvReceiptsShapeSet 2 true ++  ".Lbv_tl7708_ready:\n" ++
  "  la t0, bmvmx_value; ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2; ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2\n" ++
  "  beqz t1, .Lbv_tl7708_skip\n" ++
  -- EIP-7708 self-suppression: emit the transfer log ONLY to a DIFFERENT account. The spec
  -- emits at the value-bearing call only when caller != current_target (amsterdam
  -- interpreter.py:314 / vm/__init__.py emit_transfer_log). For a top-level transfer to SELF
  -- (sender == recipient) NO log is emitted; without this guard the guest emits a spurious log
  -- -> extra receipt log -> receipts_root/logs_bloom mismatch -> false-reject (transfer_to_self_no_log).
  -- Compare the 20 BE address bytes: sender (bmvmx_sender_addr[0..19]) vs recipient (bmvmx_ctx+72..91).
  "  la t0, bmvmx_sender_addr; la t1, bmvmx_ctx; addi t1, t1, 72; li t2, 20\n" ++
  ".Lbv_tl_selfcmp:\n" ++
  "  beqz t2, .Lbv_tl7708_skip                # all 20 bytes equal -> self-transfer -> suppress log\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_tl_notself\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_tl_selfcmp\n" ++
  ".Lbv_tl_notself:\n" ++
  "  addi sp, sp, -16\n  sd x20, 0(sp)\n" ++
  -- from32 = reverse(bmvmx_sender_addr[0..19]) into the low 20 bytes (LE), high 12 zeroed
  "  la t0, eip7708_tl_from32\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, bmvmx_sender_addr; addi t1, t1, 19; mv t2, t0; li t3, 20\n" ++
  ".Lbv_tl_from:\n  beqz t3, .Lbv_tl_from_d\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbv_tl_from\n" ++
  ".Lbv_tl_from_d:\n" ++
  -- to32 = reverse(recipient bmvmx_ctx+72 [0..19]) into the low 20 bytes (LE)
  "  la t0, eip7708_tl_to32\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, bmvmx_ctx; addi t1, t1, 91; mv t2, t0; li t3, 20\n" ++
  ".Lbv_tl_to:\n  beqz t3, .Lbv_tl_to_d\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbv_tl_to\n" ++
  ".Lbv_tl_to_d:\n" ++
  -- val32 = reverse(bmvmx_value[0..31]) (LE; the appender re-reverses to canonical BE at +160)
  "  la t0, eip7708_tl_val32\n  la t1, bmvmx_value; addi t1, t1, 31; mv t2, t0; li t3, 32\n" ++
  ".Lbv_tl_val:\n  beqz t3, .Lbv_tl_val_d\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbv_tl_val\n" ++
  ".Lbv_tl_val_d:\n" ++
  "  la x20, evm_env\n  la a0, eip7708_tl_from32\n  la a1, eip7708_tl_to32\n  la a2, eip7708_tl_val32\n" ++
  "  jal ra, eip7708_append_transfer_log\n" ++
  "  ld x20, 0(sp)\n  addi sp, sp, 16\n" ++
  ".Lbv_tl7708_skip:\n" ++
  -- .63.1.6.2.1: snapshot the EOA dispatch's event-log window (now incl. the Part 2 top-level
  -- transfer log above), to be threaded into the per-tx receipt record.
  "  jal ra, block_log_window_snapshot\n" ++
  -- nxio8: settle fold (EIP-8037 state gas + tx-error rules) instead of a raw
  -- env[568] read; a0 = effective gas_left, a1 = effective refund counter.
  "  jal ra, dispatcher_tx_gas_settle\n" ++
  "  la t4, bv_runtime_gas_left; sd a0, 0(t4)\n" ++
  "  la t4, bv_runtime_refund_counter; sd a1, 0(t4)\n" ++
  "  la t4, bv_tx_status_arr; sd a2, 0(t4)\n" ++   -- .63.1.6.2.1: receipt status, tx 0
  "  la t4, bv_last_log_start; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 0(t4)\n" ++
  "  la t4, bv_last_log_count; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 8(t4)\n" ++
  "  la t4, runtime_tx_calldata_floor; ld t5, 0(t4)\n" ++
  "  la t4, bv_runtime_calldata_floor; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_gas_left_ptr; la t5, bv_runtime_gas_left; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_refund_counter_ptr; la t5, bv_runtime_refund_counter; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_calldata_floor_ptr; la t5, bv_runtime_calldata_floor; sd t5, 0(t4)\n" ++
  "  li t5, 1; la t4, bvgr_runtime_count; sd t5, 0(t4)\n" ++
  "  j .Lbv_after_tx_gas_precharge       # EOA runtime done; skip the contract-dispatch block\n" ++
  -- evm-asm-fhsxz.2.4.2.57.11.6.2.2.1: contract-recipient execution. Reached only
  -- from the early contract-vs-EOA branch. The runtime gas-measurement tail (stage
  -- bytecode + BAL recipient storage preload, run the callable dispatcher, read
  -- gas_left/calldata_floor) is now the reusable dispatch_tx_runtime_code helper so
  -- the multi-tx dispatch loop (.6.2.2.2) can measure each transaction the same way.
  -- It is still gated inside the helper on bytecode_is_self_contained, so we only
  -- feed runtime gas to the EIP-7778/8037 gate when execution is exact (own storage
  -- only, no un-staged state); any miss/unsupported returns non-zero and we stay
  -- conservative (branch to .Lbv_after_tx_gas_precharge with bvgr_runtime_count 0).
  -- The store sequence below mirrors the former inline tail, except the refund
  -- counter is now read from evm_refund_acc (the dispatcher's EIP-3529 SSTORE
  -- refund accumulator) instead of a hardcoded 0, so the recipient's receipt-gas
  -- increment (receipt_inc) is exact; the EIP-7778 block-gas gate is unaffected
  -- (it uses block_inc, which is refund-independent).
  ".Lbv_contract_dispatch:\n" ++
  -- evm-asm-ok3nl (EIP-8025 witness validation): the currently-executing frame's
  -- code must be present in witness.codes. The executable spec loads it via
  -- WitnessState.get_code (witness_state.py), whose `self._code_db[code_hash]`
  -- raises -> InvalidBlock when the preimage is absent. We reach here only when
  -- the recipient's code_hash is non-empty (the contract path), so require that
  -- preimage up-front; otherwise the staged dispatch silently bails to the
  -- conservative fall-through and the missing current-frame code is never caught
  -- (false-accept: guest=01 exp=00). bal_code_preimages_valid's BAL-row-shape
  -- heuristic skips the recipient, so this targeted gate is the binding check.
  "  la t0, svf_codes_ptr; ld a0, 0(t0)\n" ++
  "  la t0, svf_codes_len; ld a1, 0(t0)\n" ++
  "  la a2, bv_tx_recipient_code_hash\n" ++
  "  la a3, bv_cf_code_off; la a4, bv_cf_code_len\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lbv_code_preimage_fail            # current-frame code preimage absent -> reject\n" ++
  -- bmvmx.5 (single-tx CONTRACT-recipient nonce/balance lower bound): a non-self-contained
  -- contract recipient bails inside dispatch_tx_runtime_code (structured nonzero reason codes)
  -- -> skips the @1020 sender checks, so a single value-moving tx to such a recipient with a bad
  -- nonce/balance was accepted (spec check_transaction rejects: Nonce/InsufficientBalance). Check
  -- HERE, before dispatch, on the contract path only (EOA/simple-transfer never reaches here ->
  -- no redundant lookup; the self-contained path redundantly re-checks @1020, harmless). Same
  -- proven pattern as the multi-tx checks (#8791/#8792) with i=0: sender = public_keys[0] (=
  -- bv_public_keys_ptr, verified bound to tx[0]'s signer @339), sttc_nonce = tx.nonce (single-tx
  -- context build), tefgp_max_fee (tx_effective_gas_pricing @566), gas/value from bv_simple_transfer_tx.
  -- Sound lower bounds (reject if tx.nonce<pre or pre_balance<upfront) -> no false-reject.
  "  la a0, bv_public_keys_ptr; ld a0, 0(a0); addi a0, a0, 1\n" ++   -- public_keys[0]+1 (skip SEC1 0x04)
  "  la a1, bv_stx_sender_addr; jal ra, address_from_pubkey\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); la a2, bv_stx_sender_addr; li a3, 20; ld a4, 80(s0); ld a5, 88(s0); la a6, bv_stx_sender_acct\n" ++
  "  jal ra, account_at_header_state_root\n" ++
  "  bnez a0, .Lbv_stx_checks_done\n" ++                          -- sender lookup failed/absent -> skip
  "  la t0, bv_stx_sender_acct; ld t0, 0(t0)\n" ++                -- sender pre-state nonce
  "  la t1, sttc_nonce; ld t1, 0(t1)\n" ++                        -- tx.nonce
  -- EXACT (bne, not < pre): a single tx's nonce must EQUAL pre -- spec rejects too-high too
  -- (tx_nonce nonce_diff=+1; mirrors @1082; sound: a single tx always has nonce==pre). Multi-tx
  -- keeps < pre (a sequenced same-sender tx legitimately has nonce > pre).
  "  bne t1, t0, .Lbv_sender_nonce_fail\n" ++                     -- tx.nonce != pre_nonce -> reject (NonceMismatchError)
  "  la a0, tefgp_max_fee\n" ++
  "  la t0, bv_simple_transfer_tx; ld a1, 40(t0)\n" ++            -- gas_limit (u64)
  "  la a2, bv_upfront_cost\n  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  "  la a0, bv_upfront_cost\n  la t0, bv_simple_transfer_tx; addi a1, t0, 96\n  la a2, bv_upfront_cost\n  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  "  la t0, bv_simple_transfer_tx; ld t1, 160(t0); li t2, 3; bne t1, t2, .Lbv_stx_upfront_blob_done\n" ++
  "  ld a0, 176(t0); ld a1, 184(t0); la a2, tcbg_struct\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  "  la t0, tcbg_struct; lwu t1, 168(t0); lwu t2, 172(t0)\n" ++
  "  la t3, bv_simple_transfer_tx; ld t3, 176(t3); add a0, t3, t1; mv a1, t2; la a2, bv_upfront_blob_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  "  la t0, bv_upfront_blob_count; ld a1, 0(t0); beqz a1, .Lbv_sender_upfront_fail\n" ++
  "  li t2, 6; bgtu a1, t2, .Lbv_sender_upfront_fail\n" ++
  "  slli a1, a1, 17\n" ++
  "  la a0, tcbg_blob_fee_be; la a2, bv_upfront_blob_cost\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  "  la a0, bv_upfront_cost; la a1, bv_upfront_blob_cost; la a2, bv_upfront_cost\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  ".Lbv_stx_upfront_blob_done:\n" ++
  "  la a0, bv_stx_sender_acct; addi a0, a0, 8\n  la a1, bv_upfront_cost\n  la a2, bv_upfront_islt\n  jal ra, u256_lt_be\n" ++
  "  la t0, bv_upfront_islt; ld t0, 0(t0)\n  bnez t0, .Lbv_sender_upfront_fail\n" ++
  ".Lbv_stx_checks_done:\n" ++
  "  jal ra, bv_emit_single_tx_tl7708\n" ++
  "  la a0, bv_simple_transfer_tx\n" ++
  "  ld a1, 80(s0); ld a2, 88(s0)\n" ++
  "  jal ra, dispatch_tx_runtime_code\n" ++
  "  la t0, bv_dispatch_runtime_status; sd a0, 0(t0)\n  bnez a0, .Lbv_contract_dispatch_unsupported\n" ++
  bvReceiptsShapeSet 3 true ++  -- fhsxz.2.4.2.57.11.6.5.2.1 P1: persist tx0's executed state gas into bvgr_tx_exec_state_gas[0].
  -- Clobbers only a0/t0-t2, preserves the dispatch results a1-a4 stored below. Behavior-neutral.
  "  li a0, 0; jal ra, dispatcher_capture_exec_state_gas\n" ++
  "  la t4, bv_runtime_gas_left; sd a1, 0(t4)\n" ++
  "  la t4, bv_runtime_calldata_floor; sd a2, 0(t4)\n" ++
  -- nxio8: a3 = the settle-folded refund counter (0 when the tx erred), not a
  -- raw evm_refund_acc read.
  "  la t4, bv_runtime_refund_counter; sd a3, 0(t4)\n" ++
  "  la t4, bv_tx_status_arr; sd a4, 0(t4)\n" ++   -- .63.1.6.2.1: receipt status, tx 0
  "  la t4, bv_last_log_start; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 0(t4)\n" ++
  "  la t4, bv_last_log_count; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 8(t4)\n" ++
  "  la t4, bvgr_runtime_gas_left_ptr; la t5, bv_runtime_gas_left; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_refund_counter_ptr; la t5, bv_runtime_refund_counter; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_calldata_floor_ptr; la t5, bv_runtime_calldata_floor; sd t5, 0(t4)\n" ++
  "  li t5, 1; la t4, bvgr_runtime_count; sd t5, 0(t4)\n" ++
  -- bmvmx.1.6.2: execution-vs-BAL recipient storage consistency. dispatch_tx_runtime_code
  -- just replayed the (self-contained) recipient runtime, so the persistent storage log
  -- @0xa0630000 is fully populated and every entry's addrHash is env.ADDRESS (the recipient,
  -- per #8561). Re-find the recipient's BAL AccountChanges (dispatch's bvcd_acct_ptr is stale
  -- on its zero-storage path) and verify every storage change the BAL claims was actually
  -- produced by execution with the matching final value; a mismatch means the prover-supplied
  -- BAL is not what execution produced -> reject (succ=0). A recipient absent from the BAL
  -- (a0!=0) has no claimed changes, so skip — stay conservative, do not newly false-reject.
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  la a2, bv_simple_transfer_tx; addi a2, a2, 72\n" ++
  "  la a3, bvcd_acct_ptr; la a4, bvcd_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .Lbv_after_tx_gas_precharge\n" ++
  "  la a0, evm_env                              # recipient addrHash (env.ADDRESS@0, exec-log key)\n" ++
  "  la t0, bvcd_acct_ptr; ld a1, 0(t0); la t0, bvcd_acct_len; ld a2, 0(t0)\n" ++
  "  li a3, 0xa0630000                           # persistent storage log base\n" ++
  "  la t0, evm_env; ld a4, 448(t0)              # persistentLogLength (entry count)\n" ++
  "  jal ra, bal_storage_matches_exec_log\n" ++
  "  bnez a0, .Lbv_bal_storage_mismatch_fail\n" ++
  -- bmvmx.1.6.5: the converse direction (execution ⊆ BAL). Every net storage change execution
  -- made for the recipient must also be CLAIMED by the BAL — catches a prover that OMITS a write
  -- to hide state. Together with the forward check above this pins the recipient's BAL
  -- storage_changes to EXACTLY what execution produced. bvcd_acct_ptr/len still hold the
  -- recipient AccountChanges; env.ADDRESS@0 keys the exec log; env[448] is its entry count.
  "  la a0, evm_env\n" ++
  "  la t0, bvcd_acct_ptr; ld a1, 0(t0); la t0, bvcd_acct_len; ld a2, 0(t0)\n" ++
  "  li a3, 0xa0630000\n" ++
  "  la t0, evm_env; ld a4, 448(t0)\n" ++
  "  jal ra, bal_storage_covers_exec_log\n" ++
  "  bnez a0, .Lbv_bal_storage_omit_fail\n" ++
  -- bmvmx.1.6.3 (nonce/code slice): a self-contained CALL recipient is a pre-existing contract
  -- that executes no CREATE/CREATE2 (rejected by bytecode_is_self_contained), so the call leaves
  -- its code and nonce unchanged. Its BAL nonce_changes (AccountChanges item 4) and code_changes
  -- (item 5) must therefore be empty RLP lists; a non-empty list claims a change execution did
  -- not make -> reject (succ=0). bvcd_acct_ptr/len still hold the recipient AccountChanges found
  -- above. (The balance_changes value compare needs execution-derived gas — bmvmx.1.4.3.)
  -- .61.8c-2: once CREATE/CREATE2 is activated in the self-contained gate (.8c-3), a CREATE-executing
  -- recipient legitimately changes its OWN nonce (the EVM increments the creator's nonce on each
  -- CREATE) and the created account carries code_changes, so the "code+nonce unchanged" assumption
  -- above is FALSE for it -- the strict empty-list checks below would FALSE-REJECT a VALID CREATE
  -- block at .Lbv_bal_recipient_field_fail. Skip the recipient nonce_changes/code_changes checks when
  -- the recipient bytecode contains CREATE (0xf0) or CREATE2 (0xf5); the created account's nonce/code
  -- are validated by the all-accounts comparators (bal_all_accounts_code_consistent + i3djw), not the
  -- recipient-field check. Pushdata-aware scan over bvcd_code, mirroring the .Lbv_sbc_scan value-move
  -- guard. Conservative (skipping never false-rejects). Inert until .8c-3 (CREATE recipients are
  -- self-contained-rejected pre-.8c, so this region is unreachable for them today).
  "  la t0, bvcd_code_ptr; ld t0, 0(t0); la t1, bvcd_code_len; ld t1, 0(t1); add t1, t0, t1\n" ++
  ".Lbv_rnc_scan:\n" ++
  "  bgeu t0, t1, .Lbv_rnc_check\n" ++
  "  lbu t2, 0(t0)\n" ++
  "  li t3, 0x60; bltu t2, t3, .Lbv_rnc_chk\n" ++
  "  li t3, 0x7f; bgtu t2, t3, .Lbv_rnc_chk\n" ++
  "  addi t3, t2, -0x5f; addi t0, t0, 1; add t0, t0, t3; j .Lbv_rnc_scan\n" ++
  ".Lbv_rnc_chk:\n" ++
  "  li t3, 0xf0; beq t2, t3, .Lbv_recipient_nc_done\n" ++   -- CREATE -> creator nonce++ / created code
  "  li t3, 0xf5; beq t2, t3, .Lbv_recipient_nc_done\n" ++   -- CREATE2
  "  addi t0, t0, 1; j .Lbv_rnc_scan\n" ++
  ".Lbv_rnc_check:\n" ++
  "  la t0, bvcd_acct_ptr; ld a0, 0(t0); la t0, bvcd_acct_len; ld a1, 0(t0)\n" ++
  "  li a2, 4; la a3, bv_rcf_off; la a4, bv_rcf_len   # nonce_changes\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbv_recipient_code_check               # malformed/absent -> skip (conservative)\n" ++
  -- rlp_list_nth_item returns a *list* item's full encoded size (incl. prefix), so an empty
  -- list (0xc0) is len==1; only len>1 means the list carries entries (a claimed change).
  "  la t0, bv_rcf_len; ld t0, 0(t0); li t1, 1; bgtu t0, t1, .Lbv_bal_recipient_field_fail\n" ++
  ".Lbv_recipient_code_check:\n" ++
  "  la t0, bvcd_acct_ptr; ld a0, 0(t0); la t0, bvcd_acct_len; ld a1, 0(t0)\n" ++
  "  li a2, 5; la a3, bv_rcf_off; la a4, bv_rcf_len   # code_changes\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbv_after_tx_gas_precharge             # malformed/absent -> skip (conservative)\n" ++
  "  la t0, bv_rcf_len; ld t0, 0(t0); li t1, 1; bgtu t0, t1, .Lbv_bal_recipient_field_fail\n" ++
  -- bmvmx.1.6.4.3: all-accounts storage exec-vs-BAL. Every NON-recipient BAL account's
  -- storage_changes must match the exec log — forward (every claimed change reproduced) AND
  -- reverse (every net change claimed) — keyed on each account's LE callee exec-log key.
  -- Callee entries were seeded by dispatch_tx_runtime_code (1.6.4.2.b) and produced during the
  -- descent; the recipient is skipped (checked above, BE-keyed). Mismatch/omission -> reject.
  -- This surfaces guest nested-execution divergences (per @pirapira "see more failures").
  ".Lbv_recipient_nc_done:\n" ++   -- .61.8c-2: CREATE/CREATE2 recipients skip the recipient nonce/code checks to here
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  li a2, 0xa0630000\n" ++
  "  la t0, evm_env; ld a3, 448(t0)\n" ++
  "  la a4, bv_simple_transfer_tx; addi a4, a4, 72\n" ++
  "  jal ra, bal_all_accounts_storage_consistent\n" ++
  "  bnez a0, .Lbv_bal_allaccounts_fail\n" ++
  -- bmvmx.1.6.6: per-slot tuple-SEQUENCE consistency. The checks above pin each slot's FINAL
  -- value; this pins the per-tx (block_access_index, new_value) tuple SEQUENCE that the spec
  -- hashes into header.block_access_list_hash, for every non-recipient account. Index semantics
  -- (c2#15): block_access_index = i+1 for the i-th user tx, so a single-user-tx block's writes
  -- stamp 1 == the exec default current_block_access_index (#8585) -> the sequence is a degenerate
  -- one-tuple match (NO single-tx false-reject). It bites once the multi-tx loop sets
  -- current_block_access_index = i+1 per tx. Recipient skipped (a5; pinned above). Mismatch -> reject.
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  li a2, 0xa0630000\n" ++
  "  la t0, evm_env; ld a3, 448(t0)\n" ++
  "  la a4, exec_log_txindex\n" ++
  "  la a5, bv_simple_transfer_tx; addi a5, a5, 72\n" ++
  "  jal ra, bal_all_accounts_tuple_sequences_consistent\n" ++
  "  bnez a0, .Lbv_bal_tuple_fail\n" ++
  -- i3djw (all-accounts CODE reverse): every account execution changed code for (CREATE/CREATE2
  -- deploy, has_code_change=1 in exec_code_effect_log) must be PRESENT in the BAL -- catching a
  -- producer that hides a created account by omitting it. Presence-only (a present account's declared
  -- code is validated by the forward per-account direction). exec_code_effect_log is populated by the
  -- CREATE deposit (.8b, #8623); it is EMPTY pre-.8c (CREATE is self-contained-rejected), so this is
  -- inert until CREATE activation (.8c-3) and conservative (parse fail / omitted account -> reject).
  -- NOTE for .8c-3: add a per-tx reset of exec_code_effect_count (not reset today; harmless while the
  -- log is empty, but REQUIRED once CREATE writes it so stale records don't carry across txs).
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  la a2, exec_code_effect_log; la t0, exec_code_effect_count; ld a3, 0(t0)\n" ++
  "  jal ra, bal_all_accounts_code_covers\n" ++
  "  bnez a0, .Lbv_bal_code_covers_fail\n" ++
  -- i3djw.3: all-accounts NON-STORAGE exec-vs-BAL (FORWARD). Every non-{sender,recipient,
  -- coinbase} BAL account that declares a balance/nonce change must be reproduced by an exec
  -- non-storage effect record (the i3djw.1 CALL-value producer + i3djw.2 CREATE producer
  -- populate exec_nonstorage_effect_log). A declared change with no matching exec effect, or
  -- a value mismatch, -> reject. *** REQUIRES EEST SWEEP *** : this CHANGES verdict accept/
  -- reject for value-bearing CALL blocks (the i3djw.1 producer runs live since CALL is
  -- activated #8559) — @pirapira must run EEST at scale to confirm the recorded post_balance
  -- (BE, see i3djw.1/i3djw.2) matches the BAL before finalizing. Skip-list {recipient, sender,
  -- coinbase} are gas/value-coupled (pinned on the gas path); set unconditionally above
  -- (bv_simple_transfer_tx+72, bmvmx_sender_addr, bmvmx_coinbase_addr). 32-byte-strided,
  -- address in the first 20 bytes.
  "  la t0, i3djw_skip_list\n  la t1, bv_simple_transfer_tx; addi t1, t1, 72\n  li t2, 20\n" ++
  ".Lbv_i3sk0:\n  beqz t2, .Lbv_i3sk0d\n  lbu t3, 0(t1)\n  sb t3, 0(t0)\n  addi t1, t1, 1\n  addi t0, t0, 1\n  addi t2, t2, -1\n  j .Lbv_i3sk0\n.Lbv_i3sk0d:\n" ++
  "  la t0, i3djw_skip_list; addi t0, t0, 32\n  la t1, bmvmx_sender_addr\n  li t2, 20\n" ++
  ".Lbv_i3sk1:\n  beqz t2, .Lbv_i3sk1d\n  lbu t3, 0(t1)\n  sb t3, 0(t0)\n  addi t1, t1, 1\n  addi t0, t0, 1\n  addi t2, t2, -1\n  j .Lbv_i3sk1\n.Lbv_i3sk1d:\n" ++
  "  la t0, i3djw_skip_list; addi t0, t0, 64\n  la t1, bmvmx_coinbase_addr\n  li t2, 20\n" ++
  ".Lbv_i3sk2:\n  beqz t2, .Lbv_i3sk2d\n  lbu t3, 0(t1)\n  sb t3, 0(t0)\n  addi t1, t1, 1\n  addi t0, t0, 1\n  addi t2, t2, -1\n  j .Lbv_i3sk2\n.Lbv_i3sk2d:\n" ++
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  la a2, exec_nonstorage_effect_log\n" ++
  "  la t0, exec_nonstorage_effect_count; ld a3, 0(t0)\n" ++
  "  la a4, i3djw_skip_list; li a5, 3\n" ++
  "  jal ra, bal_all_accounts_nonstorage_consistent\n" ++
  "  bnez a0, .Lbv_bal_nonstorage_fail\n" ++
  -- i3djw.3 (REVERSE covers): every exec NON-STORAGE net-change effect must be PRESENT in
  -- the BAL — catches a hidden account that execution net-changed (balance/nonce) but the
  -- BAL omits. Completes the non-storage compare (forward = BAL declared -> exec reproduces;
  -- reverse = exec changed -> BAL declares). Same effect log + skip-list as the forward.
  -- Mismatch -> bv_fail_code=45. *** REQUIRES EEST SWEEP *** (changes accept/reject for
  -- value-CALL/CREATE blocks, alongside the forward).
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  la a2, exec_nonstorage_effect_log\n" ++
  "  la t0, exec_nonstorage_effect_count; ld a3, 0(t0)\n" ++
  "  la a4, i3djw_skip_list; li a5, 3\n" ++
  "  jal ra, bal_all_accounts_nonstorage_covers\n" ++
  "  bnez a0, .Lbv_bal_nonstorage_covers_fail\n" ++
  -- i3djw.4: all-accounts CODE exec-vs-BAL (FORWARD). Every BAL account that declares a code
  -- change (only CREATE/CREATE2 deploy or SELFDESTRUCT clear can change code) must be reproduced
  -- by an exec code-effect record (exec_code_effect_log, populated by the CREATE deposit #8623)
  -- with byte-identical deployed code; a declared change with no matching exec effect, or a byte
  -- mismatch, -> reject. EIP-7702 delegations (0xef0100||addr, 23B) are installed from the
  -- authorization list (no CREATE deposit -> no exec code-effect), so the comparator SKIPS a
  -- code-declaring account whose declared new code is exactly a 23-byte 0xef0100-prefixed
  -- indicator (avoiding a 7702 false-reject; see BalAllAccountsCode .Lbaac_notfound). No
  -- skip-list: code never changes for {sender,recipient,coinbase} via the gas path.
  -- *** REQUIRES EEST SWEEP *** : CHANGES verdict accept/reject for CREATE/CREATE2 and 7702
  -- blocks — @pirapira must run EEST at scale to confirm before finalizing. Inert (no code_change
  -- declared) for plain transfer / non-deploying blocks; exec_code_effect_log is empty pre-.8c.
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  la a2, exec_code_effect_log; la t0, exec_code_effect_count; ld a3, 0(t0)\n" ++
  "  jal ra, bal_all_accounts_code_consistent\n" ++
  "  bnez a0, .Lbv_bal_code_consistent_fail\n" ++
  -- bmvmx.1.6.7: recipient storage_reads exec consistency. storage_reads (AccountChanges
  -- item 2) is consensus-bound but NOT in the state root, so verify every BAL read slot
  -- was actually accessed by the recipient (appears in the exec log). bvcd_acct_ptr/len
  -- holds the recipient AccountChanges. A read claimed but never accessed -> reject.
  "  la t0, bvcd_acct_ptr; ld t1, 0(t0); beqz t1, .Lbv_after_tx_gas_precharge\n" ++  -- no recipient AccountChanges (not in BAL) -> skip
  "  la a0, evm_env\n" ++
  "  la t0, bvcd_acct_ptr; ld a1, 0(t0); la t0, bvcd_acct_len; ld a2, 0(t0)\n" ++
  "  li a3, 0xa0630000\n" ++
  "  la t0, evm_env; ld a4, 448(t0)\n" ++
  "  jal ra, bal_storage_reads_in_exec_log\n" ++
  "  bnez a0, .Lbv_bal_reads_fail\n" ++
  -- bmvmx.1.6.3 (balance slice): execution-derived sender BAL post-balance compare.
  -- dispatch_tx_runtime_code replayed the (self-contained) recipient with EXACT gas, so the
  -- sender settlement is sender_post = sender_pre - receipt_inc*eff_gas_price - value, computed
  -- by tx_gas_bal_post_verify_runtime (sender_debit_from_gas #8583 + the runtime gas result).
  -- This is exact ONLY when execution cannot move value to the sender, so the REJECT is gated
  -- conservatively (any failed gate -> skip, never newly false-reject). The .Lbv_sbc_scan guard
  -- below is the SOLE entry into the sender + post-nonce + recipient-balance checks, so all three
  -- inherit this value-move protection (see the recipient slice's note at .Lbv_rbc_do):
  --   * recipient bytecode has no CALL(0xf1) / CALLCODE(0xf2) / DELEGATECALL(0xf4) /
  --     SELFDESTRUCT(0xff) opcode -- the ways execution can move value to/from the sender
  --     (DELEGATECALL runs delegated code in the recipient's context, which may SELFDESTRUCT to
  --     the sender; STATICCALL is safe -- static mode forbids value/SELFDESTRUCT). Pushdata-aware
  --     scan over bvcd_code. SSTORE is NO LONGER bailed: the per-tx EIP-3529 refund is now real
  --     (evm_refund_acc surfaced into bv_runtime_refund_counter, #8590 merged), so receipt_inc is
  --     exact for SSTORE-writing recipients too -- the bulk of EEST contract recipients, a large
  --     coverage gain.
  --   * the block has no withdrawals (else the sender may be credited),
  --   * the sender is not the block coinbase (else it also receives the priority fee).
  -- Only a clean value mismatch (kernel status 40) rejects; every other status (lookup miss,
  -- post absent, egp/value parse fail, underflow) is treated as "cannot compare" -> skip.
  "  la t0, svf_wds_count; ld t0, 0(t0); bnez t0, .Lbv_after_tx_gas_precharge\n" ++
  "  la t0, bvcd_code_ptr; ld t0, 0(t0); la t1, bvcd_code_len; ld t1, 0(t1); add t1, t0, t1\n" ++
  ".Lbv_sbc_scan:\n" ++
  "  bgeu t0, t1, .Lbv_sbc_safe\n" ++
  "  lbu t2, 0(t0)\n" ++
  "  li t3, 0x60; bltu t2, t3, .Lbv_sbc_chk\n" ++
  "  li t3, 0x7f; bgtu t2, t3, .Lbv_sbc_chk\n" ++
  "  addi t3, t2, -0x5f; addi t0, t0, 1; add t0, t0, t3; j .Lbv_sbc_scan\n" ++
  ".Lbv_sbc_chk:\n" ++
  "  li t3, 0xf1; beq t2, t3, .Lbv_after_tx_gas_precharge\n" ++   -- CALL -> direct value move
  "  li t3, 0xf2; beq t2, t3, .Lbv_after_tx_gas_precharge\n" ++   -- CALLCODE -> value move
  "  li t3, 0xf4; beq t2, t3, .Lbv_after_tx_gas_precharge\n" ++   -- DELEGATECALL -> delegated code runs in recipient ctx, may SELFDESTRUCT to sender
  "  li t3, 0xff; beq t2, t3, .Lbv_after_tx_gas_precharge\n" ++   -- SELFDESTRUCT -> value move
  "  addi t0, t0, 1; j .Lbv_sbc_scan\n" ++
  ".Lbv_sbc_safe:\n" ++
  "  la t0, tgbpvr_in\n" ++
  "  la t1, bv_simple_transfer_tx; ld t2, 40(t1); sd t2, 0(t0)\n" ++       -- gas_limit
  "  la t1, bv_runtime_gas_left; ld t2, 0(t1); sd t2, 8(t0)\n" ++           -- gas_left
  "  la t1, bv_runtime_refund_counter; ld t2, 0(t1); sd t2, 16(t0)\n" ++    -- real EIP-3529 refund (#8590)
  "  la t1, bv_runtime_calldata_floor; ld t2, 0(t1); sd t2, 24(t0)\n" ++    -- calldata floor
  "  la t1, bv_simple_transfer_tx\n" ++
  "  ld a0, 8(t1); ld a1, 16(t1); ld a2, 32(t1); ld a3, 24(t1)\n" ++        -- tx ptr/len, base_fee, pubkey
  "  la t0, bv_bal_start; ld a4, 0(t0); la t0, bv_bal_len; ld a5, 0(t0)\n" ++
  "  la a6, basr_records; la a7, bv_sender_bal_check\n" ++
  "  jal ra, tx_gas_bal_post_verify_runtime\n" ++
  "  la t0, bv_sender_bal_check; ld t0, 0(t0)\n" ++
  "  li t1, 40; beq t0, t1, .Lbv_sbc_bal_mismatch\n" ++          -- clean balance mismatch -> coinbase gate
  -- bmvmx.4: status 50 = check_transaction fee invalid (max_fee < base_fee, or
  -- priority_fee > max_fee); the runtime verify detected it and the spec REJECTS
  -- (InsufficientMaxFeePerGasError / PriorityFeeGreaterThanMaxFeeError), so reject
  -- here rather than fall through to the cannot-compare skip below.
  "  li t1, 50; beq t0, t1, .Lbv_fee_invalid_fail\n" ++
  "  bnez t0, .Lbv_after_tx_gas_precharge\n" ++                  -- lookup miss / cannot-compare -> skip
  -- bmvmx.1.6.3 (nonce slice): the balance matched (status 0); now verify the sender's BAL post
  -- nonce == pre_nonce + 1 against execution (a single tx from the sender increments its nonce
  -- exactly once). tgbpvr_lookup still holds the kernel's sender lookup. Non-redundant with the
  -- state-root check (which only validates the prover BAL against the prover header.state_root).
  -- Nonce is value-independent, so no coinbase gate is needed; an absent/oversized post nonce
  -- returns "skip" (2) and never rejects. A BAL post nonce != pre+1 is a prover lie -> reject.
  -- bmvmx.2 (check_transaction nonce pre-validation): BEFORE the post check, verify the spec's
  -- pre-condition tx.nonce == sender_pre_nonce (execution-specs amsterdam/fork.py check_transaction
  -- raises NonceMismatchError otherwise). The post check (post == pre+1) only validates the BAL's
  -- claimed EFFECT, not that the tx was nonce-ELIGIBLE to execute: an out-of-order tx (tx.nonce !=
  -- pre, e.g. tx.nonce=7 with pre=3) carrying a BAL post=pre+1 would otherwise false-accept a block
  -- the spec rejects. pre_nonce = tgbpvr_lookup[80] (the very value the post check reads as "pre");
  -- tx.nonce = sttc_nonce (extracted by the simple_transfer context build, tx_extract_nonce_and_gas,
  -- which ran before the gas_limit read above). Value-independent like the post check, so reuse the
  -- same .Lbv_sender_nonce_fail. Transparent for valid in-order txs (tx.nonce == pre).
  "  la t0, tgbpvr_lookup; ld t0, 80(t0)        # sender pre_nonce (witness-proven)\n" ++
  "  la t1, sttc_nonce; ld t1, 0(t1)            # tx.nonce (consensus-bound)\n" ++
  "  bne t0, t1, .Lbv_sender_nonce_fail         # tx.nonce != pre_nonce -> reject (NonceMismatchError)\n" ++
  "  la a0, tgbpvr_lookup; jal ra, sender_post_nonce_consistent\n" ++
  "  li t1, 1; beq a0, t1, .Lbv_sender_nonce_fail\n" ++
  -- bmvmx.2 (check_transaction balance pre-validation): reject if
  -- sender_pre_balance < gas_limit*max_fee_per_gas + blob_gas*max_fee_per_blob_gas + tx.value (execution-specs
  -- amsterdam/fork.py check_transaction raises InsufficientBalanceError). The
  -- runtime verify only proves BAL post == pre - actual_debit and SKIPS (not
  -- rejects) on insufficiency; the spec requires the sender cover the UPFRONT max
  -- gas_limit*max_fee plus any blob precharge (>= the actual debit), so a tx funded between actual-debit
  -- and upfront would otherwise false-accept. Operands all live here: max_fee =
  -- tefgp_max_fee (written by tx_effective_gas_pricing inside the line-956 verify),
  -- gas_limit = bv_simple_transfer_tx[40], value = bv_simple_transfer_tx[96] (BE),
  -- pre_balance = tgbpvr_lookup[48] (BE). u256_mul_u64_be returns 1 on overflow
  -- (a*b >= 2^256); u256_add_be returns carry-out; u256_lt_be writes 1 iff a<b.
  "  la a0, tefgp_max_fee\n" ++
  "  la t0, bv_simple_transfer_tx; ld a1, 40(t0)   # gas_limit (u64)\n" ++
  "  la a2, bv_upfront_cost\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail              # gas_limit*max_fee >= 2^256 -> reject\n" ++
  "  la a0, bv_upfront_cost\n" ++
  "  la t0, bv_simple_transfer_tx; addi a1, t0, 96  # tx.value (32B BE)\n" ++
  "  la a2, bv_upfront_cost\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail              # upfront cost + value >= 2^256 -> reject\n" ++
  "  la t0, bv_simple_transfer_tx; ld t1, 160(t0); li t2, 3; bne t1, t2, .Lbv_runtime_upfront_blob_done\n" ++
  "  ld a0, 176(t0); ld a1, 184(t0); la a2, tcbg_struct\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  "  la t0, tcbg_struct; lwu t1, 168(t0); lwu t2, 172(t0)\n" ++
  "  la t3, bv_simple_transfer_tx; ld t3, 176(t3); add a0, t3, t1; mv a1, t2; la a2, bv_upfront_blob_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  "  la t0, bv_upfront_blob_count; ld a1, 0(t0); beqz a1, .Lbv_sender_upfront_fail\n" ++
  "  li t2, 6; bgtu a1, t2, .Lbv_sender_upfront_fail\n" ++
  "  slli a1, a1, 17\n" ++
  "  la a0, tcbg_blob_fee_be; la a2, bv_upfront_blob_cost\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  "  la a0, bv_upfront_cost; la a1, bv_upfront_blob_cost; la a2, bv_upfront_cost\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  ".Lbv_runtime_upfront_blob_done:\n" ++
  "  la a0, tgbpvr_lookup; addi a0, a0, 48          # sender pre_balance (32B BE)\n" ++
  "  la a1, bv_upfront_cost\n" ++
  "  la a2, bv_upfront_islt\n" ++
  "  jal ra, u256_lt_be\n" ++
  "  la t0, bv_upfront_islt; ld t0, 0(t0)\n" ++
  "  bnez t0, .Lbv_sender_upfront_fail              # pre_balance < upfront -> reject\n" ++
  -- bmvmx.1.6.3 (recipient balance slice): the contract recipient RECEIVES tx.value and, on this
  -- value-movement-free path (no CALL/CALLCODE/DELEGATECALL/SELFDESTRUCT; CREATE is self-contained-
  -- rejected), its balance changes only by +value, so recipient_post == recipient_pre + value.
  -- That "value-movement-free" precondition is ENFORCED, not assumed (fhsxz.2.4.2.61.6.8): the
  -- .Lbv_sbc_scan value-move guard above (~line 1015) is the SOLE entry into this whole
  -- balance/nonce/recipient block and skips it entirely (-> .Lbv_after_tx_gas_precharge) when the
  -- recipient bytecode contains any of those opcodes -- so a contract recipient that sends value
  -- out via a value-bearing nested CALL never reaches here and is NOT false-rejected (verdict 41).
  -- The descent staged the child's CALLVALUE (call_frame_set_call_env env+96), and SELFBALANCE/
  -- BALANCE reads are self-contained-rejected (0x47/0x31), so no executed callee reads a stale own
  -- balance. Positive validation of the multi-account value deltas (caller debited / callee credited
  -- by the nested CALL) against the BAL is bmvmx.1.6.4's all-accounts exec-vs-BAL compare.
  -- Reuse the proven EOA recipient verifier. Bail (skip) when the recipient is the coinbase (its
  -- post also folds the priority fee) or the sender (self-transfer nets gas -- the sender slice owns
  -- it); withdrawals are already excluded above. A clean post mismatch (status 32) is a prover lie.
  "  la t5, bv_simple_transfer_tx; addi t5, t5, 72; ld t6, 0(s0); addi t6, t6, 32; li a0, 20\n" ++
  ".Lbv_rbc_cb_cmp:\n" ++
  "  beqz a0, .Lbv_after_tx_gas_precharge\n" ++                  -- recipient == coinbase -> skip
  "  lbu t3, 0(t5); lbu t4, 0(t6); bne t3, t4, .Lbv_rbc_not_cb\n" ++
  "  addi t5, t5, 1; addi t6, t6, 1; addi a0, a0, -1; j .Lbv_rbc_cb_cmp\n" ++
  ".Lbv_rbc_not_cb:\n" ++
  "  la t5, bv_simple_transfer_tx; addi t5, t5, 72; la t6, bv_sender_bal_check; addi t6, t6, 8; li a0, 20\n" ++
  ".Lbv_rbc_self_cmp:\n" ++
  "  beqz a0, .Lbv_after_tx_gas_precharge\n" ++                  -- recipient == sender (self-transfer) -> skip
  "  lbu t3, 0(t5); lbu t4, 0(t6); bne t3, t4, .Lbv_rbc_do\n" ++
  "  addi t5, t5, 1; addi t6, t6, 1; addi a0, a0, -1; j .Lbv_rbc_self_cmp\n" ++
  ".Lbv_rbc_do:\n" ++
  "  la t0, bv_simple_transfer_tx; addi a0, t0, 72; addi a1, t0, 96\n" ++   -- recipient addr (20B), value (32B BE)
  "  la t0, bv_bal_start; ld a2, 0(t0); la t0, bv_bal_len; ld a3, 0(t0)\n" ++
  "  la a4, basr_records; la a5, bv_simple_transfer_recipient\n" ++
  "  jal ra, simple_transfer_recipient_bal_verify\n" ++
  "  la t0, bv_simple_transfer_recipient; ld t0, 0(t0); li t1, 32; beq t0, t1, .Lbv_recipient_bal_fail\n" ++
  "  j .Lbv_after_tx_gas_precharge\n" ++
  ".Lbv_sbc_bal_mismatch:\n" ++
  -- Clean value mismatch. Skip when the sender IS the coinbase (its post also folds the fee).
  "  la t0, bv_sender_bal_check; addi t0, t0, 8; ld t1, 0(s0); addi t1, t1, 32; li t2, 20\n" ++
  ".Lbv_sbc_cb_cmp:\n" ++
  "  beqz t2, .Lbv_after_tx_gas_precharge\n" ++                  -- sender == coinbase -> skip
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_sender_bal_fail\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_sbc_cb_cmp\n" ++
  ".Lbv_creation_unsupported:\n" ++
  bvReceiptsShapeSet 60 false ++  "  j .Lbv_after_tx_gas_precharge\n" ++
  ".Lbv_contract_dispatch_unsupported:\n" ++
  "  la t0, eip7708_tl_typed_avail; sd zero, 0(t0)\n" ++
  bvRuntimeCompletenessSet 3 ++ bvReceiptsShapeSet 61 false ++  "  j .Lbv_after_tx_gas_precharge\n" ++
  ".Lbv_after_tx_gas_precharge:\n" ++
  -- fhsxz.2.4.2.57.11.6.5.2.1.3: prefill the transaction-count and
  -- intrinsic-state-gas substrate BEFORE eip8037_tx_gas_gate. The gate still
  -- runs unconditionally: a substrate parse/fill failure zeros the prefix and
  -- falls through, preserving the old conservative gate behavior while making
  -- the exact per-tx state dimension available to the follow-up gate patch.
  "  la t2, bvgr_arena_tx_count; sd zero, 0(t2)\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  la a1, bvgr_tx_gas_limits\n" ++
  "  li a2, 16\n" ++
  "  jal ra, block_verdict_tx_gas_limits\n" ++
  "  bnez a0, .Lbv_pregate_state_gas_ready\n" ++
  "  la t2, bvgr_arena_tx_count; sd a1, 0(t2)\n" ++
  "  la t2, bv_tx_list_ptr; ld a0, 0(t2)\n" ++
  "  la t2, bv_tx_list_len; ld a1, 0(t2)\n" ++
  "  la t2, bvgr_arena_tx_count; ld a2, 0(t2)\n" ++
  "  la a3, bvgr_tx_state_gas\n" ++
  "  jal ra, block_verdict_tx_state_gas_array\n" ++
  "  beqz a0, .Lbv_pregate_state_gas_ready\n" ++
  "  la t2, bvgr_tx_state_gas; la t3, bvgr_arena_tx_count; ld t3, 0(t3); li t4, 0\n" ++
  ".Lbv_pregate_state_gas_zero:\n" ++
  "  beq t4, t3, .Lbv_pregate_state_gas_ready\n" ++
  "  slli t5, t4, 3; add t5, t2, t5; sd zero, 0(t5); addi t4, t4, 1; j .Lbv_pregate_state_gas_zero\n" ++
  ".Lbv_pregate_state_gas_ready:\n" ++
  "  # EIP-8037 tx inclusion gas gate: reject parse-supported legacy tx blocks\n" ++
  "  # whose worst regular/state gas exceeds the remaining 2D block budget.\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)             # exec_payload\n" ++
  "  la t2, bv_bal_start; ld a1, 0(t2)          # bal_start\n" ++
  "  la t2, bv_bal_len; ld a2, 0(t2)            # bal_len\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2); addi a0, t1, 412; jal ra, bgv_u64le\n" ++
  "  mv a3, a0                                  # gas_limit\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  jal ra, eip8037_tx_gas_gate\n" ++
  "  bnez a0, .Lbv_eip8037_gas_fail\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  la t2, bvgr_runtime_gas_left_ptr; ld a1, 0(t2)\n" ++
  "  la t2, bvgr_runtime_refund_counter_ptr; ld a2, 0(t2)\n" ++
  "  la t2, bvgr_runtime_calldata_floor_ptr; ld a3, 0(t2)\n" ++
  "  la t2, bvgr_runtime_count; ld a4, 0(t2)\n" ++
  "  li a5, 16\n" ++
  "  jal ra, block_verdict_gas_result_arena_prepare\n" ++
  bvRuntimeCompletenessSetFromArenaStatus ++
  "  bnez a0, .Lbv_after_gas_result_gate\n" ++
  -- .57.11.6.5.2: fill bvgr_tx_state_gas (per-tx intrinsic.state) FIRST, so the EIP-7778
  -- remaining-block-gas check below can apply the spec's 2D REGULAR test
  -- min(TX_MAX_GAS_LIMIT, tx.gas - intrinsic.state) (amsterdam fork.py:591) instead of the
  -- 1D over-approx min(TX_MAX, tx.gas). block_verdict_tx_state_gas_array depends only on the
  -- tx list (not the gas-result arena), so running it here is order-safe; its bail is the
  -- same conservative skip. (Moved up from just below the EIP-7778 check.)
  "  la t2, bv_tx_list_ptr; ld a0, 0(t2)\n" ++
  "  la t2, bv_tx_list_len; ld a1, 0(t2)\n" ++
  "  la t2, bvgr_arena_tx_count; ld a2, 0(t2)\n" ++
  "  la a3, bvgr_tx_state_gas\n" ++
  "  jal ra, block_verdict_tx_state_gas_array\n" ++
  -- .57.11.6.5.2: block_verdict_tx_state_gas_array can bail (a0 != 0) even after a successful
  -- arena_prepare -- e.g. tx_intrinsic_state_gas unsupported for some tx (TxIntrinsicStateGas.lean).
  -- Do NOT skip the EIP-7778 reject check on that bail (that would be a regression: the check
  -- ran unconditionally before this reorder). Instead ZERO bvgr_tx_state_gas and fall through:
  -- the check below then uses intrinsic.state == 0 = the legacy min(TX_MAX, tx.gas) over-approx
  -- (= the pre-fix behaviour, sound), and the block_state floor sums 0 (no false-reject). The
  -- floor/ceiling still run, so this is strictly >= the old conservative skip.
  "  beqz a0, .Lbv_state_gas_filled\n" ++
  "  la t2, bvgr_tx_state_gas; la t3, bvgr_arena_tx_count; ld t3, 0(t3); li t4, 0\n" ++
  ".Lbv_state_gas_zero:\n" ++
  "  beq t4, t3, .Lbv_state_gas_filled\n" ++
  "  slli t5, t4, 3; add t5, t2, t5; sd zero, 0(t5); addi t4, t4, 1; j .Lbv_state_gas_zero\n" ++
  ".Lbv_state_gas_filled:\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2); addi a0, t1, 412; jal ra, bgv_u64le\n" ++
  "  la a1, bvgr_tx_gas_limits\n" ++
  "  la a2, bvgr_gas_left\n" ++
  "  la a3, bvgr_refund_counter\n" ++
  "  la a4, bvgr_calldata_floor\n" ++
  "  la t2, bvgr_arena_tx_count; ld a5, 0(t2)\n" ++
  "  la a6, bvgr_block_gas_increments\n" ++
  "  la a7, bvgr_tx_state_gas    # .57.11.6.5.2: per-tx intrinsic.state -> spec 2D regular test\n" ++
  "  jal ra, eip7778_remaining_block_gas_from_results\n" ++
  "  la t2, bv_eip7778_status; sd a0, 0(t2)\n" ++
  "  la t2, bv_eip7778_index; sd a1, 0(t2)\n" ++
  "  la t2, bv_eip7778_used; sd a2, 0(t2)\n" ++
  "  bnez a0, .Lbv_eip7778_block_gas_fail\n" ++
  -- g8zeq.1.4.2: EIP-8037 block_state-gas floor. block_state = sum of per-tx
  -- INTRINSIC state gas (exact + execution-independent); every valid block has
  -- header.gas_used = max(block_regular, block_state) >= block_state. So reject
  -- when block_state > header.gas_used (the header under-claims the state-gas
  -- floor it must cover). Sound by construction -- block_state is exact, so no
  -- valid block is false-rejected. The ceiling half (reject header.gas_used >
  -- max(block_regular, block_state)) lands just below, completing the EIP-8037
  -- equality; it uses block_regular = sum(bvgr_block_gas_increments), the same
  -- array the EIP-7778 gate above already trusts (arena prepared => execution-exact).
  "  la t5, bv_exec_p; ld t4, 0(t5); addi a0, t4, 420; jal ra, bgv_u64le   # header.gas_used\n" ++
  "  mv t6, a0\n" ++
  "  la t0, bvgr_tx_state_gas; la t1, bvgr_arena_tx_count; ld t1, 0(t1); li t2, 0; li t3, 0\n" ++
  ".Lbv_bstate_sum:\n" ++
  "  beq t3, t1, .Lbv_bstate_done\n" ++
  "  slli t4, t3, 3; add t5, t0, t4; ld t5, 0(t5); add t2, t2, t5; addi t3, t3, 1; j .Lbv_bstate_sum\n" ++
  ".Lbv_bstate_done:\n" ++
  "  bgtu t2, t6, .Lbv_block_state_gas_fail\n" ++
  -- xexgj: the g8zeq.1.4.2 "EIP-8037 equality" ceiling (header.gas_used > max(block_regular,
  -- block_state) -> reject) was UNSOUND. block_state (intrinsic, ~line 1040) is only a LOWER bound
  -- on the actual EIP-8037 STATE gas -- state-creation gas is execution-dependent, not intrinsic --
  -- so for a state-gas block max(block_regular, block_state) < header.gas_used and the gate
  -- false-rejected valid blocks. Verified on eip8037 state_gas_reservoir/block_regular_gas_limit:
  -- runtime_count==tx_count (so block_regular=147000 was exact), block_state=0, but the real state
  -- gas == header.gas_used == 0x07000000 -- the entire miss is block_state, which the guest cannot
  -- compute intrinsically. Replace with the SOUND block-gas-limit ceiling: every valid block has
  -- header.gas_used <= header.gas_limit (exec payload @+412); that is exactly what the
  -- "exceed_block_gas_limit" fixtures exercise. The exact EIP-8037 equality (gas_used ==
  -- max(regular,state)) needs the execution-exact state gas -- deferred; the receipts_root
  -- comparison (.63.1.6) also pins cumulative gas. (Block-state FLOOR above stays: intrinsic exact.)
  "  mv t1, t6                                            # stash gas_used (bgv_u64le clobbers t6)\n" ++
  "  la t5, bv_exec_p; ld t4, 0(t5); addi a0, t4, 412; jal ra, bgv_u64le   # header.gas_limit @+412\n" ++
  "  bgtu t1, a0, .Lbv_block_gas_used_over_fail            # header.gas_used > gas_limit -> reject\n" ++
  blockVerdictReceiptsTail

end EvmAsm.Codegen
