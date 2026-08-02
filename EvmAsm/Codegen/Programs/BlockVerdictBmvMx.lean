/-
  EvmAsm.Codegen.Programs.BlockVerdictBmvMx

  Early single-transaction EOA balance/fee precompute prefix for block_verdict.
-/

import EvmAsm.Codegen.Programs.BlockVerdictReceiptGate

namespace EvmAsm.Codegen

/-- Assembly prefix that precomputes supported single-tx EOA sender/coinbase checks. -/
def blockVerdictBmvMxPrecomputePrefix : String :=
  -- bmvmx.1.4.4: precompute the supported single-tx EOA settlement scalars BEFORE
  -- block_state_root so .4.1/.4.2 can build execution-derived sender/coinbase leaves.
  -- ADDITIVE (no consumer reads bmvmx_* yet) -> verdict byte-identical. exec_p = 0(s0)
  -- (= bv_exec_p). All bv_* writes here are idempotent with the post-348 tx preamble,
  -- and block_state_root (BlockVerdict.lean:67-302) reads none of these globals.
  "  la t0, eip7708_tl_typed_avail; sd zero, 0(t0)\n" ++
  bvReceiptsShapeClear ++               -- bmvmx.1.4.3.1: envelope predicate flags default 0
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
  -- .Lbmvmx_done (skip the whole inert compute).  GH #11211: the bmvmx_* comparison
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
  -- bmvmx.1.4.1 compare.  GH #11211 retired its write-only result flag; the compare below
  -- assert the BAL sender post balance == sender_pre - bmvmx_sender_debit. Sender address is
  -- derived from the selected public key (pubkeys = SSZ_BASE(s3) + offsets[3]@s3+12; 65-byte
  -- SEC1 key 0x04||x||y -> address_from_pubkey(key+1)). Reuses bmvmx_acct/bmvmx_cb_* scratch.
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
  ".Lbmvmx_sd_skip:\n" ++
  -- bmvmx.1.4.2: execution-derived coinbase fee credit = priority_fee_per_gas * gas_used
  -- (the tip credited to the block coinbase; EIP-1559 base fee is burned). Consumed by
  -- .4.3 as coinbase_post = coinbase_pre + credit (for the supported single-tx EOA class).
  "  la a0, bmvmx_priority_fee; la t0, bmvmx_gas_used; ld a1, 0(t0); la a2, bmvmx_coinbase_credit; jal ra, u256_mul_u64_be\n" ++
  -- bmvmx.1.4.2 compare.  GH #11211 retired its write-only result flag; the compare below
  -- assert the BAL coinbase post balance == coinbase_pre + bmvmx_coinbase_credit. Any miss /
  -- not-found / overlap (coinbase==sender/recipient) / absent leaves match=0 (conservative).
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
  ".Lbmvmx_cb_skip:\n" ++
  bvReceiptsShapeSet 1 true ++  -- Distinctness clears the performed sender/coinbase checks when value/fee effects overlap.
  "  la a0, bmvmx_sender_addr; la a1, bmvmx_ctx; addi a1, a1, 72; jal ra, .Lbmvmx_addr20_ne\n" ++
  "  bnez a0, .Lbmvmx_s_vs_cb\n" ++                                    -- sender == recipient -> clear sender_checked
  ".Lbmvmx_s_vs_cb:\n" ++
  "  la a0, bmvmx_sender_addr; la a1, bmvmx_coinbase_addr; jal ra, .Lbmvmx_addr20_ne\n" ++
  "  bnez a0, .Lbmvmx_cb_vs_s\n" ++                                    -- sender == coinbase -> clear sender_checked
  ".Lbmvmx_cb_vs_s:\n" ++
  "  la a0, bmvmx_coinbase_addr; la a1, bmvmx_sender_addr; jal ra, .Lbmvmx_addr20_ne\n" ++
  "  bnez a0, .Lbmvmx_cb_vs_r\n" ++                                    -- coinbase == sender -> clear coinbase_checked
  ".Lbmvmx_cb_vs_r:\n" ++
  "  la a0, bmvmx_coinbase_addr; la a1, bmvmx_ctx; addi a1, a1, 72; jal ra, .Lbmvmx_addr20_ne\n" ++
  "  bnez a0, .Lbmvmx_dist_done\n" ++                                  -- coinbase == recipient -> clear coinbase_checked
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
  ".Lbmvmx_done:\n"

end EvmAsm.Codegen
