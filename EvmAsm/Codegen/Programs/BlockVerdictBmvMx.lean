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
  -- #11183 ORDER-1: RETIRED sender/coinbase BAL post-balance field compares
  -- (.Lbmvmx_sd_preok / .Lbmvmx_cb_preok Class-A edges). Spec pin e5a8caf1b
  -- amsterdam fork.py:390 — only validation is hash of the BUILT BAL vs header.
  -- Spec has no supplied body and performs no field compare; a guest that still
  -- compares supplied BAL fields against exec-derived expected REJECTS blocks
  -- the spec accepts under a hash collision (FR breaks equivalence). Equivalence
  -- argument only — not "hash covers it" (that needs collision-freedom).
  -- Debit/credit scalars above stay as inert precompute. No bv_bal_start/len.
  -- Keep receipts-shape enforce for this single-tx legacy envelope (was set after
  -- the retired compares); BAL field match is no longer a gate.
  bvReceiptsShapeSet 1 true ++
  "  j .Lbmvmx_done\n" ++
  ".Lbmvmx_done:\n"

end EvmAsm.Codegen
