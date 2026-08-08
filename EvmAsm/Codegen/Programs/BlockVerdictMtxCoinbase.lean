/-
  EvmAsm.Codegen.Programs.BlockVerdictMtxCoinbase

  Multi-transaction coinbase fee live-balance threading for block_verdict.
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! Record the current transaction's priority-fee credit to the block coinbase
    as a non-storage balance effect. Later transactions that execute
    `BALANCE(COINBASE)` consult the live non-storage log before falling back to
    the pre-state trie, matching execution-specs' intra-block fee visibility. -/
def blockVerdictMtxCoinbaseFeeEffect : String :=
  "  # Make this tx's coinbase fee credit visible to later BALANCE(COINBASE) reads.\n" ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); slli t2, t1, 3\n" ++
  "  la t3, bv_mtx_ctx; ld a0, 40(t3)       # tx.gas_limit\n" ++
  "  la t3, bv_mtx_gas_left; add t3, t3, t2; ld a1, 0(t3)\n" ++
  "  la t3, bv_mtx_refund; add t3, t3, t2; ld a2, 0(t3)\n" ++
  "  la t3, bv_mtx_calldata; add t3, t3, t2; ld a3, 0(t3)\n" ++
  "  jal ra, tx_gas_result_increments\n" ++
  "  bnez a0, .Lbv_mtx_cbfee_done\n" ++
  "  la t0, bv_mtx_cbfee_receipt_inc; sd a2, 0(t0)\n" ++
  "  la t0, bv_mtx_ctx; ld a0, 8(t0); ld a1, 16(t0); la a2, bv_mtx_base_fee_be; la a3, bv_mtx_cbfee_egp; la a4, bv_mtx_cbfee_priority\n" ++
  "  jal ra, tx_effective_gas_pricing\n" ++
  "  bnez a0, .Lbv_mtx_cbfee_done\n" ++
  "  la a0, bv_mtx_cbfee_priority; la t0, bv_mtx_cbfee_receipt_inc; ld a1, 0(t0); la a2, bv_mtx_cbfee_credit\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lbv_mtx_cbfee_done\n" ++
  "  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0)\n" ++
  "  la t0, bv_exec_p; ld t0, 0(t0); addi a2, t0, 32\n" ++
  "  ld a3, 80(s0); ld a4, 88(s0); la a5, bv_mtx_cbfee_pre\n" ++
  "  jal ra, balance_live_else_header_state_root\n" ++
  "  bnez a0, .Lbv_mtx_cbfee_done\n" ++
  "  la a0, bv_mtx_cbfee_pre; la a1, bv_mtx_cbfee_credit; la a2, bv_mtx_cbfee_post\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lbv_mtx_cbfee_done\n" ++
  "  la t0, bv_exec_p; ld t0, 0(t0); addi a0, t0, 32\n" ++
  "  la a1, bv_mtx_cbfee_pre; la a2, bv_mtx_cbfee_post; li a3, 0; li a4, 0\n" ++
  "  jal ra, record_nonstorage_effect\n" ++
  ".Lbv_mtx_cbfee_done:\n"

end EvmAsm.Codegen
