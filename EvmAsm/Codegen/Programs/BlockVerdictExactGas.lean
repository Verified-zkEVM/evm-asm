/-
  EvmAsm.Codegen.Programs.BlockVerdictExactGas

  Exact Amsterdam/EIP-8037 block gas_used check for block_verdict.
-/

namespace EvmAsm.Codegen

/-- Exact EIP-8037 final header gas_used check. Assumes the runtime gas-result
    arena was prepared and `bvgr_tx_total_state_gas` was materialized by the
    `block_verdict_eip8037_tx_state_gas_net_array` call ahead of the EIP-7778
    gate (BlockVerdictFunction, evm-asm-0w05f.17.2). -/
def blockVerdictExactGasCheck : String :=
  -- xbi56.2 / #11808: exact EIP-8037 block gas_used equality.
  -- Independent regular arm from settle meters (fork.py:1176-1181 shape):
  --   before_refund ≃ tx.gas - reg_left - state_left
  --   tx_state_gas  ≃ intrinsic + exec_used   (exec from settle state_used;
  --                     spill-from-regular is inside exec_used when res_init=0)
  --   regular_consumed = tx.gas - reg_left - state_left - state_used - intrinsic
  --                    = before_refund - (intrinsic + exec_used)
  -- Does NOT subtract free `bvgr_tx_total_state_gas`. Floor on regular arm
  -- (fork.py:1176-1181); fee/receipt total floor stays in
  -- `tx_gas_result_increments` (fork.py:1155-1159).
  --
  -- ⚠️ `header.gas_used` IS A **MAX** OVER TWO INDEPENDENT DIMENSIONS, NOT A SUM,
  -- AND NOT THE RECEIPT'S `cumulative_gas_used`. At `execution-specs` @ `e5a8caf1b`:
  --
  --   fork.py:1181   block_output.block_gas_used       += tx_regular_gas
  --   fork.py:1182   block_output.block_state_gas_used += max(0, tx_state_gas)
  --   fork.py:1185   block_output.cumulative_gas_used  += tx_gas_used   -- RECEIPT
  --   fork.py:370-375
  --       block_gas_used = max(block_output.block_gas_used,
  --                            block_output.block_state_gas_used)
  --
  -- ⇒ THREE accumulators. Receipt cumulative can exceed header.gas_used.
  "  la t0, bvgr_arena_tx_count; ld t0, 0(t0); li t1, 0\n" ++
  ".Lbv_regular_eip8037_loop:\n" ++
  "  beq t1, t0, .Lbv_regular_eip8037_done\n" ++
  "  slli t5, t1, 3\n" ++
  "  la t6, bvgr_tx_gas_limits; add t6, t6, t5; ld a0, 0(t6)\n" ++
  "  la t6, bv_mtx_regular_gas_left; add t6, t6, t5; ld a1, 0(t6)\n" ++
  "  bltu a0, a1, .Lbv_block_state_gas_fail\n" ++
  "  sub a0, a0, a1\n" ++
  "  la t6, bv_mtx_state_gas_left; add t6, t6, t5; ld a1, 0(t6)\n" ++
  "  bltu a0, a1, .Lbv_block_state_gas_fail\n" ++
  "  sub a0, a0, a1\n" ++
  "  la t6, bv_mtx_state_gas_used; add t6, t6, t5; ld a1, 0(t6)\n" ++
  "  bltu a0, a1, .Lbv_block_state_gas_fail\n" ++
  "  sub a0, a0, a1\n" ++
  "  la t6, bvgr_tx_state_gas; add t6, t6, t5; ld a1, 0(t6)\n" ++
  "  bltu a0, a1, .Lbv_block_state_gas_fail\n" ++
  "  sub a0, a0, a1\n" ++
  "  la t6, bvgr_calldata_floor; add t6, t6, t5; ld a1, 0(t6)\n" ++
  "  bgeu a0, a1, .Lbv_regular_eip8037_store\n" ++
  "  mv a0, a1\n" ++
  ".Lbv_regular_eip8037_store:\n" ++
  "  la t6, bvgr_block_gas_increments; add t6, t6, t5; sd a0, 0(t6)\n" ++
  "  addi t1, t1, 1; j .Lbv_regular_eip8037_loop\n" ++
  ".Lbv_regular_eip8037_done:\n" ++
  "  la t5, bv_exec_p; ld t4, 0(t5); addi a0, t4, 420; jal ra, bgv_u64le   # header.gas_used\n" ++
  "  la t2, bv_exact_header_gas_used; sd a0, 0(t2)\n" ++
  "  mv t1, a0                                            # stash gas_used (bgv_u64le clobbers t6)\n" ++
  "  la a0, bvgr_block_gas_increments\n" ++
  "  la a1, bvgr_tx_total_state_gas\n" ++
  "  la t2, bvgr_arena_tx_count; ld a2, 0(t2)\n" ++
  "  mv a3, t1\n" ++
  "  la a4, bv_exact_expected_gas_used\n" ++
  "  jal ra, eip8037_block_gas_used\n" ++
  "  la t2, bv_exact_block_status; sd a0, 0(t2)\n" ++
  "  bnez a0, .Lbv_block_gas_used_over_fail\n" ++
  ".Lbv_block_gas_used_exact_ok:\n" ++
  "  la t2, bv_exact_header_gas_used; ld t1, 0(t2)           # reload across helper clobbers\n" ++
  "  la t5, bv_exec_p; ld t4, 0(t5); addi a0, t4, 412; jal ra, bgv_u64le   # header.gas_limit @+412\n" ++
  "  bgtu t1, a0, .Lbv_block_gas_used_over_fail            # header.gas_used > gas_limit -> reject\n" ++
  ""

end EvmAsm.Codegen
