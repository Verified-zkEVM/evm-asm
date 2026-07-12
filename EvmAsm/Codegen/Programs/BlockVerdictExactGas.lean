/-
  EvmAsm.Codegen.Programs.BlockVerdictExactGas

  Exact Amsterdam/EIP-8037 block gas_used check for block_verdict.
-/

namespace EvmAsm.Codegen

/-- Exact EIP-8037 final header gas_used check. Assumes the runtime gas-result
    arena was prepared and per-tx status/creation/state-gas arrays are populated. -/
def blockVerdictExactGasCheck : String :=
  -- xbi56.2: exact EIP-8037 block gas_used equality for rows whose runtime
  -- arena was prepared. State gas is intrinsic + executed - state_refund with
  -- tx-error creation-refund eligibility rules applied by eip8037_tx_state_gas.
  "  la a0, bvgr_tx_state_gas\n" ++
  "  la a1, bvgr_tx_exec_state_gas\n" ++
  "  la a2, bvgr_tx_state_refund\n" ++
  "  la a3, bv_tx_status_arr\n" ++
  "  la a4, bv_tx_is_creation_arr\n" ++
  "  la t2, bvgr_arena_tx_count; ld a5, 0(t2)\n" ++
  "  la a6, bvgr_tx_total_state_gas\n" ++
  "  jal ra, block_verdict_eip8037_tx_state_gas_net_array\n" ++
  "  la t2, bv_exact_net_status; sd a0, 0(t2)\n" ++
  "  la t2, bv_exact_net_index; sd a1, 0(t2)\n" ++
  "  bnez a0, .Lbv_block_state_gas_fail\n" ++
  -- Derive Amsterdam's block-regular dimension from the exact pre-refund
  -- combined gas and the net state-gas dimension (v0.6.0, EIP-2780/fork.py):
  --   tx_regular_gas = max(before_refund - tx_state_gas, calldata_floor)
  -- `before_refund` is `tx.gas - gas_left - state_gas_left`, so it includes
  -- regular gas plus state gas. v0.6.0 makes the EIP-7623/7976 calldata
  -- floor bind the block-regular dimension too (state gas subtracted
  -- FIRST, so the floor is not discounted by state spending); it was
  -- receipt-only at v0.5.0.
  "  la t0, bvgr_arena_tx_count; ld t0, 0(t0); li t1, 0\n" ++
  ".Lbv_regular_eip8037_loop:\n" ++
  "  beq t1, t0, .Lbv_regular_eip8037_done\n" ++
  "  slli t5, t1, 3\n" ++
  "  la t6, bvgr_before_refund; add t6, t6, t5; ld a0, 0(t6)\n" ++
  "  la t6, bvgr_tx_total_state_gas; add t6, t6, t5; ld a1, 0(t6)\n" ++
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
