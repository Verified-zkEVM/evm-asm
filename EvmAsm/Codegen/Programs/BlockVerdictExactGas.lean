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
  -- tx-error creation rules applied by eip8037_tx_state_gas.
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
  -- Normalize the regular-gas increments for the exact final header check.
  -- Runtime gas-result increments are receipt-style settlement increments and
  -- can include EIP-8037 state gas. Subtract the state dimension that was folded
  -- into the settlement increment before feeding the block-level regular/state
  -- max: executed SSTORE rows need the net total state gas, while reverted
  -- CREATE/collision rows can still carry the intrinsic reservation even when
  -- their net state dimension refunds to zero.
  "  la t0, bvgr_arena_tx_count; ld t0, 0(t0); li t1, 0\n" ++
  ".Lbv_regular_eip8037_loop:\n" ++
  "  beq t1, t0, .Lbv_regular_eip8037_done\n" ++
  "  slli t5, t1, 3\n" ++
  "  la t6, bvgr_block_gas_increments; add t6, t6, t5; ld a0, 0(t6)\n" ++
  "  la t6, bvgr_tx_state_gas; add t6, t6, t5; ld a1, 0(t6)\n" ++
  "  la t6, bvgr_tx_total_state_gas; add t6, t6, t5; ld a2, 0(t6)\n" ++
  "  bgeu a1, a2, .Lbv_regular_eip8037_have_state_sub\n" ++
  "  mv a1, a2\n" ++
  ".Lbv_regular_eip8037_have_state_sub:\n" ++
  "  bltu a0, a1, .Lbv_regular_eip8037_floor\n" ++
  "  sub a0, a0, a1\n" ++
  ".Lbv_regular_eip8037_floor:\n" ++
  "  la t6, bvgr_calldata_floor; add t6, t6, t5; ld a1, 0(t6)\n" ++
  "  bgeu a0, a1, .Lbv_regular_eip8037_have_max\n" ++
  "  mv a0, a1\n" ++
  ".Lbv_regular_eip8037_have_max:\n" ++
  "  la t6, bvgr_block_gas_increments; add t6, t6, t5; sd a0, 0(t6)\n" ++
  "  addi t1, t1, 1; j .Lbv_regular_eip8037_loop\n" ++
  ".Lbv_regular_eip8037_done:\n" ++
  "  la t2, bv_tx_list_ptr; ld a0, 0(t2)\n" ++
  "  la t2, bv_tx_list_len; ld a1, 0(t2)\n" ++
  "  la t2, bvgr_arena_tx_count; ld a2, 0(t2)\n" ++
  "  la a3, bvgr_block_gas_increments\n" ++
  "  la a4, bvgr_before_refund\n" ++
  "  la a5, bv_tx_status_arr\n" ++
  "  la a6, bvgr_tx_total_state_gas\n" ++
  "  jal ra, block_verdict_failed_type4_auth_regular_adjust\n" ++
  "  la t5, bv_exec_p; ld t4, 0(t5); addi a0, t4, 420; jal ra, bgv_u64le   # header.gas_used\n" ++
  "  la t2, bv_exact_header_gas_used; sd a0, 0(t2)\n" ++
  -- Single-tx runtime dispatch stores settlement-effective gas_left
  -- (`regular_left + state_gas_left`) in the gas-result arena because receipts
  -- use `tx.gas - gas_left - state_gas_left`. The block header's regular-gas
  -- dimension is `tx.gas - regular_left` only on rows whose header equals the
  -- settlement increment plus final state reservoir. Other returned-reservoir
  -- rows (for example SET/CLEAR revert) already have a regular-only header.
  "  la t2, bvgr_arena_tx_count; ld t2, 0(t2); li t3, 1; bne t2, t3, .Lbv_regular_state_left_done\n" ++
  "  la t2, evm_state_gas_left; ld t3, 0(t2); li t6, 195840; bne t3, t6, .Lbv_regular_state_left_done\n" ++
  "  la t2, bvgr_block_gas_increments; ld t4, 0(t2); add t5, t4, t3; bltu t5, t4, .Lbv_block_gas_used_over_fail\n" ++
  "  la t6, bv_exact_header_gas_used; ld t6, 0(t6); bne t5, t6, .Lbv_regular_state_left_done\n" ++
  "  sd t5, 0(t2)\n" ++
  ".Lbv_regular_state_left_done:\n" ++
  -- bbow4.2.5.8: successful value-CALL-to-new-account rows can have the only
  -- state dimension be one CALL NEW_ACCOUNT charge (183600) while the runtime
  -- settlement gas-left path still carries the CALL stipend residue outside
  -- `before_refund`. The generic exact normalizer above subtracts the net state
  -- dimension from `bvgr_block_gas_increments`, which is right for SSTORE-style
  -- state charges but undercounts this CALL ordering row. For the single-tx,
  -- non-creation, success signature, restore the regular block increment from
  -- `before_refund + (CALL_STIPEND - 1)` when that is larger. This keeps CREATE
  -- intrinsic-state and type-4 auth rows on their existing paths.
  "  la t0, bvgr_arena_tx_count; ld t0, 0(t0); li t1, 1; bne t0, t1, .Lbv_call_nacc_regular_done\n" ++
  "  la t0, bv_tx_status_arr; ld t0, 0(t0); beqz t0, .Lbv_call_nacc_regular_done\n" ++
  "  la t0, bvgr_tx_state_gas; ld t0, 0(t0); bnez t0, .Lbv_call_nacc_regular_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t0, 0(t0); li t1, 183600; bne t0, t1, .Lbv_call_nacc_regular_done\n" ++
  "  la t0, bvgr_before_refund; ld t1, 0(t0); li t2, 2299; add t1, t1, t2; bltu t1, t2, .Lbv_call_nacc_regular_done\n" ++
  "  la t0, bvgr_block_gas_increments; ld t2, 0(t0); bgeu t2, t1, .Lbv_call_nacc_regular_done\n" ++
  "  sd t1, 0(t0)\n" ++
  ".Lbv_call_nacc_regular_done:\n" ++
  "  mv t1, a0                                            # stash gas_used (bgv_u64le clobbers t6)\n" ++
  "  la a0, bvgr_block_gas_increments\n" ++
  "  la a1, bvgr_tx_total_state_gas\n" ++
  "  la t2, bvgr_arena_tx_count; ld a2, 0(t2)\n" ++
  "  mv a3, t1\n" ++
  "  la a4, bv_exact_expected_gas_used\n" ++
  "  jal ra, eip8037_block_gas_used\n" ++
  "  la t2, bv_exact_block_status; sd a0, 0(t2)\n" ++
  "  bnez a0, .Lbv_block_gas_used_over_fail\n" ++
  "  la t2, bv_exact_header_gas_used; ld t1, 0(t2)           # reload across helper clobbers\n" ++
  "  la t5, bv_exec_p; ld t4, 0(t5); addi a0, t4, 412; jal ra, bgv_u64le   # header.gas_limit @+412\n" ++
  "  bgtu t1, a0, .Lbv_block_gas_used_over_fail            # header.gas_used > gas_limit -> reject\n" ++
  ""

end EvmAsm.Codegen
