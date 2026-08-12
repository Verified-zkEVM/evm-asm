/-
  EvmAsm.Codegen.Programs.BlockVerdictFunctionTail

  Terminal settlement phase of the main block_verdict assembly string.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.BlockVerdictGasGatePrelude
import EvmAsm.Codegen.Programs.BlockVerdictExactGas
import EvmAsm.Codegen.Programs.BlockVerdictReceiptsTail

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## block_verdict terminal settlement

    This remains a suffix, not a callable subroutine: `blockVerdictFunction`
    concatenates it immediately after the runtime phase so labels and emitted
    instruction order remain byte-identical. -/
def blockVerdictFunctionTail : String :=
  blockVerdictGasGatePrelude ++
  -- #12228: mpt_walk keeps its historical status (1 = genuine trie absence)
  -- but latches a required-hash lookup miss out of band.  The root miss is
  -- exempt only when the block's authenticated root is EMPTY_TRIE_ROOT; a
  -- child miss is always unresolved.  This gate is after the gas prelude so
  -- settlement paths that jump to .Lbv_after_tx_gas_precharge cannot bypass it,
  -- and it is present only in block_verdict (standalone probes have no gate).
  "  la t0, mw_lookup_hash; ld t0, 48(t0); beqz t0, .Lbv_mpt_unresolved_ok\n" ++
  "  li t1, 1; bne t0, t1, .Lbv_mpt_unresolved_fail\n" ++
  "  ld t0, 24(s0); la t1, iw_empty_trie_root\n" ++
  "  ld t2, 0(t0); ld t3, 0(t1); bne t2, t3, .Lbv_mpt_unresolved_fail\n" ++
  "  ld t2, 8(t0); ld t3, 8(t1); bne t2, t3, .Lbv_mpt_unresolved_fail\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lbv_mpt_unresolved_fail\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lbv_mpt_unresolved_fail\n" ++
  ".Lbv_mpt_unresolved_ok:\n" ++
  -- Exact block-gas settlement needs one runtime result for every transaction.
  -- Creation and otherwise unsupported execution shapes deliberately leave that
  -- arena incomplete; their pre-execution EIP-8037 admission was already checked
  -- by eip8037_tx_gas_gate above, so retain the conservative settlement skip.
  -- Dynamic ancestor-coverage check (#11378): reject when the deepest
  -- in-window ancestor actually accessed (BLOCKHASH per block.py:61, or the
  -- parent tracked by the EIP-2935 system call per fork.py:908) exceeds the
  -- supplied witness header count. execution-specs would fail witness
  -- validation on such an access.  Must run AFTER the runtime loop (the mark
  -- is fed during execution) and AFTER the gas-gate prelude: settlement paths
  -- jump into the prelude at .Lbv_after_tx_gas_precharge, so a gate placed
  -- before it is skipped on those paths.
  "  la t5, evm_oldest_ancestor_offset; ld t4, 0(t5)\n" ++
  "  la t5, svf_headers_count; ld t3, 0(t5)\n" ++
  "  bgtu t4, t3, .Lbv_blockhash_headers_fail\n" ++
  "  bnez a0, .Lbv_after_gas_result_gate\n" ++
  -- The live per-transaction boundary has already populated
  -- bvgr_tx_state_gas.  Keep the common total-state and regular-settlement
  -- consumers below, but never reconstruct intrinsic/auth charges here from
  -- the block-final transaction list.
  -- 0w05f.17.2: materialize the v0.6 per-tx settlement identity (fork.py:1174)
  --   tx_state_gas = intrinsic.state + executed state gas
  -- into bvgr_tx_total_state_gas BEFORE the EIP-7778 gate, so the per-tx
  -- regular increment below can subtract it (fork.py:1176-1181). The executed
  -- component was captured per tx by dispatcher_capture_exec_state_gas.  A
  -- failed/unsupported transaction finalizes only its intrinsic/auth component
  -- at its own transaction boundary.
  -- Each supported transaction finalizes its total state-gas cell immediately
  -- after execution settles.  The current state-refund substrate is
  -- identically zero, so no late block-wide netting pass is needed.
  "  la t2, bv_exact_net_status; sd zero, 0(t2)\n" ++
  "  la t2, bv_exact_net_index; sd zero, 0(t2)\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2); addi a0, t1, 412; jal ra, bgv_u64le\n" ++
  "  la a1, bvgr_tx_gas_limits\n" ++
  "  la a2, bvgr_gas_left\n" ++
  "  la a3, bvgr_refund_counter\n" ++
  "  la a4, bvgr_calldata_floor\n" ++
  "  la t2, bvgr_arena_tx_count; ld a5, 0(t2)\n" ++
  "  la a6, bvgr_block_gas_increments\n" ++
  "  la a7, bvgr_tx_total_state_gas   # 0w05f.17.2: per-tx intrinsic+executed state -> tx_regular = max(before_refund - state, floor)\n" ++
  "  jal ra, eip7778_remaining_block_gas_from_results\n" ++
  "  la t2, bv_eip7778_status; sd a0, 0(t2)\n" ++
  "  la t2, bv_eip7778_index; sd a1, 0(t2)\n" ++
  "  la t2, bv_eip7778_used; sd a2, 0(t2)\n" ++
  "  beqz a0, .Lbv_eip7778_gate_ok\n" ++
  "  j .Lbv_eip7778_block_gas_fail\n" ++
  ".Lbv_eip7778_gate_ok:\n" ++
  blockVerdictExactGasCheck ++
  -- Fixed execution arenas are gas-bounded. Their producers latch an overflow
  -- and return normally to preserve call frames; reject the incomplete record here.
  "  la t0, create_nonce_table_overflow; ld t0, 0(t0); bnez t0, .Lbv_fixed_arena_overflow_fail\n" ++
  "  la t0, exec_code_effect_overflow; ld t0, 0(t0); bnez t0, .Lbv_fixed_arena_overflow_fail\n" ++
  -- AccountState producers can latch overflow during the post-dispatch commit
  -- (after the MTx runtime gate), and that failure path jumps directly here.
  -- Consume the latch at the common tail so commit overflow cannot bypass the
  -- verdict rejection merely by arriving after the earlier per-dispatch check.
  "  la t0, account_state_overflow; ld t0, 0(t0); bnez t0, .Lbv_fixed_arena_overflow_fail\n" ++
  -- B2.3 used to treat this latch as a reason to skip its comparison.  That
  -- turns a truncated non-storage execution log into an accepted block, so the
  -- common terminal gate consumes it exactly like the other fixed arenas.
  "  la t0, exec_nonstorage_effect_overflow; ld t0, 0(t0); bnez t0, .Lbv_fixed_arena_overflow_fail\n" ++
  -- The execution-derived BAL builder is append-only for the duration of a
  -- block.  Its component appenders return normally to preserve runtime call
  -- frames, so the common terminal gate consumes their shared latch rather
  -- than serializing a truncated access list.
  "  la t0, bal_builder_overflow; ld t0, 0(t0); bnez t0, .Lbv_fixed_arena_overflow_fail\n" ++
  blockVerdictReceiptsTail

end EvmAsm.Codegen
