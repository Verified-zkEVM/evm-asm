/-
  EvmAsm.Codegen.Programs.BlockVerdictTransactions

  Transaction-list validation fragments carved out of BlockVerdict.lean.
-/

namespace EvmAsm.Codegen

def blockVerdictEmptyTransactionCheckAsm : String :=
  ".Lbv_tx_present:\n" ++
  "  # execution-specs rejects b\"\" in payload.transactions before block execution.\n" ++
  "  la t5, bv_exec_p; ld t4, 0(t5); la t5, bv_tx_off; ld t3, 0(t5); add t5, t4, t3; la t6, bv_tx_list_ptr; sd t5, 0(t6)\n" ++
  "  addi a0, t4, 508; jal ra, bgv_u32le; la t6, bv_tx_off; ld t3, 0(t6); bltu a0, t3, .Lbv_after_empty_tx_check\n" ++
  "  sub t5, a0, t3; la t6, bv_tx_list_len; sd t5, 0(t6); li t6, 4; bltu t5, t6, .Lbv_after_empty_tx_check\n" ++
  "  la t6, bv_tx_list_ptr; ld a0, 0(t6); jal ra, bgv_u32le; andi t0, a0, 3; bnez t0, .Lbv_after_empty_tx_check\n" ++
  "  srli t1, a0, 2; beqz t1, .Lbv_after_empty_tx_check; slli t2, t1, 2; la t6, bv_tx_list_len; ld t3, 0(t6); bgtu t2, t3, .Lbv_after_empty_tx_check\n" ++
  "  la t6, bv_tx_count; sd t1, 0(t6); la t6, bv_tx_index; sd zero, 0(t6)\n" ++
  ".Lbv_empty_tx_loop:\n" ++
  "  la t6, bv_tx_index; ld t0, 0(t6); la t6, bv_tx_count; ld t1, 0(t6); beq t0, t1, .Lbv_after_empty_tx_check\n" ++
  "  la t6, bv_tx_list_ptr; ld t2, 0(t6); slli t3, t0, 2; add a0, t2, t3; jal ra, bgv_u32le; la t6, bv_tx_item_start; sd a0, 0(t6)\n" ++
  "  la t6, bv_tx_index; ld t0, 0(t6); addi t0, t0, 1; la t6, bv_tx_count; ld t1, 0(t6); beq t0, t1, .Lbv_empty_tx_last\n" ++
  "  la t6, bv_tx_list_ptr; ld t2, 0(t6); slli t3, t0, 2; add a0, t2, t3; jal ra, bgv_u32le\n" ++
  "  j .Lbv_empty_tx_have_end\n" ++
  ".Lbv_empty_tx_last:\n" ++
  "  la t6, bv_tx_list_len; ld a0, 0(t6)\n" ++
  ".Lbv_empty_tx_have_end:\n" ++
  "  la t6, bv_tx_item_start; ld t3, 0(t6); bltu a0, t3, .Lbv_after_empty_tx_check; beq a0, t3, .Lbv_empty_tx_fail\n" ++
  "  la t6, bv_tx_index; ld t0, 0(t6); addi t0, t0, 1; sd t0, 0(t6); j .Lbv_empty_tx_loop\n" ++
  ".Lbv_after_empty_tx_check:\n"

end EvmAsm.Codegen
