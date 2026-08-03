/-
  EvmAsm.Codegen.Programs.BlockVerdictSingleTxLog

  Small helper for block_verdict's single-transaction contract-recipient path.
  It emits the EIP-7708 top-level value-transfer log before runtime dispatch so
  receipt log order matches execution-specs: top-level value movement first,
  then recipient-code logs.
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- #10685 PR2: unlinked from guest. Kept for probe isolation / historical shape.
    Sole consumer of `bv_simple_transfer_tx` (also deleted). SPIKE_WATCH hits=0;
    mode-2 gate bypasses jal; early-exit on zero buffer before any eip7708_tl write. -/
def blockVerdictSingleTxTopLevelLogFunction : String :=
  "bv_emit_single_tx_tl7708:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp); sd x20, 8(sp)\n" ++
  "  la t0, bv_simple_transfer_tx; ld t1, 0(t0); bnez t1, .Lbvestl_ret\n" ++
  "  addi t1, t0, 96; ld t2, 0(t1); ld t3, 8(t1); or t2, t2, t3; ld t3, 16(t1); or t2, t2, t3; ld t3, 24(t1); or t2, t2, t3\n" ++
  "  beqz t2, .Lbvestl_ret\n" ++
  "  ld a0, 24(t0); beqz a0, .Lbvestl_ret\n" ++
  "  la a1, bmvmx_sender_addr; jal ra, address_from_pubkey\n" ++
  "  la t0, bmvmx_sender_addr; la t1, bv_simple_transfer_tx; addi t1, t1, 72; li t2, 20\n" ++
  ".Lbvestl_selfcmp:\n" ++
  "  beqz t2, .Lbvestl_ret\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbvestl_notself\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbvestl_selfcmp\n" ++
  ".Lbvestl_notself:\n" ++
  "  la t0, eip7708_tl_from32\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, bmvmx_sender_addr; addi t1, t1, 19; mv t2, t0; li t3, 20\n" ++
  ".Lbvestl_from:\n  beqz t3, .Lbvestl_from_done\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbvestl_from\n" ++
  ".Lbvestl_from_done:\n" ++
  "  la t0, eip7708_tl_to32\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, bv_simple_transfer_tx; addi t1, t1, 91; mv t2, t0; li t3, 20\n" ++
  ".Lbvestl_to:\n  beqz t3, .Lbvestl_to_done\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbvestl_to\n" ++
  ".Lbvestl_to_done:\n" ++
  "  la t0, eip7708_tl_val32\n  la t1, bv_simple_transfer_tx; addi t1, t1, 127; mv t2, t0; li t3, 32\n" ++
  ".Lbvestl_val:\n  beqz t3, .Lbvestl_val_done\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbvestl_val\n" ++
  ".Lbvestl_val_done:\n" ++
  "  li t1, 1; la t0, eip7708_tl_typed_avail; sd t1, 0(t0)\n" ++
  -- bmvmx.5.5.2.2.ln9ly: STAGE the top-level transfer log for re-emit after the
  -- dispatcher's per-tx event-log reset; dispatcher_reemit_pending_tl emits it as log 0
  -- from eip7708_tl_* and clears the flag. Only set on this success path.
  "  la t0, bv_pending_tl_flag; sd t1, 0(t0)\n" ++
  ".Lbvestl_ret:\n" ++
  "  ld ra, 0(sp); ld x20, 8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

end EvmAsm.Codegen
