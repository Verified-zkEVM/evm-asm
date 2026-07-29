/-
  EvmAsm.Codegen.Programs.BlockVerdictEoaBodyEffectReconcile

  EOA body-effect reconciliation prefix for block_verdict.
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Prefix which seeds the EOA skip list and publishes block-level effects. -/
def blockVerdictEoaBodyEffectReconcile : String :=
  ".Lbv_eoa_body_effect_reconcile:\n" ++
  "  li t0, 0xa0010000; li t1, 0xe0a; sd t1, 512(t0)\n" ++
  "  la t0, i3djw_skip_list\n  la t1, bv_simple_transfer_tx; addi t1, t1, 72\n  li t2, 20\n" ++
  ".Lbv_i3sk0:\n  beqz t2, .Lbv_i3sk0d\n  lbu t3, 0(t1)\n  sb t3, 0(t0)\n  addi t1, t1, 1\n  addi t0, t0, 1\n  addi t2, t2, -1\n  j .Lbv_i3sk0\n.Lbv_i3sk0d:\n" ++
  -- A zero-transaction block has a valid empty public-key section.  There is
  -- therefore no sender to skip-list: deriving one from public_keys_ptr + 1
  -- would ask `address_from_pubkey` to hash a nonexistent 64-byte SEC1 tail.
  -- Leave the zero-initialized entry unused and retain the block-level
  -- withdrawal/system reconciliation below.
  "  la t4, bv_tx_count; ld t4, 0(t4); beqz t4, .Lbv_i3sk1d\n" ++
  "  la a1, i3djw_skip_list; addi a1, a1, 32\n  la a0, bv_public_keys_ptr; ld a0, 0(a0); addi a0, a0, 1\n  jal ra, address_from_pubkey\n.Lbv_i3sk1d:\n" ++
  "  la t0, i3djw_skip_list; addi t0, t0, 64\n  la t1, bv_exec_p; ld t1, 0(t1); addi t1, t1, 32\n  li t2, 20\n" ++
  ".Lbv_i3sk2:\n  beqz t2, .Lbv_i3sk2d\n  lbu t3, 0(t1)\n  sb t3, 0(t0)\n  addi t1, t1, 1\n  addi t0, t0, 1\n  addi t2, t2, -1\n  j .Lbv_i3sk2\n.Lbv_i3sk2d:\n" ++
  "  la t0, i3djw_skip_list; addi t0, t0, 96\n  la t1, bbcv_sys_2935\n  li t4, 6\n" ++
  ".Lbv_i3sksys_o:\n  li t2, 20\n" ++
  ".Lbv_i3sksys_i:\n  lbu t3, 0(t1)\n  sb t3, 0(t0)\n  addi t1, t1, 1\n  addi t0, t0, 1\n  addi t2, t2, -1\n  bnez t2, .Lbv_i3sksys_i\n" ++
  "  addi t0, t0, 12\n  addi t4, t4, -1\n  bnez t4, .Lbv_i3sksys_o\n" ++
  "  la t2, bv_tx_list_ptr; ld a0, 0(t2)\n  la t2, bv_tx_list_len; ld a1, 0(t2)\n  la t2, bv_tx_count; ld a2, 0(t2)\n" ++
  "  la t2, bv_bal_start; ld a3, 0(t2)\n  la t2, bv_bal_len; ld a4, 0(t2)\n  la t2, bv_chain_id; ld a5, 0(t2)\n" ++
  "  jal ra, block_verdict_eip7702_auth_nonstorage_effects_array\n" ++
  "  jal ra, block_verdict_withdrawal_nonstorage_effects\n" ++
  "  bnez a0, .Lbv_bal_nonstorage_fail\n"

end EvmAsm.Codegen
