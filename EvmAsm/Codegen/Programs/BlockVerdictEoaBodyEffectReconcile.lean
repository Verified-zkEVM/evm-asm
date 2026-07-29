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
  "  bnez a0, .Lbv_bal_nonstorage_fail\n" ++
  -- EIP-7928: the post-transaction boundary runs at `block_access_index =
  -- ulen(transactions) + 1` (`fork.py:917-919`), and `process_withdrawals`
  -- incorporates there like any other producer (`fork.py:921` → `:1226`).
  -- `BlockVerdictMtxRuntime` already does exactly this after `.Lbv_mtx_done`;
  -- THIS call site did not, so on a block with **no transactions** the
  -- withdrawal credit was recorded into the nonstorage effect log by
  -- `record_nonstorage_effect` and then nothing ever walked it into the
  -- builder.  Same recorder, two callers, one contract silently different.
  --
  -- Measured by PC on one guest ELF (sha d191c0e4e299): the two call sites are
  -- MUTUALLY EXCLUSIVE — exactly one fires per block across 0, 1 and 5
  -- transactions (00566 takes this one and emitted ZERO balance rows; 00565 and
  -- 23725 take the MtxRuntime one and emitted 4 and 15).  So feeding the
  -- builder here cannot double-feed the `ntx >= 1` path; 00565 staying at 350
  -- is the canary for that.
  --
  -- With zero transactions `bv_tx_count + 1` is 1, which is the index the
  -- declared BALs of these blocks actually carry.
  "  la t0, bv_tx_count; ld t1, 0(t0); addi t1, t1, 1; la t0, current_block_access_index; sd t1, 0(t0)\n" ++
  "  jal ra, account_writes_emit_builder_tx\n" ++
  "  jal ra, account_writes_incorporate_tx\n" ++
  "  la t0, account_writes_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n"

end EvmAsm.Codegen
