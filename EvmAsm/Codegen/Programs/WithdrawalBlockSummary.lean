/-
  EvmAsm.Codegen.Programs.WithdrawalBlockSummary

  Block-level withdrawal count and body summary probes.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Withdrawal

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## block_count_withdrawals -- PR-K124

    Return `len(block.withdrawals)` as a u64, directly from the
    body RLP. Useful for receipt bookkeeping, withdrawal-array
    sizing, and as a pre-flight before per-withdrawal processing
    via PR-K78 `process_withdrawals_block`.

    PR-K85 `block_withdrawals_total` already does the per-withdrawal
    sum across the same list; K124 is the narrow counter when only
    the cardinality matters.

    Composes:
      - PR-K83 `block_body_decode`    -- split body
      - PR-K47 `rlp_list_count_items` -- N

    Status decade encoding (floor(status/100) identifies failing
    step):

      0          : success
      1          : `block_body_decode` failed
      101        : `rlp_list_count_items` on withdrawals failed

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : u64 out ptr (count)
      ra (input)  : return
      a0 (output) : composite status

    Uses 48 bytes of `.data` scratch (`bcw_struct`) plus K83/K47's
    own scratch slots. -/
/-! ## block_count_transactions -- PR-K125

    Return `len(block.transactions)` as a u64, directly from the
    body RLP. Useful for receipt bookkeeping, per-tx iteration
    sizing, and as a pre-flight before per-tx processing.

    PR-K86 `block_summary` already extracts tx_count alongside
    withdrawal_total and ommers_empty; K125 is the narrow counter
    when only the tx-count cardinality matters (mirror of PR-K124
    `block_count_withdrawals`).

    Composes:
      - PR-K83 `block_body_decode`    -- split body
      - PR-K47 `rlp_list_count_items` -- N

    Status decade encoding (floor(status/100) identifies failing
    step):

      0          : success
      1          : `block_body_decode` failed
      101        : `rlp_list_count_items` on withdrawals failed
    Status decade encoding:
      0          : success
      1          : `block_body_decode` failed
      101        : `rlp_list_count_items` on txs failed

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : u64 out ptr (count)
      ra (input)  : return
      a0 (output) : composite status

    Uses 48 bytes of `.data` scratch (`bcw_struct`) plus K83/K47's
    own scratch slots. -/
def blockCountWithdrawalsFunction : String :=
  "block_count_withdrawals:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s1, a1                   # body_rlp_len\n" ++
  "  mv s2, a2                   # count out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Step 1: block_body_decode -> bcw_struct.\n" ++
  "  la a2, bcw_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbcw_body_fail\n" ++
  "  # Step 2: rlp_list_count_items on withdrawals sub-list.\n" ++
  "  la t0, bcw_struct\n" ++
  "  ld t1, 32(t0)               # withdrawals_offset\n" ++
  "  ld t2, 40(t0)               # withdrawals_length\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  beqz a0, .Lbcw_ret\n" ++
  "  li a0, 101\n" ++
  "  j .Lbcw_ret\n" ++
  ".Lbcw_body_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbcw_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_count_withdrawals`: probe BuildUnit. Reads
    (body_len, body_bytes), writes (status, withdrawal_count) to
    OUTPUT (16 bytes). -/
def ziskBlockCountWithdrawalsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # body_len\n" ++
  "  addi a0, a3, 16             # body ptr\n" ++
  "  li a2, 0xa0010008           # count out\n" ++
  "  jal ra, block_count_withdrawals\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbcw_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockCountWithdrawalsFunction ++ "\n" ++
  ".Lbcw_pdone:"

def ziskBlockCountWithdrawalsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bcw_struct:\n" ++
  "  .zero 48"

def ziskBlockCountWithdrawalsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockCountWithdrawalsPrologue
  dataAsm     := ziskBlockCountWithdrawalsDataSection
}

/-! ## block_summary -- PR-K86

    One-pass block body audit. Decode the body, then extract:

      tx_count                u64   -- count of transactions
      withdrawal_total_gwei   u64   -- sum of withdrawal amounts
      ommers_empty            u64   -- 1 if ommers is empty, else 0

    Useful for receipt / consensus-layer cross-checks and as a
    convenient single-call entry point for callers that need
    multiple block-level summaries.

    Composes:
      - PR-K83 `block_body_decode`       -- split body
      - PR-K47 `rlp_list_count_items`    -- count txs
      - PR-K65 `withdrawals_sum_amounts` -- sum withdrawal amounts
      - Inline check                     -- ommers length == 1, byte == 0xc0

    Output struct (24 bytes):
      0..  8  tx_count
      8.. 16  withdrawal_total_gwei
     16.. 24  ommers_empty (0 or 1)

    Status encoding:
      0          : success
      1          : block_body_decode failed
      101..102   : rlp_list_count_items on txs failed (1=parse fail)
                   -- only code 101 is observed in practice
      201..202   : withdrawals_sum_amounts failed (1=parse / 2=overflow)

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : 24-byte output struct ptr
      ra (input)  : return
      a0 (output) : composite status code.

    Uses 48 bytes of `.data` scratch (`bsum_struct`). -/
def blockSummaryFunction : String :=
  "block_summary:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s1, a1                   # body_len\n" ++
  "  mv s2, a2                   # output struct ptr\n" ++
  "  # Step 1: block_body_decode -> bsum_struct.\n" ++
  "  la a2, bsum_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbsum_body_fail\n" ++
  "  # Step 2: tx_count = rlp_list_count_items(txs sub-list).\n" ++
  "  la t0, bsum_struct\n" ++
  "  ld t1, 0(t0)                # txs_offset\n" ++
  "  ld t2, 8(t0)                # txs_length\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  addi a2, s2, 0              # out[0..8] = tx_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  beqz a0, .Lbsum_s3\n" ++
  "  li t3, 100\n" ++
  "  add a0, a0, t3              # 1 -> 101\n" ++
  "  j .Lbsum_ret\n" ++
  ".Lbsum_s3:\n" ++
  "  # Step 3: withdrawals_sum_amounts -> out[8..16].\n" ++
  "  la t0, bsum_struct\n" ++
  "  ld t1, 32(t0)               # withdrawals_offset\n" ++
  "  ld t2, 40(t0)               # withdrawals_length\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  addi a2, s2, 8              # out[8..16] = total\n" ++
  "  jal ra, withdrawals_sum_amounts\n" ++
  "  beqz a0, .Lbsum_s4\n" ++
  "  li t3, 200\n" ++
  "  add a0, a0, t3              # 1 -> 201, 2 -> 202\n" ++
  "  j .Lbsum_ret\n" ++
  ".Lbsum_s4:\n" ++
  "  # Step 4: ommers_empty check -> out[16..24] (0 or 1).\n" ++
  "  la t0, bsum_struct\n" ++
  "  ld t1, 24(t0)               # ommers_length\n" ++
  "  li t2, 1\n" ++
  "  bne t1, t2, .Lbsum_ommers_not_empty\n" ++
  "  ld t3, 16(t0)               # ommers_offset\n" ++
  "  add t3, s0, t3\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  li t5, 0xc0\n" ++
  "  bne t4, t5, .Lbsum_ommers_not_empty\n" ++
  "  li t6, 1\n" ++
  "  sd t6, 16(s2)\n" ++
  "  j .Lbsum_ok\n" ++
  ".Lbsum_ommers_not_empty:\n" ++
  "  sd zero, 16(s2)\n" ++
  ".Lbsum_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbsum_ret\n" ++
  ".Lbsum_body_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbsum_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_summary`: probe BuildUnit. Reads (body_len,
    body_bytes), writes (status, tx_count, wd_total, ommers_empty)
    to OUTPUT (32 bytes total). -/
def ziskBlockSummaryPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # body_len\n" ++
  "  addi a0, a3, 16             # body ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  sd zero,  0(a2)\n" ++
  "  sd zero,  8(a2)\n" ++
  "  sd zero, 16(a2)\n" ++
  "  jal ra, block_summary\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbsum_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  withdrawalsSumAmountsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockSummaryFunction ++ "\n" ++
  ".Lbsum_pdone:"

def ziskBlockSummaryDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wd_offset:\n" ++
  "  .zero 8\n" ++
  "wd_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wsa_count:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_offset:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_length:\n" ++
  "  .zero 8\n" ++
  "wsa_struct:\n" ++
  "  .zero 48\n" ++
  ".balign 8\n" ++
  "bsum_struct:\n" ++
  "  .zero 48"

def ziskBlockSummaryProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockSummaryPrologue
  dataAsm     := ziskBlockSummaryDataSection
}

end EvmAsm.Codegen
