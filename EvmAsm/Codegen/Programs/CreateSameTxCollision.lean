/-
  EvmAsm.Codegen.Programs.CreateSameTxCollision

  Shared CREATE/CREATE2 same-transaction collision scan.
-/

namespace EvmAsm.Codegen

/-- Scan the live non-storage effect log for the latest effect on the derived
    CREATE/CREATE2 address. If the latest post nonce is nonzero, EIP-684 treats
    the next CREATE-family operation to that address as a collision even though
    the account was absent from pre-state.

    EIP-6780 same-transaction SELFDESTRUCTs need one extra live-state check:
    a contract queued in `evm_selfdestruct_destroyed_table` is still unavailable
    for another CREATE/CREATE2 during the transaction, even if the latest
    non-storage effect has post nonce zero. -/
def createSameTxCollisionScanAsm (hasSalt : Bool) : String :=
  "  la t0, exec_nonstorage_effect_count\n" ++
  "  ld t1, 0(t0)\n" ++
  "  la t2, exec_nonstorage_effect_log\n" ++
  "  li t6, 0\n" ++
  ".Lcr_same_tx_col_loop_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
  "  beqz t1, .Lcr_same_tx_col_done_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
  "  mv t3, t2\n" ++
  "  la t4, create_address_be\n" ++
  "  li t5, 20\n" ++
  ".Lcr_same_tx_col_cmp_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
  "  beqz t5, .Lcr_same_tx_col_match_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
  "  lbu x18, 0(t3)\n" ++
  "  lbu x19, 0(t4)\n" ++
  "  bne x18, x19, .Lcr_same_tx_col_next_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lcr_same_tx_col_cmp_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
  ".Lcr_same_tx_col_match_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
  "  ld t6, 104(t2)\n" ++
  ".Lcr_same_tx_col_next_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
  "  addi t2, t2, 112\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lcr_same_tx_col_loop_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
  ".Lcr_same_tx_col_done_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
  "  bnez t6, .Lcr_collision_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
  "  la t0, evm_selfdestruct_destroyed_overflow\n" ++
  "  ld t0, 0(t0)\n" ++
  "  bnez t0, .Lcr_same_tx_sd_done_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
  "  la t0, evm_selfdestruct_destroyed_count\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .Lcr_same_tx_sd_done_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
  "  la t2, evm_selfdestruct_destroyed_table\n" ++
  ".Lcr_same_tx_sd_scan_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
  "  mv t3, t2\n" ++
  "  la t4, create_address_be\n" ++
  "  li t5, 20\n" ++
  ".Lcr_same_tx_sd_cmp_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
  "  beqz t5, .Lcr_collision_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
  "  lbu x18, 0(t3)\n" ++
  "  lbu x19, 0(t4)\n" ++
  "  bne x18, x19, .Lcr_same_tx_sd_next_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lcr_same_tx_sd_cmp_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
  ".Lcr_same_tx_sd_next_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
  "  addi t2, t2, 32\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .Lcr_same_tx_sd_scan_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
  ".Lcr_same_tx_sd_done_" ++ (if hasSalt then "f5" else "f0") ++ ":\n"

end EvmAsm.Codegen
