/-
  EvmAsm.Codegen.Programs.AccountWriteMapDeletes

  Transaction-boundary deletion and tombstone reads extracted from
  `AccountWriteMap.lean` so the account-write map stays below the file-size cap.
  The three functions are a cohesive phase boundary: deferred SELFDESTRUCT
  entries become Present-None only at finalization, and readers distinguish that
  state from the same-transaction destroyed-address table.
-/

namespace EvmAsm.Codegen

/-! ## `account_writes_commit_pending`

    Finalize the transaction-local account-write state before the builder walk.
    The map is already the sole execution-state journal: `account_writes_apply_deletes`
    materializes deferred SELFDESTRUCT state in that map, then the transaction-local
    created/delete sets are cleared for the next transaction.  The created set itself
    remains live until this point because tombstone provenance is transaction-scoped.

    No AccountState pending/durable merge is performed here.  A nonzero return is a
    latched arena failure and is consumed by the caller as a rejection. -/
def accountWritesCommitPendingFunction : String :=
  "account_writes_commit_pending:\n" ++
  "  addi sp, sp, -16; sd ra, 0(sp)\n" ++
  "  jal ra, account_writes_apply_deletes; bnez a0, .Lawcp_over\n" ++
  "  la t0, account_state_created_count; sd zero, 0(t0)\n" ++
  "  la t0, account_state_delete_count; sd zero, 0(t0)\n" ++
  "  li a0, 0; j .Lawcp_ret\n" ++
  ".Lawcp_over:\n" ++
  "  la t0, account_writes_overflow; li t1, 1; sd t1, 0(t0); li a0, 1\n" ++
  ".Lawcp_ret:\n" ++
  "  ld ra, 0(sp); addi sp, sp, 16; ret\n"

/-! ## `account_writes_is_absent`

    Three-state read of `account_writes` matching
    `get_account_optional` (state_tracker.py:199-203), GH #11328 / PR #11453:

    | map state                         | a0 out | meaning                                      |
    |-----------------------------------|--------|----------------------------------------------|
    | key **missing**                   | 0      | unknown here — caller falls through          |
    | key present, `optionalState@72=0` | 1      | **destroyed** (Present-None tombstone)       |
    | key present, `optionalState@72=1` | 0      | Present Account (or STATE bit unset → not None) |

    Scans tx map first, then block-cumulative.  Only a **present** row with
    STATE valid and `optionalState@72 = 0` returns 1.  Missing row and Present
    Account both return 0 — they are **not** conflated with Present-None.

    **Same-tx completeness (coord Q on #11453):** Present-None is stamped by
    `account_writes_apply_deletes` at the **tx boundary** (spec
    `destroy_account` after `accounts_to_delete`).  Mid-tx create+SD still
    leaves an empty-code account until finalize (EIP-1052 EMPTY_CODE_HASH,
    not 0).  That mid-tx flag is still `evm_selfdestruct_destroyed_table`; it
    is **not** the same fact as Present-None (0 after finalize).  Table stays
    until mid-tx empty-code is carried by Present Account without a side list.
    Pinned Python authority (not inferred from this Lean mirror) is
    `vm/__init__.py:184,234`, `vm/interpreter.py:135,151,349`,
    `vm/instructions/system.py:691-693`, and `fork.py:1201-1202`.
    Lean mirror (not authority): this read is valid only after the boundary
    materialization above.  Collapsing the phases makes EXTCODEHASH/availability
    observe deletion too early, can admit a same-tx CREATE collision, or mischarge
    NEW_ACCOUNT; skipping the boundary path leaves deleted state visible next tx.

    a0 = address ptr (20 B BE).  Clobbers t0-t6 and a1/a2. -/
def accountWritesIsAbsentFunction : String :=
  "account_writes_is_absent:\n" ++
  "  la t0, tx_account_writes_count; ld t1, 0(t0); li t2, 0xbf780000; li t3, 0\n" ++
  ".Lawis_tx_scan:\n" ++
  "  bgeu t3, t1, .Lawis_block; slli t4, t3, 7; add t4, t2, t4; li t5, 20; mv t6, t4; mv t0, a0\n" ++
  ".Lawis_tx_cmp:\n" ++
  "  beqz t5, .Lawis_tx_hit; lbu a1, 0(t6); lbu a2, 0(t0); bne a1, a2, .Lawis_tx_next; addi t6, t6, 1; addi t0, t0, 1; addi t5, t5, -1; j .Lawis_tx_cmp\n" ++
  ".Lawis_tx_next:\n" ++
  "  addi t3, t3, 1; j .Lawis_tx_scan\n" ++
  ".Lawis_tx_hit:\n" ++
  "  ld t0, 112(t4); andi t0, t0, 8; beqz t0, .Lawis_no; ld t0, 72(t4); beqz t0, .Lawis_yes; j .Lawis_no\n" ++
  ".Lawis_block:\n" ++
  "  la t0, account_writes_count; ld t1, 0(t0); li t2, 0xbdb80000; li t3, 0\n" ++
  ".Lawis_blk_scan:\n" ++
  "  bgeu t3, t1, .Lawis_no; slli t4, t3, 7; add t4, t2, t4; li t5, 20; mv t6, t4; mv t0, a0\n" ++
  ".Lawis_blk_cmp:\n" ++
  "  beqz t5, .Lawis_blk_hit; lbu a1, 0(t6); lbu a2, 0(t0); bne a1, a2, .Lawis_blk_next; addi t6, t6, 1; addi t0, t0, 1; addi t5, t5, -1; j .Lawis_blk_cmp\n" ++
  ".Lawis_blk_next:\n" ++
  "  addi t3, t3, 1; j .Lawis_blk_scan\n" ++
  ".Lawis_blk_hit:\n" ++
  "  ld t0, 112(t4); andi t0, t0, 8; beqz t0, .Lawis_no; ld t0, 72(t4); beqz t0, .Lawis_yes\n" ++
  ".Lawis_no:\n" ++
  "  li a0, 0; ret\n" ++
  ".Lawis_yes:\n" ++
  "  li a0, 1; ret\n"

end EvmAsm.Codegen
