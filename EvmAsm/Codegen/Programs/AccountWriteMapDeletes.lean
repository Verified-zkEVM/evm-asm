/-
  EvmAsm.Codegen.Programs.AccountWriteMapDeletes

  Transaction-boundary deletion and tombstone reads extracted from
  `AccountWriteMap.lean` so the account-write map stays below the file-size cap.
  The three functions are a cohesive phase boundary: deferred SELFDESTRUCT
  entries become Present-None only at finalization, and readers distinguish that
  state from the same-transaction destroyed-address table.
-/

import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## `account_writes_commit_pending`

    Finalize the transaction-local account-write state before the builder walk.
    The map is already the sole execution-state journal: `account_writes_apply_deletes`
    materializes deferred SELFDESTRUCT state in that map, then the transaction-local
    created/delete sets are cleared for the next transaction.  The created set itself
    remains live until this point because tombstone provenance is transaction-scoped.

    No AccountState pending/durable merge is performed here.  A nonzero return is a
    latched arena failure and is consumed by the caller as a rejection. -/
def accountWritesCommitPending_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.account_writes_apply_deletes (GuestAddrs.account_writes_commit_pending + 8)),
    .BNE .x10 .x0 (36 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.account_state_created_count (GuestAddrs.account_writes_commit_pending + 16)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_state_created_count (GuestAddrs.account_writes_commit_pending + 16)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.account_state_delete_count (GuestAddrs.account_writes_commit_pending + 28)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_state_delete_count (GuestAddrs.account_writes_commit_pending + 28)),
    .SD .x5 .x0 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_overflow (GuestAddrs.account_writes_commit_pending + 48)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_overflow (GuestAddrs.account_writes_commit_pending + 48)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountWritesCommitPending_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWritesCommitPending_relocs : RelocTable :=
  [ (2, .jal .x1 "account_writes_apply_deletes"),
    (4, .la .x5 "account_state_created_count"),
    (7, .la .x5 "account_state_delete_count"),
    (12, .la .x5 "account_writes_overflow") ]

def accountWritesCommitPendingFunction : String :=
  "account_writes_commit_pending:\n" ++ emitProgramR accountWritesCommitPending_prog accountWritesCommitPending_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWritesCommitPending_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWritesCommitPendingFunction_eq_prog :
    accountWritesCommitPendingFunction = "account_writes_commit_pending:\n" ++ emitProgramR accountWritesCommitPending_prog accountWritesCommitPending_relocs := rfl

#guard accountWritesCommitPendingFunction.startsWith "account_writes_commit_pending:\n"
#guard accountWritesCommitPending_prog.length = 20
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
def accountWritesIsAbsent_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_is_absent + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tx_account_writes_count (GuestAddrs.account_writes_is_absent + 0)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (2031 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_writes_is_absent + 116) (GuestAddrs.account_writes_is_absent + 28)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x29 .x7 .x29,
    .LI .x30 (20 : Word),
    .MV .x31 .x29,
    .MV .x5 .x10,
    .BEQ .x30 .x0 (40 : BitVec 13),
    .LBU .x11 .x31 (0 : BitVec 12),
    .LBU .x12 .x5 (0 : BitVec 12),
    .BNE .x11 .x12 (20 : BitVec 13),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .LD .x5 .x29 (112 : BitVec 12),
    .ANDI .x5 .x5 (8 : BitVec 12),
    .BEQ .x5 .x0 (brOff (GuestAddrs.account_writes_is_absent + 228) (GuestAddrs.account_writes_is_absent + 100)),
    .LD .x5 .x29 (72 : BitVec 12),
    .BEQ .x5 .x0 (brOff (GuestAddrs.account_writes_is_absent + 236) (GuestAddrs.account_writes_is_absent + 108)),
    .JAL .x0 (jalOff (GuestAddrs.account_writes_is_absent + 228) (GuestAddrs.account_writes_is_absent + 112)),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.account_writes_is_absent + 116)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.account_writes_is_absent + 116)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (1975 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .LI .x28 (0 : Word),
    .BGEU .x28 .x6 (brOff (GuestAddrs.account_writes_is_absent + 228) (GuestAddrs.account_writes_is_absent + 144)),
    .SLLI .x29 .x28 (7 : BitVec 6),
    .ADD .x29 .x7 .x29,
    .LI .x30 (20 : Word),
    .MV .x31 .x29,
    .MV .x5 .x10,
    .BEQ .x30 .x0 (40 : BitVec 13),
    .LBU .x11 .x31 (0 : BitVec 12),
    .LBU .x12 .x5 (0 : BitVec 12),
    .BNE .x11 .x12 (20 : BitVec 13),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .LD .x5 .x29 (112 : BitVec 12),
    .ANDI .x5 .x5 (8 : BitVec 12),
    .BEQ .x5 .x0 (12 : BitVec 13),
    .LD .x5 .x29 (72 : BitVec 12),
    .BEQ .x5 .x0 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountWritesIsAbsent_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountWritesIsAbsent_relocs : RelocTable :=
  [ (0, .la .x5 "tx_account_writes_count"),
    (29, .la .x5 "account_writes_count") ]

def accountWritesIsAbsentFunction : String :=
  "account_writes_is_absent:\n" ++ emitProgramR accountWritesIsAbsent_prog accountWritesIsAbsent_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountWritesIsAbsent_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountWritesIsAbsentFunction_eq_prog :
    accountWritesIsAbsentFunction = "account_writes_is_absent:\n" ++ emitProgramR accountWritesIsAbsent_prog accountWritesIsAbsent_relocs := rfl

#guard accountWritesIsAbsentFunction.startsWith "account_writes_is_absent:\n"
#guard accountWritesIsAbsent_prog.length = 61
end EvmAsm.Codegen
