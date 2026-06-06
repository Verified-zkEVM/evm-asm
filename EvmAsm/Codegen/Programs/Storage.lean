/-
  EvmAsm.Codegen.Programs.Storage

  M24 Option A storage handlers (SLOAD, SSTORE, TLOAD, TSTORE).
  Supersedes M22's `(slotKey, value)` 64-byte-entry slot-table
  approach with the Option A spec from issue #7130: a 128-byte
  per-entry append-only log keyed by `(addrHash, slotKey)` with
  separate `original` and `current` value cells.

  Two logs live in `STATE_TRACKER_AREA`:
    0xa0630000  persistent storage log (SLOAD / SSTORE)
    0xa0830000  transient  storage log (TLOAD / TSTORE)

  Each entry is 128 bytes, 8-byte aligned:
    +0..32   addrHash   (M24: always 0 — single-contract; multi-contract is M25)
    +32..64  slotKey    (EVM-stack byte order: 4 LE u64 limbs, low first)
    +64..96  original   (slot's pre-tx value; 0 for cold non-preloaded)
    +96..128 current    (most recent committed value during this tx)

  Log lengths live in env:
    env+448  persistentLogLengthOff  (live counter; SSTORE increments)
    env+456  persistentLogCheckpointOff  (set at prologue end; restored on REVERT)
    env+464  transientLogLengthOff  (live counter; TSTORE increments; reset on REVERT)

  ## Semantics

  **SLOAD (0x54)** — scan persistent log from end (last-write-
  wins); copy matching `current` to the stack-top slot; default
  zero on miss. Net stack delta = 0.

  **SSTORE (0x55)** — scan from end; append a new entry preserving
  the prior `original` on match (or 0 on miss). **Always appends**
  (never mutates existing entries) — this is what makes REVERT a
  single log-length truncation instead of a journal replay.
  Net stack delta = +64 (pops key + value).

  **TLOAD (0x5c)** — same shape as SLOAD against the transient log.

  **TSTORE (0x5d)** — append-only (no scan; transient storage has
  no gas refund logic, so we never need to read the prior
  `original`). Net stack delta = +64.

  ## Inline asm conventions

  Numeric local labels (`1:`, `1b`, `1f`, …) — unique-per-use,
  reusable across handlers without collision. Scratch registers
  x14–x19 are caller-saved per the dispatcher convention.

  ## Known limitations (documented in CODEGEN.md M24)

  - Single-contract only (`addrHash = 0`); multi-contract is M25.
  - Cold reads of non-preloaded slots return `original = 0`; real
    EVM reads from the witness MPT (M27).
  - 4 MiB per log = ~32K entries each — well past any test workload.
  - Inline asm, not verified bodies. Verified-loop bodies follow later.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Additional SSTORE gas after the dispatcher warm floor and storage-access
    helper have run.

    Inputs:
    - `x12`: stack pointer. `[x12+0..32]` is key, `[x12+32..64]` is new value.
    - `x18`: pointer to found log entry's original value (`entry+64`), or zero.
    - `x19`: storage-access status (`0` warm, `1` cold).

    Clobbers `x5`, `x6`, `x14`-`x17`. Jumps to `.exit_outofgas` if the
    additional debit cannot be paid. The static dispatch table already charged
    100 gas for SSTORE, and `evm_storage_access_charge_key` already charged the
    2000 cold delta, so this computes the remaining debit to match Amsterdam's
    `vm/instructions/storage.py`:
    - clean zero -> nonzero: +19900 warm, +20000 cold
    - clean nonzero update: +2800 warm, +2900 cold
    - dirty/noop branch: +0 warm, +100 cold
    Refund-counter updates are still handled separately by later gas work. -/
def sstoreValueTransitionGasAsm : String :=
  -- x14 = OR of the new value limbs. For a missing slot, original=current=0.
  "  mv x14, x0\n" ++
  "  ld x15, 32(x12)\n" ++
  "  or x14, x14, x15\n" ++
  "  ld x15, 40(x12)\n" ++
  "  or x14, x14, x15\n" ++
  "  ld x15, 48(x12)\n" ++
  "  or x14, x14, x15\n" ++
  "  ld x15, 56(x12)\n" ++
  "  or x14, x14, x15\n" ++
  "  beqz x18, .Lsstore_missing_slot\n" ++
  -- Found slot: x15 = original_or, x16 = original/current diff,
  -- x17 = current/new diff.
  "  mv x15, x0\n" ++
  "  mv x16, x0\n" ++
  "  mv x17, x0\n" ++
  "  ld x5, 0(x18)\n" ++
  "  or x15, x15, x5\n" ++
  "  ld x6, 32(x18)\n" ++
  "  xor x6, x5, x6\n" ++
  "  or x16, x16, x6\n" ++
  "  ld x5, 32(x18)\n" ++
  "  ld x6, 32(x12)\n" ++
  "  xor x6, x5, x6\n" ++
  "  or x17, x17, x6\n" ++
  "  ld x5, 8(x18)\n" ++
  "  or x15, x15, x5\n" ++
  "  ld x6, 40(x18)\n" ++
  "  xor x6, x5, x6\n" ++
  "  or x16, x16, x6\n" ++
  "  ld x5, 40(x18)\n" ++
  "  ld x6, 40(x12)\n" ++
  "  xor x6, x5, x6\n" ++
  "  or x17, x17, x6\n" ++
  "  ld x5, 16(x18)\n" ++
  "  or x15, x15, x5\n" ++
  "  ld x6, 48(x18)\n" ++
  "  xor x6, x5, x6\n" ++
  "  or x16, x16, x6\n" ++
  "  ld x5, 48(x18)\n" ++
  "  ld x6, 48(x12)\n" ++
  "  xor x6, x5, x6\n" ++
  "  or x17, x17, x6\n" ++
  "  ld x5, 24(x18)\n" ++
  "  or x15, x15, x5\n" ++
  "  ld x6, 56(x18)\n" ++
  "  xor x6, x5, x6\n" ++
  "  or x16, x16, x6\n" ++
  "  ld x5, 56(x18)\n" ++
  "  ld x6, 56(x12)\n" ++
  "  xor x6, x5, x6\n" ++
  "  or x17, x17, x6\n" ++
  "  bnez x16, .Lsstore_dirty_or_noop\n" ++
  "  beqz x17, .Lsstore_dirty_or_noop\n" ++
  "  beqz x15, .Lsstore_clean_zero\n" ++
  "  li x14, 2800\n" ++
  "  beqz x19, .Lsstore_charge_delta\n" ++
  "  li x14, 2900\n" ++
  "  j .Lsstore_charge_delta\n" ++
  ".Lsstore_clean_zero:\n" ++
  "  li x14, 19900\n" ++
  "  beqz x19, .Lsstore_charge_delta\n" ++
  "  li x14, 20000\n" ++
  "  j .Lsstore_charge_delta\n" ++
  ".Lsstore_missing_slot:\n" ++
  "  bnez x14, .Lsstore_missing_nonzero\n" ++
  "  beqz x19, .Lsstore_gas_done\n" ++
  "  li x14, 100\n" ++
  "  j .Lsstore_charge_delta\n" ++
  ".Lsstore_missing_nonzero:\n" ++
  "  li x14, 19900\n" ++
  "  beqz x19, .Lsstore_charge_delta\n" ++
  "  li x14, 20000\n" ++
  "  j .Lsstore_charge_delta\n" ++
  ".Lsstore_dirty_or_noop:\n" ++
  "  beqz x19, .Lsstore_gas_done\n" ++
  "  li x14, 100\n" ++
  ".Lsstore_charge_delta:\n" ++
  "  ld x15, 568(x20)\n" ++
  "  bltu x15, x14, .exit_outofgas\n" ++
  "  sub x15, x15, x14\n" ++
  "  sd x15, 568(x20)\n" ++
  ".Lsstore_gas_done:\n"

/-- M24 Option A storage handlers. -/
def storageHandlers : List OpcodeHandlerSpec :=
  [ -- M24 real SLOAD. Scan persistent log from end (last-write-
    -- wins); copy matching current to stack top; default 0 on miss.
    { label   := "h_SLOAD"
    , opcodes := [0x54]
    , preBody :=
        stackUnderflowGuardAsm 1 ++ "\n" ++
        -- EIP-2929 storage-key access gas. The dispatch table already
        -- charged SLOAD's 100 warm floor, so the helper only charges the
        -- 2000 cold delta on first touch. Preserve handler return address
        -- plus dispatcher PC / stack registers across the ABI a0/a1/a2 call.
        "  mv x17, x1\n" ++
        "  mv x18, x10\n" ++
        "  mv x19, x12\n" ++
        "  li a0, 0\n" ++
        "  mv a1, x12\n" ++
        "  addi a2, x20, 568\n" ++
        "  jal ra, evm_storage_access_charge_key\n" ++
        "  mv x14, a0\n" ++
        "  mv x1, x17\n" ++
        "  mv x10, x18\n" ++
        "  mv x12, x19\n" ++
        "  li x15, 2\n" ++
        "  beq x14, x15, .exit_outofgas\n" ++
        "  li x15, 3\n" ++
        "  beq x14, x15, .exit_outofgas\n" ++
        "  ld x15, 448(x20)\n" ++         -- x15 = persistent log_length
        "  beqz x15, 4f\n" ++             -- empty log → return 0
        "  li x14, 0xa0630000\n" ++       -- x14 = log base
        "  slli x16, x15, 7\n" ++         -- x16 = log_length * 128
        "  add x14, x14, x16\n" ++        -- x14 = past last entry
        "1:\n" ++                         -- scan loop iter
        "  addi x14, x14, -128\n" ++      -- x14 = &entry[i]
        -- Compare slotKey [x14+32..x14+64] vs stack key [x12+0..x12+32]
        "  ld x16, 32(x14)\n" ++
        "  ld x17, 0(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 40(x14)\n" ++
        "  ld x17, 8(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 48(x14)\n" ++
        "  ld x17, 16(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 56(x14)\n" ++
        "  ld x17, 24(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        -- Match: copy current [x14+96..x14+128] → [x12..x12+32]
        "  ld x16, 96(x14)\n" ++
        "  sd x16, 0(x12)\n" ++
        "  ld x16, 104(x14)\n" ++
        "  sd x16, 8(x12)\n" ++
        "  ld x16, 112(x14)\n" ++
        "  sd x16, 16(x12)\n" ++
        "  ld x16, 120(x14)\n" ++
        "  sd x16, 24(x12)\n" ++
        "  j 5f\n" ++
        "3:\n" ++                         -- no match this entry — advance
        "  addi x15, x15, -1\n" ++
        "  bnez x15, 1b\n" ++
        "4:\n" ++                         -- not found — write zeros
        "  sd x0, 0(x12)\n" ++
        "  sd x0, 8(x12)\n" ++
        "  sd x0, 16(x12)\n" ++
        "  sd x0, 24(x12)\n" ++
        "5:"
    , body    := []
    , tail    := .advanceAndRet 1 }
  , -- M24 real SSTORE. Scan persistent log from end; if found, save
    -- &found.original for the append step. Then ALWAYS append a new
    -- 128-byte entry at log[log_length] with (addrHash=0,
    -- slotKey=stack[0..32], original=found_or_zero,
    -- current=stack[32..64]). Increment log_length. Body's
    -- `ADDI x12, x12, 64` does the net -2 stack pop.
    --
    -- Append-only is load-bearing: REVERT rolls back via log-length
    -- truncation, which requires existing entries to be immutable.
    { label   := "h_SSTORE"
    , opcodes := [0x55]
    , preBody :=
        stackUnderflowGuardAsm 2 ++ "\n" ++
        -- EIP-2929 storage-key access gas. The dispatch table already
        -- charged SSTORE's 100 warm floor, so this helper only charges
        -- the 2000 cold delta on first key touch. Run before the scan /
        -- append path so out-of-gas cannot mutate the storage log.
        "  mv x17, x1\n" ++
        "  mv x18, x10\n" ++
        "  mv x19, x12\n" ++
        "  li a0, 0\n" ++
        "  mv a1, x12\n" ++
        "  addi a2, x20, 568\n" ++
        "  jal ra, evm_storage_access_charge_key\n" ++
        "  mv x14, a0\n" ++
        "  mv x1, x17\n" ++
        "  mv x10, x18\n" ++
        "  mv x12, x19\n" ++
        "  li x15, 2\n" ++
        "  beq x14, x15, .exit_outofgas\n" ++
        "  li x15, 3\n" ++
        "  beq x14, x15, .exit_outofgas\n" ++
        "  mv x19, x14\n" ++            -- x19 = access status (0 warm, 1 cold)
        "  li x18, 0\n" ++                -- x18 = "found.original ptr" (0 = not found)
        "  ld x15, 448(x20)\n" ++         -- x15 = log_length
        "  beqz x15, 2f\n" ++             -- empty log → skip scan, append with original=0
        "  li x14, 0xa0630000\n" ++       -- x14 = log base
        "  slli x16, x15, 7\n" ++
        "  add x14, x14, x16\n" ++        -- x14 = past last entry
        "1:\n" ++                         -- scan loop iter
        "  addi x14, x14, -128\n" ++
        "  ld x16, 32(x14)\n" ++
        "  ld x17, 0(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 40(x14)\n" ++
        "  ld x17, 8(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 48(x14)\n" ++
        "  ld x17, 16(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 56(x14)\n" ++
        "  ld x17, 24(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        -- Match: x18 = &found.original (= x14 + 64), break to append
        "  addi x18, x14, 64\n" ++
        "  j 2f\n" ++
        "3:\n" ++                         -- no match this entry — advance
        "  addi x15, x15, -1\n" ++
        "  bnez x15, 1b\n" ++
        "2:\n" ++                         -- append step
        sstoreValueTransitionGasAsm ++
        "  ld x15, 448(x20)\n" ++         -- reload current log_length
        "  li x14, 0xa0630000\n" ++
        "  slli x16, x15, 7\n" ++
        "  add x14, x14, x16\n" ++        -- x14 = &log[log_length] (append target)
        -- addrHash = 0 (32 bytes)
        "  sd x0, 0(x14)\n" ++
        "  sd x0, 8(x14)\n" ++
        "  sd x0, 16(x14)\n" ++
        "  sd x0, 24(x14)\n" ++
        -- slotKey from stack [x12+0..x12+32] → [x14+32..x14+64]
        "  ld x16, 0(x12)\n" ++
        "  sd x16, 32(x14)\n" ++
        "  ld x16, 8(x12)\n" ++
        "  sd x16, 40(x14)\n" ++
        "  ld x16, 16(x12)\n" ++
        "  sd x16, 48(x14)\n" ++
        "  ld x16, 24(x12)\n" ++
        "  sd x16, 56(x14)\n" ++
        -- original: copy from x18 if found; else write zeros
        "  beqz x18, 6f\n" ++
        "  ld x16, 0(x18)\n" ++
        "  sd x16, 64(x14)\n" ++
        "  ld x16, 8(x18)\n" ++
        "  sd x16, 72(x14)\n" ++
        "  ld x16, 16(x18)\n" ++
        "  sd x16, 80(x14)\n" ++
        "  ld x16, 24(x18)\n" ++
        "  sd x16, 88(x14)\n" ++
        "  j 7f\n" ++
        "6:\n" ++
        "  sd x0, 64(x14)\n" ++
        "  sd x0, 72(x14)\n" ++
        "  sd x0, 80(x14)\n" ++
        "  sd x0, 88(x14)\n" ++
        "7:\n" ++
        -- current from stack [x12+32..x12+64] → [x14+96..x14+128]
        "  ld x16, 32(x12)\n" ++
        "  sd x16, 96(x14)\n" ++
        "  ld x16, 40(x12)\n" ++
        "  sd x16, 104(x14)\n" ++
        "  ld x16, 48(x12)\n" ++
        "  sd x16, 112(x14)\n" ++
        "  ld x16, 56(x12)\n" ++
        "  sd x16, 120(x14)\n" ++
        -- increment log_length
        "  addi x15, x15, 1\n" ++
        "  sd x15, 448(x20)"
    , body    := ADDI .x12 .x12 (BitVec.ofNat 12 64)
    , tail    := .advanceAndRet 1 }
  , -- M24 real TLOAD. Scan transient log from end; copy matching
    -- current to stack top; default 0 on miss. Same shape as SLOAD
    -- but base 0xa0830000 and length env+464.
    { label   := "h_TLOAD"
    , opcodes := [0x5c]
    , preBody :=
        stackUnderflowGuardAsm 1 ++ "\n" ++
        "  ld x15, 464(x20)\n" ++         -- x15 = transient log_length
        "  beqz x15, 4f\n" ++
        "  li x14, 0xa0830000\n" ++       -- x14 = transient log base
        "  slli x16, x15, 7\n" ++
        "  add x14, x14, x16\n" ++
        "1:\n" ++
        "  addi x14, x14, -128\n" ++
        "  ld x16, 32(x14)\n" ++
        "  ld x17, 0(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 40(x14)\n" ++
        "  ld x17, 8(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 48(x14)\n" ++
        "  ld x17, 16(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 56(x14)\n" ++
        "  ld x17, 24(x12)\n" ++
        "  bne x16, x17, 3f\n" ++
        "  ld x16, 96(x14)\n" ++
        "  sd x16, 0(x12)\n" ++
        "  ld x16, 104(x14)\n" ++
        "  sd x16, 8(x12)\n" ++
        "  ld x16, 112(x14)\n" ++
        "  sd x16, 16(x12)\n" ++
        "  ld x16, 120(x14)\n" ++
        "  sd x16, 24(x12)\n" ++
        "  j 5f\n" ++
        "3:\n" ++
        "  addi x15, x15, -1\n" ++
        "  bnez x15, 1b\n" ++
        "4:\n" ++
        "  sd x0, 0(x12)\n" ++
        "  sd x0, 8(x12)\n" ++
        "  sd x0, 16(x12)\n" ++
        "  sd x0, 24(x12)\n" ++
        "5:"
    , body    := []
    , tail    := .advanceAndRet 1 }
  , -- M24 real TSTORE. Append-only (no scan). Transient storage has
    -- no gas refund logic, so we never need to track / preserve
    -- `original` — every TSTORE just appends a fresh entry. Subsequent
    -- TLOADs scan from end and find the most-recent (correct) value.
    { label   := "h_TSTORE"
    , opcodes := [0x5d]
    , preBody :=
        stackUnderflowGuardAsm 2 ++ "\n" ++
        "  ld x15, 464(x20)\n" ++         -- x15 = transient log_length
        "  li x14, 0xa0830000\n" ++
        "  slli x16, x15, 7\n" ++
        "  add x14, x14, x16\n" ++        -- x14 = append target
        -- addrHash = 0
        "  sd x0, 0(x14)\n" ++
        "  sd x0, 8(x14)\n" ++
        "  sd x0, 16(x14)\n" ++
        "  sd x0, 24(x14)\n" ++
        -- slotKey from stack
        "  ld x16, 0(x12)\n" ++
        "  sd x16, 32(x14)\n" ++
        "  ld x16, 8(x12)\n" ++
        "  sd x16, 40(x14)\n" ++
        "  ld x16, 16(x12)\n" ++
        "  sd x16, 48(x14)\n" ++
        "  ld x16, 24(x12)\n" ++
        "  sd x16, 56(x14)\n" ++
        -- original = 0 (unused for transient)
        "  sd x0, 64(x14)\n" ++
        "  sd x0, 72(x14)\n" ++
        "  sd x0, 80(x14)\n" ++
        "  sd x0, 88(x14)\n" ++
        -- current from stack [x12+32..x12+64]
        "  ld x16, 32(x12)\n" ++
        "  sd x16, 96(x14)\n" ++
        "  ld x16, 40(x12)\n" ++
        "  sd x16, 104(x14)\n" ++
        "  ld x16, 48(x12)\n" ++
        "  sd x16, 112(x14)\n" ++
        "  ld x16, 56(x12)\n" ++
        "  sd x16, 120(x14)\n" ++
        -- increment transient log_length
        "  addi x15, x15, 1\n" ++
        "  sd x15, 464(x20)"
    , body    := ADDI .x12 .x12 (BitVec.ofNat 12 64)
    , tail    := .advanceAndRet 1 } ]

end EvmAsm.Codegen
