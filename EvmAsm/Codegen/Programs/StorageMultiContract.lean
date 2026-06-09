/-
  EvmAsm.Codegen.Programs.StorageMultiContract

  `zisk_storage_multicontract` — positive verification that the persistent
  storage log is keyed PER-CONTRACT on `env.ADDRESS` (beads .61.6.7 / .61.6.7.1,
  PRs #8546/#8547/#8548): a frame must read its OWN slot and must NOT read a
  different contract's slot of the same key.

  A self-contained `tinyInterpRegistry` dispatcher (plain STOP — no frame
  helpers). The `_start` runs at depth 0 with `env.ADDRESS = A (0xAA)` and
  PRE-SEEDS the persistent storage log (0xa0630000) with two entries that
  simulate prior writes by two different contracts:

    log[0] = (addrHash = B 0xBB, slotKey = 7, current = 0x99)   — contract B's slot 7
    log[1] = (addrHash = A 0xAA, slotKey = 8, current = 0x77)   — contract A's slot 8

  then runs bytecode (env.ADDRESS = A throughout):

    PUSH1 7; SLOAD; PUSH1 0; SSTORE;   -- A reads slot 7  -> isolated 0  -> store to slot 0
    PUSH1 8; SLOAD; PUSH1 1; SSTORE;   -- A reads slot 8  -> its own 0x77 -> store to slot 1
    STOP

  With the per-contract keying, A's SLOAD of slot 7 SKIPS contract B's entry
  (addrHash mismatch) and returns 0; A's SLOAD of slot 8 matches its own entry
  and returns 0x77. A bug that ignored addrHash would read B's 0x99 for slot 7.

  The halt-time dedup-and-emit (keyed on slotKey, last-write-wins, cap 3) surfaces
  the three written slots; the check asserts:
    slot for key 0 has value 0      — ISOLATION (A did not read B's slot 7)
    slot for key 1 has value 0x77   — POSITIVE  (A read its own slot 8)
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmRegistry
import EvmAsm.Codegen.Programs.EvmBasic

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def storageMultiContractPrologue : String :=
  "  la sp, lp64_sp_top\n" ++
  "  la x13, evm_memory\n" ++
  "  la x20, evm_env\n" ++
  "  la x12, evm_stack_top\n" ++
  "  la x10, sm_code\n" ++
  "  la x21, sm_code\n" ++
  "  li t0, 1000000\n  sd t0, 568(x20)\n" ++       -- gasRemaining
  "  li t0, 13\n  sd t0, 496(x20)\n" ++            -- codeSize (13-byte program)
  -- env.ADDRESS (env+0) = contract A (limb0 = 0xAA).
  "  li t0, 0xAA\n  sd t0, 0(x20)\n" ++
  "  sd x0, 8(x20); sd x0, 16(x20); sd x0, 24(x20)\n" ++
  -- log-state cells (checkpoint / transient / event / memsize), all 0.
  "  sd x0, 456(x20); sd x0, 464(x20)\n" ++
  "  sd x0, 472(x20); sd x0, 480(x20); sd x0, 488(x20)\n" ++
  -- pre-seed the persistent log with two prior cross-contract writes.
  "  li t1, 0xa0630000\n" ++
  -- log[0] = (addrHash B 0xBB, slotKey 7, original 0, current 0x99).
  "  li t0, 0xBB\n  sd t0, 0(t1); sd x0, 8(t1); sd x0, 16(t1); sd x0, 24(t1)\n" ++
  "  li t0, 7\n  sd t0, 32(t1); sd x0, 40(t1); sd x0, 48(t1); sd x0, 56(t1)\n" ++
  "  sd x0, 64(t1); sd x0, 72(t1); sd x0, 80(t1); sd x0, 88(t1)\n" ++
  "  li t0, 0x99\n  sd t0, 96(t1); sd x0, 104(t1); sd x0, 112(t1); sd x0, 120(t1)\n" ++
  -- log[1] = (addrHash A 0xAA, slotKey 8, original 0, current 0x77).
  "  addi t1, t1, 128\n" ++
  "  li t0, 0xAA\n  sd t0, 0(t1); sd x0, 8(t1); sd x0, 16(t1); sd x0, 24(t1)\n" ++
  "  li t0, 8\n  sd t0, 32(t1); sd x0, 40(t1); sd x0, 48(t1); sd x0, 56(t1)\n" ++
  "  sd x0, 64(t1); sd x0, 72(t1); sd x0, 80(t1); sd x0, 88(t1)\n" ++
  "  li t0, 0x77\n  sd t0, 96(t1); sd x0, 104(t1); sd x0, 112(t1); sd x0, 120(t1)\n" ++
  "  li t0, 2\n  sd t0, 448(x20)\n" ++             -- persistentLogLength = 2
  "  j .dispatch_loop\n" ++
  emitRuntimeDispatcherLoop

def storageMultiContractData : String :=
  emitRuntimeDispatcherDataSection tinyInterpRegistry ++ "\n" ++
  ".balign 8\n" ++
  -- PUSH1 7; SLOAD; PUSH1 0; SSTORE; PUSH1 8; SLOAD; PUSH1 1; SSTORE; STOP
  "sm_code:\n  .byte 0x60, 0x07, 0x54, 0x60, 0x00, 0x55, 0x60, 0x08, 0x54, 0x60, 0x01, 0x55, 0x00\n" ++
  ".balign 8\n" ++
  -- Non-zero tail pad (ziskemu zeroes the final .data bytes; keep STOP intact).
  "sm_tail_pad:\n  .byte 0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef\n"

def storageMultiContractUnit : BuildUnit := {
  body        := []
  prologueAsm := storageMultiContractPrologue
  epilogueAsm := emitDispatcherEpilogue tinyInterpRegistry evmAddEpilogue
  dataAsm     := storageMultiContractData
}

end EvmAsm.Codegen
