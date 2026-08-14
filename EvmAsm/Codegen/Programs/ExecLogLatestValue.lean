/-
  EvmAsm.Codegen.Programs.ExecLogLatestValue

  `exec_log_latest_value` (bead fhsxz.2.4.2.57.11.6.3.1 — foundation for cross-tx
  storage threading) — return the latest committed `current` value a given slot
  `(addrHash, slotKey)` holds in the execution storage log.

  The storage exec-log is append-per-write: one 128-byte entry per SSTORE (and per
  preload/seed), `addrHash@0 / slotKey@32 / original@64 / current@96`. Transactions
  execute in order and each per-tx dispatch RESETS `env.persistentLogLength` to its
  own preload count (Dispatch.lean callable-setup `.preload_expand_loop`), so the
  log does NOT accumulate across the `.Lbv_mtx_*` per-tx dispatches. To thread one
  transaction's committed storage into the next transaction's preload, the multi-tx
  loop must SNAPSHOT the just-finished dispatch's committed values from the LIVE log
  before the next setup wipes it. This leaf is the per-slot read of that snapshot.

  Because matching entries appear in write order, the LAST entry matching
  `(addrHash, slotKey)` carries that slot's end-of-block-so-far committed value. A
  slot with no matching entry was never touched (the caller falls back to the
  block-pre / header-state value).

  This is a pure scan over prepared inputs — soundness-neutral on its own (the
  probe exercises it; wiring into the per-tx preload is .6.3.2). It mirrors the
  match idiom of `exec_log_slot_tuples` (#8595) but keeps only the last `current`.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## exec_log_latest_value
    a0 = addrHash ptr (32B)   a1 = slotKey ptr (32B)
    a2 = exec-log base (128B entries)   a3 = entry count
    a4 = out value ptr (32B; written with the latest matching `current` on a hit)
    a0 (output) = 1 if a matching entry was found (out holds its committed value),
                  0 if the slot was never touched (out left unchanged).
    Leaf: uses only t-registers + the argument registers; no stack frame. -/
def execLogLatestValue_prog : Program :=
  [ .LI .x31 (0 : Word),
    .LI .x5 (0 : Word),
    .BEQ .x5 .x13 (152 : BitVec 13),
    .SLLI .x6 .x5 (7 : BitVec 6),
    .ADD .x7 .x12 .x6,
    .LD .x28 .x7 (0 : BitVec 12),
    .LD .x29 .x10 (0 : BitVec 12),
    .BNE .x28 .x29 (124 : BitVec 13),
    .LD .x28 .x7 (8 : BitVec 12),
    .LD .x29 .x10 (8 : BitVec 12),
    .BNE .x28 .x29 (112 : BitVec 13),
    .LD .x28 .x7 (16 : BitVec 12),
    .LD .x29 .x10 (16 : BitVec 12),
    .BNE .x28 .x29 (100 : BitVec 13),
    .LD .x28 .x7 (24 : BitVec 12),
    .LD .x29 .x10 (24 : BitVec 12),
    .BNE .x28 .x29 (88 : BitVec 13),
    .LD .x28 .x7 (32 : BitVec 12),
    .LD .x29 .x11 (0 : BitVec 12),
    .BNE .x28 .x29 (76 : BitVec 13),
    .LD .x28 .x7 (40 : BitVec 12),
    .LD .x29 .x11 (8 : BitVec 12),
    .BNE .x28 .x29 (64 : BitVec 13),
    .LD .x28 .x7 (48 : BitVec 12),
    .LD .x29 .x11 (16 : BitVec 12),
    .BNE .x28 .x29 (52 : BitVec 13),
    .LD .x28 .x7 (56 : BitVec 12),
    .LD .x29 .x11 (24 : BitVec 12),
    .BNE .x28 .x29 (40 : BitVec 13),
    .LD .x28 .x7 (96 : BitVec 12),
    .SD .x14 .x28 (0 : BitVec 12),
    .LD .x28 .x7 (104 : BitVec 12),
    .SD .x14 .x28 (8 : BitVec 12),
    .LD .x28 .x7 (112 : BitVec 12),
    .SD .x14 .x28 (16 : BitVec 12),
    .LD .x28 .x7 (120 : BitVec 12),
    .SD .x14 .x28 (24 : BitVec 12),
    .LI .x31 (1 : Word),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-148 : BitVec 21),
    .MV .x10 .x31,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def execLogLatestValueFunction : String :=
  "exec_log_latest_value:\n" ++ emitProgram execLogLatestValue_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `execLogLatestValue_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`).
    #11178: unlinked from `stateless_guest` (0 refs); probe-only. -/
theorem execLogLatestValueFunction_eq_prog :
    execLogLatestValueFunction = "exec_log_latest_value:\n" ++ emitProgram execLogLatestValue_prog := rfl

#guard execLogLatestValueFunction.startsWith "exec_log_latest_value:\n"
#guard execLogLatestValue_prog.length = 42
/-- `zisk_exec_log_latest_value`: focused probe (routine not in guest, #11178).
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : entry count
      bytes 16..48 : addrHash (32B)
      bytes 48..80 : slotKey (32B)
      bytes 80..   : exec-log (count × 128B)
    Output: bytes 0..8 = found flag (1/0); bytes 8..40 = committed value (32B) on a hit. -/
def ziskExecLogLatestValuePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  ld a3, 8(t6)                # entry count\n" ++
  "  addi a0, t6, 16             # addrHash ptr\n" ++
  "  addi a1, t6, 48             # slotKey ptr\n" ++
  "  addi a2, t6, 80             # exec-log base\n" ++
  "  li a4, 0xa0010008           # out value buffer = OUTPUT + 8\n" ++
  "  jal ra, exec_log_latest_value\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # found flag\n" ++
  "  j .Lelv_pdone\n" ++
  execLogLatestValueFunction ++ "\n" ++
  ".Lelv_pdone:"


end EvmAsm.Codegen
