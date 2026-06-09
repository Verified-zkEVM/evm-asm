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

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## exec_log_latest_value
    a0 = addrHash ptr (32B)   a1 = slotKey ptr (32B)
    a2 = exec-log base (128B entries)   a3 = entry count
    a4 = out value ptr (32B; written with the latest matching `current` on a hit)
    a0 (output) = 1 if a matching entry was found (out holds its committed value),
                  0 if the slot was never touched (out left unchanged).
    Leaf: uses only t-registers + the argument registers; no stack frame. -/
def execLogLatestValueFunction : String :=
  "exec_log_latest_value:\n" ++
  "  li t6, 0                      # found flag\n" ++
  "  li t0, 0                      # entry index i\n" ++
  ".Lelv_loop:\n" ++
  "  beq t0, a3, .Lelv_done\n" ++
  "  slli t1, t0, 7; add t2, a2, t1   # entry ptr = base + i*128\n" ++
  "  # match addrHash (entry@0 vs a0)\n" ++
  "  ld t3, 0(t2);  ld t4, 0(a0);  bne t3, t4, .Lelv_next\n" ++
  "  ld t3, 8(t2);  ld t4, 8(a0);  bne t3, t4, .Lelv_next\n" ++
  "  ld t3, 16(t2); ld t4, 16(a0); bne t3, t4, .Lelv_next\n" ++
  "  ld t3, 24(t2); ld t4, 24(a0); bne t3, t4, .Lelv_next\n" ++
  "  # match slotKey (entry@32 vs a1)\n" ++
  "  ld t3, 32(t2); ld t4, 0(a1);  bne t3, t4, .Lelv_next\n" ++
  "  ld t3, 40(t2); ld t4, 8(a1);  bne t3, t4, .Lelv_next\n" ++
  "  ld t3, 48(t2); ld t4, 16(a1); bne t3, t4, .Lelv_next\n" ++
  "  ld t3, 56(t2); ld t4, 24(a1); bne t3, t4, .Lelv_next\n" ++
  "  # matching entry: copy current (entry@96) -> out; set found. Overwrite keeps the LAST match.\n" ++
  "  ld t3, 96(t2);  sd t3, 0(a4)\n" ++
  "  ld t3, 104(t2); sd t3, 8(a4)\n" ++
  "  ld t3, 112(t2); sd t3, 16(a4)\n" ++
  "  ld t3, 120(t2); sd t3, 24(a4)\n" ++
  "  li t6, 1\n" ++
  ".Lelv_next:\n" ++
  "  addi t0, t0, 1; j .Lelv_loop\n" ++
  ".Lelv_done:\n" ++
  "  mv a0, t6\n" ++
  "  ret"

/-- `zisk_exec_log_latest_value`: focused probe.
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

def ziskExecLogLatestValueProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskExecLogLatestValuePrologue
  dataAsm     := ""
}

end EvmAsm.Codegen
