/-
  EvmAsm.Codegen.Programs.ExecLogStorageSeed

  `exec_log_append_storage_seed` (bead bmvmx.1.6.4.1, option A) — a verdict-specific
  primitive for seeding a storage slot into the persistent exec log with an explicit
  per-account `addrHash`, WITHOUT touching the shared 64-byte preload input contract
  (the `preload_expand_loop` format is used by the top-level guest's zkVM input via
  scripts/eest-stateless-to-input.py, so it must not change).

  Production block-verdict callers pass zero for this shared preload input;
  the nonzero format remains for standalone runtime-input compatibility and
  the SSTORE-clear probe.

  Production contract dispatch now leaves the shared input preload empty and resolves
  the recipient's slots through authenticated demand-driven reads. To make NESTED
  CALLEES read their witness storage (instead of cold 0) the verdict appends each
  callee's slots to the exec log keyed on that callee's address. This helper is that
  append primitive: it writes one 128-byte entry and bumps the entry count. A seeded
  slot has original == current == value (a pre-tx value, no net change — matching the
  retained standalone/probe preload format, which sets both to the preloaded value).

  Exec-log entry layout (Storage.lean): 128 bytes = addrHash@0, slotKey@32,
  original@64, current@96.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## exec_log_append_storage_seed

    Calling convention:
      a0 = exec storage-log base (e.g. 0xa0630000)
      a1 = current entry count (persistentLogLength)
      a2 = addrHash ptr (32 bytes, the account's env.ADDRESS form / exec-log key)
      a3 = slotKey ptr  (32 bytes, EVM-stack byte order — same as SLOAD/SSTORE)
      a4 = value ptr    (32 bytes, the witness slot value)
    Effect:
      writes entry[count] = (addrHash, slotKey, original=value, current=value).
    Returns:
      a0 = count + 1 (the new entry count; caller stores it to env.persistentLogLength).

    Leaf (no stack frame); clobbers t0, t1 only. -/
def execLogAppendStorageSeedFunction : String :=
  "exec_log_append_storage_seed:\n" ++
  "  slli t0, a1, 7               # count * 128\n" ++
  "  add t0, a0, t0               # entry ptr\n" ++
  -- addrHash a2[0..32] -> entry[0..32]
  "  ld t1, 0(a2);  sd t1, 0(t0)\n" ++
  "  ld t1, 8(a2);  sd t1, 8(t0)\n" ++
  "  ld t1, 16(a2); sd t1, 16(t0)\n" ++
  "  ld t1, 24(a2); sd t1, 24(t0)\n" ++
  -- slotKey a3[0..32] -> entry[32..64]
  "  ld t1, 0(a3);  sd t1, 32(t0)\n" ++
  "  ld t1, 8(a3);  sd t1, 40(t0)\n" ++
  "  ld t1, 16(a3); sd t1, 48(t0)\n" ++
  "  ld t1, 24(a3); sd t1, 56(t0)\n" ++
  -- value a4[0..32] -> original entry[64..96] AND current entry[96..128]
  "  ld t1, 0(a4);  sd t1, 64(t0);  sd t1, 96(t0)\n" ++
  "  ld t1, 8(a4);  sd t1, 72(t0);  sd t1, 104(t0)\n" ++
  "  ld t1, 16(a4); sd t1, 80(t0);  sd t1, 112(t0)\n" ++
  "  ld t1, 24(a4); sd t1, 88(t0);  sd t1, 120(t0)\n" ++
  "  addi a0, a1, 1               # new entry count\n" ++
  "  ret"

/-- `zisk_exec_log_append_storage_seed`: probe. Starting from an empty log (count 0),
    append (A=0xAA, slot 0x07, value 0x42) then (B=0xBB, slot 0x09, value 0x99), and
    read back the two entries + the returned count.
    Output (at 0xa0010000):
      +0  final count                 (expect 2)
      +8  entry0 addrHash low byte     (0xAA)
      +16 entry0 slotKey  low byte     (0x07)
      +24 entry0 original low byte     (0x42)
      +32 entry0 current  low byte     (0x42)
      +40 entry1 addrHash low byte     (0xBB)
      +48 entry1 current  low byte     (0x99) -/
def ziskExecLogStorageSeedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- addrHash A / B, keys, values in scratch.
  "  la t0, els_addrA; li t1, 0xAA; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t0, els_addrB; li t1, 0xBB; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t0, els_k7; li t1, 0x07; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t0, els_k9; li t1, 0x09; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t0, els_v42; li t1, 0x42; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t0, els_v99; li t1, 0x99; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  -- append (A, 7, 0x42) from count 0.
  "  la a0, els_log; li a1, 0; la a2, els_addrA; la a3, els_k7; la a4, els_v42\n" ++
  "  jal ra, exec_log_append_storage_seed\n" ++
  "  mv s1, a0                    # count = 1\n" ++
  -- append (B, 9, 0x99) from count 1.
  "  la a0, els_log; mv a1, s1; la a2, els_addrB; la a3, els_k9; la a4, els_v99\n" ++
  "  jal ra, exec_log_append_storage_seed\n" ++
  "  sd a0, 0(s0)                 # final count\n" ++
  -- read back entry0 (els_log + 0) and entry1 (els_log + 128).
  "  la t0, els_log\n" ++
  "  ld t1, 0(t0);   sd t1, 8(s0)\n" ++     -- entry0 addrHash
  "  ld t1, 32(t0);  sd t1, 16(s0)\n" ++    -- entry0 slotKey
  "  ld t1, 64(t0);  sd t1, 24(s0)\n" ++    -- entry0 original
  "  ld t1, 96(t0);  sd t1, 32(s0)\n" ++    -- entry0 current
  "  addi t0, t0, 128\n" ++
  "  ld t1, 0(t0);   sd t1, 40(s0)\n" ++    -- entry1 addrHash
  "  ld t1, 96(t0);  sd t1, 48(s0)\n" ++    -- entry1 current
  "  j .Lels_done\n" ++
  execLogAppendStorageSeedFunction ++ "\n" ++
  ".Lels_done:"

def ziskExecLogStorageSeedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "els_log:\n  .zero 512\n" ++
  "els_addrA:\n  .zero 32\n" ++
  "els_addrB:\n  .zero 32\n" ++
  "els_k7:\n  .zero 32\n" ++
  "els_k9:\n  .zero 32\n" ++
  "els_v42:\n  .zero 32\n" ++
  "els_v99:\n  .zero 32\n"


end EvmAsm.Codegen
