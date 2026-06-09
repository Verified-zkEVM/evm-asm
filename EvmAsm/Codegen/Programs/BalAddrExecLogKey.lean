/-
  EvmAsm.Codegen.Programs.BalAddrExecLogKey

  `bal_addr_to_exec_log_key` (bead bmvmx.1.6.4.2) — convert a BAL account's 20-byte
  big-endian address into the 32-byte key the EXEC LOG uses for that account when it
  is a nested CALLEE.

  Why a reversal: the persistent storage log keys on the executing frame's
  `env.ADDRESS` (env+0). For a nested callee, `call_frame_set_call_env` sets the
  child's `env.ADDRESS` by copying the CALL `to` stack word verbatim
  (CallFrameDescend.lean: `ld 0(a2); sd 0(a0)` ×4, a2 = `to_ptr` = `x12+32`), and EVM
  stack words are 4 LE u64 limbs (Storage.lean slotKey doc; ChildFrameHandlers.lean:154
  notes env.ADDRESS is in "stack-word representation"). So a callee's exec-log key is
  its address in LE-limb (byte-reversed) order, low-aligned in 32 bytes — NOT the
  big-endian low-aligned form the single recipient gets from staging. To seed a
  callee's storage (bmvmx.1.6.4.2.b) so its SLOAD finds the witness value, the seed's
  `addrHash` must be produced by this reversal from the BAL's 20-byte BE address.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_addr_to_exec_log_key

    Calling convention:
      a0 = 20-byte big-endian address ptr (BAL AccountChanges item 0)
      a1 = 32-byte out ptr (exec-log addrHash / stack-word key)
    Effect:
      out[i] = addr[19-i] for i in 0..20 (byte reversal), out[20..32] = 0.
      i.e. the address as a 256-bit value in 4 LE u64 limbs, matching the callee's
      env.ADDRESS during the descent.

    Leaf (no stack frame); clobbers t0..t4. -/
def balAddrToExecLogKeyFunction : String :=
  "bal_addr_to_exec_log_key:\n" ++
  "  sd x0, 0(a1); sd x0, 8(a1); sd x0, 16(a1); sd x0, 24(a1)\n" ++
  "  li t0, 0\n" ++
  ".Lbatelk_loop:\n" ++
  "  li t1, 20; beq t0, t1, .Lbatelk_done\n" ++
  "  li t2, 19; sub t2, t2, t0\n" ++          -- 19 - i (source byte: MSB-first -> LSB-first)
  "  add t3, a0, t2; lbu t4, 0(t3)\n" ++
  "  add t3, a1, t0; sb t4, 0(t3)\n" ++
  "  addi t0, t0, 1; j .Lbatelk_loop\n" ++
  ".Lbatelk_done:\n" ++
  "  ret"

/-- `zisk_bal_addr_to_exec_log_key`: probe. Address bytes a[0]=0xAA (MSB) .. a[19]=0xBB
    (LSB), interior bytes a[5]=0x33. The stack-word key must place the LSB at out[0]
    and the MSB at out[19].
    Output (at 0xa0010000):
      +0  out[0..8] (low byte = a[19] = 0xBB)         -> 0xBB
      +8  out byte at index 19 (= a[0] = 0xAA)         -> 0xAA
      +16 out byte at index 14 (= a[5] = 0x33)         -> 0x33
      +24 out[24..32] (high padding)                   -> 0 -/
def ziskBalAddrExecLogKeyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- Build the 20-byte BE address in scratch: a[0]=0xAA, a[5]=0x33, a[19]=0xBB, else 0.
  "  la t0, bael_addr\n" ++
  "  li t1, 20; mv t2, t0\n" ++
  "1:\n  beqz t1, 2f\n  sb zero, 0(t2); addi t2, t2, 1; addi t1, t1, -1; j 1b\n" ++
  "2:\n" ++
  "  li t1, 0xAA; sb t1, 0(t0)\n" ++
  "  li t1, 0x33; sb t1, 5(t0)\n" ++
  "  li t1, 0xBB; sb t1, 19(t0)\n" ++
  "  la a0, bael_addr; la a1, bael_key\n" ++
  "  jal ra, bal_addr_to_exec_log_key\n" ++
  "  la t0, bael_key\n" ++
  "  ld t1, 0(t0); sd t1, 0(s0)\n" ++             -- out[0..8] (low byte = 0xBB)
  "  lbu t1, 19(t0); sd t1, 8(s0)\n" ++           -- out[19] = 0xAA
  "  lbu t1, 14(t0); sd t1, 16(s0)\n" ++          -- out[14] = a[5] = 0x33
  "  ld t1, 24(t0); sd t1, 24(s0)\n" ++           -- out[24..32] = 0
  "  j .Lbael_done\n" ++
  balAddrToExecLogKeyFunction ++ "\n" ++
  ".Lbael_done:"

def ziskBalAddrExecLogKeyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bael_addr:\n  .zero 32\n" ++
  "bael_key:\n  .zero 32\n"

def ziskBalAddrExecLogKeyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAddrExecLogKeyPrologue
  dataAsm     := ziskBalAddrExecLogKeyDataSection
}

end EvmAsm.Codegen
