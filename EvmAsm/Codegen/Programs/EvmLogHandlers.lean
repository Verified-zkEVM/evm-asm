/-
  EvmAsm.Codegen.Programs.EvmLogHandlers

  Dispatcher handlers for LOG0 through LOG4.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Codegen.Programs.StaticContext

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Copy `topicCount` stack words into an event-log descriptor.
    Descriptor topics live at entry offsets 32, 64, 96, and 128. -/
def logTopicCopies (topicCount : Nat) : String :=
  String.intercalate "" <|
    (List.range topicCount).map fun i =>
      let stackOff := 64 + i * 32
      let entryOff := 32 + i * 32
      -- x25 (NOT x21) as the copy temp: x21 is the dispatcher's reserved EVM
      -- code-base register (PC = x10 - x21); clobbering it breaks the code-size
      -- stop guard / PC / JUMP after a LOG, halting the frame early (a LOG
      -- followed by any further opcode, e.g. LOG0-then-CALL).
      "  ld x25, " ++ toString stackOff ++ "(x12)\n" ++
      "  sd x25, " ++ toString entryOff ++ "(x14)\n" ++
      "  ld x25, " ++ toString (stackOff + 8) ++ "(x12)\n" ++
      "  sd x25, " ++ toString (entryOff + 8) ++ "(x14)\n" ++
      "  ld x25, " ++ toString (stackOff + 16) ++ "(x12)\n" ++
      "  sd x25, " ++ toString (entryOff + 16) ++ "(x14)\n" ++
      "  ld x25, " ++ toString (stackOff + 24) ++ "(x12)\n" ++
      "  sd x25, " ++ toString (entryOff + 24) ++ "(x14)\n"

/-- M26 LOG capture prefix. Appends a bounded 256-byte descriptor:
      +0  topic count (u64)
      +8  memory offset low u64
      +16 memory size low u64
      +24 copied data length (min(size, 32))
      +32..160 four 32-byte topic slots
      +160..192 first up to 32 data bytes
      +192..224 ADDRESS context word
      +224..256 CALLER context word

    Topic slots use the dispatcher's stack-word byte order (low limb first).
    The address context is copied from env.ADDRESS as the canonical low-aligned
    20-byte account address used by top-level runtime staging. Overflow writes
    halt_kind = 4 and exits via `.exit_no_epilogue` instead of silently dropping
    the event. -/
def logCapturePreBody (topicCount : Nat) : String :=
  "  ld x15, 472(x20)\n" ++          -- x15 = event log length
  "  li x16, 4096\n" ++              -- static cap: 4096 descriptors (v0.6.0 deposit blocks exceed 1024)
  "  bgeu x15, x16, 9f\n" ++
  "  la x14, evm_event_logs\n" ++
  "  slli x16, x15, 8\n" ++          -- entry offset = count * 256
  "  add x14, x14, x16\n" ++         -- x14 = descriptor pointer
  -- Zero the full descriptor before filling the fields/topics/data prefix.
  "  mv x16, x14\n" ++
  "  li x17, 32\n" ++
  "1:\n" ++
  "  sd x0, 0(x16)\n" ++
  "  addi x16, x16, 8\n" ++
  "  addi x17, x17, -1\n" ++
  "  bnez x17, 1b\n" ++
  "  li x16, " ++ toString topicCount ++ "\n" ++
  "  sd x16, 0(x14)\n" ++
  "  ld x17, 0(x12)\n" ++            -- memory offset low u64
  "  ld x18, 32(x12)\n" ++           -- memory size low u64
  "  sd x17, 8(x14)\n" ++
  "  sd x18, 16(x14)\n" ++
  logTopicCopies topicCount ++
  -- Capture the local address and caller context from the env block.
  -- env.ADDRESS @ env+0 is the EVM stack-word layout (low limb first, since #8967),
  -- but the receipt log encoder (LogRecordsRlp) consumes descriptor+192 as the
  -- canonical 20-byte BE address, so reverse the 20 address bytes here. The
  -- descriptor was pre-zeroed, so the upper 12 bytes of the +192 word stay zero
  -- (matching the canonical low-aligned form the encoder + bloom expect).
  -- x25 (NOT x21) as the byte/word temp here: x21 is the dispatcher's reserved
  -- EVM code-base register (PC = x10 - x21, JUMP/JUMPI target = x21 + dest, and
  -- the code-size stop guard `sub x5,x10,x21`). The handler runs mid-dispatch and
  -- must preserve x21, or any opcode AFTER a LOG (e.g. LOG0-then-CALL) reads a
  -- corrupted code base -> the stop guard exits the frame early, dropping the rest
  -- of the bytecode (contract_log_and_transfer_ordering: CALL never executes, so
  -- the value transfer's BAL non-storage effect + EIP-7708 log are missing).
  "  addi x22, x20, 19\n" ++        -- src = env+19 (MSB of the LE address)
  "  addi x23, x14, 192\n" ++       -- dst = descriptor+192 (canonical BE)
  "  li x16, 20\n" ++
  "42:\n" ++
  "  lbu x25, 0(x22)\n" ++
  "  sb x25, 0(x23)\n" ++
  "  addi x22, x22, -1\n" ++
  "  addi x23, x23, 1\n" ++
  "  addi x16, x16, -1\n" ++
  "  bnez x16, 42b\n" ++
  "  ld x25, 64(x20)\n" ++
  "  sd x25, 224(x14)\n" ++
  "  ld x25, 72(x20)\n" ++
  "  sd x25, 232(x14)\n" ++
  "  ld x25, 80(x20)\n" ++
  "  sd x25, 240(x14)\n" ++
  "  ld x25, 88(x20)\n" ++
  "  sd x25, 248(x14)\n" ++
  "  li x19, 32\n" ++
  "  bgeu x19, x18, 2f\n" ++
  "  mv x18, x19\n" ++
  "2:\n" ++
  "  sd x18, 24(x14)\n" ++
  "  add x22, x13, x17\n" ++         -- source = evm_memory + offset
  "  addi x23, x14, 160\n" ++        -- data-prefix destination
  "3:\n" ++
  "  beqz x18, 4f\n" ++
  "  lbu x24, 0(x22)\n" ++
  "  sb x24, 0(x23)\n" ++
  "  addi x22, x22, 1\n" ++
  "  addi x23, x23, 1\n" ++
  "  addi x18, x18, -1\n" ++
  "  j 3b\n" ++
  "4:\n" ++
  -- 8uld3.1a: capture the FULL log data into the persistent evm_log_data buffer.
  -- The descriptor's +160 prefix is truncated to 32B and its mem ptr (x13+offset)
  -- is reclaimed when the emitting frame ends, so the full data is unreadable at
  -- block-end. evm_log_data_meta[index] = (byte offset into evm_log_data, full len)
  -- is kept parallel to evm_event_logs. Live: x14=descriptor, x15=index,
  -- x17=mem offset, x13=mem base; scratch x16/x18/x19/x25/x22/x23/x24.
  -- (x25 NOT x21: x21 is the dispatcher's reserved EVM code-base register; see above.)
  "  ld x16, 16(x14)\n" ++           -- x16 = full data size (unclamped, stored at +16)
  "  la x18, evm_log_data_used\n" ++
  "  ld x19, 0(x18)\n" ++            -- x19 = used (dst byte offset into evm_log_data)
  "  la x25, evm_log_data_meta\n" ++
  "  slli x22, x15, 4\n" ++
  "  add x25, x25, x22\n" ++         -- &meta[index]
  "  sd x19, 0(x25)\n" ++            -- meta[index].offset = used
  "  sd x16, 8(x25)\n" ++            -- meta[index].len = full size
  "  li x22, 1048576\n" ++
  "  add x23, x19, x16\n" ++         -- end = used + size
  "  bgtu x23, x22, 5f\n" ++         -- overflow -> set flag, still record descriptor
  "  la x25, evm_log_data\n" ++
  "  add x25, x25, x19\n" ++         -- dst = evm_log_data + used
  "  add x22, x13, x17\n" ++         -- src = evm_memory + offset
  "  mv x24, x16\n" ++               -- remaining = full size
  "6:\n" ++
  "  beqz x24, 7f\n" ++
  "  lbu x23, 0(x22)\n" ++
  "  sb x23, 0(x25)\n" ++
  "  addi x22, x22, 1\n" ++
  "  addi x25, x25, 1\n" ++
  "  addi x24, x24, -1\n" ++
  "  j 6b\n" ++
  "7:\n" ++                          -- success: used += round8(size)
  "  addi x16, x16, 7\n" ++
  "  andi x16, x16, -8\n" ++
  "  add x19, x19, x16\n" ++
  "  sd x19, 0(x18)\n" ++
  "  addi x15, x15, 1\n" ++
  "  sd x15, 472(x20)\n" ++
  "  j 8f\n" ++
  "5:\n" ++                          -- overflow: flag it; descriptor prefix still recorded
  "  la x25, evm_log_data_overflow\n" ++
  "  li x22, 1\n" ++
  "  sd x22, 0(x25)\n" ++
  "  addi x15, x15, 1\n" ++
  "  sd x15, 472(x20)\n" ++
  "  j 8f\n" ++
  "9:\n" ++
  "  li x16, 0xa0010000\n" ++
  "  li x17, 4\n" ++                 -- LOG buffer overflow
  "  sd x17, 32(x16)\n" ++
  -- 4ch8f.10.3: LOG-overflow halt via flag+ret (routes to .exit_no_epilogue).
  dispatchHaltRet 2 ++ "\n" ++
  "8:\n"

/-- M26 LOG opcodes (LOG0..LOG4). Each handler captures a bounded
    event descriptor, pops `(2 + n)` EVM words, advances PC by one
    byte, and returns to the dispatcher. -/
def logHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_LOG0", opcodes := [0xa0]
    , preBody := stackUnderflowGuardAsm 2 ++ "\n" ++ staticContextWriteGuardAsm ++ logDynamicGasAsm 0 ++ logCapturePreBody 0
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 64)
    , tail := .advanceAndRet 1 }
  , { label := "h_LOG1", opcodes := [0xa1]
    , preBody := stackUnderflowGuardAsm 3 ++ "\n" ++ staticContextWriteGuardAsm ++ logDynamicGasAsm 1 ++ logCapturePreBody 1
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 96)
    , tail := .advanceAndRet 1 }
  , { label := "h_LOG2", opcodes := [0xa2]
    , preBody := stackUnderflowGuardAsm 4 ++ "\n" ++ staticContextWriteGuardAsm ++ logDynamicGasAsm 2 ++ logCapturePreBody 2
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 128)
    , tail := .advanceAndRet 1 }
  , { label := "h_LOG3", opcodes := [0xa3]
    , preBody := stackUnderflowGuardAsm 5 ++ "\n" ++ staticContextWriteGuardAsm ++ logDynamicGasAsm 3 ++ logCapturePreBody 3
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 160)
    , tail := .advanceAndRet 1 }
  , { label := "h_LOG4", opcodes := [0xa4]
    , preBody := stackUnderflowGuardAsm 6 ++ "\n" ++ staticContextWriteGuardAsm ++ logDynamicGasAsm 4 ++ logCapturePreBody 4
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 192)
    , tail := .advanceAndRet 1 } ]

/-! ## zisk_log_full_data_capture — 8uld3.1a probe

    Drives `logCapturePreBody 0` (LOG0) with a synthetic env/stack/memory and a
    64-byte (> 32) data region, then checks that the FULL data (not just the
    truncated 32-byte descriptor prefix) landed in the persistent `evm_log_data`
    buffer with a correct parallel `evm_log_data_meta[0] = (offset, len)` entry.

    Output (at 0xa0010000):
      +0  evm_log_data_used   (expect 64 = round8(64))
      +8  evm_log_data_overflow (expect 0)
      +16 evm_log_data_meta[0].offset (expect 0)
      +24 evm_log_data_meta[0].len    (expect 64)
      +32 the 64 captured bytes (expect 0x01,0x02,…,0x40 — INCLUDING bytes 33..64
          which the old 32-byte-prefix capture would have dropped). -/
def ziskLogFullDataCapturePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la x20, lfdc_env\n" ++
  "  sd x0, 472(x20)\n" ++          -- eventLogLength = 0 (fresh tx)
  "  la t0, evm_log_data_used; sd x0, 0(t0)\n" ++       -- per-tx reset (mimic dispatcher setup)
  "  la t0, evm_log_data_overflow; sd x0, 0(t0)\n" ++
  "  la x12, lfdc_stack\n" ++       -- EVM stack: 0(x12)=mem offset, 32(x12)=mem size
  "  sd x0, 0(x12)\n" ++            -- offset = 0
  "  li t0, 64\n" ++
  "  sd t0, 32(x12)\n" ++           -- size = 64 (> 32: proves the capture is untruncated)
  "  la x13, lfdc_mem\n" ++         -- memory base
  logCapturePreBody 0 ++            -- LOG0 capture (falls through label 8 to the dump below)
  "  li t0, 0xa0010000\n" ++
  "  la t1, evm_log_data_used; ld t2, 0(t1); sd t2, 0(t0)\n" ++
  "  la t1, evm_log_data_overflow; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  la t1, evm_log_data_meta; ld t2, 0(t1); sd t2, 16(t0)\n" ++   -- meta[0].offset
  "  ld t2, 8(t1); sd t2, 24(t0)\n" ++                              -- meta[0].len
  "  la t1, evm_log_data\n" ++
  "  addi t3, t0, 32\n" ++
  "  li t4, 64\n" ++
  ".Llfdc_dump:\n" ++
  "  beqz t4, .Llfdc_done\n" ++
  "  lbu t5, 0(t1); sb t5, 0(t3); addi t1, t1, 1; addi t3, t3, 1; addi t4, t4, -1; j .Llfdc_dump\n" ++
  ".Llfdc_done:\n" ++
  "  j .Llfdc_exit\n" ++
  ".exit_no_epilogue:\n" ++         -- logCapturePreBody's overflow exit target (unreached here)
  ".Llfdc_exit:"

def ziskLogFullDataCaptureDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "lfdc_env:\n  .zero 624\n" ++
  ".balign 8\n" ++
  "lfdc_stack:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "evm_event_logs:\n  .zero 512\n" ++          -- one 256-byte descriptor suffices
  ".balign 8\n" ++
  "evm_log_data:\n  .zero 512\n" ++
  ".balign 8\n" ++
  "evm_log_data_meta:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "evm_log_data_used:\n  .zero 8\n" ++
  "evm_log_data_overflow:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "lfdc_mem:\n" ++                              -- bytes 0..63 = 0x01,0x02,…,0x40 (LE within each quad)
  "  .quad 0x0807060504030201\n" ++
  "  .quad 0x100f0e0d0c0b0a09\n" ++
  "  .quad 0x1817161514131211\n" ++
  "  .quad 0x201f1e1d1c1b1a19\n" ++
  "  .quad 0x2827262524232221\n" ++
  "  .quad 0x302f2e2d2c2b2a29\n" ++
  "  .quad 0x3837363534333231\n" ++
  "  .quad 0x403f3e3d3c3b3a39\n" ++
  "  .zero 4032\n"

def ziskLogFullDataCaptureProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskLogFullDataCapturePrologue
  dataAsm     := ziskLogFullDataCaptureDataSection
}

end EvmAsm.Codegen
