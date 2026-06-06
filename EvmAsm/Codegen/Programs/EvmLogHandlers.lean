/-
  EvmAsm.Codegen.Programs.EvmLogHandlers

  Dispatcher handlers for LOG0 through LOG4.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmMemoryGas

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Copy `topicCount` stack words into an event-log descriptor.
    Descriptor topics live at entry offsets 32, 64, 96, and 128. -/
def logTopicCopies (topicCount : Nat) : String :=
  String.intercalate "" <|
    (List.range topicCount).map fun i =>
      let stackOff := 64 + i * 32
      let entryOff := 32 + i * 32
      "  ld x21, " ++ toString stackOff ++ "(x12)\n" ++
      "  sd x21, " ++ toString entryOff ++ "(x14)\n" ++
      "  ld x21, " ++ toString (stackOff + 8) ++ "(x12)\n" ++
      "  sd x21, " ++ toString (entryOff + 8) ++ "(x14)\n" ++
      "  ld x21, " ++ toString (stackOff + 16) ++ "(x12)\n" ++
      "  sd x21, " ++ toString (entryOff + 16) ++ "(x14)\n" ++
      "  ld x21, " ++ toString (stackOff + 24) ++ "(x12)\n" ++
      "  sd x21, " ++ toString (entryOff + 24) ++ "(x14)\n"

/-- M26 LOG capture prefix. Appends a bounded 256-byte descriptor:
      +0  topic count (u64)
      +8  memory offset low u64
      +16 memory size low u64
      +24 copied data length (min(size, 32))
      +32..160 four 32-byte topic slots
      +160..192 first up to 32 data bytes
      +192..224 ADDRESS context word
      +224..256 CALLER context word

    The descriptor uses the dispatcher's current stack-word byte order
    (low limb first). A full receipt encoder can canonicalize to the
    Ethereum byte order later. Overflow writes halt_kind = 4 and exits
    via `.exit_no_epilogue` instead of silently dropping the event. -/
def logCapturePreBody (topicCount : Nat) : String :=
  "  ld x15, 472(x20)\n" ++          -- x15 = event log length
  "  li x16, 16\n" ++                -- static cap: 16 descriptors
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
  "  ld x21, 0(x20)\n" ++
  "  sd x21, 192(x14)\n" ++
  "  ld x21, 8(x20)\n" ++
  "  sd x21, 200(x14)\n" ++
  "  ld x21, 16(x20)\n" ++
  "  sd x21, 208(x14)\n" ++
  "  ld x21, 24(x20)\n" ++
  "  sd x21, 216(x14)\n" ++
  "  ld x21, 64(x20)\n" ++
  "  sd x21, 224(x14)\n" ++
  "  ld x21, 72(x20)\n" ++
  "  sd x21, 232(x14)\n" ++
  "  ld x21, 80(x20)\n" ++
  "  sd x21, 240(x14)\n" ++
  "  ld x21, 88(x20)\n" ++
  "  sd x21, 248(x14)\n" ++
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
  "  addi x15, x15, 1\n" ++
  "  sd x15, 472(x20)\n" ++
  "  j 8f\n" ++
  "9:\n" ++
  "  li x16, 0xa0010000\n" ++
  "  li x17, 4\n" ++                 -- LOG buffer overflow
  "  sd x17, 32(x16)\n" ++
  "  j .exit_no_epilogue\n" ++
  "8:\n"

/-- M26 LOG opcodes (LOG0..LOG4). Each handler captures a bounded
    event descriptor, pops `(2 + n)` EVM words, advances PC by one
    byte, and returns to the dispatcher. -/
def logHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_LOG0", opcodes := [0xa0]
    , preBody := stackUnderflowGuardAsm 2 ++ "\n" ++ logDynamicGasAsm 0 ++ logCapturePreBody 0
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 64)
    , tail := .advanceAndRet 1 }
  , { label := "h_LOG1", opcodes := [0xa1]
    , preBody := stackUnderflowGuardAsm 3 ++ "\n" ++ logDynamicGasAsm 1 ++ logCapturePreBody 1
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 96)
    , tail := .advanceAndRet 1 }
  , { label := "h_LOG2", opcodes := [0xa2]
    , preBody := stackUnderflowGuardAsm 4 ++ "\n" ++ logDynamicGasAsm 2 ++ logCapturePreBody 2
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 128)
    , tail := .advanceAndRet 1 }
  , { label := "h_LOG3", opcodes := [0xa3]
    , preBody := stackUnderflowGuardAsm 5 ++ "\n" ++ logDynamicGasAsm 3 ++ logCapturePreBody 3
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 160)
    , tail := .advanceAndRet 1 }
  , { label := "h_LOG4", opcodes := [0xa4]
    , preBody := stackUnderflowGuardAsm 6 ++ "\n" ++ logDynamicGasAsm 4 ++ logCapturePreBody 4
    , body := ADDI .x12 .x12 (BitVec.ofNat 12 192)
    , tail := .advanceAndRet 1 } ]

end EvmAsm.Codegen
