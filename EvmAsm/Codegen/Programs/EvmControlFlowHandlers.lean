/-
  EvmAsm.Codegen.Programs.EvmControlFlowHandlers

  Dispatcher handlers for JUMPDEST, JUMP, JUMPI, and PC.
-/

import EvmAsm.Evm64.ControlFlow.Program
import EvmAsm.Codegen.Dispatch

namespace EvmAsm.Codegen

/-- Validity check shared by JUMP / taken-JUMPI: require `code[dest]`
    to be JUMPDEST (this is also how the body's invalid-dest sentinel
    routes to `.exit_invalid`), then test bit `dest = x10 - x21` of the
    valid-JUMPDEST bitmap the dispatcher prologue precomputed
    (`emitJumpdestBitmapBuild`). A literal `0x5b` inside PUSH data has
    no bit set, so it is rejected. O(1) per jump — M15.6 replaces the
    former O(dest) pushdata-aware scan. Destinations at or beyond the
    bitmap capacity (impossible for protocol-sized code) are rejected
    before the bitmap load so the lookup never reads past the region. -/
private def jumpBitmapCheckAsm : String :=
  "  li x18, 0x5b\n" ++
  "  bne x17, x18, .exit_invalid\n" ++
  "  sub x18, x10, x21\n" ++
  s!"  li x19, {jumpdestBitmapCodeCapacity}\n" ++
  "  bgeu x18, x19, .exit_invalid\n" ++
  "  srli x19, x18, 3\n" ++
  "  la x5, evm_jumpdest_bitmap\n" ++
  "  add x5, x5, x19\n" ++
  "  lbu x19, 0(x5)\n" ++
  "  andi x18, x18, 7\n" ++
  "  srl x19, x19, x18\n" ++
  "  andi x19, x19, 1\n" ++
  "  beqz x19, .exit_invalid\n" ++
  "  ret"

private def jumpValidityTail : HandlerTail :=
  .custom jumpBitmapCheckAsm

private def jumpiValidityTail : HandlerTail :=
  .custom <| "  beqz x15, .Ljumpi_not_taken_valid\n" ++
    jumpBitmapCheckAsm ++ "\n.Ljumpi_not_taken_valid:\n  ret"

/-- M14 / M15 control-flow opcodes.

    - **JUMPDEST (0x5b, M14)**: no-op marker. Empty body +
      `.advanceAndRet 1` tail.
    - **JUMP (0x56, M15)**: pops dest; if its upper limbs are zero
      and `dest.low64 < env.codeSize`, writes `x10 := x21 + dest.low64`
      and feeds the jump-validity tail. No `.advanceAndRet` (would
      over-advance by 1).
    - **JUMPI (0x57, M15)**: pops dest + cond; if cond != 0 and dest's
      upper limbs are zero and `dest.low64 < env.codeSize`, writes
      `x10 := x21 + dest.low64`; if cond is zero, advances `x10` by 1
      in the body and skips validation.
    - **PC (0x58, M15)**: pushes `x10 - x21` as a 256-bit word
      with the value in the low limb. Tail is `.advanceAndRet 1`.

    All three M15 handlers consume the dispatcher's preserved
    code-base register `x21` (set in the prologue via
    `la x21, evm_code` / `li x21, 0x40000010`). The scratch
    registers `x14`/`x15`/`x16` are caller-saved per the existing
    convention.

    **M15.5/M15.6 JUMPDEST-validity**: JUMP / taken-JUMPI test the
    target's bit in the valid-JUMPDEST bitmap that the dispatcher
    prologue precomputes with one pushdata-aware pass over the bytecode
    (M15.6; formerly an O(dest) per-jump scan). Targets at or beyond
    `env.codeSize` are rejected before the body reads `code[dest]`. A
    literal `0x5b` inside PUSH data is rejected even though the target
    byte equals JUMPDEST. Not-taken JUMPI still skips validation,
    matching execution-specs. -/
def controlFlowHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_JUMPDEST"
    , opcodes := [0x5b]
    , body    := []
    , tail    := .advanceAndRet 1 }
  , { label := "h_JUMP"
    , opcodes := [0x56]
    , preBody := stackUnderflowGuardAsm 1
    , body    := EvmAsm.Evm64.ControlFlow.evm_jump .x21 .x20 .x14 .x16 .x17
    , tail    := jumpValidityTail }
  , { label := "h_JUMPI"
    , opcodes := [0x57]
    , preBody := stackUnderflowGuardAsm 2
    , body    := EvmAsm.Evm64.ControlFlow.evm_jumpi .x21 .x20 .x14 .x15 .x16 .x17
    , tail    := jumpiValidityTail }
  , { label := "h_PC"
    , opcodes := [0x58]
    , body    := EvmAsm.Evm64.ControlFlow.evm_pc .x21 .x14
    , tail    := .advanceAndRet 1 } ]

end EvmAsm.Codegen
