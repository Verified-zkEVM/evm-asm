/-
  EvmAsm.Codegen.Programs.EvmControlFlowHandlers

  Dispatcher handlers for JUMPDEST, JUMP, JUMPI, and PC.
-/

import EvmAsm.Evm64.ControlFlow.Program
import EvmAsm.Codegen.Dispatch

namespace EvmAsm.Codegen

/-- Scanner shared by JUMP / taken-JUMPI validation: require `code[dest]`
    to be JUMPDEST, then scan from `x21` to `x10`, skipping PUSH data. -/
private def jumpPushdataAwareScanAsm : String :=
  "  li x18, 0x5b\n  bne x17, x18, .exit_invalid\n  mv x18, x21\n1:\n  beq x18, x10, 3f\n  bltu x10, x18, .exit_invalid\n  lbu x19, 0(x18)\n  li x5, 0x60\n  bltu x19, x5, 2f\n  li x5, 0x80\n  bgeu x19, x5, 2f\n  addi x19, x19, -94\n  add x18, x18, x19\n  j 1b\n2:\n  addi x18, x18, 1\n  j 1b\n3:\n  ret"

private def jumpValidityTail : HandlerTail :=
  .custom jumpPushdataAwareScanAsm

private def jumpiValidityTail : HandlerTail :=
  .custom <| "  beqz x15, .Ljumpi_not_taken_valid\n" ++
    jumpPushdataAwareScanAsm ++ "\n.Ljumpi_not_taken_valid:\n  ret"

/-- M14 / M15 control-flow opcodes.

    - **JUMPDEST (0x5b, M14)**: no-op marker. Empty body +
      `.advanceAndRet 1` tail.
    - **JUMP (0x56, M15)**: pops dest, writes `x10 := x21 + dest`.
      Tail is `.custom "  ret"`; the body has already written `x10`,
      so the dispatcher's next loop iteration reads the jump-target
      byte. No `.advanceAndRet` (would over-advance by 1).
    - **JUMPI (0x57, M15)**: pops dest + cond; if cond != 0 writes
      `x10 := x21 + dest`, else advances `x10` by 1 in the body.
      Tail is `.custom "  ret"`; body handles both branches.
    - **PC (0x58, M15)**: pushes `x10 - x21` as a 256-bit word
      with the value in the low limb. Tail is `.advanceAndRet 1`.

    All three M15 handlers consume the dispatcher's preserved
    code-base register `x21` (set in the prologue via
    `la x21, evm_code` / `li x21, 0x40000010`). The scratch
    registers `x14`/`x15`/`x16` are caller-saved per the existing
    convention.

    **M15.5 JUMPDEST-validity**: JUMP / taken-JUMPI now scan from the
    bytecode base to the target while skipping PUSH1..PUSH32 immediates.
    A literal `0x5b` inside PUSH data is rejected even though the target byte
    equals JUMPDEST. Not-taken JUMPI still skips validation, matching
    execution-specs. -/
def controlFlowHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_JUMPDEST"
    , opcodes := [0x5b]
    , body    := []
    , tail    := .advanceAndRet 1 }
  , { label := "h_JUMP"
    , opcodes := [0x56]
    , preBody := stackUnderflowGuardAsm 1
    , body    := EvmAsm.Evm64.ControlFlow.evm_jump .x21 .x14 .x17
    , tail    := jumpValidityTail }
  , { label := "h_JUMPI"
    , opcodes := [0x57]
    , preBody := stackUnderflowGuardAsm 2
    , body    := EvmAsm.Evm64.ControlFlow.evm_jumpi .x21 .x14 .x15 .x16 .x17
    , tail    := jumpiValidityTail }
  , { label := "h_PC"
    , opcodes := [0x58]
    , body    := EvmAsm.Evm64.ControlFlow.evm_pc .x21 .x14
    , tail    := .advanceAndRet 1 } ]

end EvmAsm.Codegen
