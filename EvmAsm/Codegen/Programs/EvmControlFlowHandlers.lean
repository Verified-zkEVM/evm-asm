/-
  EvmAsm.Codegen.Programs.EvmControlFlowHandlers

  Dispatcher handlers for JUMPDEST, JUMP, JUMPI, and PC.
-/

import EvmAsm.Evm64.ControlFlow.Program
import EvmAsm.Evm64.ControlFlow.Jumpdest
import EvmAsm.Codegen.Dispatch

namespace EvmAsm.Codegen

/-- Validity check shared by JUMP / taken-JUMPI: require `code[dest]`
    to be JUMPDEST in the *current frame* and reject literal `0x5b` bytes
    embedded in PUSH data. The top-level dispatcher still builds a bitmap for
    standalone probes, but nested CALL/STATICCALL frames can switch `x21` to
    different code, so this checker scans from the current code base up to the
    destination using PUSH-width skips and the current frame `env.codeSize`. -/
private def jumpBitmapCheckAsm : String :=
  "  li x18, 0x5b\n" ++
  "  bne x17, x18, .exit_invalid\n" ++
  "  sub x18, x10, x21             # dest = target - codebase\n" ++
  "  ld x19, 496(x20)              # current frame codeSize\n" ++
  "  bgeu x18, x19, .exit_invalid\n" ++
  "  mv x5, x21                    # scan ptr = codebase\n" ++
  "  li x6, 0                      # scan pc\n" ++
  "1:\n" ++
  "  beq x6, x18, 3f\n" ++
  "  bgeu x6, x18, .exit_invalid   # overshot via PUSH data\n" ++
  "  lbu x7, 0(x5)\n" ++
  "  li x19, 0x60\n" ++
  "  bltu x7, x19, 2f\n" ++
  "  li x19, 0x7f\n" ++
  "  bltu x19, x7, 2f\n" ++
  "  addi x7, x7, -0x5f            # PUSH payload width\n" ++
  "  add x6, x6, x7\n" ++
  "  add x5, x5, x7\n" ++
  "2:\n" ++
  "  addi x6, x6, 1\n" ++
  "  addi x5, x5, 1\n" ++
  "  j 1b\n" ++
  "3:\n" ++
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
      -- The verified JUMPDEST program (`ControlFlow/Jumpdest.lean`) —
      -- definitionally the empty instruction list.
    , body    := EvmAsm.Evm64.ControlFlow.evm_jumpdest
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
    , preBody := stackOverflowGuardAsm
    , body    := EvmAsm.Evm64.ControlFlow.evm_pc .x21 .x14
    , tail    := .advanceAndRet 1 } ]

end EvmAsm.Codegen
