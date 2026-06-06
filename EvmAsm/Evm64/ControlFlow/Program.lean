/-
  EvmAsm.Evm64.ControlFlow.Program

  RISC-V programs implementing the EVM control-flow opcodes
  `PC` (0x58), `JUMP` (0x56), and `JUMPI` (0x57).

  These are the next-tier control-flow primitives on top of `JUMPDEST`
  (0x5b, a no-op marker, wired in M14). All three bodies are parametric
  in registers; the M15 codegen wiring sets:

  - `codeBaseReg = .x21` — initialised in the dispatcher prologue to
    the start of the EVM bytecode region (preserved across handlers).
  - `envBaseReg = .x20` — points at the dispatcher env block; the body
    reads `env.codeSize` to reject jumps at or beyond bytecode length.
  - scratch `destReg` / `condReg` / `tmpReg` from the M7 / M12 scratch
    pool (`x14` / `x15` / `x16`).

  ## Semantics

  - **PC** pushes the byte offset of the PC opcode itself within the
    bytecode. In the dispatcher's frame, that's `x10 - codeBaseReg`
    at handler entry (the dispatcher's `jalr` lands here with `x10`
    still pointing AT the PC byte).
  - **JUMP** pops `dest` and rejects it unless the upper 192 bits are
    zero and the low limb is inside the bytecode length. For a valid
    destination, it sets `x10 := codeBaseReg + dest.low64`. The dispatcher
    loop's next `lbu x5, 0(x10)` reads the jump-target byte.
  - **JUMPI** pops `dest` (top) and `cond` (next). If `cond` is
    nonzero (any bit in any of the 4 limbs set), behaves like JUMP.
    Otherwise advances `x10` by 1 (the JUMPI opcode is 1 byte).

  ## JUMPDEST-validity (M15.5)

  `JUMP` / taken `JUMPI` load `code[dest.low64]` into `validityReg`
  only after OR-reducing the upper destination limbs to zero and checking
  `dest.low64 < env.codeSize`. If the destination is non-canonical or out
  of bounds, the body writes a non-`0x5b` sentinel into `validityReg`. The
  codegen handler tail then compares `validityReg` to `0x5b`, scans from
  the bytecode base to the target while skipping PUSH1..PUSH32 immediates,
  and routes any mismatch or PUSH-data target to `.exit_invalid`.
-/

import EvmAsm.Evm64.Code.Basic
import EvmAsm.Rv64.Program

namespace EvmAsm.Evm64
namespace ControlFlow

open EvmAsm.Rv64

/-- Parameterized RISC-V program implementing `PC` (0x58).
    Pushes the byte offset of the PC opcode itself within the EVM
    bytecode. Computes `pc = x10 - codeBaseReg` at handler entry.
    `tmpReg` must be distinct from `x0`, `x10`, `x12`, `codeBaseReg`.
    6 instructions = 24 bytes. -/
def evm_pc (codeBaseReg tmpReg : Reg) : Program :=
  SUB tmpReg .x10 codeBaseReg ;;
  ADDI .x12 .x12 (-32) ;;
  SD .x12 tmpReg 0 ;;
  SD .x12 .x0 8 ;;
  SD .x12 .x0 16 ;;
  SD .x12 .x0 24

/-- Parameterized RISC-V program implementing `JUMP` (0x56).
    Pops the 256-bit destination from the EVM stack. If its upper three
    limbs are zero and `dest.low64 < env.codeSize`, updates
    `x10 := codeBaseReg + dest.low64` and loads `code[dest.low64]` into
    `validityReg` for the handler tail's JUMPDEST-validity check. If any
    upper limb is nonzero or the destination is out of bounds, leaves `x10`
    irrelevant and writes a non-`0x5b` sentinel to `validityReg`, which the
    handler tail routes to `.exit_invalid`.

    `destReg` / `tmpReg` / `validityReg` are caller-saved temporaries.
    They are distinct from `x0`, `x10`, `x12`, `codeBaseReg`, `envBaseReg`
    (and each other). 14 instructions = 56 bytes. -/
def evm_jump (codeBaseReg envBaseReg destReg tmpReg validityReg : Reg) : Program :=
  LD destReg .x12 0 ;;
  LD validityReg .x12 8 ;;
  LD tmpReg .x12 16 ;;
  OR' validityReg validityReg tmpReg ;;
  LD tmpReg .x12 24 ;;
  OR' validityReg validityReg tmpReg ;;
  ADDI .x12 .x12 32 ;;
  BNE validityReg .x0 (BitVec.ofNat 13 24) ;;
  LD tmpReg envBaseReg (BitVec.ofNat 12 EvmAsm.Evm64.Code.codeSizeOff) ;;
  BGEU destReg tmpReg (BitVec.ofNat 13 16) ;;
  ADD .x10 codeBaseReg destReg ;;
  LBU validityReg .x10 0 ;;
  JAL .x0 (BitVec.ofNat 21 8) ;;
  ADDI validityReg .x0 (BitVec.ofNat 12 0)

/-- Parameterized RISC-V program implementing `JUMPI` (0x57).
    Pops `dest` (top of stack) and `cond` (second). If `cond` is
    nonzero (any limb has any bit set), `dest` has zero upper limbs, and
    `dest.low64 < env.codeSize`, updates `x10 := codeBaseReg + dest.low64`.
    A taken jump with any nonzero upper destination limb or an out-of-bounds
    destination writes an invalid sentinel to `validityReg`. If `cond` is
    zero, the destination is ignored and `x10` advances by 1 (fall-through).

    `destReg`, `condReg`, `tmpReg`, `validityReg` are pairwise distinct
    caller-saved temporaries, also distinct from `x0`, `x10`, `x12`,
    `codeBaseReg`, `envBaseReg`. 25 instructions = 100 bytes.

    JUMPDEST-validity: the *taken* path loads `code[dest]` into
    `validityReg`; the *not-taken* path writes the sentinel `0x5b` so
    the handler tail's `validityReg == 0x5b` check is a no-op for
    fall-through. The handler tail does the compare + halt routing.

    Branch offsets:
    - `BEQ condReg x0 28` lands at the not-taken fall-through path.
    - `BNE validityReg x0 36` rejects taken jumps with nonzero upper
      destination limbs.
    - `BGEU destReg tmpReg 28` rejects taken jumps at/after code length.
    - `JAL x0 20` from the valid taken path skips not-taken + invalid.
    - `JAL x0 8` from the not-taken path skips invalid. -/
def evm_jumpi (codeBaseReg envBaseReg destReg condReg tmpReg validityReg : Reg) : Program :=
  -- Stack top is `dest` at x12+0..31.  Load the low limb, then OR the
  -- upper three limbs together so `validityReg = 0` iff dest < 2^64.
  LD destReg .x12 0 ;;
  LD validityReg .x12 8 ;;
  LD tmpReg .x12 16 ;;
  OR' validityReg validityReg tmpReg ;;
  LD tmpReg .x12 24 ;;
  OR' validityReg validityReg tmpReg ;;
  -- The next stack word is `cond` at x12+32..63.  OR all four limbs into
  -- `condReg`; zero means fall through, nonzero means take the jump.
  LD condReg .x12 32 ;;
  LD tmpReg .x12 40 ;;
  OR' condReg condReg tmpReg ;;
  LD tmpReg .x12 48 ;;
  OR' condReg condReg tmpReg ;;
  LD tmpReg .x12 56 ;;
  OR' condReg condReg tmpReg ;;
  ADDI .x12 .x12 64 ;;
  -- Not taken: advance past the JUMPI opcode and write a harmless sentinel.
  -- Taken with nonzero upper dest limbs: jump to the invalid sentinel below.
  -- Taken with an in-range canonical dest: load code[dest].
  BEQ condReg .x0 (BitVec.ofNat 13 28) ;;
  BNE validityReg .x0 (BitVec.ofNat 13 36) ;;
  LD tmpReg envBaseReg (BitVec.ofNat 12 EvmAsm.Evm64.Code.codeSizeOff) ;;
  BGEU destReg tmpReg (BitVec.ofNat 13 28) ;;
  -- Valid taken jump: point x10 at code[dest.low64] and load that byte for
  -- the codegen tail's JUMPDEST / PUSH-data validation scan.
  ADD .x10 codeBaseReg destReg ;;
  LBU validityReg .x10 0 ;;
  JAL .x0 (BitVec.ofNat 21 20) ;;
  -- Not-taken fall-through path.
  ADDI .x10 .x10 1 ;;
  ADDI validityReg .x0 (BitVec.ofNat 12 0x5b) ;;
  JAL .x0 (BitVec.ofNat 21 8) ;;
  -- Invalid taken jump: make the downstream `validityReg == 0x5b` check fail.
  ADDI validityReg .x0 (BitVec.ofNat 12 0)

end ControlFlow
end EvmAsm.Evm64
