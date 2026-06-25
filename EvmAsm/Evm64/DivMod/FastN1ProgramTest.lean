/-
  EvmAsm.Evm64.DivMod.FastN1ProgramTest

  Functional sanity checks for the n=1 fast path (issue #9303), validating
  branch/JAL offsets end-to-end by executing `evm_div_v6` / `evm_mod_v6` on
  concrete vectors. Uses `#guard` (compiled evaluation) rather than `decide`
  to avoid slow kernel reduction over the ~450-step divide; correctness is
  established separately by the formal stack-level spec.
-/

import EvmAsm.Evm64.DivMod.FastN1Program
import EvmAsm.Rv64.Execution

namespace EvmAsm.Evm64.FastN1Test

open EvmAsm.Rv64

/-- Step until `pc` reaches `target`, bounded by `fuel`. Robust to the
    data-dependent internal branching of `divK_div128_v5` (unlike a fixed
    step count). -/
def stepUntilPc (target : Word) : Nat → MachineState → Option MachineState
  | 0, _ => none
  | n + 1, s => if s.pc == target then some s else (step s).bind (stepUntilPc target n)

/-- Test state: `a` at sp+0..24, `b` at sp+32..56, program loaded at 0. -/
def mkState (prog : Program) (sp : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : MachineState where
  regs := fun r => match r with | .x12 => sp | _ => 0
  mem := fun a =>
    if a == sp then a0 else if a == sp + 8 then a1
    else if a == sp + 16 then a2 else if a == sp + 24 then a3
    else if a == sp + 32 then b0 else if a == sp + 40 then b1
    else if a == sp + 48 then b2 else if a == sp + 56 then b3
    else 0
  code := loadProgram 0 prog
  pc := 0

/-- Run a v6 program to its exit PC and read the 4 result limbs at x12. -/
def runResult (prog : Program) (exitPc : Word) (sp : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Option (List Word) :=
  match stepUntilPc exitPc 4000 (mkState prog sp a0 a1 a2 a3 b0 b1 b2 b3) with
  | some s =>
    let r := s.getReg .x12
    some [s.getMem r, s.getMem (r + 8), s.getMem (r + 16), s.getMem (r + 24)]
  | none => none

abbrev divExit : Word := 1884
abbrev modExit : Word := 1912

-- DIV fast path (n=1)
-- DIV(100, 7) = 14
#guard runResult evm_div_v6 divExit 1024  100 0 0 0  7 0 0 0 = some [14, 0, 0, 0]
-- DIV(a, 1) = a  (s = 63, normalization active)
#guard runResult evm_div_v6 divExit 1024  5 6 7 8  1 0 0 0 = some [5, 6, 7, 8]
-- DIV(2^64 + 5, 2) = 2^63 + 2
#guard runResult evm_div_v6 divExit 1024  5 1 0 0  2 0 0 0 = some [9223372036854775810, 0, 0, 0]
-- DIV(2^192, 2^63) = 2^129  (s = 0, copyAU path; quotient in limb 2)
#guard runResult evm_div_v6 divExit 1024  0 0 0 1  0x8000000000000000 0 0 0 = some [0, 0, 2, 0]

-- DIV dispatch to reused v5
-- DIV(42, 0) = 0  (divisor zero → routed to v5 zeroPath)
#guard runResult evm_div_v6 divExit 1024  42 0 0 0  0 0 0 0 = some [0, 0, 0, 0]
-- DIV(2^128, 2^64) = 2^64  (n = 2 → routed to v5)
#guard runResult evm_div_v6 divExit 1024  0 0 1 0  0 1 0 0 = some [0, 1, 0, 0]

-- MOD fast path (n=1)
-- MOD(100, 7) = 2
#guard runResult evm_mod_v6 modExit 1024  100 0 0 0  7 0 0 0 = some [2, 0, 0, 0]
-- MOD(2^64 + 5, 2) = 1
#guard runResult evm_mod_v6 modExit 1024  5 1 0 0  2 0 0 0 = some [1, 0, 0, 0]
-- MOD(42, 0) = 0  (divisor zero → routed to v5)
#guard runResult evm_mod_v6 modExit 1024  42 0 0 0  0 0 0 0 = some [0, 0, 0, 0]

end EvmAsm.Evm64.FastN1Test
