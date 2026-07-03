/-
  EvmAsm.Evm64.AddMod.ProgramTest

  Functional sanity checks for `evm_addmod_total`, validating the three-way
  branch layout, the hardwired branch offsets, the MOD-call choreography, and
  the branch-free conditional subtract end-to-end by executing the assembled
  program (total body + skip-JAL + `evm_mod_callable_v5`) on concrete vectors.
  Uses `#guard` (compiled evaluation) rather than `decide` to avoid slow
  kernel reduction over the multi-thousand-step traces; correctness is
  established separately by the formal stack-level spec.
-/

import EvmAsm.Evm64.AddMod.Program
import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Rv64.Execution

namespace EvmAsm.Evm64.AddModTest

open EvmAsm.Rv64

/-- Step until `pc` reaches `target`, bounded by `fuel`. Robust to the
    data-dependent internal branching of the MOD callable. -/
def stepUntilPc (target : Word) : Nat → MachineState → Option MachineState
  | 0, _ => none
  | n + 1, s => if s.pc == target then some s else (step s).bind (stepUntilPc target n)

/-- Canonical test layout: `evm_addmod_total` at byte 0 (864 bytes), skip-JAL
    at 864, `evm_mod_callable_v5` at 868 (1412 bytes), end/exit at 2280.
    The four `JAL x1` call sites (bytes 244 / 348 / 452 / 836) all target the
    callable entry at 868. -/
def addmodTestProgram : Program :=
  evm_addmod_total 624 520 416 32 ;;
  JAL .x0 1416 ;;
  evm_mod_callable_v5

abbrev addmodExit : Word := 2280

/-- Test state: `a` at sp+0..24, `b` at sp+32..56, `N` at sp+64..88, program
    loaded at 0. All other memory (including the below-sp parking scratch and
    the callable's div-scratch band) defaults to 0. -/
def mkState (sp : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 : Word) : MachineState where
  regs := fun r => match r with | .x12 => sp | _ => 0
  mem := fun a =>
    if a == sp then a0 else if a == sp + 8 then a1
    else if a == sp + 16 then a2 else if a == sp + 24 then a3
    else if a == sp + 32 then b0 else if a == sp + 40 then b1
    else if a == sp + 48 then b2 else if a == sp + 56 then b3
    else if a == sp + 64 then n0 else if a == sp + 72 then n1
    else if a == sp + 80 then n2 else if a == sp + 88 then n3
    else 0
  code := loadProgram 0 addmodTestProgram
  pc := 0

/-- Run to the exit PC and return `(x12 − sp, result limbs at x12)`. The
    pointer delta must be 64 on every branch (pops 3, pushes 1). -/
def runResult (sp : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 : Word) :
    Option (Word × List Word) :=
  match stepUntilPc addmodExit 12000
      (mkState sp a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3) with
  | some s =>
    let r := s.getReg .x12
    some (r - sp, [s.getMem r, s.getMem (r + 8), s.getMem (r + 16), s.getMem (r + 24)])
  | none => none

-- Zero-modulus branch: ADDMOD(5, 7, 0) = 0.
#guard runResult 1024  5 0 0 0  7 0 0 0  0 0 0 0 = some (64, [0, 0, 0, 0])

-- No-carry branch: ADDMOD(100, 7, 9) = 107 % 9 = 8.
#guard runResult 1024  100 0 0 0  7 0 0 0  9 0 0 0 = some (64, [8, 0, 0, 0])

-- No-carry, multi-limb sum: ADDMOD(2^64 + 5, 2^64 + 6, 2^64 + 1)
--   = (2^65 + 11) % (2^64 + 1) = (2·(2^64+1) + 9) % (2^64+1) = 9.
#guard runResult 1024  5 1 0 0  6 1 0 0  1 1 0 0 = some (64, [9, 0, 0, 0])

-- Carry branch, the runtime-plan headline case:
--   ADDMOD(2^256 − 1, 1, 7) = 2^256 % 7 = 2.
#guard runResult 1024
  0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
  1 0 0 0
  7 0 0 0 = some (64, [2, 0, 0, 0])

-- Carry branch, single-limb N: ADDMOD(2^255, 2^255, 7) = 2^256 % 7 = 2
--   (r = 0, rMod = 0, result = m).
#guard runResult 1024
  0 0 0 0x8000000000000000
  0 0 0 0x8000000000000000
  7 0 0 0 = some (64, [2, 0, 0, 0])

-- Carry branch, wide 4-limb N (the v1/v4-buggy n=4 divisor regime):
--   ADDMOD(2^256 − 1, 2^256 − 1, 2^255) = (2^257 − 2) % 2^255 = 2^255 − 2.
#guard runResult 1024
  0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
  0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
  0 0 0 0x8000000000000000 =
  some (64, [0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF,
             0x7FFFFFFFFFFFFFFF])

-- Carry branch, zero result without subtract (take = 0 sub-path):
--   ADDMOD(2^256 − 1, 1, 2^255) = 2^256 % 2^255 = 0.
#guard runResult 1024
  0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
  1 0 0 0
  0 0 0 0x8000000000000000 = some (64, [0, 0, 0, 0])

-- Carry branch where the conditional subtract fires (s = m + rMod ≥ N):
--   ADDMOD(2^256 − 1, 2^256 − 1, 2^256 − 1) = (2·(2^256−1)) % (2^256−1) = 0.
--   Internals: m = 2^256 % (2^256−1) = 1, r = 2^256 − 2, rMod = 2^256 − 2,
--   s = m + rMod = 2^256 − 1 = N → subtract selected by the compare chain
--   (s ≥ N with no carry-out of the final add).
#guard runResult 1024
  0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
  0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
  0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF =
  some (64, [0, 0, 0, 0])

-- Carry branch, near-maximal N with no subtract:
--   ADDMOD(2^256 − 1, 2^256 − 2, 2^256 − 1): σ = 2^257 − 3 ≡ 2^256 − 2.
--   Internals: m = 2^256 % (2^256−1) = 1, r = 2^256 − 3, rMod = 2^256 − 3,
--   s = 2^256 − 2 < N → no subtract; result 2^256 − 2.
#guard runResult 1024
  0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
  0xFFFFFFFFFFFFFFFE 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
  0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF =
  some (64, [0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF,
             0xFFFFFFFFFFFFFFFF])

-- Carry branch, chained-borrow regression (the legacy runtime handler's
-- borrow-chain bug shape): N limbs [1, 5, 5, 8], operands chosen so the
-- conditional subtract computes s − N with s = [0, 5, 5, 9] — the borrow
-- from limb 0 must propagate through TWO equal middle limbs (per-limb
-- difference 0 with incoming borrow 1). The post-subtraction borrow test
-- (`sub x5,x5,x11; sltu x11,x5,x11`) drops the borrow here, yielding
-- [max, max, 0, 1] instead of the correct 2^192 − 1 = [max, max, max, 0].
#guard runResult 1024
  0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
  0x2000000000000000 0xa000000000000000 0xa000000000000000 0x1
  1 5 5 8 =
  some (64, [0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0])

-- Pure-oracle cross-checks: the same vectors against `EvmWord.addmod`.
example : (EvmWord.addmod 5 7 0) = 0 := by decide
example : (EvmWord.addmod 100 7 9).toNat = 8 := by decide
example :
    (EvmWord.addmod (BitVec.ofNat 256 (2 ^ 256 - 1)) 1 7).toNat = 2 := by
  decide
example :
    (EvmWord.addmod (BitVec.ofNat 256 (2 ^ 256 - 1)) (BitVec.ofNat 256 (2 ^ 256 - 1))
      (BitVec.ofNat 256 (2 ^ 255))).toNat = 2 ^ 255 - 2 := by decide

end EvmAsm.Evm64.AddModTest
