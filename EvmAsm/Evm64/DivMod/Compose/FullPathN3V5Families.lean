/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5Families

  N3 V5 iteration families: `iterN3V5` (the capped-trial per-iteration dispatch)
  and the two-digit `fullDivN3R1V5` / `fullDivN3R0V5` / `fullDivN3C3V5`.  These are
  the n=3 analogs of `FullPathN2V5Families` (`iterN2V5`, `fullDivN2R{2,1,0}V5`,
  `fullDivN2C3V5`) and of the v4 n=3 families (`fullDivN3R{1,0}V4`,
  `fullDivN3C3V4`), with the trial quotient supplied by the **capped** v5 callable
  `divKTrialCallV5QHat` (over the 3-limb normalized divisor's top limb `v2`)
  instead of the v4 `div128Quot`.  The n=3 loop runs two outer iterations
  (digits `r1`, `r0`).  Foundational layer for the v5 n=3 DIV lane.  Bead
  `evm-asm-wbc4i.9.3` (children 9.3.1/9.3.2/9.3.3).
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified
public import EvmAsm.Evm64.DivMod.LoopBody.TrialCallV5

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- V5 per-iteration computation (capped trial)
-- ============================================================================

/-- Unified per-iteration computation with double addback for n=3, **v5**: the
    trial quotient is the capped callable `divKTrialCallV5QHat u3 u2 v2` (the
    n=3 analog of `iterN2V5`, and the capped counterpart of `iterN3`/`iterN3Call`). -/
@[irreducible]
def iterN3V5 (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then
    iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
  else
    iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop

theorem iterN3V5_unfold {bltu : Bool} {v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    iterN3V5 bltu v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      (if bltu then
        iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop
      else
        iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  delta iterN3V5; rfl

-- ============================================================================
-- V5 two-digit iteration results
-- ============================================================================

/-- Digit-1 (first outer iteration) v5 result, over the normalized
    divisor/window. -/
@[irreducible]
def fullDivN3R1V5 (bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  iterN3V5 bltu_1 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word)

/-- Digit-0 (second outer iteration) v5 result, threaded on `fullDivN3R1V5`. -/
@[irreducible]
def fullDivN3R0V5 (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let r1 := fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  iterN3V5 bltu_0 v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

/-- Digit-0 mulsub borrow `c3` (the loop-exit `x10`), v5. -/
@[irreducible]
def fullDivN3C3V5 (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word :=
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let r1 := fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  if bltu_0 then
    (mulsubN4 (divKTrialCallV5QHat r1.2.2.2.1 r1.2.2.1 v.2.2.1)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  else
    (mulsubN4 (signExtend12 4095 : Word)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2

-- ============================================================================
-- Dispatch (`_eq`) lemmas
-- ============================================================================

theorem fullDivN3R1V5_eq (bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 =
      (let v := fullDivN3NormV b0 b1 b2 b3
       let u := fullDivN3NormU a0 a1 a2 a3 b2
       iterN3V5 bltu_1 v.1 v.2.1 v.2.2.1 v.2.2.2
         u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word)) := by
  delta fullDivN3R1V5; rfl

theorem fullDivN3R0V5_eq (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
      (let v := fullDivN3NormV b0 b1 b2 b3
       let u := fullDivN3NormU a0 a1 a2 a3 b2
       let r1 := fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
       iterN3V5 bltu_0 v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
         r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) := by
  delta fullDivN3R0V5; rfl

theorem fullDivN3R1V5_true (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN3R1V5 true a0 a1 a2 a3 b0 b1 b2 b3 =
      (let v := fullDivN3NormV b0 b1 b2 b3
       let u := fullDivN3NormU a0 a1 a2 a3 b2
       iterWithDoubleAddback (divKTrialCallV5QHat u.2.2.2.2 u.2.2.2.1 v.2.2.1)
         v.1 v.2.1 v.2.2.1 v.2.2.2 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word)) := by
  rw [fullDivN3R1V5_eq, iterN3V5_unfold]; simp

theorem fullDivN3R1V5_false (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN3R1V5 false a0 a1 a2 a3 b0 b1 b2 b3 =
      (let v := fullDivN3NormV b0 b1 b2 b3
       let u := fullDivN3NormU a0 a1 a2 a3 b2
       iterN3Max v.1 v.2.1 v.2.2.1 v.2.2.2 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word)) := by
  rw [fullDivN3R1V5_eq, iterN3V5_unfold]; simp

end EvmAsm.Evm64
