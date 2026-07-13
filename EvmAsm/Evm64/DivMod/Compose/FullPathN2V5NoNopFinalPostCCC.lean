/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopFinalPostCCC

  v5 parallel of the call×call×call source-path infrastructure (aliases, bundled
  runtime conditions, compact final postcondition) from FullPathN2V4NoNopFinalPost.
  Mirror with the v5 trial accessors (`divKTrialCallV5*`) and the v5 direct
  double-addback carry2 form (the v4 `loopBodyN2CallAddbackCarry2NzV4` wrapper is
  v4-trial-specific).  Keeps the call×call×call combo theorem statement small.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.CallV5NoNop

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Opaque alias for the j=2 `iterWithDoubleAddback` result (call×call×call, v5). -/
@[irreducible]
def r2CCCN2V5 (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop

theorem r2CCCN2V5_eq (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    r2CCCN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta r2CCCN2V5; rfl

/-- Opaque alias for the j=1 `iterWithDoubleAddback` result (call×call×call, v5),
    parameterized on `r2 := r2CCCN2V5 ...`. -/
@[irreducible]
def r1CCCN2V5 (v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  let r2 := r2CCCN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  iterWithDoubleAddback (divKTrialCallV5QHat r2.2.2.1 r2.2.1 v1)
    v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1

theorem r1CCCN2V5_eq (v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop : Word) :
    r1CCCN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop =
      (let r2 := r2CCCN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
       iterWithDoubleAddback (divKTrialCallV5QHat r2.2.2.1 r2.2.1 v1)
         v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) := by
  delta r1CCCN2V5; rfl

/-- The v5 direct double-addback carry2 condition for a 2-limb call digit with
    trial window `(uHi,uLo,vTop)=(u2,u1,v1)` and dividend limbs `u0..u3,uTop`. -/
def callAddbackCarry2NzV5 (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := divKTrialCallV5QHat u2 u1 v1
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
  carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0

theorem callAddbackCarry2NzV5_unfold (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    callAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      (let qHat := divKTrialCallV5QHat u2 u1 v1
       let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
       let c3 := ms.2.2.2.2
       let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
       let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
       carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) := by
  delta callAddbackCarry2NzV5; rfl

/-- Compact final postcondition for the n=2 v5 call×call×call source path. -/
@[irreducible]
def loopN2CallCallCallSourceFinalPostNoX1V5 (sp base : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem : Word) :
    Assertion :=
  let r2 := r2CCCN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r1 := r1CCCN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
  let qHat0 := divKTrialCallV5QHat r1.2.2.1 r1.2.1 v1
  let dLo0 := divKTrialCallV5DLo v1
  let divUn00 := divKTrialCallV5Un0 r1.2.1
  let scratch2 := divKTrialCallV5ScratchOut u2 u1 v1 scratchMem
  let scratch1 := divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 v1 scratch2
  let scratch0 := divKTrialCallV5ScratchOut r1.2.2.1 r1.2.1 v1 scratch1
  let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  ((loopIterPostN2CallScratchNoX1 sp base (0 : Word)
    qHat0 dLo0 divUn00 scratch0
    v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
    (.x1 ↦ᵣ raVal)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
      (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
      (qAddr2 ↦ₘ r2.1))))

theorem loopN2CallCallCallSourceFinalPostNoX1V5_unfold (sp base : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem : Word) :
    loopN2CallCallCallSourceFinalPostNoX1V5 sp base
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 raVal scratchMem =
    let r2 := r2CCCN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1CCCN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let qHat0 := divKTrialCallV5QHat r1.2.2.1 r1.2.1 v1
    let dLo0 := divKTrialCallV5DLo v1
    let divUn00 := divKTrialCallV5Un0 r1.2.1
    let scratch2 := divKTrialCallV5ScratchOut u2 u1 v1 scratchMem
    let scratch1 := divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 v1 scratch2
    let scratch0 := divKTrialCallV5ScratchOut r1.2.2.1 r1.2.1 v1 scratch1
    let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    ((loopIterPostN2CallScratchNoX1 sp base (0 : Word)
      qHat0 dLo0 divUn00 scratch0
      v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
      (.x1 ↦ᵣ raVal)) **
      (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
        (qAddr1 ↦ₘ r1.1)) **
       ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
        (qAddr2 ↦ₘ r2.1)))) := by
  delta loopN2CallCallCallSourceFinalPostNoX1V5
  rfl

/-- Bundled runtime conditions for the n=2 v5 call×call×call source path. -/
@[irreducible]
def loopN2CallCallCallSourceCondsV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word) : Prop :=
  let r2 := r2CCCN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r1 := r1CCCN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
  BitVec.ult u2 v1 ∧
  callAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop ∧
  BitVec.ult r2.2.2.1 v1 ∧
  callAddbackCarry2NzV5 v0 v1 v2 v3
    u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 ∧
  BitVec.ult r1.2.2.1 v1 ∧
  callAddbackCarry2NzV5 v0 v1 v2 v3
    u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

theorem loopN2CallCallCallSourceCondsV5_unfold
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word) :
    loopN2CallCallCallSourceCondsV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 =
    let r2 := r2CCCN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1CCCN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    BitVec.ult u2 v1 ∧
    callAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop ∧
    BitVec.ult r2.2.2.1 v1 ∧
    callAddbackCarry2NzV5 v0 v1 v2 v3
      u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 ∧
    BitVec.ult r1.2.2.1 v1 ∧
    callAddbackCarry2NzV5 v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 := by
  delta loopN2CallCallCallSourceCondsV5
  rfl

end EvmAsm.Evm64
