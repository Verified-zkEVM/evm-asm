/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Base

  Irreducible algorithm intermediates for n=2 full-path wrappers.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2LoopUnified

namespace EvmAsm.Evm64

open EvmAsm.Rv64

@[irreducible]
def fullDivN2Shift (b1 : Word) : Word :=
  (clzResult b1).1

@[irreducible]
def fullDivN2AntiShift (b1 : Word) : Word :=
  signExtend12 (0 : BitVec 12) - fullDivN2Shift b1

@[irreducible]
def fullDivN2NormV (b0 b1 b2 b3 : Word) : Word × Word × Word × Word :=
  let shift := fullDivN2Shift b1
  let antiShift := fullDivN2AntiShift b1
  (b0 <<< (shift.toNat % 64),
   (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64)),
   (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)),
   (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64)))

@[irreducible]
def fullDivN2NormU (a0 a1 a2 a3 b1 : Word) :
    Word × Word × Word × Word × Word :=
  let shift := fullDivN2Shift b1
  let antiShift := fullDivN2AntiShift b1
  (a0 <<< (shift.toNat % 64),
   (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64)),
   (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64)),
   (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64)),
   a3 >>> (antiShift.toNat % 64))

@[irreducible]
def fullDivN2R2 (bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  iterN2 bltu_2 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word)

@[irreducible]
def fullDivN2R1 (bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  iterN2 bltu_1 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1

@[irreducible]
def fullDivN2R0 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  iterN2 bltu_0 v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

@[irreducible]
def fullDivN2C3 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  if bltu_0 then
    (mulsubN4 (div128Quot r1.2.1 u.1 v.2.1)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  else
    (mulsubN4 (signExtend12 4095 : Word)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2

theorem fullDivN2Shift_unfold (b1 : Word) :
    fullDivN2Shift b1 = (clzResult b1).1 := by
  delta fullDivN2Shift
  rfl

theorem fullDivN2AntiShift_unfold (b1 : Word) :
    fullDivN2AntiShift b1 = signExtend12 (0 : BitVec 12) - fullDivN2Shift b1 := by
  delta fullDivN2AntiShift
  rfl

theorem fullDivN2NormV_unfold (b0 b1 b2 b3 : Word) :
    fullDivN2NormV b0 b1 b2 b3 =
    let shift := fullDivN2Shift b1
    let antiShift := fullDivN2AntiShift b1
    (b0 <<< (shift.toNat % 64),
     (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64)),
     (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)),
     (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))) := by
  delta fullDivN2NormV
  rfl

theorem fullDivN2NormU_unfold (a0 a1 a2 a3 b1 : Word) :
    fullDivN2NormU a0 a1 a2 a3 b1 =
    let shift := fullDivN2Shift b1
    let antiShift := fullDivN2AntiShift b1
    (a0 <<< (shift.toNat % 64),
     (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64)),
     (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64)),
     (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64)),
     a3 >>> (antiShift.toNat % 64)) := by
  delta fullDivN2NormU
  rfl

theorem fullDivN2R2_unfold (bltu_2 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    iterN2 bltu_2 v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) := by
  delta fullDivN2R2
  rfl

theorem fullDivN2R1_unfold (bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    iterN2 bltu_1 v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 := by
  delta fullDivN2R1
  rfl

theorem fullDivN2R0_unfold (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    iterN2 bltu_0 v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
      r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 := by
  delta fullDivN2R0
  rfl

theorem fullDivN2C3_unfold (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2C3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    if bltu_0 then
      (mulsubN4 (div128Quot r1.2.1 u.1 v.2.1)
        v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
    else
      (mulsubN4 (signExtend12 4095 : Word)
        v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2 := by
  delta fullDivN2C3
  rfl

end EvmAsm.Evm64
