/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Branches

  Branch-specialized unfold equations for the n=2 full-path intermediates.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Base

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem fullDivN2R2_false
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2R2 false a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    iterN2Max v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) := by
  rw [fullDivN2R2_unfold]
  simp only [iterN2_false]

theorem fullDivN2R2_true
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2R2 true a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    iterN2Call v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) := by
  rw [fullDivN2R2_unfold]
  simp only [iterN2_true]

theorem fullDivN2R1_false (bltu_2 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2R1 bltu_2 false a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    iterN2Max v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 := by
  rw [fullDivN2R1_unfold]
  simp only [iterN2_false]

theorem fullDivN2R1_true (bltu_2 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2R1 bltu_2 true a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    iterN2Call v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 := by
  rw [fullDivN2R1_unfold]
  simp only [iterN2_true]

theorem fullDivN2R0_false (bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2R0 bltu_2 bltu_1 false a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    iterN2Max v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
      r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 := by
  rw [fullDivN2R0_unfold]
  simp only [iterN2_false]

theorem fullDivN2R0_true (bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2R0 bltu_2 bltu_1 true a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    iterN2Call v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
      r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 := by
  rw [fullDivN2R0_unfold]
  simp only [iterN2_true]

theorem fullDivN2C3_false (bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2C3 bltu_2 bltu_1 false a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    (mulsubN4 (signExtend12 4095 : Word)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2 := by
  delta fullDivN2C3
  rfl

theorem fullDivN2C3_true (bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2C3 bltu_2 bltu_1 true a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    (mulsubN4 (div128Quot r1.2.1 u.1 v.2.1)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2 := by
  delta fullDivN2C3
  rfl

end EvmAsm.Evm64
