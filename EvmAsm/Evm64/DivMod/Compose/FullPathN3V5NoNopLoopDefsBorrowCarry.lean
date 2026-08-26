/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopLoopDefsBorrowCarry

  The borrow-conditional selected-carry bundle for the n=3 v5 loop:
  `loopN3SelectedBorrowCarryV5`.  Two obligations (j=1 then j=0), each of the
  form `borrow → carry` selected by the per-iteration trial flag (call ⇒
  `loopBodyN3CallAddbackCarry2NzV5`, max ⇒ `isAddbackCarry2NzN3Max`), over the
  iteration windows (j=1 over the raw window, j=0 over the first-iteration result
  `iterN3V5 bltu_1 …`).  This is the satisfiable-from-shape package the
  borrow-dispatched n=3 loop will consume — n3 mirror of
  `loopN2SelectedBorrowCarryV5` (FullPathN2V5NoNopLoopDefsBorrowCarry).
  Bead `evm-asm-wbc4i.9.3.3.3.4`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopUnified
public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5Families

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Borrow-conditional selected-carry bundle for the n=3 v5 loop (j=1 then j=0). -/
def loopN3SelectedBorrowCarryV5 (bltu_1 bltu_0 : Bool)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig : Word) : Prop :=
  let r1 := iterN3V5 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  (if bltu_1 then
    (BitVec.ult uTop
      (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) →
      loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
   else
    (BitVec.ult uTop
      (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) →
      isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)) ∧
  (if bltu_0 then
    (BitVec.ult r1.2.2.2.2.1
      (mulsubN4_c3 (divKTrialCallV5QHat r1.2.2.2.1 r1.2.2.1 v2)
        v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1) →
      loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 v3
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1)
   else
    (BitVec.ult r1.2.2.2.2.1
      (mulsubN4_c3 (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1) →
      isAddbackCarry2NzN3Max v0 v1 v2 v3
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1))

/-- Projection of the j=1 obligation. -/
theorem loopN3SelectedBorrowCarryV5.j1 {bltu_1 bltu_0 : Bool}
    {v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig : Word}
    (h : loopN3SelectedBorrowCarryV5 bltu_1 bltu_0 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) :
    (if bltu_1 then
      (BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) →
        loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
     else
      (BitVec.ult uTop
        (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) →
        isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)) :=
  h.1

/-- Projection of the j=0 obligation. -/
theorem loopN3SelectedBorrowCarryV5.j0 {bltu_1 bltu_0 : Bool}
    {v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig : Word}
    (h : loopN3SelectedBorrowCarryV5 bltu_1 bltu_0 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) :
    let r1 := iterN3V5 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    (if bltu_0 then
      (BitVec.ult r1.2.2.2.2.1
        (mulsubN4_c3 (divKTrialCallV5QHat r1.2.2.2.1 r1.2.2.1 v2)
          v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1) →
        loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 v3
          u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1)
     else
      (BitVec.ult r1.2.2.2.2.1
        (mulsubN4_c3 (signExtend12 4095 : Word)
          v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1) →
        isAddbackCarry2NzN3Max v0 v1 v2 v3
          u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1)) :=
  h.2

end EvmAsm.Evm64
