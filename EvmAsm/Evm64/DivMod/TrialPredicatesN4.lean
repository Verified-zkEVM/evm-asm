/-
  Trial-path predicates shared by the n=4 DivMod composition and arithmetic
  proofs. Keeping these definitions below the full composition layer avoids
  making pure arithmetic lemmas depend on the complete RV64 proof pipeline.
-/

import EvmAsm.Evm64.DivMod.LoopDefs.CLZResult
import EvmAsm.Evm64.DivMod.LoopDefs.Iter

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Max trial quotient condition at n=4: u4 ≥ normalized b3 (BLTU not taken). -/
def isMaxTrialN4 (a3 b2 b3 : Word) : Prop :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u4 := a3 >>> (antiShift.toNat % 64)
  ¬BitVec.ult u4 b3'

/-- Call path condition: u4 < b3' (BLTU taken, use div128). -/
def isCallTrialN4 (a3 b2 b3 : Word) : Prop :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u4 := a3 >>> (antiShift.toNat % 64)
  BitVec.ult u4 b3'

/-- Skip addback condition at n=4 with max trial quotient: borrow = 0. -/
def isSkipBorrowN4Max (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat : Word := signExtend12 4095
  (if BitVec.ult u4 (mulsubN4_c3 qHat b0' b1' b2' b3' u0 u1 u2 u3)
   then (1 : Word) else 0) = (0 : Word)

/-- Skip addback condition at n=4 with call trial quotient. -/
def isSkipBorrowN4Call (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat := div128Quot u4 u3 b3'
  (if BitVec.ult u4 (mulsubN4_c3 qHat b0' b1' b2' b3' u0 u1 u2 u3)
   then (1 : Word) else 0) = (0 : Word)

/-- Addback condition at n=4 with call trial quotient. -/
def isAddbackBorrowN4Call (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat := div128Quot u4 u3 b3'
  (if BitVec.ult u4 (mulsubN4_c3 qHat b0' b1' b2' b3' u0 u1 u2 u3)
   then (1 : Word) else 0) ≠ (0 : Word)

end EvmAsm.Evm64
