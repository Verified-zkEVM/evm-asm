/-
  EvmAsm.Evm64.DivMod.LoopDefs.Iter

  Pure computations for the Knuth Algorithm D loop body:
    * mulsub / addback limb chains and carry helpers
    * div128 trial quotient + scratch helpers (div128Quot/DLo/Un0)
    * iterWithDoubleAddback + per-n iterN*Max/iterN*Call wrappers
    * Bool-dispatch unifiers iterN1/iterN2/iterN3 with _true/_false lemmas
    * Prop-level borrow/carry predicates (is*BorrowN*/isAddbackCarry2Nz*/Carry2NzAll)

  All defs here are `Word`-valued or `Prop`-valued — no `Assertion`s. Assertion
  postcondition defs live in `LoopDefs.Post`; precondition bundles in `LoopDefs.Bundle`.
-/

import EvmAsm.Evm64.DivMod.Compose.Base

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Mulsub computation: u - q*v for 4 limbs
-- Returns (un0, un1, un2, un3, c3) where c3 is the final carry.
-- ============================================================================

/-- Mulsub: compute u - q*v for 4 limbs, returning (un0, un1, un2, un3, c3). -/
def mulsubN4 (q v0 v1 v2 v3 u0 u1 u2 u3 : Word) :
    Word × Word × Word × Word × Word :=
  let p0_lo := q * v0; let p0_hi := rv64_mulhu q v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi
  let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q * v1; let p1_hi := rv64_mulhu q v1
  let fs1 := p1_lo + c0
  let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi
  let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q * v2; let p2_hi := rv64_mulhu q v2
  let fs2 := p2_lo + c1
  let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi
  let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q * v3; let p3_hi := rv64_mulhu q v3
  let fs3 := p3_lo + c2
  let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi
  let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  (un0, un1, un2, un3, c3)

/-- Addback: compute u + v for 4 limbs (used after mulsub underflow).
    Returns (aun0, aun1, aun2, aun3, aun4). -/
def addbackN4 (un0 un1 un2 un3 u4_new v0 v1 v2 v3 : Word) :
    Word × Word × Word × Word × Word :=
  let upc0 := un0 + (signExtend12 0 : Word)
  let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0 := upc0 + v0
  let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
  let aco0 := ac1_0 ||| ac2_0
  let upc1 := un1 + aco0
  let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
  let aun1 := upc1 + v1
  let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
  let aco1 := ac1_1 ||| ac2_1
  let upc2 := un2 + aco1
  let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
  let aun2 := upc2 + v2
  let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
  let aco2 := ac1_2 ||| ac2_2
  let upc3 := un3 + aco2
  let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
  let aun3 := upc3 + v3
  let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
  let aco3 := ac1_3 ||| ac2_3
  let aun4 := u4_new + aco3
  (aun0, aun1, aun2, aun3, aun4)

/-- Extract the 4-limb carry-out from addbackN4's intermediate computation.
    This is the carry out of the 4th limb (aco3), before the u4_new addition.
    Used by the double-addback check: if carry = 0, a second addback is needed. -/
def addbackN4_carry (un0 un1 un2 un3 v0 v1 v2 v3 : Word) : Word :=
  let upc0 := un0 + (signExtend12 0 : Word)
  let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0 := upc0 + v0
  let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
  let aco0 := ac1_0 ||| ac2_0
  let upc1 := un1 + aco0
  let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
  let aun1 := upc1 + v1
  let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
  let aco1 := ac1_1 ||| ac2_1
  let upc2 := un2 + aco1
  let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
  let aun2 := upc2 + v2
  let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
  let aco2 := ac1_2 ||| ac2_2
  let upc3 := un3 + aco2
  let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
  let aun3 := upc3 + v3
  let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
  ac1_3 ||| ac2_3

/-- The first four limbs of `addbackN4` do not depend on `u4_new`; only the fifth limb does. -/
theorem addbackN4_fst4_u4_indep (un0 un1 un2 un3 u4 u4' v0 v1 v2 v3 : Word) :
    (addbackN4 un0 un1 un2 un3 u4 v0 v1 v2 v3).1 =
      (addbackN4 un0 un1 un2 un3 u4' v0 v1 v2 v3).1 ∧
    (addbackN4 un0 un1 un2 un3 u4 v0 v1 v2 v3).2.1 =
      (addbackN4 un0 un1 un2 un3 u4' v0 v1 v2 v3).2.1 ∧
    (addbackN4 un0 un1 un2 un3 u4 v0 v1 v2 v3).2.2.1 =
      (addbackN4 un0 un1 un2 un3 u4' v0 v1 v2 v3).2.2.1 ∧
    (addbackN4 un0 un1 un2 un3 u4 v0 v1 v2 v3).2.2.2.1 =
      (addbackN4 un0 un1 un2 un3 u4' v0 v1 v2 v3).2.2.2.1 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The mulsub carry c3 for n=4, used in borrow conditions. -/
def mulsubN4_c3 (qHat v0 v1 v2 v3 u0 u1 u2 u3 : Word) : Word :=
  (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2

-- ============================================================================
-- div128 quotient computation (shared across all n-cases)
-- ============================================================================

/-- Trial quotient from the div128 subroutine: divides uHi:uLo by vTop. -/
def div128Quot (uHi uLo vTop : Word) : Word :=
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := uLo >>> (32 : BitVec 6).toNat
  let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
  (q1' <<< (32 : BitVec 6).toNat) ||| q0'

/-- Low 32 bits of vTop, stored to scratch during div128 call path. -/
def div128DLo (vTop : Word) : Word :=
  (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat

/-- Low 32 bits of uLo, stored to scratch during div128 call path. -/
def div128Un0 (uLo : Word) : Word :=
  (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat

-- ============================================================================
-- Double-addback iter variants (model the FIXED algorithm with double addback)
-- ============================================================================

/-- Helper: single iteration with double addback, parameterized by qHat.
    Used by all iter* variants. -/
def iterWithDoubleAddback (qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  if BitVec.ult uTop c3 then
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
    if carry = 0 then
      let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
      (qHat + signExtend12 4095 + signExtend12 4095,
       ab'.1, ab'.2.1, ab'.2.2.1, ab'.2.2.2.1, ab'.2.2.2.2)
    else
      (qHat + signExtend12 4095, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2.1, ab.2.2.2.2)
  else
    (qHat, ms.1, ms.2.1, ms.2.2.1, ms.2.2.2.1, uTop - c3)

-- Equation lemmas for iterWithDoubleAddback in each branch.
-- These avoid expanding the full definition inline; producers `rw` with them.

theorem iterWithDoubleAddback_borrow {qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hb : BitVec.ult uTop (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) :
    let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - ms.2.2.2.2) v0 v1 v2 v3
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
    iterWithDoubleAddback qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    if carry = 0 then
      (qHat + signExtend12 4095 + signExtend12 4095,
       ab'.1, ab'.2.1, ab'.2.2.1, ab'.2.2.2.1, ab'.2.2.2.2)
    else
      (qHat + signExtend12 4095, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2.1, ab.2.2.2.2) := by
  simp only [iterWithDoubleAddback, if_pos hb]

theorem iterWithDoubleAddback_no_borrow {qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hb : ¬BitVec.ult uTop (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) :
    let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
    iterWithDoubleAddback qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    (qHat, ms.1, ms.2.1, ms.2.2.1, ms.2.2.2.1, uTop - ms.2.2.2.2) := by
  simp only [iterWithDoubleAddback, if_neg hb]

@[irreducible] def iterN1Max (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[irreducible] def iterN1Call (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[irreducible] def iterN2Max (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[irreducible] def iterN2Call (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- Unified per-iteration computation with double addback for n=2. -/
def iterN2 (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
  else iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[simp]
theorem iterN2_true {v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    iterN2 true v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp [iterN2]

@[simp]
theorem iterN2_false {v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    iterN2 false v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp [iterN2]

@[irreducible] def iterN3Max (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[irreducible] def iterN3Call (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- Unified per-iteration computation with double addback for n=3. -/
def iterN3 (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
  else iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[simp]
theorem iterN3_true {v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    iterN3 true v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp [iterN3]

@[simp]
theorem iterN3_false {v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    iterN3 false v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp [iterN3]

-- ============================================================================
-- Unified per-iteration computation with double addback for n=1.
-- ============================================================================

def iterN1 (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
  else iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[simp]
theorem iterN1_true {v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    iterN1 true v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp [iterN1]

@[simp]
theorem iterN1_false {v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    iterN1 false v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp [iterN1]

-- ============================================================================
-- Borrow/carry predicates consumed by loop iter postconditions
-- ============================================================================

/-- Borrow condition for n=1 call+skip: mulsub doesn't overflow. -/
def isSkipBorrowN1Call (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := div128Quot u1 u0 v0
  (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word)

/-- Borrow condition for n=1 call+addback: mulsub overflows. -/
def isAddbackBorrowN1Call (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := div128Quot u1 u0 v0
  (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word)

/-- Double-addback progress for given qHat: if the first addback produces
    carry 0, the second addback must produce nonzero carry. -/
def isAddbackCarry2Nz (qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - ms.2.2.2.2) v0 v1 v2 v3
  addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3 = 0 →
    addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0

/-- Specialization of `isAddbackCarry2Nz` for n=1 call path, where
    `qHat = div128Quot u1 u0 v0`. -/
def isAddbackCarry2NzN1Call (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  isAddbackCarry2Nz (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- Specialization of `isAddbackCarry2Nz` for n=1 max path, where
    `qHat = signExtend12 4095` (i.e. 2^64-1). -/
def isAddbackCarry2NzN1Max (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  isAddbackCarry2Nz (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- Specialization of `isAddbackCarry2Nz` for n=2 call path, where
    `qHat = div128Quot u2 u1 v1`. -/
def isAddbackCarry2NzN2Call (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  isAddbackCarry2Nz (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- Specialization of `isAddbackCarry2Nz` for n=2 max path. -/
def isAddbackCarry2NzN2Max (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  isAddbackCarry2Nz (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- Specialization of `isAddbackCarry2Nz` for n=3 call path, where
    `qHat = div128Quot u3 u2 v2`. -/
def isAddbackCarry2NzN3Call (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  isAddbackCarry2Nz (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- Specialization of `isAddbackCarry2Nz` for n=3 max path. -/
def isAddbackCarry2NzN3Max (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  isAddbackCarry2Nz (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- Specialization of `isAddbackCarry2Nz` for n=4 call path, where
    `qHat = div128Quot uTop u3 v3`. -/
def isAddbackCarry2NzN4Call (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  isAddbackCarry2Nz (div128Quot uTop u3 v3) v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- Specialization of `isAddbackCarry2Nz` for n=4 max path. -/
def isAddbackCarry2NzN4Max (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  isAddbackCarry2Nz (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- Universal carry2-nz hypothesis for double-addback: for *any* trial quotient
    and *any* per-iteration (u, uTop) state, the second addback carry is
    nonzero whenever the first is zero.

    This is a placeholder threaded through the Loop*/Compose layers until the
    mathematical foundation of the double-addback fix is completed (Step 1 of
    the double-addback plan — overestimate bound on `div128Quot` + the Knuth
    (normalized divisor, max-path) overestimate bound). Any spec that invokes
    a per-iteration `*_unified_j*_spec` requiring `isAddbackCarry2Nz*` discharges
    its obligation by specializing this universal to the local qHat and state. -/
def Carry2NzAll (v0 v1 v2 v3 : Word) : Prop :=
  ∀ qHat u0 u1 u2 u3 uTop : Word,
    isAddbackCarry2Nz qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop


/-- Borrow condition for n=2 call+skip: mulsub doesn't overflow. -/
def isSkipBorrowN2Call (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := div128Quot u2 u1 v1
  (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word)

/-- Borrow condition for n=2 call+addback: mulsub overflows. -/
def isAddbackBorrowN2Call (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  let qHat := div128Quot u2 u1 v1
  (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word)


/-- j=0 BLTU condition for n=3 max path after j=1 max+skip: u3_j0 ≥ v2. -/
def isMaxBltuN3After_j1_skip (v0 v1 v2 v3 u0 u1 u2 u3 : Word) : Prop :=
  let qHat : Word := signExtend12 4095
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  ¬BitVec.ult ms.2.2.1 v2

/-- j=0 borrow=0 condition for n=3 max path after j=1 max+skip. -/
def isSkipBorrowN3After_j1_skip (v0 v1 v2 v3 u0 u1 u2 u3 u0Orig : Word) : Prop :=
  let qHat : Word := signExtend12 4095
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  (if BitVec.ult ms.2.2.2.1
      (mulsubN4_c3 qHat v0 v1 v2 v3 u0Orig ms.1 ms.2.1 ms.2.2.1)
    then (1 : Word) else 0) = (0 : Word)

end EvmAsm.Evm64
