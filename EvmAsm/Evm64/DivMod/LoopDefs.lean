/-
  EvmAsm.Evm64.DivMod.LoopDefs

  Standalone computation definitions and postcondition bundles for the
  Knuth Algorithm D loop body. These extract let-chains from theorem types,
  enabling compact theorem statements and reducing elaboration overhead.

  Computation defs: mulsubN4, addbackN4 (tuple-returning functions)
  Postcondition: loopExitPostN4 (opaque Assertion for the loop exit state)
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

-- ============================================================================
-- Loop exit postcondition for n=4
-- Common assertion shape for both cpsBranch exits (taken/ntaken).
-- Parameterized by the final output values (un0_f..un3_f, u4_f, q_f, c3).
-- ============================================================================

/-- Loop exit postcondition for n=4. Both taken (loop-back) and ntaken (exit)
    paths produce this same assertion shape, differing only in the output values.
    Encapsulates u_base/j'/q_addr address computation + 21-atom assertion chain. -/
@[irreducible]
def loopExitPostN4 (sp j q_f c3 un0_f un1_f un2_f un3_f u4_f
    v0 v1 v2 v3 : Word) : Assertion :=
  let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let j' := j + signExtend12 4095
  let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
  (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
  (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
  (.x2 ↦ᵣ un3_f) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_f) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_f) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_f) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_f) **
  ((u_base + signExtend12 4064) ↦ₘ u4_f) **
  (q_addr ↦ₘ q_f)

theorem loopExitPostN4_unfold (sp j q_f c3 un0_f un1_f un2_f un3_f u4_f
    v0 v1 v2 v3 : Word) :
    loopExitPostN4 sp j q_f c3 un0_f un1_f un2_f un3_f u4_f v0 v1 v2 v3 =
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let j' := j + signExtend12 4095
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
    (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
    (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
    (.x2 ↦ᵣ un3_f) ** (.x0 ↦ᵣ (0 : Word)) **
    (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
    ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_f) **
    ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_f) **
    ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_f) **
    ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_f) **
    ((u_base + signExtend12 4064) ↦ₘ u4_f) **
    (q_addr ↦ₘ q_f) := by
  delta loopExitPostN4; rfl

-- ============================================================================
-- Composed postcondition: mulsub skip (borrow = 0) for n=4
-- Encapsulates the full mulsub computation + exit postcondition.
-- ============================================================================

/-- Full mulsub-skip postcondition for n=4 loop body.
    Computes mulsubN4 internally and produces the exit assertion. -/
@[irreducible]
def loopBodyN4SkipPost (sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  loopExitPostN4 sp j q_hat ms.2.2.2.2 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - ms.2.2.2.2) v0 v1 v2 v3

/-- Full mulsub-addback postcondition for n=4 loop body.
    Computes mulsubN4 + addbackN4 internally and produces the exit assertion. -/
@[irreducible]
def loopBodyN4AddbackPost (sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let un0 := ms.1; let un1 := ms.2.1; let un2 := ms.2.2.1
  let un3 := ms.2.2.2.1; let c3 := ms.2.2.2.2
  let u4_new := u_top - c3
  let ab := addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3
  loopExitPostN4 sp j (q_hat + signExtend12 4095) c3 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3

/-- The mulsub carry c3 for n=4, used in borrow conditions. -/
def mulsubN4_c3 (q_hat v0 v1 v2 v3 u0 u1 u2 u3 : Word) : Word :=
  (mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2

-- ============================================================================
-- Loop exit postcondition for n=1
-- Same assertion shape as n=4, but with (1 : Word) for the n-value cell.
-- ============================================================================

/-- Loop exit postcondition for n=1. -/
@[irreducible]
def loopExitPostN1 (sp j q_f c3 un0_f un1_f un2_f un3_f u4_f
    v0 v1 v2 v3 : Word) : Assertion :=
  let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let j' := j + signExtend12 4095
  let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
  (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
  (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
  (.x2 ↦ᵣ un3_f) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_f) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_f) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_f) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_f) **
  ((u_base + signExtend12 4064) ↦ₘ u4_f) **
  (q_addr ↦ₘ q_f)

/-- Full mulsub-skip postcondition for n=1 loop body. -/
@[irreducible]
def loopBodyN1SkipPost (sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  loopExitPostN1 sp j q_hat ms.2.2.2.2 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - ms.2.2.2.2) v0 v1 v2 v3

/-- Full mulsub-addback postcondition for n=1 loop body. -/
@[irreducible]
def loopBodyN1AddbackPost (sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let un0 := ms.1; let un1 := ms.2.1; let un2 := ms.2.2.1
  let un3 := ms.2.2.2.1; let c3 := ms.2.2.2.2
  let u4_new := u_top - c3
  let ab := addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3
  loopExitPostN1 sp j (q_hat + signExtend12 4095) c3 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3

-- ============================================================================
-- Unified per-iteration result for n=1 max path (BLTU not taken)
-- ============================================================================

/-- Per-iteration computation for n=1 when the trial quotient is max (BLTU not taken).
    Internally handles both skip (borrow=0) and addback (borrow≠0) paths.
    Returns (q_j, un0, un1, un2, un3, u4). -/
@[irreducible]
def iterN1Max (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  let q_hat : Word := signExtend12 4095
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  if BitVec.ult u_top c3 then
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
    (q_hat + signExtend12 4095, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2.1, ab.2.2.2.2)
  else
    (q_hat, ms.1, ms.2.1, ms.2.2.1, ms.2.2.2.1, u_top - c3)

/-- Unified postcondition for one n=1 max-path loop iteration.
    Uses iterN1Max to compute the result values, covering both skip and addback. -/
@[irreducible]
def loopIterPostN1Max (sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let r := iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let c3 := (mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN1 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3

/-- Unfold lemma for loopExitPostN1. -/
theorem loopExitPostN1_unfold (sp j q_f c3 un0_f un1_f un2_f un3_f u4_f v0 v1 v2 v3 : Word) :
    loopExitPostN1 sp j q_f c3 un0_f un1_f un2_f un3_f u4_f v0 v1 v2 v3 =
    (let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
     let j' := j + signExtend12 4095
     let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
     (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
     (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
     (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
     (.x2 ↦ᵣ un3_f) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_f) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_f) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_f) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_f) **
     ((u_base + signExtend12 4064) ↦ₘ u4_f) **
     (q_addr ↦ₘ q_f)) := by
  delta loopExitPostN1; rfl

-- ============================================================================
-- Loop exit postcondition for n=2
-- ============================================================================

/-- Loop exit postcondition for n=2. -/
@[irreducible]
def loopExitPostN2 (sp j q_f c3 un0_f un1_f un2_f un3_f u4_f
    v0 v1 v2 v3 : Word) : Assertion :=
  let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let j' := j + signExtend12 4095
  let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
  (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
  (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
  (.x2 ↦ᵣ un3_f) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_f) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_f) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_f) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_f) **
  ((u_base + signExtend12 4064) ↦ₘ u4_f) **
  (q_addr ↦ₘ q_f)

/-- Unfold the opaque `loopExitPostN2` back to its expanded form. -/
theorem loopExitPostN2_unfold (sp j q_f c3 un0_f un1_f un2_f un3_f u4_f
    v0 v1 v2 v3 : Word) :
    loopExitPostN2 sp j q_f c3 un0_f un1_f un2_f un3_f u4_f v0 v1 v2 v3 =
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let j' := j + signExtend12 4095
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
    (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
    (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
    (.x2 ↦ᵣ un3_f) ** (.x0 ↦ᵣ (0 : Word)) **
    (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
    ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_f) **
    ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_f) **
    ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_f) **
    ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_f) **
    ((u_base + signExtend12 4064) ↦ₘ u4_f) **
    (q_addr ↦ₘ q_f) := by
  delta loopExitPostN2; rfl

/-- Full mulsub-skip postcondition for n=2 loop body. -/
@[irreducible]
def loopBodyN2SkipPost (sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  loopExitPostN2 sp j q_hat ms.2.2.2.2 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - ms.2.2.2.2) v0 v1 v2 v3

/-- Full mulsub-addback postcondition for n=2 loop body. -/
@[irreducible]
def loopBodyN2AddbackPost (sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let un0 := ms.1; let un1 := ms.2.1; let un2 := ms.2.2.1
  let un3 := ms.2.2.2.1; let c3 := ms.2.2.2.2
  let u4_new := u_top - c3
  let ab := addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3
  loopExitPostN2 sp j (q_hat + signExtend12 4095) c3 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3

-- ============================================================================
-- Loop exit postcondition for n=3
-- ============================================================================

/-- Loop exit postcondition for n=3. -/
@[irreducible]
def loopExitPostN3 (sp j q_f c3 un0_f un1_f un2_f un3_f u4_f
    v0 v1 v2 v3 : Word) : Assertion :=
  let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let j' := j + signExtend12 4095
  let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
  (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
  (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
  (.x2 ↦ᵣ un3_f) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_f) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_f) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_f) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_f) **
  ((u_base + signExtend12 4064) ↦ₘ u4_f) **
  (q_addr ↦ₘ q_f)

theorem loopExitPostN3_unfold (sp j q_f c3 un0_f un1_f un2_f un3_f u4_f
    v0 v1 v2 v3 : Word) :
    loopExitPostN3 sp j q_f c3 un0_f un1_f un2_f un3_f u4_f v0 v1 v2 v3 =
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let j' := j + signExtend12 4095
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
    (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
    (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_f) **
    (.x2 ↦ᵣ un3_f) ** (.x0 ↦ᵣ (0 : Word)) **
    (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
    ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0_f) **
    ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1_f) **
    ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2_f) **
    ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3_f) **
    ((u_base + signExtend12 4064) ↦ₘ u4_f) **
    (q_addr ↦ₘ q_f) := by
  delta loopExitPostN3; rfl

/-- Full mulsub-skip postcondition for n=3 loop body. -/
@[irreducible]
def loopBodyN3SkipPost (sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  loopExitPostN3 sp j q_hat ms.2.2.2.2 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - ms.2.2.2.2) v0 v1 v2 v3

theorem loopBodyN3SkipPost_unfold (sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    loopBodyN3SkipPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
    loopExitPostN3 sp j q_hat ms.2.2.2.2 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - ms.2.2.2.2) v0 v1 v2 v3 := by
  delta loopBodyN3SkipPost; rfl

/-- Full mulsub-addback postcondition for n=3 loop body. -/
@[irreducible]
def loopBodyN3AddbackPost (sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let un0 := ms.1; let un1 := ms.2.1; let un2 := ms.2.2.1
  let un3 := ms.2.2.2.1; let c3 := ms.2.2.2.2
  let u4_new := u_top - c3
  let ab := addbackN4 un0 un1 un2 un3 u4_new v0 v1 v2 v3
  loopExitPostN3 sp j (q_hat + signExtend12 4095) c3 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3

-- ============================================================================
-- div128 quotient computation (shared across all n-cases)
-- ============================================================================

/-- Trial quotient from the div128 subroutine: divides u_hi:u_lo by v_top. -/
def div128Quot (u_hi u_lo v_top : Word) : Word :=
  let d_hi := v_top >>> (32 : BitVec 6).toNat
  let d_lo := (v_top <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u_lo >>> (32 : BitVec 6).toNat
  let div_un0 := (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u_hi d_hi
  let rhat := u_hi - q1 * d_hi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + d_hi
  let q_dlo := q1c * d_lo
  let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * d_lo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 d_hi
  let rhat2 := un21 - q0 * d_hi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
  let q0_dlo := q0c * d_lo
  let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
  (q1' <<< (32 : BitVec 6).toNat) ||| q0'

/-- Low 32 bits of v_top, stored to scratch during div128 call path. -/
def div128DLo (v_top : Word) : Word :=
  (v_top <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat

/-- Low 32 bits of u_lo, stored to scratch during div128 call path. -/
def div128Un0 (u_lo : Word) : Word :=
  (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat

-- ============================================================================
-- Call path postconditions for n=3 (includes div128 scratch cells)
-- ============================================================================

/-- Call+skip postcondition for n=3 loop body at j=0.
    Bundles div128Quot computation + loopBodyN3SkipPost + scratch cells. -/
@[irreducible]
def loopBodyN3CallSkipPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let q_hat := div128Quot u3 u2 v2
  loopBodyN3SkipPost sp (0 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

/-- Call+addback postcondition for n=3 loop body at j=0.
    Bundles div128Quot computation + loopBodyN3AddbackPost + scratch cells. -/
@[irreducible]
def loopBodyN3CallAddbackPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let q_hat := div128Quot u3 u2 v2
  loopBodyN3AddbackPost sp (0 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

/-- Borrow condition for n=3 call+skip: mulsub doesn't overflow. -/
def isSkipBorrowN3Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Prop :=
  let q_hat := div128Quot u3 u2 v2
  (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word)

/-- Borrow condition for n=3 call+addback: mulsub overflows. -/
def isAddbackBorrowN3Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Prop :=
  let q_hat := div128Quot u3 u2 v2
  (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word)

-- ============================================================================
-- Generic j versions of call path postconditions (for multi-iteration loops)
-- ============================================================================

/-- Call+skip postcondition for n=3 loop body, generic j.
    Bundles div128Quot computation + loopBodyN3SkipPost + scratch cells. -/
@[irreducible]
def loopBodyN3CallSkipPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let q_hat := div128Quot u3 u2 v2
  loopBodyN3SkipPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

/-- Call+addback postcondition for n=3 loop body, generic j.
    Bundles div128Quot computation + loopBodyN3AddbackPost + scratch cells. -/
@[irreducible]
def loopBodyN3CallAddbackPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let q_hat := div128Quot u3 u2 v2
  loopBodyN3AddbackPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

-- ============================================================================
-- Two-iteration loop precondition for n=3
-- ============================================================================

/-- Precondition for the n=3 two-iteration loop (base+448 → base+904).
    Bundles registers, v-cells, u-cells at j=1 base, and extra j=0 cells. -/
@[irreducible]
def loopN3Pre (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word) : Assertion :=
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
  (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
  (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
  (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_1 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_1 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_1 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_1 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_1 + signExtend12 4064) ↦ₘ u_top) **
  (q_addr_1 ↦ₘ q1_old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0_orig) **
  (q_addr_0 ↦ₘ q0_old)

-- ============================================================================
-- Unified per-iteration result for n=3 max path (BLTU not taken)
-- ============================================================================

/-- Per-iteration computation for n=3 when the trial quotient is max (BLTU not taken).
    Internally handles both skip (borrow=0) and addback (borrow≠0) paths.
    Returns (q_j, un0, un1, un2, un3, u4). -/
def iterN3Max (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  let q_hat : Word := signExtend12 4095
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  if BitVec.ult u_top c3 then
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
    (q_hat + signExtend12 4095, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2.1, ab.2.2.2.2)
  else
    (q_hat, ms.1, ms.2.1, ms.2.2.1, ms.2.2.2.1, u_top - c3)

/-- Unified postcondition for one n=3 max-path loop iteration.
    Uses iterN3Max to compute the result values, covering both skip and addback. -/
@[irreducible]
def loopIterPostN3Max (sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let r := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let c3 := (mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN3 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3

-- ============================================================================
-- Two-iteration loop postconditions for n=3 (max path, unified)
-- ============================================================================

/-- Postcondition for the full n=3 two-iteration loop (both iterations max path).
    Uses iterN3Max for each iteration to handle all skip/addback combinations. -/
@[irreducible]
def loopN3MaxPost (sp v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig : Word) : Assertion :=
  let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3
    u0_orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1)

-- ============================================================================
-- Unified per-iteration result for n=1 call path (BLTU taken)
-- ============================================================================

/-- Per-iteration computation for n=1 when the trial quotient comes from div128 (BLTU taken).
    For n=1: div128 uses u_hi=u1, u_lo=u0, v_top=v0.
    Internally handles both skip (borrow=0) and addback (borrow≠0) paths.
    Returns (q_j, un0, un1, un2, un3, u4). -/
@[irreducible]
def iterN1Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  let q_hat := div128Quot u1 u0 v0
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  if BitVec.ult u_top c3 then
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
    (q_hat + signExtend12 4095, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2.1, ab.2.2.2.2)
  else
    (q_hat, ms.1, ms.2.1, ms.2.2.1, ms.2.2.2.1, u_top - c3)

/-- Unified postcondition for one n=1 call-path loop iteration.
    Uses iterN1Call for the result values, plus div128 scratch cells.
    For n=1: scratch uses v0/div128DLo v0/div128Un0 u0. -/
@[irreducible]
def loopIterPostN1Call (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let r := iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let q_hat := div128Quot u1 u0 v0
  let c3 := (mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN1 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3 **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u0)

/-- Borrow condition for n=1 call+skip: mulsub doesn't overflow. -/
def isSkipBorrowN1Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Prop :=
  let q_hat := div128Quot u1 u0 v0
  (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word)

/-- Borrow condition for n=1 call+addback: mulsub overflows. -/
def isAddbackBorrowN1Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Prop :=
  let q_hat := div128Quot u1 u0 v0
  (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word)

-- ============================================================================
-- Generic j versions of n=1 call path postconditions
-- ============================================================================

/-- Call+skip postcondition for n=1 loop body, generic j.
    Bundles div128Quot computation + loopBodyN1SkipPost + scratch cells.
    For n=1: div128 uses u_hi=u1, u_lo=u0, v_top=v0. -/
@[irreducible]
def loopBodyN1CallSkipPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let q_hat := div128Quot u1 u0 v0
  loopBodyN1SkipPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u0)

/-- Call+addback postcondition for n=1 loop body, generic j.
    Bundles div128Quot computation + loopBodyN1AddbackPost + scratch cells. -/
@[irreducible]
def loopBodyN1CallAddbackPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let q_hat := div128Quot u1 u0 v0
  loopBodyN1AddbackPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u0)

-- ============================================================================
-- Unified (Bool-parameterized) per-iteration for n=1
-- ============================================================================

/-- Unified per-iteration computation for n=1.
    `bltu = true` means BLTU taken (call path, trial quotient from div128).
    `bltu = false` means BLTU not taken (max path, trial quotient = 0xFFF).
    For n=1: div128 uses u_hi=u1, u_lo=u0, v_top=v0. -/
def iterN1 (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  else iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top

@[simp]
theorem iterN1_true (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    iterN1 true v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  simp [iterN1]

@[simp]
theorem iterN1_false (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    iterN1 false v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  simp [iterN1]

/-- Unified per-iteration postcondition for n=1.
    Same structure as loopIterPostN2 but delegates to loopIterPostN1Call/Max. -/
@[irreducible]
def loopIterPostN1 (bltu : Bool) (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  match bltu with
  | true => loopIterPostN1Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top
  | false => loopIterPostN1Max sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top ** empAssertion

@[simp] theorem loopIterPostN1_call (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    loopIterPostN1 true sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    loopIterPostN1Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  delta loopIterPostN1; rfl

@[simp] theorem loopIterPostN1_max (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    loopIterPostN1 false sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    (loopIterPostN1Max sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top ** empAssertion) := by
  delta loopIterPostN1; rfl

-- ============================================================================
-- Unified per-iteration result for n=3 call path (BLTU taken)
-- ============================================================================

/-- Per-iteration computation for n=3 when the trial quotient comes from div128 (BLTU taken).
    Internally handles both skip (borrow=0) and addback (borrow≠0) paths.
    Returns (q_j, un0, un1, un2, un3, u4). -/
def iterN3Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  let q_hat := div128Quot u3 u2 v2
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  if BitVec.ult u_top c3 then
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
    (q_hat + signExtend12 4095, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2.1, ab.2.2.2.2)
  else
    (q_hat, ms.1, ms.2.1, ms.2.2.1, ms.2.2.2.1, u_top - c3)

/-- Unified postcondition for one n=3 call-path loop iteration.
    Uses iterN3Call for the result values, plus div128 scratch cells. -/
@[irreducible]
def loopIterPostN3Call (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let r := iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let q_hat := div128Quot u3 u2 v2
  let c3 := (mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN3 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3 **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

-- ============================================================================
-- Two-iteration loop precondition/postcondition for n=3 (call path)
-- ============================================================================

/-- Precondition for the n=3 two-iteration loop with scratch cells.
    Used when at least one iteration takes the call (div128) path. -/
@[irreducible]
def loopN3PreWithScratch (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
    ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  loopN3Pre sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old **
  (sp + signExtend12 3968 ↦ₘ ret_mem) **
  (sp + signExtend12 3960 ↦ₘ d_mem) **
  (sp + signExtend12 3952 ↦ₘ dlo_mem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

/-- Postcondition for the full n=3 two-iteration loop (both iterations call path).
    Uses iterN3Call for each iteration. Scratch cells have j=0's values. -/
@[irreducible]
def loopN3CallCallPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig : Word) : Assertion :=
  let r1 := iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN3Call sp base (0 : Word) v0 v1 v2 v3
    u0_orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1)

/-- Postcondition for n=3 two-iteration loop (j=1 max, j=0 call).
    Scratch cells have j=0's call values. -/
@[irreducible]
def loopN3MaxCallPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig : Word) : Assertion :=
  let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN3Call sp base (0 : Word) v0 v1 v2 v3
    u0_orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1)

/-- Postcondition for n=3 two-iteration loop (j=1 call, j=0 max).
    Scratch cells have j=1's call values (unchanged by j=0 max path). -/
@[irreducible]
def loopN3CallMaxPost (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig : Word) : Assertion :=
  let r1 := iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3
    u0_orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u2)

-- ============================================================================
-- Unified per-iteration result for n=2 max path (BLTU not taken)
-- ============================================================================

/-- Per-iteration computation for n=2 when the trial quotient is max (BLTU not taken).
    Internally handles both skip (borrow=0) and addback (borrow≠0) paths.
    Returns (q_j, un0, un1, un2, un3, u4). -/
@[irreducible]
def iterN2Max (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  let q_hat : Word := signExtend12 4095
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  if BitVec.ult u_top c3 then
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
    (q_hat + signExtend12 4095, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2.1, ab.2.2.2.2)
  else
    (q_hat, ms.1, ms.2.1, ms.2.2.1, ms.2.2.2.1, u_top - c3)

/-- Unified postcondition for one n=2 max-path loop iteration.
    Uses iterN2Max to compute the result values, covering both skip and addback. -/
@[irreducible]
def loopIterPostN2Max (sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let r := iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let c3 := (mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN2 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3

-- ============================================================================
-- Unified per-iteration result for n=2 call path (BLTU taken)
-- ============================================================================

/-- Per-iteration computation for n=2 when the trial quotient comes from div128 (BLTU taken).
    For n=2: div128 uses u_hi=u2, u_lo=u1, v_top=v1.
    Internally handles both skip (borrow=0) and addback (borrow≠0) paths.
    Returns (q_j, un0, un1, un2, un3, u4). -/
@[irreducible]
def iterN2Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  let q_hat := div128Quot u2 u1 v1
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  if BitVec.ult u_top c3 then
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
    (q_hat + signExtend12 4095, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2.1, ab.2.2.2.2)
  else
    (q_hat, ms.1, ms.2.1, ms.2.2.1, ms.2.2.2.1, u_top - c3)

/-- Unified postcondition for one n=2 call-path loop iteration.
    Uses iterN2Call for the result values, plus div128 scratch cells. -/
@[irreducible]
def loopIterPostN2Call (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let r := iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let q_hat := div128Quot u2 u1 v1
  let c3 := (mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN2 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3 **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v1) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u1)

/-- Borrow condition for n=2 call+skip: mulsub doesn't overflow. -/
def isSkipBorrowN2Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Prop :=
  let q_hat := div128Quot u2 u1 v1
  (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word)

/-- Borrow condition for n=2 call+addback: mulsub overflows. -/
def isAddbackBorrowN2Call (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Prop :=
  let q_hat := div128Quot u2 u1 v1
  (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word)

-- ============================================================================
-- Generic j versions of n=2 call path postconditions
-- ============================================================================

/-- Call+skip postcondition for n=2 loop body, generic j.
    Bundles div128Quot computation + loopBodyN2SkipPost + scratch cells.
    For n=2: div128 uses u_hi=u2, u_lo=u1, v_top=v1. -/
@[irreducible]
def loopBodyN2CallSkipPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let q_hat := div128Quot u2 u1 v1
  loopBodyN2SkipPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v1) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u1)

/-- Call+addback postcondition for n=2 loop body, generic j.
    Bundles div128Quot computation + loopBodyN2AddbackPost + scratch cells. -/
@[irreducible]
def loopBodyN2CallAddbackPostJ (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  let q_hat := div128Quot u2 u1 v1
  loopBodyN2AddbackPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ v1) **
  (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 u1)

-- ============================================================================
-- Legacy two-iteration postconditions (max+skip × max+skip specific case)
-- ============================================================================

/-- Postcondition for the full n=3 two-iteration loop (max+skip at both j=1 and j=0).
    Includes the j=0 exit postcondition plus j=1's carried frame atoms (u4_new, q[1]). -/
@[irreducible]
def loopN3MaxSkipSkipPost (sp v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig : Word) : Assertion :=
  let q_hat : Word := signExtend12 4095
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  loopBodyN3SkipPost sp (0 : Word) q_hat v0 v1 v2 v3
    u0_orig ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 **
  ((u_base_1 + signExtend12 4064) ↦ₘ (u_top - ms.2.2.2.2)) **
  (q_addr_1 ↦ₘ q_hat)

/-- j=0 BLTU condition for n=3 max path after j=1 max+skip: u3_j0 ≥ v2. -/
def isMaxBltuN3After_j1_skip (v0 v1 v2 v3 u0 u1 u2 u3 : Word) : Prop :=
  let q_hat : Word := signExtend12 4095
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  ¬BitVec.ult ms.2.2.1 v2

/-- j=0 borrow=0 condition for n=3 max path after j=1 max+skip. -/
def isSkipBorrowN3After_j1_skip (v0 v1 v2 v3 u0 u1 u2 u3 u0_orig : Word) : Prop :=
  let q_hat : Word := signExtend12 4095
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  (if BitVec.ult ms.2.2.2.1
      (mulsubN4_c3 q_hat v0 v1 v2 v3 u0_orig ms.1 ms.2.1 ms.2.2.1)
    then (1 : Word) else 0) = (0 : Word)

-- ============================================================================
-- Unified (Bool-parameterized) per-iteration computation for n=3
-- Issue #262: Unify max/call branch paths via Bool parameter
-- ============================================================================

/-- Unified per-iteration computation for n=3.
    `bltu = true` means BLTU taken (call path, trial quotient from div128).
    `bltu = false` means BLTU not taken (max path, trial quotient = 0xFFF).
    Internally handles both skip and addback via iterN3Call/iterN3Max. -/
def iterN3 (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  else iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top

@[simp]
theorem iterN3_true (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    iterN3 true v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  simp [iterN3]

@[simp]
theorem iterN3_false (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    iterN3 false v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  simp [iterN3]

/-- Unified per-iteration postcondition for n=3.
    Delegates to loopIterPostN3Call (call path) or loopIterPostN3Max (max path).
    When `bltu = true` (call path), includes div128 scratch cells.
    When `bltu = false` (max path), appends empAssertion (stripped by sepConj_emp_right'). -/
@[irreducible]
def loopIterPostN3 (bltu : Bool) (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  match bltu with
  | true => loopIterPostN3Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top
  | false => loopIterPostN3Max sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top ** empAssertion

@[simp] theorem loopIterPostN3_call (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    loopIterPostN3 true sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    loopIterPostN3Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  delta loopIterPostN3; rfl

@[simp] theorem loopIterPostN3_max (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    loopIterPostN3 false sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    (loopIterPostN3Max sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top ** empAssertion) := by
  delta loopIterPostN3; rfl

-- ============================================================================
-- Unified two-iteration loop postcondition for n=3
-- ============================================================================

/-- Unified postcondition for the n=3 two-iteration loop.
    `bltu_1` is the BLTU outcome at j=1, `bltu_0` at j=0.
    Delegates to existing per-path postconditions via match.
    For max×max, scratch cells pass through unchanged (carried as parameters).
    For other combinations, scratch cells are overwritten by div128 (params unused). -/
@[irreducible]
def loopN3UnifiedPost (bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  match bltu_1, bltu_0 with
  | false, false =>
    loopN3MaxPost sp v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig **
    (sp + signExtend12 3968 ↦ₘ ret_mem) **
    (sp + signExtend12 3960 ↦ₘ d_mem) **
    (sp + signExtend12 3952 ↦ₘ dlo_mem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | true,  true  => loopN3CallCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig
  | false, true  => loopN3MaxCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig
  | true,  false => loopN3CallMaxPost sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig

-- ============================================================================
-- Unified (Bool-parameterized) per-iteration computation for n=2
-- Issue #262: Same pattern as n=3 but div128 uses u2/u1/v1
-- ============================================================================

/-- Unified per-iteration computation for n=2.
    `bltu = true` means BLTU taken (call path, trial quotient from div128).
    `bltu = false` means BLTU not taken (max path, trial quotient = 0xFFF).
    For n=2: div128 uses u_hi=u2, u_lo=u1, v_top=v1. -/
def iterN2 (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  else iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top

@[simp]
theorem iterN2_true (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    iterN2 true v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  simp [iterN2]

@[simp]
theorem iterN2_false (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    iterN2 false v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  simp [iterN2]

/-- Unified per-iteration postcondition for n=2.
    Same structure as loopIterPostN3 but delegates to loopIterPostN2Call/Max. -/
@[irreducible]
def loopIterPostN2 (bltu : Bool) (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) : Assertion :=
  match bltu with
  | true => loopIterPostN2Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top
  | false => loopIterPostN2Max sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top ** empAssertion

@[simp] theorem loopIterPostN2_call (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    loopIterPostN2 true sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    loopIterPostN2Call sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
  delta loopIterPostN2; rfl

@[simp] theorem loopIterPostN2_max (sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    loopIterPostN2 false sp base j v0 v1 v2 v3 u0 u1 u2 u3 u_top =
    (loopIterPostN2Max sp j v0 v1 v2 v3 u0 u1 u2 u3 u_top ** empAssertion) := by
  delta loopIterPostN2; rfl

-- ============================================================================
-- Three-iteration loop precondition/postcondition for n=2
-- Issue #262: Bool-parameterized composition for 3 iterations (j=2,1,0)
-- ============================================================================

/-- Precondition for the n=2 three-iteration loop (j starts at 2).
    Includes j=2's iteration precondition plus pre-existing atoms
    for j=1 (u0_orig_1, q1_old) and j=0 (u0_orig_0, q0_old). -/
@[irreducible]
def loopN2Pre (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_1 u0_orig_0
    q2_old q1_old q0_old : Word) : Assertion :=
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (2 : Word)) **
  (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
  (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
  (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_2 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_2 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_2 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_2 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_2 + signExtend12 4064) ↦ₘ u_top) **
  (q_addr_2 ↦ₘ q2_old) **
  ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) **
  (q_addr_1 ↦ₘ q1_old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) **
  (q_addr_0 ↦ₘ q0_old)

/-- Precondition for n=2 three-iteration loop with scratch cells.
    Used when at least one iteration may take the call (div128) path. -/
@[irreducible]
def loopN2PreWithScratch (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_1 u0_orig_0
    q2_old q1_old q0_old
    ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  loopN2Pre sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_1 u0_orig_0 q2_old q1_old q0_old **
  (sp + signExtend12 3968 ↦ₘ ret_mem) **
  (sp + signExtend12 3960 ↦ₘ d_mem) **
  (sp + signExtend12 3952 ↦ₘ dlo_mem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

-- ============================================================================
-- Two-iteration (j=1, j=0) precondition/postcondition for n=2
-- Mirrors loopN3Pre/loopN3UnifiedPost but with n=2 values
-- ============================================================================

/-- Precondition for n=2 two-iteration loop (j=1, j=0).
    Same structure as loopN3Pre but with n_mem = 2. -/
@[irreducible]
def loopN2Iter10Pre (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word) : Assertion :=
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
  (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
  (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
  (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_1 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_1 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_1 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_1 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_1 + signExtend12 4064) ↦ₘ u_top) **
  (q_addr_1 ↦ₘ q1_old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0_orig) **
  (q_addr_0 ↦ₘ q0_old)

/-- Precondition for n=2 two-iteration loop with scratch cells. -/
@[irreducible]
def loopN2Iter10PreWithScratch (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
    ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  loopN2Iter10Pre sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old **
  (sp + signExtend12 3968 ↦ₘ ret_mem) **
  (sp + signExtend12 3960 ↦ₘ d_mem) **
  (sp + signExtend12 3952 ↦ₘ dlo_mem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

/-- Unified postcondition for n=2 two-iteration loop (j=1, j=0).
    Same structure as loopN3UnifiedPost but without j=2 carried atoms.
    Scratch handling: call path includes scratch, max path carries passthrough params. -/
@[irreducible]
def loopN2Iter10Post (bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig
     ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  let r1 := iterN2 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  -- j=0 iteration postcondition (includes scratch if bltu_0 = true)
  loopIterPostN2 bltu_0 sp base (0 : Word) v0 v1 v2 v3
    u0_orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  -- Carried atoms from j=1
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  -- Scratch cells
  match bltu_1, bltu_0 with
  | false, false =>
    (sp + signExtend12 3968 ↦ₘ ret_mem) **
    (sp + signExtend12 3960 ↦ₘ d_mem) **
    (sp + signExtend12 3952 ↦ₘ dlo_mem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | false, true  => empAssertion
  | true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v1) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u1)
  | true,  true  => empAssertion

/-- Unified postcondition for the n=2 three-iteration loop.
    Parameterized by `(bltu_2 bltu_1 bltu_0 : Bool)` covering all 8 path combinations.

    Structure:
    - j=0 iteration postcondition (includes scratch when bltu_0 = true)
    - Carried atoms from j=1 (u4, q) and j=2 (u4, q)
    - Scratch cells: depend on which iteration was the last call path
      - All max (F,F,F): passthrough original scratch params
      - bltu_0=true: scratch handled inside loopIterPostN2Call (empAssertion here)
      - Last call was j=1 (bltu_1=T, bltu_0=F): scratch from j=1's div128
      - Last call was j=2 (bltu_2=T, others F): scratch from j=2's div128 -/
@[irreducible]
def loopN2UnifiedPost (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top
     u0_orig_1 u0_orig_0
     ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  -- Compute iteration results
  let r2 := iterN2 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let r1 := iterN2 bltu_1 v0 v1 v2 v3 u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  -- Address bases for carried atoms
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  -- j=0 iteration postcondition (includes scratch if bltu_0 = true)
  loopIterPostN2 bltu_0 sp base (0 : Word) v0 v1 v2 v3
    u0_orig_0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  -- Carried atoms from j=1 and j=2
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  ((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1) **
  -- Scratch cells
  match bltu_2, bltu_1, bltu_0 with
  | false, false, false =>
    (sp + signExtend12 3968 ↦ₘ ret_mem) **
    (sp + signExtend12 3960 ↦ₘ d_mem) **
    (sp + signExtend12 3952 ↦ₘ dlo_mem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | false, false, true  => empAssertion
  | false, true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v1) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 r2.2.1)
  | false, true,  true  => empAssertion
  | true,  false, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v1) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u1)
  | true,  false, true  => empAssertion
  | true,  true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v1) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 r2.2.1)
  | true,  true,  true  => empAssertion

-- ============================================================================
-- Four-iteration loop precondition/postcondition for n=1
-- Issue #262: Bool-parameterized composition for 4 iterations (j=3,2,1,0)
-- ============================================================================

/-- Precondition for the n=1 four-iteration loop (j starts at 3).
    Includes j=3's iteration precondition plus pre-existing atoms
    for j=2 (u0_orig_2, q2_old), j=1 (u0_orig_1, q1_old), and j=0 (u0_orig_0, q0_old). -/
@[irreducible]
def loopN1Pre (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_2 u0_orig_1 u0_orig_0
    q3_old q2_old q1_old q0_old : Word) : Assertion :=
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (3 : Word)) **
  (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
  (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
  (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_3 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_3 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_3 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_3 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_3 + signExtend12 4064) ↦ₘ u_top) **
  (q_addr_3 ↦ₘ q3_old) **
  ((u_base_2 + signExtend12 0) ↦ₘ u0_orig_2) **
  (q_addr_2 ↦ₘ q2_old) **
  ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) **
  (q_addr_1 ↦ₘ q1_old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) **
  (q_addr_0 ↦ₘ q0_old)

/-- Precondition for n=1 four-iteration loop with scratch cells.
    Used when at least one iteration may take the call (div128) path. -/
@[irreducible]
def loopN1PreWithScratch (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_2 u0_orig_1 u0_orig_0
    q3_old q2_old q1_old q0_old
    ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  loopN1Pre sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_2 u0_orig_1 u0_orig_0 q3_old q2_old q1_old q0_old **
  (sp + signExtend12 3968 ↦ₘ ret_mem) **
  (sp + signExtend12 3960 ↦ₘ d_mem) **
  (sp + signExtend12 3952 ↦ₘ dlo_mem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

-- ============================================================================
-- Two-iteration (j=1, j=0) precondition/postcondition for n=1
-- ============================================================================

/-- Precondition for n=1 two-iteration loop (j=1, j=0).
    Same structure as loopN2Iter10Pre but with n_mem = 1. -/
@[irreducible]
def loopN1Iter10Pre (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word) : Assertion :=
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
  (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
  (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
  (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_1 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_1 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_1 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_1 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_1 + signExtend12 4064) ↦ₘ u_top) **
  (q_addr_1 ↦ₘ q1_old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0_orig) **
  (q_addr_0 ↦ₘ q0_old)

/-- Precondition for n=1 two-iteration loop with scratch cells. -/
@[irreducible]
def loopN1Iter10PreWithScratch (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
    ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  loopN1Iter10Pre sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old **
  (sp + signExtend12 3968 ↦ₘ ret_mem) **
  (sp + signExtend12 3960 ↦ₘ d_mem) **
  (sp + signExtend12 3952 ↦ₘ dlo_mem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

/-- Unified postcondition for n=1 two-iteration loop (j=1, j=0).
    Same structure as loopN2Iter10Post but with n=1 per-iteration functions.
    Scratch handling: call path includes scratch, max path carries passthrough params.
    For n=1: div128 scratch uses v0/div128DLo v0/div128Un0 u0. -/
@[irreducible]
def loopN1Iter10Post (bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig
     ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  let r1 := iterN1 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  -- j=0 iteration postcondition (includes scratch if bltu_0 = true)
  loopIterPostN1 bltu_0 sp base (0 : Word) v0 v1 v2 v3
    u0_orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  -- Carried atoms from j=1
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  -- Scratch cells
  match bltu_1, bltu_0 with
  | false, false =>
    (sp + signExtend12 3968 ↦ₘ ret_mem) **
    (sp + signExtend12 3960 ↦ₘ d_mem) **
    (sp + signExtend12 3952 ↦ₘ dlo_mem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | false, true  => empAssertion
  | true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0)
  | true,  true  => empAssertion

-- ============================================================================
-- Three-iteration (j=2, j=1, j=0) precondition/postcondition for n=1
-- ============================================================================

/-- Precondition for n=1 three-iteration loop (j=2, j=1, j=0).
    Same structure as loopN2Pre but with n_mem = 1, starting at j=2. -/
@[irreducible]
def loopN1Iter210Pre (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_1 u0_orig_0
    q2_old q1_old q0_old : Word) : Assertion :=
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (2 : Word)) **
  (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
  (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
  (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base_2 + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base_2 + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base_2 + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base_2 + signExtend12 4072) ↦ₘ u3) **
  ((u_base_2 + signExtend12 4064) ↦ₘ u_top) **
  (q_addr_2 ↦ₘ q2_old) **
  ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) **
  (q_addr_1 ↦ₘ q1_old) **
  ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) **
  (q_addr_0 ↦ₘ q0_old)

/-- Precondition for n=1 three-iteration loop with scratch cells. -/
@[irreducible]
def loopN1Iter210PreWithScratch (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_1 u0_orig_0
    q2_old q1_old q0_old
    ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  loopN1Iter210Pre sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top
    u0_orig_1 u0_orig_0 q2_old q1_old q0_old **
  (sp + signExtend12 3968 ↦ₘ ret_mem) **
  (sp + signExtend12 3960 ↦ₘ d_mem) **
  (sp + signExtend12 3952 ↦ₘ dlo_mem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0)

/-- Unified postcondition for n=1 three-iteration loop (j=2, j=1, j=0).
    Parameterized by `(bltu_2 bltu_1 bltu_0 : Bool)` covering all 8 path combinations.
    For n=1: div128 scratch uses v0/div128DLo v0/div128Un0 u0 (u0 from the call iteration). -/
@[irreducible]
def loopN1Iter210Post (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top
     u0_orig_1 u0_orig_0
     ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  -- Compute iteration results
  let r2 := iterN1 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let r1 := iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  -- Address bases for carried atoms
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  -- j=0 iteration postcondition (includes scratch if bltu_0 = true)
  loopIterPostN1 bltu_0 sp base (0 : Word) v0 v1 v2 v3
    u0_orig_0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  -- Carried atoms from j=1 and j=2
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  ((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1) **
  -- Scratch cells
  match bltu_2, bltu_1, bltu_0 with
  | false, false, false =>
    (sp + signExtend12 3968 ↦ₘ ret_mem) **
    (sp + signExtend12 3960 ↦ₘ d_mem) **
    (sp + signExtend12 3952 ↦ₘ dlo_mem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | false, false, true  => empAssertion
  | false, true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_orig_1)
  | false, true,  true  => empAssertion
  | true,  false, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0)
  | true,  false, true  => empAssertion
  | true,  true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_orig_1)
  | true,  true,  true  => empAssertion

/-- Unified postcondition for the n=1 four-iteration loop.
    Parameterized by `(bltu_3 bltu_2 bltu_1 bltu_0 : Bool)` covering all 16 path combinations.

    Structure:
    - j=0 iteration postcondition (includes scratch when bltu_0 = true)
    - Carried atoms from j=1 (u4, q), j=2 (u4, q), and j=3 (u4, q)
    - Scratch cells: depend on which iteration was the last call path
      - All max (F,F,F,F): passthrough original scratch params
      - bltu_0=true: scratch handled inside loopIterPostN1Call (empAssertion here)
      - Last call was j=1 (bltu_1=T, bltu_0=F): scratch from j=1's div128 (div128Un0 u0_orig_1)
      - Last call was j=2 (bltu_2=T, bltu_1=F, bltu_0=F): scratch from j=2's div128 (div128Un0 u0_orig_2)
      - Last call was j=3 (bltu_3=T, others F): scratch from j=3's div128 (div128Un0 u0) -/
@[irreducible]
def loopN1UnifiedPost (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top
     u0_orig_2 u0_orig_1 u0_orig_0
     ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  -- Compute iteration results
  let r3 := iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let r2 := iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
  let r1 := iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  -- Address bases for carried atoms
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  -- j=0 iteration postcondition (includes scratch if bltu_0 = true)
  loopIterPostN1 bltu_0 sp base (0 : Word) v0 v1 v2 v3
    u0_orig_0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
  -- Carried atoms from j=1, j=2, and j=3
  ((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1) **
  ((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1) **
  ((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1) **
  -- Scratch cells: value depends on the last call-path iteration
  match bltu_3, bltu_2, bltu_1, bltu_0 with
  | false, false, false, false =>
    (sp + signExtend12 3968 ↦ₘ ret_mem) **
    (sp + signExtend12 3960 ↦ₘ d_mem) **
    (sp + signExtend12 3952 ↦ₘ dlo_mem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | false, false, false, true  => empAssertion
  | false, false, true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_orig_1)
  | false, false, true,  true  => empAssertion
  | false, true,  false, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_orig_2)
  | false, true,  false, true  => empAssertion
  | false, true,  true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_orig_1)
  | false, true,  true,  true  => empAssertion
  | true,  false, false, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0)
  | true,  false, false, true  => empAssertion
  | true,  false, true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_orig_1)
  | true,  false, true,  true  => empAssertion
  | true,  true,  false, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_orig_2)
  | true,  true,  false, true  => empAssertion
  | true,  true,  true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0) **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_orig_1)
  | true,  true,  true,  true  => empAssertion

-- ============================================================================
-- Double-addback iter variants (models the FIXED algorithm)
--
-- These define the correct semantics with double addback: after the first
-- addback, check addbackN4_carry; if carry = 0 (overestimate was 2),
-- perform a second addback and decrement q by 2 instead of 1.
--
-- The original iterN*Max/iterN*Call definitions (above) model the CURRENT
-- assembly which only does single addback. These _da variants model the
-- FIXED assembly with the backward-branch double addback check.
-- ============================================================================

/-- Helper: single iteration with double addback, parameterized by q_hat.
    Used by all iter*_da variants. -/
def iterWithDoubleAddback (q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  if BitVec.ult u_top c3 then
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u_top - c3) v0 v1 v2 v3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
    if carry = 0 then
      let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
      (q_hat + signExtend12 4095 + signExtend12 4095,
       ab'.1, ab'.2.1, ab'.2.2.1, ab'.2.2.2.1, ab'.2.2.2.2)
    else
      (q_hat + signExtend12 4095, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2.1, ab.2.2.2.2)
  else
    (q_hat, ms.1, ms.2.1, ms.2.2.1, ms.2.2.2.1, u_top - c3)

@[irreducible]
def iterN1Max_da (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 u_top

@[irreducible]
def iterN1Call_da (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 u_top

@[irreducible]
def iterN2Max_da (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 u_top

@[irreducible]
def iterN2Call_da (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 u_top

@[irreducible]
def iterN3Max_da (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 u_top

@[irreducible]
def iterN3Call_da (v0 v1 v2 v3 u0 u1 u2 u3 u_top : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 u_top

end EvmAsm.Evm64
