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

/-- **FIXED** trial quotient: `div128Quot` with Knuth's classical 2-iteration
    D3 correction loop (TAOCP 4.3.1).

    Differs from `div128Quot` only in Phase 1b: the 2nd D3 correction is
    delegated to the existing `div128Quot_phase2b_q0'` helper, which already
    encodes Knuth's classical D3 single iteration (with the `rhat' < B`
    guard). Calling it for Phase 1b reuses the well-tested classical
    construction.

    With 2 D3 iterations, q1' satisfies Knuth's per-digit overshoot ≤ 0
    invariant; combined with the at-most-2 outer addbacks, qHat overshoot
    stays ≤ 2 and the BEQ branch recovers q_true correctly.

    **KNOWN BUG (2026-04-28)**: the 1st D3 correction below is missing the
    `rhatc >> 32 = 0` guard that the 2nd correction has. When `rhatc ≥ 2^32`,
    the `(rhatc << 32) | div_un1` truncates rhatc's high bits and the BLTU
    can falsely fire, producing `q1' = q_true - 1`. Numerically witnessed:
    on `(uHi=2^64-2^32+1, uLo=0, vTop=2^64-1)`, `div128Quot_v2` returns
    `2^64-2^33+1` but the true quotient is `2^64-2^32+1` (undershoot 2^32).
    Verified by `div128Quot_v2_buggy_at_unreachable_uHi` (decide-checked)
    in `SpecCallAddbackBeq/NumericalTests.lean`.

    **Why this hasn't broken anything yet**: the buggy regime requires
    `uHi ≥ 2^63`, which is unreachable through shift normalization
    (`u4 = a3 >>> antiShift`, antiShift ∈ [1, 63] under runtime
    `_hshift_nz`, so `u4 < 2^63`). So all valid call paths land at
    `rhatc < 2^32` where the guard wouldn't fire anyway.

    **Fix plan** (see `memory/project_div128_v2_phase1b_truncation_fix.md`):
    refactor the 1st correction to reuse `div128Quot_phase2b_q0'` (which has
    the guard built-in), mirroring the 2nd correction:
    ```
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' := if rhatc >>> 32 = 0 then
      let qDlo := q1c * dLo
      let rhatUn1 := (rhatc <<< 32) ||| div_un1
      if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    else rhatc
    ```
    The fix is no-op under runtime preconditions; only suppresses
    truncation-induced spurious fires at unreachable Word-level inputs.
    Verification chain:
    1. Update this def + flip `div128Quot_v2_buggy_at_unreachable_uHi`'s
       conclusion to assert correctness.
    2. Drop `rhatc < 2^32` precondition from Stub 2
       (`_phase1b_check_iff_overshoot_under_runtime`) since the guard
       provides it automatically.
    3. Strengthen Word-level Knuth-B claims (currently restricted to
       inputs with rhatc < 2^32) to apply unconditionally.
    4. Insert the matching 2-instruction guard in the RISC-V program
       (`SRLI .x1 .rhatc 32 ; BNE .x1 .x0 1st_guard_off`) before the
       1st BLTU.

    **Migration plan**: this is the target abstraction post-fix. The
    actual RISC-V program at `Program.lean:divK_div128` needs the
    corresponding 2nd D3 correction inserted (~6 instructions after
    the existing one at lines 80-87). Once the program is updated, all
    references to `div128Quot` should migrate to `div128Quot_v2`, and
    the buggy `div128Quot` removed. See
    `memory/project_n4callbeq_addback_overshoot_2pow32.md` for the
    counterexample that motivates this fix. -/
def div128Quot_v2 (uHi uLo vTop : Word) : Word :=
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := uLo >>> (32 : BitVec 6).toNat
  let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  -- Phase 1b: 1st D3 correction (unchanged).
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
  -- Phase 1b: 2nd D3 correction — reuse Knuth's classical step from
  -- `div128Quot_phase2b_q0'` (which has the `rhat' < B` guard built-in).
  let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
  -- rhat'' tracking: only changes if the 2nd D3 correction fires.
  let rhat'' :=
    if rhat' >>> (32 : BitVec 6).toNat = 0 then
      let qDlo2 := q1' * dLo
      let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
      if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
    else rhat'
  -- Phase 2 setup with q1''/rhat''.
  let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1'' * dLo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
  (q1'' <<< (32 : BitVec 6).toNat) ||| q0'

/-- Low 32 bits of vTop, stored to scratch during div128 call path. -/
def div128DLo (vTop : Word) : Word :=
  (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat

/-- Low 32 bits of uLo, stored to scratch during div128 call path. -/
def div128Un0 (uLo : Word) : Word :=
  (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat

-- ============================================================================
-- Double-addback iter variants (model the FIXED algorithm with double addback)
--
-- 🚨 Correctness note (2026-04-27): This iter assumes that `qHat` overshoots
-- the true quotient by AT MOST 2 (Knuth Theorem B). That assumption holds
-- when the trial digit is computed by Knuth's classical Phase 1b
-- (2-iteration D3 correction loop). Our `div128Quot` (in the same file)
-- does only 1 Phase 1b correction, which under hshift_nz allows val256-level
-- qHat overshoot up to ~2^33 (combining per-digit Knuth-B applied to q1' and
-- q0' independently). On such inputs `iterWithDoubleAddback` exits with the
-- wrong q_out (off by ~2^32 from q_true), making
-- `n4CallAddbackBeqSemanticHolds` provably FALSE.
--
-- See `memory/project_n4callbeq_addback_overshoot_2pow32.md` for the
-- counterexample (a3 = 2^63+2^33, b3 = 1, b2 = 2^33-1) and
-- `memory/project_knuth_d_one_correction_design.md` for the literature
-- analysis.
--
-- Remediation: either modify `div128Quot` to do 2 Phase 1b corrections
-- (matches Knuth classical, simplest fix) or harden the loop's exit
-- condition. The actual RISC-V program at `Program.lean:386` has a
-- BEQ-based addback loop matching this Lean abstraction's at-most-2
-- iterations — so the bug is in the algorithm itself, not in the
-- abstraction.
-- ============================================================================

/-- Helper: single iteration with double addback, parameterized by qHat.
    Used by all iter* variants.

    **Correctness assumption**: qHat overshoots q_true by ≤ 2. Holds for
    Knuth-classical 2-correction Phase 1b; FAILS for our 1-correction
    `div128Quot` on certain inputs. -/
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

/-- v2 mirror of `isAddbackCarry2NzN4Call`: same as v1 but uses
    `div128Quot_v2` for the trial quotient.

    Issue #1337 algorithm fix migration. -/
def isAddbackCarry2NzN4Call_v2 (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) : Prop :=
  isAddbackCarry2Nz (div128Quot_v2 uTop u3 v3) v0 v1 v2 v3 u0 u1 u2 u3 uTop

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
