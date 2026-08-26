/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128V5Phase1bBridge

  The generic Phase-1b/2b **code-vs-model selection reconciliation** for the v5
  div128 q-bridge.

  The div128 code post (`div128V5SpecPost`) selects the corrected quotient digit
  with an *outer* `rhatcHi ≠ 0` guard wrapping two unguarded D3 corrections:

      bq'    = if ult rhatUn  (q*dLo)  then q+1 else q          -- 1st correction
      q''    = if ult rhatUn' (bq'*dLo) then bq'+1 else bq'     -- 2nd correction
      qFinal = if rhatcHi ≠ 0 then q else (if brhat'Hi = 0 then q'' else bq')

  while the model `div128Quot_v5` folds the `rhatcHi = 0` guard into the *first*
  correction's fire condition and delegates the second to
  `div128Quot_phase2b_q0'`:

      fire1  = decide (rhatcHi = 0) && ult rhatUn (q*dLo)
      q'     = if fire1 then q+1 else q
      qModel = div128Quot_phase2b_q0' q' rhat' dLo un

  Both compute the same digit; this lemma proves it for arbitrary
  `q rhatc dHi dLo un`, by case analysis on `rhatcHi` and the two ULTs plus the
  `div128Quot_phase2b_q0'_and_form` rewrite.  It is the reusable heart of the
  q-bridge `div128V5SpecPost.q = div128Quot_v5` (both the Phase-1 `q1` digit and
  the Phase-2 `q0` digit have this exact shape).  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.LoopBody.TrialCall

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- `ite` over a conjunction unfolds to nested `ite` (common else branch). -/
private theorem ite_and_nest {α : Sort _} (C D : Prop) [Decidable C] [Decidable D]
    (x y : α) :
    (if C ∧ D then x else y) = if C then (if D then x else y) else y := by
  by_cases hC : C <;> by_cases hD : D <;> simp [hC, hD]

/-- **Phase-1b/2b code = model selection.**  The code's outer-`rhatcHi`-guarded
    two-correction selection equals the model's `phase1bFire`/`phase2b_q0'`
    form, for arbitrary capped quotient `q`, remainder `rhatc`, and the divisor
    halves `dHi`/`dLo` and dividend half `un`. -/
theorem div128V5_phase1b_select_eq
    (q rhatc dHi dLo un : Word) :
    (if rhatc >>> (32 : BitVec 6).toNat ≠ 0 then q
     else
      (if ((if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
              then rhatc + dHi else rhatc) >>> (32 : BitVec 6).toNat = 0)
       then
        (if BitVec.ult
              (((if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
                  then rhatc + dHi else rhatc) <<< (32 : BitVec 6).toNat) ||| un)
              ((if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
                  then q + signExtend12 4095 else q) * dLo)
          then (if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
                  then q + signExtend12 4095 else q) + signExtend12 4095
          else (if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
                  then q + signExtend12 4095 else q))
       else (if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
               then q + signExtend12 4095 else q)))
    =
    div128Quot_phase2b_q0'
      (if decide (rhatc >>> (32 : BitVec 6).toNat = 0) &&
            BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
       then q + signExtend12 4095 else q)
      (if decide (rhatc >>> (32 : BitVec 6).toNat = 0) &&
            BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
       then rhatc + dHi else rhatc)
      dLo un := by
  rw [← div128Quot_phase2b_q0'_and_form]
  by_cases hHi : rhatc >>> (32 : BitVec 6).toNat = (0 : Word)
  · -- rhatcHi = 0: outer code guard false; model fire1 = ult.
    by_cases hUlt : BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
    · simp only [hHi, hUlt, ne_eq, not_true_eq_false, if_false, if_true,
        decide_true, Bool.true_and]
      rw [ite_and_nest]
    · simp only [hHi, hUlt, ne_eq, not_true_eq_false, if_false,
        decide_true, Bool.and_false, Bool.false_eq_true]
      simp
  · -- rhatcHi ≠ 0: code picks q; model fire1 = false, phase2b guard false → q.
    simp only [hHi, ne_eq, not_false_eq_true, if_true, decide_false,
      Bool.false_and, Bool.false_eq_true, if_false]
    simp

/-- **Phase-1b/2b code = model remainder selection.**  Companion to
    `div128V5_phase1b_select_eq` for the *remainder* `rhatFinal`/`rhat''` (needed
    for `un21 = (rhatFinal << 32 ||| un) - q1Final * dLo`).  Same case analysis,
    via `div128Quot_phase2b_rhat_and_form`. -/
theorem div128V5_phase1b_rhat_select_eq
    (q rhatc dHi dLo un : Word) :
    (if rhatc >>> (32 : BitVec 6).toNat ≠ 0 then rhatc
     else
      (if ((if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
              then rhatc + dHi else rhatc) >>> (32 : BitVec 6).toNat = 0)
       then
        (if BitVec.ult
              (((if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
                  then rhatc + dHi else rhatc) <<< (32 : BitVec 6).toNat) ||| un)
              ((if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
                  then q + signExtend12 4095 else q) * dLo)
          then (if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
                  then rhatc + dHi else rhatc) + dHi
          else (if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
                  then rhatc + dHi else rhatc))
       else (if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
               then rhatc + dHi else rhatc)))
    =
    (if (if decide (rhatc >>> (32 : BitVec 6).toNat = 0) &&
            BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
         then rhatc + dHi else rhatc) >>> (32 : BitVec 6).toNat = 0 then
      let qDlo2 := (if decide (rhatc >>> (32 : BitVec 6).toNat = 0) &&
                       BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
                    then q + signExtend12 4095 else q) * dLo
      let rhatUn := ((if decide (rhatc >>> (32 : BitVec 6).toNat = 0) &&
                         BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
                      then rhatc + dHi else rhatc) <<< (32 : BitVec 6).toNat) ||| un
      if BitVec.ult rhatUn qDlo2 then
        (if decide (rhatc >>> (32 : BitVec 6).toNat = 0) &&
            BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
         then rhatc + dHi else rhatc) + dHi
      else (if decide (rhatc >>> (32 : BitVec 6).toNat = 0) &&
              BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
            then rhatc + dHi else rhatc)
     else (if decide (rhatc >>> (32 : BitVec 6).toNat = 0) &&
              BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
            then rhatc + dHi else rhatc)) := by
  rw [← div128Quot_phase2b_rhat_and_form]
  by_cases hHi : rhatc >>> (32 : BitVec 6).toNat = (0 : Word)
  · by_cases hUlt : BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
    · simp only [hHi, hUlt, ne_eq, not_true_eq_false, if_false, if_true,
        decide_true, Bool.true_and]
      rw [ite_and_nest]
    · simp only [hHi, hUlt, ne_eq, not_true_eq_false, if_false,
        decide_true, Bool.and_false, Bool.false_eq_true]
      simp
  · simp only [hHi, ne_eq, not_false_eq_true, if_true, decide_false,
      Bool.false_and, Bool.false_eq_true, if_false]

end EvmAsm.Evm64
